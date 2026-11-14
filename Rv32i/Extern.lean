import Rv32i.Asm

/-!
# External Calls (SKETCH)
A generic interface for code we do not model instruction by instruction:
system calls (`ecall`) and library functions (`malloc`, ...).

Nothing here is a Lean `axiom`. An external function is described by a `Spec`, and the
semantics is *parameterized* over an `Env` of such specs. A theorem about a program then
reads "for every environment that behaves like this, ...", so we cannot introduce an
inconsistency, and a spec can later be discharged by linking a verified implementation.

Three layers:
1. `Spec W`  : what a function does, independent of registers and of the language.
2. `Conv`    : a calling convention, lifting a `Spec` to a relation on `Machine.State PC`
               (generic in the pc type, so `Sym` and `Asm` share it).
3. `Env W`   : which specs exist, and how each language reaches them.

`W` is the *world*: abstract state that is not part of the machine, such as the set of
live heap blocks or the bytes written to stdout so far.
-/

namespace Extern

abbrev Mem := Word -> BitVec 8

/-! ## 1. Specifications -/

/-- Behaviour of an external function over world state `W`.
`post` is a relation: results may be nondeterministic (the address `malloc` returns,
the bytes `read` delivers). Calling outside `pre` is undefined behaviour: the machine
is stuck, which is a fault like any other. -/
structure Spec (W : Type) where
  /-- Number of (word-sized) arguments. -/
  arity : Nat
  pre   : (args : List Word) -> Mem -> W -> Prop
  post  : (args : List Word) -> Mem -> W -> (ret : Word) -> Mem -> W -> Prop

/-- Reuse a spec about a component `V` of a bigger world `W`; the rest of `W` is framed.
This is how independently written specs (heap, file system, ...) are combined. -/
def Spec.lift {V W : Type} (get : W -> V) (set : V -> W -> W) (f : Spec V) : Spec W where
  arity := f.arity
  pre args m w := f.pre args m (get w)
  post args m w ret m' w' := ∃ v', f.post args m (get w) ret m' v' ∧ w' = set v' w

/-! ## 2. Calling conventions -/

/-- Where arguments and the result live, and which registers survive the call.
All other registers hold arbitrary values afterwards. -/
structure Conv where
  args      : List Reg
  ret       : Reg
  preserved : Reg -> Bool

/-- Linux system call: arguments in `a0`-`a5`, everything but `a0` is preserved. -/
def Conv.syscall : Conv where
  args := [.a0, .a1, .a2, .a3, .a4, .a5]
  ret  := .a0
  preserved r := r != .a0

/-- Standard C calling convention (ILP32): `ra`, `a*` and `t*` are clobbered. -/
def Conv.c : Conv where
  args := [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7]
  ret  := .a0
  preserved
    | .sp | .gp | .tp | .s0 | .s1 | .s2 | .s3 | .s4 | .s5 | .s6
    | .s7 | .s8 | .s9 | .s10 | .s11 => true
    | _ => false

/-- A call of `f` under convention `c` takes `(s, w)` to `(s', w')`.
The pc is left alone; each language advances it in its own way. -/
def Spec.Call {W PC : Type} (f : Spec W) (c : Conv)
    (s : Machine.State PC) (w : W) (s' : Machine.State PC) (w' : W) : Prop :=
  let args := (c.args.take f.arity).map s.read
  f.pre args s.mem w
  ∧ f.post args s.mem w (s'.read c.ret) s'.mem w'
  ∧ (∀ r, c.preserved r -> s'.read r = s.read r)
  ∧ s'.pc = s.pc

/-! ## 3. Environments -/

abbrev Symbol := String

/-- Everything a program can call but does not contain. -/
structure Env (W : Type) where
  /-- System calls, by number (`a7`). -/
  syscall : Word -> Option (Spec W)
  /-- Library functions, by symbol name. -/
  extern  : Symbol -> Option (Spec W)

/-!
## Hooking into a language

Configurations become `State × W`, and the step function becomes a relation.
Ordinary instructions keep using the executable `step`; only the external rules are new.

The rule for library calls is not written out below since it needs a new instruction,
`call (f : Symbol)`, in both `Sym` (non-terminal, like `ECall`) and `Asm` (rendered as
`jal ra, f`, to stay 4 bytes wide; the linker resolves `f`):

    | call : fetch p s.pc = some (.call f) -> env.extern f = some spec ->
        spec.Call .c s w s' w' -> XStep env p (s, w) (s'.next, w')

The call is one atomic step: `ra` is clobbered by `Conv.c` instead of being modelled.
-/

open Asm in
inductive _root_.Asm.XStep {W : Type} (env : Env W) (p : Program) :
    State × W -> State × W -> Prop
  | instr {s s' w} : Asm.Step p s s' -> XStep env p (s, w) (s', w)
  | syscall {s s' w w' spec} :
      fetch p s.pc = some (.ISysI .ecall) ->
      env.syscall (s.read .a7) = some spec ->
      spec.Call .syscall s w s' w' ->
      XStep env p (s, w) (State.next s', w')

/-- `Q` is reached on *every* run from `c`, and no run gets stuck before.
With nondeterministic steps, `∃ c', Star c c' ∧ Q c'` (as in `Asm.Terminates`) is too
weak: it would let us pick the `malloc` result that happens to make the program work. -/
inductive Eventually {C : Type} (Step : C -> C -> Prop) (Q : C -> Prop) : C -> Prop
  | done {c} : Q c -> Eventually Step Q c
  | step {c} : (∃ c', Step c c') -> (∀ c', Step c c' -> Eventually Step Q c') ->
      Eventually Step Q c

/-! ## Example: `malloc` / `free` -/

/-- Live heap blocks: base address ↦ size in bytes. -/
structure Heap where
  blocks : Word -> Option Nat

/-- `[p, p + n)` does not wrap around and overlaps no live block. -/
def Heap.Fresh (h : Heap) (p : Word) (n : Nat) : Prop :=
  p.toNat + n ≤ 2 ^ 32
  ∧ ∀ q m, h.blocks q = some m -> p.toNat + n ≤ q.toNat ∨ q.toNat + m ≤ p.toNat

def Heap.set (h : Heap) (p : Word) (b : Option Nat) : Heap :=
  { blocks := fun q => if q = p then b else h.blocks q }

/-- `malloc(n)` fails with `0`, or returns a fresh, aligned block. -/
def malloc : Spec Heap where
  arity := 1
  pre _ _ _ := True
  post args m h p m' h' :=
    match args with
    | [n] => m' = m ∧
        ((p = 0 ∧ h' = h)
         ∨ (p ≠ 0 ∧ p.toNat % 16 = 0 ∧ h.Fresh p n.toNat ∧ h' = h.set p (some n.toNat)))
    | _ => False

/-- `free(p)` requires `p` to be null or the base of a live block (else: UB). -/
def free : Spec Heap where
  arity := 1
  pre args _ h :=
    match args with
    | [p] => p = 0 ∨ (h.blocks p).isSome
    | _ => False
  post args m h _ m' h' :=
    match args with
    | [p] => m' = m ∧ h' = h.set p none
    | _ => False

/-! ## Example: the `write` system call -/

/-- `write(fd, buf, len)` to stdout, where the world is the output so far.
It may write fewer than `len` bytes (but at least one, unless `len = 0`). -/
def sysWrite : Spec (List (BitVec 8)) where
  arity := 3
  pre args _ _ :=
    match args with
    | [fd, _, _] => fd = 1
    | _ => False
  post args m out k m' out' :=
    match args with
    | [_, buf, len] => m' = m ∧ k.toNat ≤ len.toNat ∧ (len ≠ 0 -> k ≠ 0)
        ∧ out' = out ++ (List.range k.toNat).map (fun i => m (buf + BitVec.ofNat 32 i))
    | _ => False

/-! ## Example: an environment combining both -/

structure World where
  heap   : Heap
  stdout : List (BitVec 8)

def linux : Env World where
  syscall n :=
    if n = 64 then some (sysWrite.lift (·.stdout) (fun o w => { w with stdout := o }))
    else none
  extern
    | "malloc" => some (malloc.lift (·.heap) (fun h w => { w with heap := h }))
    | "free"   => some (free.lift (·.heap) (fun h w => { w with heap := h }))
    | _        => none

end Extern
