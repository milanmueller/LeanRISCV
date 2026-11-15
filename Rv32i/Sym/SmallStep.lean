import Rv32i.Asm.SmallStep

namespace Rv32i

/-!

# `Sym` Language

The sym language is an Abstraction of `Asm` that only allows for symbolic jumps to labels.
Jumping and branching instructions are replaced by relative pseudo instructions.
The restriction to symbolic targets allows for defining programs as (possibly cyclic) graphs.

`Sym` reuses the instruction kinds of `Asm` (`RInstr`, `IInstr`, ...), which map 1-to-1.

## The stack
`Sym` has an abstract stack, which is part of the symbolic program counter. It holds
* return blocks: `Jump f ret` jumps to `f` and pushes the block `ret` to continue with,
  `Ret` pops it;
* spilled words: `Push rs` and `Pop rd`.

`Ret` needs a return block on top of the stack and `Pop` a word, so a block has to pop
everything it pushed before it returns.

Programs cannot touch the stack in any other way: `sp` is not a `Sym` register, and
the memory the compiled program keeps the stack in is protected. With `n` entries on the
stack, these are the `4 * n` bytes starting at `sp`, and loads from and stores to them
are stuck. The stack instructions move `sp` accordingly, but do not write to memory:
the entries only exist in the abstract stack.

-/

/-!
## Syntax
-/

open Asm (Imm5 Imm12 Imm20
  RInstr IInstr IShInstr ILInstr SInstr BInstr)

namespace Sym

/-
`Sym` does not read from, or write into `ra` and `sp`, as it models control flow and
spilling through an abstract stack. We hence exclude both from the available registers.
-/
abbrev Reg := { r : Rv32i.Reg // r ≠ .ra ∧ r ≠ .sp }

-- Internal unique labels
abbrev Label := Nat

/-- An entry of the stack: a block to return to, or a spilled word. -/
inductive Entry
  | ret (l : Label)
  | val (w : Word)
  deriving DecidableEq, Repr

/--
The symbolic program counter: a program point `(block, idx)`, and the stack (top first).
 -/
structure PC where
  block : Label
  idx   : Nat
  stack : List Entry
  deriving DecidableEq, Repr

abbrev State := Machine.State PC

-- The Syntax and semantic of `Sym` are parameterized by `Library`, so we fix it here.
section 
variable (ℓ : Library)

/-
Instructions are parameterized over a type `α` of external labels/functions.
The default is in inductive type of selected Syscalls and libc functions with axiomatized semantics.
-/
inductive Instr

  -- Standard instructions inherited from `Asm` 
  | RI (instr : RInstr) (rd : Reg) (rs1 : Reg) (rs2 : Reg)
  | II (instr : IInstr) (rd : Reg) (rs1 : Reg) (imm : Imm12)
  | IShI (instr : IShInstr) (rd : Reg) (rs1 : Reg) (imm : Imm5)
  | ILI (instr : ILInstr) (rd : Reg) (rs1 : Reg) (imm : Imm12)
  | SI (instr : SInstr) (rs1 : Reg) (rs2 : Reg) (imm : Imm12)

  -- Pseudo Instructions specific to `Sym`.
  -- `BInstr` is abstracted to carry targets for both cases.
  | BI (instr : BInstr) (rs1 : Reg) (rs2 : Reg) (ifTrue : Label) (ifFalse : Label)
  -- Unconditional jump to `target`, return to `ret` once done
  | Jump (target : Label) (ret : Label)
  -- Call external function `target`, return to `ret` once done
  | Call (target : ℓ.Function) (ret : Label)
  /-- Return to the block on top of the stack. -/
  | Ret
  /-- Spill `rs` onto the stack. -/
  | Push (rs : Reg)
  /-- Pop the word on top of the stack into `rd`. -/
  | Pop (rd : Reg)

def Instr.isTerminal : Instr ℓ → Bool
  | .BI _ _ _ _ _ => true
  | .Jump _ _     => true
  | .Call _ _     => true
  | .Ret          => true
  | _             => false

/-!
### Programs
-/

structure Block where
  instrs : List (Instr ℓ)
  neq    : instrs ≠ []
  term   : (instrs.getLast neq).isTerminal
  wf     : instrs.dropLast.all (fun i => ¬i.isTerminal)

def Instr.lsOut : Instr ℓ → List Label
  | BI _ _ _ t f => [t, f]
  | Jump t _     => [t]
  | _            => []

def Block.lsOut (b : Block ℓ) : List Label :=
  b.instrs.flatMap (Instr.lsOut ℓ)

structure Program where
  blocks : List (Block ℓ)
  nempty : blocks ≠ []
  wf : ∀ b ∈ blocks, ∀ l ∈ b.lsOut, l < blocks.length

-- From here on the library is inferred from the program / instruction.
variable {ℓ}

def Program.fetch (p : Program ℓ) (pc : PC) : Option (Instr ℓ) := do
  let b ← p.blocks[pc.block]?
  b.instrs[pc.idx]?

/-!
## Semantics
-/

namespace State

-- Advance in current block
def next (s : State) : State := { s with pc := { s.pc with idx := s.pc.idx + 1 } }

@[simp] theorem next_pc (s : State) : s.next.pc = { s.pc with idx := s.pc.idx + 1 } := rfl
@[simp] theorem next_read (s : State) (r : Reg) : s.next.read r = s.read r := rfl

def jump (s : State) (target : Label) : State :=
  { s with pc := { s.pc with block := target, idx := 0 } }

/-- Push an entry onto the stack, which grows downwards by one word. -/
def push (s : State) (e : Entry) : State :=
  let s := s.write .sp (s.read .sp - 4)
  { s with pc := { s.pc with stack := e :: s.pc.stack } }

/-- Drop the top entry, leaving the stack `rest`. -/
def pop (s : State) (rest : List Entry) : State :=
  let s := s.write .sp (s.read .sp + 4)
  { s with pc := { s.pc with stack := rest } }

/-- Whether an access to the `n` bytes at address `a` touches the memory of the stack:
the `4 * s.pc.stack.length` bytes at `sp`. Addresses wrap around, so this is the case if
`a` lies in the stack, or if the stack starts within the accessed bytes. -/
def isProtected (s : State) (a : Word) (n : Nat) : Bool :=
  let sp := s.read .sp
  (a - sp).toNat < 4 * s.pc.stack.length || (s.pc.stack ≠ [] && (sp - a).toNat < n)

/-- Execution starts at the first block with an empty stack.
`sp` only ever moves by whole words, so it stays aligned. -/
def initial (s : State) : Prop :=
  s.pc = ⟨0, 0, []⟩ ∧ (s.read .sp).toNat % 4 = 0

end State

namespace Program

def step (s : State) (w : ℓ.World) : Instr ℓ → Option (State × ℓ.World)
  | .RI op rd rs1 rs2 =>
      some <| (State.next (s.write rd (op.eval (s.read rs1) (s.read rs2))), w)
  | .II op rd rs1 imm =>
      some <| (State.next (s.write rd (op.eval (s.read rs1) imm)), w)
  | .IShI op rd rs1 imm =>
      some <| (State.next (s.write rd (op.eval (s.read rs1) imm)), w)
  -- Loads and stores are stuck if they touch the memory of the stack.
  | .ILI op rd rs1 imm => do
      let a := s.read rs1 + imm.signExtend 32
      if s.isProtected a op.width then none
      let v ← op.load s.toCore a
      pure <| (State.next (s.write rd v), w)
  | .SI op rs1 rs2 imm => do
      let a := s.read rs1 + imm.signExtend 32
      if s.isProtected a op.width then none
      let s' ← op.store s a (s.read rs2)
      pure <| (State.next s', w)
  | .BI op rs1 rs2 tt tf =>
      if op.eval (s.read rs1) (s.read rs2)
      then some (s.jump tt, w)
      else some (s.jump tf, w)
  | .Jump t r => some ((s.push (.ret r)).jump t, w)
  | .Call f ret => do
      -- the library only sees registers and memory; we continue at `ret` ourselves
      let (c', w') <- ℓ.semantics f s.toCore w
      pure (State.jump (s.withCore c') ret, w')
  | .Ret =>
      match s.pc.stack with
      | .ret l :: rest => some ((s.pop rest).jump l, w)
      | _ => none
  | .Push rs => some (State.next (s.push (.val (s.read rs))), w)
  | .Pop rd =>
      match s.pc.stack with
      | .val v :: rest => some (State.next ((s.pop rest).write rd v), w)
      | _ => none

/-- Small step relation between a configuration (machine state and library world)
and its successor. -/
def Step (p : Program ℓ) (s s' : State) (w w' : ℓ.World) : Prop :=
  ∃ i, p.fetch s.pc = some i ∧ step s w i = some (s', w')

/-- Transitive reflexive closure of `Step` -/
inductive Step.Star (p : Program ℓ) : State → State → ℓ.World → ℓ.World → Prop
  | refl (s w) : Step.Star p s s w w
  | step {s s' w w'} : Step p s s' w w' → Step.Star p s s' w w'
  | trans {s t s' w v w'} :
      Step.Star p s t w v → Step.Star p t s' v w' → Step.Star p s s' w w'

/-- Prepend a single step to a run. -/
theorem Step.Star.head {p : Program ℓ} {s t u : State} {w v x : ℓ.World} (i : Instr ℓ)
    (hf : p.fetch s.pc = some i) (hs : Program.step s w i = some (t, v))
    (h : Step.Star p t u v x) : Step.Star p s u w x :=
  .trans (.step ⟨i, hf, hs⟩) h

/-- Bounded execution: run for at most `n` steps, stopping early when execution gets stuck. -/
def run (p : Program ℓ) : Nat → State → ℓ.World → State × ℓ.World
  | 0, s, w => (s, w)
  | n + 1, s, w =>
    match p.fetch s.pc with
    | none => (s, w)
    | some i =>
      match step s w i with
      | none => (s, w)
      | some (s', w') => run p n s' w'

/-- `run` is sound: it only follows `Step`s. -/
theorem run_star (p : Program ℓ) :
    ∀ n s w, Step.Star p s (run p n s w).1 w (run p n s w).2
  | 0, s, w => .refl s w
  | n + 1, s, w => by
    unfold run
    split
    · exact .refl s w
    · rename_i i hf
      split
      · exact .refl s w
      · rename_i s' w' hs
        exact .trans (.step ⟨i, hf, hs⟩) (run_star p n s' w')

end Program
end -- Section with fixed `ℓ : Library`
end Sym
end Rv32i
