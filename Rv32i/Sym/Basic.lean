import Rv32i.Asm.Basic

namespace Rv32i

/-!

# `Sym` Language

The sym language is an Abstraction of `Asm` that only allows for symbolic jumps to labels.
Jumping and branching instructions are replaced by relative pseudo instructions.
The restriction to symbolic targets allows for defining programs as (possibly cyclic) graphs.

`Sym` reuses the instruction kinds of `Asm` (`RInstr`, `IInstr`, ...), which map 1-to-1,
but defines its own `Instr`: branch and jump targets are labels, and there is no `jalr`.

Function calls are structured: `Call f ret` jumps to `f` and remembers the block `ret` to
continue with on a call stack, `Ret` pops it. The call stack is part of the symbolic
program counter; it is ghost state that vanishes in `Asm`, where only `ra` remains.

System instructions are split by their effect on control flow:
- `ECall` is an ordinary instruction: system calls return to the next instruction.
- `Exit` terminates the program with exit code `a0`.

-/

/-!
## Syntax
-/

open Asm (Imm5 Imm12 Imm20
  RInstr IInstr IShInstr ILInstr SInstr BInstr)

namespace Sym

/-- A jump target: the index of a block in the program. -/
abbrev Label := Nat

/-- Instructions with symbolic jump targets. -/
inductive Instr
  | RI (instr : RInstr) (rd : Reg) (rs1 : Reg) (rs2 : Reg)
  | II (instr : IInstr) (rd : Reg) (rs1 : Reg) (imm : Imm12)
  | IShI (instr : IShInstr) (rd : Reg) (rs1 : Reg) (imm : Imm5)
  | ILI (instr : ILInstr) (rd : Reg) (rs1 : Reg) (imm : Imm12)
  | SI (instr : SInstr) (rs1 : Reg) (rs2 : Reg) (imm : Imm12)
  | ECall
  | Exit
  | BI (instr : BInstr) (rs1 : Reg) (rs2 : Reg) (ifTrue : Label) (ifFalse : Label)
  | J (target : Label)
  /-- Call the function at block `target`. When it returns, continue with block `ret`. -/
  | Call (target : Label) (ret : Label)
  /-- Return to the block on top of the call stack. -/
  | Ret
  | LUI (rd : Reg) (imm : Imm20)

def Instr.isTerminal : Instr -> Bool
  | .BI _ _ _ _ _ => true
  | .J _        => true
  | .Call _ _   => true
  | .Ret        => true
  | .Exit       => true
  | _           => false

/-!
### Programs
We model programs as a CFG with (only) symbolic jumps
-/
structure Block where
  instrs : List Instr
  neq    : instrs ≠ []
  term   : (instrs.getLast neq).isTerminal
  wf     : instrs.dropLast.all (fun i => ¬i.isTerminal)

def Instr.lsOut : Instr -> List Label
  | BI _ _ _ t f => [t, f]
  | J t => [t]
  | Call f r => [f, r]
  | _ => []

def Block.lsOut (b : Block) : List Label :=
  b.instrs.flatMap Instr.lsOut

structure Program where
  blocks : List Block
  nempty : blocks ≠ []
  wf : ∀ b ∈ blocks, ∀ l ∈ b.lsOut, l < blocks.length

/-- The symbolic program counter: a program point `(block, idx)`, and the blocks to
return to from the function calls that are currently active (innermost first). -/
structure PC where
  block     : Label
  idx       : Nat
  callstack : List Label
  deriving DecidableEq, Repr

/-- Fetch the instruction at program point `(pc.block, pc.idx)`. -/
def Program.fetch (p : Program) (pc : PC) : Option Instr := do
  let b ← p.blocks[pc.block]?
  b.instrs[pc.idx]?

/-!
## Semantics

Other than in `Asm`, we use a symbolic program counter.
This is the core abstraction that `Sym` makes over `Asm`.
-/

abbrev State := Machine.State PC

def State.next (s : State) : State := { s with pc := { s.pc with idx := s.pc.idx + 1 } }

@[simp] theorem State.next_pc (s : State) :
    s.next.pc = { s.pc with idx := s.pc.idx + 1 } := rfl
@[simp] theorem State.next_read (s : State) (r : Reg) : s.next.read r = s.read r := rfl

/-- Jump to the start of block `target`, keeping the call stack. -/
def jump (s : State) (target : Label) : State :=
  { s with pc := { s.pc with block := target, idx := 0 } }

/-- Push a return block onto the call stack. -/
def State.push (s : State) (ret : Label) : State :=
  { s with pc := { s.pc with callstack := ret :: s.pc.callstack } }

def State.initial (s : State) : Prop :=
  s.pc = ⟨0, 0, []⟩

/-!
### Layout
Where the translation to `Asm` (`Program.Asm` in `SymToAsm`) places each block. The semantics needs
it for one purpose only: the value of `ra` during a call.
-/

/-- The number of `Asm` instructions an instruction is translated to. -/
def Instr.size : Instr -> Nat
  | .BI _ _ _ _ _ => 2
  | .Exit         => 2
  | _             => 1

/-- The number of `Asm` instructions a block is translated to. -/
def Block.size (b : Block) : Nat :=
  (b.instrs.map Instr.size).sum

/-- The byte address of block `l` in the translated program. -/
def Label.addr (l : Label) (p : Program) : Word :=
  BitVec.ofNat 32 (4 * ((p.blocks.take l).map Block.size).sum)

/-! ### Operations -/

namespace Program

/-- Execute a single instruction.

Calls keep `ra` in sync with the call stack, so that `Asm` (which only has `ra`) agrees:
- `Call f ret` writes the address of `ret` to `ra`, like the `jal ra, f` it becomes.
- `Ret` is stuck (a fault) unless `ra` holds the address of the block it returns to.
  A function making calls itself must therefore save and restore `ra`, as in real code.

This is the only place the semantics depends on the program `p` (for its layout). -/
def step (p : Program) (s : State) : Instr -> Option State
  | .RI op rd rs1 rs2 =>
      some <| State.next (s.write rd (op.eval (s.read rs1) (s.read rs2)))
  | .II op rd rs1 imm =>
      some <| State.next (s.write rd (op.eval (s.read rs1) imm))
  | .IShI op rd rs1 imm =>
      some <| State.next (s.write rd (op.eval (s.read rs1) imm))
  | .ILI op rd rs1 imm => do
      let v ← op.load s (s.read rs1 + imm.signExtend 32)
      pure <| State.next (s.write rd v)
  | .SI op rs1 rs2 imm => do
      let s' ← op.store s (s.read rs1 + imm.signExtend 32) (s.read rs2)
      pure <| State.next s'
  | .BI op rs1 rs2 tt tf =>
      if op.eval (s.read rs1) (s.read rs2)
      then some (jump s tt)
      else some (jump s tf)
  | .J t => some (jump s t)
  | .Call f ret =>
      some (jump (State.push (s.write .ra (ret.addr p)) ret) f)
  | .Ret =>
      match s.pc.callstack with
      | [] => none
      | ret :: rest =>
        if s.read .ra = ret.addr p
        then some { s with pc := ⟨ret, 0, rest⟩ }
        else none
  | .LUI rd imm =>
      some <| State.next (s.write rd (imm ++ 0#12))
  | .ECall  => none
  | .Exit   => none

/-!
### Runs
Mirrors `Asm`: `Step`, its reflexive transitive closure `Step.Star`, and an executable `run`.
-/

/-- `Step p s s'` means that in program `p`, `s'` is the successor state of state `s`. -/
def Step (p : Program) (s s' : State) : Prop :=
  ∃ i, p.fetch s.pc = some i ∧ step p s i = some s'

/-- Transitive reflexive closure of `Step` -/
inductive Step.Star (p : Program) : State -> State -> Prop
  | refl (s) : Step.Star p s s
  | step {s s'} : Step p s s' -> Step.Star p s s'
  | trans {s t s'} : Step.Star p s t -> Step.Star p t s' -> Step.Star p s s'

/-- Prepend a single step to a run. -/
theorem Step.Star.head {p : Program} {s t u : State} (i : Instr)
    (hf : p.fetch s.pc = some i) (hs : Sym.Program.step p s i = some t) (h : Step.Star p t u) :
    Step.Star p s u :=
  .trans (.step ⟨i, hf, hs⟩) h

/-!
### Termination
A `Sym` program terminates by executing `Exit`, with the exit code in `a0`.
Getting stuck any other way (`ECall`, faulting memory accesses, `Ret` with an
empty call stack or a clobbered `ra`) is a fault.
-/

/-- `s` is a terminal state of `p`: it is about to `Exit`. -/
def Halted (p : Program) (s : State) : Prop :=
  p.fetch s.pc = some .Exit

/-- Started in `s`, program `p` reaches `Exit` with exit code `code`. -/
def Terminates (p : Program) (s : State) (code : Word) : Prop :=
  ∃ s', Step.Star p s s' ∧ Halted p s' ∧ s'.read .a0 = code

/-- Run a program for at most `n` steps, stopping early when execution gets stuck
(including at `Exit`). -/
def run (p : Program) : Nat -> State -> State
  | 0, s => s
  | n + 1, s =>
    match p.fetch s.pc with
    | none => s
    | some i =>
      match step p s i with
      | none => s
      | some s' => run p n s'

/-- `run` is sound: it only follows `Step`s. -/
theorem run_star (p : Program) : ∀ n s, Step.Star p s (run p n s)
  | 0, s => .refl s
  | n + 1, s => by
    unfold run
    split
    · exact .refl s
    · rename_i i hf
      split
      · exact .refl s
      · rename_i s' hs
        exact .trans (.step ⟨i, hf, hs⟩) (run_star p n s')

end Program

end Sym

end Rv32i
