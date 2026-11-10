import Rv32i.Asm

/-!

# `Sym` Language

The sym language is an Abstraction of `Asm` that only allows for symbolic jumps to labels.
Jumping and branching instructions are replaced by relative pseudo instructions.
The restriction to symbolic targets allows for defining programs as (possibly cyclic) graphs.

`Sym` reuses the instruction kinds of `Asm` (`RInstr`, `IInstr`, ...), which map 1-to-1,
but defines its own `Instr`: branch and jump targets are labels, and there is no `jalr`.

System instructions are split by their effect on control flow:
- `ECall` is an ordinary instruction: system calls return to the next instruction.
- `Exit` terminates the program with exit code `a0`.
- `EBreak` is a trap, i.e. a fault.

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
  | EBreak
  | BI (instr : BInstr) (rs1 : Reg) (rs2 : Reg) (ifTrue : Label) (ifFalse : Label)
  | J (target : Label)
  | LUI (rd : Reg) (imm : Imm20)

def Instr.isTerminal : Instr -> Bool
  | .BI _ _ _ _ _ => true
  | .J _        => true
  | .Exit       => true
  | .EBreak     => true
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
  | _ => []

def Block.lsOut (b : Block) : List Label :=
  b.instrs.flatMap Instr.lsOut

structure Program where
  blocks : List Block
  nempty : blocks ≠ []
  wf : ∀ b ∈ blocks, ∀ l ∈ b.lsOut, l < blocks.length

/-- Fetch the instruction at program point `(block, index)`. -/
def Program.fetch (p : Program) (pc : Label × Nat) : Option Instr := do
  let b ← p.blocks[pc.1]?
  b.instrs[pc.2]?

/-!
## Semantics

Other than in `Asm`, we use a symbolic program counter.
This is the core abstraction that `Sym` makes over `Asm`.
-/

abbrev State := Machine.State (Label × Nat)

def State.next (s : State) : State := { s with pc := (s.pc.1, s.pc.2 + 1) }

@[simp] theorem State.next_pc (s : State) : s.next.pc = (s.pc.1, s.pc.2 + 1) := rfl
@[simp] theorem State.next_read (s : State) (r : Reg) : s.next.read r = s.read r := rfl

def jump (s : State) (target : Label) : State :=
  { s with pc := (target, 0) }

def State.initial (s : State) : Prop :=
  s.pc = (0, 0)

/-! ### Operations -/

def step (s : State) : Instr -> Option State
  | .RI op rd rs1 rs2 =>
      some <| State.next (s.write rd (op.eval (s.read rs1) (s.read rs2)))
  | .II op rd rs1 imm =>
      some <| State.next (s.write rd (op.toRInstr.eval (s.read rs1) (imm.signExtend 32)))
  | .IShI op rd rs1 shamt =>
      some <| State.next (s.write rd (op.toRInstr.eval (s.read rs1) (shamt.setWidth 32)))
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
  | .LUI rd imm =>
      some <| State.next (s.write rd (imm ++ 0#12))
  | .ECall  => none
  | .Exit   => none
  | .EBreak => none

end Sym

