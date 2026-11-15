import Rv32i.Asm.Basic

namespace Rv32i

/-!

# `Sym` Language

The sym language is an Abstraction of `Asm` that only allows for symbolic jumps to labels.
Jumping and branching instructions are replaced by relative pseudo instructions.
The restriction to symbolic targets allows for defining programs as (possibly cyclic) graphs.

`Sym` reuses the instruction kinds of `Asm` (`RInstr`, `IInstr`, ...), which map 1-to-1.

Function calls are structured: `Call f ret` jumps to `f` and remembers the block `ret` to
continue with on a call stack, `Ret` pops it.
The call stack is part of the symbolic program counter.

-/

/-!
## Syntax
-/

open Asm (Imm5 Imm12 Imm20
  RInstr IInstr IShInstr ILInstr SInstr BInstr)

namespace Sym

/-
`Sym` does not read from, or write into `ra`, as it models control flow through a callstack.
We hence exclude `ra` from the available registers.
-/
abbrev Reg := { r : Rv32i.Reg // r ≠ .ra }

-- Internal unique labels
abbrev Label := Nat

/--
The symbolic program counter: a program point `(block, idx)`.
Callstack is a LIFO queue of Labels.
 -/
structure PC where
  block     : Label
  idx       : Nat
  callstack : List Label
  deriving DecidableEq, Repr

abbrev State := Machine.State PC

-- The Syntax and semantic of `Sym` are parameterized by `Library`, so we fix it here.
section 
variable (ℓ : Library)

/-
Instructions are parameterized over a type `α` of external labels/functions.
The default is in inductive type of selected Syscalls and libc functions with axiomatized semantics.
-/
inductive Instr (α : Type)

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
  | Call (target : α) (ret : Label)
  /-- Return to the block on top of the call stack. -/
  | Ret

def Instr.isTerminal : Instr α → Bool
  | .BI _ _ _ _ _ => true
  | .Jump _ _     => true
  | .Call _ _     => true
  | .Ret          => true
  | _             => false

/-!
### Programs
-/

structure Block (α : Type) where
  instrs : List (Instr α)
  neq    : instrs ≠ []
  term   : (instrs.getLast neq).isTerminal
  wf     : instrs.dropLast.all (fun i => ¬i.isTerminal)

def Instr.lsOut : Instr α → List Label
  | BI _ _ _ t f => [t, f]
  | Jump t _     => [t]
  | _            => []

def Block.lsOut (b : Block α) : List Label :=
  b.instrs.flatMap Instr.lsOut

structure Program (α : Type) where
  blocks : List (Block α)
  nempty : blocks ≠ []
  wf : ∀ b ∈ blocks, ∀ l ∈ b.lsOut, l < blocks.length


def Program.fetch (p : Program α) (pc : PC) : Option (Instr α) := do
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

def push (s : State) (ret : Label) : State :=
  { s with pc := { s.pc with callstack := ret :: s.pc.callstack } }

def initial (s : State) : Prop :=
  s.pc = ⟨0, 0, []⟩

end State

namespace Program

def step (s : State) : Instr α → Option State
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
      then some (s.jump tt)
      else some (s.jump tf)
  | .Jump t r => some ((s.push r).jump t)
  | .Call f ret =>
    -- TODO: Define semantics for `Call`
    s
  | .Ret =>
      match s.pc.callstack with
      | [] => none
      | ret :: rest => some { s with pc := ⟨ret, 0, rest⟩ }

-- Relation view on `step`
def Step (p : Program α) (s s' : State) : Prop :=
  ∃ i, p.fetch s.pc = some i ∧ step s i = some s'

-- Transitive reflexive closure of `Step`
inductive Step.Star (p : Program α) : State → State → Prop
  | refl (s) : Step.Star p s s
  | step {s s'} : Step p s s' → Step.Star p s s'
  | trans {s t s'} : Step.Star p s t → Step.Star p t s' → Step.Star p s s'

/-- Prepend a single step to a run. -/
theorem Step.Star.head {p : Program α} {s t u : State} (i : Instr α)
    (hf : p.fetch s.pc = some i) (hs : Sym.Program.step s i = some t) (h : Step.Star p t u) :
    Step.Star p s u :=
  .trans (.step ⟨i, hf, hs⟩) h

-- Bounded execution
def run (p : Program α) : Nat → State → State
  | 0, s => s
  | n + 1, s =>
    match p.fetch s.pc with
    | none => s
    | some i =>
      match step s i with
      | none => s
      | some s' => run p n s'

theorem run_star (p : Program α) : ∀ n s, Step.Star p s (run p n s)
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
end -- Section with fixed `ℓ : Library`
end Sym
end Rv32i
