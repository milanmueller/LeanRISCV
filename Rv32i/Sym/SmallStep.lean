import Rv32i.Asm.SmallStep

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
  /-- Return to the block on top of the call stack. -/
  | Ret

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

def push (s : State) (ret : Label) : State :=
  { s with pc := { s.pc with callstack := ret :: s.pc.callstack } }

def initial (s : State) : Prop :=
  s.pc = ⟨0, 0, []⟩

end State

namespace Program

def step (s : State) (w : ℓ.World) : Instr ℓ → Option (State × ℓ.World)
  | .RI op rd rs1 rs2 =>
      some <| (State.next (s.write rd (op.eval (s.read rs1) (s.read rs2))), w)
  | .II op rd rs1 imm =>
      some <| (State.next (s.write rd (op.eval (s.read rs1) imm)), w)
  | .IShI op rd rs1 imm =>
      some <| (State.next (s.write rd (op.eval (s.read rs1) imm)), w)
  | .ILI op rd rs1 imm => do
      let v ← op.load s.toCore (s.read rs1 + imm.signExtend 32)
      pure <| (State.next (s.write rd v), w)
  | .SI op rs1 rs2 imm => do
      let s' ← op.store s (s.read rs1 + imm.signExtend 32) (s.read rs2)
      pure <| (State.next s', w)
  | .BI op rs1 rs2 tt tf =>
      if op.eval (s.read rs1) (s.read rs2)
      then some (s.jump tt, w)
      else some (s.jump tf, w)
  | .Jump t r => some ((s.push r).jump t, w)
  | .Call f ret => do
      -- the library only sees registers and memory; we continue at `ret` ourselves
      let (c', w') <- ℓ.semantics f s.toCore w
      pure (State.jump (s.withCore c') ret, w')
  | .Ret =>
      match s.pc.callstack with
      | [] => none
      | ret :: rest => some ({ s with pc := ⟨ret, 0, rest⟩ }, w)

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
