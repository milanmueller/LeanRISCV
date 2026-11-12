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

/-!
### Runs
Mirrors `Asm`: `Step`, its reflexive transitive closure `Step.Star`, and an executable `run`.
-/

/-- `Step p s s'` means that in program `p`, `s'` is the successor state of state `s`. -/
def Step (p : Program) (s s' : State) : Prop :=
  ∃ i, p.fetch s.pc = some i ∧ step s i = some s'

/-- Transitive reflexive closure of `Step` -/
inductive Step.Star (p : Program) : State -> State -> Prop
  | refl (s) : Step.Star p s s
  | step {s s'} : Step p s s' -> Step.Star p s s'
  | trans {s t s'} : Step.Star p s t -> Step.Star p t s' -> Step.Star p s s'

/-- Prepend a single step to a run. -/
theorem Step.Star.head {p : Program} {s t u : State} (i : Instr)
    (hf : p.fetch s.pc = some i) (hs : Sym.step s i = some t) (h : Step.Star p t u) :
    Step.Star p s u :=
  .trans (.step ⟨i, hf, hs⟩) h

/-!
### Termination
A `Sym` program terminates by executing `Exit`, with the exit code in `a0`.
Getting stuck any other way (`EBreak`, `ECall`, faulting memory accesses) is a fault.
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
      match step s i with
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

/-!
## `Sym` -> `Asm`
Programs are laid out by concatenating their blocks in order, starting at address `0`.
Each `Sym` instruction becomes one or two `Asm` instructions:
- `BI op rs1 rs2 tt tf` becomes `op rs1, rs2, tt` followed by `jal zero, tf`.
- `J t` becomes `jal zero, t`.
- `Exit` becomes `addi a7, zero, 93; ecall` (the Linux `exit` syscall, see `Asm.Halted`).
- Everything else maps 1-to-1.

Labels are resolved to pc-relative offsets. Branches only reach ±4 KiB and `jal` ±1 MiB;
the translation fails (returns `none`) if any jump target is out of range.
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

def relOffset (n : Nat) (pc target : Word) : Option (BitVec n) :=
  let off := (target - pc).extractLsb' 1 n
  if (off ++ 0#1).signExtend 32 = target - pc then some off else none

/-- Translate the instruction at byte address `pc`, failing if a jump target is out of range. -/
def Instr.toAsm (p : Program) (pc : Word) : Instr -> Option (List Asm.Instr)
  | .RI op rd rs1 rs2   => some [.RI op rd rs1 rs2]
  | .II op rd rs1 imm   => some [.II op rd rs1 imm]
  | .IShI op rd rs1 imm => some [.IShI op rd rs1 imm]
  | .ILI op rd rs1 imm  => some [.ILI op rd rs1 imm]
  | .SI op rs1 rs2 imm  => some [.SI op rs1 rs2 imm]
  | .ECall  => some [.ISysI .ecall]
  | .Exit   => some [.II .addi .a7 .zero (Asm.sysExit.setWidth 12), .ISysI .ecall]
  | .EBreak => some [.ISysI .ebreak]
  | .BI op rs1 rs2 tt tf => do
    let offT ← relOffset 12 pc (tt.addr p)
    let offF ← relOffset 20 (pc + 4) (tf.addr p)
    pure [.BI op rs1 rs2 offT, .JI .jal .zero offF]
  | .J t => do
    let off ← relOffset 20 pc (t.addr p)
    pure [.JI .jal .zero off]
  | .LUI rd imm => some [.UI .lui rd imm]

/-- Translate a sequence of instructions, the first of which is at byte address `pc`. -/
def Program.toAsmFrom (p : Program) : Word -> List Instr -> Option Asm.Program
  | _,  []      => some []
  | pc, i :: is => do
    let is' ← i.toAsm p pc
    let rest ← p.toAsmFrom (pc + BitVec.ofNat 32 (4 * i.size)) is
    pure (is' ++ rest)

/-- The maximum number of instructions of an `Asm` program: instruction `k` sits at byte
address `4 * k`, which must fit into a `Word` for `Asm.fetch` to find it. -/
abbrev Program.maxLength : Nat := 2 ^ 30

/-- Translate a `Sym` program to `Asm`, if all jump targets are in range and the result
fits into the address space (at most `Program.maxLength` instructions).
Block `l` starts at byte address `l.addr p`. -/
def Program.Asm (p : Program) : Option Asm.Program := do
  let a ← p.toAsmFrom 0 (p.blocks.flatMap Block.instrs)
  if a.length ≤ Program.maxLength then some a else none

/-! ### Relating `Sym.State` to `Asm.State` -/

def Program.addr (p : Program) (pc : Label × Nat) : Option Word := do
  let b ← p.blocks[pc.1]?
  if pc.2 < b.instrs.length then
    some (pc.1.addr p + BitVec.ofNat 32 (4 * ((b.instrs.take pc.2).map Instr.size).sum))
  else none

def State.Asm (s : State) (p : Program) : Option Asm.State := do
  let pc ← p.addr s.pc
  pure { regs := s.regs, mem := s.mem, pc }

theorem Program.addr_isSome (p : Program) (pc : Label × Nat) :
    (p.addr pc).isSome = (p.fetch pc).isSome := by
  simp only [Program.addr, Program.fetch]
  cases p.blocks[pc.1]? <;> simp
  split <;> simp_all

theorem Program.addr_start (p : Program) (l : Label) (hl : l < p.blocks.length) :
    p.addr (l, 0) = some (l.addr p) := by
  simp [Program.addr, hl, p.blocks[l].neq]

theorem State.Asm_eq_some {s : State} {p : Program} {s' : Asm.State} :
    s.Asm p = some s' ↔
      p.addr s.pc = some s'.pc ∧ s'.regs = s.regs ∧ s'.mem = s.mem := by
  cases s'
  simp only [State.Asm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Machine.State.mk.injEq]
  constructor
  · rintro ⟨pc, h, rfl, rfl, rfl⟩; exact ⟨h, rfl, rfl⟩
  · rintro ⟨h, rfl, rfl⟩; exact ⟨_, h, rfl, rfl, rfl⟩

end Sym
