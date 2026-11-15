import Rv32i.Library.Core

namespace Rv32i

/-!
# `Asm` Language
The final language of the compilation/refinement pipeline.
(Pretty-) printing `Asm.Program` results in valid RISC-V assembly (see `Asm.Compile`).

Jump targets are numeric, pc-relative offsets, and `jalr` jumps to a computed address.
The instruction kinds (`RInstr`, `IInstr`, ...) defined here are shared with `Sym`.
-/

namespace Asm

/-!
## Instruction Types
-/

abbrev Imm5  := BitVec 5
abbrev Imm12 := BitVec 12
abbrev Imm20 := BitVec 20

inductive RInstr
  | add | sub | sll | slt | sltu | xor | srl | sra | or | and
  deriving DecidableEq, BEq, Inhabited

instance : ToString RInstr where
  toString : RInstr -> String
    | .add => "add" | .sub => "sub" | .sll => "sll" | .slt => "slt"
    | .sltu => "sltu" | .xor => "xor" | .srl => "srl" | .sra => "sra"
    | .or => "or" | .and => "and"

inductive IInstr
  | addi | xori | ori | andi | slti | sltiu
  deriving DecidableEq, BEq, Inhabited

instance : ToString IInstr where
  toString : IInstr -> String
    | .addi => "addi" | .xori => "xori" | .ori => "ori"
    | .andi => "andi" | .slti => "slti" | .sltiu => "sltiu"

inductive IShInstr
  | slli | srli | srai
  deriving DecidableEq, BEq, Inhabited

instance : ToString IShInstr where
  toString : IShInstr -> String
    | .slli => "slli" | .srli => "srli" | .srai => "srai"

inductive ILInstr
  | lb | lh | lw | lbu | lhu
  deriving DecidableEq, BEq, Inhabited

instance : ToString ILInstr where
  toString : ILInstr -> String
    | .lb => "lb" | .lh => "lh" | .lw => "lw"
    | .lbu => "lbu" | .lhu => "lhu"

inductive SInstr
  | sb | sh | sw
  deriving DecidableEq, BEq, Inhabited

instance : ToString SInstr where
  toString : SInstr -> String
    | .sb => "sb" | .sh => "sh" | .sw => "sw"

inductive BInstr
  | beq | bne | blt | bge | bltu | bgeu
  deriving DecidableEq, BEq, Inhabited

instance : ToString BInstr where
  toString : BInstr -> String
    | .beq => "beq" | .bne => "bne" | .blt => "blt" | .bge => "bge"
    | .bltu => "bltu" | .bgeu => "bgeu"

inductive JInstr
  | jal
  deriving DecidableEq, BEq, Inhabited

instance : ToString JInstr where
  toString : JInstr -> String
    | .jal => "jal"

inductive UInstr
  | lui | auipc
  deriving DecidableEq, BEq, Inhabited

instance : ToString UInstr where
  toString : UInstr -> String
    | .lui => "lui" | .auipc => "auipc"

/-!
## Instructions
-/

section
variable (ℓ : Library)

/-- Instructions with numeric jump targets.
Branch / jump offsets are in units of 2 bytes (the implicit bit 0 is not encoded),
so an offset `n` means a byte offset of `2 * n` relative to the jumping instruction. -/
inductive Instr
  | RI (instr : RInstr) (rd : Reg) (rs1 : Reg) (rs2 : Reg)
  | II (instr : IInstr) (rd : Reg) (rs1 : Reg) (imm : Imm12)
  | IShI (instr : IShInstr) (rd : Reg) (rs1 : Reg) (imm : Imm5)
  | ILI (instr : ILInstr) (rd : Reg) (rs1 : Reg) (imm : Imm12)
  | SI (instr : SInstr) (rs1 : Reg) (rs2 : Reg) (imm : Imm12)
  | BI (instr : BInstr) (rs1 : Reg) (rs2 : Reg) (offset : Imm12)
  | JI (instr : JInstr) (rd : Reg) (offset : Imm20)
  | UI (instr : UInstr) (rd : Reg) (imm : Imm20)
  | jalr (rd : Reg) (rs1 : Reg) (imm : Imm12)
  -- Pseudo insructions we use in `Asm`
  | call (target : ℓ.Function) -- Calling external functions

instance : ToString (Instr ℓ) where
  toString : (Instr ℓ) -> String
    | .RI i rd rs1 rs2   => s!"{i} {rd.abiName}, {rs1.abiName}, {rs2.abiName}"
    | .II i rd rs1 imm   => s!"{i} {rd.abiName}, {rs1.abiName}, {imm.toInt}"
    | .IShI i rd rs1 imm => s!"{i} {rd.abiName}, {rs1.abiName}, {imm.toNat}"
    | .ILI i rd rs1 imm  => s!"{i} {rd.abiName}, {imm.toInt}({rs1.abiName})"
    | .SI i rs1 rs2 imm  => s!"{i} {rs2.abiName}, {imm.toInt}({rs1.abiName})"
    | .BI i rs1 rs2 off  => s!"{i} {rs1.abiName}, {rs2.abiName}, . + {2 * off.toInt}"
    | .JI i rd off       => s!"{i} {rd.abiName}, . + {2 * off.toInt}"
    | .UI i rd imm       => s!"{i} {rd.abiName}, {imm.toNat}"
    | .jalr rd rs1 imm   => s!"jalr {rd.abiName}, {imm.toInt}({rs1.abiName})"
    -- not the `call` pseudo instruction, which the assembler expands to 8 bytes
    | .call target       => s!"jal ra, {target}"

/-- The `ret` pseudo instruction: return to the caller, i.e. jump to the address in `ra`. -/
abbrev Instr.ret : (Instr ℓ) := .jalr .zero .ra 0

/-!
### Programs
-/

abbrev Program := List (Instr ℓ)

-- From here on the library is inferred from the program / instruction.
variable {ℓ}

/-!
## Semantics
The machine state (registers, memory, pc) is `Machine.State`, shared with `Sym`;
`Asm` uses a byte address as program counter.
-/
abbrev State := Machine.State Word

/-!
### Byte-address pc
-/

/-- Continue with the next instruction. -/
def State.next (s : State) : State := { s with pc := s.pc + 4 }

@[simp] theorem State.next_pc (s : State) : (State.next s).pc = s.pc + 4 := rfl
@[simp] theorem State.next_read (s : State) (r : Reg) :
    (State.next s).read r = s.read r := rfl

/-- Jump to `target`, getting stuck if it is not 4-byte aligned. -/
def State.jump (s : State) (target : Word) : Option State :=
  if target.toNat % 4 = 0 then some { s with pc := target } else none

def State.initial (s : State) : Prop :=
  s.pc = 0

/-! ### Operations -/

def RInstr.eval : RInstr -> Word -> Word -> Word
  | .add,  a, b => a + b
  | .sub,  a, b => a - b
  | .sll,  a, b => a.shiftLeft (b.toNat % 32)
  | .slt,  a, b => if a.slt b then 1 else 0
  | .sltu, a, b => if a.ult b then 1 else 0
  | .xor,  a, b => a.xor b
  | .srl,  a, b => a.ushiftRight (b.toNat % 32)
  | .sra,  a, b => a.sshiftRight (b.toNat % 32)
  | .or,   a, b => a.or b
  | .and,  a, b => a.and b

def IInstr.eval : IInstr -> Word -> Imm12 -> Word
  | .addi,  rs, imm => rs + imm.signExtend 32
  | .xori,  rs, imm => rs.xor (imm.signExtend 32)
  | .ori,   rs, imm => rs.or (imm.signExtend 32)
  | .andi,  rs, imm => rs.and (imm.signExtend 32)
  | .slti,  rs, imm => if rs.slt (imm.signExtend 32) then 1 else 0
  | .sltiu, rs, imm => if rs.ult (imm.signExtend 32) then 1 else 0

def IShInstr.eval : IShInstr -> Word -> Imm5 -> Word
  | .slli, rs, imm => rs.shiftLeft (imm.toNat)
  | .srli, rs, imm => rs.ushiftRight (imm.toNat)
  | .srai, rs, imm => rs.sshiftRight (imm.toNat)

/-- Whether a branch is taken. -/
def BInstr.eval : BInstr -> Word -> Word -> Bool
  | .beq,  a, b => a == b
  | .bne,  a, b => a != b
  | .blt,  a, b => a.slt b
  | .bge,  a, b => !a.slt b
  | .bltu, a, b => a.ult b
  | .bgeu, a, b => !a.ult b

/-- The number of bytes a load reads. -/
def ILInstr.width : ILInstr -> Nat
  | .lb | .lbu => 1
  | .lh | .lhu => 2
  | .lw        => 4

/-- The number of bytes a store writes. -/
def SInstr.width : SInstr -> Nat
  | .sb => 1
  | .sh => 2
  | .sw => 4

/-- Execute a load from address `a`, extending the result to a full word.
Independent of the pc, so `Sym` can reuse it. -/
def ILInstr.load : ILInstr -> Machine.Core -> Word -> Option Word
  | .lb,  s, a => some ((s.load8 a).signExtend 32)
  | .lbu, s, a => some ((s.load8 a).setWidth 32)
  | .lh,  s, a => if a.toNat % 2 = 0 then some ((s.load16 a).signExtend 32) else none
  | .lhu, s, a => if a.toNat % 2 = 0 then some ((s.load16 a).setWidth 32) else none
  | .lw,  s, a => if a.toNat % 4 = 0 then some (s.load32 a) else none

/-- Execute a store of (the low bits of) `v` to address `a`.
Generic in the pc type, so `Sym` can reuse it. -/
def SInstr.store {PC : Type} :
    SInstr -> Machine.State PC -> Word -> Word -> Option (Machine.State PC)
  | .sb, s, a, v => some (s.store8 a (v.setWidth 8))
  | .sh, s, a, v => if a.toNat % 2 = 0 then some (s.store16 a (v.setWidth 16)) else none
  | .sw, s, a, v => if a.toNat % 4 = 0 then some (s.store32 a v) else none

namespace Program

/-- Execute a single instruction. -/
def step (s : State) (w : ℓ.World) : (Instr ℓ) -> Option (State × ℓ.World)
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
  | .BI op rs1 rs2 off =>
      if op.eval (s.read rs1) (s.read rs2)
      then do
        let s' <- s.jump (s.pc + (off ++ 0#1).signExtend 32)
        pure <| (s', w)
      else some (s.next, w)
  | .JI .jal rd off => do
      let s' <- State.jump (s.write rd (s.pc + 4)) (s.pc + (off ++ 0#1).signExtend 32)
      pure <| (s', w)
  | .UI .lui rd imm   => do
    let s' <- State.next (s.write rd (imm ++ 0#12))
    pure (s', w)
  | .UI .auipc rd imm => do
    let s' <- State.next (s.write rd (s.pc + (imm ++ 0#12)))
    pure (s', w)
  | .jalr rd rs1 imm => do
      -- compute the target before writing `rd`, which may equal `rs1`
      let target := (s.read rs1 + imm.signExtend 32) &&& ~~~1
      let s' <- State.jump (s.write rd (s.pc + 4)) target
      pure (s', w)
  | .call target => do
      -- the library only sees registers and memory; we advance the pc ourselves.
      -- Like `jal ra`, the call leaves the return address in `ra`, where the library sees it.
      let (c', w') <- ℓ.semantics target (s.write .ra (s.pc + 4)).toCore w
      pure (State.next (s.withCore c'), w')

/-- Fetch instruction from a Program for given `pc`. -/
def fetch (p : Program ℓ) (pc : Word) : Option (Instr ℓ) :=
  if pc % 4 ≠ 0 then none else p[(pc / 4).toNat]?

/-- Small step relation between a configuration (machine state and library world)
and its successor. -/
def Step (p : Program ℓ) (s s' : State) (w w' : ℓ.World) : Prop :=
  ∃ i, fetch p s.pc = some i ∧ step s w i = some (s', w')

/-- Transitive reflexive closure of `Step` -/
inductive Step.Star (p : Program ℓ) : State -> State -> ℓ.World -> ℓ.World -> Prop
  | refl (s w) : Step.Star p s s w w
  | step {s s' w w'} : Step p s s' w w' -> Step.Star p s s' w w'
  | trans {s t s' w v w'} :
      Step.Star p s t w v -> Step.Star p t s' v w' -> Step.Star p s s' w w'

/-- Prepend a single step to a run: the workhorse for symbolic execution in proofs. -/
theorem Step.Star.head {p : Program ℓ} {s t u : State} {w v x : ℓ.World} (i : Instr ℓ)
    (hf : fetch p s.pc = some i) (hs : Program.step s w i = some (t, v))
    (h : Step.Star p t u v x) : Step.Star p s u w x :=
  .trans (.step ⟨i, hf, hs⟩) h

/-- Bounded execution: run for at most `n` steps, stopping early when execution gets stuck.
Note that `run` does not stop at `ret`. -/
def run (p : Program ℓ) : Nat -> State -> ℓ.World -> State × ℓ.World
  | 0, s, w => (s, w)
  | n + 1, s, w =>
    match fetch p s.pc with
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
end -- Section with `ℓ : Library` variable
end Asm

end Rv32i
