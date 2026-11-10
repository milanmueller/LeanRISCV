import Rv32i.Machine

/-!
# `Asm` Language
The final language of the compilation/refinement pipeline.
(Pretty-) printing `Asm.Program` results in valid RISC-V assembly.

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

inductive ISysInstr
  | ecall | ebreak
  deriving DecidableEq, BEq, Inhabited

instance : ToString ISysInstr where
  toString : ISysInstr -> String
    | .ecall => "ecall" | .ebreak => "ebreak"

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

/-- Instructions with numeric jump targets.
Branch / jump offsets are in units of 2 bytes (the implicit bit 0 is not encoded),
so an offset `n` means a byte offset of `2 * n` relative to the jumping instruction. -/
inductive Instr
  | RI (instr : RInstr) (rd : Reg) (rs1 : Reg) (rs2 : Reg)
  | II (instr : IInstr) (rd : Reg) (rs1 : Reg) (imm : Imm12)
  | IShI (instr : IShInstr) (rd : Reg) (rs1 : Reg) (imm : Imm5)
  | ILI (instr : ILInstr) (rd : Reg) (rs1 : Reg) (imm : Imm12)
  | ISysI (instr : ISysInstr)
  | SI (instr : SInstr) (rs1 : Reg) (rs2 : Reg) (imm : Imm12)
  | BI (instr : BInstr) (rs1 : Reg) (rs2 : Reg) (offset : Imm12)
  | JI (instr : JInstr) (rd : Reg) (offset : Imm20)
  /-- Jump to the address `rs1 + imm` (bit 0 cleared), storing `pc + 4` in `rd`. -/
  | jalr (rd : Reg) (rs1 : Reg) (imm : Imm12)
  | UI (instr : UInstr) (rd : Reg) (imm : Imm20)

instance : ToString Instr where
  toString : Instr -> String
    | .RI i rd rs1 rs2   => s!"{i} {rd.abiName}, {rs1.abiName}, {rs2.abiName}"
    | .II i rd rs1 imm   => s!"{i} {rd.abiName}, {rs1.abiName}, {imm.toInt}"
    | .IShI i rd rs1 imm => s!"{i} {rd.abiName}, {rs1.abiName}, {imm.toNat}"
    | .ILI i rd rs1 imm  => s!"{i} {rd.abiName}, {imm.toInt}({rs1.abiName})"
    | .ISysI i           => s!"{i}"
    | .SI i rs1 rs2 imm  => s!"{i} {rs2.abiName}, {imm.toInt}({rs1.abiName})"
    | .BI i rs1 rs2 off  => s!"{i} {rs1.abiName}, {rs2.abiName}, . + {2 * off.toInt}"
    | .JI i rd off       => s!"{i} {rd.abiName}, . + {2 * off.toInt}"
    | .jalr rd rs1 imm   => s!"jalr {rd.abiName}, {imm.toInt}({rs1.abiName})"
    | .UI i rd imm       => s!"{i} {rd.abiName}, {imm.toNat}"

/-!
### Programs
Other than in `Sym`, we don't support symbolic targets.
We hence gain nothing from supporting labels and instead model programs
by a flat array of instructions to simplify pc semantics.
-/
abbrev Program := List Instr

/-- Render a program as a complete assembly file.
The program is a single `_start` block, so instruction `i` sits at byte offset `4 * i`.
(No `ToString` instance: `Program` unfolds to `List Instr`, which already has one.) -/
def Program.render (p : Program) : String :=
  let preamble :=
    [ ".option norvc"   -- no compressed instructions: keeps `. + n` offsets exact
    , ".text"           -- following lines are code
    , ".globl _start"   -- export `_start`, the linker's default entry
    , "_start:" ]
  String.intercalate "\n" (preamble ++ p.map (s!"  {·}")) ++ "\n"

/-!
## Semantics
The machine state (registers, memory, pc) is `Machine.State`, shared with `Sym`;
`Asm` uses a byte address as program counter.
-/

/-- `Asm` state: the program counter is a byte address. -/
abbrev State := Machine.State Word


/-!
### Byte-address pc
Control flow on `Asm` states, in the `Asm.State` namespace (`Sym` has its own versions).

Dot notation (`s.next`) only finds these when `s` has type `Asm.State`. The generic
functions `write` and `store` return a `Machine.State Word` instead, for which dot
notation only searches `Machine.State`; on their results, call these as functions:
`State.next (s.write rd v)`.
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

/-- The result of an R-type operation. Shifts only use the low 5 bits of the amount. -/
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

/-- I-type operations are R-type operations with a (sign-extended) immediate operand.
Note that `sltiu` compares against the *sign*-extended immediate, as unsigned. -/
def IInstr.toRInstr : IInstr -> RInstr
  | .addi => .add | .xori => .xor | .ori => .or
  | .andi => .and | .slti => .slt | .sltiu => .sltu

def IShInstr.toRInstr : IShInstr -> RInstr
  | .slli => .sll | .srli => .srl | .srai => .sra

/-- Whether a branch is taken. -/
def BInstr.eval : BInstr -> Word -> Word -> Bool
  | .beq,  a, b => a == b
  | .bne,  a, b => a != b
  | .blt,  a, b => a.slt b
  | .bge,  a, b => !a.slt b
  | .bltu, a, b => a.ult b
  | .bgeu, a, b => !a.ult b

/-- Execute a load from address `a`, extending the result to a full word.
Generic in the pc type, so `Sym` can reuse it. -/
def ILInstr.load {PC : Type} : ILInstr -> Machine.State PC -> Word -> Option Word
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

/-- Execute a single instruction. -/
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
  | .BI op rs1 rs2 off =>
      if op.eval (s.read rs1) (s.read rs2)
      then s.jump (s.pc + (off ++ 0#1).signExtend 32)
      else some s.next
  | .JI .jal rd off =>
      State.jump (s.write rd (s.pc + 4)) (s.pc + (off ++ 0#1).signExtend 32)
  | .jalr rd rs1 imm =>
      -- compute the target before writing `rd`, which may equal `rs1`
      let target := (s.read rs1 + imm.signExtend 32) &&& ~~~1
      State.jump (s.write rd (s.pc + 4)) target
  | .UI .lui rd imm   => some <| State.next (s.write rd (imm ++ 0#12))
  | .UI .auipc rd imm => some <| State.next (s.write rd (s.pc + (imm ++ 0#12)))
  | .ISysI _ => none

/-- Fetch instruction from a Program for given `pc`. -/
def fetch (p : Program) (pc : Word) : Option Instr :=
  if pc % 4 ≠ 0 then none else p[(pc / 4).toNat]?

/--
Core reasoning Definition: `Step p s s'` means that in program `p`,
`s'` is the successor state of state `s`.
-/
def Step (p : Program) (s s' : State) : Prop :=
  ∃ i, fetch p s.pc = some i ∧ step s i = s'

/-- Transitive reflexive closure of `Step` -/
inductive Step.Star (p : Program) : State -> State -> Prop
  | refl (s) : Step.Star p s s
  | step {s s'} : Step p s s' -> Step.Star p s s'
  | trans {s t s'} : Step.Star p s t -> Step.Star p t s' -> Step.Star p s s'

/-!
### Termination
A program terminates by making the Linux `exit` system call: `ecall` with the syscall
number `93` in `a7` and the exit code in `a0` (the OS only reports its low 8 bits).
This is how programs end when run as a process, e.g. under `qemu-riscv32`.

Any other way of getting stuck (`ebreak`, other syscalls, misaligned accesses, running off
the program) is a fault, not termination.
-/

/-- The Linux `exit` syscall number. -/
abbrev sysExit : Word := 93

/-- `s` is a terminal state of `p`: it is about to call `exit`. -/
def Halted (p : Program) (s : State) : Prop :=
  fetch p s.pc = some (.ISysI .ecall) ∧ s.read .a7 = sysExit

/-- Started in `s`, program `p` reaches `exit` with exit code `code`. -/
def Terminates (p : Program) (s : State) (code : Word) : Prop :=
  ∃ s', Step.Star p s s' ∧ Halted p s' ∧ s'.read .a0 = code

/-- Prepend a single step to a run: the workhorse for symbolic execution in proofs. -/
theorem Step.Star.head {p : Program} {s t u : State} (i : Instr)
    (hf : fetch p s.pc = some i) (hs : Asm.step s i = some t) (h : Step.Star p t u) :
    Step.Star p s u :=
  .trans (.step ⟨i, hf, hs⟩) h

/-- Run a program for at most `n` steps, stopping early when execution gets stuck
(including at `ecall` / `ebreak`). -/
def run (p : Program) : Nat -> State -> State
  | 0, s => s
  | n + 1, s =>
    match fetch p s.pc with
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

end Asm
