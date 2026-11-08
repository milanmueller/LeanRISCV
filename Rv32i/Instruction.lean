import Rv32i.Register

-- Instructions
abbrev OpCode := BitVec 7
abbrev Funct3 := BitVec 3
abbrev Funct7 := BitVec 7
abbrev Imm5   := BitVec 5
abbrev Imm12  := BitVec 12
abbrev Imm20  := BitVec 20
-- Branch / jump byte offsets; bit 0 is implicit (always 0) and not encoded.
abbrev Imm13  := BitVec 13
abbrev Imm21  := BitVec 21

-- Labels as String
abbrev Label := String
inductive Target
  | label (l : Label) -- Jump to label
  | rel (offset : Int) -- Jump inside current block
  deriving DecidableEq, BEq, Inhabited

instance : ToString Target where
  toString : Target -> String
    | .label l => l
    | .rel offset => s!". + {4 * offset}"

-- Basic Instruction Types

inductive RInstr 
  | add | sub | sll | slt | sltu | xor | srl | sra | or | and
  deriving DecidableEq, BEq, Inhabited

namespace RInstr

  def toString : RInstr -> String
    | .add => "add" | .sub => "sub" | .sll => "sll" | .slt => "slt"
    | .sltu => "sltu" | .xor => "xor" | .srl => "srl" | .sra => "sra"
    | .or => "or" | .and => "and"

  instance : ToString RInstr := ⟨toString⟩

  def opcode : OpCode := 0b0110011

  def funct3 : RInstr -> Funct3
    | add | sub => 0b000
    | sll       => 0b001
    | slt       => 0b010
    | sltu      => 0b011
    | xor       => 0b100
    | srl | sra => 0b101
    | or        => 0b110
    | and       => 0b111

  def funct7 : RInstr -> Funct7
    | sub | sra => 0b0100000
    | _         => 0b0000000

end RInstr

inductive IInstr 
  | addi | xori | ori | andi | slti | sltiu
  | jalr
  deriving DecidableEq, BEq, Inhabited

namespace IInstr

  def toString : IInstr -> String
    | .addi => "addi" | .xori => "xori" | .ori => "ori" | .andi => "andi"
    | .slti => "slti" | .sltiu => "sltiu"
    | .jalr => "jalr"

  instance : ToString IInstr := ⟨toString⟩

  def opcode : IInstr -> OpCode
    | jalr => 0b1100111
    | _    => 0b0010011

  def funct3 : IInstr -> Funct3
    | addi | jalr => 0b000
    | slti        => 0b010
    | sltiu       => 0b011
    | xori        => 0b100
    | ori         => 0b110
    | andi        => 0b111

end IInstr

-- Load instructions are I-Type as well, but they are printed as
-- `lw rd, imm(rs1)`, so we separate them at the type level.

inductive ILInstr
  | lb | lh | lw | lbu | lhu
  deriving DecidableEq, BEq, Inhabited

namespace ILInstr

  def toString : ILInstr -> String
    | .lb => "lb" | .lh => "lh" | .lw => "lw" | .lbu => "lbu" | .lhu => "lhu"

  instance : ToString ILInstr := ⟨toString⟩

  def opcode : OpCode := 0b0000011

  def funct3 : ILInstr -> Funct3
    | lb  => 0b000
    | lh  => 0b001
    | lw  => 0b010
    | lbu => 0b100
    | lhu => 0b101

end ILInstr

-- Instructions `slli`, `srli`, `srai`, `ecall` and `ebreak`
-- are I-Type instructions, but they also indicate (parts of)
-- the immediate's value. Hence we extract them into special 
-- types to differenciate at the type level.

inductive IShInstr
  | slli | srli | srai
  deriving DecidableEq, BEq, Inhabited

namespace IShInstr

  def toString : IShInstr -> String
    | .slli => "slli" | .srli => "srli" | .srai => "srai"

  instance : ToString IShInstr := ⟨toString⟩

  def opcode : OpCode := 0b0010011

  def funct3 : IShInstr -> Funct3
    | slli        => 0b001
    | srli | srai => 0b101

  -- The upper 7 bits of the immediate are fixed per instruction
  def funct7 : IShInstr -> Funct7
    | slli | srli => 0b0000000
    | srai        => 0b0100000

end IShInstr

inductive ISysInstr
  | ecall | ebreak
  deriving DecidableEq, BEq, Inhabited

namespace ISysInstr

  def toString : ISysInstr -> String
    | .ecall => "ecall" | .ebreak => "ebreak"

  instance : ToString ISysInstr := ⟨toString⟩

  def opcode : OpCode := 0b1110011

  def funct3 : Funct3 := 0b000

  def imm12 : ISysInstr -> Imm12
    | ecall  => 0
    | ebreak => 1

end ISysInstr

inductive SInstr
  | sb | sh | sw
  deriving DecidableEq, BEq, Inhabited

namespace SInstr

  def toString : SInstr -> String
    | .sb => "sb" | .sh => "sh" | .sw => "sw"

  instance : ToString SInstr := ⟨toString⟩

  def opcode : OpCode := 0b0100011

  def funct3 : SInstr -> Funct3
    | sb => 0b000
    | sh => 0b001
    | sw => 0b010

end SInstr

inductive BInstr
  | beq | bne | blt | bge | bltu | bgeu
  deriving DecidableEq, BEq, Inhabited

namespace BInstr

  def toString : BInstr -> String
    | .beq => "beq" | .bne => "bne" | .blt => "blt" | .bge => "bge"
    | .bltu => "bltu" | .bgeu => "bgeu"

  instance : ToString BInstr := ⟨toString⟩

  def opcode : OpCode := 0b1100011

  def funct3 : BInstr -> Funct3
    | beq  => 0b000
    | bne  => 0b001
    | blt  => 0b100
    | bge  => 0b101
    | bltu => 0b110
    | bgeu => 0b111

end BInstr

inductive JInstr
  | jal
  deriving DecidableEq, BEq, Inhabited

namespace JInstr

  def toString : JInstr -> String
    | .jal => "jal"

  instance : ToString JInstr := ⟨toString⟩

  def opcode : OpCode := 0b1101111

end JInstr

inductive UInstr
  | lui | auipc
  deriving DecidableEq, BEq, Inhabited

namespace UInstr

  def toString : UInstr -> String
    | .lui => "lui" | .auipc => "auipc"

  instance : ToString UInstr := ⟨toString⟩

  def opcode : UInstr -> OpCode
    | lui   => 0b0110111
    | auipc => 0b0010111

end UInstr

-- Collecting everything into a single `Instr` type for
-- instructions

inductive Instr
  | RI (instr : RInstr) (rd : Reg) (rs1 : Reg) (rs2 : Reg)
  | II (instr : IInstr) (rd : Reg) (rs1 : Reg) (imm : Imm12)
  | ILI (instr : ILInstr) (rd : Reg) (rs1 : Reg) (imm : Imm12)
  | IShI (instr : IShInstr) (rd : Reg) (rs1 : Reg) (imm : Imm5)
  | ISysI (instr : ISysInstr) (rd : Reg) (rs1 : Reg)
  | SI (instr : SInstr) (rs1 : Reg) (rs2 : Reg) (imm : Imm12)
  | BI (instr : BInstr) (rs1 : Reg) (rs2 : Reg) (t : Target)
  | JI (instr : JInstr) (rd : Reg) (t : Target)
  | UI (instr : UInstr) (rd : Reg) (imm : Imm20)

namespace Instr

  def isTerminator : Instr -> Bool
    | .JI _ _ (.label _) => True
    | .II .jalr _ _ _    => True
    | .ISysI .ebreak _ _ => True
    | _ => False

  -- The label this instruction refers to, if any
  def label? : Instr -> Option Label
    | .BI _ _ _ (.label l) => some l
    | .JI _ _ (.label l)   => some l
    | _                    => none

  -- Printing `Instr` should generate valid RISC-V ASM
  instance : ToString Instr where
    toString : Instr -> String
      | .RI i rd rs1 rs2   => s!"{i} {rd.abiName}, {rs1.abiName}, {rs2.abiName}"
      | .II i rd rs1 imm   => s!"{i} {rd.abiName}, {rs1.abiName}, {imm.toInt}"
      | .ILI i rd rs1 imm  => s!"{i} {rd.abiName}, {imm.toInt}({rs1.abiName})"
      | .IShI i rd rs1 imm => s!"{i} {rd.abiName}, {rs1.abiName}, {imm.toNat}"
      | .ISysI i _ _       => s!"{i}"
      | .SI i rs1 rs2 imm  => s!"{i} {rs2.abiName}, {imm.toInt}({rs1.abiName})"
      | .BI i rs1 rs2 t    => s!"{i} {rs1.abiName}, {rs2.abiName}, {t}"
      | .JI i rd t         => s!"{i} {rd.abiName}, {t}"
      | .UI i rd imm       => s!"{i} {rd.abiName}, {imm.toNat}"

end Instr

structure Block where
  label : Label
  body : List Instr
  terminated : body ≠ [] ∧ body.getLast?.any Instr.isTerminator

namespace Block

  -- All labels this block may jump to
  def labels_out (b : Block) : List Label := b.body.filterMap Instr.label?

  instance : ToString Block where
    toString (b : Block) : String :=
      let lines := b.body.map fun i => s!"  {i}"
      String.intercalate "\n" (s!"{b.label}:" :: lines)

end Block

structure Program where
  blocks : List Block
  nodup  : (blocks.map (·.label)).Nodup
  nempty : blocks ≠ []
  start  : (blocks.head nempty).label = "_start"
  wf     : ∀ b ∈ blocks, ∀ l ∈ b.labels_out, l ∈ blocks.map (·.label)

instance : ToString Program where
  toString (p : Program) : String :=
    let preamble := String.intercalate "\n"
      [ ".option norvc"   -- no compressed instructions: keeps `Target.rel` offsets exact
      , ".text"           -- following lines are code
      , ".globl _start" ] -- export `_start` (the first block), the linker's default entry
    preamble ++ "\n" ++ String.intercalate "\n\n" (p.blocks.map toString) ++ "\n"
