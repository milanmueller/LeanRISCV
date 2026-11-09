import Rv32i.Register

-- Operations, immediates and straight-line instructions shared by `Sym` and `Asm`

abbrev Imm5  := BitVec 5
abbrev Imm12 := BitVec 12
abbrev Imm20 := BitVec 20
-- Branch / jump byte offsets; bit 0 is implicit (always 0) and not encoded.
abbrev Imm13 := BitVec 13
abbrev Imm21 := BitVec 21

inductive RInstr
  | add | sub | sll | slt | sltu | xor | srl | sra | or | and
  deriving DecidableEq, Inhabited

instance : ToString RInstr where
  toString
    | .add => "add" | .sub => "sub" | .sll => "sll" | .slt => "slt"
    | .sltu => "sltu" | .xor => "xor" | .srl => "srl" | .sra => "sra"
    | .or => "or" | .and => "and"

-- Register-immediate arithmetic (`jalr` is handled separately as a jump)
inductive IInstr
  | addi | xori | ori | andi | slti | sltiu
  deriving DecidableEq, Inhabited

instance : ToString IInstr where
  toString
    | .addi => "addi" | .xori => "xori" | .ori => "ori" | .andi => "andi"
    | .slti => "slti" | .sltiu => "sltiu"

-- Loads are I-Type, but printed as `lw rd, imm(rs1)`
inductive ILInstr
  | lb | lh | lw | lbu | lhu
  deriving DecidableEq, Inhabited

instance : ToString ILInstr where
  toString
    | .lb => "lb" | .lh => "lh" | .lw => "lw" | .lbu => "lbu" | .lhu => "lhu"

-- Shifts by immediate only take a 5 bit shift amount
inductive IShInstr
  | slli | srli | srai
  deriving DecidableEq, Inhabited

instance : ToString IShInstr where
  toString
    | .slli => "slli" | .srli => "srli" | .srai => "srai"

inductive SInstr
  | sb | sh | sw
  deriving DecidableEq, Inhabited

instance : ToString SInstr where
  toString
    | .sb => "sb" | .sh => "sh" | .sw => "sw"

inductive BInstr
  | beq | bne | blt | bge | bltu | bgeu
  deriving DecidableEq, Inhabited

instance : ToString BInstr where
  toString
    | .beq => "beq" | .bne => "bne" | .blt => "blt" | .bge => "bge"
    | .bltu => "bltu" | .bgeu => "bgeu"

-- Straight-line instructions, valid in both `Sym` and `Asm`
inductive Basic
  | RI   (op : RInstr)   (rd rs1 rs2 : Reg)
  | II   (op : IInstr)   (rd rs1 : Reg) (imm : Imm12)
  | ILI  (op : ILInstr)  (rd rs1 : Reg) (imm : Imm12)
  | IShI (op : IShInstr) (rd rs1 : Reg) (shamt : Imm5)
  | SI   (op : SInstr)   (rs1 rs2 : Reg) (imm : Imm12)
  | lui  (rd : Reg) (imm : Imm20)
  | ecall
  deriving DecidableEq, Inhabited

instance : ToString Basic where
  toString
    | .RI op rd rs1 rs2   => s!"{op} {rd.abiName}, {rs1.abiName}, {rs2.abiName}"
    | .II op rd rs1 imm   => s!"{op} {rd.abiName}, {rs1.abiName}, {imm.toInt}"
    | .ILI op rd rs1 imm  => s!"{op} {rd.abiName}, {imm.toInt}({rs1.abiName})"
    | .IShI op rd rs1 sh  => s!"{op} {rd.abiName}, {rs1.abiName}, {sh.toNat}"
    | .SI op rs1 rs2 imm  => s!"{op} {rs2.abiName}, {imm.toInt}({rs1.abiName})"
    | .lui rd imm         => s!"lui {rd.abiName}, {imm.toNat}"
    | .ecall              => "ecall"

def preamble : String := String.intercalate "\n"
  [ ".option norvc"   -- no compressed instructions: keeps numeric offsets exact
  , ".text"
  , ".globl _start" ] -- the linker's default entry
