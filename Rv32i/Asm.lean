import Rv32i.Base

-- Assembly-level language: flat instruction list, numeric (byte) jump offsets

namespace Asm

inductive Instr
  | basic (i : Basic)
  | BI    (op : BInstr) (rs1 rs2 : Reg) (off : Imm13)
  | jal   (rd : Reg) (off : Imm21)
  | jalr  (rd rs1 : Reg) (imm : Imm12)
  | auipc (rd : Reg) (imm : Imm20)
  | ebreak
  deriving DecidableEq, Inhabited

instance : Coe Basic Instr := ⟨.basic⟩

-- Offset relative to the current instruction, e.g. `. + 8` / `. - 8`
private def rel (o : Int) : String := if o < 0 then s!". - {-o}" else s!". + {o}"

instance : ToString Instr where
  toString
    | .basic i           => toString i
    | .BI op rs1 rs2 off => s!"{op} {rs1.abiName}, {rs2.abiName}, {rel off.toInt}"
    | .jal rd off        => s!"jal {rd.abiName}, {rel off.toInt}"
    | .jalr rd rs1 imm   => s!"jalr {rd.abiName}, {imm.toInt}({rs1.abiName})"
    | .auipc rd imm      => s!"auipc {rd.abiName}, {imm.toNat}"
    | .ebreak            => "ebreak"

-- Execution starts at the first instruction
structure Program where
  instrs : List Instr

instance : ToString Program where
  toString p := preamble ++ "\n_start:\n" ++
    String.intercalate "\n" (p.instrs.map (s!"  {·}")) ++ "\n"

end Asm
