import Rv32i.Asm

/-!
# `Sym` Language
The sym language is an Abstraction of `Asm` that only allows for symbolic jumps to labels.
To do so, jumping and branching instructions are replaced by relative pseudo instructions.
The restriction to symbolic targets allows for defining programs as (possibly cyclic) graphs.

`Sym` reuses the instruction kinds of `Asm` (`RInstr`, `IInstr`, ...), which map 1-to-1,
but defines its own `Instr`: branch and jump targets are labels, and there is no `jalr`.
-/

open Asm (Imm5 Imm12 Imm20
  RInstr IInstr IShInstr ILInstr ISysInstr SInstr BInstr JInstr UInstr)

namespace Sym

abbrev Label := String

/-- Instructions with symbolic jump targets. -/
inductive Instr
  | RI (instr : RInstr) (rd : Reg) (rs1 : Reg) (rs2 : Reg)
  | II (instr : IInstr) (rd : Reg) (rs1 : Reg) (imm : Imm12)
  | IShI (instr : IShInstr) (rd : Reg) (rs1 : Reg) (imm : Imm5)
  | ILI (instr : ILInstr) (rd : Reg) (rs1 : Reg) (imm : Imm12)
  | ISysI (instr : ISysInstr)
  | SI (instr : SInstr) (rs1 : Reg) (rs2 : Reg) (imm : Imm12)
  | BI (instr : BInstr) (rs1 : Reg) (rs2 : Reg) (target : Label)
  | JI (instr : JInstr) (rd : Reg) (target : Label)
  | UI (instr : UInstr) (rd : Reg) (imm : Imm20)

instance : ToString Instr where
  toString : Instr -> String
    | .RI i rd rs1 rs2   => s!"{i} {rd.abiName}, {rs1.abiName}, {rs2.abiName}"
    | .II i rd rs1 imm   => s!"{i} {rd.abiName}, {rs1.abiName}, {imm.toInt}"
    | .IShI i rd rs1 imm => s!"{i} {rd.abiName}, {rs1.abiName}, {imm.toNat}"
    | .ILI i rd rs1 imm  => s!"{i} {rd.abiName}, {imm.toInt}({rs1.abiName})"
    | .ISysI i           => s!"{i}"
    | .SI i rs1 rs2 imm  => s!"{i} {rs2.abiName}, {imm.toInt}({rs1.abiName})"
    | .BI i rs1 rs2 l    => s!"{i} {rs1.abiName}, {rs2.abiName}, {l}"
    | .JI i rd l         => s!"{i} {rd.abiName}, {l}"
    | .UI i rd imm       => s!"{i} {rd.abiName}, {imm.toNat}"

end Sym
