import Rv32i.Asm

namespace Asm

/-!
### Shorthand constructors
Mnemonics are unique across instruction kinds, so we define one function per mnemonic,
e.g. `Instr.addi rd rs1 imm := Instr.II .addi rd rs1 imm`. This allows writing
`[.addi .a0 .zero 0, .add .a0 .a0 .t0]` instead of `[.II .addi ..., .RI .add ...]`.
The macros take the target namespace (`Asm` or `Sym`), since `Sym.Instr` shares these kinds.
-/

open Lean in
set_option hygiene false in
/-- `shorthandR% Ns add sub ...` defines `Ns.Instr.add (rd rs1 rs2)` etc. -/
macro "shorthandR% " ns:ident ms:ident* : command => do
  let cmds ← ms.mapM fun m =>
    `(@[reducible] def $(mkIdent (ns.getId ++ `Instr ++ m.getId)) (rd rs1 rs2 : Reg) :
        $(mkIdent (ns.getId ++ `Instr)) := .RI $(mkIdent (`Asm ++ `RInstr ++ m.getId)) rd rs1 rs2)
  pure ⟨mkNullNode cmds⟩

open Lean in
set_option hygiene false in
/-- Like `shorthandR%`, for `II` (`(rd rs1) (imm : Imm12)`). -/
macro "shorthandI% " ns:ident ms:ident* : command => do
  let cmds ← ms.mapM fun m =>
    `(@[reducible] def $(mkIdent (ns.getId ++ `Instr ++ m.getId)) (rd rs1 : Reg) (imm : Imm12) :
        $(mkIdent (ns.getId ++ `Instr)) := .II $(mkIdent (`Asm ++ `IInstr ++ m.getId)) rd rs1 imm)
  pure ⟨mkNullNode cmds⟩

open Lean in
set_option hygiene false in
/-- Like `shorthandR%`, for `IShI` (`(rd rs1) (imm : Imm5)`). -/
macro "shorthandISh% " ns:ident ms:ident* : command => do
  let cmds ← ms.mapM fun m =>
    `(@[reducible] def $(mkIdent (ns.getId ++ `Instr ++ m.getId)) (rd rs1 : Reg) (imm : Imm5) :
        $(mkIdent (ns.getId ++ `Instr)) := .IShI $(mkIdent (`Asm ++ `IShInstr ++ m.getId)) rd rs1 imm)
  pure ⟨mkNullNode cmds⟩

open Lean in
set_option hygiene false in
/-- Like `shorthandR%`, for `ILI` (`(rd rs1) (imm : Imm12)`). -/
macro "shorthandIL% " ns:ident ms:ident* : command => do
  let cmds ← ms.mapM fun m =>
    `(@[reducible] def $(mkIdent (ns.getId ++ `Instr ++ m.getId)) (rd rs1 : Reg) (imm : Imm12) :
        $(mkIdent (ns.getId ++ `Instr)) := .ILI $(mkIdent (`Asm ++ `ILInstr ++ m.getId)) rd rs1 imm)
  pure ⟨mkNullNode cmds⟩

open Lean in
set_option hygiene false in
/-- Like `shorthandR%`, for `SI` (`(rs1 rs2) (imm : Imm12)`). -/
macro "shorthandS% " ns:ident ms:ident* : command => do
  let cmds ← ms.mapM fun m =>
    `(@[reducible] def $(mkIdent (ns.getId ++ `Instr ++ m.getId)) (rs1 rs2 : Reg) (imm : Imm12) :
        $(mkIdent (ns.getId ++ `Instr)) := .SI $(mkIdent (`Asm ++ `SInstr ++ m.getId)) rs1 rs2 imm)
  pure ⟨mkNullNode cmds⟩

shorthandR%   Asm add sub sll slt sltu xor srl sra or and
shorthandI%   Asm addi xori ori andi slti sltiu
shorthandISh% Asm slli srli srai
shorthandIL%  Asm lb lh lw lbu lhu
shorthandS%   Asm sb sh sw

namespace Instr
abbrev ecall  : Instr := .ISysI .ecall
abbrev ebreak : Instr := .ISysI .ebreak
abbrev beq  (rs1 rs2 : Reg) (off : Imm12) : Instr := .BI .beq rs1 rs2 off
abbrev bne  (rs1 rs2 : Reg) (off : Imm12) : Instr := .BI .bne rs1 rs2 off
abbrev blt  (rs1 rs2 : Reg) (off : Imm12) : Instr := .BI .blt rs1 rs2 off
abbrev bge  (rs1 rs2 : Reg) (off : Imm12) : Instr := .BI .bge rs1 rs2 off
abbrev bltu (rs1 rs2 : Reg) (off : Imm12) : Instr := .BI .bltu rs1 rs2 off
abbrev bgeu (rs1 rs2 : Reg) (off : Imm12) : Instr := .BI .bgeu rs1 rs2 off
abbrev jal   (rd : Reg) (off : Imm20) : Instr := .JI .jal rd off
abbrev lui   (rd : Reg) (imm : Imm20) : Instr := .UI .lui rd imm
abbrev auipc (rd : Reg) (imm : Imm20) : Instr := .UI .auipc rd imm
end Instr


end Asm
