import Rv32i.Base

-- Symbolic language: control flow graph of basic blocks, jumps only to labels

abbrev Label := String

namespace Sym

inductive Instr
  | basic (i : Basic)
  | la    (rd : Reg) (l : Label) -- pseudo: rd := address of l
  deriving DecidableEq, Inhabited

instance : Coe Basic Instr := ⟨.basic⟩

-- Block terminators: the only control flow
inductive Term
  | j      (l : Label)
  | BI     (op : BInstr) (rs1 rs2 : Reg) (lThen lElse : Label)
  | call   (f next : Label)          -- pseudo: call f, then continue at `next`
  | jalr   (rd rs1 : Reg) (imm : Imm12)
  | ebreak
  deriving DecidableEq, Inhabited

namespace Term

  def labels : Term → List Label
    | .j l          => [l]
    | .BI _ _ _ t e => [t, e]
    | .call f n     => [f, n]
    | _             => []

  -- Printed with an explicit fall-through jump; layout may drop it later
  def lines : Term → List String
    | .j l              => [s!"j {l}"]
    | .BI op rs1 rs2 t e => [s!"{op} {rs1.abiName}, {rs2.abiName}, {t}", s!"j {e}"]
    | .call f n         => [s!"call {f}", s!"j {n}"]
    | .jalr rd rs1 imm  => [s!"jalr {rd.abiName}, {imm.toInt}({rs1.abiName})"]
    | .ebreak           => ["ebreak"]

end Term

instance : ToString Instr where
  toString
    | .basic i => toString i
    | .la rd l => s!"la {rd.abiName}, {l}"

structure Block where
  label : Label
  body  : List Instr
  term  : Term

namespace Block

  def labelsOut (b : Block) : List Label :=
    b.body.filterMap (fun | .la _ l => some l | _ => none) ++ b.term.labels

  instance : ToString Block where
    toString b := String.intercalate "\n" <|
      s!"{b.label}:" :: (b.body.map toString ++ b.term.lines).map (s!"  {·}")

end Block

structure Program where
  blocks : List Block
  nodup  : (blocks.map (·.label)).Nodup
  nempty : blocks ≠ []
  start  : (blocks.head nempty).label = "_start"
  wf     : ∀ b ∈ blocks, ∀ l ∈ b.labelsOut, l ∈ blocks.map (·.label)

instance : ToString Program where
  toString p := preamble ++ "\n" ++ String.intercalate "\n\n" (p.blocks.map toString) ++ "\n"

end Sym
