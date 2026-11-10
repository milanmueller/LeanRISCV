/-!
# Registers
-/
abbrev Word := BitVec 32

inductive Reg where
  | zero | ra | sp | gp | tp
  | t0 | t1 | t2
  | s0 | s1
  | a0 | a1 | a2 | a3 | a4 | a5 | a6 | a7
  | s2 | s3 | s4 | s5 | s6 | s7 | s8 | s9 | s10 | s11
  | t3 | t4 | t5 | t6
  deriving DecidableEq, Repr, Inhabited

namespace Reg

/-- Alias for `s0`. -/
abbrev fp : Reg := .s0

/-- The 5-bit hardware encoding of a register. -/
def toBitVec (r : Reg) : BitVec 5 := BitVec.ofNat 5 r.ctorIdx

/-- ABI name, as used in assembly. -/
def abiName : Reg → String
  | zero => "zero" | ra => "ra" | sp => "sp" | gp => "gp" | tp => "tp"
  | t0 => "t0" | t1 => "t1" | t2 => "t2"
  | s0 => "s0" | s1 => "s1"
  | a0 => "a0" | a1 => "a1" | a2 => "a2" | a3 => "a3"
  | a4 => "a4" | a5 => "a5" | a6 => "a6" | a7 => "a7"
  | s2 => "s2" | s3 => "s3" | s4 => "s4" | s5 => "s5" | s6 => "s6"
  | s7 => "s7" | s8 => "s8" | s9 => "s9" | s10 => "s10" | s11 => "s11"
  | t3 => "t3" | t4 => "t4" | t5 => "t5" | t6 => "t6"

instance : ToString Reg := ⟨abiName⟩

/-!
## Register subsets
-/

/-- Registers that may be used as destination of ordinary operations by convention.
Excluded are the special-purpose registers:
`zero` (writes are discarded), `ra` (return address), `sp`, `gp` and `tp`. -/
def isDest : Reg -> Bool
  | zero | ra | sp | gp | tp => false
  | _ => true

end Reg

abbrev TReg := { r : Reg // r.isDest }

instance : Coe TReg Reg := ⟨Subtype.val⟩
