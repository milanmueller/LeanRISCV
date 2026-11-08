-- Registers
abbrev Word := BitVec 32
abbrev Reg  := BitVec 5

namespace Reg

  -- ABI names
  def zero : Reg := 0
  def ra   : Reg := 1
  def sp   : Reg := 2
  def gp   : Reg := 3
  def tp   : Reg := 4
  def t0   : Reg := 5
  def t1   : Reg := 6
  def t2   : Reg := 7
  def s0   : Reg := 8
  def fp   : Reg := 8  -- alias for s0
  def s1   : Reg := 9
  def a0   : Reg := 10
  def a1   : Reg := 11
  def a2   : Reg := 12
  def a3   : Reg := 13
  def a4   : Reg := 14
  def a5   : Reg := 15
  def a6   : Reg := 16
  def a7   : Reg := 17
  def s2   : Reg := 18
  def s3   : Reg := 19
  def s4   : Reg := 20
  def s5   : Reg := 21
  def s6   : Reg := 22
  def s7   : Reg := 23
  def s8   : Reg := 24
  def s9   : Reg := 25
  def s10  : Reg := 26
  def s11  : Reg := 27
  def t3   : Reg := 28
  def t4   : Reg := 29
  def t5   : Reg := 30
  def t6   : Reg := 31
  
  -- Printing 
  def abiNames : Array String := #[
      "zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2",
      "s0", "s1", "a0", "a1", "a2", "a3", "a4", "a5",
      "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7",
      "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6"
  ]
  def xName (r : Reg) : String := s!"x{r.toNat}"
  def abiName (r : Reg) : String := abiNames[r.toNat]!

end Reg
