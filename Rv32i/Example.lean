import Rv32i.Instruction

open Instr in
def startBlock : Block where
  label := "_start"
  body :=
    [ II .addi Reg.a0 Reg.zero 0     -- sum := 0
    , II .addi Reg.t0 Reg.zero 10    -- i := 10
    , JI .jal Reg.zero (.label "loop") ]
  terminated := by simp [Instr.isTerminator]

open Instr in
def loopBlock : Block where
  label := "loop"
  body :=
    [ RI .add Reg.a0 Reg.a0 Reg.t0           -- sum += i
    , II .addi Reg.t0 Reg.t0 (-1)            -- i -= 1
    , BI .bne Reg.t0 Reg.zero (.label "loop") -- while i != 0
    , JI .jal Reg.zero (.label "done") ]
  terminated := by simp [Instr.isTerminator]

open Instr in
def doneBlock : Block where
  label := "done"
  body :=
    [ II .addi Reg.a7 Reg.zero 93    -- Linux `exit` syscall
    , ISysI .ecall Reg.zero Reg.zero -- exit(a0) = exit(55)
    , ISysI .ebreak Reg.zero Reg.zero ]
  terminated := by simp [Instr.isTerminator]

def example1 : Program where
  blocks := [startBlock, loopBlock, doneBlock]
  nodup  := by decide
  nempty := by simp
  start  := by rfl
  wf     := by
    intro b hb l hl
    simp [startBlock, loopBlock, doneBlock] at hb
    rcases hb with rfl | rfl | rfl <;>
      simp_all [Block.labels_out, Instr.label?, startBlock, loopBlock, doneBlock] <;>
      grind

def main : IO Unit := IO.print (toString example1)
