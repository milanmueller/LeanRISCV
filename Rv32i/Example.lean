import Rv32i.Sym

open Sym Basic

-- sum of 1..10, returned as exit code
def example1 : Sym.Program where
  blocks :=
    [ { label := "_start"
        body  := [ II .addi Reg.a0 Reg.zero 0     -- sum := 0
                 , II .addi Reg.t0 Reg.zero 10 ]  -- i := 10
        term  := .j "loop" }
    , { label := "loop"
        body  := [ RI .add Reg.a0 Reg.a0 Reg.t0   -- sum += i
                 , II .addi Reg.t0 Reg.t0 (-1) ]  -- i -= 1
        term  := .BI .bne Reg.t0 Reg.zero "loop" "done" }
    , { label := "done"
        body  := [ II .addi Reg.a7 Reg.zero 93    -- Linux `exit` syscall
                 , ecall ]                        -- exit(a0) = exit(55)
        term  := .ebreak } ]
  nodup  := by decide
  nempty := by simp
  start  := rfl
  wf     := by decide

def main : IO Unit := IO.print (toString example1)
