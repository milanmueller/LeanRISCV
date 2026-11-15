import Rv32i.Library.Core
import Rv32i.Asm.Compile

namespace Rv32i

/-!
# Implementation of the `core` Library
The assembly blocks behind `exit`, `malloc` and `free`, for RV32 Linux.
They are the trusted counterpart of `Library.Core.semantics`.

There is no allocator state: every block is its own anonymous `mmap`, which `free`
`munmap`s again. The mapping starts with a 16 byte header holding its length, and
`malloc` returns the address right after it:

    mapping:  | length | (unused) | block ...
              ^ +0     ^ +4       ^ +16 = result of `malloc`

Linux system calls take their number in `a7` and arguments in `a0`-`a5`, return in `a0`
(an error is a value in `[-4095, -1]`) and preserve all other registers.
-/

namespace Library.Core

open Asm (LibInstr Imm12)

private abbrev I := LibInstr Library.core

private def li (rd : Reg) (imm : Imm12) : I := .asm (.II .addi rd .zero imm)
private def addi (rd rs1 : Reg) (imm : Imm12) : I := .asm (.II .addi rd rs1 imm)
private def ret : I := .asm (.ret _)

/-- Branch / jump offsets below are in units of 2 bytes: `2 * n` skips `n` instructions. -/
def implementation : Asm.Implementation Library.core
  | .exit =>
    [ li .a7 93                         --      a7 := SYS_exit
    , .ecall ]                          --      exit(a0), does not return
  | .malloc =>
    [ .asm (.BI .beq .a0 .zero (2 * 15)) --  0: size = 0: fail
    , addi .a1 .a0 16                   --  1: length := size + header
    , .asm (.BI .bltu .a1 .a0 (2 * 13)) --  2: length overflowed: fail
    , li .a0 0                          --  3: addr   := NULL (kernel chooses)
    , li .a2 3                          --  4: prot   := PROT_READ | PROT_WRITE
    , li .a3 0x22                       --  5: flags  := MAP_PRIVATE | MAP_ANONYMOUS
    , li .a4 (-1)                       --  6: fd     := -1
    , li .a5 0                          --  7: offset := 0
    , li .a7 222                        --  8: a7 := SYS_mmap2
    , .ecall                            --  9: a0 := mmap2(a0, a1, a2, a3, a4, a5)
    , .asm (.UI .lui .a2 0xFFFFF)       -- 10: a2 := -4096
    , .asm (.BI .bltu .a2 .a0 (2 * 4))  -- 11: a0 in [-4095, -1]: fail
    , .asm (.SI .sw .a0 .a1 0)          -- 12: header := length
    , addi .a0 .a0 16                   -- 13: result := mapping + header
    , .asm (.JI .jal .zero (2 * 2))     -- 14: goto done
    , li .a0 0                          -- 15: fail: result := NULL
    , li .a1 0                          -- 16: done: zero everything we touched
    , li .a2 0
    , li .a3 0
    , li .a4 0
    , li .a5 0
    , li .a7 0
    , ret ]
  | .free =>
    [ .asm (.BI .beq .a0 .zero (2 * 5)) --  0: free(NULL) does nothing
    , .asm (.ILI .lw .a1 .a0 (-16))     --  1: length  := header
    , addi .a0 .a0 (-16)                --  2: mapping := block - header
    , li .a7 215                        --  3: a7 := SYS_munmap
    , .ecall                            --  4: a0 := munmap(a0, a1), 0 on success
    , li .a1 0                          --  5: zero everything we touched
    , li .a7 0
    , ret ]

end Library.Core

end Rv32i
