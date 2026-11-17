import Rv32i.Sym.BigStep

namespace Rv32i.Sym

/-!
# Compiling `Sym` to `Asm`

Blocks are laid out one after the other, in order, so block `0` starts at address `0`.
Every `Sym` instruction compiles to a fixed number of `Asm` instructions (`Instr.size`),
which determines where each block starts (`Program.offset`). Symbolic targets become
pc-relative `auipc`/`jalr` pairs (`goto`), so the result is position independent.

## The stack
`Sym`'s stack is kept on the machine stack, growing downwards from `sp`. Each entry is
one word: a spilled word is stored as is, a return block as the address of a landing pad
that jumps to it. `ra` is not a `Sym` register, so it is free as scratch.

`Sym` moves `sp` exactly like the compiled program, and is stuck when it accesses the
memory of the stack, so the two agree on all registers but `ra`, and on all memory but
the stack's. What `Sym` cannot enforce is on the library: external functions have to
preserve `sp`, stay out of the stack's memory, and not depend on `ra`.

## Limits
Address arithmetic wraps around at `2 ^ 32`, so an `auipc`/`jalr` pair reaches every
address from everywhere. A jump is therefore only out of range if its target has no
address at all, i.e. if the compiled program does not fit into the `2 ^ 32` byte address
space; this is the one case in which `Program.compile` fails.

Every jump is compiled to the far form, also the near ones: this keeps the size of an
instruction independent of the layout.
-/

variable {ℓ : Library}

/-- The number of `Asm` instructions an instruction compiles to. -/
def Instr.size : Instr ℓ → Nat
  | .BI ..   => 5
  | .Jump .. => 7
  | .Call .. => 3
  | .Ret     => 3
  | .Push .. => 2
  | .Pop ..  => 2
  | _        => 1

def Block.size (b : Block ℓ) : Nat :=
  (b.instrs.map Instr.size).sum

/-- The number of `Asm` instructions a program compiles to. -/
def Program.size (p : Program ℓ) : Nat :=
  (p.blocks.map Block.size).sum

/-- The index of the first `Asm` instruction of block `l`: its address is `4 * p.offset l`. -/
def Program.offset (p : Program ℓ) (l : Label) : Nat :=
  ((p.blocks.take l).map Block.size).sum

/-- Jump from index `pos`, where the first of the two instructions is placed, to the
instruction at index `target`, using `ra` as scratch.

With `d` the byte distance, `auipc` adds its upper 20 bits to the pc and `jalr` the
lower 12. `jalr` sign extends, so if bit 11 of `d` is set it subtracts `2 ^ 12`, which
the upper part makes up for: `hi ++ 0#12 = d - lo.signExtend 32`, modulo `2 ^ 32`. -/
def goto (pos target : Nat) : List (Asm.Instr ℓ) :=
  let d : Word := BitVec.ofInt 32 (4 * ((target : Int) - pos))
  let lo : Asm.Imm12 := d.extractLsb' 0 12
  let hi : Asm.Imm20 := (d - lo.signExtend 32).extractLsb' 12 20
  [ .UI .auipc .ra hi
  , .jalr .zero .ra lo ]

/-- Compile the instruction placed at index `pos`, where block `l` starts at index `start l`.
Offsets of `BI` and `JI` are in units of 2 bytes: `2 * n` skips `n` instructions. -/
def Instr.compile (start : Label → Nat) (pos : Nat) : Instr ℓ → List (Asm.Instr ℓ)
  | .RI op rd rs1 rs2   => [.RI op rd rs1 rs2]
  | .II op rd rs1 imm   => [.II op rd rs1 imm]
  | .IShI op rd rs1 imm => [.IShI op rd rs1 imm]
  | .ILI op rd rs1 imm  => [.ILI op rd rs1 imm]
  | .SI op rs1 rs2 imm  => [.SI op rs1 rs2 imm]
  -- The branch itself only skips the `goto f`, so its own range does not matter.
  | .BI op rs1 rs2 t f =>
    [ .BI op rs1 rs2 (2 * 3) ] ++     -- 0: taken: goto 3
    goto (pos + 1) (start f) ++       -- 1: goto f
    goto (pos + 3) (start t)          -- 3: goto t
  | .Jump t r =>
    [ .II .addi .sp .sp (-4)          -- 0: grow the stack
    , .JI .jal .ra (2 * 3) ] ++       -- 1: ra := address of 2, goto 4
    goto (pos + 2) (start r) ++       -- 2: landing pad: `Ret` comes back here
    [ .SI .sw .sp .ra 0 ] ++          -- 4: push the landing pad
    goto (pos + 5) (start t)          -- 5: goto t
  -- `call` leaves its return address in `ra`, which is the next instruction.
  | .Call f r =>
    .call f :: goto (pos + 1) (start r)
  | .Ret =>
    [ .ILI .lw .ra .sp 0              -- pop the landing pad
    , .II .addi .sp .sp 4
    , .ret ℓ ]
  | .Push rs =>
    [ .II .addi .sp .sp (-4)
    , .SI .sw .sp rs 0 ]
  | .Pop rd =>
    [ .ILI .lw rd .sp 0
    , .II .addi .sp .sp 4 ]

theorem Instr.length_compile (start : Label → Nat) (pos : Nat) (i : Instr ℓ) :
    (i.compile start pos).length = i.size := by
  cases i <;> rfl

/-- Compile consecutive instructions, the first of which is placed at index `pos`. -/
def compileInstrs (start : Label → Nat) : Nat → List (Instr ℓ) → List (Asm.Instr ℓ)
  | _, [] => []
  | pos, i :: is => i.compile start pos ++ compileInstrs start (pos + i.size) is

/-- Compile consecutive blocks, the first of which is placed at index `pos`. -/
def compileBlocks (start : Label → Nat) : Nat → List (Block ℓ) → List (Asm.Instr ℓ)
  | _, [] => []
  | pos, b :: bs => compileInstrs start pos b.instrs ++ compileBlocks start (pos + b.size) bs

/-- Compile a program, or `none` if it does not fit into the address space: then some
instructions have no address, and jumps to them are out of range. -/
def Program.compile (p : Program ℓ) : Option (Asm.Program ℓ) :=
  if 4 * p.size ≤ 2 ^ 32 then some (compileBlocks p.offset 0 p.blocks) else none


end Rv32i.Sym
