import Rv32i.Register

namespace Rv32i

/-!
# Machine State
The machine state shared by both the `Sym` and the `Asm` languages of the pipeline:
- A total valuation of registers.
- Byte-addressed memory `Word → BitVec 8` (little-endian, like RISC-V).
- A program counter of type `PC`.

Languages only differ in how they represent the program counter:
`Asm.State := Machine.State Word` (a byte address), `Sym.State` a symbolic program point.
The pc-free part (registers and memory) is its own structure, `Machine.Core`, which
`State PC` extends. External code (see `Library`) only ever sees the `Core`, so it cannot
touch the pc, and behaves identically in every language.

Everything that does not touch the pc is defined on `Core`. Reads are available on a
`State PC` through the parent structure (`s.read r` is `s.toCore.read r`); updates are
lifted to `State PC`, so the result can be updated with `{ s.write rd v with pc := ... }`
in either language. Each lifted update has a simp lemma pushing `toCore` inside.

Language-specific functions on the pc (like `Asm`'s `next` and `jump`) live in their
language's file, but still in the `Machine.State` namespace, restricted to their pc type:
generic functions return a `Machine.State PC`, not e.g. `Asm.State`, so dot notation on
their results only searches `Machine.State`.
-/

namespace Machine

abbrev Byte := BitVec 8

/-- The part of the machine state that is independent of the pc: registers and memory. -/
structure Core where
  regs : Reg → Word
  mem  : Word → Byte

structure State (PC : Type) extends Core where
  pc : PC

namespace Core

/-! ## Registers -/

/-- Read a register; `zero` always reads as `0`. -/
def read (c : Core) (r : Reg) : Word :=
  if r = .zero then 0 else c.regs r

/-- Write a register; writes to `zero` are discarded. -/
def write (c : Core) (rd : Reg) (v : Word) : Core :=
  if rd = .zero then c
  else { c with regs := fun r => if r = rd then v else c.regs r }

/-! Simp lemmas for reasoning about register reads symbolically,
without unfolding the register function. -/

@[simp] theorem read_zero (c : Core) : c.read .zero = 0 := rfl

@[simp] theorem read_write (c : Core) (rd r : Reg) (v : Word) :
    (c.write rd v).read r = if r = .zero then 0 else if r = rd then v else c.read r := by
  unfold write read
  by_cases h : rd = .zero <;> by_cases h' : r = .zero <;> simp_all

/-! ## Memory (little-endian) -/

def load8 (c : Core) (a : Word) : Byte := c.mem a
def load16 (c : Core) (a : Word) : BitVec 16 := c.load8 (a + 1) ++ c.load8 a
def load32 (c : Core) (a : Word) : Word := c.load16 (a + 2) ++ c.load16 a

def store8 (c : Core) (a : Word) (v : Byte) : Core :=
  { c with mem := fun x => if x = a then v else c.mem x }
def store16 (c : Core) (a : Word) (v : BitVec 16) : Core :=
  (c.store8 a (v.extractLsb' 0 8)).store8 (a + 1) (v.extractLsb' 8 8)
def store32 (c : Core) (a : Word) (v : Word) : Core :=
  (c.store16 a (v.extractLsb' 0 16)).store16 (a + 2) (v.extractLsb' 16 16)

end Core

namespace State

variable {PC : Type}

/-! ## Updates, lifted from `Core`
Each keeps the pc and acts on the `Core` only. -/

def write (s : State PC) (rd : Reg) (v : Word) : State PC :=
  { s with toCore := s.toCore.write rd v }

def store8 (s : State PC) (a : Word) (v : Byte) : State PC :=
  { s with toCore := s.toCore.store8 a v }
def store16 (s : State PC) (a : Word) (v : BitVec 16) : State PC :=
  { s with toCore := s.toCore.store16 a v }
def store32 (s : State PC) (a : Word) (v : Word) : State PC :=
  { s with toCore := s.toCore.store32 a v }

@[simp] theorem write_toCore (s : State PC) (rd : Reg) (v : Word) :
    (s.write rd v).toCore = s.toCore.write rd v := rfl
@[simp] theorem store8_toCore (s : State PC) (a : Word) (v : Byte) :
    (s.store8 a v).toCore = s.toCore.store8 a v := rfl
@[simp] theorem store16_toCore (s : State PC) (a : Word) (v : BitVec 16) :
    (s.store16 a v).toCore = s.toCore.store16 a v := rfl
@[simp] theorem store32_toCore (s : State PC) (a : Word) (v : Word) :
    (s.store32 a v).toCore = s.toCore.store32 a v := rfl

@[simp] theorem write_pc (s : State PC) (rd : Reg) (v : Word) : (s.write rd v).pc = s.pc := rfl
@[simp] theorem store8_pc (s : State PC) (a : Word) (v : Byte) : (s.store8 a v).pc = s.pc := rfl
@[simp] theorem store16_pc (s : State PC) (a : Word) (v : BitVec 16) :
    (s.store16 a v).pc = s.pc := rfl
@[simp] theorem store32_pc (s : State PC) (a : Word) (v : Word) : (s.store32 a v).pc = s.pc := rfl

/-- Replace the registers and memory, keeping the pc: how a language continues
after external code has run on the `Core`. -/
def withCore (s : State PC) (c : Core) : State PC := { s with toCore := c }

@[simp] theorem withCore_toCore (s : State PC) (c : Core) : (s.withCore c).toCore = c := rfl
@[simp] theorem withCore_pc (s : State PC) (c : Core) : (s.withCore c).pc = s.pc := rfl

end State

end Machine

end Rv32i
