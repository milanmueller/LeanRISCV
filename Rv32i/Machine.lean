import Rv32i.Register

/-!
# Machine State
The machine state shared by both the `Sym` and the `Asm` languages of the pipeline:
- A total valuation of registers.
- Byte-addressed memory `Word -> BitVec 8` (little-endian, like RISC-V).
- A program counter of type `PC`.

Languages only differ in how they represent the program counter:
`Asm.State := Machine.State Word` (a byte address), `Sym.State` a symbolic program point.
Everything that does not touch the pc (registers, memory) is defined once, generically
in `PC`, and returns a `State PC` again, so the result can be updated with
`{ s.write rd v with pc := ... }` in either language.

Language-specific functions on the pc (like `Asm`'s `next` and `jump`) live in their
language's file, but still in the `Machine.State` namespace, restricted to their pc type:
generic functions return a `Machine.State PC`, not e.g. `Asm.State`, so dot notation on
their results only searches `Machine.State`.
-/

namespace Machine

structure State (PC : Type) where
  regs : Reg -> Word
  mem  : Word -> BitVec 8
  pc   : PC

namespace State

variable {PC : Type}

/-! ## Registers -/

/-- Read a register; `zero` always reads as `0`. -/
def read (s : State PC) (r : Reg) : Word :=
  if r = .zero then 0 else s.regs r

/-- Write a register; writes to `zero` are discarded. -/
def write (s : State PC) (rd : Reg) (v : Word) : State PC :=
  if rd = .zero then s
  else { s with regs := fun r => if r = rd then v else s.regs r }

/-! Simp lemmas for reasoning about register reads and the pc symbolically,
without unfolding the register function. -/

@[simp] theorem read_zero (s : State PC) : s.read .zero = 0 := rfl

@[simp] theorem read_write (s : State PC) (rd r : Reg) (v : Word) :
    (s.write rd v).read r = if r = .zero then 0 else if r = rd then v else s.read r := by
  unfold write read
  by_cases h : rd = .zero <;> by_cases h' : r = .zero <;> simp_all

@[simp] theorem write_pc (s : State PC) (rd : Reg) (v : Word) : (s.write rd v).pc = s.pc := by
  unfold write; split <;> rfl

/-! ## Memory (little-endian) -/

def load8 (s : State PC) (a : Word) : BitVec 8 := s.mem a
def load16 (s : State PC) (a : Word) : BitVec 16 := s.load8 (a + 1) ++ s.load8 a
def load32 (s : State PC) (a : Word) : Word := s.load16 (a + 2) ++ s.load16 a

def store8 (s : State PC) (a : Word) (v : BitVec 8) : State PC :=
  { s with mem := fun x => if x = a then v else s.mem x }
def store16 (s : State PC) (a : Word) (v : BitVec 16) : State PC :=
  (s.store8 a (v.extractLsb' 0 8)).store8 (a + 1) (v.extractLsb' 8 8)
def store32 (s : State PC) (a : Word) (v : Word) : State PC :=
  (s.store16 a (v.extractLsb' 0 16)).store16 (a + 2) (v.extractLsb' 16 16)

end State

end Machine
