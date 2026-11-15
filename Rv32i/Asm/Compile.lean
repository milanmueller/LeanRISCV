import Rv32i.Asm.SmallStep

namespace Rv32i

/-!
# Compiling `Asm` to an assembly file
(Pretty-) printing an `Asm.Program` results in valid RISC-V assembly.

A program `call`s the external functions of its library, so a complete assembly file
also has to contain their code. Printing is therefore parametric over an
`Implementation` of the library: an assembly block for each external function, which is
written to the end of the program under the function's name.
-/

namespace Asm

section
variable (ℓ : Library)

/--
The instructions an external function is implemented with: those of `Asm`, and `ecall`
to reach the operating system. `ecall` is deliberately not part of `Asm.Instr`:
programs only see the outside world through the library's semantics, which the
implementation blocks are trusted to refine.
-/
inductive LibInstr
  | asm (i : Instr ℓ)
  | ecall

instance : ToString (LibInstr ℓ) where
  toString
    | .asm i => toString i
    | .ecall => "ecall"

instance : Coe (Instr ℓ) (LibInstr ℓ) := ⟨.asm⟩

/-- An assembly block for each external function.
A block is entered by `call` with the return address in `ra`, so it ends in `ret`
(unless, like `exit`, it never returns). -/
abbrev Implementation := ℓ.Function → List (LibInstr ℓ)

variable {ℓ}

def Instr.callee : Instr ℓ → Option ℓ.Function
  | .call f => some f
  | _       => none

/-- The external functions called by a program, in order of first use. Functions are
identified by name, as that is what distinguishes their blocks in the assembly file. -/
def Program.externals (p : Program ℓ) : List ℓ.Function :=
  (p.filterMap Instr.callee).foldl
    (fun fs f => if fs.any (toString · == toString f) then fs else fs ++ [f]) []

/--
Render a program as a complete assembly file.
The program is a single `_start` block, so instruction `i` sits at byte offset `4 * i`.
It is followed by a block for each external function it calls, labelled with the
function's name.

Only functions called by the program itself get a block: if an implementation block
calls another external function that the program does not, the file will not link.
 -/
def Program.compile (impl : Implementation ℓ) (p : Program ℓ) : String :=
  let preamble :=
    [ ".option norvc"   -- no compressed instructions: keeps `. + n` offsets exact
    , ".text"           -- following lines are code
    , ".globl _start"   -- export `_start`, the linker's default entry
    , "_start:" ]
  let block (f : ℓ.Function) := s!"{f}:" :: (impl f).map (s!"  {·}")
  let lines := preamble ++ p.map (s!"  {·}") ++ p.externals.flatMap block
  String.intercalate "\n" lines ++ "\n"

end
end Asm

end Rv32i
