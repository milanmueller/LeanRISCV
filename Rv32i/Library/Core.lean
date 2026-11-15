import Rv32i.Machine

namespace Rv32i

/-!
# Libraries
Real programs speak to the outside world through either linked functions or syscalls.
A `Library` is a collection of external functions alongside axiomatized semantics.

External code only ever sees the pc-free `Machine.Core` (registers and memory), so a
library behaves identically in every language of the pipeline.
-/

structure Library where
  Function : Type
  [toStringFunction : ToString Function]
  World : Type -- Allows libraries to define their own state (e.g. allocated memory).
  semantics : Function → Machine.Core → World → Option (Machine.Core × World)

attribute [instance] Library.toStringFunction

/-!
# The `core` Library
A minimal concrete library: the `exit` syscall, `malloc` and `free`.

The semantics below is the *specification* that the assembly blocks in
`Rv32i.Library.Compile` are trusted to implement; nothing here is proven about them.
Since `Library.semantics` is a function, it has to say exactly what happens to every
register. The blocks are written to make that easy to state: besides the result in `a0`,
every register they touch is zeroed before returning.
-/

namespace Library.Core

inductive Function
  | exit   -- `exit(a0)`: terminate with exit code `a0`
  | malloc -- `a0 := malloc(a0)`
  | free   -- `free(a0)`
  deriving DecidableEq, Repr, Inhabited

instance : ToString Function where
  toString
    | .exit => "exit" | .malloc => "malloc" | .free => "free"

/-- An allocated block: the addresses `[base, base + size)`. -/
structure Block where
  base : Word
  size : Word
  deriving DecidableEq, Repr

namespace Block

/-- `b` is something `malloc` may return: non-null, 16-byte aligned, non-empty,
and it does not wrap around the address space. -/
def valid (b : Block) : Bool :=
  b.base ≠ 0 && b.base.toNat % 16 = 0 && b.size ≠ 0 && b.base.toNat + b.size.toNat ≤ 2 ^ 32

def disjoint (a b : Block) : Bool :=
  a.base.toNat + a.size.toNat ≤ b.base.toNat || b.base.toNat + b.size.toNat ≤ a.base.toNat

end Block

/--
The state of the outside world.

`oracle` is how a deterministic semantics models the allocator's free choice of
addresses: it is the stream of addresses the allocator will propose, of which `malloc`
consumes one per call. Statements about programs quantify over the initial world, and
with it over every possible allocator behaviour.
-/
structure World where
  /-- The exit code, once `exit` has been called. -/
  exit   : Option Word
  /-- The blocks handed out by `malloc` and not yet `free`d. -/
  live   : List Block
  oracle : Nat → Word

/-- A world in which nothing has happened yet. -/
def World.initial (w : World) : Prop :=
  w.exit = none ∧ w.live = []

/-- Zero the given registers. -/
def clear (c : Machine.Core) (rs : List Reg) : Machine.Core :=
  rs.foldl (·.write · 0) c

/--
* `exit` records the exit code `a0` in the world. A real machine stops here; the
  `Machine` model has no notion of halting, so it keeps stepping, but from now on every
  library call is stuck. "The program exits with code `n`" is: it reaches a world with
  `exit = some n`.
* `malloc` takes the next address `p` proposed by the oracle. If `[p, p + a0)` is a
  valid block disjoint from all live ones, it becomes live and `a0 := p`; otherwise the
  allocation fails with `a0 := 0`. In particular `malloc(0)` fails.
  Memory is left as is: the contents of a fresh block are unspecified.
  Clobbers `a1`-`a5` and `a7`.
* `free` of the null pointer does nothing, `free` of the base of a live block removes it,
  and anything else (double free, pointers not from `malloc`) is stuck.
  Clobbers `a0`, `a1` and `a7`.

The model does not enforce that programs stay within their live blocks; `live` is there
so that this can be demanded on top.
-/
def semantics (f : Function) (c : Machine.Core) (w : World) : Option (Machine.Core × World) :=
  if w.exit.isSome then none else
  match f with
  | .exit => some (c, { w with exit := some (c.read .a0) })
  | .malloc =>
    let b : Block := ⟨w.oracle 0, c.read .a0⟩
    let w := { w with oracle := fun i => w.oracle (i + 1) }
    let c := clear c [.a1, .a2, .a3, .a4, .a5, .a7]
    if b.valid && w.live.all b.disjoint
    then some (c.write .a0 b.base, { w with live := b :: w.live })
    else some (c.write .a0 0, w)
  | .free =>
    let p := c.read .a0
    let c := clear c [.a0, .a1, .a7]
    if p = 0 then some (c, w)
    else if w.live.any (·.base = p)
    then some (c, { w with live := w.live.filter (·.base ≠ p) })
    else none

end Library.Core

/-- The minimal library: `exit`, `malloc` and `free`. -/
@[reducible] def Library.core : Library where
  Function := Core.Function
  World := Core.World
  semantics := Core.semantics

end Rv32i
