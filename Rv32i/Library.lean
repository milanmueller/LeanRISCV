import Rv32i.Machine

namespace Rv32i

/-!
# Libraries
Real programs speak to the outside world through either linked functions or syscalls.
A `Library` is a collection of external functions alongside axiomatized semantics.
-/

open Machine (State)

structure Library where
  Function : Type
  [toStringFunction : ToString Function]
  World : Type -- Allows libraries to define their own state (e.g. allocated memory).
  semantics : Function → State PC → World → Option (State PC × World)

attribute [instance] Library.toStringFunction

end Rv32i
