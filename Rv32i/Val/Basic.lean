import Rv32i.Sym.Basic

namespace Rv32i

/-!
# `Val` Language
`Val` is a simple language with basic control constructs (while and if-else)
and a notion of pointers. It compiles to `Sym`.
-/

/-
This Sketch has some issues:
* Stack is unbounded, which would require spilling onto heap
  -> Put that one abstraction higher..
* No notion of termination
* In general, should be closer to `Sym` for easier compilation...
-/

/-!
## Syntax
-/

namespace Val

abbrev Var := String

structure State where
  stack : Var -> Option Word
  heap  : Word -> Option Machine.Byte

inductive Val
  | V (var : Var) | C (const : Word)

inductive Expr
  | const (c : Word)
  | var (v : Var)
  | add (v₁ : Val) (v₂ : Val)
  | sub (v₁ : Val) (v₂ : Val)
  | sll (v₁ : Val) (v₂ : Val)
  | srl (v₁ : Val) (v₂ : Val)
  | sra (v₁ : Val) (v₂ : Val)
  | and (v₁ : Val) (v₂ : Val)
  | or  (v₁ : Val) (v₂ : Val)
  | xor (v₁ : Val) (v₂ : Val)
  | slt (v₁ : Val) (v₂ : Val)
  | ult (v₁ : Val) (v₂ : Val)

inductive Stmt
  | Assign (dst : Var) (e : Expr)
  | Load (addr : Expr) (dst : Var)
  | Store (addr : Expr) (src : Val)
  | If (cond : Val) (sthen : List Stmt) (selse : List Stmt)
  | While (cond : Val) (sbody : List Stmt)
  | Call (proc : String)

structure Procedure where
  name   : String
  stmts  : List Stmt
  params : List Var
  res    : List Var


