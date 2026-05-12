import Mining.Ops
import Mining.Utils

open Utils (Option.both)


structure Identifier where
  level : Nat
  symbol : String
deriving BEq, Hashable, Repr

instance : ToString Identifier where
  toString
  | ⟨level, symbol⟩ =>  s!"{level}-{symbol}"

open Identifier


inductive Term where
  | value : BitVec 32 → Term
  | var : Identifier → Term
  | op : Unary → Term → Term
deriving BEq, Hashable, Repr

def termToString : Term → String
    | Term.value b => toString b
    | Term.var v => toString v
    | Term.op u t => s!"{u} {termToString t}"

instance : ToString Term where
  toString := termToString

class ToTerm (α : Type) where
  toTerm : α → Term
open ToTerm
export ToTerm (toTerm)

namespace Term

  def number : Term → Option (BitVec 32)
    | Term.value b => some b
    | Term.op unary term =>
        term.number.elim none (fun num => unary.eval num)
    | _ => none

end Term

instance : ToTerm Nat where
  toTerm n := Term.value n

instance : ToTerm Identifier where
  toTerm (i) := Term.var i

instance : ToTerm Term where
  toTerm := id


inductive Expr where
  | atom : Term → Expr
  | imk (operation : Op) (operand1 operand2 : Expr)
deriving BEq, Hashable, Repr

class ToExpr (α : Type) where
  toExpr : α → Expr
open ToExpr

def exprToString : Expr → String
  | Expr.atom term => toString term
  | Expr.imk op x1 x2 => s!"{exprToString x1} {op} {exprToString x2}"

instance : ToString Expr where
  toString := exprToString

def asExpr [ToExpr α] (a : α) := toExpr a

instance : ToExpr Expr where
  toExpr := id

instance : ToExpr Term where
  toExpr := Expr.atom

instance : ToExpr (BitVec 32) where
  toExpr bv := toExpr (Term.value bv)

instance : ToExpr Nat where
  toExpr n := toExpr (Term.value (BitVec.ofNat 32 n))

instance : ToExpr Identifier where
  toExpr i := toExpr (toTerm i)

namespace Expr

  def mk [ToExpr α] [ToExpr β] (op1 : α) op (op2 : β) :=
    Expr.imk op (toExpr op1) (toExpr op2)

  def number : Expr → Option (BitVec 32)
  | atom term => term.number
  | _ => none

  def numbers : Expr → Option ((BitVec 32) × (BitVec 32))
    | imk _ op1 op2 => Option.both (number op1) (number op2)
    | _ => none

  def evaluate (expr : Expr) : Expr := match expr with
    | imk op _ _ =>
      let nums? := expr.numbers
      nums?.elim expr (fun nums => toExpr (op.eval nums.1 nums.2))

    | _ => expr

end Expr
