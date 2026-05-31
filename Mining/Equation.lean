import Mining.Expressions

open Utils

-- inductive Identity where
--   | mk : Identifier → (BitVec 32) → Identity
-- deriving Repr, BEq, Hashable
def Identity := Identifier × (BitVec 32)
deriving BEq, Hashable, Repr

instance : Inhabited Identity where
  default := (⟨1, "a"⟩, (0).asBitVec)

instance : ToString Identity where
  toString identity := s!"{identity.fst} = {identity.snd}"


structure Equation where
  left : Term
  op1 : Term
  op : Op
  op2 : Term
deriving BEq, Hashable

instance : ToString Equation where
  toString eq := s!"{eq.left} = {eq.op1} {eq.op} {eq.op2}"

def equation [ToTerm α] [ToTerm β] [ToTerm γ] (left : α) (o1 : β) (op : Op) (o2 : γ) : Equation :=
  Equation.mk (toTerm left) (toTerm o1) op (toTerm o2)

def exampleEquation := equation 6 4 Op.add 2

#eval (toString exampleEquation)

namespace Equation

  def equality [ToTerm α] [ToTerm β] (a : α) (b : β) :=
    equation a b Op.add 0

  abbrev Contradiction := (BitVec 32 × BitVec 32)
  inductive Result where
  | eq : Equation → Result
  | id : Identity → Result
  | trivial : Result
  | contradiction : Contradiction → Result

  instance : ToString Result where
    toString result := match result with
    | Result.eq eq => (toString eq)
    | Result.id ident => (toString ident)
    | Result.trivial => "Trivial"
    | Result.contradiction (a, b) => s!"{a} = {b}"

  def toResult (left : Term) (right : BitVec 32) :=
    match left with
    | Term.var identifier => Result.id (identifier, right)
    | Term.value num =>
        if num == right then Result.trivial else
        Result.contradiction (num, right)
    | Term.op unary innerTerm => toResult
        (innerTerm) (unary.inverse.eval right)

  -- def exampleTerm := (Term.op (rightRotate 4) (Term.var (id 1 "ex")))
  -- #eval toResult exampleTerm 0x12345678


  def evaluate (equation : Equation) : Result :=

    let ⟨left, op1, op, op2⟩ := equation
    let rightExpr := (Expr.mk op1 op op2)
    let rightNumber? := rightExpr.evaluate.number

    rightNumber?.elim (Result.eq equation) (toResult left ·)


  def balance (argEq : Equation) : Result :=

    let ⟨left, op1, op, op2⟩ := argEq
    let leftNumber? := left.number

    leftNumber?.elim (argEq.evaluate) (fun leftNum =>

      if op == Op.and then (argEq.evaluate) else -- skip for now

      op1.number.elim
        -- if op1 is a variable, move op2 to the left
        ((equation op1 left (op.inverse) op2).evaluate)
        -- else, we have to move op1 to the left
        (fun op1Num => (toResult op2 (op.reverseInverse leftNum op1Num)))
      )

  def identifiers (argEq : Equation) : List Identifier :=
    let ⟨left, op1, _, op2⟩ := argEq
    [left.identifier, op1.identifier, op2.identifier].foldl
      (init := []) (fun prev element => prev ++ element.toList)

end Equation


namespace Term
  def substitute (term : Term) (identity : Identity) := match term with
  | Term.var identifier => if identifier == identity.fst then
      Term.value identity.snd else term

  | Term.op unary term => Term.op unary (substitute term identity)

  | Term.value num => Term.value num

end Term

namespace Equation
  def substitute (argEquation : Equation) (identity : Identity) :=
      let ⟨left, op1, op, op2⟩ := argEquation
      let sub := fun (x : Term) => x.substitute identity
      equation (sub left) (sub op1) op (sub op2)
end Equation

class Substitute (α : Type) where
  substitute : α → Identity → α

namespace Identity
  def substitute (identity : Identity) [Substitute α] (a : α) : α :=
    Substitute.substitute a identity
end Identity

open Substitute

def substituteExpr (expr : Expr) (identity : Identity) := match expr with
  | Expr.atom term => Expr.atom (term.substitute identity)
  | Expr.imk op op1 op2 => Expr.mk (substituteExpr op1 identity) op (substituteExpr op2 identity)

instance : Substitute Expr where
  substitute := substituteExpr
