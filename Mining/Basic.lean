import Std
open Std (HashSet HashMap)


def Nat.asBitVec (n : Nat) := BitVec.ofNat 32 n

def Option.both ( a b : (Option α)) : Option (α × α) :=
  a.bind (fun a => b.bind (fun b => some (a, b)))

def HashSet.map {α β} [BEq α] [Hashable α] [BEq β] [Hashable β]
  (s : Std.HashSet α) (f : α → β) : Std.HashSet β :=
  s.fold (init := ∅) (fun acc x => acc.insert (f x))


inductive Op where
  | add : Op
  | sub : Op
deriving Repr, BEq, Hashable

instance : ToString Op where
  toString op := toString (repr op)

namespace Op

  def binaryOp (T : Type) := T → T → T

  def eval : Op → (binaryOp (BitVec 32))
    | Op.add => BitVec.add
    | Op.sub => BitVec.sub

  def inverse : Op → Op
  | add => sub
  | sub => add

  def commutative : Op → Bool
    | add => true
    | sub => false

  -- a = b op c ↔ c = a rev b
  def reverseInverse (op : Op) (a b : BitVec 32) : BitVec 32 :=
    match op with
    | sub => Op.sub.eval b a
    -- commutative operations:
    | _ => op.inverse.eval a b


end Op


inductive Identifier where
 | id (level : Nat) (symbol : String) : Identifier
deriving BEq, Hashable, Repr

instance : ToString Identifier where
  toString
  | Identifier.id level symbol =>  s!"{level}-{symbol}"

open Identifier


inductive Term where
  | value (b : BitVec 32)
  | var (v : Identifier)
deriving BEq, Hashable, Repr

instance : ToString Term where
  toString
    | Term.value b => toString b
    | Term.var v => toString v

class ToTerm (α : Type) where
  toTerm : α → Term
open ToTerm

namespace Term

  def number : Term → Option (BitVec 32)
    | Term.value b => some b
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


-- inductive Identity where
--   | mk : Identifier → (BitVec 32) → Identity
-- deriving Repr, BEq, Hashable
def Identity := Identifier × (BitVec 32)
deriving BEq, Hashable, Repr

instance : Inhabited Identity where
  default := ((id 1 "a"), (0).asBitVec)

instance : ToString Identity where
  toString identity := s!"{identity.fst} = {identity.snd}"


def Restriction := (BitVec 32) × (BitVec 32)
deriving BEq, Hashable

instance : ToString Restriction where
  toString res := s!"{res.fst} = {res.snd}"


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

  inductive Result where
  | eq : Equation → Result
  | id : Identity → Result
  | re : Restriction → Result

  instance : ToString Result where
    toString result := match result with
    | Result.eq eq => (toString eq)
    | Result.id ident => (toString ident)
    | Result.re res => (toString res)

  def toResult (left : Term) (right : BitVec 32) :=
    match left with
    | Term.var identifier => Result.id (identifier, right)
    | Term.value num => Result.re (num, right)


  def evaluate (equation : Equation) : Result :=

    let rightExpr := (Expr.mk equation.op1 equation.op equation.op2)
    let rightNumber? := rightExpr.evaluate.number
    rightNumber?.elim (Result.eq equation) (fun number =>
      match equation.left with
      | Term.var identifier => Result.id (identifier, number)
      | Term.value leftNum => Result.re (leftNum, number)
    )

  def balance (argEq : Equation) : Result :=
    let ⟨left, op1, op, op2⟩ := argEq
    match left with
    | Term.var _ => Result.eq argEq
    | Term.value nLeft =>
      match op1 with

      | Term.var _ => -- if the first operand is a variable, move second operand to the left
        -- o1 = left op⁻¹ op2
        Result.eq (equation op1 left (op.inverse) op2)

      | Term.value n1 => -- else, we have to move the first one to the left
        (toResult op2 (op.reverseInverse nLeft n1))


end Equation


class Substitute (α : Type) where
  substitute : α → Identity → α

namespace Identity
  def substitute (identity : Identity) [Substitute α] (a : α) : α :=
    Substitute.substitute a identity
end Identity

open Substitute

instance : Substitute Term where
  substitute (term identity) :=
    if let Term.var var := term then
      if var == identity.fst then Term.value identity.snd
      else term
    else term

def substituteExpr (expr : Expr) (identity : Identity) := match expr with
  | Expr.atom term => Expr.atom (substitute term identity)
  | Expr.imk op op1 op2 => Expr.mk (substituteExpr op1 identity) op (substituteExpr op2 identity)

instance : Substitute Expr where
  substitute := substituteExpr

instance : Substitute Equation where
  substitute eq identity :=
    let sub := fun x => substitute x identity
    equation (sub eq.left) (sub eq.op1) eq.op (sub eq.op2)


structure System where
  equations : (HashSet Equation)
  answers : (HashMap Identifier (BitVec 32))
  pending : (List Identity)
  restrictions : (HashSet Restriction)

  abbrev Answers := (HashMap Identifier (BitVec 32))


def asCollectionString [ToString α] (list : List α) (brackets : String × String) :=
  s!"{brackets.fst}\n" ++
  (",\n".intercalate (list.map (fun element => s!"  {toString element}")))
  ++ s!"\n{brackets.snd}"

instance : ToString Answers where
  toString answers := asCollectionString (answers.toList) ("{", "}")

instance [BEq α] [Hashable α] [ToString α]: ToString (HashSet α) where
  toString set := asCollectionString (set.toList) ("{", "}")

instance : ToString (List Identity) where
  toString identities := asCollectionString identities ("[", "]")

instance : ToString System where
  toString system :=
    s!"equations:\n{system.equations}\n" ++
    s!"answers:\n{system.answers}\n" ++
    s!"pending:\n{system.pending}\n" ++
    s!"restrictions:\n{system.restrictions}\n"

namespace System

  def empty : System := System.mk {} {} [] {}

  def addEquation (system : System) (equation : Equation) :=
      { system with equations := system.equations.insert equation }

  def addAnswer (system : System) (answer : Identity) :=
      { system with answers := system.answers.insert answer.fst answer.snd }

  def addPending (system : System) (pending : Identity) :=
      { system with pending := system.pending.concat pending }

  def addRestriction (system : System) (restriction : Restriction) :=
      { system with restrictions := system.restrictions.insert restriction }

  def apply (system : System) (result : Equation.Result) :=
    match result with
    | Equation.Result.eq newEquation => system.addEquation newEquation
    | Equation.Result.id newIdentity => system.addPending newIdentity
    | Equation.Result.re newRestriction => system.addRestriction newRestriction

  def applyToEquations (system₀ : System) (processor : Equation → Equation.Result) :=
    let equationsToProcess := system₀.equations
    equationsToProcess.fold
      (init := { system₀ with equations := {} })
      (fun system equation =>
        system.apply (processor equation) )

end System

#eval (HashSet.ofList [1, 2, 3]).partition (fun x => x < 3)

-- 2 h8 = 0 = 1 h8 + 1 a
-- 1 h8 = 0 - 1 a

def goalEq1 := equation (id 1 "h8") (10) Op.sub (id 1 "h")
def goalEq2 := equation (id 1 "h7") (id 1 "h") Op.sub (id 1 "g")
def identity1 : Identity := ((id 1 "h8"), ((3).asBitVec))
def identity2 : Identity := ((id 1 "h7"), ((3).asBitVec))

#eval goalEq1
#eval identity2.substitute goalEq1
#eval goalEq1.balance
#eval identity1.substitute goalEq1
#eval (identity1.substitute goalEq1).balance

#eval goalEq2
#eval goalEq2.balance
#eval identity2.substitute goalEq2
#eval (identity2.substitute goalEq2).balance


def h1s := [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
    0x5be0cd19]

def h2s := [0x6705d79c, 0xbdf5a4d, 0x9793c992, 0x41a0ad81, 0x1f13094d, 0x78270100, 0x0, 0x0]

def letters := ["a", "b", "c", "d", "e", "f", "g", "h"]

def h1Terms := h1s.map (toTerm ·)
def h2Terms := h2s.map (toTerm ·)
def letterIdentifiers := letters.map (id 1 · )
def letterTerms := letterIdentifiers.map (toTerm ·)

def myEquations := ((h1Terms.zip h2Terms).zip letterTerms).map
  fun tup => equation tup.1.2 tup.1.1 Op.add tup.2

def mySystem := System.mk (HashSet.ofList myEquations) {} [] {}

#eval myEquations
#eval mySystem
#eval myEquations.map (·.balance)
#eval mySystem.applyToEquations Equation.balance

-- def letters := [0xfcfbf135, 0x5077abc8, 0x5b24d620, 0x9c50b847, 0xce04b6ce, 0xdd219874, 0xe07c2655,
--     0xa41f32e7].map (fun x => BitVec.ofNat 32 x)

-- #eval letters



-- def res := (List.zip h1s letters).map (fun pair => pair.1 + pair.2)

-- #eval res
-- #eval (List.zip res letters).map (fun pair => pair.1 - pair.2) == h1s

namespace Afuera

class Adentro (α : Type) where
  adentro := Nat


#check Adentro.adentro
export Adentro (adentro)

end Afuera

#check Afuera.adentro
