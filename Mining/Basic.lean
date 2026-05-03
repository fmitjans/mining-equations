import Std
open Std (HashSet)


def Nat.asBitVec (n : Nat) := BitVec.ofNat 32 n

def Option.both ( a b : (Option α)) : Option (α × α) :=
  a.bind (fun a => b.bind (fun b => some (a, b)))

def HashSet.map {α β} [BEq α] [Hashable α] [BEq β] [Hashable β]
  (f : α → β) (s : Std.HashSet α) : Std.HashSet β :=
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


instance : ToTerm Identifier where
  toTerm (i) := Term.var i


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
  toString identity := s!"id {identity.fst} {identity.snd}"


structure Equation where
  left : Identifier
  right: Expr
deriving BEq, Hashable, Repr

instance : ToString Equation where
  toString
    | Equation.mk identifier expression =>
      s!"{identifier} = {expression}"

def equation [ToExpr α] [ToExpr β] (left : Identifier) (o1 : α) (op : Op) (o2 : β) :=
  Equation.mk left (Expr.mk o1 op o2)

namespace Equation

  def evaluate : Equation → Equation
    | ⟨identifier, expr⟩ => ⟨identifier, expr.evaluate⟩

  def toIdentity : Equation → Option Identity
  | Equation.mk left right => right.number.bind (fun number => some (left, number))

end Equation


def BinEquation := Term × Term × Op × Term
def exampleBinEquation := (Term.value 6, Term.value 4, Op.add, Term.value 2)

class Substitute (α : Type) where
  substitute : α → Identity → α
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
  substitute equation identity := match equation with
  | Equation.mk identifier expr =>
      Equation.mk identifier (substitute expr identity)


structure System where
  equations : (HashSet Equation)
  answers : (HashSet Identity)

instance [BEq α] [Hashable α] [ToString α]: ToString (HashSet α) where
  toString set :=
    ("{ \n") ++
      (",\n".intercalate (set.toList.map (fun element => s!"  {toString element}")))
      ++ "\n}"

instance : ToString System where
  toString system := s!"equations:\n{system.equations}\n" ++
    s!"answers:\n{system.answers}"

namespace System

  def moveAnswers (system : System) : System :=

    system.equations.fold
      (init := {equations := {}, answers := system.answers})

      (fun (acc : System) (equation : Equation) =>
        let identity? := equation.toIdentity
        identity?.elim

        -- If not an identity, add to equations
          (System.mk (acc.equations.insert equation) (acc.answers))

        -- Else add to answers
          (fun identity =>
          System.mk (acc.equations) (acc.answers.insert identity)))


end System

#eval (HashSet.ofList [1, 2, 3]).partition (fun x => x < 3)


def extractIdentifier (expr : Expr) :=
  if let Expr.atom term := expr then
    if let Term.var ident := term then
      some ident else none else none

-- 2 h8 = 0 = 1 h8 + 1 a
-- 1 h8 = 0 - 1 a

def letters := ["a", "b", "c", "d", "e", "f", "g", "h"]

def goalEq1 := equation (id 1 "h8") (0x0) Op.sub (id 1 "h")
def goalEq2 := equation (id 1 "h7") (0x0) Op.sub (id 1 "g")
def identity1 := ((id 1 "h"), (0xe07c2655.asBitVec))

def candidate := substitute goalEq1 identity1
#eval candidate.evaluate.toIdentity.get!

def impostor := Equation.mk (id 1 "h") (toExpr 0xe07c2655.asBitVec)
def mySystem : System := System.mk
  (equations := HashSet.ofList [goalEq1, goalEq2, impostor])
  (answers := {})

#eval IO.print mySystem


-- def letters := [0xfcfbf135, 0x5077abc8, 0x5b24d620, 0x9c50b847, 0xce04b6ce, 0xdd219874, 0xe07c2655,
--     0xa41f32e7].map (fun x => BitVec.ofNat 32 x)

-- #eval letters

-- def h1s := [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
--     0x5be0cd19].map (fun x => BitVec.ofNat 32 x)

-- def h2s := [0x6705d79c, 0xbdf5a4d, 0x9793c992, 0x41a0ad81, 0x1f13094d, 0x78270100, 0x0, 0x0]

-- def res := (List.zip h1s letters).map (fun pair => pair.1 + pair.2)

-- #eval res
-- #eval (List.zip res letters).map (fun pair => pair.1 - pair.2) == h1s
