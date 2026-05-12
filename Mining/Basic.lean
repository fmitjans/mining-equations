import Mining.Utils
import Mining.Ops
import Mining.Expressions

open Std (HashSet HashMap)
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

    leftNumber?.elim (Result.eq argEq) (fun leftNum =>

      if op == Op.and then (Result.eq argEq) else

      op1.number.elim
        -- if op1 is a variable, move op2 to the left
        (Result.eq (equation op1 left (op.inverse) op2))
        -- else, we have to move op1 to the left
        (fun op1Num => (toResult op2 (op.reverseInverse leftNum op1Num)))
      )

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
  contradictions : (HashSet Equation.Contradiction)

  abbrev Answers := (HashMap Identifier (BitVec 32))


def asCollectionString [ToString α] (list : List α) (brackets : String × String) :=
  let sortedStrings := (list.map toString).mergeSort
  s!"{brackets.fst}\n" ++
  (",\n".intercalate (sortedStrings.map (fun string => s!"  {string}")))
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

  def empty : System := System.mk {} {} [] {} {}

  class SystemAddition (α : Type) where
    add : System → α → System

  export SystemAddition (add)

  instance : SystemAddition Equation where
    add system equation := { system with equations := system.equations.insert equation }

  instance : SystemAddition Identity where
    add system pending := { system with pending := system.pending.concat pending }

  instance : SystemAddition Equation.Contradiction where
    add system contradiction := { system with contradictions := system.contradictions.insert contradiction }

  instance : SystemAddition Equation.Result where
    add system result :=
      match result with
    | Equation.Result.eq newEquation => system.add newEquation
    | Equation.Result.id newIdentity => system.add newIdentity
    | Equation.Result.trivial => system
    | Equation.Result.contradiction (a, b) => system.add (a, b)


  def addAnswer (system : System) (answer : Identity) :=
      { system with answers := system.answers.insert answer.fst answer.snd }

  def addRestriction (system : System) (restriction : Restriction) :=
      { system with restrictions := system.restrictions.insert restriction }


  def applyToEquations (system₀ : System) (processor : Equation → Equation.Result) :=
    let equationsToProcess := system₀.equations
    equationsToProcess.fold
      (init := { system₀ with equations := {} })
      (fun system equation =>
        system.add (processor equation) )

end System


def h1s := [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
    0x5be0cd19]

def h2s := [0x6705d79c, 0xbdf5a4d, 0x9793c992, 0x41a0ad81, 0x1f13094d, 0x78270100, 0x0, 0x0]

def letters := ["a", "b", "c", "d", "e", "f", "g", "h"]

def letters63 := [0x5077abc8, 0x5b24d620, 0x9c50b847, 0xbe6dc7e7, 0xdd219874, 0xe07c2655, 0xa41f32e7, 0xbd43aa60]


namespace Sha256

  def rightRotate [ToTerm α] (n : Nat) (t : α) := Term.op (Unary.rightRotate n) (toTerm t)

  def tripleRotate (identifier : Identifier) (letter : Identifier) (r1 r2 r3 : Nat) :=

    let auxIdentifier : Identifier := ⟨identifier.level, (identifier.symbol ++ ".aux")⟩

    let firstEquation :=
      equation auxIdentifier (rightRotate r1 letter) Op.xor (rightRotate r2 letter)

    let secondEquation :=
      equation identifier auxIdentifier Op.xor (rightRotate r3 letter)

    [firstEquation, secondEquation]

  -- #eval tripleRotate ⟨63, "S1"⟩ ⟨63, "e"⟩ 6 11 25

  def not [ToTerm α] (t : α) := Term.op Unary.not (toTerm t)

  def crossedAnd (level : Nat) :=
    let ⟨ch, ch1, ch2⟩ : onePlusTuple 2 Identifier :=
      (⟨level, "ch"⟩, ⟨level, "ch.1"⟩, ⟨level, "ch.2"⟩)

    let ⟨e, f, g⟩ : onePlusTuple 2 Identifier :=
      (⟨level, "e"⟩, ⟨level, "f"⟩, ⟨level, "g"⟩)

    let equation₁ := equation ch1 e Op.and f
    let equation₂ := equation ch2 (not e) Op.and g
    let finalEquation := equation ch ch1 Op.xor ch2

    [equation₁, equation₂, finalEquation]

  def temp1Equations (level : Nat) :=
    let ⟨temp1, temp1₁, temp1₂, temp1₃⟩ : onePlusTuple 3 Identifier :=
      (⟨level, "temp1"⟩, ⟨level, "temp1.1"⟩, ⟨level, "temp1.2"⟩, ⟨level, "temp1.3"⟩)

    let ⟨h, S1, ch, k, w⟩ : onePlusTuple 4 Identifier :=
      (⟨level, "h"⟩, ⟨level, "S1"⟩, ⟨level, "ch"⟩, ⟨level, "k"⟩, ⟨level, "w"⟩)

    let eq1 := equation temp1₁ h Op.add S1
    let eq2 := equation temp1₂ temp1₁ Op.add ch
    let eq3 := equation temp1₃ temp1₂ Op.add k
    let finalEquation := equation temp1 temp1₃ Op.add w

    [eq1, eq2, eq3, finalEquation]

  def majEquations (level : Nat) :=
    let ⟨maj, maj1, maj2, maj3, maj4⟩ : onePlusTuple 4 Identifier :=
      (⟨level, "maj"⟩, ⟨level, "maj1"⟩, ⟨level, "maj2"⟩, ⟨level, "maj3"⟩, ⟨level, "maj4"⟩)

    let ⟨a, b, c⟩ : onePlusTuple 2 Identifier :=
      (⟨level, "a"⟩, ⟨level, "b"⟩, ⟨level, "c"⟩)

    let eq1 := equation maj1 a Op.and b
    let eq2 := equation maj2 a Op.and c
    let eq3 := equation maj3 b Op.and c
    let eq4 := equation maj4 maj1 Op.xor maj2

    let finalEquation := equation maj maj4 Op.xor maj3

    [eq1, eq2, eq3, eq4, finalEquation]

    def letterIdentifiers (level : Nat) : onePlusTuple 7 Identifier :=
      (⟨level, "a"⟩, ⟨level, "b"⟩, ⟨level, "c"⟩, ⟨level, "d"⟩,
       ⟨level, "e"⟩, ⟨level, "f"⟩, ⟨level, "g"⟩, ⟨level, "h"⟩)

    def letterReasignEquations (level : Nat) :=

      let ⟨a, b, c, d, e, f, g, h⟩ : onePlusTuple 7 Identifier :=
        letterIdentifiers level

      let ⟨a2, b2, c2, d2, e2, f2, g2, h2⟩ : onePlusTuple 7 Identifier :=
        letterIdentifiers (level + 1)

      let ⟨temp1, temp2⟩ : onePlusTuple 1 Identifier :=
        (⟨level, "temp1"⟩, ⟨level, "temp2"⟩)

      [
        Equation.equality h2 g,
        Equation.equality g2 f,
        Equation.equality f2 e,
        equation e2 d Op.add temp1,
        Equation.equality d2 c,
        Equation.equality c2 b,
        Equation.equality b2 a,
        equation a2 temp1 Op.add temp2,
      ]


    def sha256Equations (level : Nat) :=

      let ⟨a, b, c, d, e, f, g, h⟩ : onePlusTuple 7 Identifier :=
        letterIdentifiers level

      let ⟨S1, ch, temp1, S0, maj, temp2⟩ : onePlusTuple 5 Identifier :=
      (⟨level, "S1"⟩, ⟨level, "ch"⟩, ⟨level, "temp1"⟩,
       ⟨level, "S0"⟩, ⟨level, "maj"⟩, ⟨level, "temp2"⟩)

      let eqsS1 := tripleRotate S1 e 6 11 25
      let eqsch := crossedAnd level
      let eqstemp1 := temp1Equations level
      let eqsS0 := tripleRotate S0 a 2 13 22
      let eqsmaj := majEquations level
      let eqstemp2 := [equation temp2 S0 Op.add maj]
      let eqsLetters := letterReasignEquations level

      eqsS1 ++ eqsch ++ eqstemp1 ++ eqsS0 ++
        eqsmaj ++ eqstemp2 ++ eqsLetters

  def k63 := 0xc67178f2
  def w63 := 0x5e809082


end Sha256


def mySystem := (Sha256.sha256Equations 63).foldl
  (init := System.empty) (fun prev equation => prev.add equation)

#eval mySystem
#eval mySystem.applyToEquations Equation.balance

-- def letters := [0xfcfbf135, 0x5077abc8, 0x5b24d620, 0x9c50b847, 0xce04b6ce, 0xdd219874, 0xe07c2655,
--     0xa41f32e7].map (fun x => BitVec.ofNat 32 x)

-- #eval letters



-- def res := (List.zip h1s letters).map (fun pair => pair.1 + pair.2)

-- #eval res
-- #eval (List.zip res letters).map (fun pair => pair.1 - pair.2) == h1s
