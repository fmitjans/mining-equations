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


namespace System
  inductive Steps where
    | balance
    | evaluate
    | substitute
  deriving Repr
end System

instance : ToString System.Steps where toString step := toString (repr step)


structure System where
  equations : HashMap Identifier (HashSet Equation)
  answers : (HashMap Identifier (BitVec 32))
  pending : (List Identity)
  contradictions : (HashSet Equation.Contradiction)
  nextStep : System.Steps
  definitions : List Identity

  abbrev Answers := (HashMap Identifier (BitVec 32))
  abbrev SysEquations := HashMap Identifier (HashSet Equation)


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

instance : ToString SysEquations where
  toString equationsMap :=

    let equationSets : List (HashSet Equation) :=
      equationsMap.toList.map (fun pair => pair.snd)

    let singleSet : HashSet Equation := (equationSets.foldl
      (init := {}) (fun prev newSet => prev.union newSet))

    asCollectionString singleSet.toList ("[", "]")

instance : ToString System where
  toString system :=
    s!"equations:\n{system.equations}\n" ++
    s!"answers:\n{system.answers}\n" ++
    s!"pending:\n{system.pending}\n" ++
    s!"contradictions:\n{system.contradictions}\n" ++
    s!"next step: {system.nextStep}"

namespace System

  def empty : System := System.mk {} {} [] {} Steps.balance []

  class SystemAddition (α : Type) where
    add : System → α → System

  export SystemAddition (add)

  instance : SystemAddition Identity where
    add system pending := { system with pending := system.pending.concat pending }

  instance : SystemAddition Equation.Contradiction where
    add system contradiction := { system with contradictions := system.contradictions.insert contradiction }

  def addUnprocessed (system : System) (argEq : Equation) :=
    let eqIdentifiers := argEq.identifiers
      let newEquations := eqIdentifiers.foldl (init := system.equations)
        (fun prev identifier => insertIntoValue prev identifier argEq)
      {system with equations := newEquations }

  instance : SystemAddition Equation.Result where
    add system result :=
      match result with
    | Equation.Result.eq newEquation => system.addUnprocessed newEquation
    | Equation.Result.id newIdentity => system.add newIdentity
    | Equation.Result.trivial => system
    | Equation.Result.contradiction (a, b) => system.add (a, b)

  instance : SystemAddition Equation where
    add system argEq := system.add argEq.balance


  def addAnswer (system : System) (answer : Identity) :=
      { system with answers := system.answers.insert answer.fst answer.snd }

  def addDefinition (system : System) (definition : Identity) :=
    { system with definitions := system.definitions.insert definition }

  def addList [SystemAddition α] (system : System) (list : List α) :=
    list.foldl (init := system) (fun prev addition => prev.add addition)

  def deleteEquation (system : System) (argEq : Equation) :=
    let newEquations := argEq.identifiers.foldl (init := system.equations)
      (fun prevEqs identifier =>
        prevEqs.modify identifier (fun prevSet => prevSet.erase argEq))

    { system with equations := newEquations }

  -- def applyToEquations (system₀ : System) (processor : Equation → Equation.Result) :=
  --   let equationsToProcess := system₀.equations
  --   equationsToProcess.fold
  --     (init := { system₀ with equations := {} })
  --     (fun system equation =>
  --       system.add (processor equation) )

  def substitute (system : System) (identity : Identity) :=
    let ⟨identifier, value⟩ := identity

    match (system.answers.get? identifier) with

    | some existingValue =>
        if existingValue == value then system else
        system.add ((existingValue, value) : Equation.Contradiction)

    | none =>
        let affectedEquations : List Equation :=
          let affectedSet? := system.equations[identifier]?
          (affectedSet?.toList.map (fun set => HashSet.toList set)).flatten

        let systemWithNewEquations := affectedEquations.foldl (init := system)
          (fun prev (argEq : Equation) =>
          let newEquation := argEq.substitute identity
          prev
            |> (System.deleteEquation · argEq)
            |> (System.add · newEquation.balance)
          )

        systemWithNewEquations.addAnswer identity


  def changeStep (system : System) :=
    match system.nextStep with
    | Steps.balance => { system with nextStep := Steps.evaluate }
    | Steps.evaluate => { system with nextStep := Steps.substitute }
    | Steps.substitute => { system with nextStep := Steps.balance }

  def substituteAll (system : System) :=
    system.pending.foldl (init := { system with pending := {} })
      (fun prev identity =>
        prev.substitute identity)

  -- def next (system : System) := match system.nextStep with
  --   | Steps.balance => (system.applyToEquations Equation.balance).changeStep
  --   | Steps.evaluate => (system.applyToEquations Equation.evaluate).changeStep
  --   | Steps.substitute => system |> .substituteAll |> .changeStep

  def goFoward (system : System) (steps : Nat) := match steps with
  | 0 => system
  | n + 1 =>
    if system.contradictions.isEmpty.not then system
    else if system.pending.isEmpty then system
    else (system.substituteAll).goFoward n

end System


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
      (⟨level-1, "e"⟩, ⟨level-1, "f"⟩, ⟨level-1, "g"⟩)

    let equation₁ := equation ch1 e Op.and f
    let equation₂ := equation ch2 (not e) Op.and g
    let finalEquation := equation ch ch1 Op.xor ch2

    [equation₁, equation₂, finalEquation]

  def temp1Equations (level : Nat) :=
    let ⟨temp1, temp1₁, temp1₂, temp1₃⟩ : onePlusTuple 3 Identifier :=
      (⟨level, "temp1"⟩, ⟨level, "temp1.1"⟩, ⟨level, "temp1.2"⟩, ⟨level, "temp1.3"⟩)

    let ⟨h, S1, ch, k, w⟩ : onePlusTuple 4 Identifier :=
      (⟨(level - 1), "h"⟩, ⟨level, "S1"⟩, ⟨level, "ch"⟩, ⟨level, "k"⟩, ⟨level, "w"⟩)

    let eq1 := equation temp1₁ h Op.add S1
    let eq2 := equation temp1₂ temp1₁ Op.add ch
    let eq3 := equation temp1₃ temp1₂ Op.add k
    let finalEquation := equation temp1 temp1₃ Op.add w

    [eq1, eq2, eq3, finalEquation]

  def majEquations (level : Nat) :=
    let ⟨maj, maj1, maj2, maj3, maj4⟩ : onePlusTuple 4 Identifier :=
      (⟨level, "maj"⟩, ⟨level, "maj1"⟩, ⟨level, "maj2"⟩, ⟨level, "maj3"⟩, ⟨level, "maj4"⟩)

    let ⟨a, b, c⟩ : onePlusTuple 2 Identifier :=
      (⟨(level - 1), "a"⟩, ⟨(level - 1), "b"⟩, ⟨(level - 1), "c"⟩)

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

    let ⟨a, b, c, d, e, f, g, _⟩ : onePlusTuple 7 Identifier :=
      letterIdentifiers (level - 1)

    let ⟨a2, b2, c2, d2, e2, f2, g2, h2⟩ : onePlusTuple 7 Identifier :=
      letterIdentifiers (level)

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

  def letters := ["a", "b", "c", "d", "e", "f", "g", "h"]

  def finalHs := letters.mapFinIdx ( fun index letter _ =>

    let initialHId := Identifier.mk 0 s!"h{index}"
    let finalHId := Identifier.mk 63 s!"h{index}"
    let letterId := Identifier.mk 63 letter

    equation finalHId initialHId Op.add letterId )

  def levelEquations (level : Nat) :=

    let ⟨a, _, _, _, e, _, _, _⟩ : onePlusTuple 7 Identifier :=
      letterIdentifiers (level - 1)

    let ⟨S1, _, _, S0, maj, temp2⟩ : onePlusTuple 5 Identifier :=
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

  def fixedEquations := finalHs

  -- def startingIdentities : List Identity := [
  -- (⟨62, "w"⟩, 0xee6c3388), (⟨63, "w"⟩, 0x5e809082) ]

  def initialHs : List Identity := [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,0x510e527f,
    0x9b05688c, 0x1f83d9ab, 0x5be0cd19].mapFinIdx (fun index value _ =>
      (⟨0, s!"h{index}"⟩, value))

  def kIdentities : List Identity := [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
    ].mapFinIdx (fun index num _ => (⟨index, "k"⟩, num))

  def wIdentities : List Identity := [
        0x43c92c6d, 0x8f746591, 0x574674ca, 0xd8e19662, 0xfb5306c6, 0x54d6b874, 0x7b4e3f5a, 0x5449b567,
        0x80000000, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x100, 0x6f5d3411, 0x93893d32, 0x4f0d09aa, 0xe52b085d,
        0x6d752336, 0x6e3c82ac, 0x5aad578a, 0xa5bf3f71, 0x14ac0a88, 0xc78c9351, 0x693b2c1e, 0x49685b49,
        0x61d33a1d, 0x818d2f19, 0xa054a7b0, 0xa92ce681, 0x360aa9a9, 0xb943cbf, 0xffd9f2b2, 0xa8299ae,
        0x2be41b99, 0x7873f608, 0xcab07892, 0x71c3f553, 0xf354d206, 0x4678b5bc, 0xf4aac245, 0xba434603,
        0x7c937e73, 0x74d2f80f, 0x12d9415d, 0xbe6426b8, 0x754f69d7, 0x9e8c0340, 0xf18152f, 0x3ad31975,
        0x8b653b43, 0x9dcfa3a9, 0x198f320a, 0x33a77d11, 0x6e4ff7c2, 0xcca49249, 0xf63cc5a9, 0x57ff0e3e,
        0xc32f94c9, 0xdd5926fb, 0xee6c3388, 0x5e809082].mapFinIdx (fun index num _ => (⟨index, "w"⟩, num))



  def sha256Identities := initialHs ++ kIdentities ++ wIdentities

end Sha256

#print List.allM

def h1s := [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
    0x5be0cd19]

def h2s := [0x6705d79c, 0xbdf5a4d, 0x9793c992, 0x41a0ad81, 0x1f13094d, 0x78270100, 0x0, 0x0]

def letters := ["a", "b", "c", "d", "e", "f", "g", "h"]

def letterValues0 := (0...64).toList.map (fun _ => (0...8).toList)
def letterValues := letterValues0.set 54 [0x1a7609b2, 0xcb808803, 0x16fd6124, 0x8b0284da, 0x7be8afd, 0x6e18b00d, 0x713ef5e1, 0xb2ee8163]
#eval letterValues

def letterIds (level : Nat) : List Identity :=
  (letters.zip (letterValues[level]!)).map (fun pair =>
    (⟨level, pair.1⟩, pair.2))

#eval letterIds 54

def mySystem :=
  System.empty
  |> (·.addList ((55...64).toList.map fun n => Sha256.levelEquations n).flatten)
  |> (·.addList (Sha256.fixedEquations))
  |> (·.addList Sha256.sha256Identities)
  |> (·.addList (letterIds 54))

#eval mySystem
-- #eval mySystem.goFoward 3
-- #eval mySystem.goFoward 4
-- #eval mySystem.goFoward 5
-- #eval mySystem.goFoward 8
-- #eval mySystem.goFoward 9
-- #eval mySystem.goFoward 11
#eval mySystem.goFoward 300

-- #eval IO.print ((mySystem.goFoward 40).answers.filter (fun k _ => (system0.answers.contains k).not) : Answers)
