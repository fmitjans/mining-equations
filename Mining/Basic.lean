import Mining.Utils
import Mining.Ops
import Mining.Expressions
import Mining.Sha256

open Std (HashSet HashMap)
open Utils


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

  def basicSha :=
    let initial := System.empty
      |> (·.addList (Sha256.allEquations 100))
      |> (·.addList (Sha256.baseIdentities 100))

    { initial.goFoward 1 with answers := {} }


end System



def h1s := [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
    0x5be0cd19]

def h2s := [0x6705d79c, 0xbdf5a4d, 0x9793c992, 0x41a0ad81, 0x1f13094d, 0x78270100, 0x0, 0x0]


def mySystem :=
  System.empty
  |> (·.addList ((150...164).toList.map fun n => Sha256.levelEquations n).flatten)
  |> (·.addList (Sha256.initialHs 100))
  |> (·.addList (Sha256.baseIdentities 100))
  -- |> (·.addList (letterIds 54 100))

#eval mySystem
-- #eval mySystem.goFoward 3
-- #eval mySystem.goFoward 4
-- #eval mySystem.goFoward 5
-- #eval mySystem.goFoward 8
-- #eval mySystem.goFoward 9
-- #eval mySystem.goFoward 11
#eval mySystem.goFoward 300

#eval IO.println (asCollectionString (Sha256.wEquations) ("[", "]"))
-- #eval IO.print ((mySystem.goFoward 40).answers.filter (fun k _ => (system0.answers.contains k).not) : Answers)
