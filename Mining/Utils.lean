import Std
open Std (HashSet HashMap)

namespace Utils

def Nat.asBitVec (n : Nat) := BitVec.ofNat 32 n

def Option.both ( a b : (Option α)) : Option (α × α) :=
  a.bind (fun a => b.bind (fun b => some (a, b)))

def HashSet.map {α β} [BEq α] [Hashable α] [BEq β] [Hashable β]
  (s : Std.HashSet α) (f : α → β) : Std.HashSet β :=
  s.fold (init := ∅) (fun acc x => acc.insert (f x))


abbrev onePlusTuple (n : Nat) (t : Type) := match n with
    | 0 => t | n + 1 => t × (onePlusTuple n t)


def insertIntoValue [BEq α] [Hashable α] [BEq β] [Hashable β]
  (argMap : HashMap α (HashSet β)) (key : α) (value : β) :=

  let oldSet? := argMap.get? key
  oldSet?.elim
    (argMap.insert key (({} : HashSet β).insert value))
    (fun oldSet => argMap.insert key (oldSet.insert value))
