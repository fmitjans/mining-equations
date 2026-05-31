import Mining.Equation

open Utils

namespace Sha256

  def rightRotate [ToTerm α] (n : Nat) (t : α) := Term.op (Unary.rightRotate n) (toTerm t)

  def rightShift [ToTerm α] (n : Nat) (t : α) := Term.op (Unary.rightShift n) (toTerm t)

  def tripleRotate (identifier : Identifier) (letter : Identifier) (r1 r2 r3 : Nat) :=

    let auxIdentifier : Identifier := ⟨identifier.level, (identifier.symbol ++ ".aux")⟩

    let firstEquation :=
      equation auxIdentifier (rightRotate r1 letter) Op.xor (rightRotate r2 letter)

    let secondEquation :=
      equation identifier auxIdentifier Op.xor (rightRotate r3 letter)

    [firstEquation, secondEquation]

  -- #eval tripleRotate ⟨63, "S1"⟩ ⟨63, "e"⟩ 6 11 25

  def not [ToTerm α] (t : α) := Term.op Unary.not (toTerm t)

  def letters := ["a", "b", "c", "d", "e", "f", "g", "h"]

  def inputIdentifiers (argLevel : Nat) (baseLevel : Nat := 0) : onePlusTuple 7 Identifier :=
    if argLevel == 0 then
      let level := baseLevel
      (⟨level, "h0"⟩, ⟨level, "h1"⟩, ⟨level, "h2"⟩, ⟨level, "h3"⟩,
       ⟨level, "h4"⟩, ⟨level, "h5"⟩, ⟨level, "h6"⟩, ⟨level, "h7"⟩,)
    else
      let level := baseLevel + argLevel - 1
      (⟨level, "a"⟩, ⟨level, "b"⟩, ⟨level, "c"⟩, ⟨level, "d"⟩,
       ⟨level, "e"⟩, ⟨level, "f"⟩, ⟨level, "g"⟩, ⟨level, "h"⟩)

  def crossedAnd (argLevel : Nat) (baseLevel : Nat := 0) :=
    let level := baseLevel + argLevel
    let ⟨ch, ch1, ch2⟩ : onePlusTuple 2 Identifier :=
      (⟨level, "ch"⟩, ⟨level, "ch.1"⟩, ⟨level, "ch.2"⟩)

    let inputsIds := inputIdentifiers argLevel baseLevel
    let ⟨_, _, _, _, e, f, g, _⟩ : onePlusTuple 7 Identifier := inputsIds

    let equation₁ := equation ch1 e Op.and f
    let equation₂ := equation ch2 (not e) Op.and g
    let finalEquation := equation ch ch1 Op.xor ch2

    [equation₁, equation₂, finalEquation]

  def temp1Equations (argLevel : Nat) (baseLevel : Nat := 0) :=
    let level := baseLevel + argLevel

    let ⟨temp1, temp1₁, temp1₂, temp1₃⟩ : onePlusTuple 3 Identifier :=
      (⟨level, "temp1"⟩, ⟨level, "temp1.1"⟩, ⟨level, "temp1.2"⟩, ⟨level, "temp1.3"⟩)

    let inputsIds := inputIdentifiers argLevel baseLevel
    let ⟨_, _, _, _, _, _, _, h⟩ : onePlusTuple 7 Identifier := inputsIds

    let ⟨S1, ch, k, w⟩ : onePlusTuple 3 Identifier :=
      (⟨level, "S1"⟩, ⟨level, "ch"⟩, ⟨level, "k"⟩, ⟨level, "w"⟩)

    let eq1 := equation temp1₁ h Op.add S1
    let eq2 := equation temp1₂ temp1₁ Op.add ch
    let eq3 := equation temp1₃ temp1₂ Op.add k
    let finalEquation := equation temp1 temp1₃ Op.add w

    [eq1, eq2, eq3, finalEquation]

  def majEquations (argLevel : Nat) (baseLevel : Nat := 0) :=

    let level := baseLevel + argLevel

    let ⟨maj, maj1, maj2, maj3, maj4⟩ : onePlusTuple 4 Identifier :=
      (⟨level, "maj"⟩, ⟨level, "maj1"⟩, ⟨level, "maj2"⟩, ⟨level, "maj3"⟩, ⟨level, "maj4"⟩)

    let inputsIds := inputIdentifiers argLevel baseLevel
    let ⟨a, b, c, _, _, _, _, _⟩ : onePlusTuple 7 Identifier := inputsIds

    let eq1 := equation maj1 a Op.and b
    let eq2 := equation maj2 a Op.and c
    let eq3 := equation maj3 b Op.and c
    let eq4 := equation maj4 maj1 Op.xor maj2

    let finalEquation := equation maj maj4 Op.xor maj3

    [eq1, eq2, eq3, eq4, finalEquation]

  def letterIdentifiers (level : Nat) : onePlusTuple 7 Identifier :=
    (⟨level, "a"⟩, ⟨level, "b"⟩, ⟨level, "c"⟩, ⟨level, "d"⟩,
      ⟨level, "e"⟩, ⟨level, "f"⟩, ⟨level, "g"⟩, ⟨level, "h"⟩)

  def letterReasignEquations (argLevel : Nat) (baseLevel : Nat := 0) :=

    let level := baseLevel + argLevel

    let inputsIds := inputIdentifiers argLevel baseLevel
    let ⟨a, b, c, d, e, f, g, _⟩ : onePlusTuple 7 Identifier := inputsIds

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

  def finalHs (baseLevel : Nat := 0) := letters.mapFinIdx ( fun index letter _ =>

    let initialHId := Identifier.mk baseLevel s!"h{index}"
    let finalHId := Identifier.mk (baseLevel + 63) s!"h{index}"
    let letterId := Identifier.mk (baseLevel + 63) letter

    equation finalHId initialHId Op.add letterId )

  def levelEquations (argLevel : Nat) (baseLevel : Nat := 0) :=

    let level := baseLevel + argLevel

    let inputsIds := inputIdentifiers argLevel baseLevel
    let ⟨a, _, _, _, e, _, _, _⟩ : onePlusTuple 7 Identifier := inputsIds

    let ⟨S1, _, _, S0, maj, temp2⟩ : onePlusTuple 5 Identifier :=
    (⟨level, "S1"⟩, ⟨level, "ch"⟩, ⟨level, "temp1"⟩,
      ⟨level, "S0"⟩, ⟨level, "maj"⟩, ⟨level, "temp2"⟩)

    let eqsS1 := tripleRotate S1 e 6 11 25
    let eqsch := crossedAnd argLevel baseLevel
    let eqstemp1 := temp1Equations argLevel baseLevel
    let eqsS0 := tripleRotate S0 a 2 13 22
    let eqsmaj := majEquations argLevel baseLevel
    let eqstemp2 := [equation temp2 S0 Op.add maj]
    let eqsLetters := letterReasignEquations argLevel baseLevel

    eqsS1 ++ eqsch ++ eqstemp1 ++ eqsS0 ++
      eqsmaj ++ eqstemp2 ++ eqsLetters

  -- def startingIdentities : List Identity := [
  -- (⟨62, "w"⟩, 0xee6c3388), (⟨63, "w"⟩, 0x5e809082) ]

  def initialHs (baseLevel : Nat := 0) : List Identity :=
    [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,0x510e527f,
    0x9b05688c, 0x1f83d9ab, 0x5be0cd19].mapFinIdx (fun index value _ =>
      (⟨baseLevel, s!"h{index}"⟩, value))

  def kIdentities (baseLevel : Nat := 0) : List Identity := [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
    ].mapFinIdx (fun index num _ => (⟨(baseLevel + index), "k"⟩, num))

  -- def wIdentities (baseLevel : Nat := 0) : List Identity := [
  --       0x43c92c6d, 0x8f746591, 0x574674ca, 0xd8e19662, 0xfb5306c6, 0x54d6b874, 0x7b4e3f5a, 0x5449b567,
  --       0x80000000, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x100, 0x6f5d3411, 0x93893d32, 0x4f0d09aa, 0xe52b085d,
  --       0x6d752336, 0x6e3c82ac, 0x5aad578a, 0xa5bf3f71, 0x14ac0a88, 0xc78c9351, 0x693b2c1e, 0x49685b49,
  --       0x61d33a1d, 0x818d2f19, 0xa054a7b0, 0xa92ce681, 0x360aa9a9, 0xb943cbf, 0xffd9f2b2, 0xa8299ae,
  --       0x2be41b99, 0x7873f608, 0xcab07892, 0x71c3f553, 0xf354d206, 0x4678b5bc, 0xf4aac245, 0xba434603,
  --       0x7c937e73, 0x74d2f80f, 0x12d9415d, 0xbe6426b8, 0x754f69d7, 0x9e8c0340, 0xf18152f, 0x3ad31975,
  --       0x8b653b43, 0x9dcfa3a9, 0x198f320a, 0x33a77d11, 0x6e4ff7c2, 0xcca49249, 0xf63cc5a9, 0x57ff0e3e,
  --       0xc32f94c9, 0xdd5926fb, 0xee6c3388, 0x5e809082].mapFinIdx
  --         (fun index num _ => (⟨(baseLevel + index), "w"⟩, num))

  def rotateAndShift (leftIdentifier : Identifier) (argIdentifier : Identifier) (r1 r2 r3 : Nat) :=

    let auxIdentifier : Identifier := ⟨leftIdentifier.level, (leftIdentifier.symbol ++ ".aux")⟩

    let firstEquation :=
      equation auxIdentifier (rightRotate r1 argIdentifier) Op.xor (rightRotate r2 argIdentifier)

    let secondEquation :=
      equation leftIdentifier auxIdentifier Op.xor (rightShift r3 argIdentifier)

    [firstEquation, secondEquation]

  def wEquations (baseLevel : Nat := 0) : List Equation :=
    let firstEquations := (0...16).toList.map fun index =>
      Equation.equality (Identifier.mk (baseLevel + index) "w") (Identifier.mk (index) "input")

    let otherEquations := (16...64).toList.map fun relIndex =>

      let index := baseLevel + relIndex

      let ⟨w, w15, w2, s0, s1, w16, w7, waux1, waux2⟩ : onePlusTuple 8 Identifier :=
        (⟨index, "w"⟩, ⟨index - 15, "w"⟩, ⟨index - 2, "w"⟩, ⟨index, "s0"⟩, ⟨index, "s1"⟩,
         ⟨index - 16, "w"⟩, ⟨index - 7, "w"⟩, ⟨index, "waux1"⟩, ⟨index, "waux2"⟩)

      let s0eqs := rotateAndShift s0 w15 7 18 3
      let s1eqs := rotateAndShift s1 w2 17 19 10

      [
        equation waux1 w16 Op.add s0,
        equation waux2 waux1 Op.add w7,
        equation w waux2 Op.add s1
      ] ++ s0eqs ++ s1eqs

    firstEquations ++ otherEquations.flatten

  def baseIdentities (baseLevel : Nat := 0) :=
    (initialHs baseLevel) ++ (kIdentities baseLevel)

  def allLevelEquations (baseLevel : Nat := 0) := (0...64).toList.foldl (fun prev n =>  prev.append (Sha256.levelEquations n baseLevel)) []

  def allEquations (baseLevel : Nat := 0) :=
    (allLevelEquations baseLevel) ++ (wEquations baseLevel) ++ (finalHs baseLevel)

  def miningIdentities (baseLevel : Nat := 0) : List Identity :=
    [(⟨baseLevel + 63, "h6"⟩, (0).asBitVec), (⟨baseLevel + 63, "h7"⟩, (0).asBitVec)]

end Sha256
