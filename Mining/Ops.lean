import Mining.Utils
open Utils (Nat.asBitVec)

inductive Op where
  | add : Op
  | sub : Op
  | xor : Op
  | and : Op
deriving Repr, BEq, Hashable

instance : ToString Op where
  toString op := toString (repr op)

namespace Op

  def binaryOp (T : Type) := T → T → T

  def eval : Op → (binaryOp (BitVec 32))
    | Op.add => BitVec.add
    | Op.sub => BitVec.sub
    | Op.xor => BitVec.xor
    | Op.and => BitVec.and

  def inverse : Op → Op
  | add => sub
  | sub => add
  | xor => xor
  | and => and -- False, but it won't matter

  def commutative : Op → Bool
    | add => true
    | sub => false
    | xor => true
    | and => true

  -- a = b op c ↔ c = a rev b
  def reverseInverse (op : Op) (a b : BitVec 32) : BitVec 32 :=
    match op with
    | sub => Op.sub.eval b a
    -- commutative operations:
    | _ => op.inverse.eval a b


end Op


inductive Unary where
  | not : Unary
  | rightRotate : Nat → Unary
  | leftRotate : Nat → Unary
  | rightShift : Nat → Unary
  | leftShift : Nat → Unary
deriving Repr, BEq, Hashable

instance : ToString Unary where
  toString op := toString (repr op)

namespace Unary

  def eval : Unary → ((BitVec 32) → (BitVec 32))
  | not => BitVec.not
  | rightRotate n => fun bv => bv.rotateRight n
  | leftRotate n => fun bv => bv.rotateLeft n
  | rightShift n => fun bv => bv.ushiftRight n
  | leftShift n => fun bv => bv.shiftLeft n

  def inverse : Unary → Unary
  | not => not
  | rightRotate n => leftRotate n
  | leftRotate n => rightRotate n
  | rightShift n => leftShift n -- not true, todo fix
  | leftShift n => rightShift n

end Unary

-- def exampleBV := 0x12345678.asBitVec
-- #eval (Unary.not.eval) exampleBV
-- #eval ((Unary.rightRotate 4).eval) exampleBV
-- #eval ((Unary.leftRotate 4).eval) exampleBV
