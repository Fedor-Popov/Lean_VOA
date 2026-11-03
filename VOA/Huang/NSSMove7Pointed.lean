import VOA.Huang.NSSMove3PointedSanity

/-! # Scalar check of the loop transposition

This is the existing pointed scalar model, not a categorical instance.
The cup and cap scalars are one and the braiding scalar is `phase (x*y)`.
-/
namespace VOA.Huang.NSCongruence.PointedThree

/-- The scalar of the monodromy loop around a homogeneous strand. -/
def loopScalar (x y : ZMod 3) : Scalar := phase (2 * x * y)

/-- The forward sewing scalar before inserting the loop. -/
def forwardSewingScalar (r i j : ZMod 3) : Scalar := phase ((2 * r - i) * j)

/-- The inverse sewing scalar before inserting the loop. -/
def inverseSewingScalar (b i j : ZMod 3) : Scalar := phase ((2 * b - j) * i)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
-- Evaluate all 81 quadruples of labels using exact rational arithmetic.
/-- All 81 scalar instances of the `NSSMove6` loop transposition. -/
theorem loopTranspose_scalar : ∀ r b i j : ZMod 3,
    forwardSewingScalar r i j * loopScalar b (-r + i) =
      inverseSewingScalar b i j * loopScalar r (j - b) := by decide +kernel

end VOA.Huang.NSCongruence.PointedThree
