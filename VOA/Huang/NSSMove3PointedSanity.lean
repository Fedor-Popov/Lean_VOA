import VOA.Huang.NSSMove2Diagrams
import Mathlib.Algebra.QuadraticAlgebra.Basic

/-! # Exact scalar checks in the pointed Z/3 example

This is a scalar model, not a constructed `SphericalFusion` instance. The
identification with graded vector spaces is not formalized.
The coefficient ring has a generator `omega` satisfying `omega²+omega+1=0`.
All finite computations below are checked by the Lean kernel.
-/
namespace VOA.Huang.NSCongruence.PointedThree

abbrev Scalar := QuadraticAlgebra ℚ (-1) (-1)

def omega : Scalar := ⟨0, 1⟩
def phase (x : ZMod 3) : Scalar := omega ^ x.val

/-- S includes the dual on the FIRST index, as in `categoricalS`. -/
def sEntry (a b : ZMod 3) : Scalar := phase (-2 * a * b)

def coefficient (a b r s : ZMod 3) : Scalar :=
  QuadraticAlgebra.C (1 / 3 : ℚ) * sEntry r a * sEntry (-s) b

def inverseCrossing (a b i j : ZMod 3) : Scalar :=
  if j = a + b then phase (-(a - b) * i) else 0

def forwardCrossing (a b i j : ZMod 3) : Scalar :=
  if i = a + b then phase ((a - b) * j) else 0

theorem omega_primitive : omega ^ 3 = 1 ∧ omega ≠ 1 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
-- The finite rational calculation checks all 81 label quadruples in the kernel.
/-- All 81 choices of exterior and mixed labels, with the actual S convention. -/
theorem exchange_holds : ∀ a b i j : ZMod 3,
    inverseCrossing a b i j =
      ∑ r : ZMod 3, ∑ s : ZMod 3,
        coefficient a b r s * forwardCrossing r s i j := by decide +kernel

/-- The scalar trace of rotation on a simple pointed probe. The independent
calculation uses a one-dimensional Hom space and the inverse half-braiding. -/
def indicator (a b v : ZMod 3) (m : ℕ) (l : ℤ) : Scalar :=
  if (m : ZMod 3) * v = a + b then phase (-(a - b) * v * (l : ZMod 3)) else 0

/-- Simple probes have one channel in each block; reassociation has scalar 1. -/
def closure (v : ZMod 3) (n k : ℕ) (i j : ZMod 3) (f : Scalar) : Scalar :=
  if i = (k + 1 : ℕ) * v then
    if j = (n + 1 : ℕ) * v then f else 0
  else 0

/-- Both trace clauses, for every positive degree, in the simple pointed model. -/
theorem twoBlockTrace_holds (a b v : ZMod 3) (n k : ℕ) :
    (indicator a b v (n + 1) (k + 1) =
      ∑ i, ∑ j, closure v n k i j (inverseCrossing a b i j)) ∧
    (indicator a b v (k + 1) (-(n + 1)) =
      ∑ i, ∑ j, closure v n k i j (forwardCrossing a b i j)) := by
  simp only [closure, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  constructor
  · unfold indicator inverseCrossing
    congr 2
    push_cast
    ring
  · unfold indicator forwardCrossing
    congr 2
    push_cast
    ring

end VOA.Huang.NSCongruence.PointedThree
