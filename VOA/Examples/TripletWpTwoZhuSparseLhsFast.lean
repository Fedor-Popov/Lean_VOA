/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseCompute

/-! # Fast Virasoro recurrence for the W(2) Zhu polynomial

For a homogeneous state of weight `w`, left Zhu multiplication by the conformal vector is
`L₋₂ + 2 L₋₁ + L₀`.  The sparse Virasoro action already computes the first two
summands directly, while `L₀` is scalar multiplication by `w`.  Keeping the weight attached
to each sparse coordinate avoids replaying the much slower generic field evaluator.
-/

namespace VOA.LatGen.WpTwoZhuSparseLhs

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute
open VOA.LatGen.WpTwoZhuSparseCompute

/-- The three homogeneous pieces of left Zhu multiplication by `ω`. -/
def zhuOmegaPartFastSparseQ
    (x : ℕ × SparseRational.Poly ℕ) : List (ℕ × SparseRational.Poly ℕ) :=
  [(x.1 + 2, virActSparseQ 2 x.2),
   (x.1 + 1, scaleQ 2 (virActSparseQ 1 x.2)),
   (x.1, scaleQ (x.1 : ℚ) x.2)]

/-- Iterated homogeneous Zhu powers using the direct Virasoro recurrence. -/
def zhuOmegaPartsFastSparseQ : ℕ → List (ℕ × SparseRational.Poly ℕ)
  | 0 => [(0, vacuumSparseQ)]
  | n + 1 => (zhuOmegaPartsFastSparseQ n).flatMap zhuOmegaPartFastSparseQ

def omegaPowerFastSparseQ (n : ℕ) : SparseRational.Poly ℕ :=
  flattenGradedSparseQ (zhuOmegaPartsFastSparseQ n)

/-- The factored Zhu polynomial evaluated through the fast Virasoro recurrence. -/
def fTwoFastSparseQ : SparseRational.Poly ℕ :=
  sumQ [omegaPowerFastSparseQ 5,
    scaleQ (-5 / 4) (omegaPowerFastSparseQ 4),
    scaleQ (13 / 64) (omegaPowerFastSparseQ 3),
    scaleQ (3 / 64) (omegaPowerFastSparseQ 2)]

end VOA.LatGen.WpTwoZhuSparseLhs
