/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.VirasoroRealStructure
import VOA.Examples.VirasoroLengthTwoBoundary

/-!
# Canonical real structures on the boundary Virasoro models

Every boundary central charge is realized by a real Feigin--Fuchs background charge.  This file
supplies that charge explicitly and specializes the general descent theorem to construct a
canonical real structure on each simple boundary Virasoro VOA.
-/

namespace VOA
namespace VirGradedUnitarity

open VOA.VirModule VOA.VirSimple

/-- The square of the real Feigin--Fuchs background charge at the boundary-model index `n`. -/
noncomputable def boundaryBackgroundChargeSq (n : ℕ) : ℝ :=
  (2 * (n : ℝ) - 1) ^ 2 / (4 * (2 * n + 1))

/-- The proposed squared background charge is nonnegative: its numerator
is a square and its denominator is positive. Its real square root is therefore
an actual solution of the required square equation. -/
theorem boundaryBackgroundChargeSq_nonneg (n : ℕ) :
    0 ≤ boundaryBackgroundChargeSq n := by
  unfold boundaryBackgroundChargeSq
  positivity

/-- A real Feigin--Fuchs background charge for the boundary central charge. -/
noncomputable def boundaryBackgroundCharge (n : ℕ) : ℂ :=
  (Real.sqrt (boundaryBackgroundChargeSq n) : ℂ)

/-- The chosen background charge lies on the real axis, so complex
conjugation fixes it. This is the compatibility needed for the real structure. -/
@[simp] theorem boundaryBackgroundCharge_fixed (n : ℕ) :
    (starRingEnd ℂ) (boundaryBackgroundCharge n) = boundaryBackgroundCharge n := by
  exact Complex.conj_ofReal _

/-- Substitution of the chosen real background charge into the Feigin--Fuchs
formula 1-12λ² gives exactly the boundary minimal-model central charge. The
nonnegative square-root identity justifies the substitution. -/
theorem boundaryBackgroundCharge_spec (n : ℕ) :
    1 - 12 * boundaryBackgroundCharge n ^ 2 = boundaryCharge n := by
  have hsqrt : Real.sqrt (boundaryBackgroundChargeSq n) ^ 2 =
      boundaryBackgroundChargeSq n :=
    Real.sq_sqrt (boundaryBackgroundChargeSq_nonneg n)
  have hlamSq : boundaryBackgroundCharge n ^ 2 =
      (boundaryBackgroundChargeSq n : ℂ) := by
    change (Real.sqrt (boundaryBackgroundChargeSq n) : ℂ) ^ 2 =
      (boundaryBackgroundChargeSq n : ℂ)
    norm_cast
  rw [hlamSq]
  norm_num [boundaryBackgroundChargeSq, boundaryCharge, boundaryMinimalCentralCharge]
  have hdenR : (2 * (n : ℂ) + 1) ≠ 0 := by
    exact_mod_cast (show (2 * (n : ℚ) + 1) ≠ 0 by positivity)
  field_simp [hdenR]
  ring

/-- The canonical partition-basis real structure on the simple boundary Virasoro model. -/
noncomputable def boundaryVirasoroRealStructure (n : ℕ) :
    RealStructure (virasoroSimple (boundaryCharge n)) :=
  virasoroSimpleRealStructure (boundaryBackgroundCharge_spec n)
    (boundaryBackgroundCharge_fixed n)

end VirGradedUnitarity
end VOA
