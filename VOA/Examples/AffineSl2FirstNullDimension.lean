/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2SimpleCharacterRank

/-! # Exact actual dimension loss at the first admissible vacuum root -/
namespace VOA.PolynomialMatrix
open Polynomial Matrix
noncomputable section

/-- A simple determinant root has exactly one-dimensional kernel. The proof
uses an invertible single-column replacement detected by the determinant derivative. -/
theorem finrank_ker_of_simple_root {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (M : Matrix ι ι K[X]) (z : K) (hz : M.det.eval z = 0)
    (hd : M.det.derivative.eval z ≠ 0) :
    Module.finrank K (evaluate M z).mulVecLin.ker = 1 := by
  have hj : ∃ j, (M.updateCol j (fun i => (M i j).derivative)).det.eval z ≠ 0 := by
    by_contra! h
    apply hd
    rw [derivative_det_columns, Polynomial.eval_finsetSum]
    exact Finset.sum_eq_zero (fun j _ => h j)
  obtain ⟨j, hj⟩ := hj
  let A := evaluate M z
  let B := evaluate (M.updateCol j (fun i => (M i j).derivative)) z
  have hB : B.det ≠ 0 := by
    change ((Polynomial.evalRingHom z).mapMatrix _).det ≠ 0
    rw [← RingHom.map_det]
    exact hj
  have hAzero : A.det = 0 := by
    change ((Polynomial.evalRingHom z).mapMatrix M).det = 0
    rw [← RingHom.map_det]
    exact hz
  have hmul (v : ι → K) (hv : v j = 0) : B.mulVec v = A.mulVec v := by
    funext i
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a = j
    · subst a
      simp [hv]
    · simp [A, B, evaluate, RingHom.mapMatrix_apply, Matrix.map_apply, ha]
  let L : A.mulVecLin.ker →ₗ[K] K := (LinearMap.proj j).comp A.mulVecLin.ker.subtype
  have hinj : Function.Injective L := by
    intro x y he
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply Matrix.eq_zero_of_mulVec_eq_zero hB
    rw [hmul _ (sub_eq_zero.mpr he)]
    change A.mulVecLin (x.val - y.val) = 0
    rw [map_sub, x.property, y.property, sub_self]
  have hle : Module.finrank K A.mulVecLin.ker ≤ 1 := by
    simpa using LinearMap.finrank_le_finrank_of_injective hinj
  have hge : 1 ≤ Module.finrank K A.mulVecLin.ker := by
    apply Submodule.one_le_finrank_iff.mpr
    intro hbot
    obtain ⟨v, hv, hvA⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hAzero
    have hm : v ∈ A.mulVecLin.ker := hvA
    rw [hbot, Submodule.mem_bot] at hm
    exact hv hm
  exact Nat.le_antisymm hle hge

/-- Equivalent exact rank loss at a simple root. -/
theorem rank_add_one_of_simple_root {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (M : Matrix ι ι K[X]) (z : K) (hz : M.det.eval z = 0)
    (hd : M.det.derivative.eval z ≠ 0) :
    (evaluate M z).rank + 1 = Fintype.card ι := by
  have h := (evaluate M z).mulVecLin.finrank_range_add_finrank_ker
  rw [finrank_ker_of_simple_root M z hz hd, Module.finrank_pi] at h
  exact h

end
end VOA.PolynomialMatrix

namespace VOA.AffineSl2GeneralRigidity
noncomputable section

/-- The genuine first admissible highest-charge simple quotient loses
exactly one PBW dimension, uniformly in every coprime admissible numerator and denominator. -/
theorem admissible_simpleJointPiece_first_finrank_add_one (p q : ℕ) (hp : 2 ≤ p)
    (hq : 0 < q) (hcop : p.Coprime q) :
    Module.finrank ℂ (simpleJointPiece ((p : ℂ) / q - 2)
      (admissible_level_noncritical p q hp hq) (q * (p - 1) : ℕ) (2 * ((p : ℤ) - 1))) + 1 =
      Fintype.card (JointIndex (q * (p - 1) : ℕ) (2 * ((p : ℤ) - 1))) := by
  classical
  rw [simpleJointPiece_finrank_eq_gramRank]
  obtain ⟨hz, hd⟩ := Wak.Charged.vacuumChevalleyDeterminant_admissible_simple p q hp hq hcop
  exact PolynomialMatrix.rank_add_one_of_simple_root _ _ hz hd

end
end VOA.AffineSl2GeneralRigidity
