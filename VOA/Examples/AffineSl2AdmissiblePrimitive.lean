/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2AdmissibleNullVector
import VOA.Examples.AffineSl2BoundarySingularFamily

/-!
# Uniform primitive states from the actual admissible determinant

Below-root nondegeneracy kills every positive current image. The first-energy
charge gap kills the horizontal raising image. Thus the genuine null state
supplies the singularity fields without a singular-vector existence premise.
-/
namespace VOA.AffineSl2GeneralRigidity
open AffineVOA AffineVOA.HighestModule AffineVOA.Inst AffineVOA.Strong
open VertexOperatorAlgebra Sl2Sing Sl2SingLY
noncomputable section
open scoped Classical

/-- Every current preserves the actual maximal graded ideal. -/
theorem current_mem_maxIdeal (k : ℂ) (hk : k + 2 ≠ 0) (a : Fin 3) (m : ℤ)
    (x : WakModule k) (hi : x ∈ QuotVOA.maxGradedIdeal (universal k hk)) :
    J k a m x ∈ QuotVOA.maxGradedIdeal (universal k hk) := by
  rw [← smul_currentState_eq_J k hk]
  exact (QuotVOA.maxGradedIdeal_isIdeal (universal k hk)) _ _ _ hi

/-- A nonzero-index current changes the simultaneous energy and half-charge
by its known mode and color. -/
theorem current_mem_joint (k : ℂ) (hk : k + 2 ≠ 0) (n c : ℤ)
    (a : Fin 3) (m : ℤ) (hm : m ≠ 0) (x : WakModule k)
    (hx : x ∈ jointSpace k hk n (2 * c)) :
    J k a m x ∈ jointSpace k hk (n - m) (2 * (c + ![1, -1, 0] a)) := by
  have hg := jointSpace_le_grading k hk n (2 * c) hx
  have hjg := J_mem_gradingZA k a m n hg
  apply (mem_jointSpace_iff k hk _ _ _).mpr
  refine ⟨(universal k hk).L_zero_grading _ hjg, ?_⟩
  have hh := ((mem_jointSpace_iff k hk _ _ _).mp hx).2
  fin_cases a
  · exact H0_E m hh _ (by push_cast; ring)
  · exact H0_F m hh _ (by push_cast; ring)
  · simpa using H0_H m hm hh

/-- Any null state at the first admissible energy is annihilated by every
strictly positive current mode. -/
theorem admissible_first_null_positive (p q : ℕ) (hp : 2 ≤ p) (hq : 0 < q)
    (hcop : p.Coprime q)
    (x : WakModule ((p : ℂ) / q - 2))
    (hx : x ∈ jointSpace _ (admissible_level_noncritical p q hp hq)
      (q * (p - 1) : ℕ) (2 * ((p : ℤ) - 1)))
    (hi : x ∈ QuotVOA.maxGradedIdeal
      (universal _ (admissible_level_noncritical p q hp hq))) : SingP _ x := by
  intro a m hm
  by_cases hlarge : (q * (p - 1) : ℕ) < m
  · exact J_gradingZA_eq_zero _ a hlarge
      (jointSpace_le_grading _ _ _ _ hx)
  · have hnonneg : 0 ≤ (q * (p - 1) : ℕ) - m := by omega
    have hj := current_mem_joint _ (admissible_level_noncritical p q hp hq)
      _ _ a m (by omega) x hx
    have hji := current_mem_maxIdeal _ (admissible_level_noncritical p q hp hq) a m x hi
    have hj' : J _ a m x ∈ jointSpace _ (admissible_level_noncritical p q hp hq)
        (((q * (p - 1) : ℕ) - m).toNat : ℕ)
        (2 * (((p : ℤ) - 1) + ![1, -1, 0] a)) := by
      simpa only [Int.toNat_of_nonneg hnonneg] using hj
    exact admissible_null_eq_zero_below_all p q hp hq hcop _ _
      (by omega) _ hj' hji

/-- The first actual admissible null state is horizontal highest: its
raising image would be a forbidden higher-charge null at the same energy. -/
theorem admissible_first_null_raising (p q : ℕ) (hp : 2 ≤ p) (hq : 0 < q)
    (hcop : p.Coprime q)
    (x : WakModule ((p : ℂ) / q - 2))
    (hx : x ∈ jointSpace _ (admissible_level_noncritical p q hp hq)
      (q * (p - 1) : ℕ) (2 * ((p : ℤ) - 1)))
    (hi : x ∈ QuotVOA.maxGradedIdeal
      (universal _ (admissible_level_noncritical p q hp hq))) : J _ colE 0 x = 0 := by
  let k : ℂ := (p : ℂ) / q - 2
  let hk := admissible_level_noncritical p q hp hq
  have hg := jointSpace_le_grading k hk _ _ hx
  have hjg := J_mem_gradingZA k colE 0 (q * (p - 1) : ℕ) hg
  rw [sub_zero] at hjg
  have hh := ((mem_jointSpace_iff k hk _ _ _).mp hx).2
  have hj : J k colE 0 x ∈ jointSpace k hk (q * (p - 1) : ℕ) (2 * (p : ℤ)) := by
    apply (mem_jointSpace_iff k hk _ _ _).mpr
    exact ⟨(universal k hk).L_zero_grading _ hjg,
      H0_E 0 hh _ (by push_cast; ring)⟩
  by_cases hz : J k colE 0 x = 0
  · exact hz
  have hbound := halfCharge_le_energy_of_joint_ne_zero k hk _ _ _ hj hz
  have hn : 0 < q * (p - 1) := Nat.mul_pos hq (by omega)
  exact null_eq_zero_of_vacuumChevalley_ne_zero k hk (q * (p - 1)) p
    (Wak.Charged.vacuumChevalleyDeterminant_admissible_above_charge p q hp hq hcop
      p (by omega) (by omega)) _ hj (current_mem_maxIdeal k hk colE 0 x hi)

/-- Nonzero affine primitive states exist uniformly at every admissible
level, at the predicted first energy and horizontal highest weight. -/
theorem admissible_primitive_exists (p q : ℕ) (hp : 2 ≤ p) (hq : 0 < q)
    (hcop : p.Coprime q) :
    ∃ x : WakModule ((p : ℂ) / q - 2), x ≠ 0 ∧
      x ∈ jointSpace _ (admissible_level_noncritical p q hp hq)
        (q * (p - 1) : ℕ) (2 * ((p : ℤ) - 1)) ∧
      J _ colE 0 x = 0 ∧ SingP _ x := by
  obtain ⟨x, hxne, hx, hi⟩ := admissible_first_null p q hp hq hcop
  exact ⟨x, hxne, hx, admissible_first_null_raising p q hp hq hcop x hx hi,
    admissible_first_null_positive p q hp hq hcop x hx hi⟩

end
end VOA.AffineSl2GeneralRigidity

namespace VOA.AffineSl2BoundarySingularFamily
open AffineVOA AffineVOA.Inst AffineVOA.Strong AffineSl2GeneralRigidity
noncomputable section

/-- The uniform boundary family has a genuine nonzero affine highest state.
This is derived from the actual Gram determinant, not supplied as data. -/
theorem boundary_primitive_exists (n : ℕ) :
    ∃ x : WakModule (level n), x ≠ 0 ∧
      x ∈ jointSpace _ (level_noncritical n) (denominator n : ℕ) 2 ∧
      J _ colE 0 x = 0 ∧ SingP _ x := by
  have hc : Nat.Coprime 2 (denominator n) := by simp [denominator]
  have he := admissible_primitive_exists 2 (denominator n) (by omega)
    (by dsimp [denominator]; omega) hc
  have ht (k : ℂ) (hk : k + 2 ≠ 0)
      (hklevel : k = (2 : ℂ) / (denominator n) - 2) :
      ∃ x : WakModule k, x ≠ 0 ∧
        x ∈ jointSpace k hk (denominator n : ℕ) 2 ∧
        J k colE 0 x = 0 ∧ SingP k x := by
    subst k
    simpa using he
  exact ht (level n) (level_noncritical n) (by unfold level; ring)

/-- An unconditional `Candidate` for every boundary index. Its leading
C₂ symbol and maximal-ideal generation remain independent later theorems. -/
noncomputable def uniformCandidate (n : ℕ) (hn : 1 ≤ n) : Candidate (level n) n := by
  let x := Classical.choose (boundary_primitive_exists n)
  have hs := Classical.choose_spec (boundary_primitive_exists n)
  have hx := hs.2.1
  exact {
    indexPositive := hn
    isBoundaryLevel := rfl
    noncritical := level_noncritical n
    vector := x
    homogeneous := jointSpace_le_grading _ _ _ _ hx
    horizontalRaising := hs.2.2.1
    horizontalCharge := by simpa using ((mem_jointSpace_iff _ _ _ _ _).mp hx).2
    positiveSingular := hs.2.2.2
    nonzero := hs.1
  }

end
end VOA.AffineSl2BoundarySingularFamily
