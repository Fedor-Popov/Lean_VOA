/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2AdmissibleRigidity
import VOA.Examples.AffineSl2AdmissibleVacuumGap
import VOA.Examples.AffineSimpleQuotient

/-!
# Actual null states at every admissible affine vacuum level

The proved determinant root is converted into a nonzero vector of the actual
maximal graded ideal, with its energy and Cartan charge. This does not assert
positive-mode singularity, a leading symbol, or a character formula.
-/
namespace VOA.AffineSl2GeneralRigidity
open AffineVOA AffineVOA.HighestModule VertexOperatorAlgebra
noncomputable section
open scoped Classical

/-- A root of the actual Chevalley block supplies an honest nonzero null
state in the specified simultaneous eigenspace. -/
theorem exists_null_of_vacuumChevalley_root (k : ℂ) (hk : k + 2 ≠ 0)
    (n : ℕ) (c : ℤ) (hz : (vacuumChevalleyPolynomial n c).det.eval k = 0) :
    ∃ x : WakModule k, x ≠ 0 ∧ x ∈ jointSpace k hk n (2 * c) ∧
      x ∈ QuotVOA.maxGradedIdeal (universal k hk) := by
  classical
  have hm : ((Polynomial.evalRingHom k).mapMatrix
      (vacuumChevalleyPolynomial n c)).det = 0 := by
    rw [← RingHom.map_det]
    exact hz
  obtain ⟨r, hrne, hr⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hm
  let x : WakModule k := ∑ i, r i • currentPBWBasis k hk i.val
  have hx : x ∈ jointSpace k hk n (2 * c) :=
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, rfl⟩))
  refine ⟨x, ?_, hx, ?_⟩
  · intro he
    have hc := Fintype.linearIndependent_iff.mp
      (jointWords_linearIndependent k hk n (2 * c)) r he
    exact hrne (funext hc)
  · apply (vacuumChevalley_ideal_iff k hk x).mp
    apply vacuumChevalley_kernel_ideal k hk n c r
    intro j
    have hh := congrFun hr j
    simpa only [Matrix.vecMul, dotProduct, RingHom.mapMatrix_apply,
      Matrix.map_apply, Pi.zero_apply] using hh

/-- A nonsingular actual Chevalley block has zero intersection with the
maximal graded ideal. -/
theorem null_eq_zero_of_vacuumChevalley_ne_zero (k : ℂ) (hk : k + 2 ≠ 0)
    (n : ℕ) (c : ℤ) (hd : (vacuumChevalleyPolynomial n c).det.eval k ≠ 0)
    (x : WakModule k) (hx : x ∈ jointSpace k hk n (2 * c))
    (hi : x ∈ QuotVOA.maxGradedIdeal (universal k hk)) : x = 0 := by
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
  have ht := (vacuumChevalley_ideal_iff k hk x).mpr hi
  have hz := (LiRadical.mem_maxGradedIdeal_iff (universalForm_invariant k hk)
    (universalForm_normalized k hk)).mp ht
  have hm : ((Polynomial.evalRingHom k).mapMatrix
      (vacuumChevalleyPolynomial n c)).det ≠ 0 := by
    rw [← RingHom.map_det]
    exact hd
  have hv : Matrix.vecMul r ((Polynomial.evalRingHom k).mapMatrix
      (vacuumChevalleyPolynomial n c)) = 0 := by
    funext j
    change (∑ i, r i * (vacuumChevalleyPolynomial n c i j).eval k) = 0
    have he := hz (currentPBWBasis k hk j.val)
    rw [← hr] at he
    simpa only [vacuumChevalleyPolynomial_actual k hk,
      map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using he
  have hr0 := Matrix.eq_zero_of_vecMul_eq_zero hm hv
  rw [← hr, hr0]
  simp

/-- In every admissible joint block below the first root, an actual null
state vanishes. The displayed principal bound is automatic in occupied
positive-energy vacuum blocks. -/
theorem admissible_null_eq_zero_below (p q : ℕ) (hp : 2 ≤ p) (hq : 0 < q)
    (hcop : p.Coprime q) (n : ℕ) (c : ℤ) (hn : n < q * (p - 1))
    (hc : 0 < 2 * (n : ℤ) - c)
    (x : WakModule ((p : ℂ) / q - 2))
    (hx : x ∈ jointSpace _ (admissible_level_noncritical p q hp hq) n (2 * c))
    (hi : x ∈ QuotVOA.maxGradedIdeal
      (universal _ (admissible_level_noncritical p q hp hq))) : x = 0 := by
  exact null_eq_zero_of_vacuumChevalley_ne_zero _ _ n c
    (Wak.Charged.vacuumChevalleyDeterminant_admissible_below p q hp hq hcop n c hn hc)
    x hx hi

/-- A nonzero occupied vacuum block cannot have half-charge larger than
its energy. This is a property of actual PBW words. -/
theorem halfCharge_le_energy_of_joint_ne_zero (k : ℂ) (hk : k + 2 ≠ 0)
    (n c : ℤ) (x : WakModule k) (hx : x ∈ jointSpace k hk n (2 * c))
    (hne : x ≠ 0) : c ≤ n := by
  by_contra hc
  have hempty : IsEmpty (JointIndex n (2 * c)) := by
    refine ⟨fun i => ?_⟩
    have hb := Sl2NonLisse.wordCharge_le_twice_wordDeg
      (AffineSl2PBWWakimotoReduction.orderedPBWColorWord i.val)
    change currentCharge i.val ≤ 2 * currentEnergy i.val at hb
    rw [i.property.1, i.property.2] at hb
    omega
  have hz : jointSpace k hk n (2 * c) = ⊥ := by
    simp [jointSpace]
  rw [hz, Submodule.mem_bot] at hx
  exact hne hx

/-- The actual maximal ideal has no joint states below the first
admissible energy; the auxiliary principal-bound premise is removed. -/
theorem admissible_null_eq_zero_below_all (p q : ℕ) (hp : 2 ≤ p) (hq : 0 < q)
    (hcop : p.Coprime q) (n : ℕ) (c : ℤ) (hn : n < q * (p - 1))
    (x : WakModule ((p : ℂ) / q - 2))
    (hx : x ∈ jointSpace _ (admissible_level_noncritical p q hp hq) n (2 * c))
    (hi : x ∈ QuotVOA.maxGradedIdeal
      (universal _ (admissible_level_noncritical p q hp hq))) : x = 0 := by
  by_cases hz : x = 0
  · exact hz
  have hcharge := halfCharge_le_energy_of_joint_ne_zero _ _ n c x hx hz
  by_cases hn0 : n = 0
  · subst n
    have hg := jointSpace_le_grading _ (admissible_level_noncritical p q hp hq) 0
      (2 * c) hx
    have hm : x ∈ QuotVOA.maxGradedIdeal
        (universal _ (admissible_level_noncritical p q hp hq)) ⊓
        (universal _ (admissible_level_noncritical p q hp hq)).grading 0 := ⟨hi, hg⟩
    rw [SimpleQuot.maxGradedIdeal_inf_grading_zero_eq_bot _
      (Wak.vacuumA_ne_zero_free _ (admissible_level_noncritical p q hp hq)),
      Submodule.mem_bot] at hm
    exact hm
  · exact admissible_null_eq_zero_below p q hp hq hcop n c hn (by omega) x hx hi

/-- Uniform nonzero null states at the first admissible vacuum energy.
The determinant theorem discharges the root premise for the actual VOA. -/
theorem admissible_first_null (p q : ℕ) (hp : 2 ≤ p) (hq : 0 < q)
    (hcop : p.Coprime q) :
    ∃ x : WakModule ((p : ℂ) / q - 2), x ≠ 0 ∧
      x ∈ jointSpace _ (admissible_level_noncritical p q hp hq)
        (q * (p - 1) : ℕ) (2 * ((p : ℤ) - 1)) ∧
      x ∈ QuotVOA.maxGradedIdeal
        (universal _ (admissible_level_noncritical p q hp hq)) := by
  exact exists_null_of_vacuumChevalley_root _ _ _ _
    (Wak.Charged.vacuumChevalleyDeterminant_admissible_simple p q hp hq hcop).1

/-- At odd boundary denominator `2m+1`, the actual null state has exactly
energy `2m+1` and horizontal charge two. -/
theorem boundary_first_null (m : ℕ) :
    ∃ x : WakModule ((2 : ℂ) / (2 * m + 1 : ℕ) - 2), x ≠ 0 ∧
      x ∈ jointSpace _
        (admissible_level_noncritical 2 (2 * m + 1) (by omega) (by omega))
        (2 * m + 1 : ℕ) 2 ∧
      x ∈ QuotVOA.maxGradedIdeal (universal _
        (admissible_level_noncritical 2 (2 * m + 1) (by omega) (by omega))) := by
  have hc : Nat.Coprime 2 (2 * m + 1) := by simp
  simpa using admissible_first_null 2 (2 * m + 1) (by omega) (by omega) hc

end
end VOA.AffineSl2GeneralRigidity
