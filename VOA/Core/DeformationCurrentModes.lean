/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.DeformationReconstruction

/-!
# Current commutators in a regular first-order deformation

The linearized Jacobi identity controls modes acting on every state, even when
regularity is known only for pairs of weight-one currents. Its commutator slice
shows that regular current lifts obey the original Lie brackets: the derivative
of the central term is zero. This is the operator relation needed before using
the universal affine vacuum representation. It does not prove that evaluation
has a one-dimensional weight-zero image or that the generated carrier separates
the pure first-order vacuum.
-/
namespace VOA.Deform
open VertexOperatorAlgebra
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {W : VertexOperatorAlgebra V} (D : FirstOrderDeformation W)

/-- Set the iterate index to zero in linearized Jacobi. The left finite sum
collapses, leaving the first-order commutator of two modes at arbitrary indices. -/
theorem jacobi_mode_commutator (u v x : V) (m n : ℤ) :
    D.smul₁ u m (W.smul v n x) + W.smul u m (D.smul₁ v n x)
      - (D.smul₁ v n (W.smul u m x) + W.smul v n (D.smul₁ u m x))
    = ∑ᶠ i : ℤ, cbz m i •
        (W.smul (D.smul₁ u i v) (m + n - i) x
          + D.smul₁ (W.smul u i v) (m + n - i) x) := by
  have h := D.jacobi u v x 0 m n
  rw [finsum_eq_single _ (0 : ℤ)
    (fun i hi => by rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul])] at h
  simpa only [cbz_zero_left, if_pos rfl, mul_one, one_smul, negOnePow,
    Even.zero, if_pos, zero_add, add_zero, sub_zero] using h

/-- A current product above the first positive mode has negative weight and
therefore vanishes in a VOA of CFT type. -/
theorem current_product_high {a b : V} (ha : a ∈ W.grading 1)
    (hb : b ∈ W.grading 1) {i : ℤ} (hi : 2 ≤ i) : W.smul a i b = 0 := by
  have h := W.smul_mem_grading ha hb i
  rw [W.positivity _ (by omega), Submodule.mem_bot] at h
  exact h

/-- The first positive product of two currents is a multiple of the vacuum.
Every deformation field annihilates that state in its first argument, by the
vacuum axiom and linearity, so it contributes no differentiated central term. -/
theorem deformation_of_current_pole {a b : V} (ha : a ∈ W.grading 1)
    (hb : b ∈ W.grading 1) (n : ℤ) (x : V) :
    D.smul₁ (W.smul a 1 b) n x = 0 := by
  have h := W.smul_mem_grading ha hb 1
  norm_num only at h
  rw [W.vacuum_grade] at h
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
  rw [← hc, D.smul₁_smul_left, D.smul₁_vacuum_left, smul_zero]

/-- For regular current pairs, all terms of the differentiated commutator
vanish except the zero-mode Lie bracket. This identity holds on every state
and at all integer mode indices; regularity is used only on the current pair. -/
theorem regular_current_commutator (hreg : D.Regular) {a b : V}
    (ha : a ∈ W.grading 1) (hb : b ∈ W.grading 1) (x : V) (m n : ℤ) :
    D.smul₁ a m (W.smul b n x) + W.smul a m (D.smul₁ b n x)
      - (D.smul₁ b n (W.smul a m x) + W.smul b n (D.smul₁ a m x))
    = D.smul₁ (W.smul a 0 b) (m + n) x := by
  rw [jacobi_mode_commutator]
  rw [finsum_eq_single _ (0 : ℤ) (fun i hi => by
    by_cases hn : i < 0
    · rw [cbz_apply_neg m hn, zero_smul]
    · rw [hreg a ha b hb i (by omega), PreVertexAlgebra.smul_zero_left, zero_add]
      by_cases h1 : i = 1
      · subst i
        rw [deformation_of_current_pole D ha hb, smul_zero]
      · rw [current_product_high ha hb (by omega), D.smul₁_zero_left, smul_zero])]
  rw [cbz_zero, one_smul, hreg a ha b hb 0 (by omega),
    PreVertexAlgebra.smul_zero_left, zero_add, sub_zero]


/-- A graded deformation cannot create current products in negative grades. -/
theorem deformation_current_product_high (hD : D.IsGraded) {a b : V}
    (ha : a ∈ W.grading 1) (hb : b ∈ W.grading 1) {i : ℤ} (hi : 2 ≤ i) :
    D.smul₁ a i b = 0 := by
  have h := hD 1 1 a ha b hb i
  rw [W.positivity _ (by omega), Submodule.mem_bot] at h
  exact h

/-- After the zero-mode correction has been normalized away, the only extra
current commutator is central. Its coefficient is exactly the deformation's
first positive product, rather than a separately postulated level parameter.
This derives an operator identity from an arbitrary normalized graded deformation;
it does not yet imply the singular-vector scalar obstruction equations. -/
theorem poleForm_current_commutator (hD : D.IsGraded) (hnorm : D.InPoleForm)
    {a b : V} (ha : a ∈ W.grading 1) (hb : b ∈ W.grading 1)
    (δ : ℂ) (hpole : D.HasPoleCoeff a b δ) (x : V) (m n : ℤ) :
    D.smul₁ a m (W.smul b n x) + W.smul a m (D.smul₁ b n x)
      - (D.smul₁ b n (W.smul a m x) + W.smul b n (D.smul₁ a m x))
    = D.smul₁ (W.smul a 0 b) (m + n) x
      + if m + n = 0 then ((m : ℂ) * δ) • x else 0 := by
  rw [jacobi_mode_commutator]
  let F : ℤ → V := fun i => cbz m i •
    (W.smul (D.smul₁ a i b) (m + n - i) x
      + D.smul₁ (W.smul a i b) (m + n - i) x)
  have hsupp : Function.support F ⊆ (↑({0, 1} : Finset ℤ) : Set ℤ) := by
    intro i hi
    by_contra hh
    have h0 : i ≠ 0 := by simpa using fun h : i = 0 => hh (by simp [h])
    have h1 : i ≠ 1 := by simpa using fun h : i = 1 => hh (by simp [h])
    apply hi
    dsimp [F]
    by_cases hn : i < 0
    · rw [cbz_apply_neg m hn, zero_smul]
    · rw [deformation_current_product_high D hD ha hb (by omega),
        current_product_high ha hb (by omega), PreVertexAlgebra.smul_zero_left,
        D.smul₁_zero_left, add_zero, smul_zero]
  change (∑ᶠ i : ℤ, F i) = _
  rw [finsum_eq_sum_of_support_subset F hsupp]
  have hb1 : cbz m 1 = (m : ℂ) := by simp [cbz, gBinom]
  have hp : D.smul₁ a 1 b = δ • W.vacuum := hpole.symm
  simp only [Finset.sum_insert, Finset.mem_singleton, zero_ne_one, not_false_eq_true,
    Finset.sum_singleton, F, cbz_zero, one_smul, sub_zero, hnorm a ha b hb,
    PreVertexAlgebra.smul_zero_left, zero_add, hp, hb1,
    deformation_of_current_pole D ha hb, add_zero, PreVertexAlgebra.smul_smul_left,
    PreVertexAlgebra.smul_vacuum_left]
  by_cases hmn : m + n = 0
  · simp [hmn, smul_smul]
  · have hmn' : m + n - 1 ≠ -1 := by omega
    simp [hmn, hmn']

end VOA.Deform
