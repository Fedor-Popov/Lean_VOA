/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.VirasoroLengthTwoBoundarySemantic
import VOA.Examples.VirasoroBoundaryRealStructure

/-!
# Boundary Virasoro graded unitarity through filtration degree two

This file packages the orthogonal tower calculations into the actual layers of the Virasoro
length flag.  The result is deliberately bounded: it proves clauses (iv) and (vi) only for
filtration degrees `p ≤ 2`.  The final theorem uses the canonical boundary-model real structure,
so it has no real-structure hypothesis and introduces no existence axiom.
-/

set_option linter.style.longLine false

namespace VOA

namespace VirGradedUnitarity

open VOA.VirModule VOA.VirSimple VOA.VirGoodFil
open VOA.VirQuotForm VOA.VertexOperatorAlgebra

/-! ## General finite orthogonal-basis positivity -/

section OrthogonalPositivity

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

private theorem sesq_sum_left (h : SesqForm E) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → E) (y : E) :
    h (∑ i ∈ s, v i) y = ∑ i ∈ s, h (v i) y := by
  induction s using Finset.induction_on with
  | empty => simp [h.zero_left]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, h.add_left, ih]

private theorem sesq_sum_right (h : SesqForm E) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : E) (v : ι → E) :
    h x (∑ i ∈ s, v i) = ∑ i ∈ s, h x (v i) := by
  induction s using Finset.induction_on with
  | empty => simp [h.zero_right]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, h.add_right, ih]

/-- A finite orthogonal basis with strictly positive real diagonal makes a sesquilinear form
positive definite.  This is the coordinate lemma needed to pass from tower norms to arbitrary
complex linear combinations. -/
theorem isPosOn_top_of_orthogonal_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : SesqForm E) (e : Module.Basis ι ℂ E)
    (horth : ∀ i j : ι, i ≠ j → h (e i) (e j) = 0)
    (hdiag : ∀ i : ι, ∃ r : ℝ, 0 < r ∧ h (e i) (e i) = (r : ℂ)) :
    IsPosOn h (⊤ : Submodule ℂ E) := by
  intro x _ hx
  classical
  choose r hrpos hrdiag using hdiag
  let a : ι → ℂ := fun i => e.repr x i
  have ha : ∃ i : ι, a i ≠ 0 := by
    by_contra hzero
    push Not at hzero
    apply hx
    apply e.repr.injective
    ext i
    simpa [a] using hzero i
  let q : ι → ℝ := fun i => Complex.normSq (a i) * r i
  have hq_nonneg : ∀ i, 0 ≤ q i := fun i => mul_nonneg (Complex.normSq_nonneg _) (le_of_lt (hrpos i))
  have hq_pos : ∃ i, 0 < q i := by
    obtain ⟨i, hi⟩ := ha
    exact ⟨i, mul_pos (Complex.normSq_pos.2 hi) (hrpos i)⟩
  refine ⟨∑ i, q i, Finset.sum_pos' (fun i _ => hq_nonneg i)
    (by obtain ⟨i, hi⟩ := hq_pos; exact ⟨i, Finset.mem_univ _, hi⟩), ?_⟩
  have hexpand :
      h x x = ∑ i : ι, ((starRingEnd ℂ) (a i) * a i) * h (e i) (e i) := by
    calc
      h x x = h (∑ i : ι, a i • e i) (∑ i : ι, a i • e i) := by
        simp only [a, e.sum_repr]
      _ = _ := by
        rw [sesq_sum_left]
        apply Finset.sum_congr rfl
        intro i _
        rw [h.smul_left, sesq_sum_right]
        rw [Finset.sum_eq_single i]
        · rw [h.smul_right]
          ring
        · intro j _ hji
          rw [h.smul_right, horth i j hji.symm]
          simp
        · intro hi
          exact absurd (Finset.mem_univ i) hi
  rw [hexpand]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [hrdiag i, ← Complex.normSq_eq_conj_mul_self]
  dsimp [q]
  push_cast
  ring

/-- Restriction of a sesquilinear form to a complex submodule. -/
private def sesqRestrict (h : SesqForm E) (S : Submodule ℂ E) : SesqForm S where
  toFun x y := h (x : E) (y : E)
  add_left x y z := h.add_left x y z
  smul_left a x y := h.smul_left a x y
  add_right x y z := h.add_right x y z
  smul_right a x y := h.smul_right a x y

/-- Orthogonal positive generators give positivity on their entire complex span. -/
theorem isPosOn_span_of_orthogonal_family {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : SesqForm E) (v : ι → E) (hv : LinearIndependent ℂ v)
    (horth : ∀ i j : ι, i ≠ j → h (v i) (v j) = 0)
    (hdiag : ∀ i : ι, ∃ r : ℝ, 0 < r ∧ h (v i) (v i) = (r : ℂ)) :
    IsPosOn h (Submodule.span ℂ (Set.range v)) := by
  let S := Submodule.span ℂ (Set.range v)
  let e : Module.Basis ι ℂ S := Module.Basis.span hv
  have htop : IsPosOn (sesqRestrict h S) (⊤ : Submodule ℂ S) := by
    apply isPosOn_top_of_orthogonal_basis (sesqRestrict h S) e
    · intro i j hij
      change h ((e i : S) : E) ((e j : S) : E) = 0
      rw [show ((e i : S) : E) = v i by
        exact congrArg Subtype.val (Module.Basis.span_apply hv i),
        show ((e j : S) : E) = v j by
          exact congrArg Subtype.val (Module.Basis.span_apply hv j)]
      exact horth i j hij
    · intro i
      change ∃ r : ℝ, 0 < r ∧ h ((e i : S) : E) ((e i : S) : E) = (r : ℂ)
      rw [show ((e i : S) : E) = v i by
        exact congrArg Subtype.val (Module.Basis.span_apply hv i)]
      exact hdiag i
  intro x hx hne
  let xS : S := ⟨x, hx⟩
  have hxSne : xS ≠ 0 := fun hz => hne (by simpa [xS] using congrArg Subtype.val hz)
  obtain ⟨r, hr, hval⟩ := htop xS Submodule.mem_top hxSne
  exact ⟨r, hr, hval⟩

/-- An orthogonal family with nonzero diagonal makes the bilinear form nondegenerate on its
span. -/
theorem restrict_span_nondegenerate_of_orthogonal_family {ι : Type*}
    (β : LinearMap.BilinForm ℂ E) (v : ι → E) (hv : LinearIndependent ℂ v)
    (horth : ∀ i j : ι, i ≠ j → β (v i) (v j) = 0)
    (hdiag : ∀ i : ι, β (v i) (v i) ≠ 0) :
    (β.restrict (Submodule.span ℂ (Set.range v))).Nondegenerate := by
  let e : Module.Basis ι ℂ (Submodule.span ℂ (Set.range v)) := Module.Basis.span hv
  apply LinearMap.IsOrthoᵢ.nondegenerate_of_not_isOrtho_basis_self e
  · rw [LinearMap.isOrthoᵢ_def]
    intro i j hij
    simpa [e, LinearMap.IsOrtho] using horth i j hij
  · intro i
    simpa [e, LinearMap.IsOrtho] using hdiag i

end OrthogonalPositivity

/-! ## The degree-one step -/

/-- In weight `N ≥ 2`, the universal length-one filtration step is exactly the line generated by
the stress-tensor global descendant. -/
theorem virFil_one_eq_span_lengthOne (c : ℂ) (N : ℕ) (hN : 2 ≤ N) :
    virFil c 1 (N : ℤ) = ℂ ∙ lengthOneTowerAt c N := by
  apply le_antisymm
  · rw [virFil, Submodule.span_le]
    rintro _ ⟨w, hw, henergy, hlength, rfl⟩
    cases w with
    | nil =>
        have hzero : N = 0 := by exact_mod_cast henergy.symm
        omega
    | cons i rest =>
        have hrest : rest = [] := by
          apply List.length_eq_zero_iff.mp
          simp only [List.length_cons] at hlength
          omega
        subst rest
        have hi : i = N - 2 := by
          simp only [energyVir_cons, energyVir_nil] at henergy
          omega
        subst i
        apply Submodule.mem_span_singleton.mpr
        refine ⟨(((N - 2).factorial : ℂ))⁻¹, ?_⟩
        rw [lengthOneTowerAt_eq, smul_smul]
        have hfac : (((N - 2).factorial : ℂ)) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero (N - 2)
        rw [inv_mul_cancel₀ hfac, one_smul]
  · rw [Submodule.span_le]
    rintro _ rfl
    exact lengthOneTowerAt_mem_virFil c N hN

/-- The same exact line after passage to the simple quotient. -/
theorem goodFil_one_eq_span_boundaryLengthOne (n N : ℕ) (hN : 2 ≤ N) :
    goodFil (boundaryCharge n) 1 (N : ℤ) = ℂ ∙ boundaryLengthOneTowerAt n N := by
  rw [goodFil, virFil_one_eq_span_lengthOne (boundaryCharge n) N hN,
    Submodule.map_span]
  congr 1
  rw [Set.image_singleton]
  congr 1
  rw [boundaryLengthOneTowerAt, lengthOneTowerAt, mkQ_L_pow]
  rfl

/-! ## Towers inside the weight-space subtype -/

/-- A retained tower, regarded as a vector of the weight-`N` subspace. -/
noncomputable def boundaryTowerIn (n N : ℕ) (hn : 2 ≤ n) (hN : 2 ≤ N)
    (m : BoundaryLengthLETwoTowerIndex n N) :
    (virasoroSimple (boundaryCharge n)).grading (N : ℤ) :=
  ⟨boundaryLengthLETwoTowerAt n N m,
    goodFil_le_grading (boundaryCharge n) 2 (N : ℤ) (by
      rw [goodFil_two_eq_span_boundaryTowers n N hn hN]
      exact Submodule.subset_span ⟨m, rfl⟩)⟩

@[simp] theorem coe_boundaryTowerIn (n N : ℕ) (hn : 2 ≤ n) (hN : 2 ≤ N)
    (m : BoundaryLengthLETwoTowerIndex n N) :
    (boundaryTowerIn n N hn hN m :
      VirUniv (boundaryCharge n) ⧸ maxIdealVir (boundaryCharge n)) =
        boundaryLengthLETwoTowerAt n N m := rfl

/-- The unique retained index of filtration degree one. -/
def boundaryStressIndex (n N : ℕ) (hN : 2 ≤ N) :
    BoundaryLengthLETwoTowerIndex n N :=
  ⟨⟨1, ⟨by omega, by simpa using hN⟩⟩, Or.inr (by norm_num)⟩

@[simp] theorem boundaryStressIndex_val (n N : ℕ) (hN : 2 ≤ N) :
    (boundaryStressIndex n N hN).1.1 = 1 := rfl

@[simp] theorem boundaryTowerIn_stress (n N : ℕ) (hn : 2 ≤ n) (hN : 2 ≤ N) :
    boundaryTowerIn n N hn hN (boundaryStressIndex n N hN) =
      ⟨boundaryLengthOneTowerAt n N,
        goodFil_le_grading (boundaryCharge n) 2 (N : ℤ) (by
          rw [goodFil_two_eq_span_boundaryTowers n N hn hN]
          exact Submodule.subset_span ⟨boundaryStressIndex n N hN, rfl⟩)⟩ := by
  apply Subtype.ext
  simp [boundaryTowerIn, boundaryLengthLETwoTowerAt]

/-- The retained length-two indices (`m ≥ 2`), excluding the stress-tensor tower. -/
def BoundaryLengthTwoTowerIndex (n N : ℕ) :=
  {m : BoundaryLengthLETwoTowerIndex n N // 2 ≤ m.1.1}

instance (n N : ℕ) : DecidableEq (BoundaryLengthTwoTowerIndex n N) :=
  Subtype.instDecidableEq

noncomputable instance (n N : ℕ) : Fintype (BoundaryLengthTwoTowerIndex n N) :=
  Fintype.subtype
    ((Finset.univ : Finset (BoundaryLengthLETwoTowerIndex n N)).filter fun m => 2 ≤ m.1.1) (by
      intro m
      simp)

/-- The length-two tower subspace in weight `N`. -/
noncomputable def boundaryLengthTwoSpan (n N : ℕ) (hn : 2 ≤ n) (hN : 2 ≤ N) :
    Submodule ℂ ((virasoroSimple (boundaryCharge n)).grading (N : ℤ)) :=
  Submodule.span ℂ
    (Set.range fun m : BoundaryLengthTwoTowerIndex n N => boundaryTowerIn n N hn hN m.1)

/-- The official degree-one flag step is the stress-tensor tower line. -/
theorem pieceIn_one_eq_span_stress (n N : ℕ) (hn : 2 ≤ n) (hN : 2 ≤ N) :
    (virGradedFlag (boundaryCharge n)).pieceIn 1 (N : ℤ) =
      ℂ ∙ boundaryTowerIn n N hn hN (boundaryStressIndex n N hN) := by
  ext x
  constructor
  · intro hx
    have hx' : (x : VirUniv (boundaryCharge n) ⧸ maxIdealVir (boundaryCharge n)) ∈
        goodFil (boundaryCharge n) 1 (N : ℤ) := hx
    rw [goodFil_one_eq_span_boundaryLengthOne n N hN,
      Submodule.mem_span_singleton] at hx'
    obtain ⟨a, ha⟩ := hx'
    rw [Submodule.mem_span_singleton]
    refine ⟨a, ?_⟩
    apply Subtype.ext
    simpa [boundaryTowerIn, boundaryLengthLETwoTowerAt] using ha
  · intro hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨a, rfl⟩ := hx
    apply Submodule.smul_mem
    change boundaryLengthLETwoTowerAt n N (boundaryStressIndex n N hN) ∈
      goodFil (boundaryCharge n) 1 (N : ℤ)
    rw [boundaryLengthLETwoTowerAt, dif_pos (by rfl),
      goodFil_one_eq_span_boundaryLengthOne n N hN]
    exact Submodule.mem_span_singleton_self _

/-- The official degree-two flag step is the span of all retained towers. -/
theorem pieceIn_two_eq_span_boundaryTowerIn (n N : ℕ) (hn : 2 ≤ n) (hN : 2 ≤ N) :
    (virGradedFlag (boundaryCharge n)).pieceIn 2 (N : ℤ) =
      Submodule.span ℂ (Set.range (boundaryTowerIn n N hn hN)) := by
  ext x
  constructor
  · intro hx
    have hx' : (x : VirUniv (boundaryCharge n) ⧸ maxIdealVir (boundaryCharge n)) ∈
        Submodule.span ℂ (Set.range (boundaryLengthLETwoTowerAt n N)) := by
      rw [← goodFil_two_eq_span_boundaryTowers n N hn hN]
      exact hx
    obtain ⟨a, ha⟩ :=
      (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx'
    apply (Submodule.mem_span_range_iff_exists_fun ℂ).mpr
    refine ⟨a, ?_⟩
    apply Subtype.ext
    simpa using ha
  · intro hx
    obtain ⟨a, ha⟩ :=
      (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
    change (x : VirUniv (boundaryCharge n) ⧸ maxIdealVir (boundaryCharge n)) ∈
      goodFil (boundaryCharge n) 2 (N : ℤ)
    rw [goodFil_two_eq_span_boundaryTowers n N hn hN]
    apply (Submodule.mem_span_range_iff_exists_fun ℂ).mpr
    refine ⟨a, ?_⟩
    simpa using congrArg Subtype.val ha

/-- The retained tower family remains linearly independent inside the weight-space subtype. -/
theorem boundaryTowerIn_linearIndependent (n N : ℕ) (hn : 2 ≤ n) (hN : 2 ≤ N) :
    LinearIndependent ℂ (boundaryTowerIn n N hn hN) := by
  apply LinearIndependent.of_comp
    ((virasoroSimple (boundaryCharge n)).grading (N : ℤ)).subtype
  simpa [Function.comp_def] using boundaryLengthLETwoTowerAt_linearIndependent n N hn

/-- The retained towers as a basis of the official degree-two flag step. -/
noncomputable def boundaryPieceInTwoTowerBasis (n N : ℕ) (hn : 2 ≤ n) (hN : 2 ≤ N) :
    Module.Basis (BoundaryLengthLETwoTowerIndex n N) ℂ
      ((virGradedFlag (boundaryCharge n)).pieceIn 2 (N : ℤ)) :=
  (Module.Basis.span (boundaryTowerIn_linearIndependent n N hn hN)).map
    (LinearEquiv.ofEq _ _ (pieceIn_two_eq_span_boundaryTowerIn n N hn hN).symm)

/-! ## Identification of the first two official layers -/

theorem pieceIn_zero_eq_bot_of_two_le (n N : ℕ) (hN : 2 ≤ N) :
    (virGradedFlag (boundaryCharge n)).pieceIn 0 (N : ℤ) = ⊥ := by
  ext x
  change (x : VirUniv (boundaryCharge n) ⧸ maxIdealVir (boundaryCharge n)) ∈
    goodFil (boundaryCharge n) 0 (N : ℤ) ↔ x ∈ (⊥ : Submodule ℂ _)
  rw [goodFil_zero_of_pos (boundaryCharge n) (by omega)]
  simp

/-- In positive weight, the degree-one layer is exactly the stress-tensor tower line. -/
theorem layer_one_eq_span_stress (n N : ℕ) (hn : 2 ≤ n) (hN : 2 ≤ N) :
    (virGradedFlag (boundaryCharge n)).layer (N : ℤ)
        (LiRadical.gradedForm (Bsimp (boundaryCharge n)) (N : ℤ)) 1 =
      ℂ ∙ boundaryTowerIn n N hn hN (boundaryStressIndex n N hN) := by
  rw [GradedFlag.layer, GradedFlag.pieceLT_succ,
    pieceIn_zero_eq_bot_of_two_le n N hN,
    LinearMap.BilinForm.orthogonal_bot, inf_top_eq,
    pieceIn_one_eq_span_stress n N hn hN]

/-- The degree-two step splits as the stress line plus all genuine length-two towers. -/
theorem pieceIn_two_eq_stress_sup_lengthTwo (n N : ℕ) (hn : 2 ≤ n) (hN : 2 ≤ N) :
    (virGradedFlag (boundaryCharge n)).pieceIn 2 (N : ℤ) =
      (ℂ ∙ boundaryTowerIn n N hn hN (boundaryStressIndex n N hN)) ⊔
        boundaryLengthTwoSpan n N hn hN := by
  rw [pieceIn_two_eq_span_boundaryTowerIn n N hn hN]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    by_cases hm : m.1.1 = 1
    · apply Submodule.mem_sup_left
      rw [Submodule.mem_span_singleton]
      refine ⟨1, ?_⟩
      rw [one_smul]
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      exact hm.symm
    · apply Submodule.mem_sup_right
      apply Submodule.subset_span
      exact ⟨⟨m, by have := m.1.2.1; omega⟩, rfl⟩
  · apply sup_le
    · rw [Submodule.span_singleton_le_iff_mem]
      apply Submodule.subset_span
      exact ⟨boundaryStressIndex n N hN, rfl⟩
    · rw [boundaryLengthTwoSpan, Submodule.span_le]
      rintro _ ⟨m, rfl⟩
      apply Submodule.subset_span
      exact ⟨m.1, rfl⟩

/-- Genuine length-two towers are orthogonal to the stress-tensor tower line. -/
theorem boundaryLengthTwoSpan_le_orthogonal_stress (n N : ℕ)
    (hn : 2 ≤ n) (hN : 2 ≤ N) :
    boundaryLengthTwoSpan n N hn hN ≤
      (LiRadical.gradedForm (Bsimp (boundaryCharge n)) (N : ℤ)).orthogonal
        (ℂ ∙ boundaryTowerIn n N hn hN (boundaryStressIndex n N hN)) := by
  rw [boundaryLengthTwoSpan, Submodule.span_le]
  rintro _ ⟨m, rfl⟩
  change ∀ x, x ∈ ℂ ∙ boundaryTowerIn n N hn hN (boundaryStressIndex n N hN) →
    (LiRadical.gradedForm (Bsimp (boundaryCharge n)) (N : ℤ)) x
      (boundaryTowerIn n N hn hN m.1) = 0
  intro x hx
  rw [Submodule.mem_span_singleton] at hx
  obtain ⟨a, rfl⟩ := hx
  change (Bsimp (boundaryCharge n)).form
    (a • boundaryLengthLETwoTowerAt n N (boundaryStressIndex n N hN))
    (boundaryLengthLETwoTowerAt n N m.1) = 0
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul,
    Bsimp_boundaryLengthLETwoTowerAt_orthogonal n N hn]
  · exact mul_zero _
  · intro heq
    have hval := congrArg (fun k : BoundaryLengthLETwoTowerIndex n N => k.1.1) heq
    have hm2 := m.2
    simp only [boundaryStressIndex_val] at hval
    omega

/-- In positive weight, the official degree-two layer is exactly the span of the genuine
length-two towers. -/
theorem layer_two_eq_lengthTwoSpan (n N : ℕ) (hn : 2 ≤ n) (hN : 2 ≤ N) :
    (virGradedFlag (boundaryCharge n)).layer (N : ℤ)
        (LiRadical.gradedForm (Bsimp (boundaryCharge n)) (N : ℤ)) 2 =
      boundaryLengthTwoSpan n N hn hN := by
  let β := LiRadical.gradedForm (Bsimp (boundaryCharge n)) (N : ℤ)
  let s := boundaryTowerIn n N hn hN (boundaryStressIndex n N hN)
  rw [GradedFlag.layer, GradedFlag.pieceLT_succ,
    pieceIn_one_eq_span_stress n N hn hN]
  apply le_antisymm
  · intro x hx
    have hxpiece : x ∈ (ℂ ∙ s) ⊔ boundaryLengthTwoSpan n N hn hN := by
      rw [← pieceIn_two_eq_stress_sup_lengthTwo n N hn hN]
      exact hx.1
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hxpiece
    rw [Submodule.mem_span_singleton] at hy
    obtain ⟨a, rfl⟩ := hy
    have hxorth := hx.2
    change ∀ y, y ∈ ℂ ∙ s → β y x = 0 at hxorth
    have hxs : β s x = 0 := hxorth s (Submodule.mem_span_singleton_self s)
    have hzs : β s z = 0 := boundaryLengthTwoSpan_le_orthogonal_stress n N hn hN hz
      s (Submodule.mem_span_singleton_self s)
    rw [← hyz, map_add, map_smul, hzs, add_zero] at hxs
    simp only [smul_eq_mul] at hxs
    have hdiag : β s s ≠ 0 := by
      change (Bsimp (boundaryCharge n)).form
        (boundaryLengthLETwoTowerAt n N (boundaryStressIndex n N hN))
        (boundaryLengthLETwoTowerAt n N (boundaryStressIndex n N hN)) ≠ 0
      exact Bsimp_boundaryLengthLETwoTowerAt_self_ne_zero n N hn _
    have ha : a = 0 := (mul_eq_zero.mp hxs).resolve_right hdiag
    rw [ha, zero_smul, zero_add] at hyz
    rwa [hyz] at hz
  · intro x hx
    constructor
    · rw [pieceIn_two_eq_stress_sup_lengthTwo n N hn hN]
      exact Submodule.mem_sup_right hx
    · change ∀ y, y ∈ ℂ ∙ boundaryTowerIn n N hn hN (boundaryStressIndex n N hN) →
        (LiRadical.gradedForm (Bsimp (boundaryCharge n)) (N : ℤ)) y x = 0
      exact boundaryLengthTwoSpan_le_orthogonal_stress n N hn hN hx

/-! ## Nondegeneracy and positivity in weights `N ≥ 2` -/

private noncomputable def boundaryStressFamily (n N : ℕ) (hn : 2 ≤ n) (hN : 2 ≤ N) :
    Fin 1 → (virasoroSimple (boundaryCharge n)).grading (N : ℤ) :=
  fun _ => boundaryTowerIn n N hn hN (boundaryStressIndex n N hN)

private theorem boundaryStressFamily_linearIndependent (n N : ℕ)
    (hn : 2 ≤ n) (hN : 2 ≤ N) :
    LinearIndependent ℂ (boundaryStressFamily n N hn hN) := by
  rw [Fintype.linearIndependent_iff]
  intro f hsum i
  have hsne : boundaryTowerIn n N hn hN (boundaryStressIndex n N hN) ≠ 0 := by
    intro h
    have h' : boundaryLengthLETwoTowerAt n N (boundaryStressIndex n N hN) = 0 := by
      simpa using congrArg Subtype.val h
    exact boundaryLengthLETwoTowerAt_ne_zero n N hn _ h'
  fin_cases i
  simp only [Fin.sum_univ_one, boundaryStressFamily] at hsum
  exact (smul_eq_zero.mp hsum).resolve_right hsne

private theorem span_boundaryStressFamily (n N : ℕ) (hn : 2 ≤ n) (hN : 2 ≤ N) :
    Submodule.span ℂ (Set.range (boundaryStressFamily n N hn hN)) =
      ℂ ∙ boundaryTowerIn n N hn hN (boundaryStressIndex n N hN) := by
  congr 1
  ext x
  simp [boundaryStressFamily, eq_comm]

private theorem boundaryLengthTwoFamily_linearIndependent (n N : ℕ)
    (hn : 2 ≤ n) (hN : 2 ≤ N) :
    LinearIndependent ℂ
      (fun m : BoundaryLengthTwoTowerIndex n N => boundaryTowerIn n N hn hN m.1) :=
  (boundaryTowerIn_linearIndependent n N hn hN).comp Subtype.val Subtype.val_injective

/-- The canonical form is nondegenerate on the degree-one flag step. -/
theorem boundary_pieceIn_one_nondegenerate (n N : ℕ) (hn : 2 ≤ n) (hN : 2 ≤ N) :
    ((LiRadical.gradedForm (Bsimp (boundaryCharge n)) (N : ℤ)).restrict
      ((virGradedFlag (boundaryCharge n)).pieceIn 1 (N : ℤ))).Nondegenerate := by
  rw [pieceIn_one_eq_span_stress n N hn hN]
  rw [← span_boundaryStressFamily n N hn hN]
  apply restrict_span_nondegenerate_of_orthogonal_family _ _
    (boundaryStressFamily_linearIndependent n N hn hN)
  · intro i j hij
    exact absurd (Subsingleton.elim i j) hij
  · intro i
    change (Bsimp (boundaryCharge n)).form
      (boundaryLengthLETwoTowerAt n N (boundaryStressIndex n N hN))
      (boundaryLengthLETwoTowerAt n N (boundaryStressIndex n N hN)) ≠ 0
    exact Bsimp_boundaryLengthLETwoTowerAt_self_ne_zero n N hn _

/-- The canonical form is nondegenerate on the full degree-two flag step. -/
theorem boundary_pieceIn_two_nondegenerate (n N : ℕ) (hn : 2 ≤ n) (hN : 2 ≤ N) :
    ((LiRadical.gradedForm (Bsimp (boundaryCharge n)) (N : ℤ)).restrict
      ((virGradedFlag (boundaryCharge n)).pieceIn 2 (N : ℤ))).Nondegenerate := by
  rw [pieceIn_two_eq_span_boundaryTowerIn n N hn hN]
  apply restrict_span_nondegenerate_of_orthogonal_family _ _
    (boundaryTowerIn_linearIndependent n N hn hN)
  · intro i j hij
    change (Bsimp (boundaryCharge n)).form
      (boundaryLengthLETwoTowerAt n N i) (boundaryLengthLETwoTowerAt n N j) = 0
    exact Bsimp_boundaryLengthLETwoTowerAt_orthogonal n N hn i j hij
  · intro i
    change (Bsimp (boundaryCharge n)).form
      (boundaryLengthLETwoTowerAt n N i) (boundaryLengthLETwoTowerAt n N i) ≠ 0
    exact Bsimp_boundaryLengthLETwoTowerAt_self_ne_zero n N hn i

/-- The signed Hermitian form is positive on the degree-one layer. -/
theorem boundary_layer_one_positive (n N : ℕ) (hn : 2 ≤ n) (hN : 2 ≤ N)
    (R : RealStructure (virasoroSimple (boundaryCharge n))) :
    IsPosOn (signedForm (gradedSesq (Bsimp (boundaryCharge n)) R (N : ℤ)) 1)
      ((virGradedFlag (boundaryCharge n)).layer (N : ℤ)
        (LiRadical.gradedForm (Bsimp (boundaryCharge n)) (N : ℤ)) 1) := by
  rw [layer_one_eq_span_stress n N hn hN]
  rw [← span_boundaryStressFamily n N hn hN]
  apply isPosOn_span_of_orthogonal_family _ _
    (boundaryStressFamily_linearIndependent n N hn hN)
  · intro i j hij
    exact absurd (Subsingleton.elim i j) hij
  · intro i
    obtain ⟨r, hr, hdiag⟩ := dif_pos (boundaryStressIndex_val n N hN) ▸
      Bsimp_boundaryLengthLETwoTowerAt_self_sign n N hn (boundaryStressIndex n N hN)
    refine ⟨r, hr, ?_⟩
    change (-1 : ℂ) ^ (1 : ℕ) * (Bsimp (boundaryCharge n)).form
      (R.rho (boundaryLengthLETwoTowerAt n N (boundaryStressIndex n N hN)))
      (boundaryLengthLETwoTowerAt n N (boundaryStressIndex n N hN)) = (r : ℂ)
    rw [rho_boundaryLengthLETwoTowerAt R, hdiag]
    norm_num

/-- The signed Hermitian form is positive on the degree-two layer. -/
theorem boundary_layer_two_positive (n N : ℕ) (hn : 2 ≤ n) (hN : 2 ≤ N)
    (R : RealStructure (virasoroSimple (boundaryCharge n))) :
    IsPosOn (signedForm (gradedSesq (Bsimp (boundaryCharge n)) R (N : ℤ)) 2)
      ((virGradedFlag (boundaryCharge n)).layer (N : ℤ)
        (LiRadical.gradedForm (Bsimp (boundaryCharge n)) (N : ℤ)) 2) := by
  rw [layer_two_eq_lengthTwoSpan n N hn hN]
  apply isPosOn_span_of_orthogonal_family _ _
    (boundaryLengthTwoFamily_linearIndependent n N hn hN)
  · intro i j hij
    change (-1 : ℂ) ^ (2 : ℕ) * (Bsimp (boundaryCharge n)).form
      (R.rho (boundaryLengthLETwoTowerAt n N i.1))
      (boundaryLengthLETwoTowerAt n N j.1) = 0
    rw [rho_boundaryLengthLETwoTowerAt R,
      Bsimp_boundaryLengthLETwoTowerAt_orthogonal n N hn]
    · norm_num
    · exact fun heq => hij (Subtype.ext heq)
  · intro i
    have hi1 : i.1.1.1 ≠ 1 := by have := i.2; omega
    obtain ⟨r, hr, hdiag⟩ := dif_neg hi1 ▸
      Bsimp_boundaryLengthLETwoTowerAt_self_sign n N hn i.1
    refine ⟨r, hr, ?_⟩
    change (-1 : ℂ) ^ (2 : ℕ) * (Bsimp (boundaryCharge n)).form
      (R.rho (boundaryLengthLETwoTowerAt n N i.1))
      (boundaryLengthLETwoTowerAt n N i.1) = (r : ℂ)
    rw [rho_boundaryLengthLETwoTowerAt R, hdiag]
    norm_num

/-! ## The honest bounded graded-unitarity predicate -/

/-- Clause (iv), restricted to filtration degrees at most two. -/
def LayerNondegenerateThroughTwo (F : GradedFlag (virasoroSimple c)) (N : ℤ)
    (β : LinearMap.BilinForm ℂ ((virasoroSimple c).grading N)) : Prop :=
  ∀ p : ℕ, p ≤ 2 → (β.restrict (F.pieceIn p N)).Nondegenerate

/-- Clause (vi), restricted to filtration degrees at most two. -/
def LayerPositiveThroughTwo (F : GradedFlag (virasoroSimple c)) (N : ℤ)
    (β : LinearMap.BilinForm ℂ ((virasoroSimple c).grading N))
    (h : SesqForm ((virasoroSimple c).grading N)) : Prop :=
  ∀ p : ℕ, p ≤ 2 → IsPosOn (signedForm h p) (F.layer N β p)

/-- Graded unitarity at one weight, honestly truncated to filtration degrees `p ≤ 2`. -/
def GradedUnitaryThroughTwoAt (F : GradedFlag (virasoroSimple c)) (N : ℤ)
    (β : LinearMap.BilinForm ℂ ((virasoroSimple c).grading N))
    (h : SesqForm ((virasoroSimple c).grading N)) : Prop :=
  LayerNondegenerateThroughTwo F N β ∧ LayerPositiveThroughTwo F N β h

/-- The full bounded statement in every weight `N ≥ 2`, conditional only on a supplied real
structure. -/
theorem boundary_gradedUnitaryThroughTwoAt_of_two_le (n N : ℕ)
    (hn : 2 ≤ n) (hN : 2 ≤ N)
    (R : RealStructure (virasoroSimple (boundaryCharge n))) :
    GradedUnitaryThroughTwoAt (virGradedFlag (boundaryCharge n)) (N : ℤ)
      (LiRadical.gradedForm (Bsimp (boundaryCharge n)) (N : ℤ))
      (gradedSesq (Bsimp (boundaryCharge n)) R (N : ℤ)) := by
  letI := (virasoroSimple (boundaryCharge n)).finrank (N : ℤ)
  constructor
  · intro p hp
    interval_cases p
    · rw [pieceIn_zero_eq_bot_of_two_le n N hN]
      exact nondegenerate_restrict_bot _
    · exact boundary_pieceIn_one_nondegenerate n N hn hN
    · exact boundary_pieceIn_two_nondegenerate n N hn hN
  · intro p hp
    interval_cases p
    · rw [GradedFlag.layer_zero, pieceIn_zero_eq_bot_of_two_le n N hN]
      exact isPosOn_bot _
    · exact boundary_layer_one_positive n N hn hN R
    · exact boundary_layer_two_positive n N hn hN R

/-! ## Zero and empty weight spaces -/

/-- If the ambient weight space is zero, the bounded graded-unitarity statement is vacuous. -/
theorem boundary_gradedUnitaryThroughTwoAt_of_grading_eq_bot (n : ℕ) (N : ℤ)
    (hgr : (virasoroSimple (boundaryCharge n)).grading N = ⊥)
    (R : RealStructure (virasoroSimple (boundaryCharge n))) :
    GradedUnitaryThroughTwoAt (virGradedFlag (boundaryCharge n)) N
      (LiRadical.gradedForm (Bsimp (boundaryCharge n)) N)
      (gradedSesq (Bsimp (boundaryCharge n)) R N) := by
  letI := (virasoroSimple (boundaryCharge n)).finrank N
  have hall (S : Submodule ℂ ((virasoroSimple (boundaryCharge n)).grading N)) : S = ⊥ := by
    apply (Submodule.eq_bot_iff S).mpr
    intro x _
    apply Subtype.ext
    have hx : (x : VirUniv (boundaryCharge n) ⧸ maxIdealVir (boundaryCharge n)) ∈
        (⊥ : Submodule ℂ (VirUniv (boundaryCharge n) ⧸ maxIdealVir (boundaryCharge n))) :=
      hgr ▸ x.2
    exact (Submodule.mem_bot ℂ).mp hx
  constructor
  · intro p _
    rw [hall ((virGradedFlag (boundaryCharge n)).pieceIn p N)]
    exact nondegenerate_restrict_bot _
  · intro p _
    rw [hall ((virGradedFlag (boundaryCharge n)).layer N
      (LiRadical.gradedForm (Bsimp (boundaryCharge n)) N) p)]
    exact isPosOn_bot _

/-- The bounded statement at weight one. -/
theorem boundary_gradedUnitaryThroughTwoAt_one (n : ℕ)
    (R : RealStructure (virasoroSimple (boundaryCharge n))) :
    GradedUnitaryThroughTwoAt (virGradedFlag (boundaryCharge n)) 1
      (LiRadical.gradedForm (Bsimp (boundaryCharge n)) 1)
      (gradedSesq (Bsimp (boundaryCharge n)) R 1) :=
  boundary_gradedUnitaryThroughTwoAt_of_grading_eq_bot n 1
    (virasoroSimple_grading_one (boundaryCharge n)) R

/-- The bounded statement at every negative weight. -/
theorem boundary_gradedUnitaryThroughTwoAt_neg (n : ℕ) (N : ℤ) (hN : N < 0)
    (R : RealStructure (virasoroSimple (boundaryCharge n))) :
    GradedUnitaryThroughTwoAt (virGradedFlag (boundaryCharge n)) N
      (LiRadical.gradedForm (Bsimp (boundaryCharge n)) N)
      (gradedSesq (Bsimp (boundaryCharge n)) R N) :=
  boundary_gradedUnitaryThroughTwoAt_of_grading_eq_bot n N
    ((virasoroSimple (boundaryCharge n)).positivity N hN) R

private noncomputable def boundaryVacuumFamily (n : ℕ) :
    Fin 1 → (virasoroSimple (boundaryCharge n)).grading 0 :=
  fun _ => vacuumIn (virasoroSimple (boundaryCharge n))

private theorem boundaryVacuumFamily_linearIndependent (n : ℕ) :
    LinearIndependent ℂ (boundaryVacuumFamily n) := by
  rw [Fintype.linearIndependent_iff]
  intro f hsum i
  have hvac : vacuumIn (virasoroSimple (boundaryCharge n)) ≠ 0 :=
    vacuumIn_ne_zero (virasoroSimple_vacuum_ne_zero (boundaryCharge n))
  fin_cases i
  simp only [Fin.sum_univ_one, boundaryVacuumFamily] at hsum
  exact (smul_eq_zero.mp hsum).resolve_right hvac

private theorem span_boundaryVacuumFamily_eq_top (n : ℕ) :
    Submodule.span ℂ (Set.range (boundaryVacuumFamily n)) = ⊤ := by
  apply eq_top_iff.mpr
  intro x _
  have hx : (x : VirUniv (boundaryCharge n) ⧸ maxIdealVir (boundaryCharge n)) ∈
      ℂ ∙ (virasoroSimple (boundaryCharge n)).vacuum := by
    rw [← (virasoroSimple (boundaryCharge n)).vacuum_grade]
    exact x.2
  rw [Submodule.mem_span_singleton] at hx
  obtain ⟨a, ha⟩ := hx
  apply (Submodule.mem_span_range_iff_exists_fun ℂ).mpr
  refine ⟨fun _ => a, ?_⟩
  simp only [Fin.sum_univ_one, boundaryVacuumFamily]
  apply Subtype.ext
  exact ha

theorem boundary_pieceIn_zero_weight_eq_top (n p : ℕ) :
    (virGradedFlag (boundaryCharge n)).pieceIn p 0 = ⊤ := by
  apply eq_top_iff.mpr
  intro x _
  change (x : VirUniv (boundaryCharge n) ⧸ maxIdealVir (boundaryCharge n)) ∈
    goodFil (boundaryCharge n) p 0
  apply goodFil_mono (boundaryCharge n) 0 (Nat.zero_le p)
  rw [goodFil_zero_zero, ← (virasoroSimple (boundaryCharge n)).vacuum_grade]
  exact x.2

private theorem boundary_weight_zero_piece_nondegenerate (n p : ℕ) :
    ((LiRadical.gradedForm (Bsimp (boundaryCharge n)) 0).restrict
      ((virGradedFlag (boundaryCharge n)).pieceIn p 0)).Nondegenerate := by
  rw [boundary_pieceIn_zero_weight_eq_top n p,
    ← span_boundaryVacuumFamily_eq_top n]
  apply restrict_span_nondegenerate_of_orthogonal_family _ _
    (boundaryVacuumFamily_linearIndependent n)
  · intro i j hij
    exact absurd (Subsingleton.elim i j) hij
  · intro i
    change (Bsimp (boundaryCharge n)).form
      (virasoroSimple (boundaryCharge n)).vacuum
      (virasoroSimple (boundaryCharge n)).vacuum ≠ 0
    rw [(Bsimp_normalized (boundaryCharge n)).vacuum_self]
    norm_num

private theorem boundary_layer_succ_zero_weight_eq_bot (n q : ℕ) :
    (virGradedFlag (boundaryCharge n)).layer 0
      (LiRadical.gradedForm (Bsimp (boundaryCharge n)) 0) (q + 1) = ⊥ := by
  rw [GradedFlag.layer, GradedFlag.pieceLT_succ,
    boundary_pieceIn_zero_weight_eq_top n (q + 1),
    boundary_pieceIn_zero_weight_eq_top n q]
  have hspan : (ℂ ∙ vacuumIn (virasoroSimple (boundaryCharge n)) :
      Submodule ℂ ((virasoroSimple (boundaryCharge n)).grading 0)) = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    rw [Submodule.mem_span_singleton]
    have hx : (x : VirUniv (boundaryCharge n) ⧸ maxIdealVir (boundaryCharge n)) ∈
        ℂ ∙ (virasoroSimple (boundaryCharge n)).vacuum := by
      rw [← (virasoroSimple (boundaryCharge n)).vacuum_grade]
      exact x.2
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨a, ha⟩ := hx
    refine ⟨a, ?_⟩
    apply Subtype.ext
    exact ha
  rw [← hspan]
  apply LinearMap.BilinForm.span_singleton_inf_orthogonal_eq_bot
  change (Bsimp (boundaryCharge n)).form
    (virasoroSimple (boundaryCharge n)).vacuum
    (virasoroSimple (boundaryCharge n)).vacuum ≠ 0
  rw [(Bsimp_normalized (boundaryCharge n)).vacuum_self]
  norm_num

/-- The complete bounded statement at weight zero. -/
theorem boundary_gradedUnitaryThroughTwoAt_zero (n : ℕ)
    (R : RealStructure (virasoroSimple (boundaryCharge n))) :
    GradedUnitaryThroughTwoAt (virGradedFlag (boundaryCharge n)) 0
      (LiRadical.gradedForm (Bsimp (boundaryCharge n)) 0)
      (gradedSesq (Bsimp (boundaryCharge n)) R 0) := by
  constructor
  · intro p _
    exact boundary_weight_zero_piece_nondegenerate n p
  · intro p hp
    interval_cases p
    · exact isPosOn_layer_zero_vacuum_simple (boundaryCharge n) R
    · rw [boundary_layer_succ_zero_weight_eq_bot n 0]
      exact isPosOn_bot _
    · rw [show (2 : ℕ) = 1 + 1 by omega,
        boundary_layer_succ_zero_weight_eq_bot n 1]
      exact isPosOn_bot _

/-! ## Assembly in every conformal weight -/

/-- The bounded graded-unitarity statement in every integer conformal weight, for an arbitrary
real structure.  The proof separates the vacuum, the empty weight-one space, the positive-weight
tower calculation, and the vanishing negative-weight spaces. -/
theorem boundary_gradedUnitaryThroughTwoAt (n : ℕ) (hn : 2 ≤ n) (N : ℤ)
    (R : RealStructure (virasoroSimple (boundaryCharge n))) :
    GradedUnitaryThroughTwoAt (virGradedFlag (boundaryCharge n)) N
      (LiRadical.gradedForm (Bsimp (boundaryCharge n)) N)
      (gradedSesq (Bsimp (boundaryCharge n)) R N) := by
  cases N with
  | ofNat N =>
      cases N with
      | zero => exact boundary_gradedUnitaryThroughTwoAt_zero n R
      | succ N =>
          cases N with
          | zero => exact boundary_gradedUnitaryThroughTwoAt_one n R
          | succ N =>
              exact boundary_gradedUnitaryThroughTwoAt_of_two_le n (N + 2) hn (by omega) R
  | negSucc N =>
      exact boundary_gradedUnitaryThroughTwoAt_neg n (Int.negSucc N) (by omega) R

/-- Boundary Virasoro graded unitarity through filtration degree two, uniformly in every
integer conformal weight.  This is unconditional: it uses `boundaryVirasoroRealStructure`. -/
theorem boundary_gradedUnitaryThroughTwo (n : ℕ) (hn : 2 ≤ n) (N : ℤ) :
    GradedUnitaryThroughTwoAt (virGradedFlag (boundaryCharge n)) N
      (LiRadical.gradedForm (Bsimp (boundaryCharge n)) N)
      (gradedSesq (Bsimp (boundaryCharge n)) (boundaryVirasoroRealStructure n) N) :=
  boundary_gradedUnitaryThroughTwoAt n hn N (boundaryVirasoroRealStructure n)

end VirGradedUnitarity

end VOA
