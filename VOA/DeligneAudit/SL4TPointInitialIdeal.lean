import VOA.DeligneAudit.SL4TPointDegreeFiltration
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! The homogeneous relation ideal obtained by taking highest degrees on a finite point set. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial

variable {ι σ : Type*}

/-- Multiplication by a polynomial of bounded degree shifts the point-function filtration. -/
theorem pointDegreeFiltration_mul (x : ι → σ → ℂ) (n m : ℕ)
    (p : MvPolynomial σ ℂ) (hp : p.totalDegree ≤ m) (f : ι → ℂ)
    (hf : f ∈ pointDegreeFiltration x n) :
    finitePointEvaluation x p * f ∈ pointDegreeFiltration x (m + n) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨q, hq, rfl⟩ := hf
      rw [← map_mul]
      exact Submodule.subset_span ⟨p * q,
        (totalDegree_mul p q).trans_lt (Nat.add_lt_add_of_le_of_lt hp hq), rfl⟩
  | zero => simpa using (pointDegreeFiltration x (m + n)).zero_mem
  | add f g _ _ hf hg =>
      rw [mul_add]
      exact Submodule.add_mem _ hf hg
  | smul c f _ hf =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ c hf

/-- A bounded polynomial is the sum of its homogeneous pieces up to that bound. -/
theorem homogeneousComponents_sum_upto (p : MvPolynomial σ ℂ) (n : ℕ)
    (hp : p.totalDegree ≤ n) :
    (∑ a ∈ Finset.range (n + 1), homogeneousComponent a p) = p := by
  classical
  calc
    _ = ∑ a ∈ Finset.range (p.totalDegree + 1), homogeneousComponent a p := by
      symm
      apply Finset.sum_subset
      · exact Finset.range_mono (Nat.add_le_add_right hp 1)
      · intro a _ ha
        exact homogeneousComponent_eq_zero a p (by
          simp only [Finset.mem_range] at ha
          omega)
    _ = p := sum_homogeneousComponent p

/-- Removing the degree `n` part leaves a function of strictly lower degree. -/
theorem pointDegreeFiltration_lowerDifference (x : ι → σ → ℂ)
    (p : MvPolynomial σ ℂ) (n : ℕ) (hp : p.totalDegree ≤ n) :
    finitePointEvaluation x p - finitePointEvaluation x (homogeneousComponent n p) ∈
      pointDegreeFiltration x n := by
  have he := homogeneousComponents_sum_upto p n hp
  rw [Finset.sum_range_succ] at he
  have hf := congrArg (finitePointEvaluation x) he
  rw [map_add, map_sum] at hf
  rw [← hf, add_sub_cancel_right]
  apply Submodule.sum_mem
  intro a ha
  exact Submodule.subset_span ⟨homogeneousComponent a p,
    (homogeneousComponent_isHomogeneous a p).totalDegree_le.trans_lt
      (Finset.mem_range.mp ha), rfl⟩

/-- A homogeneous polynomial is a leading relation when its value has lower degree. -/
def pointInitialSubmodule (x : ι → σ → ℂ) : Submodule ℂ (MvPolynomial σ ℂ) where
  carrier := {p | ∀ n,
    finitePointEvaluation x (homogeneousComponent n p) ∈ pointDegreeFiltration x n}
  zero_mem' := by intro n; simp only [map_zero]; exact Submodule.zero_mem _
  add_mem' := by
    intro p q hp hq n
    simp only [map_add]
    exact Submodule.add_mem _ (hp n) (hq n)
  smul_mem' := by
    intro c p hp n
    simp only [map_smul]
    exact Submodule.smul_mem _ c (hp n)

/-- Membership of a homogeneous polynomial in the leading relation space is a single test. -/
theorem pointInitialSubmodule_homogeneous (x : ι → σ → ℂ)
    (p : MvPolynomial σ ℂ) (n : ℕ) (hp : p.IsHomogeneous n) :
    p ∈ pointInitialSubmodule x ↔ finitePointEvaluation x p ∈ pointDegreeFiltration x n := by
  classical
  constructor
  · intro h
    have hn := h n
    simpa only [homogeneousComponent_of_mem hp, if_pos rfl] using hn
  · intro h a
    rw [homogeneousComponent_of_mem hp]
    by_cases ha : a = n
    · subst a
      simpa only [if_pos rfl] using h
    · rw [if_neg ha, map_zero]
      exact Submodule.zero_mem _

/-- The leading relation space is closed under multiplication by arbitrary polynomials. -/
theorem pointInitialSubmodule_mul (x : ι → σ → ℂ) (p q : MvPolynomial σ ℂ)
    (hq : q ∈ pointInitialSubmodule x) : p * q ∈ pointInitialSubmodule x := by
  classical
  have hpiece (a b : ℕ) :
      homogeneousComponent a p * homogeneousComponent b q ∈ pointInitialSubmodule x := by
    apply (pointInitialSubmodule_homogeneous x _ (a + b)
      ((homogeneousComponent_isHomogeneous a p).mul
        (homogeneousComponent_isHomogeneous b q))).mpr
    rw [map_mul]
    exact pointDegreeFiltration_mul x b a (homogeneousComponent a p)
      (homogeneousComponent_isHomogeneous a p).totalDegree_le _ (hq b)
  have he : p * q =
      ∑ a ∈ Finset.range (p.totalDegree + 1),
        ∑ b ∈ Finset.range (q.totalDegree + 1),
          homogeneousComponent a p * homogeneousComponent b q := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul, sum_homogeneousComponent]
  rw [he]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => hpiece a b

/-- The ideal of top-degree relations of a point set, expressed degree by degree. -/
def pointInitialIdeal (x : ι → σ → ℂ) : Ideal (MvPolynomial σ ℂ) where
  __ := (pointInitialSubmodule x).toAddSubgroup
  smul_mem' := fun p q hq => pointInitialSubmodule_mul x p q hq

/-- Every homogeneous component of a leading relation is again a leading relation. -/
theorem pointInitialIdeal_component (x : ι → σ → ℂ) (p : MvPolynomial σ ℂ)
    (hp : p ∈ pointInitialIdeal x) (n : ℕ) :
    homogeneousComponent n p ∈ pointInitialIdeal x :=
  (pointInitialSubmodule_homogeneous x _ n
    (homogeneousComponent_isHomogeneous n p)).mpr (hp n)

/-- The top homogeneous part of a polynomial vanishing at every point is a leading relation. -/
theorem pointInitialIdeal_of_vanishing (x : ι → σ → ℂ) (p : MvPolynomial σ ℂ)
    (hp : finitePointEvaluation x p = 0) (n : ℕ) (hn : p.totalDegree ≤ n) :
    homogeneousComponent n p ∈ pointInitialIdeal x := by
  apply (pointInitialSubmodule_homogeneous x _ n
    (homogeneousComponent_isHomogeneous n p)).mpr
  have h := pointDegreeFiltration_lowerDifference x p n hn
  rw [hp, zero_sub] at h
  exact (Submodule.neg_mem_iff _).mp h

/-- Each positive filtration stage consists of evaluations with the stated degree bound. -/
theorem pointDegreeFiltration_succ_mem (x : ι → σ → ℂ) (n : ℕ) (f : ι → ℂ) :
    f ∈ pointDegreeFiltration x (n + 1) ↔
      ∃ p : MvPolynomial σ ℂ, p.totalDegree ≤ n ∧ finitePointEvaluation x p = f := by
  constructor
  · intro hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
        obtain ⟨p, hp, rfl⟩ := hf
        exact ⟨p, by omega, rfl⟩
    | zero => exact ⟨0, by simp, map_zero _⟩
    | add f g _ _ hf hg =>
        obtain ⟨p, hp, rfl⟩ := hf
        obtain ⟨q, hq, rfl⟩ := hg
        exact ⟨p + q, (totalDegree_add p q).trans (max_le hp hq), map_add _ _ _⟩
    | smul c f _ hf =>
        obtain ⟨p, hp, rfl⟩ := hf
        exact ⟨c • p, (totalDegree_smul_le c p).trans hp, map_smul _ _ _⟩
  · rintro ⟨p, hp, rfl⟩
    exact Submodule.subset_span ⟨p, by omega, rfl⟩

/-- Every homogeneous leading relation lifts to a vanishing polynomial of the same degree bound. -/
theorem pointInitialIdeal_homogeneous_lift (x : ι → σ → ℂ)
    (p : MvPolynomial σ ℂ) (n : ℕ) (hp : p.IsHomogeneous n)
    (hmem : p ∈ pointInitialIdeal x) :
    ∃ q : MvPolynomial σ ℂ, finitePointEvaluation x q = 0 ∧
      q.totalDegree ≤ n ∧ homogeneousComponent n q = p := by
  have hf := (pointInitialSubmodule_homogeneous x p n hp).mp hmem
  cases n with
  | zero =>
      rw [pointDegreeFiltration_zero, Submodule.mem_bot] at hf
      exact ⟨p, hf, hp.totalDegree_le, by
        rw [homogeneousComponent_of_mem hp, if_pos rfl]⟩
  | succ n =>
      obtain ⟨q, hq, he⟩ := (pointDegreeFiltration_succ_mem x n _).mp hf
      refine ⟨p - q, by rw [map_sub, he, sub_self],
        (totalDegree_sub p q).trans (max_le hp.totalDegree_le (by omega)), ?_⟩
      rw [map_sub, homogeneousComponent_of_mem hp, if_pos rfl,
        homogeneousComponent_eq_zero (n + 1) q (by omega), sub_zero]

/-- The degreewise relation ideal is exactly generated by top parts of vanishing polynomials. -/
theorem pointInitialIdeal_eq_span_vanishing (x : ι → σ → ℂ) :
    pointInitialIdeal x = Ideal.span {p | ∃ q : MvPolynomial σ ℂ, ∃ n : ℕ,
      finitePointEvaluation x q = 0 ∧ q.totalDegree ≤ n ∧ homogeneousComponent n q = p} := by
  apply le_antisymm
  · intro p hp
    have he := sum_homogeneousComponent p
    rw [← he]
    apply Ideal.sum_mem
    intro n _
    obtain ⟨q, hq, hd, hc⟩ := pointInitialIdeal_homogeneous_lift x
      (homogeneousComponent n p) n (homogeneousComponent_isHomogeneous n p)
      (pointInitialIdeal_component x p hp n)
    exact Ideal.subset_span ⟨q, n, hq, hd, hc⟩
  · apply Ideal.span_le.mpr
    rintro p ⟨q, n, hq, hd, rfl⟩
    exact pointInitialIdeal_of_vanishing x q hq n hd

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.pointDegreeFiltration_mul
#print axioms VOA.DeligneAudit.SL4T.homogeneousComponents_sum_upto
#print axioms VOA.DeligneAudit.SL4T.pointDegreeFiltration_lowerDifference
#print axioms VOA.DeligneAudit.SL4T.pointInitialSubmodule_homogeneous
#print axioms VOA.DeligneAudit.SL4T.pointInitialSubmodule_mul
#print axioms VOA.DeligneAudit.SL4T.pointInitialIdeal_component
#print axioms VOA.DeligneAudit.SL4T.pointInitialIdeal_of_vanishing
#print axioms VOA.DeligneAudit.SL4T.pointDegreeFiltration_succ_mem
#print axioms VOA.DeligneAudit.SL4T.pointInitialIdeal_homogeneous_lift
#print axioms VOA.DeligneAudit.SL4T.pointInitialIdeal_eq_span_vanishing
