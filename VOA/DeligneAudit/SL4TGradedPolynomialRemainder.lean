import VOA.DeligneAudit.SL4TStableSubmoduleMinors
import VOA.DeligneAudit.SL4TCore
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Homogeneous polynomials over a graded coefficient algebra

Let `A` be a `ℤ`-graded commutative `ℂ`-algebra and give the polynomial variable degree one. A
polynomial is homogeneous of degree `δ` when its coefficient of `t^l` lies in degree `δ - l`.
This file proves that homogeneous polynomials are closed under sums and products, that
reduction modulo a homogeneous monic polynomial preserves homogeneity, that a matrix whose
entries have degrees `col b - row a` has a homogeneous determinant, that power sums obtained
from a graded elementary sequence are graded, that the degree components of a product are the
expected convolution, and that a finite-dimensional graded algebra vanishes in all large
degrees.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

section GradedMonoid

variable {R : Type*} [CommRing R] [Algebra ℂ R] (ℬ : ℤ → Submodule ℂ R)
variable [SetLike.GradedMonoid ℬ]

/-- Power sums of a graded signed elementary sequence are graded: `p_s` has degree `s`. -/
theorem powerSumOfCoeff_mem_graded (d : ℕ) (e : ℕ → R) (he : ∀ n : ℕ, e n ∈ ℬ n) (s : ℕ) :
    powerSumOfCoeff d e s ∈ ℬ s := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
      cases s with
      | zero =>
          rw [powerSumOfCoeff]
          exact SetLike.natCast_mem_graded ℬ d
      | succ n =>
          rw [powerSumOfCoeff]
          apply Submodule.sub_mem
          · exact Submodule.smul_mem _ _ (he (n + 1))
          · apply Submodule.sum_mem
            intro i _
            have h := SetLike.mul_mem_graded (ih (n - i.val) (by omega)) (he (i.val + 1))
            have hi := i.isLt
            have hdeg : (((n - i.val : ℕ) : ℤ) + ((i.val + 1 : ℕ) : ℤ)) = ((n + 1 : ℕ) : ℤ) := by
              push_cast
              omega
            rw [hdeg] at h
            exact h

end GradedMonoid

variable {A : Type*} [CommRing A] [Algebra ℂ A] (𝒜 : ℤ → Submodule ℂ A) [GradedAlgebra 𝒜]

/-- A polynomial over a graded algebra is homogeneous of degree `δ`, with the variable in degree
one, when its coefficient of `t^l` lies in degree `δ - l`. -/
def PolynomialHomogeneous (δ : ℤ) (f : A[X]) : Prop :=
  ∀ l : ℕ, f.coeff l ∈ 𝒜 (δ - l)

variable {𝒜}

omit [GradedAlgebra 𝒜] in
theorem polynomialHomogeneous_zero (δ : ℤ) : PolynomialHomogeneous 𝒜 δ (0 : A[X]) := by
  intro l
  rw [coeff_zero]
  exact Submodule.zero_mem _

omit [GradedAlgebra 𝒜] in
theorem PolynomialHomogeneous.add {δ : ℤ} {f g : A[X]} (hf : PolynomialHomogeneous 𝒜 δ f)
    (hg : PolynomialHomogeneous 𝒜 δ g) : PolynomialHomogeneous 𝒜 δ (f + g) := by
  intro l
  rw [coeff_add]
  exact Submodule.add_mem _ (hf l) (hg l)

omit [GradedAlgebra 𝒜] in
theorem PolynomialHomogeneous.sub {δ : ℤ} {f g : A[X]} (hf : PolynomialHomogeneous 𝒜 δ f)
    (hg : PolynomialHomogeneous 𝒜 δ g) : PolynomialHomogeneous 𝒜 δ (f - g) := by
  intro l
  rw [coeff_sub]
  exact Submodule.sub_mem _ (hf l) (hg l)

omit [GradedAlgebra 𝒜] in
theorem polynomialHomogeneous_sum {ι : Type*} (s : Finset ι) (f : ι → A[X]) (δ : ℤ)
    (hf : ∀ i ∈ s, PolynomialHomogeneous 𝒜 δ (f i)) :
    PolynomialHomogeneous 𝒜 δ (∑ i ∈ s, f i) := by
  intro l
  rw [finsetSum_coeff]
  exact Submodule.sum_mem _ fun i hi => hf i hi l

omit [GradedAlgebra 𝒜] in
theorem polynomialHomogeneous_C {a : A} {e : ℤ} (ha : a ∈ 𝒜 e) :
    PolynomialHomogeneous 𝒜 e (Polynomial.C a) := by
  intro l
  rw [coeff_C]
  split_ifs with hl
  · subst hl
    simpa using ha
  · exact Submodule.zero_mem _

theorem polynomialHomogeneous_X_pow (n : ℕ) :
    PolynomialHomogeneous 𝒜 n ((X : A[X]) ^ n) := by
  intro l
  rw [coeff_X_pow]
  split_ifs with hl
  · subst hl
    rw [sub_self]
    exact SetLike.one_mem_graded 𝒜
  · exact Submodule.zero_mem _

theorem PolynomialHomogeneous.mul {δ ε : ℤ} {f g : A[X]} (hf : PolynomialHomogeneous 𝒜 δ f)
    (hg : PolynomialHomogeneous 𝒜 ε g) : PolynomialHomogeneous 𝒜 (δ + ε) (f * g) := by
  intro n
  rw [coeff_mul]
  apply Submodule.sum_mem
  intro x hx
  have hn := Finset.mem_antidiagonal.mp hx
  have h := SetLike.mul_mem_graded (hf x.1) (hg x.2)
  have hdeg : δ - (x.1 : ℤ) + (ε - (x.2 : ℤ)) = δ + ε - (n : ℤ) := by
    rw [← hn]
    push_cast
    ring
  rw [hdeg] at h
  exact h

omit [GradedAlgebra 𝒜] in
theorem PolynomialHomogeneous.of_eq {δ ε : ℤ} {f : A[X]} (hf : PolynomialHomogeneous 𝒜 δ f)
    (h : δ = ε) : PolynomialHomogeneous 𝒜 ε f := h ▸ hf

/-- Reduction of a power of the variable modulo a homogeneous monic polynomial is
homogeneous. -/
theorem polynomialHomogeneous_X_pow_modByMonic (P : A[X]) (r : ℕ) (hP : P.Monic)
    (hr : P.natDegree = r) (hPh : PolynomialHomogeneous 𝒜 r P) (n : ℕ) :
    PolynomialHomogeneous 𝒜 n ((X : A[X]) ^ n %ₘ P) := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · intro l
    rw [Subsingleton.elim ((X ^ n %ₘ P).coeff l) 0]
    exact Submodule.zero_mem _
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · have hP1 : P = 1 := Polynomial.eq_one_of_monic_natDegree_zero hP (hr.trans hr0)
    subst hP1
    rw [modByMonic_one]
    exact polynomialHomogeneous_zero _
  have hdeg : P.degree = (r : WithBot ℕ) := by rw [degree_eq_natDegree hP.ne_zero, hr]
  induction n with
  | zero =>
      rw [pow_zero, (modByMonic_eq_self_iff hP).mpr]
      · simpa using polynomialHomogeneous_X_pow (𝒜 := 𝒜) 0
      · rw [degree_one, hdeg]
        exact_mod_cast hrpos
  | succ n ih =>
      have hm : (X : A[X]) ^ (n + 1) %ₘ P = X * (X ^ n %ₘ P) %ₘ P := by
        apply modByMonic_eq_of_dvd_sub hP
        rw [pow_succ', ← mul_sub, modByMonic_eq_sub_mul_div, sub_sub_cancel]
        exact dvd_mul_of_dvd_right (dvd_mul_right P _) X
      have hlt : (X ^ n %ₘ P).degree < (r : WithBot ℕ) := by
        rw [← hdeg]
        exact degree_modByMonic_lt _ hP
      rw [hm, monic_remainder_variable_mul P _ r hP hr hrpos hlt]
      apply PolynomialHomogeneous.sub
      · have h := (polynomialHomogeneous_X_pow (𝒜 := 𝒜) 1).mul ih
        rw [pow_one] at h
        exact h.of_eq (by push_cast; ring)
      · have h := (polynomialHomogeneous_C (ih (r - 1))).mul hPh
        exact h.of_eq (by push_cast [Nat.cast_sub (show 1 ≤ r by omega)]; ring)

/-- Reduction modulo a homogeneous monic polynomial preserves homogeneity. -/
theorem PolynomialHomogeneous.modByMonic {δ : ℤ} {f : A[X]}
    (hf : PolynomialHomogeneous 𝒜 δ f) (P : A[X]) (r : ℕ) (hP : P.Monic)
    (hr : P.natDegree = r) (hPh : PolynomialHomogeneous 𝒜 r P) :
    PolynomialHomogeneous 𝒜 δ (f %ₘ P) := by
  have hsum : f %ₘ P = ∑ i ∈ Finset.range (f.natDegree + 1),
      Polynomial.C (f.coeff i) * (X ^ i %ₘ P) := by
    conv_lhs => rw [f.as_sum_range_C_mul_X_pow]
    rw [← modByMonicHom_apply, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [modByMonicHom_apply, ← smul_eq_C_mul, ← smul_eq_C_mul, smul_modByMonic]
  rw [hsum]
  apply polynomialHomogeneous_sum
  intro i _
  have h := (polynomialHomogeneous_C (hf i)).mul
    (polynomialHomogeneous_X_pow_modByMonic P r hP hr hPh i)
  exact h.of_eq (by ring)

/-- A matrix whose entries have degrees `col b - row a` has determinant of degree
`Σ col - Σ row`. -/
theorem det_mem_graded {j : ℕ} (M : Matrix (Fin j) (Fin j) A) (row col : Fin j → ℤ)
    (hM : ∀ a b, M a b ∈ 𝒜 (col b - row a)) :
    M.det ∈ 𝒜 ((∑ b, col b) - ∑ a, row a) := by
  rw [Matrix.det_apply]
  apply Submodule.sum_mem
  intro σ _
  have hp : ∏ i, M (σ i) i ∈ 𝒜 (∑ i, (col i - row (σ i))) :=
    SetLike.prod_mem_graded 𝒜 (fun i => col i - row (σ i)) (fun i => M (σ i) i)
      (fun i _ => hM (σ i) i)
  rw [Finset.sum_sub_distrib, Equiv.sum_comp σ row] at hp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]
    exact hp
  · rw [h, Units.neg_smul, one_smul]
    exact Submodule.neg_mem _ hp

/-- The degree components of a product are the convolution of the components of one factor
with the components of the other. -/
theorem decompose_mul_eq_sum (a x : A) (d : ℤ) [∀ (i : ℤ) (y : 𝒜 i), Decidable (y ≠ 0)] :
    (DirectSum.decompose 𝒜 (a * x) d : A) =
      ∑ e ∈ (DirectSum.decompose 𝒜 a).support,
        (DirectSum.decompose 𝒜 a e : A) * DirectSum.decompose 𝒜 x (d - e) := by
  rw [← GradedRing.proj_apply]
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 a]
  rw [Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [GradedRing.proj_apply]
  have h := DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 (b := x)
    (DirectSum.decompose 𝒜 a e).2 (j := d - e)
  rwa [add_sub_cancel] at h

/-- A finite-dimensional graded algebra vanishes in all large degrees. -/
theorem graded_eventually_bot [FiniteDimensional ℂ A] :
    ∃ D : ℕ, ∀ d : ℤ, (D : ℤ) < d → 𝒜 d = ⊥ := by
  classical
  have hind : iSupIndep 𝒜 := (DirectSum.Decomposition.isInternal 𝒜).submodule_iSupIndep
  letI := hind.fintypeNeBotOfFiniteDimensional
  let s : Finset ℤ := Finset.univ.image (fun i : {i // 𝒜 i ≠ ⊥} => i.val)
  obtain ⟨M, hM⟩ := s.bddAbove
  refine ⟨M.toNat, fun d hd => ?_⟩
  by_contra hne
  have hmem : d ∈ s := Finset.mem_image.mpr ⟨⟨d, hne⟩, Finset.mem_univ _, rfl⟩
  have := hM hmem
  omega

end

end VOA.DeligneAudit.SL4T
