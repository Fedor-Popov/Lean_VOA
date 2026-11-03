/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.Roots

/-!
# Symmetric occupancy specialization

This proves the occupancy-polynomial assertion of Lemma 4.2 of arXiv:2609.33348
for symmetric polynomials over any commutative ℚ-algebra, including polynomial
coefficient rings. A finite subset selects the variables set to `z + δ`, with
all other variables set to `z`. The coefficient of `δ^d` is a polynomial in the
subset cardinality of degree at most `d`.

The proof first counts the specialization of elementary symmetric generators,
then uses the fundamental theorem of symmetric polynomials. Their bivariate
lifts have occupancy degree bounded by displacement degree, a property closed
under addition and multiplication. Simultaneous translation supplies the common
center, and the formal-center corollary retains its polynomial dependence.

The final two theorems supply the root-count consequence: enough distinct
vanishing occupancy cardinalities force coefficientwise vanishing, and hence
vanishing to the prescribed displacement order, at every occupancy cardinality.
-/

namespace VOA.SymmetricOccupancy

open scoped BigOperators
open Finset Polynomial

noncomputable section

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [CommRing K]

/-- Set the variables indexed by `S` to the common displacement and all others to zero. -/
def specialize (S : Finset σ) : MvPolynomial σ K →+* K[X] :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i ↦ if i ∈ S then Polynomial.X else 0)

omit [Fintype σ] in
/-- A squarefree monomial survives precisely when its support is occupied. -/
theorem specialize_squarefree (S T : Finset σ) :
    specialize (K := K) S (∏ i ∈ T, MvPolynomial.X i) =
      if T ⊆ S then Polynomial.X ^ T.card else 0 := by
  classical
  simp only [specialize, map_prod, MvPolynomial.eval₂Hom_X']
  split_ifs with h
  · simp only [Finset.prod_congr rfl (fun i hi ↦ if_pos (h hi)), Finset.prod_const]
  · obtain ⟨i, hi, his⟩ := Finset.not_subset.mp h
    exact Finset.prod_eq_zero hi (if_neg his)

/-- The elementary symmetric generator specializes to the corresponding binomial count. -/
theorem specialize_esymm (S : Finset σ) (r : ℕ) :
    specialize (K := K) S (MvPolynomial.esymm σ K r) =
      Polynomial.C (S.card.choose r : K) * Polynomial.X ^ r := by
  classical
  rw [MvPolynomial.esymm, map_sum]
  simp_rw [specialize_squarefree]
  calc
    (∑ T ∈ powersetCard r univ, if T ⊆ S then (Polynomial.X : K[X]) ^ T.card else 0) =
        ∑ T ∈ powersetCard r S, (Polynomial.X : K[X]) ^ r := by
      rw [← Finset.sum_filter]
      have he : (powersetCard r univ).filter (fun T ↦ T ⊆ S) = powersetCard r S := by
        ext T
        simp [Finset.mem_powersetCard, and_comm]
      rw [he]
      exact Finset.sum_congr rfl (fun T hT ↦ congrArg _ (mem_powersetCard.mp hT).2)
    _ = _ := by simp [nsmul_eq_mul]

/-- Simultaneously translate all variables by the common center. -/
def translate (z : K) : MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  MvPolynomial.aeval (fun i ↦ MvPolynomial.C z + MvPolynomial.X i)

omit [Fintype σ] [DecidableEq σ] in
theorem rename_translate (z : K) (F : MvPolynomial σ K) (e : Equiv.Perm σ) :
    MvPolynomial.rename e (translate z F) = translate z (MvPolynomial.rename e F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [translate]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    congr 1
    simp [translate]

omit [Fintype σ] [DecidableEq σ] in
theorem isSymmetric_translate (z : K) (F : MvPolynomial σ K) (hF : F.IsSymmetric) :
    (translate z F).IsSymmetric := by
  intro e
  rw [rename_translate, hF e]

/-- Set occupied variables to `z + δ` and unoccupied variables to `z`. -/
def shiftedSpecialize (z : K) (S : Finset σ) : MvPolynomial σ K →+* K[X] :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i ↦ Polynomial.C z + if i ∈ S then Polynomial.X else 0)

omit [Fintype σ] in
theorem specialize_translate (z : K) (S : Finset σ) (F : MvPolynomial σ K) :
    specialize S (translate z F) = shiftedSpecialize z S F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [translate, specialize, shiftedSpecialize]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    congr 1
    simp [translate, specialize, shiftedSpecialize]

end

noncomputable section RationalAlgebra
variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [CommRing K] [Algebra ℚ K]

/-- The Newton basis polynomial representing the binomial coefficient. -/
def binomial (r : ℕ) : K[X] :=
  Polynomial.map (algebraMap ℚ K) ((r.factorial : ℚ)⁻¹ • descPochhammer ℚ r)

theorem eval_binomial (r v : ℕ) :
    (binomial (K := K) r).eval (v : K) = (v.choose r : K) := by
  have hrat : (((r.factorial : ℚ)⁻¹ • descPochhammer ℚ r) : ℚ[X]).eval (v : ℚ) =
      (v.choose r : ℚ) := by
    rw [Polynomial.eval_smul]
    simp only [smul_eq_mul]
    rw [Nat.cast_choose_eq_descPochhammer_div]
    simp only [div_eq_mul_inv]
    exact mul_comm _ _
  have hv : (v : K) = algebraMap ℚ K (v : ℚ) := by simp
  rw [binomial, hv, Polynomial.eval_map, Polynomial.eval₂_at_apply, hrat]
  simp

theorem natDegree_binomial_le (r : ℕ) :
    (binomial (K := K) r).natDegree ≤ r := by
  exact Polynomial.natDegree_map_le.trans <|
    (Polynomial.natDegree_smul_le _ _).trans (by simp)

/-- In a bivariate polynomial, occupancy degree is bounded by displacement degree. -/
def DiagonalBound (p : Polynomial K[X]) : Prop :=
  ∀ d, (p.coeff d).natDegree ≤ d

omit [Algebra ℚ K] in
theorem diagonalBound_constant (a : K) :
    DiagonalBound (Polynomial.C (Polynomial.C a)) := by
  intro d
  by_cases h : d = 0
  · subst d; simp
  · simp [Polynomial.coeff_C, h]

omit [Algebra ℚ K] in
theorem DiagonalBound.add {p q : Polynomial K[X]}
    (hp : DiagonalBound p) (hq : DiagonalBound q) : DiagonalBound (p + q) := by
  intro d
  rw [Polynomial.coeff_add]
  exact Polynomial.natDegree_add_le_of_degree_le (hp d) (hq d)

omit [Algebra ℚ K] in
theorem DiagonalBound.mul {p q : Polynomial K[X]}
    (hp : DiagonalBound p) (hq : DiagonalBound q) : DiagonalBound (p * q) := by
  intro d
  rw [Polynomial.coeff_mul]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro ij hij
  exact Polynomial.natDegree_mul_le.trans <|
    (Nat.add_le_add (hp ij.1) (hq ij.2)).trans (Finset.mem_antidiagonal.mp hij).le

/-- The occupancy lift of an elementary symmetric generator. -/
def generator (r : ℕ) : Polynomial K[X] := Polynomial.monomial r (binomial r)

theorem diagonalBound_generator (r : ℕ) : DiagonalBound (generator (K := K) r) := by
  intro d
  by_cases h : r = d
  · subst d
    simpa [generator] using natDegree_binomial_le (K := K) r
  · simp [generator, Polynomial.coeff_monomial, h]

/-- Replace elementary generators by their bivariate occupancy lifts. -/
def liftGenerators (n : ℕ) : MvPolynomial (Fin n) K →+* Polynomial K[X] :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C) (fun i ↦ generator (i.val + 1))

theorem diagonalBound_liftGenerators {n : ℕ} (p : MvPolynomial (Fin n) K) :
    DiagonalBound (liftGenerators n p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa [liftGenerators] using diagonalBound_constant a
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp =>
    rw [map_mul]
    exact hp.mul (by simpa [liftGenerators] using diagonalBound_generator (K := K) (i.val + 1))

/-- Evaluation of occupancy at a subset cardinality recovers literal specialization. -/
theorem map_liftGenerators {n : ℕ} (p : MvPolynomial (Fin n) K)
    (S : Finset σ) :
    Polynomial.map (Polynomial.evalRingHom (S.card : K)) (liftGenerators n p) =
      specialize S (MvPolynomial.aeval (fun i : Fin n ↦ MvPolynomial.esymm σ K (i.val + 1)) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [liftGenerators, specialize]
  | add p q hp hq => simp only [map_add, Polynomial.map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.map_mul, hp, MvPolynomial.aeval_X]
    congr 1
    simp [liftGenerators, generator, eval_binomial, specialize_esymm,
      ← Polynomial.C_mul_X_pow_eq_monomial]

/-- Every symmetric polynomial admits a bivariate occupancy lift whose displacement-`d`
coefficient has occupancy degree at most `d`. -/
theorem exists_lift (F : MvPolynomial σ K) (hF : F.IsSymmetric) :
    ∃ P : Polynomial K[X], DiagonalBound P ∧ ∀ S : Finset σ,
      Polynomial.map (Polynomial.evalRingHom (S.card : K)) P = specialize S F := by
  obtain ⟨p, hp⟩ := MvPolynomial.esymmAlgHom_surjective K
    (σ := σ) (n := Fintype.card σ) le_rfl ⟨F, hF⟩
  refine ⟨liftGenerators _ p, diagonalBound_liftGenerators p, ?_⟩
  intro S
  rw [map_liftGenerators]
  have he := congrArg Subtype.val hp
  rw [MvPolynomial.esymmAlgHom_apply] at he
  rw [he]

/-- The coefficient of displacement degree `d` is polynomial in the number of occupied
variables, of degree at most `d`. This is the centered form of the occupancy lemma. -/
theorem exists_coefficient_polynomial (F : MvPolynomial σ K)
    (hF : F.IsSymmetric) (d : ℕ) :
    ∃ q : K[X], q.natDegree ≤ d ∧ ∀ S : Finset σ,
      q.eval (S.card : K) = (specialize S F).coeff d := by
  obtain ⟨P, hP, he⟩ := exists_lift F hF
  refine ⟨P.coeff d, hP d, fun S ↦ ?_⟩
  have hc := congrArg (fun p : K[X] ↦ p.coeff d) (he S)
  simpa using hc

/-- The shifted occupancy lemma: the coefficient of `δ^d` after substituting `z+δ`
in any `v` positions and `z` elsewhere is a polynomial in `v` of degree at most `d`. -/
theorem exists_shifted_coefficient_polynomial (F : MvPolynomial σ K)
    (hF : F.IsSymmetric) (z : K) (d : ℕ) :
    ∃ q : K[X], q.natDegree ≤ d ∧ ∀ S : Finset σ,
      q.eval (S.card : K) = (shiftedSpecialize z S F).coeff d := by
  obtain ⟨q, hq, he⟩ := exists_coefficient_polynomial (translate z F)
    (isSymmetric_translate z F hF) d
  exact ⟨q, hq, fun S ↦ by simpa only [specialize_translate] using he S⟩

/-- The common center can itself be a formal variable; all coefficients remain polynomial. -/
theorem exists_formal_center_coefficient_polynomial (F : MvPolynomial σ K)
    (hF : F.IsSymmetric) (d : ℕ) :
    ∃ q : Polynomial K[X], q.natDegree ≤ d ∧ ∀ S : Finset σ,
      q.eval (S.card : K[X]) =
        (shiftedSpecialize Polynomial.X S (MvPolynomial.map Polynomial.C F)).coeff d := by
  exact exists_shifted_coefficient_polynomial (MvPolynomial.map Polynomial.C F)
    (hF.map Polynomial.C) Polynomial.X d

/-- More than `d` distinct vanishing occupancy cardinalities force the degree-`d`
displacement coefficient to vanish at every occupancy cardinality. -/
theorem shifted_coeff_eq_zero_of_cardinal_roots [IsDomain K] [CharZero K]
    {ι : Type*} [Fintype ι] (F : MvPolynomial σ K) (hF : F.IsSymmetric)
    (z : K) (d : ℕ) (S : ι → Finset σ)
    (hinj : Function.Injective (fun i ↦ (S i).card))
    (hzero : ∀ i, (shiftedSpecialize z (S i) F).coeff d = 0)
    (hcard : d < Fintype.card ι) (T : Finset σ) :
    (shiftedSpecialize z T F).coeff d = 0 := by
  obtain ⟨q, hq, he⟩ := exists_shifted_coefficient_polynomial F hF z d
  have hz : q = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero q
    (Nat.cast_injective.comp hinj) (fun i ↦ (he (S i)).trans (hzero i))
    (hq.trans_lt hcard)
  rw [← he T, hz, Polynomial.eval_zero]

/-- Vanishing to order `m` at `m` distinct occupancy cardinalities propagates to every
occupancy cardinality. This packages the occupancy root-count step used for clusters. -/
theorem X_pow_dvd_shifted_of_cardinal_roots [IsDomain K] [CharZero K]
    {ι : Type*} [Fintype ι] (F : MvPolynomial σ K) (hF : F.IsSymmetric)
    (z : K) (m : ℕ) (S : ι → Finset σ)
    (hinj : Function.Injective (fun i ↦ (S i).card))
    (hzero : ∀ i, Polynomial.X ^ m ∣ shiftedSpecialize z (S i) F)
    (hcard : m ≤ Fintype.card ι) (T : Finset σ) :
    Polynomial.X ^ m ∣ shiftedSpecialize z T F := by
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  exact shifted_coeff_eq_zero_of_cardinal_roots F hF z d S hinj
    (fun i ↦ Polynomial.X_pow_dvd_iff.mp (hzero i) d hd) (hd.trans_le hcard) T

end RationalAlgebra
end VOA.SymmetricOccupancy
