/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroGramLeadingCoefficient
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Ordinary null relations force determinant factors

If r rows of a polynomial matrix vanish at c, its determinant contains
(X-c)^r. An invertible constant row change transports this conclusion to
independent ordinary null relations. This is a multiplicity lower-bound
mechanism for a future singular-vector argument. It does not construct the
minimal-model singular vectors or establish simple roots.
-/
namespace VOA.VirDeformModes.NormalOrdering
open Polynomial

/-- Each row vanishing at c contributes one factor X-c to the determinant.
The proof factors these rows entry by entry, retaining the quotient matrix. -/
theorem pow_X_sub_C_dvd_det_of_zero_rows {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Polynomial ℂ)) (c : ℂ) (s : Finset ι)
    (h : ∀ i ∈ s, ∀ j, (M i j).eval c = 0) :
    (X-Polynomial.C c)^s.card ∣ M.det := by
  classical
  let v : ι → Polynomial ℂ := fun i => if i ∈ s then X-Polynomial.C c else 1
  let Q : Matrix ι ι (Polynomial ℂ) := fun i j =>
    if i ∈ s then M i j /ₘ (X-Polynomial.C c) else M i j
  have he : M = Matrix.of (fun i j => v i * Q i j) := by
    apply Matrix.ext
    intro i j
    by_cases hi : i ∈ s
    · simpa [v, Q, hi] using
        (mul_divByMonic_eq_iff_isRoot.mpr (h i hi j)).symm
    · simp [v, Q, hi]
  have hv : (∏ i, v i) = (X-Polynomial.C c)^s.card := by
    simp [v, Finset.prod_ite_mem_eq, Finset.prod_const]
  refine ⟨Q.det, ?_⟩
  rw [he, Matrix.det_mul_column, hv]

/-- Invertible constant row changes preserve determinant divisibility.
Their determinant is a nonzero constant polynomial, hence a unit that cancels. -/
theorem pow_X_sub_C_dvd_det_of_null_rows {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Polynomial ℂ)) (c : ℂ) (s : Finset ι)
    (U : Matrix ι ι ℂ) (hU : U.det ≠ 0)
    (h : ∀ i ∈ s, ∀ j, ∑ k, U i k * (M k j).eval c = 0) :
    (X-Polynomial.C c)^s.card ∣ M.det := by
  let A : Matrix ι ι (Polynomial ℂ) := U.map Polynomial.C * M
  have ha : ∀ i ∈ s, ∀ j, (A i j).eval c = 0 := by
    intro i hi j
    simpa [A, Matrix.mul_apply, Polynomial.eval_finsetSum] using h i hi j
  have hd := pow_X_sub_C_dvd_det_of_zero_rows A c s ha
  have hu : IsUnit (Polynomial.C U.det : Polynomial ℂ) :=
    (isUnit_iff_ne_zero.mpr hU).map Polynomial.C
  change (X-Polynomial.C c)^s.card ∣ (U.map Polynomial.C * M).det at hd
  have hmap : (U.map Polynomial.C).det = Polynomial.C U.det :=
    (Polynomial.C.map_det U).symm
  rw [Matrix.det_mul, hmap] at hd
  exact hu.dvd_mul_left.mp hd

/-- A subset of the rows of a coefficient-space basis may be used as null
relations. Their cardinality gives a proved lower bound for the determinant's
vanishing order, with no deformation data involved. -/
theorem pow_X_sub_C_dvd_det_of_basis_null_rows {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Polynomial ℂ)) (c : ℂ) (s : Finset ι)
    (b : Module.Basis ι ℂ (ι → ℂ))
    (h : ∀ i ∈ s, ∀ j, ∑ k, b i k * (M k j).eval c = 0) :
    (X-Polynomial.C c)^s.card ∣ M.det := by
  have hu : IsUnit (Matrix.of (fun i j => b i j)) :=
    Matrix.linearIndependent_rows_iff_isUnit.mp b.linearIndependent
  have hd : (Matrix.of (fun i j => b i j)).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  exact pow_X_sub_C_dvd_det_of_null_rows M c s _ hd h

/-- Any finite linearly independent family of ordinary null rows supplies
its cardinality many determinant factors. The proof completes that family to
a basis; no basis-completion assumption is left to the caller. -/
theorem pow_X_sub_C_dvd_det_of_independent_null_rows
    {ι τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype τ]
    (M : Matrix ι ι (Polynomial ℂ)) (c : ℂ) (v : τ → ι → ℂ)
    (hv : LinearIndependent ℂ v)
    (h : ∀ i j, ∑ k, v i k * (M k j).eval c = 0) :
    (X-Polynomial.C c)^(Fintype.card τ) ∣ M.det := by
  classical
  let hs := hv.linearIndepOn_id
  let b₀ := Module.Basis.extend hs
  letI : Finite (hs.extend (Set.subset_univ (Set.range v))) :=
    Module.Finite.finite_basis b₀
  letI : Fintype (hs.extend (Set.subset_univ (Set.range v))) := Fintype.ofFinite _
  let e : hs.extend (Set.subset_univ (Set.range v)) ≃ ι :=
    Fintype.equivOfCardEq (by
      rw [← Module.finrank_eq_card_basis b₀, Module.finrank_fintype_fun_eq_card])
  let a : τ ↪ ι := {
    toFun := fun j => e ⟨v j, hs.subset_extend _ (Set.mem_range_self j)⟩
    inj' := by
      intro i j hij
      apply hv.injective
      exact congrArg Subtype.val (e.injective hij) }
  let b := b₀.reindex e
  have hb : ∀ j, b (a j) = v j := by
    intro j
    simp [b, a, Module.Basis.reindex_apply, b₀, Module.Basis.extend_apply_self]
  have hd := pow_X_sub_C_dvd_det_of_basis_null_rows M c (Finset.univ.map a) b (by
    intro i hi j
    obtain ⟨t,ht,rfl⟩ := Finset.mem_map.mp hi
    rw [hb]
    exact h t j)
  simpa using hd

/-- The full specialized left nullspace forces that many powers of X-c
in the determinant. A finite basis of the nullspace provides the independent
rows; its inclusion in coefficient space is injective. -/
theorem pow_X_sub_C_nullity_dvd_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Polynomial ℂ)) (c : ℂ) :
    (X-Polynomial.C c)^(Module.finrank ℂ
      (LinearMap.ker (M.map (Polynomial.eval c)).vecMulLinear)) ∣ M.det := by
  let K := LinearMap.ker (M.map (Polynomial.eval c)).vecMulLinear
  let b := Module.finBasis ℂ K
  have hv := b.linearIndependent.map' K.subtype K.ker_subtype
  have hh : ∀ i j, ∑ k, (K.subtype (b i)) k * (M k j).eval c = 0 := by
    intro i j
    have hb := (b i).property
    have he := LinearMap.mem_ker.mp hb
    exact congrFun he j
  have hd := pow_X_sub_C_dvd_det_of_independent_null_rows M c _ hv hh
  simpa using hd

/-- For a nonzero polynomial determinant, its root multiplicity is at least
the dimension of the specialized nullspace. This is only a lower bound;
it does not assert that the root is simple. -/
theorem nullity_le_det_rootMultiplicity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Polynomial ℂ)) (c : ℂ) (hM : M.det ≠ 0) :
    Module.finrank ℂ (LinearMap.ker (M.map (Polynomial.eval c)).vecMulLinear) ≤
      M.det.rootMultiplicity c := by
  exact (Polynomial.le_rootMultiplicity_iff hM).mpr (pow_X_sub_C_nullity_dvd_det M c)

/-- The actual vacuum partition determinant inherits the nullity bound.
Its required nonvanishing is already proved by the sharp-degree calculation. -/
theorem partitionNullity_le_rootMultiplicity (n : ℕ) (c : ℂ) :
    Module.finrank ℂ (LinearMap.ker
      ((partitionGramPolynomial n).map (Polynomial.eval c)).vecMulLinear) ≤
      (partitionGramPolynomial n).det.rootMultiplicity c :=
  nullity_le_det_rootMultiplicity _ c (partitionDeterminant_ne_zero n)

/-- Nullspaces at distinct charges contribute simultaneously: their linear
factors are coprime, so the product of all nullity powers divides the determinant. -/
theorem prod_nullity_factors_dvd_det {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype τ] (M : Matrix ι ι (Polynomial ℂ)) (c : τ → ℂ)
    (hc : Function.Injective c) :
    (∏ t, (X-Polynomial.C (c t))^(Module.finrank ℂ
      (LinearMap.ker (M.map (Polynomial.eval (c t))).vecMulLinear))) ∣ M.det := by
  apply Fintype.prod_dvd_of_coprime
  · intro i j hij
    exact (Polynomial.pairwise_coprime_X_sub_C hc hij).pow
  · intro t
    exact pow_X_sub_C_nullity_dvd_det M (c t)

/-- The sum of specialized nullspace dimensions over any finite set of
distinct charges cannot exceed the polynomial determinant's degree. -/
theorem sum_nullities_le_det_degree {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype τ] (M : Matrix ι ι (Polynomial ℂ)) (hM : M.det ≠ 0)
    (c : τ → ℂ) (hc : Function.Injective c) :
    (∑ t, Module.finrank ℂ
      (LinearMap.ker (M.map (Polynomial.eval (c t))).vecMulLinear)) ≤ M.det.natDegree := by
  have hd := Polynomial.natDegree_le_of_dvd (prod_nullity_factors_dvd_det M c hc) hM
  rw [Polynomial.natDegree_prod_of_monic _ _
    (fun t _ => (Polynomial.monic_X_sub_C (c t)).pow _)] at hd
  simpa only [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one] using hd

/-- For vacuum partition Gram matrices the nullity budget is the exact sum
of partition lengths. This links ordinary singular-space dimensions to the
completed sharp-degree calculation, without assuming which charges are singular. -/
theorem sum_partitionNullities_le_lengths {τ : Type*} [Fintype τ]
    (n : ℕ) (c : τ → ℂ) (hc : Function.Injective c) :
    (∑ t, Module.finrank ℂ (LinearMap.ker
      ((partitionGramPolynomial n).map (Polynomial.eval (c t))).vecMulLinear)) ≤
      ∑ j : VirModule.SortedOfEnergy n, j.val.length := by
  simpa only [partitionDeterminant_natDegree] using
    sum_nullities_le_det_degree (partitionGramPolynomial n) (partitionDeterminant_ne_zero n) c hc

/-- Ordinary independent partition relations, supplied inside a coefficient
basis, force a power of the corresponding charge factor in the actual vacuum
Gram determinant. Constructing such relations uniformly remains separate. -/
theorem partitionDeterminant_dvd_of_basis_null_rows (n : ℕ) (c : ℂ)
    (s : Finset (VirModule.SortedOfEnergy n))
    (b : Module.Basis (VirModule.SortedOfEnergy n) ℂ (VirModule.SortedOfEnergy n → ℂ))
    (h : ∀ i ∈ s, ∀ j, ∑ k, b i k * (partitionGramPolynomial n k j).eval c = 0) :
    (X-Polynomial.C c)^s.card ∣ (partitionGramPolynomial n).det :=
  pow_X_sub_C_dvd_det_of_basis_null_rows _ c s b h

end VOA.VirDeformModes.NormalOrdering
