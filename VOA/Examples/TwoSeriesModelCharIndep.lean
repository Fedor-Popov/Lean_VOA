/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.JetProductRank

/-!
# Independence of mixed elementary-symmetric monomials

Split `m + s` variables into the first `m` (`B`) and the last `s` (`A`).  The products

  `e_1(t)^{γ_1} ⋯ e_m(t)^{γ_m} · e_1(t_A)^{β_1} ⋯ e_s(t_A)^{β_s}`

of elementary symmetric polynomials of **all** variables (only the first `m` of them) and of the
`A`-variables are linearly independent (`linearIndependent_mixed`).  They form a basis of the
polynomials symmetric in `A` and in `B` separately, with generating function
`1/((q)_m (q)_s)`.

* `linearIndependent_rename_mul` — products of independent families in disjoint variables are
  independent;
* the proof of the main statement scales the `B`-variables by `z`: `e_k(t) ↦ z^k e_k(t_B) + O(z^{k-1})`
  (`hz_esymm`), and the top `z`-coefficient reduces it to the disjoint-variable case.

Everything is proved outright.
-/

namespace VOA.TwoSeries.ModelChar

open MvPolynomial VOA.JetProduct
open scoped BigOperators

noncomputable section

variable {m s : ℕ}

/-! ### Disjoint variables -/

/-- The splitting `ℂ[t_{m+s}] ≅ ℂ[t_B][t_A]`... as `ℂ[t_B]`-coefficients over `t_A`. -/
def splitE (m s : ℕ) : MvPolynomial (Fin (m + s)) ℂ →ₐ[ℂ]
    MvPolynomial (Fin s) (MvPolynomial (Fin m) ℂ) :=
  ((sumAlgEquiv ℂ (Fin s) (Fin m)).toAlgHom).comp
    (rename (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin m) (Fin s))))

theorem splitE_injective : Function.Injective (splitE m s) := by
  rw [splitE, AlgHom.coe_comp]
  exact (sumAlgEquiv ℂ (Fin s) (Fin m)).injective.comp
    (rename_injective _ (Equiv.injective _))

theorem splitE_natAdd (f : MvPolynomial (Fin s) ℂ) :
    splitE m s (rename (Fin.natAdd m) f) = map (MvPolynomial.C) f := by
  have : (splitE m s).comp (rename (Fin.natAdd m)) =
      (mapAlgHom (Algebra.ofId ℂ (MvPolynomial (Fin m) ℂ))) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [splitE, sumAlgEquiv, sumRingEquiv, sumToIter_Xl]
  have h := AlgHom.congr_fun this f
  simpa [mapAlgHom, Algebra.ofId] using h

theorem splitE_castAdd (g : MvPolynomial (Fin m) ℂ) :
    splitE m s (rename (Fin.castAdd s) g) = MvPolynomial.C g := by
  have : (splitE m s).comp (rename (Fin.castAdd s)) =
      (IsScalarTower.toAlgHom ℂ (MvPolynomial (Fin m) ℂ)
        (MvPolynomial (Fin s) (MvPolynomial (Fin m) ℂ))) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [splitE, sumAlgEquiv, sumRingEquiv, sumToIter_Xr]
  have h := AlgHom.congr_fun this g
  simpa using h

theorem coeff_splitE_mul (f : MvPolynomial (Fin s) ℂ) (g : MvPolynomial (Fin m) ℂ)
    (μ : Fin s →₀ ℕ) :
    coeff μ (splitE m s (rename (Fin.castAdd s) g * rename (Fin.natAdd m) f)) =
      coeff μ f • g := by
  rw [map_mul, splitE_natAdd, splitE_castAdd, coeff_C_mul, coeff_map, smul_eq_C_mul,
    mul_comm]

/-- Products of independent families in disjoint variables are independent. -/
theorem linearIndependent_rename_mul {ι κ : Type*} {g : ι → MvPolynomial (Fin m) ℂ}
    {f : κ → MvPolynomial (Fin s) ℂ} (hg : LinearIndependent ℂ g)
    (hf : LinearIndependent ℂ f) :
    LinearIndependent ℂ (fun p : ι × κ =>
      rename (Fin.castAdd s) (g p.1) * rename (Fin.natAdd m) (f p.2)) := by
  classical
  rw [linearIndependent_iff']
  intro S c hS p0 hp0
  -- coefficientwise in `t_A`
  have hμ : ∀ μ : Fin s →₀ ℕ, ∑ p ∈ S, (c p * coeff μ (f p.2)) • g p.1 = 0 := by
    intro μ
    have h := congrArg (fun P => coeff μ (splitE m s P)) hS
    simp only [map_sum, map_smul, coeff_sum, coeff_smul, coeff_splitE_mul, map_zero,
      coeff_zero] at h
    rw [← h]
    exact Finset.sum_congr rfl fun p _ => by rw [smul_smul]
  -- group by the `B`-index
  have hgrp : ∀ μ : Fin s →₀ ℕ, ∀ i ∈ S.image Prod.fst,
      ∑ p ∈ S.filter (fun p => p.1 = i), c p * coeff μ (f p.2) = 0 := by
    intro μ
    have h := hμ μ
    rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (t := S.image Prod.fst)
      (fun p hp => Finset.mem_image_of_mem _ hp)] at h
    have h2 : ∑ i ∈ S.image Prod.fst,
        (∑ p ∈ S.filter (fun p => p.1 = i), c p * coeff μ (f p.2)) • g i = 0 := by
      rw [← h]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
    exact (linearIndependent_iff'.mp hg) _ _ h2
  have hi0 : p0.1 ∈ S.image Prod.fst := Finset.mem_image_of_mem _ hp0
  -- the fibre over `p0.1` gives a relation among the `f`
  have hrel : ∑ p ∈ S.filter (fun p => p.1 = p0.1), c p • f p.2 = 0 := by
    ext μ
    rw [coeff_sum, coeff_zero]
    simp only [coeff_smul, smul_eq_mul]
    exact hgrp μ p0.1 hi0
  have hinj : Set.InjOn Prod.snd (S.filter (fun p => p.1 = p0.1) : Set (ι × κ)) := by
    intro p hp q hq hpq
    have h1 := (Finset.mem_filter.mp hp).2
    have h2 := (Finset.mem_filter.mp hq).2
    exact Prod.ext (h1.trans h2.symm) hpq
  have hrel' : ∑ k ∈ (S.filter (fun p => p.1 = p0.1)).image Prod.snd, c (p0.1, k) • f k = 0 := by
    rw [Finset.sum_image (fun p hp q hq hpq => hinj hp hq hpq), ← hrel]
    apply Finset.sum_congr rfl
    intro p hp
    have h1 := (Finset.mem_filter.mp hp).2
    rw [show (p0.1, p.2) = p from Prod.ext h1.symm rfl]
  have := (linearIndependent_iff'.mp hf) _ _ hrel' p0.2
    (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hp0, rfl⟩))
  simpa using this

/-! ### Scaling the first `m` variables -/

/-- `t_i ↦ z t_i` for the first `m` variables, into polynomials in `z`. -/
def hz (m s : ℕ) : MvPolynomial (Fin (m + s)) ℂ →ₐ[ℂ] Polynomial (MvPolynomial (Fin (m + s)) ℂ) :=
  aeval fun i => Polynomial.C (X i) * Polynomial.X ^ (if (i : ℕ) < m then 1 else 0)

theorem hz_natAdd (f : MvPolynomial (Fin s) ℂ) :
    hz m s (rename (Fin.natAdd m) f) = Polynomial.C (rename (Fin.natAdd m) f) := by
  have : (hz m s).comp (rename (Fin.natAdd m)) =
      (Polynomial.CAlgHom).comp (rename (Fin.natAdd m)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [hz]
  exact AlgHom.congr_fun this f

theorem hz_esymm (k : ℕ) :
    (hz m s (esymm (Fin (m + s)) ℂ k)).natDegree ≤ k ∧
      (hz m s (esymm (Fin (m + s)) ℂ k)).coeff k = rename (Fin.castAdd s) (esymm (Fin m) ℂ k) := by
  classical
  have hexp : hz m s (esymm (Fin (m + s)) ℂ k) =
      ∑ t ∈ Finset.powersetCard k (Finset.univ : Finset (Fin (m + s))),
      Polynomial.C (∏ i ∈ t, X i) *
        Polynomial.X ^ (∑ i ∈ t, (if (i : ℕ) < m then 1 else 0)) := by
    rw [esymm, map_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [map_prod]
    simp only [hz, aeval_X]
    rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]
  have hcard : ∀ t ∈ Finset.powersetCard k (Finset.univ : Finset (Fin (m + s))),
      ∑ i ∈ t, (if (i : ℕ) < m then 1 else 0) ≤ k := by
    intro t ht
    rw [Finset.mem_powersetCard] at ht
    calc ∑ i ∈ t, (if (i : ℕ) < m then 1 else 0) ≤ ∑ i ∈ t, 1 :=
          Finset.sum_le_sum fun i _ => by split_ifs <;> omega
      _ = k := by rw [Finset.sum_const, smul_eq_mul, mul_one, ht.2]
  refine ⟨?_, ?_⟩
  · rw [hexp]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro t ht
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (hcard t ht)
  · rw [hexp, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    -- the surviving subsets are those inside the first `m` variables
    have hiff : ∀ t ∈ Finset.powersetCard k (Finset.univ : Finset (Fin (m + s))),
        (k = ∑ i ∈ t, (if (i : ℕ) < m then 1 else 0)) ↔
          t ∈ Finset.powersetCard k (Finset.univ.map (Fin.castAddEmb s)) := by
      intro t ht
      have ht' := Finset.mem_powersetCard.mp ht
      rw [Finset.mem_powersetCard]
      constructor
      · intro h
        refine ⟨fun i hi => ?_, ht'.2⟩
        by_contra hni
        have hlt : (i : ℕ) < m ∨ ¬ (i : ℕ) < m := em _
        rcases hlt with hlt | hlt
        · exact hni (Finset.mem_map.mpr ⟨⟨i, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
        · have : ∑ j ∈ t, (if (j : ℕ) < m then 1 else 0) < k := by
            calc ∑ j ∈ t, (if (j : ℕ) < m then 1 else 0) <
                ∑ j ∈ t, 1 := Finset.sum_lt_sum (fun j _ => by split_ifs <;> omega)
                  ⟨i, hi, by simp [hlt]⟩
              _ = k := by rw [Finset.sum_const, smul_eq_mul, mul_one, ht'.2]
          omega
      · rintro ⟨hsub, -⟩
        rw [← ht'.2, Finset.card_eq_sum_ones]
        apply Finset.sum_congr rfl
        intro i hi
        obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp (hsub hi)
        simp
    rw [← Finset.sum_filter]
    have hfilt : (Finset.powersetCard k (Finset.univ : Finset (Fin (m + s)))).filter
        (fun t : Finset (Fin (m + s)) => k = ∑ i ∈ t, (if (i : ℕ) < m then 1 else 0)) =
          Finset.powersetCard k (Finset.univ.map (Fin.castAddEmb s)) := by
      ext t
      rw [Finset.mem_filter]
      constructor
      · rintro ⟨ht, h⟩; exact (hiff t ht).mp h
      · intro h
        have ht : t ∈ Finset.powersetCard k (Finset.univ : Finset (Fin (m + s))) :=
          Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_powersetCard.mp h).2⟩
        exact ⟨ht, (hiff t ht).mpr h⟩
    rw [hfilt, Finset.powersetCard_map, Finset.sum_map, esymm, map_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [map_prod]
    simp only [rename_X]
    change ∏ i ∈ u.map (Fin.castAddEmb s), X i = _
    rw [Finset.prod_map]
    rfl

/-- Leading coefficients of products, for factors of bounded degree. -/
theorem prod_natDegree_coeff {ι : Type*} (S : Finset ι) (Q : ι → Polynomial (MvPolynomial
    (Fin (m + s)) ℂ)) (d : ι → ℕ) (hQ : ∀ i ∈ S, (Q i).natDegree ≤ d i) :
    (∏ i ∈ S, Q i).natDegree ≤ ∑ i ∈ S, d i ∧
      (∏ i ∈ S, Q i).coeff (∑ i ∈ S, d i) = ∏ i ∈ S, (Q i).coeff (d i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have ih' := ih fun i hi => hQ i (Finset.mem_insert_of_mem hi)
    have hQa := hQ a (Finset.mem_insert_self _ _)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    exact ⟨Polynomial.natDegree_mul_le.trans (Nat.add_le_add hQa ih'.1),
      by rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hQa ih'.1, ih'.2]⟩

theorem hz_esymmPow (γ : Fin m → ℕ) :
    (hz m s (esymmPow (Fin.append γ (fun _ : Fin s => 0)))).natDegree ≤ awt γ ∧
      (hz m s (esymmPow (Fin.append γ (fun _ : Fin s => 0)))).coeff (awt γ) =
        rename (Fin.castAdd s) (esymmPow γ) := by
  have hprod : hz m s (esymmPow (Fin.append γ (fun _ : Fin s => 0))) =
      ∏ k : Fin m, (hz m s (esymm (Fin (m + s)) ℂ ((k : ℕ) + 1))) ^ γ k := by
    rw [esymmPow, map_prod, Fin.prod_univ_add]
    simp [Fin.append_left, Fin.append_right]
  have hQ : ∀ k ∈ (Finset.univ : Finset (Fin m)),
      ((hz m s (esymm (Fin (m + s)) ℂ ((k : ℕ) + 1))) ^ γ k).natDegree ≤ ((k : ℕ) + 1) * γ k := by
    intro k _
    exact Polynomial.natDegree_pow_le.trans
      ((Nat.mul_le_mul_left _ (hz_esymm _).1).trans (le_of_eq (mul_comm _ _)))
  have h := prod_natDegree_coeff Finset.univ _ _ hQ
  rw [hprod]
  refine ⟨h.1, ?_⟩
  rw [awt, h.2, esymmPow, map_prod]
  apply Finset.prod_congr rfl
  intro k _
  rw [mul_comm, Polynomial.coeff_pow_of_natDegree_le (hz_esymm _).1, (hz_esymm _).2, map_pow]

/-- **Independence of the mixed elementary-symmetric monomials.** -/
theorem linearIndependent_mixed :
    LinearIndependent ℂ (fun p : (Fin m → ℕ) × (Fin s → ℕ) =>
      esymmPow (Fin.append p.1 (fun _ : Fin s => 0)) * rename (Fin.natAdd m) (esymmPow p.2)) := by
  classical
  have htens := linearIndependent_rename_mul (m := m) (s := s)
    (esymmPow_linearIndependent m) (esymmPow_linearIndependent s)
  rw [linearIndependent_iff']
  intro S c hS p0 hp0
  by_contra hne
  set S' := S.filter (fun p => c p ≠ 0) with hS'
  have hS'ne : S'.Nonempty := ⟨p0, Finset.mem_filter.mpr ⟨hp0, hne⟩⟩
  obtain ⟨p1, hp1, hmax⟩ := Finset.exists_max_image S' (fun p => awt p.1) hS'ne
  set D := awt p1.1
  let c' : (Fin m → ℕ) × (Fin s → ℕ) → ℂ := fun p => if awt p.1 = D then c p else 0
  have hrel : ∑ p ∈ S, c' p • (rename (Fin.castAdd s) (esymmPow p.1) *
      rename (Fin.natAdd m) (esymmPow p.2)) = 0 := by
    have h := congrArg (fun P => (hz m s P).coeff D) hS
    simp only [map_sum, map_smul, Polynomial.finsetSum_coeff, Polynomial.coeff_smul, map_mul,
      hz_natAdd, Polynomial.coeff_mul_C, map_zero, Polynomial.coeff_zero] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hc : c p = 0
    · simp [c', hc]
    · have hle : awt p.1 ≤ D := hmax p (Finset.mem_filter.mpr ⟨hp, hc⟩)
      have hz1 := hz_esymmPow (s := s) p.1
      by_cases hD : awt p.1 = D
      · simp only [c', if_pos hD]
        rw [← hD, hz1.2]
      · simp only [c', if_neg hD, zero_smul]
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_ne (hz1.1.trans hle)
          (by intro h'; exact hD (le_antisymm hle (h' ▸ hz1.1)) |>.elim)), zero_mul, smul_zero]
  have := (linearIndependent_iff'.mp htens) S c' hrel p1 (Finset.mem_filter.mp hp1).1
  simp only [c'] at this
  rw [if_pos rfl] at this
  exact (Finset.mem_filter.mp hp1).2 this

end

end VOA.TwoSeries.ModelChar
