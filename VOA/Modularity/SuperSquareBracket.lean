/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.CuspDegeneration
import VOA.Modules.SuperZhuResidue

/-!
# Square-bracket modes and the cusp degeneration for an integral-weight super VOA

The scalar change-of-coordinate coefficients in Zhu's square-bracket modes do not see parity.
Parity enters only when two states are exchanged.  Consequently the construction of `a[n]`, its
eventual truncation, and DLM Lemma 9.2(c) port from a VOA to a super VOA without a Koszul sign.

This file makes that sign-free part explicit for a `SuperNearVOA`.  The first signed statement is
downstream: modulo the super Zhu ideal, `a[0]b` is the **super**commutator
`a * b - koszul p q • b * a` for parity-homogeneous `a,b`.

## Main results

* `superVSqZ` — the all-integer square-bracket mode of a super near-VOA;
* `superVSqZ_tail_eventually_zero` — the positive even tail truncates;
* `superNegTwoFamily_cusp` — the super version of DLM Lemma 9.2(c).

No result in this file assumes spin-statistics, rationality, or semisimplicity.
-/

namespace VOA

open scoped BigOperators

set_option autoImplicit false

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace SuperNearVOA

variable (V : SuperNearVOA 𝒱)

/-- The summand defining a super square-bracket mode has finite support: the coordinate-change
coefficient vanishes below the square-bracket index, while ordinary modes vanish above a
regularity bound. -/
theorem superSqModeZ_support_finite (a : 𝒱) (k : ℕ) (m : ℤ) (v : 𝒱) :
    (Function.support fun i : ℤ => sqBracketCoeffZ k m i • V.smul a i v).Finite := by
  obtain ⟨N, hN⟩ := V.regularity a v
  refine Set.Finite.subset (Set.finite_Ico m N) ?_
  intro i hi
  simp only [Function.mem_support, ne_eq] at hi
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hi (by rw [sqBracketCoeffZ_of_lt k (not_le.mp h), zero_smul])
  · by_contra h
    push_neg at h
    have hz : V.smul a i v = 0 := hN i h
    exact hi (by rw [hz, smul_zero])

/-- The all-integer square-bracket mode `a[m]` for a super near-VOA.  The formula is identical to
the bosonic one because changing the formal coordinate exchanges no states. -/
noncomputable def superVSqZ (a : 𝒱) (k : ℕ) (m : ℤ) : 𝒱 →ₗ[ℂ] 𝒱 where
  toFun v := ∑ᶠ i : ℤ, sqBracketCoeffZ k m i • V.smul a i v
  map_add' x y := by
    simp only [SuperVertexAlgebra.smul_add_right, smul_add]
    rw [finsum_add_distrib (V.superSqModeZ_support_finite a k m x)
      (V.superSqModeZ_support_finite a k m y)]
  map_smul' c x := by
    show (∑ᶠ i : ℤ, sqBracketCoeffZ k m i • V.smul a i (c • x))
      = c • ∑ᶠ i : ℤ, sqBracketCoeffZ k m i • V.smul a i x
    rw [smul_finsum' c (V.superSqModeZ_support_finite a k m x)]
    refine finsum_congr (fun i => ?_)
    rw [SuperVertexAlgebra.smul_smul_right, smul_comm]

@[simp] theorem superVSqZ_apply (a : 𝒱) (k : ℕ) (m : ℤ) (v : 𝒱) :
    V.superVSqZ a k m v = ∑ᶠ i : ℤ, sqBracketCoeffZ k m i • V.smul a i v := rfl

/-- Square-bracket modes of sufficiently large index vanish on any fixed pair of states. -/
theorem superVSqZ_eventually_zero (a : 𝒱) (k : ℕ) (v : 𝒱) :
    ∃ N : ℤ, ∀ m : ℤ, N ≤ m → V.superVSqZ a k m v = 0 := by
  obtain ⟨N, hN⟩ := V.regularity a v
  refine ⟨N, fun m hm => ?_⟩
  rw [V.superVSqZ_apply]
  refine finsum_eq_zero_of_forall_eq_zero (fun i => ?_)
  rcases lt_or_ge i N with hi | hi
  · rw [sqBracketCoeffZ_of_lt k (by omega), zero_smul]
  · have hz : V.smul a i v = 0 := hN i hi
    rw [hz, smul_zero]

/-- The positive even tail `a[2m]v` occurring in the genus-one relation is eventually zero. -/
theorem superVSqZ_tail_eventually_zero (a : 𝒱) (k : ℕ) (v : 𝒱) :
    ∃ K : ℕ, ∀ m : ℕ, K ≤ m →
      V.superVSqZ a k (2 * (m + 1) - 2 : ℤ) v = 0 := by
  obtain ⟨N, hN⟩ := V.superVSqZ_eventually_zero a k v
  exact ⟨N.toNat, fun m hm => hN _ (by omega)⟩

/-- A square-bracket mode with index at least `-2`, truncated to a common ordinary-mode window. -/
theorem superVSqZ_eq_sum_Ico {k : ℕ} {M : ℤ} (hM : -2 ≤ M) (a v : 𝒱) {P : ℕ}
    (hP : ∀ i : ℤ, (P : ℤ) ≤ i → V.smul a i v = 0) :
    V.superVSqZ a k M v
      = ∑ i ∈ Finset.Ico (-2 : ℤ) (P : ℤ), sqBracketCoeffZ k M i • V.smul a i v := by
  classical
  rw [V.superVSqZ_apply]
  refine finsum_eq_finsetSum_of_support_subset _ (fun i hi => ?_)
  simp only [Function.mem_support, ne_eq] at hi
  simp only [Finset.coe_Ico, Set.mem_Ico]
  constructor
  · by_contra hc
    push_neg at hc
    exact hi (by rw [sqBracketCoeffZ_of_lt k (by omega), zero_smul])
  · by_contra hc
    push_neg at hc
    exact hi (by rw [hP i hc, smul_zero])

/-- The depth-zero super Zhu residue on the same ordinary-mode window. -/
theorem superPres_zero_eq_sum_Ico {k : ℕ} (a v : 𝒱) {P : ℕ}
    (hP : ∀ i : ℤ, (P : ℤ) ≤ i → V.smul a i v = 0) (hkP : k ≤ P) :
    V.superPres k a v 0
      = ∑ i ∈ Finset.Ico (-2 : ℤ) (P : ℤ), cbz (k : ℤ) (i + 2) • V.smul a i v := by
  classical
  have hmapset : Finset.Ico (-2 : ℤ) (P : ℤ)
      = (Finset.range (P + 2)).map ⟨fun j : ℕ => (j : ℤ) - 2, fun x y h => by simpa using h⟩ := by
    ext i
    simp only [Finset.mem_Ico, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(i + 2).toNat, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      omega
  rw [hmapset, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have hterm : ∀ j ∈ Finset.range (P + 2),
      cbz (k : ℤ) (((j : ℤ) - 2) + 2) • V.smul a ((j : ℤ) - 2) v
        = cbz ((k : ℤ) + ((0 : ℕ) : ℤ)) (j : ℤ)
            • V.smul a ((j : ℤ) - 2 - ((0 : ℕ) : ℤ)) v := by
    intro j _
    rw [show (((j : ℤ) - 2) + 2) = (j : ℤ) from by ring,
      show ((k : ℤ) + ((0 : ℕ) : ℤ)) = (k : ℤ) from by push_cast; ring,
      show ((j : ℤ) - 2 - ((0 : ℕ) : ℤ)) = (j : ℤ) - 2 from by push_cast; ring]
  rw [Finset.sum_congr rfl hterm, superPres]
  have hsub : Finset.range (k + 0 + 1) ⊆ Finset.range (P + 2) :=
    Finset.range_mono (by omega)
  refine Finset.sum_subset hsub (fun j _ hj => ?_)
  rw [Finset.mem_range, not_lt] at hj
  rw [show ((k : ℤ) + ((0 : ℕ) : ℤ)) = (k : ℤ) from by push_cast; ring,
    cbz_lt (by omega) (by omega : (k : ℤ) < (j : ℤ)), zero_smul]

/-- DLM Lemma 9.2(c) for a super near-VOA.  No Koszul factor occurs: every summand contains modes
of the same state `a`, and no homogeneous states are interchanged. -/
theorem superNegTwoFamily_cusp {k : ℕ} (hk : 1 ≤ k) (a v : 𝒱) :
    V.superVSqZ a k (-2) v
        + ∑ᶠ m : ℕ, (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0)
            • V.superVSqZ a k (2 * ((m : ℤ) + 2) - 2) v
      = V.superPres k a v 0 + (1 / 12 : ℂ) • V.superVSqZ a k 0 v := by
  classical
  obtain ⟨N, hN⟩ := V.regularity a v
  set P : ℕ := (max N (k : ℤ)).toNat with hPdef
  have hP : ∀ i : ℤ, (P : ℤ) ≤ i → V.smul a i v = 0 := by
    intro i hi
    exact hN i (by omega)
  have hkP : k ≤ P := by omega
  set S : Finset ℤ := Finset.Ico (-2 : ℤ) (P : ℤ) with hS
  have hmode : ∀ M : ℤ, -2 ≤ M → V.superVSqZ a k M v
      = ∑ i ∈ S, sqBracketCoeffZ k M i • V.smul a i v :=
    fun M hM => V.superVSqZ_eq_sum_Ico hM a v hP
  have hzero : ∀ m : ℕ, P ≤ m →
      V.superVSqZ a k (2 * ((m : ℤ) + 2) - 2) v = 0 := by
    intro m hm
    rw [hmode _ (by omega)]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [Finset.mem_Ico] at hi
    rw [sqBracketCoeffZ_of_lt k (by omega), zero_smul]
  have hfin : ∑ᶠ m : ℕ, (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0)
        • V.superVSqZ a k (2 * ((m : ℤ) + 2) - 2) v
      = ∑ m ∈ Finset.range P, (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0)
        • V.superVSqZ a k (2 * ((m : ℤ) + 2) - 2) v := by
    refine finsum_eq_finsetSum_of_support_subset _ (fun m hm => ?_)
    simp only [Function.mem_support, ne_eq] at hm
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    push_neg at hc
    exact hm (by rw [hzero m hc, smul_zero])
  have hswap : ∑ m ∈ Finset.range P,
        (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0)
          • V.superVSqZ a k (2 * ((m : ℤ) + 2) - 2) v
      = ∑ i ∈ S, (∑ m ∈ Finset.range P, ((2 * (m + 2) - 1 : ℕ) : ℂ)
          * zhuG (m + 2) 0 * sqBracketCoeffZ k (2 * ((m : ℤ) + 2) - 2) i)
            • V.smul a i v := by
    rw [Finset.sum_congr rfl (fun m _ => by rw [hmode _ (by omega), Finset.smul_sum]),
      Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl (fun m _ => by rw [smul_smul])
  have hmfin : ∀ i ∈ S,
      ∑ m ∈ Finset.range P, ((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0
          * sqBracketCoeffZ k (2 * ((m : ℤ) + 2) - 2) i
        = ∑ᶠ m : ℕ, ((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0
          * sqBracketCoeffZ k (2 * ((m : ℤ) + 2) - 2) i := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    refine (finsum_eq_finsetSum_of_support_subset _ (fun m hm => ?_)).symm
    simp only [Function.mem_support, ne_eq] at hm
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    push_neg at hc
    exact hm (by rw [sqBracketCoeffZ_of_lt k (by omega), mul_zero])
  rw [hfin, hswap, Finset.sum_congr rfl (fun i hi => by rw [hmfin i hi]),
    hmode _ (by omega), hmode (0 : ℤ) (by omega),
    V.superPres_zero_eq_sum_Ico a v hP hkP, Finset.smul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_Ico] at hi
  rw [smul_smul, ← add_smul, ← add_smul]
  congr 1
  have hkey := sqBracketCoeffZ_neg_two_cusp hk (i + 2).toNat
  rw [show (((i + 2).toNat : ℤ) - 2) = i from by omega,
    show (((i + 2).toNat : ℤ)) = i + 2 from by omega] at hkey
  linear_combination hkey

end SuperNearVOA

end VOA
