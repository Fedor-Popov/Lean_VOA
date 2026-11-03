/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.SympFermC2
import VOA.Core.FLM
import VOA.Core.WeakAssoc
import VOA.Foundations.IotaZExpansion

/-!
# Evaluation identities for symplectic-fermion Zhu descent

This file proves the arbitrary-word evaluation descent.  `sfGenField_coeff` expands a derived
fermion field mode, `cbz_convol_smul` performs the required Vandermonde convolution, and
`sfEvalWordTransform_pos` inducts through normal ordering.  Its `s = 1` specialization is the
matrix coefficient of every symplectic-fermion Zhu circle generator.
-/

namespace VOA.SympFerm

open VOA
open scoped BigOperators

set_option autoImplicit false

/-! ## §1  Derived generator coefficients -/

theorem sfGenField_coeff (a : Fin 2) (k : ℕ) (m : ℤ) :
    sfGenField a k m = cbz (m + (k : ℤ)) (k : ℤ) • chi a (m + (k : ℤ)) := by
  show ((k.factorial : ℂ)⁻¹) • ((deriv^[k] (chi a)) m) = _
  rw [VertexOperatorAlgebra.deriv_pow_apply,
    cbz_apply_nonneg _ (by positivity : (0 : ℤ) ≤ (k : ℤ)), Int.toNat_natCast,
    ← Int.cast_smul_eq_zsmul ℂ, smul_smul,
    VertexOperatorAlgebra.deriv_scalar_eq_gBinom]

/-! ## §2  A convolution lemma for the integer binomial -/

section Convol

variable {M : Type*} [AddCommGroup M]

/-- Swap of two `ℤ`-indexed finsums for a jointly finitely supported family. -/
private theorem finsum_swapZ (F : ℤ → ℤ → M)
    (hF : (Function.support fun q : ℤ × ℤ => F q.1 q.2).Finite) :
    ∑ᶠ a : ℤ, ∑ᶠ b : ℤ, F a b = ∑ᶠ b : ℤ, ∑ᶠ a : ℤ, F a b := by
  have hswap : (Function.support fun q : ℤ × ℤ => F q.2 q.1).Finite := by
    have hpre : (Function.support fun q : ℤ × ℤ => F q.2 q.1)
        = (Equiv.prodComm ℤ ℤ) ⁻¹' (Function.support fun p : ℤ × ℤ => F p.1 p.2) := rfl
    rw [hpre]
    exact hF.preimage ((Equiv.prodComm ℤ ℤ).injective.injOn)
  calc ∑ᶠ a : ℤ, ∑ᶠ b : ℤ, F a b
      = ∑ᶠ p : ℤ × ℤ, F p.1 p.2 := (finsum_curry (fun p : ℤ × ℤ => F p.1 p.2) hF).symm
    _ = ∑ᶠ q : ℤ × ℤ, F q.2 q.1 :=
        (finsum_comp_equiv (Equiv.prodComm ℤ ℤ) (f := fun p : ℤ × ℤ => F p.1 p.2)).symm
    _ = ∑ᶠ b : ℤ, ∑ᶠ a : ℤ, F a b := finsum_curry (fun q : ℤ × ℤ => F q.2 q.1) hswap

variable [Module ℂ M]

/-- The `i`-support of a `cbz`-weighted family with nonnegative top index. -/
private theorem cbz_smul_support (k : ℤ) (hk : 0 ≤ k) (F : ℤ → M) :
    (Function.support fun i : ℤ => cbz k i • F i).Finite := by
  refine Set.Finite.subset (Set.finite_Icc (0 : ℤ) k) ?_
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Icc]
  constructor
  · by_contra h
    exact hi (by rw [cbz_apply_neg k (by omega), zero_smul])
  · by_contra h
    exact hi (by rw [cbz_lt hk (by omega), zero_smul])

/-- **The convolution identity.**  `∑_p C(k₁,p) ∑_i C(k₂,i) G(i+p) = ∑_N C(k₁+k₂,N) G(N)`,
the coefficient form of `(1+z)^{k₁}(1+z)^{k₂} = (1+z)^{k₁+k₂}`.  `k₁` may be **negative** (then
`C(k₁,·)` has infinite support); finiteness comes from `G` vanishing above `B`. -/
theorem cbz_convol_smul (k₁ k₂ : ℤ) (hk₂ : 0 ≤ k₂) (G : ℤ → M) (B : ℤ)
    (hG : ∀ s : ℤ, B ≤ s → G s = 0) :
    ∑ᶠ p : ℤ, cbz k₁ p • (∑ᶠ i : ℤ, cbz k₂ i • G (i + p))
      = ∑ᶠ N : ℤ, cbz (k₁ + k₂) N • G N := by
  -- inner reindex `i ↦ N = i + p`
  have hinner : ∀ p : ℤ, (∑ᶠ i : ℤ, cbz k₂ i • G (i + p))
      = ∑ᶠ N : ℤ, cbz k₂ (N - p) • G N := by
    intro p
    have := finsum_comp_equiv (Equiv.addRight p) (f := fun N : ℤ => cbz k₂ (N - p) • G N)
    simpa using this
  have hfin : ∀ p : ℤ, (Function.support fun N : ℤ => cbz k₂ (N - p) • G N).Finite := by
    intro p
    refine Set.Finite.subset (Set.finite_Icc p (p + k₂)) ?_
    intro N hN
    rw [Function.mem_support] at hN
    rw [Set.mem_Icc]
    constructor
    · by_contra h
      exact hN (by rw [cbz_apply_neg k₂ (by omega), zero_smul])
    · by_contra h
      exact hN (by rw [cbz_lt hk₂ (by omega), zero_smul])
  have hstep : ∀ p : ℤ, cbz k₁ p • (∑ᶠ i : ℤ, cbz k₂ i • G (i + p))
      = ∑ᶠ N : ℤ, (cbz k₁ p * cbz k₂ (N - p)) • G N := by
    intro p
    rw [hinner p, smul_finsum' (cbz k₁ p) (hfin p)]
    exact finsum_congr fun N => by rw [smul_smul]
  rw [finsum_congr hstep]
  -- swap
  have hjoint : (Function.support
      fun q : ℤ × ℤ => (cbz k₁ q.1 * cbz k₂ (q.2 - q.1)) • G q.2).Finite := by
    refine Set.Finite.subset ((Set.finite_Icc (0 : ℤ) B).prod (Set.finite_Icc (0 : ℤ) B)) ?_
    rintro ⟨p, N⟩ hq
    rw [Function.mem_support] at hq
    have h1 : (0 : ℤ) ≤ p := by
      by_contra h
      exact hq (by rw [cbz_apply_neg k₁ (by omega), zero_mul, zero_smul])
    have h2 : p ≤ N := by
      by_contra h
      exact hq (by rw [cbz_apply_neg k₂ (by omega), mul_zero, zero_smul])
    have h3 : N < B := by
      by_contra h
      exact hq (by rw [hG N (by omega), smul_zero])
    exact Set.mk_mem_prod (Set.mem_Icc.mpr ⟨h1, by omega⟩) (Set.mem_Icc.mpr ⟨by omega, by omega⟩)
  rw [finsum_swapZ (fun p N => (cbz k₁ p * cbz k₂ (N - p)) • G N) hjoint]
  refine finsum_congr fun N => ?_
  have hpfin : (Function.support fun p : ℤ => cbz k₁ p * cbz k₂ (N - p)).Finite := by
    refine Set.Finite.subset (Set.finite_Icc (N - k₂) N) ?_
    intro p hp
    rw [Function.mem_support] at hp
    rw [Set.mem_Icc]
    constructor
    · by_contra h
      exact hp (by rw [cbz_lt hk₂ (by omega), mul_zero])
    · by_contra h
      exact hp (by rw [cbz_apply_neg k₂ (by omega), mul_zero])
  rw [← finsum_smul' hpfin, cbz_mul_vandermonde]

end Convol

/-! ## §3  The exterior evaluation and binomial transforms -/

/-- The functional on mode space which identifies every level with level zero, with the
alternating Zhu sign. -/
noncomputable def sfEvalC (c : Fin 2) : SFModes →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ (fun p : ℕ × Fin 2 => if p.2 = c then ((-1 : ℂ) ^ p.1) else 0)

theorem sfEvalC_single (c : Fin 2) (k : ℕ) (a : Fin 2) :
    sfEvalC c (Finsupp.single ((k, a) : ℕ × Fin 2) (1 : ℂ))
      = (if a = c then ((-1 : ℂ) ^ k) else 0) := by
  rw [sfEvalC, Finsupp.linearCombination_single, smul_eq_mul, one_mul]

/-- The dual-number evaluation of the exterior Fock algebra. -/
noncomputable def sfEval (c : Fin 2) : FockSF →ₐ[ℂ] DualNumber ℂ :=
  CliffordAlgebra.lift QSF
    ⟨(LinearMap.toSpanSingleton ℂ (DualNumber ℂ) DualNumber.eps).comp (sfEvalC c), by
      intro m
      change (sfEvalC c m • (DualNumber.eps : DualNumber ℂ))
          * (sfEvalC c m • (DualNumber.eps : DualNumber ℂ)) = _
      rw [Algebra.smul_mul_assoc, mul_smul_comm, DualNumber.eps_mul_eps, smul_zero, smul_zero]
      simp⟩

theorem sfEval_sfCre (c : Fin 2) (k : ℕ) (a : Fin 2) :
    sfEval c (sfCre k a) = (if a = c then ((-1 : ℂ) ^ k) else 0) • (DualNumber.eps : DualNumber ℂ)
    := by
  rw [sfCre, sfEval, CliffordAlgebra.lift_ι_apply, LinearMap.comp_apply,
    LinearMap.toSpanSingleton_apply, sfEvalC_single]

theorem eps_ne_zero : (DualNumber.eps : DualNumber ℂ) ≠ 0 := by
  intro hz
  have h := congrArg TrivSqZeroExt.snd hz
  rw [DualNumber.snd_eps, TrivSqZeroExt.snd_zero] at h
  exact one_ne_zero h

/-- The binomially transformed matrix coefficient of a word field.  At `s = 1` this is the
evaluation of its Zhu circle residue. -/
noncomputable def sfEvalWordTransform (c : Fin 2) (l : SFWord) (s : ℤ) (v : FockSF) :
    DualNumber ℂ :=
  ∑ᶠ i : ℤ, cbz (sfWeight l : ℤ) i • sfEval c ((YwordSF l) (s - i) v)

/-- A nonnegative-upper-index `cbz` finsum is its evident finite range sum. -/
theorem cbz_finsum_eq_range {M : Type*} [AddCommMonoid M] [Module ℂ M]
    (N : ℕ) (F : ℤ → M) :
    (∑ᶠ i : ℤ, cbz (N : ℤ) i • F i)
      = ∑ i ∈ Finset.range (N + 1), cbz (N : ℤ) (i : ℤ) • F (i : ℤ) := by
  have hlo : ∀ p : ℤ, p < 0 → cbz (N : ℤ) p • F p = 0 := by
    intro p hp
    rw [cbz_apply_neg _ hp, zero_smul]
  have hhi : ∀ p : ℤ, ((N + 1 : ℕ) : ℤ) ≤ p → cbz (N : ℤ) p • F p = 0 := by
    intro p hp
    rw [cbz_lt (by positivity) (by omega), zero_smul]
  have hsubset : Function.support (fun p : ℤ => cbz (N : ℤ) p • F p)
      ⊆ ↑((Finset.range (N + 1)).map ⟨(Int.ofNat ·), by intro a b h; simpa using h⟩) := by
    intro p hp
    rw [Function.mem_support] at hp
    have hp0 : 0 ≤ p := by by_contra h; exact hp (hlo p (by omega))
    have hpN : p < ((N + 1 : ℕ) : ℤ) := by by_contra h; exact hp (hhi p (by omega))
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Finset.mem_range,
      Function.Embedding.coeFn_mk]
    exact ⟨p.toNat, by omega, by simp [Int.toNat_of_nonneg hp0]⟩
  rw [finsum_eq_finsetSum_of_support_subset _ hsubset, Finset.sum_map]
  rfl

/-- Negative-index derived-generator coefficients in the normal-ordering strip vanish. -/
theorem sfGenField_coeff_eq_zero_of_neg_lt (a : Fin 2) (k : ℕ) (m : ℤ)
    (hm : m < 0) (hlo : -((k : ℤ) + 1) < m) : sfGenField a k m = 0 := by
  rw [sfGenField_coeff]
  have htop : 0 ≤ m + (k : ℤ) := by omega
  have hlt : m + (k : ℤ) < (k : ℤ) := by omega
  rw [cbz_lt htop hlt, zero_smul]

/-- The alternating coefficient of a creation-mode derived generator is a fixed-upper-index
binomial. -/
theorem sfGenField_creation_eval_coeff (k m : ℕ) :
    cbz ((m : ℤ) + (k : ℤ)) (k : ℤ) * (-1 : ℂ) ^ (m + k)
      = (-1 : ℂ) ^ k * cbz (-((k : ℤ) + 1)) (m : ℤ) := by
  have hprod :
      (∏ i ∈ Finset.range m, (((-(k : ℤ) - 1 : ℤ) : ℂ) - (i : ℂ)))
        = (-1 : ℂ) ^ m *
          ∏ i ∈ Finset.range m, ((((m + k : ℕ) : ℤ) : ℂ) - (i : ℂ)) := by
    let f : ℕ → ℂ := fun i => ((((m + k : ℕ) : ℤ) : ℂ) - (i : ℂ))
    calc
      (∏ i ∈ Finset.range m, (((-(k : ℤ) - 1 : ℤ) : ℂ) - (i : ℂ)))
          = ∏ i ∈ Finset.range m, ((-1 : ℂ) * f (m - 1 - i)) := by
            refine Finset.prod_congr rfl fun i hi => ?_
            rw [Finset.mem_range] at hi
            have hcast : ((m - 1 - i : ℕ) : ℂ) = (m : ℂ) - 1 - (i : ℂ) := by
              rw [Nat.cast_sub (by omega : i ≤ m - 1), Nat.cast_sub (by omega : 1 ≤ m)]
              push_cast
              ring
            simp only [f]
            rw [hcast]
            push_cast
            ring
      _ = (-1 : ℂ) ^ m *
            ∏ i ∈ Finset.range m, f (m - 1 - i) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
      _ = (-1 : ℂ) ^ m *
            ∏ i ∈ Finset.range m, ((((m + k : ℕ) : ℤ) : ℂ) - (i : ℂ)) := by
            rw [Finset.prod_range_reflect]
  have hneg : gBinom (-(k : ℤ) - 1) m
      = (-1 : ℂ) ^ m * gBinom ((m + k : ℕ) : ℤ) m := by
    rw [gBinom, gBinom, hprod]
    ring
  have hchoose : (m + k).choose k = (m + k).choose m := by
    simpa [Nat.add_sub_cancel_right] using
      (Nat.choose_symm (show k ≤ m + k by omega)).symm
  rw [cbz_apply_nonneg _ (by positivity : (0 : ℤ) ≤ (k : ℤ)),
    cbz_apply_nonneg _ (by positivity : (0 : ℤ) ≤ (m : ℤ)),
    Int.toNat_natCast, Int.toNat_natCast,
    show (m : ℤ) + (k : ℤ) = ((m + k : ℕ) : ℤ) by omega,
    show (-((k : ℤ) + 1) : ℤ) = -(k : ℤ) - 1 by ring, hneg,
    gBinom_natCast_eq_choose (by omega : k ≤ m + k),
    gBinom_natCast_eq_choose (by omega : m ≤ m + k),
    hchoose, pow_add]
  ring

/-- On the creation half of normal ordering, evaluation turns a derived generator into
left multiplication by `eps` with the negative-binomial coefficient used by Vandermonde. -/
theorem sfEval_sfGenField_nonneg (c a : Fin 2) (k : ℕ) (m : ℤ) (hm : 0 ≤ m) (x : FockSF) :
    sfEval c (sfGenField a k m x)
      = ((if a = c then (-1 : ℂ) ^ k else 0) * cbz (-((k : ℤ) + 1)) m)
          • ((DualNumber.eps : DualNumber ℂ) * sfEval c x) := by
  set mn := m.toNat
  have hmn : (mn : ℤ) = m := by omega
  rw [← hmn]
  rw [sfGenField_coeff, LinearMap.smul_apply, map_smul, chi, if_pos (by positivity),
    show ((mn : ℤ) + (k : ℤ)).toNat = mn + k by omega]
  rw [show creSF a (mn + k) x = sfCre (mn + k) a * x from rfl,
    map_mul, sfEval_sfCre]
  by_cases ha : a = c
  · rw [if_pos ha, if_pos ha, pow_add]
    rw [smul_mul_assoc, smul_smul]
    rw [← pow_add, sfGenField_creation_eval_coeff]
  · rw [if_neg ha, if_neg ha]
    simp

/-- Split the total binomial transform of a nonempty word into the transforms belonging to its
head weight and tail weight. -/
theorem sfEvalWordTransform_cons_split (c : Fin 2) (p : ℕ × Fin 2) (rest : SFWord)
    (s : ℤ) (v : FockSF) :
    sfEvalWordTransform c (p :: rest) s v
      = ∑ᶠ t : ℤ, cbz ((p.1 : ℤ) + 1) t •
          (∑ᶠ j : ℤ, cbz (sfWeight rest : ℤ) j •
            sfEval c ((YwordSF (p :: rest)) (s - (j + t)) v)) := by
  obtain ⟨B0, hB0⟩ := YwordSF_isField (p :: rest) v
  let G : ℤ → DualNumber ℂ := fun N => sfEval c ((YwordSF (p :: rest)) (s - N) v)
  have hG : ∀ N : ℤ, (s - B0 + 1) ≤ N → G N = 0 := by
    intro N hN
    simp only [G]
    rw [hB0 (s - N) (by omega), map_zero]
  have hconv := cbz_convol_smul ((p.1 : ℤ) + 1) (sfWeight rest : ℤ)
    (by positivity) G (s - B0 + 1) hG
  rw [sfEvalWordTransform, sfWeight_cons,
    show (((p.1 + 1 + sfWeight rest : ℕ) : ℤ))
        = ((p.1 : ℤ) + 1) + (sfWeight rest : ℤ) by push_cast; ring,
    ← hconv]

/-- The normal-ordering split after applying the tail binomial transform.  The creation half is
the negative-binomial coefficient from `sfEval_sfGenField_nonneg`; the reordered half is exactly
the same tail transform with the annihilation mode first applied to the right state. -/
theorem sfEval_nprod_tail_transform (c : Fin 2) (p : ℕ × Fin 2) (rest : SFWord)
    (s t : ℤ) (v : FockSF) :
    (∑ᶠ j : ℤ, cbz (sfWeight rest : ℤ) j •
      sfEval c ((YwordSF (p :: rest)) (s - (j + t)) v))
      = ∑ᶠ m : ℤ,
          if 0 ≤ m then
            (((if p.2 = c then (-1 : ℂ) ^ p.1 else 0) * cbz (-((p.1 : ℤ) + 1)) m)
              • ((DualNumber.eps : DualNumber ℂ) *
                sfEvalWordTransform c rest (s - t - m) v))
          else
            (koszul 1 (rest.length : ZMod 2)) •
              sfEvalWordTransform c rest (s - t - m) (sfGenField p.2 p.1 m v) := by
  rw [cbz_finsum_eq_range]
  rw [YwordSF_cons]
  have hmap : ∀ j ∈ Finset.range (sfWeight rest + 1),
      sfEval c
          (nprodε (koszul 1 (rest.length : ZMod 2)) (sfGenField_isField p.2 p.1)
            (YwordSF_isField rest) (s - ((j : ℤ) + t)) v)
        = ∑ᶠ m : ℤ, sfEval c
            (normalOrderedε (koszul 1 (rest.length : ZMod 2)) (sfGenField p.2 p.1)
              (YwordSF rest) m (s - ((j : ℤ) + t) - m) v) := by
    intro j hj
    rw [nprodε_apply]
    exact map_finsum (sfEval c).toLinearMap
      (normalOrderedε_diag_support_finite _ (sfGenField_isField p.2 p.1)
        (YwordSF_isField rest) (s - ((j : ℤ) + t)) v)
  have hmap' :
      (∑ j ∈ Finset.range (sfWeight rest + 1),
        cbz (sfWeight rest : ℤ) (j : ℤ) • sfEval c
          (nprodε (koszul 1 (rest.length : ZMod 2)) (sfGenField_isField p.2 p.1)
            (YwordSF_isField rest) (s - ((j : ℤ) + t)) v))
        = ∑ j ∈ Finset.range (sfWeight rest + 1),
          cbz (sfWeight rest : ℤ) (j : ℤ) •
            (∑ᶠ m : ℤ, sfEval c
              (normalOrderedε (koszul 1 (rest.length : ZMod 2)) (sfGenField p.2 p.1)
                (YwordSF rest) m (s - ((j : ℤ) + t) - m) v)) := by
    exact Finset.sum_congr rfl fun j hj => by rw [hmap j hj]
  rw [hmap']
  have hsmul : ∀ j ∈ Finset.range (sfWeight rest + 1),
      cbz (sfWeight rest : ℤ) (j : ℤ) •
          (∑ᶠ m : ℤ, sfEval c
            (normalOrderedε (koszul 1 (rest.length : ZMod 2)) (sfGenField p.2 p.1)
              (YwordSF rest) m (s - ((j : ℤ) + t) - m) v))
        = ∑ᶠ m : ℤ, cbz (sfWeight rest : ℤ) (j : ℤ) • sfEval c
            (normalOrderedε (koszul 1 (rest.length : ZMod 2)) (sfGenField p.2 p.1)
              (YwordSF rest) m (s - ((j : ℤ) + t) - m) v) := by
    intro j hj
    apply smul_finsum'
    exact (normalOrderedε_diag_support_finite _ (sfGenField_isField p.2 p.1)
      (YwordSF_isField rest) (s - ((j : ℤ) + t)) v).subset fun m hm => by
        rw [Function.mem_support] at hm ⊢
        intro hz
        exact hm (by rw [hz, map_zero])
  rw [Finset.sum_congr rfl hsmul]
  rw [← finsum_sum_comm (Finset.range (sfWeight rest + 1))
    (fun m j => cbz (sfWeight rest : ℤ) (j : ℤ) • sfEval c
      (normalOrderedε (koszul 1 (rest.length : ZMod 2)) (sfGenField p.2 p.1)
        (YwordSF rest) m (s - ((j : ℤ) + t) - m) v)) (fun j hj => ?_)]
  · refine finsum_congr fun m => ?_
    by_cases hm : 0 ≤ m
    · rw [if_pos hm]
      have hterm : ∀ j ∈ Finset.range (sfWeight rest + 1),
          cbz (sfWeight rest : ℤ) (j : ℤ) • sfEval c
              (normalOrderedε (koszul 1 (rest.length : ZMod 2)) (sfGenField p.2 p.1)
                (YwordSF rest) m (s - ((j : ℤ) + t) - m) v)
            = ((if p.2 = c then (-1 : ℂ) ^ p.1 else 0) *
                cbz (-((p.1 : ℤ) + 1)) m) •
              (cbz (sfWeight rest : ℤ) (j : ℤ) •
                ((DualNumber.eps : DualNumber ℂ) *
                  sfEval c ((YwordSF rest) ((s - t - m) - (j : ℤ)) v))) := by
        intro j hj
        rw [normalOrderedε_apply, if_pos hm, Module.End.mul_apply,
          sfEval_sfGenField_nonneg c p.2 p.1 m hm,
          show s - ((j : ℤ) + t) - m = (s - t - m) - (j : ℤ) by ring,
          smul_comm (cbz (sfWeight rest : ℤ) (j : ℤ))]
      rw [Finset.sum_congr rfl hterm, ← Finset.smul_sum]
      congr 1
      rw [sfEvalWordTransform, cbz_finsum_eq_range]
      rw [show (∑ j ∈ Finset.range (sfWeight rest + 1),
            cbz (sfWeight rest : ℤ) (j : ℤ) •
              ((DualNumber.eps : DualNumber ℂ) *
                sfEval c ((YwordSF rest) ((s - t - m) - (j : ℤ)) v)))
          = (DualNumber.eps : DualNumber ℂ) *
              ∑ j ∈ Finset.range (sfWeight rest + 1),
                cbz (sfWeight rest : ℤ) (j : ℤ) •
                  sfEval c ((YwordSF rest) ((s - t - m) - (j : ℤ)) v) from by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j hj => by rw [mul_smul_comm]]
    · rw [if_neg hm]
      have hterm : ∀ j ∈ Finset.range (sfWeight rest + 1),
          cbz (sfWeight rest : ℤ) (j : ℤ) • sfEval c
              (normalOrderedε (koszul 1 (rest.length : ZMod 2)) (sfGenField p.2 p.1)
                (YwordSF rest) m (s - ((j : ℤ) + t) - m) v)
            = (koszul 1 (rest.length : ZMod 2)) •
              (cbz (sfWeight rest : ℤ) (j : ℤ) •
                sfEval c ((YwordSF rest) ((s - t - m) - (j : ℤ))
                  (sfGenField p.2 p.1 m v))) := by
        intro j hj
        rw [normalOrderedε_apply, if_neg hm, LinearMap.smul_apply, Module.End.mul_apply, map_smul,
          show s - ((j : ℤ) + t) - m = (s - t - m) - (j : ℤ) by ring,
          smul_comm (cbz (sfWeight rest : ℤ) (j : ℤ))]
      rw [Finset.sum_congr rfl hterm, ← Finset.smul_sum]
      congr 1
      rw [sfEvalWordTransform, cbz_finsum_eq_range]
  · refine Set.Finite.subset
      (normalOrderedε_diag_support_finite (koszul 1 (rest.length : ZMod 2))
        (sfGenField_isField p.2 p.1) (YwordSF_isField rest) (s - ((j : ℤ) + t)) v) ?_
    intro m hm
    rw [Function.mem_support] at hm ⊢
    intro hz
    apply hm
    change cbz (sfWeight rest : ℤ) (j : ℤ) • sfEval c
      (normalOrderedε (koszul 1 (rest.length : ZMod 2)) (sfGenField p.2 p.1)
        (YwordSF rest) m (s - ((j : ℤ) + t) - m) v) = 0
    rw [hz, map_zero, smul_zero]

/-- If all sufficiently low modes of a word field kill a fixed state, then the same lower
truncation bound kills its binomial evaluation transform. -/
theorem sfEvalWordTransform_eq_zero_of_lt (c : Fin 2) (l : SFWord) (v : FockSF) (B s : ℤ)
    (hB : ∀ q : ℤ, q < B → (YwordSF l) q v = 0) (hs : s < B) :
    sfEvalWordTransform c l s v = 0 := by
  rw [sfEvalWordTransform, cbz_finsum_eq_range]
  apply Finset.sum_eq_zero
  intro i hi
  rw [hB (s - (i : ℤ)) (by omega), map_zero, smul_zero]

@[simp] theorem sfEvalWordTransform_zero (c : Fin 2) (l : SFWord) (s : ℤ) :
    sfEvalWordTransform c l s 0 = 0 := by
  rw [sfEvalWordTransform]
  apply finsum_eq_zero_of_forall_eq_zero
  intro i
  rw [map_zero, map_zero, smul_zero]

/-- The binomial transform of every word field has zero exterior evaluation at every
strictly positive offset.  The induction invariant is deliberately stronger than the Zhu
circle case `s = 1`: it is what makes every contraction term in the annihilation half of normal
ordering fall under the induction hypothesis. -/
theorem sfEvalWordTransform_pos :
    ∀ (l : SFWord) (c : Fin 2) (s : ℤ) (v : FockSF),
      0 < s → sfEvalWordTransform c l s v = 0
  | [], c, s, v, hs => by
      rw [sfEvalWordTransform, sfWeight_nil, cbz_finsum_eq_range]
      simp [YwordSF_nil, idField_apply, hs.ne']
  | p :: rest, c, s, v, hs => by
      let A : ℂ := if p.2 = c then (-1 : ℂ) ^ p.1 else 0
      let P : ℤ := (p.1 : ℤ) + 1
      obtain ⟨B0, hB0⟩ := YwordSF_isField rest v
      let G : ℤ → DualNumber ℂ := fun N =>
        (DualNumber.eps : DualNumber ℂ) * sfEvalWordTransform c rest (s - N) v
      have hG : ∀ N : ℤ, (s - B0 + 1) ≤ N → G N = 0 := by
        intro N hN
        simp only [G]
        rw [sfEvalWordTransform_eq_zero_of_lt c rest v B0 (s - N) hB0 (by omega),
          mul_zero]
      have hneg : ∀ (t m : ℤ), 0 ≤ t → t ≤ P → m < 0 →
          sfEvalWordTransform c rest (s - t - m) (sfGenField p.2 p.1 m v) = 0 := by
        intro t m ht0 htP hm
        by_cases hmP : m ≤ -P
        · exact sfEvalWordTransform_pos rest c (s - t - m) (sfGenField p.2 p.1 m v)
            (by omega)
        · have hfield : sfGenField p.2 p.1 m = 0 :=
            sfGenField_coeff_eq_zero_of_neg_lt p.2 p.1 m hm (by simpa [P] using hmP)
          rw [hfield, LinearMap.zero_apply, sfEvalWordTransform_zero]
      have hinner : ∀ t : ℤ, 0 ≤ t → t ≤ P →
          (∑ᶠ j : ℤ, cbz (sfWeight rest : ℤ) j •
            sfEval c ((YwordSF (p :: rest)) (s - (j + t)) v))
            = A • (∑ᶠ m : ℤ, cbz (-P) m • G (t + m)) := by
        intro t ht0 htP
        rw [sfEval_nprod_tail_transform]
        have hfamily : (Function.support fun m : ℤ => cbz (-P) m • G (t + m)).Finite := by
          refine Set.Finite.subset (Set.finite_Icc (0 : ℤ) (s - B0 - t)) ?_
          intro m hm
          rw [Function.mem_support] at hm
          rw [Set.mem_Icc]
          constructor
          · by_contra hm0
            exact hm (by rw [cbz_apply_neg (-P) (by omega), zero_smul])
          · by_contra hmB
            exact hm (by rw [hG (t + m) (by omega), smul_zero])
        rw [smul_finsum' A hfamily]
        refine finsum_congr fun m => ?_
        by_cases hm : 0 ≤ m
        · rw [if_pos hm, smul_smul]
          simp only [A, P, G]
          congr 2
          ring_nf
        · rw [if_neg hm, hneg t m ht0 htP (by omega), smul_zero,
            cbz_apply_neg (-P) (by omega), zero_smul, smul_zero]
      have hfamily : ∀ t : ℤ,
          (Function.support fun m : ℤ => cbz (-P) m • G (t + m)).Finite := by
        intro t
        refine Set.Finite.subset (Set.finite_Icc (0 : ℤ) (s - B0 - t)) ?_
        intro m hm
        rw [Function.mem_support] at hm
        rw [Set.mem_Icc]
        constructor
        · by_contra hm0
          exact hm (by rw [cbz_apply_neg (-P) (by omega), zero_smul])
        · by_contra hmB
          exact hm (by rw [hG (t + m) (by omega), smul_zero])
      have hswap :
          (∑ t ∈ Finset.range (p.1 + 2), cbz P (t : ℤ) •
              (∑ᶠ m : ℤ, cbz (-P) m • G ((t : ℤ) + m)))
            = ∑ᶠ m : ℤ, cbz (-P) m •
                (∑ᶠ t : ℤ, cbz P t • G (t + m)) := by
        calc
          (∑ t ∈ Finset.range (p.1 + 2), cbz P (t : ℤ) •
              (∑ᶠ m : ℤ, cbz (-P) m • G ((t : ℤ) + m)))
              = ∑ t ∈ Finset.range (p.1 + 2), ∑ᶠ m : ℤ,
                  cbz P (t : ℤ) • (cbz (-P) m • G ((t : ℤ) + m)) := by
                    refine Finset.sum_congr rfl fun t ht => ?_
                    exact smul_finsum' _ (hfamily (t : ℤ))
          _ = ∑ᶠ m : ℤ, ∑ t ∈ Finset.range (p.1 + 2),
                  cbz P (t : ℤ) • (cbz (-P) m • G ((t : ℤ) + m)) := by
                    rw [finsum_sum_comm (Finset.range (p.1 + 2))
                      (fun m t => cbz P (t : ℤ) •
                        (cbz (-P) m • G ((t : ℤ) + m))) (fun t ht => ?_)]
                    exact (hfamily (t : ℤ)).subset fun m hm => by
                      rw [Function.mem_support] at hm ⊢
                      intro hz
                      apply hm
                      change cbz P (t : ℤ) • (cbz (-P) m • G ((t : ℤ) + m)) = 0
                      rw [hz, smul_zero]
          _ = ∑ᶠ m : ℤ, cbz (-P) m •
                (∑ᶠ t : ℤ, cbz P t • G (t + m)) := by
                    refine finsum_congr fun m => ?_
                    rw [show P = ((p.1 + 1 : ℕ) : ℤ) by simp [P]]
                    rw [cbz_finsum_eq_range]
                    rw [Finset.smul_sum]
                    exact Finset.sum_congr rfl fun t ht => by rw [smul_comm]
      have hconv := cbz_convol_smul (-P) P (by simp [P]; omega) G (s - B0 + 1) hG
      have hconv0 :
          (∑ᶠ m : ℤ, cbz (-P) m • (∑ᶠ t : ℤ, cbz P t • G (t + m))) = G 0 := by
        rw [hconv]
        have hzero : -P + P = 0 := by ring
        rw [hzero]
        rw [finsum_eq_single _ 0 (fun N hN => by
          rw [cbz_zero_left, if_neg hN, zero_smul])]
        rw [cbz_zero, one_smul]
      rw [sfEvalWordTransform_cons_split]
      rw [show ((p.1 : ℤ) + 1) = ((p.1 + 1 : ℕ) : ℤ) by simp]
      rw [cbz_finsum_eq_range]
      rw [Finset.sum_congr rfl (fun t ht => by
        rw [hinner (t : ℤ) (by positivity) (by rw [Finset.mem_range] at ht; simp [P]; omega)])]
      have hfactor :
          (∑ t ∈ Finset.range (p.1 + 1 + 1), cbz ((p.1 + 1 : ℕ) : ℤ) (t : ℤ) •
              (A • (∑ᶠ m : ℤ, cbz (-P) m • G ((t : ℤ) + m))))
            = A • (∑ t ∈ Finset.range (p.1 + 2), cbz P (t : ℤ) •
                (∑ᶠ m : ℤ, cbz (-P) m • G ((t : ℤ) + m))) := by
        rw [show p.1 + 1 + 1 = p.1 + 2 by omega]
        rw [show (((p.1 + 1 : ℕ) : ℤ)) = P by simp [P]]
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun t ht => by rw [smul_comm]
      rw [hfactor, hswap, hconv0]
      simp only [G]
      rw [sub_zero, sfEvalWordTransform_pos rest c s v hs, mul_zero, smul_zero]

/-- The `s = 1` specialization used by the Zhu circle residue. -/
theorem sfEval_word_circle_modes (c : Fin 2) (l : SFWord) (v : FockSF) :
    (∑ i ∈ Finset.range (sfWeight l + 1), cbz (sfWeight l : ℤ) (i : ℤ) •
      sfEval c ((YwordSF l) (1 - (i : ℤ)) v)) = 0 := by
  have h := sfEvalWordTransform_pos l c 1 v (by norm_num)
  rw [sfEvalWordTransform, cbz_finsum_eq_range] at h
  exact h

end VOA.SympFerm
