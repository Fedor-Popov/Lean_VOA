/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeChargeMContraction
import VOA.Examples.LatticeFields

/-!
# The charge-`(-1)` Heisenberg–lattice mutual locality `Local αLat Y(e^{-α},z)`

The charge-`(-1)` transcription of `LatExp.latticeHL_local` (`Local αLat Yeα`,
`Examples/LatticeFields` §14): the boson current `α(z)` is mutually local with the **inverse**
lattice vertex operator `Y(e^{-α},z) = Yemα (-1)`.  Mechanically mirrors the charge-`+1` proof,
substituting the charge-`(-1)` substrate (`EminusC (-1)`, `EplusC (-1)`, `aExpCZ (-1)`, `EEC (-1)`,
`Yemα (-1)`) and the charge-`(-1)` structure constant `2·(-1) = -2` (the originals use `⟨α,α⟩ = 2`).

All `sorry`-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`), `pbw`-free.
-/

namespace VOA
namespace LatExp

open scoped BigOperators TensorProduct
open Module (End)
open HeisenbergN (oscN vacuumN)
open LatticeVOA (LatModule LatGrp eVec latState latVacuum zGradeOp)

/-! ## §0  The charge-`(-1)` Newton-sum reassembly without the `c•` prefactor -/

/-- The charge-`(-1)` Newton sum reassembles as `∑ = -(L • aExpCZ(-1) L)` (the
`aExpCZ_sum_reassembly` identity with the `c = -1` prefactor moved to the right). -/
theorem aExpCZneg1_sum_reassembly (L : ℤ) (K : ℕ) (hK : L.toNat ≤ K) :
    ∑ m ∈ Finset.range K, (-(α ((m : ℤ) + 1))).comp (aExpCZ (-1) (L - 1 - m))
      = (-1 : ℂ) • ((L : ℂ) • aExpCZ (-1) L) := by
  have h := aExpCZ_sum_reassembly (-1) L K hK
  rw [← h, smul_smul]
  norm_num

/-! ## §8'  The `E⁺(-α)` contraction companion `[α₋ₖ, E⁺(-α)] = -2·E⁺(-α)_{N-k}` -/

/-- **The charge-`(-1)` creation-mode `E⁺` contraction** `[α₋ₖ, aExpCZ(-1)_M] =
-2·aExpCZ(-1)_{M-k}`:
the charge-`(-1)` transcription of `alphaNeg_comp_aExpZ`.  The Heisenberg commutator sub-proofs
`hcomm`/`hmove` are charge-independent; the `aExpCZ_recursion (-1)` step carries the extra `(-1)•`
factor (handled exactly as in `EminusCm1_contraction`). -/
theorem alphaNeg_comp_aExpCZ (k : ℕ) (hk : 1 ≤ k) :
    ∀ M : ℤ, (α (-(k : ℤ))).comp (aExpCZ (-1) M)
      = (aExpCZ (-1) M).comp (α (-(k : ℤ))) + ((2 * (-1) : ℂ)) • aExpCZ (-1) (M - k) := by
  have hcomm : ∀ m : ℕ, α (-(k : ℤ)) * α ((m : ℤ) + 1) - α ((m : ℤ) + 1) * α (-(k : ℤ))
      = (if (m : ℤ) + 1 = (k : ℤ) then (-((2 * k : ℕ) : ℂ)) else 0) • LinearMap.id := by
    intro m
    have h := HeisenbergN.oscN_comm 1 2 0 0 (-(k : ℤ)) ((m : ℤ) + 1)
    simp only [true_and] at h
    rw [show α (-(k : ℤ)) = HeisenbergN.oscN 1 2 0 (-(k : ℤ)) from rfl,
      show α ((m : ℤ) + 1) = HeisenbergN.oscN 1 2 0 ((m : ℤ) + 1) from rfl, h]
    by_cases hc : (m : ℤ) + 1 = (k : ℤ)
    · rw [if_pos (show -(k : ℤ) + ((m : ℤ) + 1) = 0 by omega), if_pos hc]
      congr 1; push_cast; ring
    · rw [if_neg (show ¬ (-(k : ℤ) + ((m : ℤ) + 1) = 0) by omega), if_neg hc]
  have hmove : ∀ m : ℕ, (α (-(k : ℤ))).comp (-(α ((m : ℤ) + 1)))
      = (-(α ((m : ℤ) + 1))).comp (α (-(k : ℤ)))
        + (if (m : ℤ) + 1 = (k : ℤ) then ((2 * k : ℕ) : ℂ) else 0) • LinearMap.id := by
    intro m
    have hAB : α (-(k : ℤ)) * α ((m : ℤ) + 1)
        = α ((m : ℤ) + 1) * α (-(k : ℤ))
          + (if (m : ℤ) + 1 = (k : ℤ) then (-((2 * k : ℕ) : ℂ)) else 0) • LinearMap.id :=
      sub_eq_iff_eq_add'.mp (hcomm m)
    rw [LinearMap.comp_neg, LinearMap.neg_comp,
      show (α (-(k : ℤ))).comp (α ((m : ℤ) + 1)) = α (-(k : ℤ)) * α ((m : ℤ) + 1) from rfl,
      show (α ((m : ℤ) + 1)).comp (α (-(k : ℤ))) = α ((m : ℤ) + 1) * α (-(k : ℤ)) from rfl, hAB]
    by_cases hc : (m : ℤ) + 1 = (k : ℤ)
    · rw [if_pos hc, if_pos hc]; push_cast; module
    · rw [if_neg hc, if_neg hc]; simp
  suffices H : ∀ n : ℕ, ∀ M : ℤ, M.toNat ≤ n →
      (α (-(k : ℤ))).comp (aExpCZ (-1) M)
        = (aExpCZ (-1) M).comp (α (-(k : ℤ))) + ((2 * (-1) : ℂ)) • aExpCZ (-1) (M - k) by
    exact fun M => H M.toNat M le_rfl
  intro n
  induction n with
  | zero =>
    intro M hM
    by_cases h0 : M = 0
    · subst h0
      rw [aExpCZ_zero, LinearMap.comp_id, LinearMap.id_comp,
        aExpCZ_neg (-1) (show (0 : ℤ) - k < 0 by omega), smul_zero, add_zero]
    · rw [aExpCZ_neg (-1) (by omega : M < 0), aExpCZ_neg (-1) (show M - k < 0 by omega),
        LinearMap.comp_zero, LinearMap.zero_comp, smul_zero, add_zero]
  | succ n ih =>
    intro M hM
    by_cases hsmall : M.toNat ≤ n
    · exact ih M hsmall
    · have hM1 : 1 ≤ M := by omega
      have hMne : (M : ℂ) ≠ 0 := by simp only [ne_eq, Int.cast_eq_zero]; omega
      conv_lhs => rw [aExpCZ_recursion (-1) M hM1]
      rw [LinearMap.comp_smul, LinearMap.comp_smul, comp_sum']
      have hterm : ∀ m ∈ Finset.range M.toNat,
          (α (-(k : ℤ))).comp ((-(α ((m : ℤ) + 1))).comp (aExpCZ (-1) (M - 1 - m)))
            = (-(α ((m : ℤ) + 1))).comp ((aExpCZ (-1) (M - 1 - m)).comp (α (-(k : ℤ))))
              + ((2 * (-1) : ℂ)) • (-(α ((m : ℤ) + 1))).comp (aExpCZ (-1) ((M - k) - 1 - m))
              + (if (m : ℤ) + 1 = (k : ℤ) then ((2 * k : ℕ) : ℂ) else 0)
                  • aExpCZ (-1) (M - 1 - m) := by
        intro m _
        rw [← LinearMap.comp_assoc, hmove m, LinearMap.add_comp, LinearMap.comp_assoc,
          ih (M - 1 - m) (by omega)]
        simp only [LinearMap.comp_add, LinearMap.comp_smul, LinearMap.smul_comp,
          LinearMap.id_comp]
        rw [show M - 1 - (m : ℤ) - k = (M - k) - 1 - m from by ring]
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib]
      have hcol1 : (∑ m ∈ Finset.range M.toNat,
            (-(α ((m : ℤ) + 1))).comp ((aExpCZ (-1) (M - 1 - m)).comp (α (-(k : ℤ)))))
          = (-1 : ℂ) • ((M : ℂ) • ((aExpCZ (-1) M).comp (α (-(k : ℤ))))) := by
        simp only [← LinearMap.comp_assoc, ← sum_comp', aExpCZneg1_sum_reassembly M M.toNat le_rfl,
          LinearMap.smul_comp]
      have hcol2 : (∑ m ∈ Finset.range M.toNat,
            ((2 * (-1) : ℂ)) • (-(α ((m : ℤ) + 1))).comp (aExpCZ (-1) ((M - k) - 1 - m)))
          = ((2 * (-1) : ℂ)) • ((-1 : ℂ) • (((M - k : ℤ) : ℂ) • aExpCZ (-1) (M - k))) := by
        rw [← Finset.smul_sum, aExpCZneg1_sum_reassembly (M - k) M.toNat (by omega)]
      have hcol3 : (∑ m ∈ Finset.range M.toNat,
            (if (m : ℤ) + 1 = (k : ℤ) then ((2 * k : ℕ) : ℂ) else 0) • aExpCZ (-1) (M - 1 - m))
          = ((2 * k : ℕ) : ℂ) • aExpCZ (-1) (M - k) := by
        by_cases hkM : k ≤ M.toNat
        · rw [Finset.sum_eq_single (k - 1)]
          · rw [if_pos (by omega), show M - 1 - ((k : ℕ) - 1 : ℕ) = M - k from by
                rw [show ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 from by omega]; ring]
          · intro b _ hb; rw [if_neg (by omega), zero_smul]
          · intro hmem; exact absurd (Finset.mem_range.mpr (by omega)) hmem
        · rw [aExpCZ_neg (-1) (show M - k < 0 by omega), smul_zero]
          refine Finset.sum_eq_zero fun m hm => ?_
          simp only [Finset.mem_range] at hm
          rw [if_neg (by omega), zero_smul]
      rw [hcol1, hcol2, hcol3, inv_smul_eq_iff₀ hMne]
      push_cast
      module

/-! ## §7  The field-level boson OPE `[α(z₁), E⁻(-α,z₂)]` -/

/-- The charge-`(-1)` annihilation-mode field contraction (mirror of `alpha_comp_Eminus_pos`):
for `m ≥ 1`, `αₘ ∘ E⁻(-α)_t = E⁻(-α)_t ∘ αₘ + (-2)·E⁻(-α)_{t-m}`. -/
theorem alpha_comp_EminusC_pos {m : ℕ} (hm : 1 ≤ m) (t : ℤ) :
    (α (m : ℤ)).comp (EminusC (-1) t)
      = (EminusC (-1) t).comp (α (m : ℤ)) + ((2 * (-1) : ℂ)) • EminusC (-1) (t - m) := by
  by_cases ht : 0 ≤ t
  · set N := t.toNat with hN
    have htN : (t : ℤ) = (N : ℤ) := (Int.toNat_of_nonneg ht).symm
    rw [EminusC_nonneg (-1) ht, alpha_comp_EminusOpC (-1) m N hm]
    congr 1
    by_cases hmN : m ≤ N
    · rw [if_pos hmN]
      have : t - m = ((N - m : ℕ) : ℤ) := by rw [htN, Nat.cast_sub hmN]
      rw [EminusC_nonneg (-1) (by omega), this, Int.toNat_natCast]
    · rw [if_neg hmN, EminusC_neg (-1) (by omega), smul_zero]
  · rw [EminusC_neg (-1) (by omega), EminusC_neg (-1) (by omega)]
    simp

/-- The charge-`(-1)` creation-mode commutation (mirror of `alpha_comp_Eminus_neg`):
for `m < 0`, `αₘ ∘ E⁻(-α)_t = E⁻(-α)_t ∘ αₘ`. -/
theorem alpha_comp_EminusC_neg {m : ℤ} (hm : m < 0) (t : ℤ) :
    (α m).comp (EminusC (-1) t) = (EminusC (-1) t).comp (α m) := by
  refine LinearMap.ext fun q => ?_
  rw [EminusC_apply]
  split_ifs with ht
  · simp only [LinearMap.comp_apply, α, EminusOpC, LinearMap.mulLeft_apply,
      HeisenbergN.oscN_apply_neg 1 2 0 hm]
    ring
  · simp

/-- **The field-level boson OPE `[α(z₁), E⁻(-α,z₂)]`** (charge-`(-1)` transcription of
`alphaField_comm_Eminus`): the `z₁ʲz₂ᵗ`-coefficient is `(-2)·E⁻(-α)_{t+j+1}` for `j ≤ -2` and `0`
otherwise. -/
theorem alphaField_comm_EminusC (j t : ℤ) :
    bracketDist alphaField (EminusC (-1)) j t
      = if j ≤ -2 then ((2 * (-1) : ℂ)) • EminusC (-1) (t + j + 1) else 0 := by
  rw [bracketDist_apply, alphaField_apply]
  change (α (-j - 1)).comp (EminusC (-1) t) - (EminusC (-1) t).comp (α (-j - 1)) = _
  by_cases hj : j ≤ -2
  · rw [if_pos hj]
    have hmval : ((-j - 1).toNat : ℤ) = -j - 1 := Int.toNat_of_nonneg (by omega)
    have hm1 : 1 ≤ (-j - 1).toNat := by omega
    have hc := alpha_comp_EminusC_pos hm1 t
    rw [show (-j - 1 : ℤ) = (((-j - 1).toNat : ℤ)) from hmval.symm, hc,
      show t - ((-j - 1).toNat : ℤ) = t + j + 1 from by rw [hmval]; ring]
    abel
  · rw [if_neg hj]
    rcases (show -j - 1 < 0 ∨ -j - 1 = 0 from by omega) with hlt | heq
    · rw [alpha_comp_EminusC_neg hlt t, sub_self]
    · rw [heq]
      change (oscN 1 2 0 0).comp (EminusC (-1) t) - (EminusC (-1) t).comp (oscN 1 2 0 0) = 0
      rw [HeisenbergN.oscN_zero, LinearMap.zero_comp, LinearMap.comp_zero, sub_zero]

/-! ## §13  The field-level boson OPE `[α(z₁), E⁺(-α,z₂)]` -/

/-- `E⁺(-α) = aExpCZ(-1)` commutes with positive boson modes (mirror of
`aExpZ_commute_alphaPos`). -/
theorem aExpCZ_commute_alphaPos (M : ℤ) {p : ℤ} (hp : 1 ≤ p) :
    Commute (aExpCZ (-1) M) (α p) := by
  by_cases hM : 0 ≤ M
  · rw [aExpCZ_nonneg (-1) hM]
    have h := aExpC_commute_alpha (-1) M.toNat (p - 1).toNat
    rwa [show ((p - 1).toNat : ℤ) + 1 = p from by omega] at h
  · rw [aExpCZ_neg (-1) (by omega)]; exact Commute.zero_left _

/-- **The field-level boson OPE `[α(z₁), E⁺(-α,z₂)]`** (charge-`(-1)` transcription of
`alphaField_comm_Eplus`): the `z₁ʲz₂ᵗ`-coefficient is `(-2)·E⁺(-α)_{t+j+1}` for `j ≥ 0` and `0`
otherwise. -/
theorem alphaField_comm_EplusC (j t : ℤ) :
    bracketDist alphaField (EplusC (-1)) j t
      = if 0 ≤ j then ((2 * (-1) : ℂ)) • EplusC (-1) (t + j + 1) else 0 := by
  rw [bracketDist_apply, alphaField_apply]
  change (α (-j - 1)).comp (EplusC (-1) t) - (EplusC (-1) t).comp (α (-j - 1)) = _
  by_cases hj : 0 ≤ j
  · rw [if_pos hj, show -j - 1 = -((j + 1).toNat : ℤ) from by omega, EplusC_eq_aExpCZ (-1) t,
      EplusC_eq_aExpCZ (-1) (t + j + 1), alphaNeg_comp_aExpCZ (j + 1).toNat (by omega) (-t),
      show -t - ((j + 1).toNat : ℤ) = -(t + j + 1) from by omega]
    abel
  · rw [if_neg hj]
    rcases (show -j - 1 = 0 ∨ 1 ≤ -j - 1 from by omega) with h0 | h1
    · rw [h0, show α (0 : ℤ) = (0 : End ℂ B) from HeisenbergN.oscN_zero 1 2 0,
        LinearMap.zero_comp, LinearMap.comp_zero, sub_zero]
    · rw [EplusC_eq_aExpCZ (-1) t,
        show (α (-j - 1)).comp (aExpCZ (-1) (-t)) = (aExpCZ (-1) (-t)).comp (α (-j - 1)) from
          (aExpCZ_commute_alphaPos (-t) h1).eq.symm, sub_self]

/-! ## §14a  The boson-current/dressing commutator `[α(z₁), EE(-α,z₂)]` -/

/-- For fixed `b`, `q ↦ E⁺(-α)_{b-q} y` has finite support (mirror of
`Eplus_shift_support_finite`). -/
theorem EplusC_shift_support_finite (b : ℤ) (y : B) :
    (Function.support (fun q : ℤ => EplusC (-1) (b - q) y)).Finite := by
  obtain ⟨B0, hB0⟩ := EplusC_isField (-1) y
  apply Set.Finite.subset (Set.finite_Icc b (b - B0))
  intro q hq
  rw [Function.mem_support] at hq
  rw [Set.mem_Icc]
  constructor
  · by_contra h
    exact hq (by rw [EplusC_pos (-1) (show 0 < b - q by omega), LinearMap.zero_apply])
  · by_contra h
    exact hq (hB0 (b - q) (by omega))

/-- The `EEC (-1)`-defining marginal `q ↦ E⁻(-α)_q E⁺(-α)_{s-q} x` has finite support
(mirror of `EE_marg_support_finite`). -/
theorem EEC_marg_support_finite (s : ℤ) (x : B) :
    (Function.support (fun q : ℤ => EminusC (-1) q (EplusC (-1) (s - q) x))).Finite := by
  apply Set.Finite.subset (EplusC_shift_support_finite s x)
  intro q hq
  rw [Function.mem_support] at hq ⊢
  intro h; exact hq (by rw [h, map_zero])

/-- **The charge-`(-1)` boson-current/dressing commutator** `[α(z₁), EE(-α,z₂)]` (mirror of
`alphaField_comm_EE`): the `z₁ʲz₂ᵗ`-coefficient is `(-2)·EE(-α)_{t+j+1}` except at `j = -1`. -/
theorem alphaField_comm_EEC (j t : ℤ) :
    bracketDist alphaField (EEC (-1)) j t
      = if j = -1 then 0 else ((2 * (-1) : ℂ)) • EEC (-1) (t + j + 1) := by
  refine LinearMap.ext fun x => ?_
  have hsupp1 : (Function.support
      (fun m : ℤ => alphaField j (EminusC (-1) m (EplusC (-1) (t - m) x)))).Finite := by
    apply Set.Finite.subset (EEC_marg_support_finite t x)
    intro m hm; rw [Function.mem_support] at hm ⊢
    intro h; exact hm (by rw [h, map_zero])
  have hsupp2 : (Function.support
      (fun m : ℤ => EminusC (-1) m (EplusC (-1) (t - m) (alphaField j x)))).Finite :=
    EEC_marg_support_finite t (alphaField j x)
  rw [bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    show EEC (-1) t ((alphaField j) x)
        = ∑ᶠ m : ℤ, EminusC (-1) m (EplusC (-1) (t - m) (alphaField j x)) from
      EEC_apply_conv (-1) t (alphaField j x),
    show (alphaField j) (EEC (-1) t x)
        = ∑ᶠ m : ℤ, alphaField j (EminusC (-1) m (EplusC (-1) (t - m) x)) from by
      rw [EEC_apply_conv (-1) t x, map_finsum (alphaField j) (EEC_marg_support_finite t x)],
    ← finsum_sub_distrib hsupp1 hsupp2,
    show (∑ᶠ m : ℤ, (alphaField j (EminusC (-1) m (EplusC (-1) (t - m) x))
            - EminusC (-1) m (EplusC (-1) (t - m) (alphaField j x))))
          = ∑ᶠ m : ℤ, ((bracketDist alphaField (EminusC (-1)) j m) (EplusC (-1) (t - m) x)
              + EminusC (-1) m ((bracketDist alphaField (EplusC (-1)) j (t - m)) x)) from
        finsum_congr fun m => by
          rw [bracketDist_apply, bracketDist_apply]
          exact leibniz_vec (alphaField j) (EminusC (-1) m) (EplusC (-1) (t - m)) x]
  simp only [alphaField_comm_EminusC, alphaField_comm_EplusC]
  rcases (show j ≤ -2 ∨ j = -1 ∨ 0 ≤ j from by omega) with hj | hj | hj
  · -- j ≤ -2 : the E⁺ commutator drops; reindex m ↦ m + (j+1)
    rw [if_neg (by omega : ¬ j = -1),
      show (∑ᶠ m : ℤ, ((if j ≤ -2 then ((2 * (-1) : ℂ)) • EminusC (-1) (m + j + 1) else 0)
                (EplusC (-1) (t - m) x)
              + EminusC (-1) m ((if 0 ≤ j then ((2 * (-1) : ℂ)) • EplusC (-1) (t - m + j + 1)
                else 0) x)))
          = ∑ᶠ m : ℤ, ((2 * (-1) : ℂ)) • EminusC (-1) (m + j + 1) (EplusC (-1) (t - m) x) from
        finsum_congr fun m => by
          rw [if_pos hj, if_neg (by omega : ¬ 0 ≤ j), LinearMap.smul_apply,
            LinearMap.zero_apply, map_zero, add_zero],
      show (((2 * (-1) : ℂ)) • EEC (-1) (t + j + 1)) x
          = ((2 * (-1) : ℂ)) • EEC (-1) (t + j + 1) x from rfl,
      EEC_apply_conv (-1) (t + j + 1) x, smul_finsum' ((2 * (-1) : ℂ))
        (EEC_marg_support_finite (t + j + 1) x),
      ← finsum_comp_equiv (Equiv.addRight (j + 1))
        (f := fun m : ℤ => ((2 * (-1) : ℂ)) • EminusC (-1) m (EplusC (-1) (t + j + 1 - m) x))]
    refine finsum_congr fun m => ?_
    simp only [Equiv.coe_addRight]
    rw [show m + (j + 1) = m + j + 1 from by ring,
      show t + j + 1 - (m + j + 1) = t - m from by ring]
  · -- j = -1 : both commutators drop
    subst hj
    rw [if_pos rfl]
    refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
    rw [if_neg (by omega : ¬ (-1 : ℤ) ≤ -2), if_neg (by omega : ¬ (0 : ℤ) ≤ -1)]
    simp
  · -- 0 ≤ j : the E⁻ commutator drops; already in EE form
    rw [if_neg (by omega : ¬ j = -1),
      show (∑ᶠ m : ℤ, ((if j ≤ -2 then ((2 * (-1) : ℂ)) • EminusC (-1) (m + j + 1) else 0)
                (EplusC (-1) (t - m) x)
              + EminusC (-1) m ((if 0 ≤ j then ((2 * (-1) : ℂ)) • EplusC (-1) (t - m + j + 1)
                else 0) x)))
          = ∑ᶠ m : ℤ, ((2 * (-1) : ℂ)) • EminusC (-1) m (EplusC (-1) (t + j + 1 - m) x) from
        finsum_congr fun m => by
          rw [if_neg (by omega : ¬ j ≤ -2), if_pos hj, LinearMap.zero_apply, zero_add,
            LinearMap.smul_apply, map_smul, show t - m + j + 1 = t + j + 1 - m from by ring],
      show (((2 * (-1) : ℂ)) • EEC (-1) (t + j + 1)) x
          = ((2 * (-1) : ℂ)) • EEC (-1) (t + j + 1) x from rfl,
      EEC_apply_conv (-1) (t + j + 1) x, smul_finsum' ((2 * (-1) : ℂ))
        (EEC_marg_support_finite (t + j + 1) x)]

/-! ## §14b  The Heisenberg–lattice commutator `[α(z₁), Y(e^{-α},z₂)]` -/

/-- **The charge-`(-1)` Heisenberg–lattice commutator** `[α(z₁), Y(e^{-α},z₂)] = (-2)·Y(e^{-α},z₂)`
on a basis state (mirror of `alphaLat_comm_Yeα_tmul`): the `α₀` zero-mode supplies the charge defect
`2·(n-1) - 2·n = -2` between the sectors `n` and `n-1`. -/
theorem alphaLat_comm_Yemα_neg1_tmul (j t : ℤ) (p : B) (n : ℤ) :
    bracketDist alphaLat (Yemα (-1)) j t (p ⊗ₜ[ℂ] eVec n)
      = ((2 * (-1) : ℂ)) • Yemα (-1) (t + j + 1) (p ⊗ₜ[ℂ] eVec n) := by
  rw [bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    Yemα_tmul, alphaLat_tmul, alphaLat_tmul]
  by_cases hj : j = -1
  · -- j = -1 : boson commutator vanishes; the `α₀` grading supplies the `(-2)·Y` charge
    subst hj
    rw [if_pos rfl, if_pos rfl, map_add, map_smul, Yemα_tmul, Yemα_tmul, Yemα_tmul]
    simp only [Int.cast_neg, Int.cast_one]
    have hbz : alphaField (-1) (EEC (-1) (t - 2 * (-1) * n) p)
        = EEC (-1) (t - 2 * (-1) * n) (alphaField (-1) p) := by
      have h0 := alphaField_comm_EEC (-1) (t - 2 * (-1) * n)
      rw [if_pos rfl] at h0
      have hp := LinearMap.congr_fun h0 p
      rw [bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
        LinearMap.zero_apply] at hp
      exact sub_eq_zero.mp hp
    rw [hbz,
      show ((2 * (n + -1) : ℤ) : ℂ) = ((2 * n : ℤ) : ℂ) + ((2 * (-1) : ℂ)) from by push_cast; ring,
      add_smul, show (t + -1 + 1 - 2 * (-1) * n) = (t - 2 * (-1) * n) from by ring]
    abel
  · -- j ≠ -1 : boson commutator `(-2)·EE_{t+j+1}` carries the charge; grading absent
    rw [if_neg hj, if_neg hj, add_zero, add_zero, Yemα_tmul, Yemα_tmul,
      ← TensorProduct.sub_tmul]
    simp only [Int.cast_neg, Int.cast_one]
    have hbe : alphaField j (EEC (-1) (t - 2 * (-1) * n) p)
          - EEC (-1) (t - 2 * (-1) * n) (alphaField j p)
        = ((2 * (-1) : ℂ)) • EEC (-1) (t - 2 * (-1) * n + j + 1) p := by
      have h0 := alphaField_comm_EEC j (t - 2 * (-1) * n)
      rw [if_neg hj] at h0
      have hp := LinearMap.congr_fun h0 p
      rw [bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
        LinearMap.smul_apply] at hp
      exact hp
    rw [hbe, TensorProduct.smul_tmul',
      show (t - 2 * (-1) * n + j + 1) = (t + j + 1 - 2 * (-1) * n) from by ring]

/-- **Operator lift**: `bracketDist αLat (Yemα (-1)) j t = (-2)·Yemα(-1)_{t+j+1}` on all of
`LatModule` (mirror of `alphaLat_comm_Yeα`). -/
theorem alphaLat_comm_Yemα_neg1 (j t : ℤ) :
    bracketDist alphaLat (Yemα (-1)) j t = ((2 * (-1) : ℂ)) • Yemα (-1) (t + j + 1) := by
  refine LinearMap.ext fun y => ?_
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add y1 y2 h1 h2 => rw [map_add, map_add, h1, h2]
  | tmul p g =>
      induction g using Finsupp.induction_linear with
      | zero => erw [TensorProduct.tmul_zero, map_zero, map_zero]
      | add g1 g2 h1 h2 => erw [TensorProduct.tmul_add, map_add, map_add, h1, h2]
      | single n a =>
          rw [show (Finsupp.single n a : LatGrp) = a • eVec n from
            (Finsupp.smul_single_one n a).symm]
          erw [TensorProduct.tmul_smul, map_smul, map_smul, alphaLat_comm_Yemα_neg1_tmul,
            LinearMap.smul_apply]

/-! ## §15  The charge-`(-1)` Heisenberg–lattice mutual locality -/

/-- **The charge-`(-1)` Heisenberg–lattice mutual locality** `Local αLat Y(e^{-α},z)` with bound
`N = 1` (mirror of `latticeHL_local`): the commutator `(-2)·Yemα(-1)_{t+j+1}` telescopes to `0`
under `mulBySub`, `pbw`-free. -/
theorem latticeHL_neg1_local : Local alphaLat (Yemα (-1)) := by
  refine ⟨1, ?_⟩
  rw [mulBySubPow_one]
  funext m n
  rw [mulBySub_apply, alphaLat_comm_Yemα_neg1, alphaLat_comm_Yemα_neg1,
    show n + (m - 1) + 1 = (n - 1) + m + 1 from by ring, sub_self]
  rfl

end LatExp
end VOA
