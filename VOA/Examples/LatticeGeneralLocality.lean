/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeWordFields
import VOA.Examples.LatticeCrossLocality

/-!
# General-charge mutual locality of the lattice `A₁` vertex operators

The last hard crux of the operator-first lattice VOA reconstruction: the general-charge mutual
locality

* `genFieldLat_local_Yemα i m : Local (genFieldLat i) (Yemα m)` — the boson generator field is
  mutually local with every charge-`m` lattice vertex operator (bound `1`, lifted by
  `deriv_iterate_left`).

This generalizes `LatExp.latticeHL_neg1_local` (charge `-1`, boson factor `-2`) to an arbitrary
charge `m` (boson factor `2m`).  All `sorry`/`admit`/`axiom`/`pbw`-free.
-/

namespace VOA
namespace LatExp

open scoped BigOperators TensorProduct
open Module (End)
open HeisenbergN (oscN vacuumN)
open LatticeVOA (LatModule LatGrp eVec latState latVacuum zGradeOp)

/-! ## §1  The charge-`c` boson-current contractions (boson factor `2c`) -/

/-- **The charge-`c` creation-mode `E⁺` contraction** `[α₋ₖ, aExpCZ c_M] = 2c·aExpCZ c_{M-k}`:
the charge-`c` transcription of `alphaNeg_comp_aExpCZ` (charge `-1`).  Keeps the `c•` reassembly
form so it works at `c = 0` too. -/
theorem alphaNeg_comp_aExpCZc (c : ℂ) (k : ℕ) (hk : 1 ≤ k) :
    ∀ M : ℤ, (α (-(k : ℤ))).comp (aExpCZ c M)
      = (aExpCZ c M).comp (α (-(k : ℤ))) + ((2 * c : ℂ)) • aExpCZ c (M - k) := by
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
      (α (-(k : ℤ))).comp (aExpCZ c M)
        = (aExpCZ c M).comp (α (-(k : ℤ))) + ((2 * c : ℂ)) • aExpCZ c (M - k) by
    exact fun M => H M.toNat M le_rfl
  intro n
  induction n with
  | zero =>
    intro M hM
    by_cases h0 : M = 0
    · subst h0
      rw [aExpCZ_zero, LinearMap.comp_id, LinearMap.id_comp,
        aExpCZ_neg c (show (0 : ℤ) - k < 0 by omega), smul_zero, add_zero]
    · rw [aExpCZ_neg c (by omega : M < 0), aExpCZ_neg c (show M - k < 0 by omega),
        LinearMap.comp_zero, LinearMap.zero_comp, smul_zero, add_zero]
  | succ n ih =>
    intro M hM
    by_cases hsmall : M.toNat ≤ n
    · exact ih M hsmall
    · have hM1 : 1 ≤ M := by omega
      have hMne : (M : ℂ) ≠ 0 := by simp only [ne_eq, Int.cast_eq_zero]; omega
      conv_lhs => rw [aExpCZ_recursion c M hM1]
      rw [LinearMap.comp_smul, LinearMap.comp_smul, comp_sum']
      have hterm : ∀ m ∈ Finset.range M.toNat,
          (α (-(k : ℤ))).comp ((-(α ((m : ℤ) + 1))).comp (aExpCZ c (M - 1 - m)))
            = (-(α ((m : ℤ) + 1))).comp ((aExpCZ c (M - 1 - m)).comp (α (-(k : ℤ))))
              + ((2 * c : ℂ)) • (-(α ((m : ℤ) + 1))).comp (aExpCZ c ((M - k) - 1 - m))
              + (if (m : ℤ) + 1 = (k : ℤ) then ((2 * k : ℕ) : ℂ) else 0)
                  • aExpCZ c (M - 1 - m) := by
        intro m _
        rw [← LinearMap.comp_assoc, hmove m, LinearMap.add_comp, LinearMap.comp_assoc,
          ih (M - 1 - m) (by omega)]
        simp only [LinearMap.comp_add, LinearMap.comp_smul, LinearMap.smul_comp,
          LinearMap.id_comp]
        rw [show M - 1 - (m : ℤ) - k = (M - k) - 1 - m from by ring]
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
        smul_add, smul_add, smul_add]
      -- Column 1: reassemble the moved-α sum (with c• prefactor) into M • (aExpCZ M ∘ α₋ₖ).
      have hcol1 : c • (∑ m ∈ Finset.range M.toNat,
            (-(α ((m : ℤ) + 1))).comp ((aExpCZ c (M - 1 - m)).comp (α (-(k : ℤ)))))
          = (M : ℂ) • ((aExpCZ c M).comp (α (-(k : ℤ)))) := by
        simp only [← LinearMap.comp_assoc, ← sum_comp', ← LinearMap.smul_comp]
        rw [aExpCZ_sum_reassembly c M M.toNat le_rfl]
      have hcol2 : c • (∑ m ∈ Finset.range M.toNat,
            ((2 * c : ℂ)) • (-(α ((m : ℤ) + 1))).comp (aExpCZ c ((M - k) - 1 - m)))
          = ((2 * c : ℂ)) • (((M - k : ℤ) : ℂ) • aExpCZ c (M - k)) := by
        rw [Finset.smul_sum]
        simp only [smul_comm c (2 * c : ℂ)]
        rw [← Finset.smul_sum, ← Finset.smul_sum,
          aExpCZ_sum_reassembly c (M - k) M.toNat (by omega)]
      have hcol3 : c • (∑ m ∈ Finset.range M.toNat,
            (if (m : ℤ) + 1 = (k : ℤ) then ((2 * k : ℕ) : ℂ) else 0) • aExpCZ c (M - 1 - m))
          = c • (((2 * k : ℕ) : ℂ) • aExpCZ c (M - k)) := by
        congr 1
        by_cases hkM : k ≤ M.toNat
        · rw [Finset.sum_eq_single (k - 1)]
          · rw [if_pos (by omega), show M - 1 - ((k : ℕ) - 1 : ℕ) = M - k from by
                rw [show ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 from by omega]; ring]
          · intro b _ hb; rw [if_neg (by omega), zero_smul]
          · intro hmem; exact absurd (Finset.mem_range.mpr (by omega)) hmem
        · rw [aExpCZ_neg c (show M - k < 0 by omega), smul_zero]
          refine Finset.sum_eq_zero fun m hm => ?_
          simp only [Finset.mem_range] at hm
          rw [if_neg (by omega), zero_smul]
      rw [hcol1, hcol2, hcol3]
      rw [show ((aExpCZ c M).comp (α (-(k : ℤ))) + ((2 * c : ℂ)) • aExpCZ c (M - k))
            = (M : ℂ)⁻¹ • ((M : ℂ) • ((aExpCZ c M).comp (α (-(k : ℤ)))
                + ((2 * c : ℂ)) • aExpCZ c (M - k))) from by
          rw [smul_smul, inv_mul_cancel₀ hMne, one_smul]]
      rw [smul_add, smul_smul, smul_smul]
      push_cast
      module

/-! ## §7  The field-level boson OPE `[α(z₁), E⁻(cα,z₂)]` (boson factor `2c`) -/

/-- The charge-`c` annihilation-mode field contraction:
for `m ≥ 1`, `αₘ ∘ E⁻(cα)_t = E⁻(cα)_t ∘ αₘ + 2c·E⁻(cα)_{t-m}`. -/
theorem alpha_comp_EminusCc_pos (c : ℂ) {m : ℕ} (hm : 1 ≤ m) (t : ℤ) :
    (α (m : ℤ)).comp (EminusC c t)
      = (EminusC c t).comp (α (m : ℤ)) + ((2 * c : ℂ)) • EminusC c (t - m) := by
  by_cases ht : 0 ≤ t
  · set N := t.toNat with hN
    have htN : (t : ℤ) = (N : ℤ) := (Int.toNat_of_nonneg ht).symm
    rw [EminusC_nonneg c ht, alpha_comp_EminusOpC c m N hm]
    congr 1
    by_cases hmN : m ≤ N
    · rw [if_pos hmN]
      have : t - m = ((N - m : ℕ) : ℤ) := by rw [htN, Nat.cast_sub hmN]
      rw [EminusC_nonneg c (by omega), this, Int.toNat_natCast]
    · rw [if_neg hmN, EminusC_neg c (by omega), smul_zero]
  · rw [EminusC_neg c (by omega), EminusC_neg c (by omega)]
    simp

/-- The charge-`c` creation-mode commutation: for `m < 0`, `αₘ ∘ E⁻(cα)_t = E⁻(cα)_t ∘ αₘ`. -/
theorem alpha_comp_EminusCc_neg (c : ℂ) {m : ℤ} (hm : m < 0) (t : ℤ) :
    (α m).comp (EminusC c t) = (EminusC c t).comp (α m) := by
  refine LinearMap.ext fun q => ?_
  rw [EminusC_apply]
  split_ifs with ht
  · simp only [LinearMap.comp_apply, α, EminusOpC, LinearMap.mulLeft_apply,
      HeisenbergN.oscN_apply_neg 1 2 0 hm]
    ring
  · simp

/-- **The field-level boson OPE `[α(z₁), E⁻(cα,z₂)]`**: the `z₁ʲz₂ᵗ`-coefficient is
`2c·E⁻(cα)_{t+j+1}` for `j ≤ -2` and `0` otherwise. -/
theorem alphaField_comm_EminusCc (c : ℂ) (j t : ℤ) :
    bracketDist alphaField (EminusC c) j t
      = if j ≤ -2 then ((2 * c : ℂ)) • EminusC c (t + j + 1) else 0 := by
  rw [bracketDist_apply, alphaField_apply]
  change (α (-j - 1)).comp (EminusC c t) - (EminusC c t).comp (α (-j - 1)) = _
  by_cases hj : j ≤ -2
  · rw [if_pos hj]
    have hmval : ((-j - 1).toNat : ℤ) = -j - 1 := Int.toNat_of_nonneg (by omega)
    have hm1 : 1 ≤ (-j - 1).toNat := by omega
    have hc := alpha_comp_EminusCc_pos c hm1 t
    rw [show (-j - 1 : ℤ) = (((-j - 1).toNat : ℤ)) from hmval.symm, hc,
      show t - ((-j - 1).toNat : ℤ) = t + j + 1 from by rw [hmval]; ring]
    abel
  · rw [if_neg hj]
    rcases (show -j - 1 < 0 ∨ -j - 1 = 0 from by omega) with hlt | heq
    · rw [alpha_comp_EminusCc_neg c hlt t, sub_self]
    · rw [heq]
      change (oscN 1 2 0 0).comp (EminusC c t) - (EminusC c t).comp (oscN 1 2 0 0) = 0
      rw [HeisenbergN.oscN_zero, LinearMap.zero_comp, LinearMap.comp_zero, sub_zero]

/-! ## §13  The field-level boson OPE `[α(z₁), E⁺(cα,z₂)]` (boson factor `2c`) -/

/-- `E⁺(cα) = aExpCZ c` commutes with positive boson modes. -/
theorem aExpCZc_commute_alphaPos (c : ℂ) (M : ℤ) {p : ℤ} (hp : 1 ≤ p) :
    Commute (aExpCZ c M) (α p) := by
  by_cases hM : 0 ≤ M
  · rw [aExpCZ_nonneg c hM]
    have h := aExpC_commute_alpha c M.toNat (p - 1).toNat
    rwa [show ((p - 1).toNat : ℤ) + 1 = p from by omega] at h
  · rw [aExpCZ_neg c (by omega)]; exact Commute.zero_left _

/-- **The field-level boson OPE `[α(z₁), E⁺(cα,z₂)]`**: the `z₁ʲz₂ᵗ`-coefficient is
`2c·E⁺(cα)_{t+j+1}` for `j ≥ 0` and `0` otherwise. -/
theorem alphaField_comm_EplusCc (c : ℂ) (j t : ℤ) :
    bracketDist alphaField (EplusC c) j t
      = if 0 ≤ j then ((2 * c : ℂ)) • EplusC c (t + j + 1) else 0 := by
  rw [bracketDist_apply, alphaField_apply]
  change (α (-j - 1)).comp (EplusC c t) - (EplusC c t).comp (α (-j - 1)) = _
  by_cases hj : 0 ≤ j
  · rw [if_pos hj, show -j - 1 = -((j + 1).toNat : ℤ) from by omega, EplusC_eq_aExpCZ c t,
      EplusC_eq_aExpCZ c (t + j + 1), alphaNeg_comp_aExpCZc c (j + 1).toNat (by omega) (-t),
      show -t - ((j + 1).toNat : ℤ) = -(t + j + 1) from by omega]
    abel
  · rw [if_neg hj]
    rcases (show -j - 1 = 0 ∨ 1 ≤ -j - 1 from by omega) with h0 | h1
    · rw [h0, show α (0 : ℤ) = (0 : End ℂ B) from HeisenbergN.oscN_zero 1 2 0,
        LinearMap.zero_comp, LinearMap.comp_zero, sub_zero]
    · rw [EplusC_eq_aExpCZ c t,
        show (α (-j - 1)).comp (aExpCZ c (-t)) = (aExpCZ c (-t)).comp (α (-j - 1)) from
          (aExpCZc_commute_alphaPos c (-t) h1).eq.symm, sub_self]

/-! ## §14a  The boson-current/dressing commutator `[α(z₁), EE(cα,z₂)]` -/

/-- For fixed `b`, `q ↦ E⁺(cα)_{b-q} y` has finite support. -/
theorem EplusCc_shift_support_finite (c : ℂ) (b : ℤ) (y : B) :
    (Function.support (fun q : ℤ => EplusC c (b - q) y)).Finite := by
  obtain ⟨B0, hB0⟩ := EplusC_isField c y
  apply Set.Finite.subset (Set.finite_Icc b (b - B0))
  intro q hq
  rw [Function.mem_support] at hq
  rw [Set.mem_Icc]
  constructor
  · by_contra h
    exact hq (by rw [EplusC_pos c (show 0 < b - q by omega), LinearMap.zero_apply])
  · by_contra h
    exact hq (hB0 (b - q) (by omega))

/-- The `EEC c`-defining marginal `q ↦ E⁻(cα)_q E⁺(cα)_{s-q} x` has finite support. -/
theorem EECc_marg_support_finite (c : ℂ) (s : ℤ) (x : B) :
    (Function.support (fun q : ℤ => EminusC c q (EplusC c (s - q) x))).Finite := by
  apply Set.Finite.subset (EplusCc_shift_support_finite c s x)
  intro q hq
  rw [Function.mem_support] at hq ⊢
  intro h; exact hq (by rw [h, map_zero])

/-- **The charge-`c` boson-current/dressing commutator** `[α(z₁), EE(cα,z₂)]`: the
`z₁ʲz₂ᵗ`-coefficient is `2c·EE(cα)_{t+j+1}` except at `j = -1`. -/
theorem alphaField_comm_EECc (c : ℂ) (j t : ℤ) :
    bracketDist alphaField (EEC c) j t
      = if j = -1 then 0 else ((2 * c : ℂ)) • EEC c (t + j + 1) := by
  refine LinearMap.ext fun x => ?_
  have hsupp1 : (Function.support
      (fun m : ℤ => alphaField j (EminusC c m (EplusC c (t - m) x)))).Finite := by
    apply Set.Finite.subset (EECc_marg_support_finite c t x)
    intro m hm; rw [Function.mem_support] at hm ⊢
    intro h; exact hm (by rw [h, map_zero])
  have hsupp2 : (Function.support
      (fun m : ℤ => EminusC c m (EplusC c (t - m) (alphaField j x)))).Finite :=
    EECc_marg_support_finite c t (alphaField j x)
  rw [bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    show EEC c t ((alphaField j) x)
        = ∑ᶠ m : ℤ, EminusC c m (EplusC c (t - m) (alphaField j x)) from
      EEC_apply_conv c t (alphaField j x),
    show (alphaField j) (EEC c t x)
        = ∑ᶠ m : ℤ, alphaField j (EminusC c m (EplusC c (t - m) x)) from by
      rw [EEC_apply_conv c t x, map_finsum (alphaField j) (EECc_marg_support_finite c t x)],
    ← finsum_sub_distrib hsupp1 hsupp2,
    show (∑ᶠ m : ℤ, (alphaField j (EminusC c m (EplusC c (t - m) x))
            - EminusC c m (EplusC c (t - m) (alphaField j x))))
          = ∑ᶠ m : ℤ, ((bracketDist alphaField (EminusC c) j m) (EplusC c (t - m) x)
              + EminusC c m ((bracketDist alphaField (EplusC c) j (t - m)) x)) from
        finsum_congr fun m => by
          rw [bracketDist_apply, bracketDist_apply]
          exact leibniz_vec (alphaField j) (EminusC c m) (EplusC c (t - m)) x]
  simp only [alphaField_comm_EminusCc, alphaField_comm_EplusCc]
  rcases (show j ≤ -2 ∨ j = -1 ∨ 0 ≤ j from by omega) with hj | hj | hj
  · rw [if_neg (by omega : ¬ j = -1),
      show (∑ᶠ m : ℤ, ((if j ≤ -2 then ((2 * c : ℂ)) • EminusC c (m + j + 1) else 0)
                (EplusC c (t - m) x)
              + EminusC c m ((if 0 ≤ j then ((2 * c : ℂ)) • EplusC c (t - m + j + 1)
                else 0) x)))
          = ∑ᶠ m : ℤ, ((2 * c : ℂ)) • EminusC c (m + j + 1) (EplusC c (t - m) x) from
        finsum_congr fun m => by
          rw [if_pos hj, if_neg (by omega : ¬ 0 ≤ j), LinearMap.smul_apply,
            LinearMap.zero_apply, map_zero, add_zero],
      show (((2 * c : ℂ)) • EEC c (t + j + 1)) x
          = ((2 * c : ℂ)) • EEC c (t + j + 1) x from rfl,
      EEC_apply_conv c (t + j + 1) x, smul_finsum' ((2 * c : ℂ))
        (EECc_marg_support_finite c (t + j + 1) x),
      ← finsum_comp_equiv (Equiv.addRight (j + 1))
        (f := fun m : ℤ => ((2 * c : ℂ)) • EminusC c m (EplusC c (t + j + 1 - m) x))]
    refine finsum_congr fun m => ?_
    simp only [Equiv.coe_addRight]
    rw [show m + (j + 1) = m + j + 1 from by ring,
      show t + j + 1 - (m + j + 1) = t - m from by ring]
  · subst hj
    rw [if_pos rfl]
    refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
    rw [if_neg (by omega : ¬ (-1 : ℤ) ≤ -2), if_neg (by omega : ¬ (0 : ℤ) ≤ -1)]
    simp
  · rw [if_neg (by omega : ¬ j = -1),
      show (∑ᶠ m : ℤ, ((if j ≤ -2 then ((2 * c : ℂ)) • EminusC c (m + j + 1) else 0)
                (EplusC c (t - m) x)
              + EminusC c m ((if 0 ≤ j then ((2 * c : ℂ)) • EplusC c (t - m + j + 1)
                else 0) x)))
          = ∑ᶠ m : ℤ, ((2 * c : ℂ)) • EminusC c m (EplusC c (t + j + 1 - m) x) from
        finsum_congr fun m => by
          rw [if_neg (by omega : ¬ j ≤ -2), if_pos hj, LinearMap.zero_apply, zero_add,
            LinearMap.smul_apply, map_smul, show t - m + j + 1 = t + j + 1 - m from by ring],
      show (((2 * c : ℂ)) • EEC c (t + j + 1)) x
          = ((2 * c : ℂ)) • EEC c (t + j + 1) x from rfl,
      EEC_apply_conv c (t + j + 1) x, smul_finsum' ((2 * c : ℂ))
        (EECc_marg_support_finite c (t + j + 1) x)]

/-! ## §14b  The Heisenberg–lattice commutator `[α(z₁), Y(e^{mα},z₂)]` (factor `2m`) -/

/-- **The charge-`m` Heisenberg–lattice commutator** `[α(z₁), Y(e^{mα},z₂)] = 2m·Y(e^{mα},z₂)`
on a basis state.  At `j = -1` the boson commutator vanishes and the `α₀` zero-mode grading
supplies the `2m·Y` charge (the sector defect `2n - 2(n+m)` cancels against `2(n+m)` to leave
`2m`); at `j ≠ -1` the boson commutator `2m·EE_{t+j+1}` carries it.  Via `alphaField_comm_EECc`. -/
theorem alphaLat_comm_Yemα_tmul (m j t : ℤ) (p : B) (n : ℤ) :
    bracketDist alphaLat (Yemα m) j t (p ⊗ₜ[ℂ] eVec n)
      = ((2 * m : ℂ)) • Yemα m (t + j + 1) (p ⊗ₜ[ℂ] eVec n) := by
  rw [bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    Yemα_tmul, alphaLat_tmul, alphaLat_tmul]
  by_cases hj : j = -1
  · -- j = -1 : boson commutator vanishes; the `α₀` grading supplies the `2m·Y` charge
    subst hj
    rw [if_pos rfl, if_pos rfl, map_add, map_smul, Yemα_tmul, Yemα_tmul, Yemα_tmul]
    have hbz : alphaField (-1) (EEC (m : ℂ) (t - 2 * m * n) p)
        = EEC (m : ℂ) (t - 2 * m * n) (alphaField (-1) p) := by
      have h0 := alphaField_comm_EECc (m : ℂ) (-1) (t - 2 * m * n)
      rw [if_pos rfl] at h0
      have hp := LinearMap.congr_fun h0 p
      rw [bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
        LinearMap.zero_apply] at hp
      exact sub_eq_zero.mp hp
    rw [hbz,
      show ((2 * (n + m) : ℤ) : ℂ) = ((2 * n : ℤ) : ℂ) + ((2 * m : ℂ)) from by push_cast; ring,
      add_smul, show (t + -1 + 1 - 2 * m * n) = (t - 2 * m * n) from by ring]
    abel
  · -- j ≠ -1 : boson commutator `2m·EE_{t+j+1}` carries the charge; grading absent
    rw [if_neg hj, if_neg hj, add_zero, add_zero, Yemα_tmul, Yemα_tmul,
      ← TensorProduct.sub_tmul]
    have hbe : alphaField j (EEC (m : ℂ) (t - 2 * m * n) p)
          - EEC (m : ℂ) (t - 2 * m * n) (alphaField j p)
        = ((2 * m : ℂ)) • EEC (m : ℂ) (t - 2 * m * n + j + 1) p := by
      have h0 := alphaField_comm_EECc (m : ℂ) j (t - 2 * m * n)
      rw [if_neg hj] at h0
      have hp := LinearMap.congr_fun h0 p
      rw [bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
        LinearMap.smul_apply] at hp
      exact hp
    rw [hbe, TensorProduct.smul_tmul',
      show (t - 2 * m * n + j + 1) = (t + j + 1 - 2 * m * n) from by ring]

/-- **Operator lift**: `bracketDist αLat (Yemα m) j t = 2m·Yemα m_{t+j+1}` on all of `LatModule`. -/
theorem alphaLat_comm_Yemα (m j t : ℤ) :
    bracketDist alphaLat (Yemα m) j t = ((2 * m : ℂ)) • Yemα m (t + j + 1) := by
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
          erw [TensorProduct.tmul_smul, map_smul, map_smul, alphaLat_comm_Yemα_tmul,
            LinearMap.smul_apply]

/-! ## §15  The general-charge Heisenberg–lattice mutual locality -/

/-- **The general-charge Heisenberg–lattice mutual locality** `Local αLat Y(e^{mα},z)` with bound
`N = 1`: the commutator `2m·Yemα m_{t+j+1}` telescopes to `0` under `mulBySub`, `pbw`-free. -/
theorem alphaLat_Yemα_local (m : ℤ) : Local alphaLat (Yemα m) := by
  refine ⟨1, ?_⟩
  rw [mulBySubPow_one]
  funext s t
  rw [mulBySub_apply, alphaLat_comm_Yemα, alphaLat_comm_Yemα,
    show t + (s - 1) + 1 = (t - 1) + s + 1 from by ring, sub_self]
  rfl

/-- **Boson-generator/charge locality** `Local (genFieldLat i) (Yemα m)` for every `i` and `m`:
lift `alphaLat_Yemα_local` along `deriv_iterate_left i` and the `(i!)⁻¹` scalar (mirror of
`genFieldLat_local`).  `sorry`/`pbw`-free. -/
theorem genFieldLat_local_Yemα (i : ℕ) (m : ℤ) : Local (genFieldLat i) (Yemα m) := by
  change Local ((i.factorial : ℂ)⁻¹ • (VOA.deriv^[i] alphaLat)) (Yemα m)
  exact VertexOperatorAlgebra.Local.smul' _ ((alphaLat_Yemα_local m).deriv_iterate_left i)

/-! ## §16  The reverse cross-charge locality `Local (Yemα (-1)) (Yemα 1)`

The mirror of `Yemα_cross_local : Local (Yemα 1) (Yemα (-1))` under `Local.symm`.  Together with
the diagonal localities `Yemα_one_local`, `Yemα_negOne_local` and the cross `Yemα_cross_local`,
this completes the four pairwise mutual-localities of the charge-`±1` generators (the boson
generator `genFieldLat i` localities being supplied by `genFieldLat_local_Yemα`). -/

/-- **The reverse cross-charge mutual locality** `Local (Yemα (-1)) (Yemα 1)` (cross pairing
`⟨-α,α⟩ = -2`, bound `N = 2`), the `Local.symm` of `Yemα_cross_local`.  `sorry`/`pbw`-free. -/
theorem Yemα_negOne_one_local : Local (Yemα (-1)) (Yemα 1) :=
  Yemα_cross_local.symm

end LatExp
end VOA
