/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeChargeMContraction
import VOA.Examples.LatticeEnergyMomentum


/-!
# The lattice "momentum" charge-shift of the exponential dressing — crux A, half (*)

For the reconstruction translation `Trec = rTensor(L₋₁) + ½·rTensor(α₋₁)·zGradeOp`, the covariance
`DCovariant Trec (Yemα m)` reduces (on a basis state `p ⊗ e^{nα}`) to two boson identities on the
Fock factor `B`.  This file proves the first, `(*)`:

* `alphaNeg1_comm_EEC c r : [α₋₁, EEC c r] = (2c)·EEC c (r+1)`

— `α₋₁` commutes through the creation half `EminusC` (both are `mulLeft` of a creation polynomial)
and shifts the annihilation half `EplusC` by `+1` with factor `2c` (via the general-charge
`α₋₁`–`aExpCZ` contraction `alphaNeg1_comp_aExpCZ`).  Summing over the normal-ordered terms gives
the global `z`-index shift.  All `pbw`-free / axiom-clean.
-/

open VOA VOA.LatExp VOA.LatticeVOA
open Module (End)
open scoped TensorProduct BigOperators

namespace VOA.LatExp

/-- **General-charge `α₋₁`–`aExpCZ` contraction** `[α₋₁, aExpCZ c M] = (2c)·aExpCZ c (M-1)`
(the `k=1` case, every charge `c`).  Ported from `alphaNeg_comp_aExpCZ` (charge `-1`). -/
theorem alphaNeg1_comp_aExpCZ (c : ℂ) :
    ∀ M : ℤ, (α (-1)).comp (aExpCZ c M)
      = (aExpCZ c M).comp (α (-1)) + ((2 * c : ℂ)) • aExpCZ c (M - 1) := by
  have hcomm : ∀ m : ℕ, α (-1) * α ((m : ℤ) + 1) - α ((m : ℤ) + 1) * α (-1)
      = (if (m : ℤ) + 1 = (1 : ℤ) then (-(2 : ℂ)) else 0) • LinearMap.id := by
    intro m
    have h := HeisenbergN.oscN_comm 1 2 0 0 (-1 : ℤ) ((m : ℤ) + 1)
    simp only [true_and] at h
    rw [show α (-1) = HeisenbergN.oscN 1 2 0 (-1) from rfl,
      show α ((m : ℤ) + 1) = HeisenbergN.oscN 1 2 0 ((m : ℤ) + 1) from rfl, h]
    by_cases hc1 : (m : ℤ) + 1 = (1 : ℤ)
    · rw [if_pos (show -1 + ((m : ℤ) + 1) = 0 by omega), if_pos hc1]
      congr 1; push_cast; ring
    · rw [if_neg (show ¬ (-1 + ((m : ℤ) + 1) = 0) by omega), if_neg hc1]
  have hmove : ∀ m : ℕ, (α (-1)).comp (-(α ((m : ℤ) + 1)))
      = (-(α ((m : ℤ) + 1))).comp (α (-1))
        + (if (m : ℤ) + 1 = (1 : ℤ) then (2 : ℂ) else 0) • LinearMap.id := by
    intro m
    have hAB : α (-1) * α ((m : ℤ) + 1)
        = α ((m : ℤ) + 1) * α (-1)
          + (if (m : ℤ) + 1 = (1 : ℤ) then (-(2 : ℂ)) else 0) • LinearMap.id :=
      sub_eq_iff_eq_add'.mp (hcomm m)
    rw [LinearMap.comp_neg, LinearMap.neg_comp,
      show (α (-1)).comp (α ((m : ℤ) + 1)) = α (-1) * α ((m : ℤ) + 1) from rfl,
      show (α ((m : ℤ) + 1)).comp (α (-1)) = α ((m : ℤ) + 1) * α (-1) from rfl, hAB]
    by_cases hc1 : (m : ℤ) + 1 = (1 : ℤ)
    · rw [if_pos hc1, if_pos hc1]; module
    · rw [if_neg hc1, if_neg hc1]; simp
  suffices H : ∀ n : ℕ, ∀ M : ℤ, M.toNat ≤ n →
      (α (-1)).comp (aExpCZ c M)
        = (aExpCZ c M).comp (α (-1)) + ((2 * c : ℂ)) • aExpCZ c (M - 1) by
    exact fun M => H M.toNat M le_rfl
  intro n
  induction n with
  | zero =>
    intro M hM
    by_cases h0 : M = 0
    · subst h0
      rw [aExpCZ_zero, LinearMap.comp_id, LinearMap.id_comp,
        aExpCZ_neg c (show (0 : ℤ) - 1 < 0 by omega), smul_zero, add_zero]
    · rw [aExpCZ_neg c (by omega : M < 0), aExpCZ_neg c (show M - 1 < 0 by omega),
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
          (α (-1)).comp ((-(α ((m : ℤ) + 1))).comp (aExpCZ c (M - 1 - m)))
            = (-(α ((m : ℤ) + 1))).comp ((aExpCZ c (M - 1 - m)).comp (α (-1)))
              + ((2 * c : ℂ)) • (-(α ((m : ℤ) + 1))).comp (aExpCZ c ((M - 1) - 1 - m))
              + (if (m : ℤ) + 1 = (1 : ℤ) then (2 : ℂ) else 0)
                  • aExpCZ c (M - 1 - m) := by
        intro m _
        rw [← LinearMap.comp_assoc, hmove m, LinearMap.add_comp, LinearMap.comp_assoc,
          ih (M - 1 - m) (by omega)]
        simp only [LinearMap.comp_add, LinearMap.comp_smul, LinearMap.smul_comp,
          LinearMap.id_comp]
        rw [show M - 1 - (m : ℤ) - 1 = (M - 1) - 1 - m from by ring]
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib]
      rw [inv_smul_eq_iff₀ hMne, smul_add, smul_add]
      -- the three columns, multiplied by `c` (reassembly, no inverse)
      have col1c : c • (∑ m ∈ Finset.range M.toNat,
            (-(α ((m : ℤ) + 1))).comp ((aExpCZ c (M - 1 - m)).comp (α (-1))))
          = (M : ℂ) • ((aExpCZ c M).comp (α (-1))) := by
        rw [show (∑ m ∈ Finset.range M.toNat,
                  (-(α ((m : ℤ) + 1))).comp ((aExpCZ c (M - 1 - m)).comp (α (-1))))
                = (∑ m ∈ Finset.range M.toNat,
                  (-(α ((m : ℤ) + 1))).comp (aExpCZ c (M - 1 - m))).comp (α (-1)) from by
            simp only [← LinearMap.comp_assoc]; rw [← sum_comp'],
          ← LinearMap.smul_comp, aExpCZ_sum_reassembly c M M.toNat le_rfl, LinearMap.smul_comp]
      have col2c : c • (∑ m ∈ Finset.range M.toNat,
            ((2 * c : ℂ)) • (-(α ((m : ℤ) + 1))).comp (aExpCZ c ((M - 1) - 1 - m)))
          = ((2 * c : ℂ)) • (((M - 1 : ℤ) : ℂ) • aExpCZ c (M - 1)) := by
        rw [← Finset.smul_sum, smul_comm c (2 * c : ℂ),
          aExpCZ_sum_reassembly c (M - 1) M.toNat (by omega)]
      have col3c : c • (∑ m ∈ Finset.range M.toNat,
            (if (m : ℤ) + 1 = (1 : ℤ) then (2 : ℂ) else 0) • aExpCZ c (M - 1 - m))
          = ((2 * c : ℂ)) • aExpCZ c (M - 1) := by
        rw [show (∑ m ∈ Finset.range M.toNat,
                  (if (m : ℤ) + 1 = (1 : ℤ) then (2 : ℂ) else 0) • aExpCZ c (M - 1 - m))
                = (2 : ℂ) • aExpCZ c (M - 1) from by
            rw [Finset.sum_eq_single 0]
            · rw [if_pos (by norm_num), show M - 1 - ((0 : ℕ) : ℤ) = M - 1 from by ring]
            · intro b _ hb; rw [if_neg (by omega), zero_smul]
            · intro hmem; exact absurd (Finset.mem_range.mpr (by omega)) hmem,
          smul_smul, mul_comm]
      rw [col1c, col2c, col3c]
      module

/-- **`α₋₁` commutes with `EminusC c b`** (both are `mulLeft` of a polynomial in the creation
variables): general-charge transcription of `alpha_comp_EminusC_neg`. -/
theorem alphaNeg1_comm_EminusC (c : ℂ) (b : ℤ) :
    α (-1) * EminusC c b = EminusC c b * α (-1) := by
  change (α (-1)).comp (EminusC c b) = (EminusC c b).comp (α (-1))
  refine LinearMap.ext fun q => ?_
  rw [EminusC_apply]
  split_ifs with ht
  · simp only [LinearMap.comp_apply, α, EminusOpC, LinearMap.mulLeft_apply,
      HeisenbergN.oscN_apply_neg 1 2 0 (show (-1 : ℤ) < 0 by norm_num)]
    ring
  · simp

/-- **The `α₋₁`–`EplusC` index shift** `[α₋₁, EplusC c t] = (2c)·EplusC c (t+1)`. -/
theorem alphaNeg1_EplusC_shift (c : ℂ) (t : ℤ) :
    α (-1) * EplusC c t - EplusC c t * α (-1) = ((2 * c : ℂ)) • EplusC c (t + 1) := by
  rw [EplusC_eq_aExpCZ, EplusC_eq_aExpCZ, show -(t + 1) = -t - 1 from by ring,
    show α (-1) * aExpCZ c (-t) = (α (-1)).comp (aExpCZ c (-t)) from rfl,
    alphaNeg1_comp_aExpCZ c (-t)]
  rw [show (aExpCZ c (-t)).comp (α (-1)) = aExpCZ c (-t) * α (-1) from rfl]
  abel

/-- **Per-term `α₋₁`-bracket of the normal-ordered product**: `α₋₁` commutes through the creation
half `EminusC` and shifts the annihilation half `EplusC` by `+1` with factor `2c`. -/
theorem alphaNeg1_comm_normalOrdered (c : ℂ) (k n : ℤ) :
    α (-1) * normalOrdered (EminusC c) (EplusC c) k n
      - normalOrdered (EminusC c) (EplusC c) k n * α (-1)
      = ((2 * c : ℂ)) • normalOrdered (EminusC c) (EplusC c) k (n + 1) := by
  simp only [normalOrdered_apply]
  have hsh := alphaNeg1_EplusC_shift c n
  by_cases hk : 0 ≤ k
  · simp only [if_pos hk]
    have hc_em : α (-1) * EminusC c k = EminusC c k * α (-1) := alphaNeg1_comm_EminusC c k
    rw [show α (-1) * (EminusC c k * EplusC c n) = EminusC c k * (α (-1) * EplusC c n) from by
          rw [← mul_assoc, hc_em, mul_assoc],
        mul_assoc (EminusC c k) (EplusC c n) (α (-1)), ← mul_sub, hsh, mul_smul_comm]
  · simp only [if_neg hk]
    have hc_em : EplusC c n * (EminusC c k * α (-1)) = EplusC c n * (α (-1) * EminusC c k) := by
      rw [alphaNeg1_comm_EminusC c k]
    rw [show α (-1) * (EplusC c n * EminusC c k) = (α (-1) * EplusC c n) * EminusC c k from
          (mul_assoc _ _ _).symm,
        mul_assoc (EplusC c n) (EminusC c k) (α (-1)), hc_em,
        ← mul_assoc (EplusC c n) (α (-1)) (EminusC c k), ← sub_mul, hsh, smul_mul_assoc]

/-- **(*) The `α₋₁`-bracket of the charge-`c` boson dressing**: `[α₋₁, EEC c r] = (2c)·EEC c (r+1)`
(the lattice "momentum" charge-shift of the exponential dressing). -/
theorem alphaNeg1_comm_EEC (c : ℂ) (r : ℤ) :
    α (-1) * EEC c r - EEC c r * α (-1) = ((2 * c : ℂ)) • EEC c (r + 1) := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, EEC, nprod_apply]
  rw [map_finsum (α (-1))
        (normalOrdered_diag_support_finite (EminusC_isField c) (EplusC_isField c) r x),
    ← finsum_sub_distrib
        ((normalOrdered_diag_support_finite (EminusC_isField c) (EplusC_isField c) r x).subset
          (fun m hm => by
            rw [Function.mem_support] at hm ⊢; exact fun h => hm (by rw [h, map_zero])))
        (normalOrdered_diag_support_finite (EminusC_isField c) (EplusC_isField c) r (α (-1) x)),
    smul_finsum' (2 * c : ℂ)
        (normalOrdered_diag_support_finite (EminusC_isField c) (EplusC_isField c) (r + 1) x)]
  refine finsum_congr fun k => ?_
  rw [show (r + 1) - k = (r - k) + 1 from by ring]
  have hterm := congrArg (fun (T : End ℂ B) => T x) (alphaNeg1_comm_normalOrdered c k (r - k))
  simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] using hterm

end VOA.LatExp
