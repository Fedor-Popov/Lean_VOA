/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesSliceMap
import VOA.Examples.AffineSl2BoundaryMaximalIdeal

/-!
# Creation Sugawara modes on a positive-current-singular vector

For a vector `t` of the universal affine vacuum module `V^k(sl₂)` killed by every positive current
mode (`SingP k t`), the normal-ordered Sugawara sum `L_{-m-1} t` is a *finite* sum of current
words: only the terms whose right-hand mode is non-positive survive.  We record

* `Lm_singP` — the exact formula
  `L_{-m-1} t = c₀ ∑_{a,b} κ⁻¹(a,b) (J^b_{-m-1} J^a_0 t + ∑_{p=0}^{m} J^a_{-p-1} J^b_{p-m} t)`;
* `Lm_singP_expand` — the same with the Casimir `κ⁻¹` written out (`e = 0`, `f = 1`, `h = 2`);
* the elementary commutators of current modes used by the slice-closure argument
  (`J_comm_apply`, `e_f_comm`, `e_h_comm`, `zero_f_comm`, `zero_h_comm`, `zero_e_comm`).

Everything here is proved; no new axiom.
-/

namespace VOA.TwoSeries.SliceMap

open VOA.AffineVOA VOA.AffineVOA.SugawaraCov VOA.AffineVOA.Strong
open scoped BigOperators

noncomputable section

variable (k : ℂ) (hk : k + 2 ≠ 0)

/-! ## §1  Commutators of current modes, applied to vectors -/

/-- The current commutator applied to a vector. -/
theorem J_comm_apply (a b : Fin 3) (m n : ℤ) (y : WakModule k) :
    J k a m (J k b n y) = J k b n (J k a m y) + ∑ c, fabc a b c • J k c (m + n) y +
      (if m + n = 0 then ((m : ℂ) * k * kappa a b) • y else 0) := by
  have h := congrArg (fun T : Module.End ℂ (WakModule k) => T y) (current_comm k a b m n)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  split_ifs <;> simp [add_comm, add_left_comm]

/-- `[e_μ, f_ν] = h_{μ+ν}` away from the central term. -/
theorem e_f_comm (μ ν : ℤ) (hμν : μ + ν ≠ 0) (y : WakModule k) :
    J k 0 μ (J k 1 ν y) = J k 1 ν (J k 0 μ y) + J k 2 (μ + ν) y := by
  rw [J_comm_apply, if_neg hμν, add_zero, Fin.sum_univ_three]
  simp [fabc]

/-- `[e_μ, h_ν] = -2 e_{μ+ν}` away from the central term (there is none: `κ(e,h) = 0`). -/
theorem e_h_comm (μ ν : ℤ) (y : WakModule k) :
    J k 0 μ (J k 2 ν y) = J k 2 ν (J k 0 μ y) + (-2 : ℂ) • J k 0 (μ + ν) y := by
  rw [J_comm_apply, Fin.sum_univ_three]
  split_ifs <;> simp [fabc, kappa]

/-- `[f_μ, h_ν] = 2 f_{μ+ν}`. -/
theorem f_h_comm (μ ν : ℤ) (y : WakModule k) :
    J k 1 μ (J k 2 ν y) = J k 2 ν (J k 1 μ y) + (2 : ℂ) • J k 1 (μ + ν) y := by
  rw [J_comm_apply, Fin.sum_univ_three]
  split_ifs <;> simp [fabc, kappa]

/-- `[f_μ, f_ν] = 0`. -/
theorem f_f_comm (μ ν : ℤ) (y : WakModule k) :
    J k 1 μ (J k 1 ν y) = J k 1 ν (J k 1 μ y) := by
  rw [J_comm_apply, Fin.sum_univ_three]
  split_ifs <;> simp [fabc, kappa]

/-- `[h_μ, f_ν] = -2 f_{μ+ν}`. -/
theorem h_f_comm (μ ν : ℤ) (y : WakModule k) :
    J k 2 μ (J k 1 ν y) = J k 1 ν (J k 2 μ y) + (-2 : ℂ) • J k 1 (μ + ν) y := by
  rw [J_comm_apply, Fin.sum_univ_three]
  split_ifs <;> simp [fabc, kappa]

/-- `[h_0, h_ν] = 0`. -/
theorem h0_h_comm (ν : ℤ) (y : WakModule k) :
    J k 2 0 (J k 2 ν y) = J k 2 ν (J k 2 0 y) := by
  rw [J_comm_apply, Fin.sum_univ_three]
  split_ifs <;> simp [fabc, kappa]

/-- `[f_0, e_ν] = -h_ν` for `ν ≠ 0`. -/
theorem f0_e_comm (ν : ℤ) (hν : ν ≠ 0) (y : WakModule k) :
    J k 1 0 (J k 0 ν y) = J k 0 ν (J k 1 0 y) + (-1 : ℂ) • J k 2 ν y := by
  rw [J_comm_apply, if_neg (by omega), add_zero, Fin.sum_univ_three]
  simp [fabc]

/-- `[h_0, e_ν] = 2 e_ν`. -/
theorem h0_e_comm (ν : ℤ) (y : WakModule k) :
    J k 2 0 (J k 0 ν y) = J k 0 ν (J k 2 0 y) + (2 : ℂ) • J k 0 ν y := by
  rw [J_comm_apply, Fin.sum_univ_three]
  split_ifs <;> simp [fabc, kappa]

/-- `[e_0, e_ν] = 0`. -/
theorem e_e_comm (μ ν : ℤ) (y : WakModule k) :
    J k 0 μ (J k 0 ν y) = J k 0 ν (J k 0 μ y) := by
  rw [J_comm_apply, Fin.sum_univ_three]
  split_ifs <;> simp [fabc, kappa]

/-! ## §2  The Sugawara modes on a positive-singular vector -/

/-- The `p`-th normal-ordered summand of `L_n` (`n = -m-1`), as in `nprod_apply`. -/
theorem nprod_coeff_apply (a b : Fin 3) (n : ℤ) (x : WakModule k) :
    VOA.nprod (Jfield_isField k a) (Jfield_isField k b) (-n - 2) x =
      ∑ᶠ p : ℤ, (if 0 ≤ p then J k a (-p - 1) (J k b (n + p + 1) x)
        else J k b (n + p + 1) (J k a (-p - 1) x)) := by
  rw [VOA.nprod_apply]
  refine finsum_congr fun p => ?_
  rw [normalOrdered_apply, Jfield_apply, Jfield_apply,
    show -(-n - 2 - p) - 1 = n + p + 1 by ring]
  split_ifs <;> rfl

/-- The finite support of the normal-ordered sum on a positive-singular vector. -/
theorem nprod_coeff_singP (t : WakModule k) (ht : SingP k t) (a b : Fin 3) (m : ℕ) :
    VOA.nprod (Jfield_isField k a) (Jfield_isField k b) (-(-(m : ℤ) - 1) - 2) t =
      J k b (-(m : ℤ) - 1) (J k a 0 t) +
        ∑ p ∈ Finset.range (m + 1), J k a (-(p : ℤ) - 1) (J k b ((p : ℤ) - m) t) := by
  classical
  rw [nprod_coeff_apply]
  set F : ℤ → WakModule k := fun p => if 0 ≤ p then J k a (-p - 1) (J k b (-(m : ℤ) - 1 + p + 1) t)
    else J k b (-(m : ℤ) - 1 + p + 1) (J k a (-p - 1) t) with hF
  have hsupp : Function.support F ⊆
      ((Finset.range (m + 2)).image (fun i : ℕ => (i : ℤ) - 1) : Set ℤ) := by
    intro p hp
    rw [Function.mem_support] at hp
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    by_cases h0 : 0 ≤ p
    · by_cases hpm : p ≤ m
      · exact ⟨(p + 1).toNat, by omega, by omega⟩
      · exfalso; apply hp
        simp only [hF, if_pos h0]
        rw [ht b _ (by omega), map_zero]
    · by_cases hp1 : p = -1
      · exact ⟨0, by omega, by simp [hp1]⟩
      · exfalso; apply hp
        simp only [hF, if_neg h0]
        rw [ht a _ (by omega), map_zero]
  rw [finsum_eq_sum_of_support_subset F hsupp,
    Finset.sum_image (fun x _ y _ h => by simpa using h), Finset.sum_range_succ']
  rw [add_comm]
  congr 1
  · simp only [hF, Nat.cast_zero, zero_sub]
    rw [if_neg (by omega)]
    congr 2
    ring_nf
  · refine Finset.sum_congr rfl fun p _ => ?_
    simp only [hF]
    rw [if_pos (by push_cast; omega)]
    push_cast
    congr 2 <;> ring_nf

/-- **Creation Sugawara modes on a positive-singular vector.** -/
theorem Lm_singP (t : WakModule k) (ht : SingP k t) (m : ℕ) :
    Lm k hk (-(m : ℤ) - 1) t =
      (2 * (k + dualCoxeter))⁻¹ • ∑ a : Fin 3, ∑ b : Fin 3, kappaInv a b •
        (J k b (-(m : ℤ) - 1) (J k a 0 t) +
          ∑ p ∈ Finset.range (m + 1), J k a (-(p : ℤ) - 1) (J k b ((p : ℤ) - m) t)) := by
  rw [Lm, YA_omega_eq, mode_apply, show -(-(m : ℤ) - 1 + 1) - 1 = -(-(m : ℤ) - 1) - 2 by ring]
  unfold AffineVOA.sugawaraField
  show ((2 * (k + dualCoxeter))⁻¹ • (Reconstruction.evalAt (-(-(m : ℤ) - 1) - 2) t
      (∑ a : Fin 3, ∑ b : Fin 3,
        kappaInv a b • VOA.nprod (Jfield_isField k a) (Jfield_isField k b)))) = _
  rw [map_sum]
  refine congrArg ((2 * (k + dualCoxeter))⁻¹ • ·) ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul]
  refine congrArg (kappaInv a b • ·) ?_
  rw [Reconstruction.evalAt_apply, nprod_coeff_singP k t ht a b m]

/-- The Sugawara formula on a positive-singular vector with `κ⁻¹` written out. -/
theorem Lm_singP_expand (t : WakModule k) (ht : SingP k t) (m : ℕ) :
    Lm k hk (-(m : ℤ) - 1) t =
      c0 k • ((J k 1 (-(m : ℤ) - 1) (J k 0 0 t) +
          ∑ p ∈ Finset.range (m + 1), J k 0 (-(p : ℤ) - 1) (J k 1 ((p : ℤ) - m) t)) +
        (J k 0 (-(m : ℤ) - 1) (J k 1 0 t) +
          ∑ p ∈ Finset.range (m + 1), J k 1 (-(p : ℤ) - 1) (J k 0 ((p : ℤ) - m) t)) +
        (1 / 2 : ℂ) • (J k 2 (-(m : ℤ) - 1) (J k 2 0 t) +
          ∑ p ∈ Finset.range (m + 1), J k 2 (-(p : ℤ) - 1) (J k 2 ((p : ℤ) - m) t))) := by
  rw [Lm_singP k hk t ht m, c0]
  congr 1
  simp only [Fin.sum_univ_three, kappaInv]
  simp

end

end VOA.TwoSeries.SliceMap
