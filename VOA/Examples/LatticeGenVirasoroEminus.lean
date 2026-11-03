/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenTranslation

/-!
# The E⁻ Virasoro defect `[L₋₁, E⁻(α,z)]`

The creation half `E⁻(α)_N = mulLeft(vSchur α N)` is `L₋₁`-covariant up to the `chargeOsc α (-1)`
defect: `[L₋₁, E⁻(α)_N] = (N+1)·E⁻(α)_{N+1} − chargeOsc α(-1)·E⁻(α)_N`.  The key structural fact is
`chargeOsc α(-(m+1)) = mulLeft(vVar α m)` (the charge creation IS the charge-weighted variable), so
the `A₁` `mulXN`/`cVar` machinery lifts verbatim with `chargeOsc α(-(m+1))` in place of `α₋(m+1)`.

Cross-charge lift of A₁'s `LatticeExpVirasoro` §E⁻.  All `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN

variable (L : IntegralLattice)

/-- **The general `[L₋₁, chargeOsc α n]` commutator** `= -n·chargeOsc α (n-1)` (frame sum of
`LvirN_comm_oscN`). -/
theorem LvirN_comm_chargeOsc (β : L.carrier) (n : ℤ) :
    HeisenbergN.LvirN (rank L) 1 (-1) * chargeOsc L β n
      - chargeOsc L β n * HeisenbergN.LvirN (rank L) 1 (-1)
      = (-(n : ℂ)) • chargeOsc L β (n - 1) := by
  rw [chargeOsc, chargeOsc, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub,
    LvirN_comm_oscN (rank L) 1 (by norm_num : (1 : ℂ) ≠ 0) b (-1) n,
    show (-1 : ℤ) + n = n - 1 from by ring, smul_comm]

/-- **The charge creation IS the charge-weighted variable**: `chargeOsc α(-(m+1)) = mulLeft(vVar α m)`. -/
theorem chargeOsc_neg_eq_mulLeft_vVar (β : L.carrier) (m : ℕ) :
    chargeOsc L β (-((m : ℤ) + 1)) = LinearMap.mulLeft ℂ (vVar L β m) := by
  refine LinearMap.ext fun p => ?_
  rw [chargeOsc, LinearMap.coe_sum, Finset.sum_apply, LinearMap.mulLeft_apply, vVar, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [LinearMap.smul_apply, oscN_neg (rank L) 1 a (show -((m : ℤ) + 1) < 0 by omega),
    show (-(-((m : ℤ) + 1)) - 1).toNat = m from by omega, mulXN_apply, smul_mul_assoc, chargeCoord]

/-- The `E⁻` operator recursion (composition form): `E⁻(α)_{N+1} =
(N+1)⁻¹·∑_{m<N+1} chargeOsc α(-(m+1))·E⁻(α)_{N-m}`.  From the `vSchur` Newton recursion. -/
theorem EminusVec_succ_op (β : L.carrier) (N : ℕ) :
    EminusVec L β (N + 1)
      = ((N : ℂ) + 1)⁻¹ • ∑ m ∈ Finset.range (N + 1),
          chargeOsc L β (-((m : ℤ) + 1)) * EminusVec L β (N - m) := by
  have hvs : vSchur L β (N + 1) = ((N : ℂ) + 1)⁻¹ • ∑ m ∈ Finset.range (N + 1),
      vVar L β m * vSchur L β (N - m) := by
    have h := vSchur_recursion_sum L β (N + 1)
    rw [show (N + 1) - 1 = N from rfl] at h
    rw [h, smul_smul, show ((N : ℂ) + 1)⁻¹ * ((N + 1 : ℕ) : ℂ) = 1 from by
      push_cast; exact inv_mul_cancel₀ (Nat.cast_add_one_ne_zero N), one_smul]
  refine LinearMap.ext fun p => ?_
  have hR : (∑ m ∈ Finset.range (N + 1),
        (chargeOsc L β (-((m : ℤ) + 1)) * EminusVec L β (N - m)) p)
      = (∑ m ∈ Finset.range (N + 1), vVar L β m * vSchur L β (N - m)) * p := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Module.End.mul_apply, chargeOsc_neg_eq_mulLeft_vVar, LinearMap.mulLeft_apply, EminusVec,
      LinearMap.mulLeft_apply, mul_assoc]
  rw [LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply, hR, EminusVec,
    LinearMap.mulLeft_apply, hvs, smul_mul_assoc]

/-- The abstract index-combine behind the E⁻ telescoping (generic over `FockN (rank L)`). -/
theorem combinePQGen (n : ℕ) (g : ℕ → End ℂ (FockN (rank L))) :
    (∑ m ∈ Finset.range (n + 1), ((m : ℂ) + 1) • g (m + 1))
      + (∑ m ∈ Finset.range (n + 1), (((n - m : ℕ) : ℂ) + 1) • g m)
    = ((n : ℂ) + 1) • ∑ i ∈ Finset.range (n + 2), g i := by
  induction n with
  | zero =>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, zero_add,
      Nat.sub_self, one_smul]
    abel
  | succ n ih =>
    rw [Finset.sum_range_succ (fun m => ((m : ℂ) + 1) • g (m + 1)),
      Finset.sum_range_succ (fun m => (((n + 1 - m : ℕ) : ℂ) + 1) • g m),
      Finset.sum_range_succ (fun i => g i)]
    have hQ : (∑ m ∈ Finset.range (n + 1), (((n + 1 - m : ℕ) : ℂ) + 1) • g m)
        = (∑ m ∈ Finset.range (n + 1), (((n - m : ℕ) : ℂ) + 1) • g m)
          + ∑ m ∈ Finset.range (n + 1), g m := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m hm => ?_
      simp only [Finset.mem_range] at hm
      rw [show ((n + 1 - m : ℕ) : ℂ) + 1 = (((n - m : ℕ) : ℂ) + 1) + 1 from by
        rw [show n + 1 - m = (n - m) + 1 from by omega]; push_cast; ring, add_smul, one_smul]
    rw [hQ]
    have hP : (∑ m ∈ Finset.range (n + 1), ((m : ℂ) + 1) • g (m + 1))
        = ((n : ℂ) + 1) • ∑ i ∈ Finset.range (n + 2), g i
          - (∑ m ∈ Finset.range (n + 1), (((n - m : ℕ) : ℂ) + 1) • g m) := by
      rw [eq_sub_iff_add_eq, ih]
    rw [hP, Finset.sum_range_succ (fun i => g i)]
    simp only [Nat.sub_self, Nat.cast_zero, zero_add]
    push_cast
    module

/-- **The E⁻ `chargeOsc(-1)`-defect `L₋₁`-covariance**:
`[L₋₁, E⁻(β)_N] = (N+1)·E⁻(β)_{N+1} − chargeOsc β(-1)·E⁻(β)_N`.  Strong induction via
`EminusVec_succ_op` + `combinePQGen`; the creation modes `chargeOsc β(-(m+1))` are `L₋₁`-covariant
(`LvirN_comm_chargeOsc`) and commute with the `chargeOsc β(-1)` defect.  Cross-charge lift of A₁'s
`LvirN_comm_EminusOpC` (SIMPLER: no charge scalar). -/
theorem LvirN_comm_EminusVec (β : L.carrier) :
    ∀ N : ℕ, HeisenbergN.LvirN (rank L) 1 (-1) * EminusVec L β N
        - EminusVec L β N * HeisenbergN.LvirN (rank L) 1 (-1)
      = ((N : ℂ) + 1) • EminusVec L β (N + 1)
        - chargeOsc L β (-1) * EminusVec L β N := by
  set Lv : End ℂ (FockN (rank L)) := HeisenbergN.LvirN (rank L) 1 (-1) with hLv
  have hderiv : ∀ X Y : End ℂ (FockN (rank L)), Lv * (X * Y) - (X * Y) * Lv
      = (Lv * X - X * Lv) * Y + X * (Lv * Y - Y * Lv) := by
    intro X Y; simp only [sub_mul, mul_sub, mul_assoc]; abel
  have hLc : ∀ m : ℕ, Lv * chargeOsc L β (-((m : ℤ) + 1)) - chargeOsc L β (-((m : ℤ) + 1)) * Lv
      = ((m : ℂ) + 1) • chargeOsc L β (-(((m : ℤ) + 1) + 1)) := by
    intro m
    rw [hLv, LvirN_comm_chargeOsc L β (-((m : ℤ) + 1)),
      show (-((m : ℤ) + 1)) - 1 = -(((m : ℤ) + 1) + 1) from by ring]
    congr 1; push_cast; ring
  have hcomm : ∀ m : ℕ, chargeOsc L β (-((m : ℤ) + 1)) * chargeOsc L β (-1)
      = chargeOsc L β (-1) * chargeOsc L β (-((m : ℤ) + 1)) := by
    intro m
    rw [chargeOsc_neg_eq_mulLeft_vVar,
      show chargeOsc L β (-1) = LinearMap.mulLeft ℂ (vVar L β 0) from by
        rw [show (-1 : ℤ) = -((0 : ℕ) + 1) from by norm_num, chargeOsc_neg_eq_mulLeft_vVar]]
    refine LinearMap.ext fun p => ?_
    simp only [Module.End.mul_apply, LinearMap.mulLeft_apply]
    rw [← mul_assoc, ← mul_assoc, mul_comm (vVar L β m) (vVar L β 0)]
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  match N with
  | 0 =>
    have h0 : EminusVec L β 0 = 1 := by
      rw [EminusVec, vSchur_zero, LinearMap.mulLeft_one]; exact Module.End.one_eq_id.symm
    have h1 : EminusVec L β 1 = chargeOsc L β (-1) := by
      rw [EminusVec_succ_op L β 0, Finset.sum_range_one]
      simp only [Nat.sub_self, h0, mul_one, Nat.cast_zero, zero_add, inv_one, one_smul]
    rw [h0, h1, mul_one, one_mul, sub_self, Nat.cast_zero, zero_add, one_smul, mul_one, sub_self]
  | (n + 1) =>
    have hn1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    have pt : ∀ m ∈ Finset.range (n + 1),
        Lv * (chargeOsc L β (-((m : ℤ) + 1)) * EminusVec L β (n - m))
          - (chargeOsc L β (-((m : ℤ) + 1)) * EminusVec L β (n - m)) * Lv
        = ((m : ℂ) + 1) • (chargeOsc L β (-(((m : ℤ) + 1) + 1)) * EminusVec L β ((n + 1) - (m + 1)))
          + (((n - m : ℕ) : ℂ) + 1) • (chargeOsc L β (-((m : ℤ) + 1)) * EminusVec L β ((n + 1) - m))
          - chargeOsc L β (-1) * (chargeOsc L β (-((m : ℤ) + 1)) * EminusVec L β (n - m)) := by
      intro m hm
      simp only [Finset.mem_range] at hm
      rw [hderiv, hLc m, ih (n - m) (by omega), smul_mul_assoc, mul_sub, mul_smul_comm,
        show (n + 1) - (m + 1) = n - m from by omega, show (n + 1) - m = (n - m) + 1 from by omega,
        show chargeOsc L β (-((m : ℤ) + 1)) * (chargeOsc L β (-1) * EminusVec L β (n - m))
            = chargeOsc L β (-1) * (chargeOsc L β (-((m : ℤ) + 1)) * EminusVec L β (n - m)) from by
          rw [← mul_assoc, hcomm m, mul_assoc]]
      abel
    conv_lhs => rw [EminusVec_succ_op L β n]
    set R₀ := ∑ m ∈ Finset.range (n + 1),
      chargeOsc L β (-((m : ℤ) + 1)) * EminusVec L β (n - m) with hR₀
    have hcR : R₀ = ((n : ℂ) + 1) • EminusVec L β (n + 1) := by
      rw [EminusVec_succ_op L β n, ← hR₀, smul_smul, mul_inv_cancel₀ hn1, one_smul]
    have hBrR : Lv * R₀ - R₀ * Lv
        = ((n : ℂ) + 1) • (∑ i ∈ Finset.range (n + 2),
            chargeOsc L β (-((i : ℤ) + 1)) * EminusVec L β ((n + 1) - i))
          - chargeOsc L β (-1) * R₀ := by
      rw [hR₀, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
        Finset.sum_congr rfl pt, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      rw [show (∑ m ∈ Finset.range (n + 1),
              ((m : ℂ) + 1) • (chargeOsc L β (-(((m : ℤ) + 1) + 1)) * EminusVec L β ((n + 1) - (m + 1))))
            = ∑ m ∈ Finset.range (n + 1),
              ((m : ℂ) + 1) • ((fun i : ℕ => chargeOsc L β (-((i : ℤ) + 1)) * EminusVec L β ((n + 1) - i)) (m + 1))
          from Finset.sum_congr rfl fun m _ => by
            simp only []
            rw [show (((m : ℤ) + 1) + 1 : ℤ) = ((m + 1 : ℕ) : ℤ) + 1 from by push_cast; ring],
        combinePQGen L n (fun i : ℕ => chargeOsc L β (-((i : ℤ) + 1)) * EminusVec L β ((n + 1) - i)),
        ← Finset.mul_sum, ← hR₀]
    rw [show Lv * (((n : ℂ) + 1)⁻¹ • R₀) - (((n : ℂ) + 1)⁻¹ • R₀) * Lv
          = ((n : ℂ) + 1)⁻¹ • (Lv * R₀ - R₀ * Lv) from by
        rw [mul_smul_comm, smul_mul_assoc, ← smul_sub],
      hBrR]
    set Rp := ∑ i ∈ Finset.range (n + 2),
      chargeOsc L β (-((i : ℤ) + 1)) * EminusVec L β ((n + 1) - i) with hRp
    have hcR' : Rp = (((n + 1 : ℕ) : ℂ) + 1) • EminusVec L β (n + 1 + 1) := by
      rw [hRp, EminusVec_succ_op L β (n + 1), ← hRp, smul_smul,
        mul_inv_cancel₀ (Nat.cast_add_one_ne_zero (n + 1)), one_smul]
    rw [show ((n : ℂ) + 1)⁻¹ • (((n : ℂ) + 1) • Rp - chargeOsc L β (-1) * R₀)
          = ((n : ℂ) + 1)⁻¹ • (((n : ℂ) + 1) • Rp) - ((n : ℂ) + 1)⁻¹ • (chargeOsc L β (-1) * R₀)
          from smul_sub _ _ _,
      smul_smul, inv_mul_cancel₀ hn1, one_smul, hcR', hcR,
      show ((n : ℂ) + 1)⁻¹ • (chargeOsc L β (-1) * (((n : ℂ) + 1) • EminusVec L β (n + 1)))
          = chargeOsc L β (-1) * EminusVec L β (n + 1) from by
        rw [mul_smul_comm, smul_smul, inv_mul_cancel₀ hn1, one_smul]]

/-- The **ℤ-indexed E⁻ Virasoro defect** `[L₋₁, E⁻(β)_t] = (t+1)·E⁻(β)_{t+1} − chargeOsc β(-1)·E⁻(β)_t`. -/
theorem LvirN_comm_EminusVecField (β : L.carrier) (t : ℤ) :
    HeisenbergN.LvirN (rank L) 1 (-1) * EminusVecField L β t
      - EminusVecField L β t * HeisenbergN.LvirN (rank L) 1 (-1)
      = ((t + 1 : ℤ)) • EminusVecField L β (t + 1) - chargeOsc L β (-1) * EminusVecField L β t := by
  by_cases ht : 0 ≤ t
  · have key : ((t.toNat : ℕ) : ℂ) = (t : ℂ) := by rw [← Int.cast_natCast, Int.toNat_of_nonneg ht]
    rw [EminusVecField_apply, if_pos ht, EminusVecField_apply, if_pos (by omega : (0 : ℤ) ≤ t + 1),
      show (t + 1).toNat = t.toNat + 1 from by omega, LvirN_comm_EminusVec L β t.toNat]
    rw [show ((t.toNat : ℂ) + 1) = (((t + 1 : ℤ)) : ℂ) from by rw [key]; push_cast; ring,
      Int.cast_smul_eq_zsmul ℂ (t + 1) (EminusVec L β (t.toNat + 1))]
  · rw [EminusVecField_apply, if_neg ht, mul_zero, zero_mul, sub_self, mul_zero, sub_zero]
    rcases lt_or_eq_of_le (show t + 1 ≤ 0 by omega) with h | h
    · rw [EminusVecField_apply, if_neg (by omega : ¬ (0 : ℤ) ≤ t + 1)]; exact (smul_zero _).symm
    · rw [h, zero_smul]

end VOA.LatGen
