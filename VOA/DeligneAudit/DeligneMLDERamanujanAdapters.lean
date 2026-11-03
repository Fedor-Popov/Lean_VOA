/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneMLDERamanujanFull
import VOA.DeligneAudit.DeligneMLDEEightSq
import VOA.DeligneAudit.DeligneMLDEProduct
import VOA.DeligneAudit.DeligneCharacterD4MLDE
import VOA.DeligneAudit.G2StarMLDE

/-!
# Ramanujan's three identities, discharged for `D4MLDE` and `G2Star`

* `ramanujan6`: `1008 θP₅ = 24P₁ + 504P₅ - 12096P₁P₅ + 480P₃ + 57600P₃²` (`2θE₆ = E₂E₆ - E₄²`), from
  `order_seven`, `ramanujan`, `ramanujan4` and `E₄² = E₈` (`EightSq.eight_sq`, Mathlib Sturm bound).
* `D4MLDE.ramanujanIdentities : DeligneCharacter.D4MLDE.RamanujanIdentities`;
* `G2Star.ramanujanFormal : G2Star.RamanujanFormal`.
-/

namespace VOA.DeligneAudit.DeligneMLDE.Heat

open PowerSeries VOA.QSeries VOA.QSeries.JTP

open scoped BigOperators

noncomputable section

theorem coeff_P5 (n : ℕ) : coeff n P5 = (DeligneCharacter.sigmaK 5 n : ℚ) := by
  rw [P5, coeff_lamQ_divisors, DeligneCharacter.sigmaK]
  push_cast
  rw [Nat.sum_div_divisors n (fun d => ((d : ℚ)) ^ 5)]

theorem coeff_P7 (n : ℕ) : coeff n P7 = (DeligneCharacter.sigmaK 7 n : ℚ) := by
  rw [P7, coeff_lamQ_divisors, DeligneCharacter.sigmaK]
  push_cast
  rw [Nat.sum_div_divisors n (fun d => ((d : ℚ)) ^ 7)]

theorem sigmaK_zero (k : ℕ) : DeligneCharacter.sigmaK k 0 = 0 := by
  simp [DeligneCharacter.sigmaK]

/-- `E₄² = E₈` in `P`-form: `120 P₃² = P₇ - P₃`. -/
theorem eightSqP : PowerSeries.C 120 * (P3 * P3) = P7 - P3 := by
  have hE4 : PowerSeries.mk EightSq.e4 = 1 + 240 * P3 := by
    refine PowerSeries.ext fun n => ?_
    rw [coeff_mk, map_add, coeff_one, show (240 : PowerSeries ℚ) = PowerSeries.C 240 from
      (map_ofNat _ 240).symm, coeff_C_mul, coeff_P3, EightSq.e4]
    split_ifs with h <;> simp [h, sigmaK_zero]
  have hE8 : PowerSeries.mk EightSq.e8 = 1 + 480 * P7 := by
    refine PowerSeries.ext fun n => ?_
    rw [coeff_mk, map_add, coeff_one, show (480 : PowerSeries ℚ) = PowerSeries.C 480 from
      (map_ofNat _ 480).symm, coeff_C_mul, coeff_P7, EightSq.e8]
    split_ifs with h <;> simp [h, sigmaK_zero]
  have h : PowerSeries.mk EightSq.e4 * PowerSeries.mk EightSq.e4 = PowerSeries.mk EightSq.e8 := by
    refine PowerSeries.ext fun n => ?_
    rw [coeff_mul, coeff_mk]
    simpa only [coeff_mk] using EightSq.eight_sq n
  rw [hE4, hE8] at h
  have h480 : (480 : PowerSeries ℚ) ≠ 0 := by
    rw [show (480 : PowerSeries ℚ) = PowerSeries.C 480 from (map_ofNat _ 480).symm]
    exact fun h0 => by simpa using congrArg (coeff 0) h0
  rw [show (PowerSeries.C (120 : ℚ) : PowerSeries ℚ) = 120 from map_ofNat _ 120]
  apply mul_left_cancel₀ h480
  linear_combination h

/-- **`2θE₆ = E₂E₆ - E₄²`**, in `P`-form. -/
theorem ramanujan6 :
    PowerSeries.C 1008 * eulerOp P5 = PowerSeries.C 24 * P1 + PowerSeries.C 504 * P5 - PowerSeries.C 12096 * (P1 * P5) + PowerSeries.C 480 * P3
      + PowerSeries.C 57600 * (P3 * P3) := by
  refine PowerSeries.ext fun n => ?_
  have h7 := congrArg (coeff n) order_seven
  have h3 := congrArg (coeff n) ramanujan
  have h5 := congrArg (coeff n) ramanujan4
  have h8 := congrArg (coeff n) eightSqP
  simp only [map_add, map_sub, coeff_C_mul, coeff_eulerOp, map_zero] at h7 h3 h5 h8 ⊢
  linarith

end

end VOA.DeligneAudit.DeligneMLDE.Heat

/-! ## The `RamanujanIdentities` -/

namespace VOA.DeligneAudit.DeligneCharacter.D4MLDE

open PowerSeries VOA.QSeries.JTP VOA.DeligneAudit.DeligneMLDE.Heat

theorem sigS_one : sigS 1 = P1 := by
  refine PowerSeries.ext fun n => ?_
  rw [sigS, coeff_mk, coeff_P1]; split_ifs with h <;> simp [h, sigmaK_zero]

theorem sigS_three : sigS 3 = P3 := by
  refine PowerSeries.ext fun n => ?_
  rw [sigS, coeff_mk, coeff_P3]; split_ifs with h <;> simp [h, sigmaK_zero]

theorem sigS_five : sigS 5 = P5 := by
  refine PowerSeries.ext fun n => ?_
  rw [sigS, coeff_mk, coeff_P5]; split_ifs with h <;> simp [h, sigmaK_zero]

theorem eulerOp_natMul (c : ℕ) [c.AtLeastTwo] (F : PowerSeries ℚ) :
    eulerOp ((OfNat.ofNat c : PowerSeries ℚ) * F) = (OfNat.ofNat c : PowerSeries ℚ) * eulerOp F := by
  rw [show (OfNat.ofNat c : PowerSeries ℚ) = PowerSeries.C (OfNat.ofNat c) from (map_ofNat _ c).symm,
    eulerOp_C_mul]

/-- **Ramanujan's three identities, proved** (the named input). -/
theorem ramanujanIdentities : RamanujanIdentities := by
  have h1 := ramanujan
  have h2 := ramanujan4
  have h3 := ramanujan6
  simp only [map_ofNat] at h1 h2 h3
  refine ⟨?_, ?_, ?_⟩
  · rw [E2s, E4s, sigS_one, sigS_three, eulerOp_sub, eulerOp_one, eulerOp_natMul]
    linear_combination (-48 : PowerSeries ℚ) * h1
  · rw [E2s, E4s, E6s, sigS_one, sigS_three, sigS_five, eulerOp_add, eulerOp_one, eulerOp_natMul]
    linear_combination (1 : PowerSeries ℚ) * h2
  · rw [E2s, E4s, E6s, sigS_one, sigS_three, sigS_five, eulerOp_sub, eulerOp_one, eulerOp_natMul]
    linear_combination (-1 : PowerSeries ℚ) * h3

end VOA.DeligneAudit.DeligneCharacter.D4MLDE

/-! ## The `RamanujanFormal` -/

namespace VOA.DeligneAudit.G2Star

open PowerSeries VOA.QSeries.JTP VOA.DeligneAudit.DeligneMLDE.Heat

theorem eisQ_eq (k : ℕ) (c : ℚ) (P : PowerSeries ℚ)
    (hP : ∀ n, coeff n P = (DeligneCharacter.sigmaK (k - 1) n : ℚ)) :
    eisQ k c = 1 + PowerSeries.C c * P := by
  refine PowerSeries.ext fun n => ?_
  rw [eisQ, coeff_mk, map_add, coeff_one, coeff_C_mul, hP]
  split_ifs with h <;> simp [h, sigmaK_zero]

/-- **the `RamanujanFormal`, proved.** -/
theorem ramanujanFormal : RamanujanFormal := by
  have hE := DeligneCharacter.D4MLDE.ramanujanIdentities
  have e2 : E2q = DeligneCharacter.D4MLDE.E2s := by
    rw [E2q, eisQ_eq 2 (-24) P1 coeff_P1, DeligneCharacter.D4MLDE.E2s,
      DeligneCharacter.D4MLDE.sigS_one, map_neg, map_ofNat]; ring
  have e4 : E4q = DeligneCharacter.D4MLDE.E4s := by
    rw [E4q, eisQ_eq 4 240 P3 coeff_P3, DeligneCharacter.D4MLDE.E4s,
      DeligneCharacter.D4MLDE.sigS_three, map_ofNat]
  have e6 : E6q = DeligneCharacter.D4MLDE.E6s := by
    rw [E6q, eisQ_eq 6 (-504) P5 coeff_P5, DeligneCharacter.D4MLDE.E6s,
      DeligneCharacter.D4MLDE.sigS_five, map_neg, map_ofNat]; ring
  exact ⟨by rw [e2, e4]; exact hE.e2, by rw [e2, e4, e6]; exact hE.e4⟩

end VOA.DeligneAudit.G2Star

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneMLDE.Heat.ramanujan6
#print axioms VOA.DeligneAudit.DeligneCharacter.D4MLDE.ramanujanIdentities
#print axioms VOA.DeligneAudit.G2Star.ramanujanFormal
end AxiomAudit
