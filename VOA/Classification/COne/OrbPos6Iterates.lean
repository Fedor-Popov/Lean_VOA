import VOA.Classification.COne.OrbPos6Products
import VOA.Classification.COne.OrbPos6Schur
import VOA.Moonshine.LatticeTwistedUntwisted

/-! # The Δ-corrected charged iterates -/

namespace VOA.Classification.COne.OrbPos6
open VOA VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet VOA.HeisenbergN
open OrbPos2 OrbPos3 OrbPos4 OrbPos5 LatMod TwistedReduction

theorem coefficientField_recover {n : ℕ} (hn : 0 < n) (a j β k : ℤ)
    (d : ℕ) (p : Osc) :
    coefficientField n a j β d p ((n : ℤ) * k + a * β) =
      mode ((latticeModule 1 le_rfl j).YM (latStateGen (latP 1) p β)) (k - d) := by
  have hn0 : (n : ℤ) ≠ 0 := by omega
  simp only [coefficientField, LinearMap.coe_mk, AddHom.coe_mk, add_sub_cancel_right,
    Int.mul_emod_right, ite_true, Int.mul_ediv_cancel_left _ hn0]

/-- The constructed fields on every Schur descendant, including all Δ terms. -/
theorem shiftedY_schur {n : ℕ} (hn : 0 < n) (a j β γ k : ℤ) (N : ℕ) :
    shiftedY n a j (latStateGen (latP 1) (vSchur (latP 1) β N) γ)
      ((n : ℤ) * k + a * γ) =
      ∑ q ∈ Finset.range (N + 1), cbinom (-(a : ℂ) * β / n) q •
        mode ((latticeModule 1 le_rfl j).YM
          (latStateGen (latP 1) (vSchur (latP 1) β (N - q)) γ)) (k - q) := by
  rw [shiftedY_latState]
  change ((Finsupp.lsum ℂ (coefficientField n a j γ))
    (deltaCoeffs ((a : ℂ) / (2 * n)) (vSchur (latP 1) β N))) _ = _
  rw [deltaCoeffs_vSchur, map_sum]
  simp only [Finset.sum_apply, Finsupp.lsum_single, map_smul, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro q hq
  rw [coefficientField_recover hn]
  congr 2
  ring

theorem charge_smul (β γ ℓ : ℤ) :
    (V2m 1 le_rfl).smul (latChargeGen (latP 1) β) ℓ (latChargeGen (latP 1) γ) =
      latticeCocycle (latP 1) β γ • latStateGen (latP 1)
        (if 0 ≤ -ℓ - 1 - (2 * β * γ) then vSchur (latP 1) β (-ℓ - 1 - (2 * β * γ)).toNat else 0)
        (β + γ) := by
  simpa only [latP_form] using
    Moonshine.LatticeTwisted.smul_echg_echg (latP 1) (latP_even 1)
      (latP_posDef 1 le_rfl) β γ ℓ

theorem charge_smul_zero (β γ ℓ : ℤ) (h : -(2 * β * γ) ≤ ℓ) :
    (V2m 1 le_rfl).smul (latChargeGen (latP 1) β) ℓ
      (latChargeGen (latP 1) γ) = 0 := by
  rw [charge_smul, if_neg (by omega), latStateGen_zero_boson, smul_zero]

/-- The complete Δ correction on the ordinary product of any two exponential
states, at every product index. This is a finite binomial convolution. -/
theorem shiftedY_charge_smul {n : ℕ} (hn : 0 < n) (a j β γ ℓ k : ℤ)
    (x : Space) :
    shiftedY n a j
      ((V2m 1 le_rfl).smul (latChargeGen (latP 1) β) ℓ (latChargeGen (latP 1) γ))
      ((n : ℤ) * k + a * (β + γ)) x =
      ∑ᶠ q : ℕ, cbinom (-(a : ℂ) * β / n) q •
        mode ((latticeModule 1 le_rfl j).YM
          ((V2m 1 le_rfl).smul (latChargeGen (latP 1) β) (ℓ + q)
            (latChargeGen (latP 1) γ))) (k - q) x := by
  by_cases hhigh : -(2 * β * γ) ≤ ℓ
  · rw [charge_smul_zero β γ ℓ hhigh, map_zero]
    symm
    apply finsum_eq_zero_of_forall_eq_zero
    intro q
    rw [charge_smul_zero β γ (ℓ + q) (by omega), map_zero, mode_zero,
      LinearMap.zero_apply, smul_zero]
  · let N := (-ℓ - 1 - (2 * β * γ)).toNat
    have hN : (N : ℤ) = -ℓ - 1 - (2 * β * γ) := Int.toNat_of_nonneg (by omega)
    have hsource (q : ℕ) (hq : q ≤ N) :
        (V2m 1 le_rfl).smul (latChargeGen (latP 1) β) (ℓ + q)
          (latChargeGen (latP 1) γ) =
        latticeCocycle (latP 1) β γ •
          latStateGen (latP 1) (vSchur (latP 1) β (N - q)) (β + γ) := by
      rw [charge_smul, if_pos (by omega)]
      congr 3
      omega
    rw [finsum_nat_eq_sum_range (N + 1) _ (fun q hq => by
      rw [charge_smul_zero β γ (ℓ + q) (by omega), map_zero, mode_zero,
        LinearMap.zero_apply, smul_zero])]
    rw [show ℓ = ℓ + (0 : ℕ) by simp, hsource 0 (Nat.zero_le _)]
    simp only [Nat.cast_zero, add_zero, Nat.sub_zero, map_smul, Pi.smul_apply, LinearMap.smul_apply]
    rw [shiftedY_schur hn, LinearMap.sum_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [hsource q (by have := Finset.mem_range.mp hq; omega)]
    simp only [map_smul, mode_smul, LinearMap.smul_apply]
    exact smul_comm _ _ _

end VOA.Classification.COne.OrbPos6
