import VOA.Classification.COne.OrbPos6Charged

/-! # A literal charged-state restriction of the `OrbPos5` target -/

namespace VOA.Classification.COne.OrbPos6
open VOA VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet VOA.HeisenbergN
open OrbPos2 OrbPos3 OrbPos4 OrbPos5 LatMod TwistedReduction

theorem resc_chargeField_off {n : ℕ} (hn : 0 < n) (a j β e : ℤ)
    (he : (e - a * β) % (n : ℤ) ≠ 0) :
    rescFld hn (shiftedY_truncation hn a j (latChargeGen (latP 1) β)) e = 0 := by
  apply Subtype.ext
  funext t
  change shiftedY n a j (latChargeGen (latP 1) β) ((n : ℤ) * (-t - 1) + e) = 0
  rw [shiftedY_charge]
  apply fractionalChargeMode_support
  simpa only [show (n : ℤ) * (-t - 1) + e - a * β = (n : ℤ) * (-t - 1) + (e - a * β) by ring,
    Int.add_emod, Int.mul_emod_right, zero_add, Int.emod_emod] using he

theorem shiftedY_charge_smul_off (n : ℕ) (a j β γ ℓ k : ℤ)
    (hk : (k - a * (β + γ)) % (n : ℤ) ≠ 0) :
    shiftedY n a j ((V2m 1 le_rfl).smul (latChargeGen (latP 1) β) ℓ
      (latChargeGen (latP 1) γ)) k = 0 := by
  rw [charge_smul, map_smul, Pi.smul_apply, shiftedY_latState,
    sectorField_support n a j (β + γ) k _ hk, smul_zero]

/-- The charged identity also holds for every second residue class; the
incompatible classes vanish on both sides. -/
theorem charge_product_all_right_offsets {n : ℕ} (hn : 0 < n) (a j β γ e f ℓ s : ℤ)
    (he : (e - a * β) % (n : ℤ) = 0) (x : Space) :
    mode (Fld.prod ℓ
      (rescFld hn (shiftedY_truncation hn a j (latChargeGen (latP 1) β)) e)
      (rescFld hn (shiftedY_truncation hn a j (latChargeGen (latP 1) γ)) f)).1 s x =
    ∑ᶠ d : ℕ, cbinom ((e : ℂ) / n) d • shiftedY n a j
      ((V2m 1 le_rfl).smul (latChargeGen (latP 1) β) (ℓ + d)
        (latChargeGen (latP 1) γ)) ((n : ℤ) * (s - d) + e + f) x := by
  by_cases hf : (f - a * γ) % (n : ℤ) = 0
  · exact chargedProductFormula hn a j β γ e f he hf ℓ s x
  · rw [resc_chargeField_off hn a j γ f hf, prod_zero_right, mode_fld_zero]
    symm
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    rw [shiftedY_charge_smul_off n a j β γ (ℓ + d) _ (by
      simpa only [show (n : ℤ) * (s - d) + e + f - a * (β + γ) =
          (n : ℤ) * (s - d) + (e - a * β) + (f - a * γ) by ring,
        Int.add_emod, Int.mul_emod_right, he, Int.zero_emod, zero_add, Int.emod_emod] using hf),
      LinearMap.zero_apply, smul_zero]

theorem charge_eigen_residue {n : ℕ} (hn : 0 < n) (a β : ℤ) (r : ℕ)
    (hu : latChargeGen (latP 1) β ∈ (shiftAut n a).twistedEigenspace n r) :
    (-(r : ℤ) - a * β) % (n : ℤ) = 0 := by
  have he : shiftAut n a (latChargeGen (latP 1) β) =
      phase n (-(r : ℤ)) • latChargeGen (latP 1) β := by
    rw [Aut.twistedEigenspace, Module.End.mem_eigenspace_iff] at hu
    convert hu using 2
    simp only [phase, Int.cast_neg, Int.cast_natCast]
    congr 1
    ring
  rw [latChargeGen, shiftAut_latState] at he
  have hc : phase n (a * β) = phase n (-(r : ℤ)) :=
    (smul_left_injective ℂ (COne.latChargeGen_ne_zero 1 β)) he
  exact (phase_eq_iff hn _ _).mp hc.symm

/-- Exactly `ShiftedProductFormula` with both state quantifiers restricted
to lattice exponential states. The eigenspace and residue quantifiers are
unchanged. This proposition is weaker than the all-state target. -/
def ShiftedProductFormulaCharged {n : ℕ} (hn : 0 < n) (a j : ℤ) : Prop :=
  ∀ (r : ℕ) (β : ℤ), latChargeGen (latP 1) β ∈ (shiftAut n a).twistedEigenspace n r →
    ∀ (γ e : ℤ), 0 ≤ e → e < n → ∀ (ℓ s : ℤ) (x : Space),
    mode (Fld.prod ℓ
      (rescFld hn (shiftedY_truncation hn a j (latChargeGen (latP 1) β)) (-(r : ℤ)))
      (rescFld hn (shiftedY_truncation hn a j (latChargeGen (latP 1) γ)) e)).1 s x =
    ∑ᶠ d : ℕ, cbinom ((-(r : ℤ) : ℂ) / n) d • shiftedY n a j
      ((V2m 1 le_rfl).smul (latChargeGen (latP 1) β) (ℓ + d)
        (latChargeGen (latP 1) γ)) ((n : ℤ) * (s - d) - (r : ℤ) + e) x

theorem shiftedProductFormulaCharged_of_full {n : ℕ} (hn : 0 < n) (a j : ℤ)
    (h : ShiftedProductFormula hn a j) : ShiftedProductFormulaCharged hn a j :=
  fun r β hu γ e he0 hen ℓ s x =>
    h r (latChargeGen (latP 1) β) hu (latChargeGen (latP 1) γ) e he0 hen ℓ s x

/-- Unconditional proof of the literal charged-state restriction. -/
theorem shiftedProductFormulaCharged {n : ℕ} (hn : 0 < n) (a j : ℤ) :
    ShiftedProductFormulaCharged hn a j := by
  intro r β hu γ e _ _ ℓ s x
  simpa only [sub_eq_add_neg, Int.cast_neg] using
    charge_product_all_right_offsets hn a j β γ (-(r : ℤ)) e ℓ s
      (charge_eigen_residue hn a β r hu) x

end VOA.Classification.COne.OrbPos6
