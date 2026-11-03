import VOA.Classification.COne.OrbPos5Module
import VOA.Moonshine.HeisenbergTwistedModuleFieldComm
import VOA.Modules.Translation

/-!
# Products of the rescaled charged fields

The ordinary module iterate identity and the integral monomial product rule
give an explicit formula for the left side of the shifted product identity.
The shift convention is that of `OrbPos5`: momentum `k+j/2-a/(2n)`.
-/

set_option maxSynthPendingDepth 3

namespace VOA.Classification.COne.OrbPos6
open VOA VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet VOA.HeisenbergN
open OrbPos2 OrbPos3 OrbPos4 OrbPos5 LatMod TwistedReduction

noncomputable def ordinaryField (j : ℤ) (u : Space) : Fld Space :=
  ⟨(latticeModule 1 le_rfl j).YM u, by
    intro x
    obtain ⟨K, hK⟩ := (latticeModule 1 le_rfl j).truncation u x
    refine ⟨-K - 1, fun t ht => ?_⟩
    have h := hK (-t - 1) (by omega)
    simpa only [mode_apply, show -(-t - 1) - 1 = t by omega] using h⟩

theorem ordinaryField_prod (j ℓ : ℤ) (u v : Space) :
    Fld.prod ℓ (ordinaryField j u) (ordinaryField j v) =
      ordinaryField j ((V2m 1 le_rfl).smul u ℓ v) := by
  apply fld_ext_mode
  intro s x
  rw [Fld.mode_prod_iterate]
  symm
  rw [show (ordinaryField j ((V2m 1 le_rfl).smul u ℓ v)).1 =
    (latticeModule 1 le_rfl j).YM ((V2m 1 le_rfl).smul u ℓ v) from rfl,
    module_iterate0]
  rw [finsum_int_eq_finsum_nat _ (fun i hi => by
    rw [cbz_apply_neg ℓ hi, mul_zero, zero_smul])]
  apply finsum_congr
  intro i
  rw [negOnePow_natCast, cbz_apply_nonneg _ (Int.natCast_nonneg i),
    Int.toNat_natCast, negOnePow_eq_zpow']
  rfl

theorem resc_chargeField {n : ℕ} (hn : 0 < n) (a j β e : ℤ)
    (he : (e - a * β) % (n : ℤ) = 0) :
    rescFld hn (shiftedY_truncation hn a j (latChargeGen (latP 1) β)) e =
      fzmul ((e - a * β) / (n : ℤ)) (ordinaryField j (latChargeGen (latP 1) β)) := by
  apply Subtype.ext
  change resc (shiftedY n a j (latChargeGen (latP 1) β)) n e = _
  have hc : shiftedY n a j (latChargeGen (latP 1) β) =
      coefficientField n a j β 0 1 := by
    rw [latChargeGen, shiftedY_latState]
    change (Finsupp.lsum ℂ (coefficientField n a j β)) (deltaCoeffs _ 1) = _
    rw [deltaCoeffs_one, Finsupp.lsum_single]
  rw [hc, resc_coefficientField hn, if_pos he]
  simp only [Nat.cast_zero, sub_zero]
  rfl

/-- All integral products of the rescaled exponentials, expressed using the
ordinary lattice iterate. This is the product side, not yet its identification
with the full shifted iterate on oscillator descendants. -/
theorem charge_product_ordinary {n : ℕ} (hn : 0 < n) (a j β γ e f ℓ s : ℤ)
    (he : (e - a * β) % (n : ℤ) = 0) (hf : (f - a * γ) % (n : ℤ) = 0) (x : Space) :
    mode (Fld.prod ℓ
      (rescFld hn (shiftedY_truncation hn a j (latChargeGen (latP 1) β)) e)
      (rescFld hn (shiftedY_truncation hn a j (latChargeGen (latP 1) γ)) f)).1 s x =
      ∑ᶠ d : ℕ, gBinom ((e - a * β) / (n : ℤ)) d •
        mode ((latticeModule 1 le_rfl j).YM
          ((V2m 1 le_rfl).smul (latChargeGen (latP 1) β) (ℓ + d)
            (latChargeGen (latP 1) γ)))
          ((e - a * β) / (n : ℤ) + ((f - a * γ) / (n : ℤ) + s) - d) x := by
  rw [resc_chargeField hn a j β e he, resc_chargeField hn a j γ f hf,
    prod_fzmul_right, mode_fzmul]
  have hloc : Local (ordinaryField j (latChargeGen (latP 1) β)).1
      (ordinaryField j (latChargeGen (latP 1) γ)).1 :=
    Moonshine.VnatBlock.local_YM (latticeModule 1 le_rfl j).toWeakModule
      (latChargeGen (latP 1) β) (latChargeGen (latP 1) γ)
  rw [mode_prod_fzmul_left hloc]
  apply finsum_congr
  intro d
  rw [ordinaryField_prod, add_comm s ((f - a * γ) / (n : ℤ))]
  rfl

end VOA.Classification.COne.OrbPos6
