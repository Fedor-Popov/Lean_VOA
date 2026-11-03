import VOA.Classification.COne.PlusRatTelescope
import VOA.Classification.COne.PlusSplitZhuSchur

/-! # The E-telescope on the sign top

In the sign module `V_L^-` (top vector `u = α(-1)𝟙`), with `E = e^α + e^{-α}` and `J = 2m-2`:
`E_n u = 0` for `n ≥ 1`, `E_0 u = -c(e^α - e^{-α})` and `E_J(e^α - e^{-α}) = -2c u`, where `c`
is the charge coordinate of `α`.  Hence the telescoping sum of `PlusRatTelescope` equals
`2c² u ≠ 0` on the sign top.  This is the computation that separates `V_{2m}⁺` from `M(1)⁺`
(for which a non-split extension of the vacuum by the sign sector does exist).
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusRatSign
open VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
open PlusUnitary PlusC2 PlusCharacterTable PlusSplitting PlusRatTelescope LatMod PlusZhuSchur

variable (m : ℕ) (hm : 1 ≤ m)

/-- The charge coordinate of the generator `α`. -/
abbrev cc : ℂ := chargeCoord (latP m) ((1 : ℤ) : (latP m).carrier) (a0 m)

include hm in
theorem cc_ne_zero : cc m ≠ 0 := by
  have := chargeCoord_nat_ne_zero m hm 1 le_rfl
  simpa [cc] using this

theorem chargeCoord_negOne :
    chargeCoord (latP m) ((-1 : ℤ) : (latP m).carrier) (a0 m) = -cc m :=
  chargeCoord_neg (latP m) ((1 : ℤ) : (latP m).carrier) (a0 m)

/-- The zero boson mode reads the charge. -/
theorem boson_zero_charge (a : (latP m).carrier) :
    (V2m m hm).smul (bosonState (latP m) (a0 m)) 0 (latChargeGen (latP m) a) =
      chargeCoord (latP m) a (a0 m) • latChargeGen (latP m) a := by
  rw [V2m, latChargeGen, smul_bosonState_latStateGen, if_pos rfl, oscN_zero]
  simp [latStateGen]

/-- `e^a_0 (α(-1)𝟙) = -c_a e^a`, by skew symmetry. -/
theorem charge_zero_boson (a : (latP m).carrier) :
    (V2m m hm).smul (latChargeGen (latP m) a) 0 (bosonState (latP m) (a0 m)) =
      -(chargeCoord (latP m) a (a0 m) • latChargeGen (latP m) a) := by
  rw [VertexOperatorAlgebra.skew_mode, finsum_eq_single _ 0]
  · have h0 : (V2m m hm).Y (bosonState (latP m) (a0 m)) (-0 - 1 - ((0 : ℕ) : ℤ))
        (latChargeGen (latP m) a) = chargeCoord (latP m) a (a0 m) • latChargeGen (latP m) a := by
      rw [show (-0 - 1 - ((0 : ℕ) : ℤ)) = -(0 : ℤ) - 1 by ring]
      exact boson_zero_charge m hm a
    rw [h0]
    simp [sgn]
  · intro j hj
    have he : (V2m m hm).Y (bosonState (latP m) (a0 m)) (-0 - 1 - (j : ℤ))
        (latChargeGen (latP m) a) = 0 := by
      rw [show -0 - 1 - (j : ℤ) = -(j : ℤ) - 1 by ring]
      exact boson_positive_charge m hm a j (by omega)
    rw [he, map_zero, smul_zero, smul_zero]

/-- `E_n u = 0` for `n ≥ 1`. -/
theorem E_pos_sign (n : ℤ) (hn : 0 < n) :
    (V2m m hm).smul ((EP m hm : VP m hm) : LatModuleGen (latP m)) n
      (bosonState (latP m) (a0 m)) = 0 := by
  rw [EP_coe, PreVertexAlgebra.smul_add_left, charge_positive_boson m hm _ _ hn,
    charge_positive_boson m hm _ _ hn, zero_add]

/-- `E_0 u = -c(e^α - e^{-α})`. -/
theorem E_zero_sign :
    (V2m m hm).smul ((EP m hm : VP m hm) : LatModuleGen (latP m)) 0
      (bosonState (latP m) (a0 m)) =
      -(cc m • latChargeGen (latP m) ((1 : ℤ) : (latP m).carrier)) +
        cc m • latChargeGen (latP m) ((-1 : ℤ) : (latP m).carrier) := by
  rw [EP_coe, PreVertexAlgebra.smul_add_left, charge_zero_boson, charge_zero_boson,
    chargeCoord_negOne, neg_smul, neg_neg]

/-- `S_1(a) ⊗ e^0 = c_a u`. -/
theorem schur_one_state (a : (latP m).carrier) :
    latStateGen (latP m) (vSchur (latP m) a 1) 0 =
      chargeCoord (latP m) a (a0 m) • bosonState (latP m) (a0 m) := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, vSchur_succ]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.sub_zero, vSchur_zero, mul_one,
    zero_add, Nat.cast_zero, inv_one, one_smul]
  rw [vVar_rankOne, latStateGen_csmul]
  rfl

/-- `E_{2m-2} e^{±α} = S_1(∓α) ⊗ e^0`. -/
theorem E_top_charge (a : ℤ) (ha : a = 1 ∨ a = -1) :
    (V2m m hm).smul ((EP m hm : VP m hm) : LatModuleGen (latP m)) ((2 * m - 2 : ℕ) : ℤ)
      (latChargeGen (latP m) a) =
      latStateGen (latP m) (vSchur (latP m) (-a) 1) 0 := by
  have hi : (((2 * m - 1 : ℕ) : ℤ) - 1) = ((2 * m - 2 : ℕ) : ℤ) := by
    have : 2 * m - 1 = (2 * m - 2) + 1 := by omega
    rw [this]; push_cast; ring
  have h2 : 2 * m - (2 * m - 1) = 1 := by omega
  rw [EP_coe, PreVertexAlgebra.smul_add_left, ← hi]
  rcases ha with rfl | rfl
  · rw [charge_same m hm (2 * m - 1) 1 (Or.inl rfl), zero_add]
    have hn := charge_opposite m hm (2 * m - 1) (by omega) (-1) (Or.inr rfl)
    norm_num only [neg_neg] at hn
    rw [hn, h2]
  · rw [charge_same m hm (2 * m - 1) (-1) (Or.inr rfl), add_zero]
    have hn := charge_opposite m hm (2 * m - 1) (by omega) 1 (Or.inl rfl)
    rw [hn, h2]
    norm_num

/-- `E_{2m-2} E_0 u = 2c² u`. -/
theorem E_top_E_zero_sign :
    (V2m m hm).smul ((EP m hm : VP m hm) : LatModuleGen (latP m)) ((2 * m - 2 : ℕ) : ℤ)
      ((V2m m hm).smul ((EP m hm : VP m hm) : LatModuleGen (latP m)) 0
        (bosonState (latP m) (a0 m))) =
      ((2 : ℂ) * cc m ^ 2) • bosonState (latP m) (a0 m) := by
  have e1 := E_top_charge m hm 1 (Or.inl rfl)
  have e2 := E_top_charge m hm (-1) (Or.inr rfl)
  rw [PreVertexAlgebra.smul_def] at e1 e2
  rw [E_zero_sign, PreVertexAlgebra.smul_def, map_add, map_neg, map_smul, map_smul]
  erw [e1, e2]
  rw [schur_one_state, schur_one_state]
  have h1 : chargeCoord (latP m) ((-(1 : ℤ) : ℤ) : (latP m).carrier) (a0 m) = -cc m :=
    chargeCoord_negOne m
  have h2 : chargeCoord (latP m) ((-(-1 : ℤ) : ℤ) : (latP m).carrier) (a0 m) = cc m := by
    norm_num
  rw [h1, h2, smul_smul, smul_smul, ← neg_smul, ← add_smul]
  congr 1
  ring

end VOA.Classification.COne.PlusRatSign
