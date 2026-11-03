import VOA.Classification.COne.OrbRat6Twist

/-! # Reducing the twisted separation to a Heisenberg zero mode

`sig aT = c₀ v₀ + c₃ v₃ + c₆ v₆` with `c₃ = −20√3 i/3` (`sig_aT`, the other spin-3 components
vanish).  Pulled back to `V₁₈`: `iotaW aT = c₀' e^{α'} + c₃ A₃ + c₆' e^{−α'}` where `A₃` is the
Heisenberg state with `scaleMorph A₃ = v₃` (`A3`).  The charged parts have zero modes vanishing on
the tops `e^{λ_j}` (`|j| < 9`), so

  `topVal j = c₃ · heisVal j`,  `heisVal j` = eigenvalue of `o(A₃)` on `e^{λ_j}`

(`topVal_eq`), and the twisted separation reduces to `HeisenbergTopSeparation`.
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

noncomputable section

namespace VOA.Classification.COne.OrbRat6

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod Complex
  MvPolynomial VOA.LatGen.Screen OrbC2b OrbRat2 OrbRat5 VertexOperatorAlgebra ConverseUniverse
  PlusSplitting PlusRational ABDWeakAdmissible VOA.Huang.LogRemovalAdmissible PlusUnitary

theorem s3_pow9 : s3 ^ 9 = 81 * s3 := by rw [pow_succ, s3_pow8]
theorem s3_pow10 : s3 ^ 10 = 243 := by rw [pow_succ, s3_pow9]; ring_nf; rw [s3_sq]; norm_num
theorem s3_pow11 : s3 ^ 11 = 243 * s3 := by rw [pow_succ, s3_pow10]
theorem s3_pow12 : s3 ^ 12 = 729 := by rw [pow_succ, s3_pow11]; ring_nf; rw [s3_sq]; norm_num

def c0T : ℂ := (-100 / 3 + 20 * s3) + I * (-100 / 3 + 20 * s3)
def c3T : ℂ := -20 * s3 * I / 3
def c6T : ℂ := (10 + 6 * s3) + I * (-6 * s3 - 10)

theorem c3T_ne : c3T ≠ 0 := by
  unfold c3T
  have := s3_ne
  intro h
  have h2 : s3 * I = 0 := by linear_combination (-3 / 20) * h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact s3_ne h3
  · exact I_ne_zero h3

/-- `sig aT` in the spin-3 basis. -/
theorem sig_aT : sig aT = R7 c0T 0 0 c3T 0 0 c6T := by
  rw [aT, sig, Aut.mul_apply, expF_R7', expE_R7', eps1_eq_one]
  apply R7_congr <;>
  · try simp only [c0T, c3T, c6T]
    ring_nf
    try simp only [I_sq, I_pow_three, I_pow_four, I_pow_five, I_pow_six, I_pow_seven, Ipow8,
      Ipow9, Ipow10, Ipow11, Ipow12, s3_sq, s3_pow3, s3_pow4, s3_pow5, s3_pow6, s3_pow7, s3_pow8,
      s3_pow9,
      s3_pow10, s3_pow11, s3_pow12]
    ring_nf
    try simp only [I_sq, I_pow_three, I_pow_four, I_pow_five, I_pow_six, I_pow_seven, Ipow8,
      Ipow9, Ipow10, Ipow11, Ipow12, s3_sq, s3_pow3, s3_pow4, s3_pow5, s3_pow6, s3_pow7, s3_pow8,
      s3_pow9,
      s3_pow10, s3_pow11, s3_pow12]
    try ring_nf

theorem bar_aW : bar aW = aT := rfl

/-! ## The Heisenberg state `A₃` -/

theorem vv3_fixed : charU 1 le_rfl zU (vv 3) = vv 3 := by
  have h := vv_bigrad 3
  rw [charU_bigrad zU h]
  try norm_num [ci]

theorem vv3_range : vv 3 ∈ LinearMap.range sm := mem_range_sm vv3_fixed

/-- The `V₁₈` Heisenberg state with `scaleMorph A₃ = v₃`. -/
def A3 : Sp9 := vv3_range.choose

theorem sm_A3 : sm A3 = vv 3 := vv3_range.choose_spec

theorem sm_L0 (x : Sp9) : sm (V18.L 0 x) = V1.L 0 (sm x) :=
  voaHom_map_L sm_hom (scaleMorph_omega 1 le_rfl 3) 0 x

theorem A3_grading : A3 ∈ V18.grading 9 := by
  have h : sm (V18.L 0 A3) = sm (((9 : ℤ) : ℂ) • A3) := by
    rw [sm_L0, sm_A3, map_smul, sm_A3, V1.L_zero_grading _ (vv_grading 3 (by norm_num))]
    try push_cast
  exact mem_grading_of_L0 V18 (scaleMorph_injective 1 le_rfl 3 h)

theorem sm_charge (k : ℤ) :
    sm (latChargeGen (latP (1 * 3 ^ 2)) k) =
      latCob (latP (1 * 3 ^ 2)) (latP 1) (scaleIota 1 3) k •
        latChargeGen (latP 1) (scaleIota 1 3 k) := by
  show latMorphC (latP (1 * 3 ^ 2)) (latP 1) (scaleIota 1 3)
    (latCob (latP (1 * 3 ^ 2)) (latP 1) (scaleIota 1 3)) (latChargeGen (latP (1 * 3 ^ 2)) k) = _
  rw [latMorphC_latChargeGen]

theorem scaleIota_one : scaleIota 1 3 (1 : ℤ) = (3 : ℤ) := by
  show ((3 : ℕ) : ℤ) * (1 : ℤ) = 3; norm_num

theorem scaleIota_neg_one : scaleIota 1 3 (-1 : ℤ) = (-3 : ℤ) := by
  show ((3 : ℕ) : ℤ) * (-1 : ℤ) = -3; norm_num

theorem vv6_line : ∃ d : ℂ, vv 6 = d • latStateGen (latP 1) 1 (-3 : ℤ) := by
  have h : vv 6 ∈ Sd (-3) 0 := by
    have := vv_bigrad 6
    convert this using 2 <;> norm_num
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp (Sd_zero (-3) h)
  exact ⟨d, hd.symm⟩

theorem latCob_ne' (k : ℤ) : latCob (latP (1 * 3 ^ 2)) (latP 1) (scaleIota 1 3) k ≠ 0 :=
  latCob_ne_zero _ _ _ _

/-- The decomposition of `iotaW aT`. -/
theorem iotaW_aW_decomp : ∃ a b : ℂ,
    iotaW aW = a • latChargeGen (latP (1 * 3 ^ 2)) (1 : ℤ) + c3T • A3 +
      b • latChargeGen (latP (1 * 3 ^ 2)) (-1 : ℤ) := by
  obtain ⟨d, hd⟩ := vv6_line
  refine ⟨c0T * (latCob (latP (1 * 3 ^ 2)) (latP 1) (scaleIota 1 3) (1 : ℤ))⁻¹,
    c6T * d * (latCob (latP (1 * 3 ^ 2)) (latP 1) (scaleIota 1 3) (-1 : ℤ))⁻¹, ?_⟩
  apply scaleMorph_injective 1 le_rfl 3
  change sm _ = sm _
  rw [sm_iotaW, bar_aW, sig_aT, map_add, map_add, map_smul, map_smul, map_smul, sm_A3,
    sm_charge, sm_charge, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ (latCob_ne' (1 : ℤ)),
    mul_assoc, mul_assoc, inv_mul_cancel₀ (latCob_ne' (-1)), mul_one, mul_one, R7]
  rw [scaleIota_one, scaleIota_neg_one,
    show latChargeGen (latP 1) (-3 : ℤ) = latStateGen (latP 1) 1 (-3 : ℤ) from rfl,
    ← smul_smul, ← hd, vv_zero]
  simp only [zero_smul, add_zero]

theorem charged_top_zero {j : ℤ} (hj9 : |j| < 9) (k : ℤ) (hk : k = 1 ∨ k = -1) :
    mode ((Nj j).YM (latChargeGen (latP (1 * 3 ^ 2)) k)) 8 top9 = 0 := by
  have h := latticeModule_latChargeGen (1 * 3 ^ 2) (one_le_mn2 1 le_rfl 3) j k 0 (-8 - 1) 1
  change mode ((Nj j).YM (latChargeGen (latP (1 * 3 ^ 2)) k)) 8
    (latStateGen (latP (1 * 3 ^ 2)) 1 (0 : ℤ)) = 0
  rw [mode_apply, h]
  have hj1 : -9 < j := by rw [abs_lt] at hj9; exact hj9.1
  have hj2 : j < 9 := by rw [abs_lt] at hj9; exact hj9.2
  rw [show (1 : FockN _) = vacuumN _ from rfl, EEVec_vacuum, if_neg (by
    rcases hk with rfl | rfl <;> push_cast <;> omega)]
  simp [latStateGen]

/-! ## The Heisenberg eigenvalue -/

theorem A3_line {j : ℤ} (hj9 : |j| < 9) :
    ∃ c : ℂ, mode ((Nj j).YM A3) 8 top9 = c • top9 := by
  have hx := mode_mem_weight (Nj j) A3_grading (top9_mem j) 8
  rw [show hj j + ((9 : ℤ) : ℂ) - ((8 : ℤ) : ℂ) - 1 = hj j by push_cast; ring] at hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (Nj_weight_top hj9 hx)
  exact ⟨c, hc.symm⟩

/-- The eigenvalue of `o(A₃)` on `e^{λ_j}`. -/
def heisVal (j : ℤ) : ℂ := if hj9 : |j| < 9 then (A3_line hj9).choose else 0

theorem heisVal_spec {j : ℤ} (hj9 : |j| < 9) :
    mode ((Nj j).YM A3) 8 top9 = heisVal j • top9 := by
  rw [heisVal, dif_pos hj9]
  exact (A3_line hj9).choose_spec

/-- `topVal j = c₃ · heisVal j`. -/
theorem topVal_eq {j : ℤ} (hj9 : |j| < 9) : topVal j = c3T * heisVal j := by
  obtain ⟨a, b, hab⟩ := iotaW_aW_decomp
  have h := topVal_spec hj9
  rw [hab, map_add, map_add, map_smul, map_smul, map_smul] at h
  change (a • mode ((Nj j).YM _) 8 top9 + c3T • mode ((Nj j).YM A3) 8 top9) +
    b • mode ((Nj j).YM _) 8 top9 = _ at h
  rw [charged_top_zero hj9 (1 : ℤ) (Or.inl rfl), charged_top_zero hj9 (-1 : ℤ) (Or.inr rfl),
    heisVal_spec hj9, smul_zero, smul_zero, zero_add, add_zero, smul_smul] at h
  have h2 := sub_eq_zero.mpr h
  rw [← sub_smul] at h2
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact (sub_eq_zero.mp h3).symm
  · exact absurd h3 top9_ne

/-- OPEN: the Heisenberg state `A₃` separates `e^{λ_j}` and `e^{λ_{−j}}`. -/
def HeisenbergTopSeparation : Prop :=
  ∀ j ∈ ({1, 2, 4, 5, 7, 8} : Finset ℤ), heisVal j ≠ heisVal (-j)

theorem twistedTopSeparation_of_heis (h : HeisenbergTopSeparation) : TwistedTopSeparation := by
  intro j hj
  have hall : ∀ x ∈ ({1, 2, 4, 5, 7, 8} : Finset ℤ), |x| < 9 := by decide
  have hj9 := hall j hj
  have hj9' : |(-j)| < 9 := by rwa [abs_neg]
  rw [topVal_eq hj9, topVal_eq hj9']
  intro heq
  exact h j hj (mul_left_cancel₀ c3T_ne heq)

/-- The six twisted pairs, reduced to the Heisenberg separation. -/
theorem cubicTwistedDoubledPairs_of_heis (h : HeisenbergTopSeparation) :
    CubicTwistedDoubledPairs :=
  cubicTwistedDoubledPairs_of_sep (twistedTopSeparation_of_heis h)

end VOA.Classification.COne.OrbRat6
