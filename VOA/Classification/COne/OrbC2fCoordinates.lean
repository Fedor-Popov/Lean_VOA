import VOA.Classification.COne.OrbC2fCubic

/-! # Identification of the current-coordinate cubic generators -/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbC2f
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  MvPolynomial VOA.SparseRational PlusC2Eval PlusUnitary PlusC2 LatMod OrbC2c OrbC2e

local notation "W" => latticeVOAGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)
local notation "e" => latChargeGen (latP 1) (1 : ℤ)
local notation "f" => latChargeGen (latP 1) (-1 : ℤ)
local notation "h" => hSt (latP 1) (1 : ℤ)

theorem cubicE_eq_charges : cubicE =
    latChargeGen (latP 1) (2 : ℤ) + latChargeGen (latP 1) (-2 : ℤ) := by
  have hp := V2m_charge_smul_charge 1 le_rfl (1 : ℤ) (1 : ℤ) (-3)
  have hn := V2m_charge_smul_charge 1 le_rfl (-1 : ℤ) (-1 : ℤ) (-3)
  norm_num [latP_form, PlusCharacterTable.rankOne_cocycle, schurR,
    evRc_cons, evRc_nil, evalWordC_nil] at hp hn
  exact congrArg₂ (· + ·) hp hn

theorem cubicJ_current : cubicJ = (-3 : ℂ) • (W).smul h (-3) h +
    (3 : ℂ) • ((W).smul e (-3) f + (W).smul f (-3) e) := by
  simp only [cubicJ, cubicE, map_add, Aut.map_smul, rotC_e, rotC_f,
    PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_right,
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq]

theorem hSt_one_eq : h = cα 1 • ls 1 [(1,[0])] := by
  rw [hSt, WpC2.vSchur_one', vVar_rankOne, latStateGen_csmul]
  congr 1
  simp [ls, evR_cons, evR_nil, evalWord_cons, evalWord_nil]

theorem current_h_three_h : (W).smul h (-3) h = ls 1 [(2,[2,0])] := by
  rw [hSt_one_eq, PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right,
    smul_smul, cα_sq 1 le_rfl]
  have hh := V2m_smul_evR_W 1 le_rfl [(1,[0])] (-3) [(1,[0])]
  change (W).smul (ls 1 [(1,[0])]) (-3) (ls 1 [(1,[0])]) =
    ls 1 (polyActW [(1,[0])] 2 [(1,[0])]) at hh
  rw [hh]
  have hc : normR (polyActW [(1,[0])] 2 [(1,[0])]) = normR [(1,[2,0])] := by decide +kernel
  rw [← ls_normR, hc, ls_normR]
  norm_num only [Nat.cast_one, mul_one]
  simpa only [scaleR, List.map_cons, List.map_nil, mul_one, Rat.cast_ofNat] using
    (ls_scaleR 1 2 [(1,[2,0])]).symm

theorem current_opposite_three : (W).smul e (-3) f + (W).smul f (-3) e =
    ls 1 (scaleR (1/3) JR ++ [(2,[2,0])]) := by
  have hp := V2m_charge_smul_charge 1 le_rfl (1 : ℤ) (-1 : ℤ) (-3)
  have hn := V2m_charge_smul_charge 1 le_rfl (-1 : ℤ) (1 : ℤ) (-3)
  norm_num only [latP_form, ci, PlusCharacterTable.rankOne_cocycle, one_smul,
    Int.cast_ofNat, Int.cast_neg, Int.cast_one, mul_one, mul_neg, neg_mul,
    neg_neg, sub_neg_eq_add, add_neg_cancel, neg_add_cancel] at hp hn
  change (V2m 1 le_rfl).smul e (-3) f + (V2m 1 le_rfl).smul f (-3) e = _
  rw [hp, hn]
  have hcn : chargeCoord (latP 1) ((-1 : ℤ) : (latP 1).carrier) (a0 1) = -cα 1 :=
    OrbC2e.chargeCoord_neg (latP 1) (1 : ℤ) (a0 1)
  change latStateGen (latP 1) (evRc (a0 1) (cα 1) (schurR 4)) (0 : ℤ) +
    latStateGen (latP 1) (evRc (a0 1) (chargeCoord (latP 1) (-1 : ℤ) (a0 1))
      (schurR 4)) (0 : ℤ) = _
  rw [hcn, ← evRc_negChargeR, ← latStateGen_add_boson, ← evRc_append]
  have hc : normR (reduceR 2 (schurR 4 ++ negChargeR (schurR 4))) =
      normR (liftR (scaleR (1/3) JR ++ [(2,[2,0])])) := by decide +kernel
  have he := congrArg (evRc (a0 1) (cα 1)) hc
  rw [evRc_normR, evRc_reduceR, evRc_normR, evRc_liftR] at he
  · exact congrArg (fun p => latStateGen (latP 1) p 0) he
  · convert cα_sq 1 le_rfl using 1
    norm_num

/-- The neutral current expression is exactly the certified J. -/
theorem cubicJ_eq_neutral : cubicJ = ls 1 JR := by
  rw [cubicJ_current, current_h_three_h, current_opposite_three, ls_append, ls_scaleR]
  push_cast
  module

end VOA.Classification.COne.OrbC2f
