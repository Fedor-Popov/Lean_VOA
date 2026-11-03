import VOA.Classification.COne.PlusRat3Gen

/-! # Further quadratic product certificates for the degree-two computations

Certified by the neutral evaluator (`decide +kernel`), all `m`:

* `H⁴₍ⱼ₎ω` (`j ≤ 3`) and `H⁶₍ⱼ₎ω` (`j ≤ 5`) as combinations of `L(-1)^k H^{2t}`;
* `L(1)H⁸`, `L(2)H⁴`, `L(2)H⁶`, `L(2)H⁸`;
* `L(2)ω = ½ 𝟙` (central charge one);
* `L(2)E = 0` (charged evaluator).
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat4
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusCharacterTable PlusSplitting
  PlusRatTelescope PlusZhuSchur PlusZhuNormalForms PlusResonantPairs PlusRatSign PlusRat2
  VOA.Huang.LogRemovalAdmissible ABDWeakAdmissible PlusRat3

/-- `H⁴₍ⱼ₎ω`. -/
def T4w : ℕ → List (ℚ × ℕ × ℕ)
  | 0 => [(1 / 2, 3, 1), (3, 1, 2)]
  | 1 => [(4 / 3, 2, 1), (4, 0, 2)]
  | 2 => [(7 / 3, 1, 1)]
  | 3 => [(2, 0, 1)]
  | _ => []

/-- `H⁶₍ⱼ₎ω`. -/
def T6w : ℕ → List (ℚ × ℕ × ℕ)
  | 0 => [(1 / 3, 5, 1), (15 / 4, 3, 2), (5, 1, 3)]
  | 1 => [(6 / 5, 4, 1), (21 / 2, 2, 2), (6, 0, 3)]
  | 2 => [(13 / 4, 3, 1), (39 / 2, 1, 2)]
  | 3 => [(6, 2, 1), (18, 0, 2)]
  | 4 => [(31 / 5, 1, 1)]
  | 5 => [(2, 0, 1)]
  | _ => []

theorem cert4w_0 : normR (polyActW H4R (-0 - 1) omR) = normR (combR (T4w 0)) := by decide +kernel
theorem cert4w_1 : normR (polyActW H4R (-1 - 1) omR) = normR (combR (T4w 1)) := by decide +kernel
theorem cert4w_2 : normR (polyActW H4R (-2 - 1) omR) = normR (combR (T4w 2)) := by decide +kernel
theorem cert4w_3 : normR (polyActW H4R (-3 - 1) omR) = normR (combR (T4w 3)) := by decide +kernel

theorem cert6w_0 : normR (polyActW H6R (-0 - 1) omR) = normR (combR (T6w 0)) := by decide +kernel
theorem cert6w_1 : normR (polyActW H6R (-1 - 1) omR) = normR (combR (T6w 1)) := by decide +kernel
theorem cert6w_2 : normR (polyActW H6R (-2 - 1) omR) = normR (combR (T6w 2)) := by decide +kernel
theorem cert6w_3 : normR (polyActW H6R (-3 - 1) omR) = normR (combR (T6w 3)) := by decide +kernel
theorem cert6w_4 : normR (polyActW H6R (-4 - 1) omR) = normR (combR (T6w 4)) := by decide +kernel
theorem cert6w_5 : normR (polyActW H6R (-5 - 1) omR) = normR (combR (T6w 5)) := by decide +kernel

theorem certL1H8 : normR (polyActW omR (-2 - 1) H8R) =
    normR (combR [(-1 / 2520, 5, 1), (-1 / 15, 3, 2), (-10 / 3, 1, 3)]) := by decide +kernel
theorem certL2H4 : normR (polyActW omR (-3 - 1) H4R) = normR (combR [(2, 0, 1)]) := by decide +kernel
theorem certL2H6 : normR (polyActW omR (-3 - 1) H6R) =
    normR (combR [(4 / 5, 2, 1), (18, 0, 2)]) := by decide +kernel
theorem certL2H8 : normR (polyActW omR (-3 - 1) H8R) =
    normR (combR [(13 / 140, 4, 1), (26 / 5, 2, 2), (60, 0, 3)]) := by decide +kernel
theorem certL2om : normR (polyActW omR (-3 - 1) omR) = normR [(1 / 2, [])] := by decide +kernel

variable (m : ℕ) (hm : 1 ≤ m)

theorem H4w_eq (j : ℕ) (hj : j < 4) :
    (V2mPlus m hm).smul (HP m hm 2) j (HP m hm 1) = combV m hm (T4w j) := by
  interval_cases j
  · exact smul_HP_eq m hm 2 1 (by norm_num) (by norm_num) 0 _ (by decide) cert4w_0
  · exact smul_HP_eq m hm 2 1 (by norm_num) (by norm_num) 1 _ (by decide) cert4w_1
  · exact smul_HP_eq m hm 2 1 (by norm_num) (by norm_num) 2 _ (by decide) cert4w_2
  · exact smul_HP_eq m hm 2 1 (by norm_num) (by norm_num) 3 _ (by decide) cert4w_3

theorem H6w_eq (j : ℕ) (hj : j < 6) :
    (V2mPlus m hm).smul (HP m hm 3) j (HP m hm 1) = combV m hm (T6w j) := by
  interval_cases j
  · exact smul_HP_eq m hm 3 1 (by norm_num) (by norm_num) 0 _ (by decide) cert6w_0
  · exact smul_HP_eq m hm 3 1 (by norm_num) (by norm_num) 1 _ (by decide) cert6w_1
  · exact smul_HP_eq m hm 3 1 (by norm_num) (by norm_num) 2 _ (by decide) cert6w_2
  · exact smul_HP_eq m hm 3 1 (by norm_num) (by norm_num) 3 _ (by decide) cert6w_3
  · exact smul_HP_eq m hm 3 1 (by norm_num) (by norm_num) 4 _ (by decide) cert6w_4
  · exact smul_HP_eq m hm 3 1 (by norm_num) (by norm_num) 5 _ (by decide) cert6w_5

theorem L1_H8 : (V2mPlus m hm).smul (HP m hm 1) 2 (HP m hm 4) =
    combV m hm [(-1 / 2520, 5, 1), (-1 / 15, 3, 2), (-10 / 3, 1, 3)] :=
  smul_HP_eq m hm 1 4 (by norm_num) (by norm_num) 2 _ (by decide) certL1H8

theorem L2_H4 : (V2mPlus m hm).smul (HP m hm 1) 3 (HP m hm 2) = combV m hm [(2, 0, 1)] :=
  smul_HP_eq m hm 1 2 (by norm_num) (by norm_num) 3 _ (by decide) certL2H4

theorem L2_H6 : (V2mPlus m hm).smul (HP m hm 1) 3 (HP m hm 3) =
    combV m hm [(4 / 5, 2, 1), (18, 0, 2)] :=
  smul_HP_eq m hm 1 3 (by norm_num) (by norm_num) 3 _ (by decide) certL2H6

theorem L2_H8 : (V2mPlus m hm).smul (HP m hm 1) 3 (HP m hm 4) =
    combV m hm [(13 / 140, 4, 1), (26 / 5, 2, 2), (60, 0, 3)] :=
  smul_HP_eq m hm 1 4 (by norm_num) (by norm_num) 3 _ (by decide) certL2H8

theorem hasN_vacuum : HasN m hm (V2mPlus m hm).vacuum vacR := hasPoly_vacuum m hm

/-- `L(2)ω = ½ 𝟙`. -/
theorem L2_omega : (V2mPlus m hm).smul (HP m hm 1) 3 (HP m hm 1) =
    (1 / 2 : ℂ) • (V2mPlus m hm).vacuum := by
  have h := eq_of_hasN m hm (hasN_smul_left m hm (hasN_HP m hm 1 le_rfl (by norm_num))
    (hasN_HP m hm 1 le_rfl (by norm_num)) 3) (hasN_smul m hm (hasN_vacuum m hm) (1 / 2))
    (by decide +kernel)
  rw [h]
  push_cast
  rfl

/-- `L(2) e^δ = 0`. -/
theorem L2_charge (δ : (latP m).carrier) :
    (V2m m hm).smul (latStateGen (latP m) (evR (a0 m) omR) 0) 3
      (latChargeGen (latP m) δ) = 0 := by
  rw [charge_eq_evRc m δ (chargeCoord (latP m) δ (a0 m)),
    V2m_smul_evRc m hm omR [(1, [])] 3 0 δ (by simp [wWtC]), ← evRc_normR]
  have h : normR (polyActC omR (-3 - 1) 0 [(1, [])]) = [] := by decide +kernel
  rw [h, evRc_nil]
  simp [latStateGen]

/-- `L(2)E = 0`. -/
theorem L2_E : (V2mPlus m hm).smul (V2mPlus m hm).conformalVector 3 (EP m hm) = 0 := by
  apply Subtype.ext
  rw [V2mPlus_smul_coe, omega_coe, EP_coe, PreVertexAlgebra.smul_add_right, L2_charge,
    L2_charge, add_zero]
  rfl

end VOA.Classification.COne.PlusRat4
