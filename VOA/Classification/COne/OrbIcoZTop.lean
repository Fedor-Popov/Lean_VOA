import VOA.Classification.COne.OrbIcoZNormal
import VOA.Classification.COne.OrbIcoTCoupling

/-! Nonvanishing of the top self-product, using the thirteen-dimensional sl2 multiplet.
Only the already certified charged endpoint is needed; no oscillator expansion
of a self-product is performed here. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbPrim OrbSpan OrbC2c OrbOctaR
  VOA.LatGen VOA.LatGen.Triplet OrbRat6 Screening VOA.IntegralLattice

private abbrev pair71 (i j : ℕ) := V2v.smul (wv 6 i) 71 (wv 6 j)

private theorem pair71_grading (i j : ℕ) : pair71 i j ∈ V2v.grading 0 := by
  convert V2v.grading_mode _ (wv_grading 6 i) _ (wv_grading 6 j) 71 using 2

private theorem ho_zero_of_grade_zero {x : Sp} (hx : x ∈ V2v.grading 0) : ho x = 0 := by
  rw [V2v.vacuum_grade, Submodule.mem_span_singleton] at hx
  obtain ⟨c, rfl⟩ := hx
  rw [map_smul, ho_eq_scr, screening_vacuum, smul_zero]

private theorem pair71_off_diagonal (i j : ℕ) (hij : i + j ≠ 12) : pair71 i j = 0 := by
  have hh := ho_zero_of_grade_zero (pair71_grading i j)
  rw [ho_smul, ho_wv, ho_wv, PreVertexAlgebra.smul_smul_left,
    PreVertexAlgebra.smul_smul_right, ← add_smul] at hh
  have hc : (((2 * 6 : ℕ) : ℂ) - 2 * i) +
      (((2 * 6 : ℕ) : ℂ) - 2 * j) ≠ 0 := by
    intro h
    have he : (i : ℂ) + j = 12 := by linear_combination -h / 2
    exact hij (by exact_mod_cast he)
  exact (smul_eq_zero.mp hh).resolve_left hc

private theorem pair71_step (i : ℕ) (hi : i < 12) :
    ((12 - i : ℕ) : ℂ) • pair71 (i + 1) (11 - i) =
      -((i + 1 : ℕ) : ℂ) • pair71 i (12 - i) := by
  have he := eo_smul (wv 6 (i + 1)) 71 (wv 6 (12 - i))
  rw [show V2v.smul (wv 6 (i + 1)) 71 (wv 6 (12 - i)) = 0 from
    pair71_off_diagonal _ _ (by omega), map_zero,
    eo_wv 6 i (by omega), eo_wv' 6 (12 - i) (by omega), if_neg (by omega),
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right,
    show 12 - i - 1 = 11 - i by omega] at he
  have hz : eps1 • (((i + 1 : ℕ) : ℂ) • pair71 i (12 - i) +
      ((12 - i : ℕ) : ℂ) • pair71 (i + 1) (11 - i)) = 0 := by
    simpa only [smul_add, smul_smul] using he.symm
  have h := (smul_eq_zero.mp hz).resolve_left eps1_ne_zero
  simpa only [neg_smul] using eq_neg_of_add_eq_zero_right h

private def diagCoeff (i : ℕ) : ℚ := (-1)^i / ((12:ℕ).choose i : ℚ)

private theorem pair71_diagonal (i : ℕ) (hi : i ≤ 12) :
    pair71 i (12 - i) = (diagCoeff i : ℂ) • pair71 0 12 := by
  induction i with
  | zero => simp [diagCoeff]
  | succ i ih =>
    have hlt : i < 12 := by omega
    have hc : ((12 - i : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : 12 - i ≠ 0)
    have hs := pair71_step i hlt
    rw [ih (by omega)] at hs
    calc
      pair71 (i + 1) (12 - (i + 1)) =
          ((12 - i : ℕ) : ℂ)⁻¹ • (((12 - i : ℕ) : ℂ) • pair71 (i + 1) (11 - i)) := by
        rw [inv_smul_smul₀ hc, show 12 - (i + 1) = 11 - i by omega]
      _ = (diagCoeff (i + 1) : ℂ) • pair71 0 12 := by
        rw [hs, smul_smul, smul_smul]
        congr 1
        interval_cases i <;> norm_num [diagCoeff, Nat.choose]

private theorem wv6_last : ∃ c : ℂ, c ≠ 0 ∧
    wv 6 12 = c • latChargeGen (latP 1) (-6 : ℤ) := by
  have hv : wv 6 12 ∈ bigradα (latP 1) (0, (-6 : ℤ)) := by
    have h := Submodule.smul_mem _ (cnk 6 12) (vn_bigrad 6 12)
    norm_num at h
    exact h
  rw [bigradα, HeisenbergN.gradingZN_zero_eq_span_vacuum,
    Submodule.map_span, Set.image_singleton] at hv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
  have hcn : cnk 6 12 ≠ 0 := by norm_num [cnk]
  have hn : wv 6 12 ≠ 0 := by
    unfold wv
    exact smul_ne_zero hcn (vn_ne_zero 6 12 (by omega))
  refine ⟨c, ?_, hc.symm⟩
  intro hz
  rw [hz, zero_smul] at hc
  exact hn hc.symm

private theorem pair71_endpoint : ∃ c : ℂ, c ≠ 0 ∧
    pair71 0 12 = c • V2v.vacuum := by
  obtain ⟨c, hc, he⟩ := wv6_last
  rw [pair71, wv_zero, he, PreVertexAlgebra.smul_smul_right]
  have h := smul_chargeGen_bottom (6 : ℤ) (-6 : ℤ)
  norm_num only [latP_form, Int.reduceMul, Int.reduceNeg, Int.reduceSub,
    Int.reduceAdd] at h
  norm_num only [Nat.cast_ofNat] at ⊢
  rw [h, smul_smul]
  exact ⟨c * latticeCocycle (latP 1) (6 : ℤ) (-6 : ℤ),
    mul_ne_zero hc (VOA.LatGen.Screen.latticeCocycle_ne_zero _ _ _), rfl⟩

open OrbIco OrbIcoT

private theorem X_expansion : (Xico : Sp) =
    f0 • wv 6 0 + f0 • wv 6 12 + f2 • wv 6 2 + f2 • wv 6 10 +
      f4 • wv 6 4 + f4 • wv 6 8 + f6 • wv 6 6 := by
  rw [Xico_eq_Tb, fpoly_eq]
  simp only [← MvPolynomial.smul_eq_C_mul, map_add, map_smul,
    Tb_xy 12 0 6 (by omega), Tb_xy 0 12 6 (by omega),
    Tb_xy 10 2 6 (by omega), Tb_xy 2 10 6 (by omega),
    Tb_xy 8 4 6 (by omega), Tb_xy 4 8 6 (by omega),
    Tb_xy 6 6 6 (by omega)]
  simp only [smul_add]
  abel

private theorem pair71_formula (i j : ℕ) (hi : i ≤ 12) (hj : j ≤ 12) :
    pair71 i j = if i + j = 12 then (diagCoeff i : ℂ) • pair71 0 12 else 0 := by
  split_ifs with h
  · have hj' : j = 12 - i := by omega
    rw [hj']
    exact pair71_diagonal i hi
  · exact pair71_off_diagonal i j h

private def icoTopFactor : ℂ :=
  2 * f0^2 + f2^2 / 33 + 2 * f4^2 / 495 + f6^2 / 924

private theorem icoTopFactor_ne_zero : icoTopFactor ≠ 0 := by
  have hg := gp_re_pos
  have he : icoTopFactor = ((0 : ℝ) : ℂ) +
      (((2 * (-3 - 4 * gp.re)^2 + (-22 - 44 * gp.re)^2 / 33 +
        2 * (99 + 132 * gp.re)^2 / 495 + (44 + 88 * gp.re)^2 / 924) : ℝ) : ℂ) := by
    unfold icoTopFactor f0 f2 f4 f6
    have hreal : (gp.re : ℂ) = gp := by
      apply Complex.ext
      · simp
      · simp [gp, s5]
    have hrealim : gp.im = 0 := by simp [gp, s5]
    rw [← hreal]
    push_cast
    simp only [Complex.ofReal_re]
    ring
  have hp : 0 < 2 * (-3 - 4 * gp.re)^2 + (-22 - 44 * gp.re)^2 / 33 +
        2 * (99 + 132 * gp.re)^2 / 495 + (44 + 88 * gp.re)^2 / 924 := by
    have h : 0 < (-3 - 4 * gp.re)^2 := sq_pos_of_ne_zero (by linarith)
    positivity
  intro hz
  have hc := congrArg Complex.re he
  rw [hz] at hc
  simp only [Complex.zero_re, Complex.add_re, Complex.ofReal_re] at hc
  linarith

/-- The actual A5 top self-product is a nonzero multiple of the vacuum. -/
theorem self_top_nonzero : ∃ c : ℂ, c ≠ 0 ∧
    Wi.smul Xico 71 Xico = c • Wi.vacuum := by
  obtain ⟨c, hc, he⟩ := pair71_endpoint
  refine ⟨icoTopFactor * c, mul_ne_zero icoTopFactor_ne_zero hc, ?_⟩
  apply Subtype.ext
  change V2v.smul (Xico : Sp) 71 Xico = (icoTopFactor * c) • V2v.vacuum
  rw [X_expansion]
  simp only [PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_right,
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right]
  change _ = _
  have h00 := pair71_formula 0 0 (by omega) (by omega)
  have h012 := pair71_formula 0 12 (by omega) (by omega)
  have h02 := pair71_formula 0 2 (by omega) (by omega)
  have h010 := pair71_formula 0 10 (by omega) (by omega)
  have h04 := pair71_formula 0 4 (by omega) (by omega)
  have h08 := pair71_formula 0 8 (by omega) (by omega)
  have h06 := pair71_formula 0 6 (by omega) (by omega)
  have h120 := pair71_formula 12 0 (by omega) (by omega)
  have h1212 := pair71_formula 12 12 (by omega) (by omega)
  have h122 := pair71_formula 12 2 (by omega) (by omega)
  have h1210 := pair71_formula 12 10 (by omega) (by omega)
  have h124 := pair71_formula 12 4 (by omega) (by omega)
  have h128 := pair71_formula 12 8 (by omega) (by omega)
  have h126 := pair71_formula 12 6 (by omega) (by omega)
  have h20 := pair71_formula 2 0 (by omega) (by omega)
  have h212 := pair71_formula 2 12 (by omega) (by omega)
  have h22 := pair71_formula 2 2 (by omega) (by omega)
  have h210 := pair71_formula 2 10 (by omega) (by omega)
  have h24 := pair71_formula 2 4 (by omega) (by omega)
  have h28 := pair71_formula 2 8 (by omega) (by omega)
  have h26 := pair71_formula 2 6 (by omega) (by omega)
  have h100 := pair71_formula 10 0 (by omega) (by omega)
  have h1012 := pair71_formula 10 12 (by omega) (by omega)
  have h102 := pair71_formula 10 2 (by omega) (by omega)
  have h1010 := pair71_formula 10 10 (by omega) (by omega)
  have h104 := pair71_formula 10 4 (by omega) (by omega)
  have h108 := pair71_formula 10 8 (by omega) (by omega)
  have h106 := pair71_formula 10 6 (by omega) (by omega)
  have h40 := pair71_formula 4 0 (by omega) (by omega)
  have h412 := pair71_formula 4 12 (by omega) (by omega)
  have h42 := pair71_formula 4 2 (by omega) (by omega)
  have h410 := pair71_formula 4 10 (by omega) (by omega)
  have h44 := pair71_formula 4 4 (by omega) (by omega)
  have h48 := pair71_formula 4 8 (by omega) (by omega)
  have h46 := pair71_formula 4 6 (by omega) (by omega)
  have h80 := pair71_formula 8 0 (by omega) (by omega)
  have h812 := pair71_formula 8 12 (by omega) (by omega)
  have h82 := pair71_formula 8 2 (by omega) (by omega)
  have h810 := pair71_formula 8 10 (by omega) (by omega)
  have h84 := pair71_formula 8 4 (by omega) (by omega)
  have h88 := pair71_formula 8 8 (by omega) (by omega)
  have h86 := pair71_formula 8 6 (by omega) (by omega)
  have h60 := pair71_formula 6 0 (by omega) (by omega)
  have h612 := pair71_formula 6 12 (by omega) (by omega)
  have h62 := pair71_formula 6 2 (by omega) (by omega)
  have h610 := pair71_formula 6 10 (by omega) (by omega)
  have h64 := pair71_formula 6 4 (by omega) (by omega)
  have h68 := pair71_formula 6 8 (by omega) (by omega)
  have h66 := pair71_formula 6 6 (by omega) (by omega)
  simp only [pair71] at *
  rw [h00, h012, h02, h010, h04, h08, h06, h120, h1212, h122, h1210, h124, h128, h126, h20, h212, h22, h210, h24, h28, h26, h100, h1012, h102, h1010, h104, h108, h106, h40, h412, h42, h410, h44, h48, h46, h80, h812, h82, h810, h84, h88, h86, h60, h612, h62, h610, h64, h68, h66]
  norm_num [diagCoeff, Nat.choose] at ⊢
  rw [he]
  simp only [smul_smul, ← add_smul]
  congr 1
  unfold icoTopFactor
  ring

/-- The same nonzero top scalar survives in the intrinsic Zhu algebra. -/
theorem self_top_Zhu_nonzero : ∃ c : ℂ, c ≠ 0 ∧ selfMode 71 = c • mk Wi Wi.vacuum := by
  obtain ⟨c, hc, he⟩ := self_top_nonzero
  exact ⟨c, hc, by rw [selfMode, he, map_smul]⟩

end VOA.Classification.COne.OrbIcoZ
