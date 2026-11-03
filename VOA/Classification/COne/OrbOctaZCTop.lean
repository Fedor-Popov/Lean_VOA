import VOA.Classification.COne.OrbOctaZCNormal
import VOA.Classification.COne.OrbOctaRCPrimary

/-! Nonvanishing of the top self-product, using the nine-dimensional sl2 multiplet.
Only the already certified charged endpoint is needed; no oscillator expansion
of a self-product is performed here. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbOctaZC
open VOA VertexOperatorAlgebra OrbPrim OrbSpan OrbC2c OrbOctaR
  VOA.LatGen VOA.LatGen.Triplet OrbRat6 Screening VOA.IntegralLattice

private abbrev pair31 (i j : ℕ) := V2v.smul (wv 4 i) 31 (wv 4 j)

private theorem pair31_grading (i j : ℕ) : pair31 i j ∈ V2v.grading 0 := by
  convert V2v.grading_mode _ (wv_grading 4 i) _ (wv_grading 4 j) 31 using 2

private theorem ho_zero_of_grade_zero {x : Sp} (hx : x ∈ V2v.grading 0) : ho x = 0 := by
  rw [V2v.vacuum_grade, Submodule.mem_span_singleton] at hx
  obtain ⟨c, rfl⟩ := hx
  rw [map_smul, ho_eq_scr, screening_vacuum, smul_zero]

private theorem pair31_off_diagonal (i j : ℕ) (hij : i + j ≠ 8) : pair31 i j = 0 := by
  have hh := ho_zero_of_grade_zero (pair31_grading i j)
  rw [ho_smul, ho_wv, ho_wv, PreVertexAlgebra.smul_smul_left,
    PreVertexAlgebra.smul_smul_right, ← add_smul] at hh
  have hc : (((2 * 4 : ℕ) : ℂ) - 2 * i) +
      (((2 * 4 : ℕ) : ℂ) - 2 * j) ≠ 0 := by
    intro h
    have he : (i : ℂ) + j = 8 := by linear_combination -h / 2
    exact hij (by exact_mod_cast he)
  exact (smul_eq_zero.mp hh).resolve_left hc

private theorem pair31_step (i : ℕ) (hi : i < 8) :
    ((8 - i : ℕ) : ℂ) • pair31 (i + 1) (7 - i) =
      -((i + 1 : ℕ) : ℂ) • pair31 i (8 - i) := by
  have he := eo_smul (wv 4 (i + 1)) 31 (wv 4 (8 - i))
  rw [show V2v.smul (wv 4 (i + 1)) 31 (wv 4 (8 - i)) = 0 from
    pair31_off_diagonal _ _ (by omega), map_zero,
    eo_wv 4 i (by omega), eo_wv' 4 (8 - i) (by omega), if_neg (by omega),
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right,
    show 8 - i - 1 = 7 - i by omega] at he
  have hz : eps1 • (((i + 1 : ℕ) : ℂ) • pair31 i (8 - i) +
      ((8 - i : ℕ) : ℂ) • pair31 (i + 1) (7 - i)) = 0 := by
    simpa only [smul_add, smul_smul] using he.symm
  have h := (smul_eq_zero.mp hz).resolve_left eps1_ne_zero
  simpa only [neg_smul] using eq_neg_of_add_eq_zero_right h

private def diagCoeff : ℕ → ℚ
  | 0 => 1 | 1 => -1/8 | 2 => 1/28 | 3 => -1/56 | 4 => 1/70
  | 5 => -1/56 | 6 => 1/28 | 7 => -1/8 | 8 => 1 | _ => 0

private theorem pair31_diagonal (i : ℕ) (hi : i ≤ 8) :
    pair31 i (8 - i) = (diagCoeff i : ℂ) • pair31 0 8 := by
  induction i with
  | zero => simp [diagCoeff]
  | succ i ih =>
    have hlt : i < 8 := by omega
    have hc : ((8 - i : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : 8 - i ≠ 0)
    have hs := pair31_step i hlt
    rw [ih (by omega)] at hs
    calc
      pair31 (i + 1) (8 - (i + 1)) =
          ((8 - i : ℕ) : ℂ)⁻¹ • (((8 - i : ℕ) : ℂ) • pair31 (i + 1) (7 - i)) := by
        rw [inv_smul_smul₀ hc, show 8 - (i + 1) = 7 - i by omega]
      _ = (diagCoeff (i + 1) : ℂ) • pair31 0 8 := by
        rw [hs, smul_smul, smul_smul]
        congr 1
        interval_cases i <;> norm_num [diagCoeff]

private theorem pair31_endpoint : pair31 0 8 =
    latticeCocycle (latP 1) (4 : ℤ) (-4 : ℤ) • V2v.vacuum := by
  rw [pair31, wv_zero, OrbOctaRC.wv4_eight_value]
  have h := smul_chargeGen_bottom (4 : ℤ) (-4 : ℤ)
  norm_num only [latP_form, Int.reduceMul, Int.reduceNeg, Int.reduceSub,
    Int.reduceAdd] at h
  exact h

/-- The explicit nonzero scalar, without requiring a convention for the cocycle sign. -/
theorem self_top_coefficient :
    OrbOctaR.W.smul OrbOctaR.X 31 OrbOctaR.X =
      ((96 / 5 : ℂ) * latticeCocycle (latP 1) (4 : ℤ) (-4 : ℤ)) • OrbOctaR.W.vacuum := by
  apply Subtype.ext
  change V2v.smul (OrbOctaR.X : Sp) 31 (OrbOctaR.X : Sp) = _
  rw [OrbOctaR.X_coe]
  simp only [PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_right,
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right]
  change 2 • (2 • pair31 0 0 + 28 • pair31 4 0 + 2 • pair31 8 0) +
      28 • (2 • pair31 0 4 + 28 • pair31 4 4 + 2 • pair31 8 4) +
      2 • (2 • pair31 0 8 + 28 • pair31 4 8 + 2 • pair31 8 8) =
      ((96 / 5 : ℂ) * latticeCocycle (latP 1) (4 : ℤ) (-4 : ℤ)) • V2v.vacuum
  have h44 := pair31_diagonal 4 (by decide)
  have h80 := pair31_diagonal 8 (by decide)
  norm_num only [diagCoeff, Nat.reduceSub, Rat.cast_div, Rat.cast_one,
    Rat.cast_ofNat, one_smul] at h44 h80
  rw [pair31_off_diagonal 0 0 (by decide), pair31_off_diagonal 0 4 (by decide),
    pair31_off_diagonal 4 0 (by decide), pair31_off_diagonal 4 8 (by decide),
    pair31_off_diagonal 8 4 (by decide), pair31_off_diagonal 8 8 (by decide),
    h44, h80, pair31_endpoint]
  simp only [smul_zero, zero_add, add_zero, smul_smul, ← add_smul]
  congr 1
  ring

/-- The top self-mode is a nonzero scalar multiple of the vacuum in Zhu's algebra. -/
theorem self_top_nonzero : ∃ c : ℂ, c ≠ 0 ∧ selfMode 31 = c • mk W W.vacuum := by
  refine ⟨(96 / 5 : ℂ) * latticeCocycle (latP 1) (4 : ℤ) (-4 : ℤ),
    mul_ne_zero (by norm_num) (VOA.LatGen.Screen.latticeCocycle_ne_zero _ _ _), ?_⟩
  rw [selfMode, self_top_coefficient, map_smul]

end VOA.Classification.COne.OrbOctaZC
