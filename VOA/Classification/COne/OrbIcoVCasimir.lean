import VOA.Classification.COne.OrbIcoTCoupling

/-! Horizontal Casimir separation of the two actual icosahedral Virasoro towers.
The construction uses a degree-two operator, independently of the output level. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbRat6 OrbIco
  VOA.LatGen VOA.LatGen.Triplet

/-- The spin Casimir, normalized to eigenvalue `4 n(n+1)` on spin `n`. -/
def spinCasimir : Module.End ℂ Sp := ho * ho + (2 : ℂ) • ho +
  (4 * eps1) • (fo * eo)

theorem spinCasimir_apply (x : Sp) :
    spinCasimir x = ho (ho x) + (2 : ℂ) • ho x + (4 * eps1) • fo (eo x) := rfl

theorem eo_L (m : ℤ) (x : Sp) : eo (V2v.L m x) = V2v.L m (eo x) := by
  rw [eo_eq_scr, eo_eq_scr]
  exact scr_comm_L V2v chargeGen_pos_grading m x

theorem ho_L (m : ℤ) (x : Sp) : ho (V2v.L m x) = V2v.L m (ho x) := by
  rw [ho_eq_scr, ho_eq_scr]
  exact scr_comm_L V2v hSt_grading m x

theorem spinCasimir_L (m : ℤ) (x : Sp) :
    spinCasimir (V2v.L m x) = V2v.L m (spinCasimir x) := by
  simp only [spinCasimir_apply, ho_L, fo_L, eo_L, map_add, map_smul]

theorem spinCasimir_wv (n i : ℕ) (hi : i ≤ 2 * n) :
    spinCasimir (wv n i) = (4 * (n : ℂ) * (n + 1)) • wv n i := by
  rw [spinCasimir_apply, ho_wv, map_smul, ho_wv, eo_wv' n i hi]
  by_cases h0 : i = 0
  · subst i
    simp only [if_true, map_zero, smul_zero, add_zero, Nat.cast_zero, mul_zero, sub_zero,
      smul_smul]
    module
  · rw [if_neg h0, map_smul, OrbIco.fo_wv n (i - 1) (by omega),
      show i - 1 + 1 = i by omega, smul_smul, smul_smul, smul_smul]
    push_cast [Nat.cast_sub (show 1 ≤ i by omega),
      Nat.cast_sub (show i - 1 ≤ 2 * n by omega)]
    simp only [smul_smul, ← add_smul]
    congr 1
    linear_combination 4 * (i : ℂ) * (2 * n - (i - 1)) * eps1_sq


theorem spinCasimir_Tb {n : ℕ} {P : P2} (hP : P ∈ binDeg (2 * n)) :
    spinCasimir (Tb P) = (4 * (n : ℂ) * (n + 1)) • Tb P := by
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, he, rfl⟩ := hx
    simp only [Set.mem_setOf_eq] at he
    rw [Tb_monomial, one_smul, tbm_of_deg (by omega)]
    exact spinCasimir_wv n (e 1) (by omega)
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, map_smul, hx, smul_comm]

theorem spinCasimir_Xico : spinCasimir (Xico : Sp) = (168 : ℂ) • (Xico : Sp) := by
  rw [OrbIcoT.Xico_eq_Tb]
  convert spinCasimir_Tb (n := 6) fpoly_mem using 1
  norm_num

theorem spinCasimir_vacuum : spinCasimir V2v.vacuum = 0 := by
  have h := spinCasimir_wv 0 0 (by omega)
  have he : wv 0 0 = V2v.vacuum := by
    rw [wv_zero]
    rfl
  simpa [he] using h

end VOA.Classification.COne.OrbIcoV
