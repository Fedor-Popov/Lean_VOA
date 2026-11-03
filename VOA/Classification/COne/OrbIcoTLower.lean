import VOA.Classification.COne.OrbIcoTScreenVOA

/-! Vanishing below the first nonzero sixth-channel antidiagonal. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoT
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  VOA.SparseRational PlusC2Eval OrbIco OrbPrim OrbRat6

theorem sixth_zero_row (j : ℕ) (hj : j < 6) :
    V2v.smul (wv 6 0) 35 (wv 6 j) = 0 := by
  rw [wv_zero, wv, PreVertexAlgebra.smul_smul_right]
  obtain ⟨p, hp, he⟩ := vn_bigrad 6 j
  rw [← he]
  change _ • V2v.smul (latChargeGen (latP 1) ((6 : ℕ) : ℤ)) 35
    (latStateGen (latP 1) p (((6 : ℕ) : ℤ) - (j : ℤ) : ℤ)) = 0
  rw [smul_chargeGen_state]
  have hz := Screen.EEVec_mem_gradingZN (latP 1) ((6 : ℕ) : ℤ)
    (-(35 : ℤ) - 1 - (latP 1).form ((6 : ℕ) : ℤ)
      ((((6 : ℕ) : ℤ) - (j : ℤ)) : ℤ)) hp
  rw [gradingZN_of_neg (by rw [latP_form]; push_cast; nlinarith), Submodule.mem_bot] at hz
  rw [hz]
  simp [latStateGen]

theorem sixth_pair_zero (i j : ℕ) (hij : i + j < 6) :
    V2v.smul (wv 6 i) 35 (wv 6 j) = 0 := by
  induction i generalizing j with
  | zero => exact sixth_zero_row j (by omega)
  | succ i ih =>
    have h := congrArg fo (ih j (by omega))
    rw [fo_smul, fo_wv 6 i (by omega), fo_wv 6 j (by omega),
      PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right,
      ih (j + 1) (by omega), smul_zero, add_zero, map_zero] at h
    exact (smul_eq_zero.mp h).resolve_left (by exact_mod_cast (show 2 * 6 - i ≠ 0 by omega))

end VOA.Classification.COne.OrbIcoT
