import VOA.Classification.COne.OrbIcoTSchurTop
import VOA.Classification.COne.PlusSplitHalfCharacters

/-! The symbolic Schur screening calculation acts on actual lattice states. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoT
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  VOA.SparseRational PlusC2Eval OrbIco OrbPrim OrbRat6

theorem fo_screen (P Q : RawPoly ℕ) (s : ℕ) (d : ℤ)
    (hd : 2 * d - 1 = (s : ℤ))
    (h : shEval Q = EEVec (latP 1) (-1 : ℤ) (s : ℤ) (shEval P)) :
    fo (latStateGen (latP 1) (shEval P) d) =
      latStateGen (latP 1) (shEval Q) ((d - 1 : ℤ)) := by
  rw [fo_eq]
  change V2v.smul (latChargeGen (latP 1) (-1 : ℤ)) 0 _ = _
  rw [smul_chargeGen_state, PlusCharacterTable.rankOne_cocycle, one_smul, latP_form]
  rw [show -(0 : ℤ) - 1 - 2 * ((1 : ℕ) : ℤ) * (-1) * d = (s : ℤ) by
    push_cast at *; omega, ← h]
  congr 1
  change (-1 : ℤ) + d = d - 1
  omega

theorem vn_succ (n k : ℕ) : vn n (k + 1) = fo (vn n k) := by
  simp only [vn, pow_succ', Module.End.mul_apply]

theorem EEVec_top (P : RawPoly ℕ) (N : ℕ) (h : ∀ t ∈ P, t.2.sum = N) :
    EEVec (latP 1) (6 : ℤ) (-(N : ℤ)) (shEval P) =
      (topSum P : ℂ) • vacuumN _ := by
  rw [WpC2.EEVec_eq_weight_bounded_sum' (latP 1) _ _ (shEval_grading P N h)]
  rw [show max (0 : ℤ) (-(N : ℤ)) = 0 by omega, add_neg_cancel,
    Finset.Icc_self, Finset.sum_singleton]
  simp only [Int.toNat_zero, sub_neg_eq_add, zero_add, Int.toNat_natCast,
    vSchur_zero, one_mul]
  exact topSum_sound P N h

end VOA.Classification.COne.OrbIcoT
