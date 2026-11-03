import VOA.Classification.COne.OrbIcoTSchur

/-! Top coefficients and blockwise assembly for the symbolic screening calculation. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoT
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  VOA.SparseRational PlusC2Eval OrbIco OrbPrim

theorem shEval_grading (P : RawPoly ℕ) (N : ℕ) (h : ∀ t ∈ P, t.2.sum = N) :
    shEval P ∈ gradingWN (rank (latP 1)) N := by
  induction P with
  | nil => exact Submodule.zero_mem _
  | cons t P ih =>
    rcases t with ⟨q, w⟩
    rw [shEval_cons]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _
      ((h (q, w) (by simp)) ▸ shWord_grading w)) (ih (fun t ht => h t (by simp [ht])))

theorem aExp_shWord_of_lt (w : List ℕ) (beta : ℤ) (k : ℕ) (hk : w.sum < k) :
    aExpVec (latP 1) beta k (shWord w) = 0 := by
  have h := aExpVec_mem_gradingZN (latP 1) beta k (shWord_grading w)
  rwa [gradingZN_of_neg (by omega), Submodule.mem_bot] at h

def topCoeff (w : List ℕ) : ℚ := (w.map fun n => ((n + 11).choose 11 : ℚ)).prod

theorem topCoeff_sound (w : List ℕ) :
    aExpVec (latP 1) (6 : ℤ) w.sum (shWord w) = (topCoeff w : ℂ) • vacuumN _ := by
  induction w with
  | nil => simp [topCoeff, shWord_nil, aExpVec_zero, vacuumN]
  | cons i w ih =>
    rw [List.sum_cons, shWord_cons, aExpVec_mul, Finset.sum_eq_single i]
    · rw [sh, aExpVec_vSchur (latP 1) (latP_posDef 1 le_rfl) _ _ i i le_rfl,
        gco_m12, Nat.sub_self, vSchur_zero, Nat.add_sub_cancel_left, ih,
        smul_mul_smul_comm]
      simp [topCoeff, vacuumN]
    · intro k hk hki
      rcases lt_or_gt_of_ne hki with hlt | hgt
      · rw [aExp_shWord_of_lt w 6 (i + w.sum - k) (by omega), mul_zero]
      · rw [sh, aExpVec_vSchur_of_lt (latP 1) _ _ hgt, zero_mul]
    · intro hi
      exact (hi (Finset.mem_range.mpr (by omega))).elim

def topSum (P : RawPoly ℕ) : ℚ := (P.map fun t => t.1 * topCoeff t.2).sum

theorem topSum_sound (P : RawPoly ℕ) (N : ℕ) (h : ∀ t ∈ P, t.2.sum = N) :
    aExpVec (latP 1) (6 : ℤ) N (shEval P) = (topSum P : ℂ) • vacuumN _ := by
  induction P with
  | nil => simp [shEval_nil, topSum]
  | cons t P ih =>
    rcases t with ⟨q, w⟩
    rw [shEval_cons, map_add, map_smul,
      ← h (q, w) (by simp), topCoeff_sound]
    rw [h (q, w) (by simp), ih (fun t ht => h t (by simp [ht]))]
    simp [topSum, add_smul, smul_smul]

theorem shScreen_single (s : ℕ) (q : ℚ) (w : List ℕ) (Q : RawPoly ℕ)
    (h : normR (shScreen s [(q, w)]) = Q) :
    shEval Q = EEVec (latP 1) (-1 : ℤ) (s : ℤ) ((q : ℂ) • shWord w) := by
  rw [← h, shEval_norm, shScreen_sound, shEval_cons, shEval_nil, add_zero]

theorem shScreen_blocks (s : ℕ) (P : RawPoly ℕ) (Qs : List (RawPoly ℕ))
    (hs : List.Forall₂ (fun t Q => shEval Q =
      EEVec (latP 1) (-1 : ℤ) (s : ℤ) ((t.1 : ℂ) • shWord t.2)) P Qs) :
    shEval Qs.flatten = EEVec (latP 1) (-1 : ℤ) (s : ℤ) (shEval P) := by
  induction hs with
  | nil => simp [shEval_nil]
  | cons h hs ih =>
    rename_i t Q P Qs
    rcases t with ⟨q, w⟩
    simp only [List.flatten_cons, shEval_append, h, ih, shEval_cons, map_add]

theorem shEval_merge (P Q R : RawPoly ℕ) (h : normR (P ++ Q) = R) :
    shEval R = shEval P + shEval Q := by
  rw [← h, shEval_norm, shEval_append]

end VOA.Classification.COne.OrbIcoT
