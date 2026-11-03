import VOA.Classification.COne.OrbIcoChan2
import VOA.Classification.COne.PlusC2Eval

/-! A sparse evaluator in products of Schur states for the six screening steps. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoT
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  VOA.SparseRational PlusC2Eval OrbIco OrbPrim

theorem list_sum_range {A : Type*} [AddCommMonoid A] (n : ℕ) (f : ℕ → A) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, Finset.sum_range_succ]

abbrev sh (n : ℕ) : FockN (rank (latP 1)) := vSchur (latP 1) (-1 : ℤ) n
abbrev shWord (w : List ℕ) : FockN (rank (latP 1)) := evalWord sh w
abbrev shEval (P : RawPoly ℕ) : FockN (rank (latP 1)) := evalRaw sh P

theorem shWord_nil : shWord [] = 1 := rfl

theorem shWord_cons (i : ℕ) (w : List ℕ) : shWord (i :: w) = sh i * shWord w := rfl

theorem shEval_nil : shEval [] = 0 := rfl

theorem shEval_cons (q : ℚ) (w : List ℕ) (P : RawPoly ℕ) :
    shEval ((q, w) :: P) = (q : ℂ) • shWord w + shEval P := by
  simp [shEval, evalRaw, MvPolynomial.smul_eq_C_mul]

theorem shEval_append (P Q : RawPoly ℕ) : shEval (P ++ Q) = shEval P + shEval Q :=
  evalRaw_append _ P Q

theorem shEval_flatMap {ι : Type*} (xs : List ι) (f : ι → RawPoly ℕ) :
    shEval (xs.flatMap f) = (xs.map fun x => shEval (f x)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [List.flatMap_cons, shEval_append, ih, List.map_cons, List.sum_cons]

theorem shEval_scale (q : ℚ) (P : RawPoly ℕ) :
    shEval (scaleR q P) = (q : ℂ) • shEval P := by
  rw [scaleR, shEval, evalRaw_scale, algebraMap_rat_mul]

/-- Degree zero Schur factors are units and need not be stored. -/
def shPrepend (i : ℕ) (P : RawPoly ℕ) : RawPoly ℕ :=
  if i = 0 then P else P.map fun t => (t.1, i :: t.2)

theorem shEval_prepend (i : ℕ) (P : RawPoly ℕ) :
    shEval (shPrepend i P) = sh i * shEval P := by
  by_cases hi : i = 0
  · simp [shPrepend, hi, sh, vSchur_zero]
  · rw [shPrepend, if_neg hi]
    induction P with
    | nil => simp [shEval_nil]
    | cons t P ih =>
      rcases t with ⟨q, w⟩
      rw [List.map_cons, shEval_cons, shEval_cons, ih, shWord_cons, mul_add, mul_smul_comm]

def gTwo (k : ℕ) : ℚ := if k = 0 then 1 else if k = 1 then -2 else 1

theorem gTwo_sound (k : ℕ) (hk : k ≤ 2) : (gTwo k : ℂ) = gco 2 k := by
  interval_cases k <;> norm_num [gTwo, gco_zero, gco_two_one, gco_two_two]

/-- The annihilating exponential acting on a Schur word. -/
def shAnnihilate (n : ℕ) : List ℕ → RawPoly ℕ
  | [] => if n = 0 then [(1, [])] else []
  | i :: w => (List.range (n + 1)).flatMap fun k =>
      if k ≤ i ∧ k ≤ 2 then
        scaleR (gTwo k) (shPrepend (i - k) (shAnnihilate (n - k) w)) else []

theorem shAnnihilate_sound (w : List ℕ) (n : ℕ) :
    shEval (shAnnihilate n w) = aExpVec (latP 1) (-1 : ℤ) n (shWord w) := by
  induction w generalizing n with
  | nil =>
    rw [shWord_nil]
    change shEval (shAnnihilate n []) = aExpVec (latP 1) (-1 : ℤ) n (vacuumN _)
    rw [aExpVec_vacuum, shAnnihilate]
    split_ifs <;> simp [shEval_cons, shEval_nil, shWord_nil, vacuumN]
  | cons i w ih =>
    rw [shWord_cons, aExpVec_mul, shAnnihilate, shEval_flatMap]
    rw [list_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hi : k ≤ i
    · by_cases h2 : k ≤ 2
      · rw [if_pos ⟨hi, h2⟩, shEval_scale, shEval_prepend, ih]
        rw [sh, aExpVec_vSchur (latP 1) (latP_posDef 1 le_rfl) _ _ i k hi]
        rw [latP_form]
        norm_num only [Nat.cast_one, mul_one, mul_neg, neg_mul, neg_neg, Int.cast_ofNat]
        rw [gTwo_sound k h2, smul_mul_assoc]
      · rw [if_neg (by simp [h2]), shEval_nil]
        rw [sh, aExpVec_vSchur (latP 1) (latP_posDef 1 le_rfl) _ _ i k hi, latP_form]
        norm_num only [Nat.cast_one, mul_one, mul_neg, neg_mul, neg_neg, Int.cast_ofNat]
        rw [gco_two_ge k (by omega), zero_smul, zero_mul]
    · rw [if_neg (by simp [hi]), shEval_nil, sh,
        aExpVec_vSchur_of_lt (latP 1) _ _ (by omega : i < k), zero_mul]

theorem shWord_grading (w : List ℕ) : shWord w ∈ gradingWN (rank (latP 1)) w.sum := by
  induction w with
  | nil => simpa [shWord_nil, vSchur_zero] using Screen.vSchur_mem_gradingWN (latP 1) (-1 : ℤ) 0
  | cons i w ih =>
    rw [shWord_cons, List.sum_cons, mem_gradingWN] at *
    exact (Screen.vSchur_mem_gradingWN (latP 1) (-1 : ℤ) i |> mem_gradingWN.mp).mul ih

/-- A nonnegative charge-dressing mode in the Schur-product basis. -/
def shScreenWord (s : ℕ) (w : List ℕ) : RawPoly ℕ :=
  (List.range (w.sum + 1)).flatMap fun k => shPrepend (s + k) (shAnnihilate k w)

theorem shScreenWord_sound (s : ℕ) (w : List ℕ) :
    shEval (shScreenWord s w) = EEVec (latP 1) (-1 : ℤ) (s : ℤ) (shWord w) := by
  rw [WpC2.EEVec_eq_weight_bounded_sum' (latP 1) _ _ (shWord_grading w),
    shScreenWord, shEval_flatMap]
  rw [list_sum_range, show max (0 : ℤ) (s : ℤ) = s by omega]
  refine Finset.sum_nbij' (fun k => (s : ℤ) + k) (fun m => (m - s).toNat) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_Icc]
    omega
  · intro m hm
    simp only [Finset.mem_Icc] at hm
    simp only [Finset.mem_range]
    omega
  · intro k hk; simp
  · intro m hm
    simp only [Finset.mem_Icc] at hm
    dsimp only
    omega
  · intro k hk
    rw [shEval_prepend, shAnnihilate_sound]
    rw [show ((s : ℤ) + k).toNat = s + k by omega,
      show ((s : ℤ) + k - s).toNat = k by omega]

/-- A screening of a sparse input; each input term can be certified separately. -/
def shScreen (s : ℕ) (P : RawPoly ℕ) : RawPoly ℕ :=
  P.flatMap fun t => scaleR t.1 (shScreenWord s t.2)

theorem shScreen_sound (s : ℕ) (P : RawPoly ℕ) :
    shEval (shScreen s P) = EEVec (latP 1) (-1 : ℤ) (s : ℤ) (shEval P) := by
  induction P with
  | nil => simp [shScreen, shEval_nil]
  | cons t P ih =>
    rcases t with ⟨q, w⟩
    rw [shScreen, List.flatMap_cons, shEval_append, shEval_scale, shScreenWord_sound,
      ← shScreen, ih, shEval_cons, map_add, map_smul]

theorem shEval_norm (P : RawPoly ℕ) : shEval (normR P) = shEval P := by
  rw [normR, shEval, evalRaw_toRaw, evalSparse_normalizeQ]

end VOA.Classification.COne.OrbIcoT
