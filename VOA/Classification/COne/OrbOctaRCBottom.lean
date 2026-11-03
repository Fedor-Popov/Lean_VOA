import VOA.Classification.COne.OrbOctaRCExp

/-! The lowest oscillator coefficient of an exponential action. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbOctaRC
open VOA VOA.SparseRational HeisenbergN PlusC2Eval PlusUnitary OrbC2e OrbC2g

theorem expWordR_below {r : ℕ} (a : Fin r) (c : ℂ) (w : List ℕ) (s : ℤ)
    (hs : s + wWtC w < 0) : evRc a c (expWordR w s) = 0 := by
  induction w generalizing s with
  | nil => simp only [wWtC, Nat.cast_zero, add_zero] at hs
           simp [expWordR, not_le.mpr hs, evRc_nil]
  | cons i w ih =>
    cases i with
    | zero =>
      rw [expWordR, evRc_prependC, ih _ hs, mul_zero]
    | succ i =>
      simp only [wWtC, Nat.cast_add, Nat.cast_one] at hs
      rw [expWordR, evRc_normR, evRc_append, evRc_prependC,
        evRc_scaleR, evRc_prependC, ih s (by omega), ih (s + i + 1) (by omega)]
      simp

theorem expWordR_bottom {r : ℕ} (a : Fin r) (c : ℂ) (w : List ℕ)
    (hw : ∀ i ∈ w, 0 < i) :
    evRc a c (expWordR w (-(wWtC w : ℤ))) = (-c) ^ w.length • (1 : FockN r) := by
  induction w with
  | nil => simp [wWtC, expWordR, schurR, evRc_cons, evRc_nil, evalWordC_nil]
  | cons i w ih =>
    have hi := hw i (by simp)
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    have ht : ∀ j ∈ w, 0 < j := fun j hj => hw j (by simp [hj])
    have hs : -((wWtC ((i + 1) :: w) : ℕ) : ℤ) + i + 1 = -(wWtC w : ℤ) := by
      simp only [wWtC, Nat.cast_add, Nat.cast_one]
      ring
    rw [expWordR, evRc_normR, evRc_append, evRc_prependC,
      expWordR_below _ _ w _ (by simp only [wWtC, Nat.cast_add, Nat.cast_one]; omega),
      mul_zero, zero_add, evRc_scaleR, evRc_prependC, hs, ih ht]
    simp only [xvc, List.length_cons, Rat.cast_neg, Rat.cast_one,
      pow_succ, ← MvPolynomial.smul_eq_C_mul, smul_smul]
    congr 1
    ring

def bottomValue (c : ℂ) (P : RawPoly ℕ) : ℂ :=
  (P.map fun t => (t.1 : ℂ) * (-c) ^ t.2.length).sum

theorem expPolyR_bottom {r : ℕ} (a : Fin r) (c : ℂ) (P : RawPoly ℕ) (N : ℕ)
    (hP : ∀ t ∈ P, wWtC t.2 = N ∧ ∀ i ∈ t.2, 0 < i) :
    evRc a c (expPolyR (-(N : ℤ)) P) = bottomValue c P • (1 : FockN r) := by
  rw [expPolyR, evRc_normR]
  induction P with
  | nil => simp [evRc_nil, bottomValue]
  | cons t P ih =>
    have ht := hP t (by simp)
    rw [List.flatMap_cons, evRc_append, evRc_scaleR, ← ht.1,
      expWordR_bottom _ _ _ ht.2, ht.1, ih (fun u hu => hP u (by simp [hu]))]
    simp [bottomValue, add_smul, smul_smul]

end VOA.Classification.COne.OrbOctaRC
