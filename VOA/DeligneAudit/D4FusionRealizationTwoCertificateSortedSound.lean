/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoCertificateSound
import VOA.DeligneAudit.D4FusionRealizationTwoCertificateSortedData

/-! Soundness uses permutation only. No claim that the sorting comparator
or the supplied input ordering has been verified is required. -/
namespace VOA.DeligneAudit.D4Two.Certificate

theorem coeff_perm {v w : SV} (h : v.Perm w) (i : ℕ) : coeff v i = coeff w i := by
  simpa only [coeff] using
    (h.map (fun p : ℕ × ℤ => if p.1 = i then p.2 else 0)).sum_eq

theorem groupedZero_sound (key : ℕ) (a : ℤ) (v : SV)
    (h : groupedZero key a v = true) (i : ℕ) : coeff ((key, a) :: v) i = 0 := by
  induction v generalizing key a with
  | nil =>
      have ha : a = 0 := by simpa only [groupedZero, beq_iff_eq] using h
      simp [ha]
  | cons p v ih =>
      rcases p with ⟨j, b⟩
      simp only [groupedZero] at h
      split_ifs at h with hj
      · subst j
        have hz := ih key (a + b) h
        by_cases hi : key = i
        · simpa only [coeff_cons, if_pos hi, add_assoc] using hz
        · simpa only [coeff_cons, if_neg hi, zero_add] using hz
      · have hp : a = 0 ∧ groupedZero j b v = true := by
          simpa only [Bool.and_eq_true, beq_iff_eq] using h
        simpa [hp.1] using ih j b hp.2

/-- Acceptance implies all coefficients vanish, even if the sort has only
rearranged unsorted input: every completed group is checked zero. -/
theorem coeff_zero_of_sortedZero {v : SV} (h : sortedZero v = true) (i : ℕ) :
    coeff v i = 0 := by
  rw [← coeff_perm (msort_perm 40 v) i]
  unfold sortedZero at h
  split at h
  · rename_i he
    rw [he]
    rfl
  · rename_i p rest he
    rw [he]
    exact groupedZero_sound p.1 p.2 rest h i

theorem vec_zero_of_sortedZero (n : ℕ) {v : SV} (h : sortedZero v = true) :
    vec n v = 0 := by
  funext i
  simp [vec, coeff_zero_of_sortedZero h i]

theorem vec_eq_of_sortedZero (n : ℕ) (a : ℤ) (v w : SV)
    (h : sortedZero (scale a v ++ scale (-1) w) = true) :
    (a : ℂ) • vec n v = vec n w := by
  apply sub_eq_zero.mp
  simpa only [vec_append, vec_scale, Int.cast_neg, Int.cast_one, neg_one_smul,
    sub_eq_add_neg] using vec_zero_of_sortedZero n h

end VOA.DeligneAudit.D4Two.Certificate

#print axioms VOA.DeligneAudit.D4Two.Certificate.vec_eq_of_sortedZero
