/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoCertificateData
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Soundness of the light integer-only two-site equality checker. -/
namespace VOA.DeligneAudit.D4Two.Certificate

@[simp] theorem coeff_nil (i : ℕ) : coeff [] i = 0 := rfl

@[simp] theorem coeff_cons (p : ℕ × ℤ) (v : SV) (i : ℕ) :
    coeff (p :: v) i = (if p.1 = i then p.2 else 0) + coeff v i := by
  simp [coeff]

@[simp] theorem coeff_append (v w : SV) (i : ℕ) :
    coeff (v ++ w) i = coeff v i + coeff w i := by
  simp [coeff]

@[simp] theorem coeff_scale (a : ℤ) (v : SV) (i : ℕ) :
    coeff (scale a v) i = a * coeff v i := by
  induction v with
  | nil => simp [scale]
  | cons p v ih =>
      simp only [scale, List.map_cons, coeff_cons] at ih ⊢
      rw [ih, mul_add]
      split_ifs <;> simp

/-- The finite support certificate is checked explicitly, so no ordering
or completeness of the supplied coordinate list is assumed. -/
theorem coeff_zero_of_zeroOn {coordinates : List ℕ} {v : SV}
    (h : zeroOnCheck coordinates v = true) (i : ℕ) : coeff v i = 0 := by
  have hparts : (v.all fun t => t.1 ∈ coordinates) = true ∧
      (coordinates.all fun j => coeff v j == 0) = true := by
    simpa only [zeroOnCheck, Bool.and_eq_true] using h
  have hs : ∀ p ∈ v, p.1 ∈ coordinates := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using hparts.1
  have hz : ∀ j ∈ coordinates, coeff v j = 0 := by
    simpa only [List.all_eq_true, beq_iff_eq] using hparts.2
  by_cases hi : i ∈ coordinates
  · exact hz i hi
  · unfold coeff
    apply List.sum_eq_zero
    intro z hz
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
    have hp' : p.1 ≠ i := by
      intro he
      exact hi (he ▸ hs p hp)
    simp [hp']

/-- The complex coordinate vector represented by a sparse integer list. -/
def vec (n : ℕ) (v : SV) : Fin n → ℂ := fun i => (coeff v i : ℂ)

@[simp] theorem vec_append (n : ℕ) (v w : SV) :
    vec n (v ++ w) = vec n v + vec n w := by
  funext i
  simp [vec]

@[simp] theorem vec_scale (n : ℕ) (a : ℤ) (v : SV) :
    vec n (scale a v) = (a : ℂ) • vec n v := by
  funext i
  simp [vec]

theorem vec_flatMap {α : Type*} (n : ℕ) (l : List α) (g : α → SV) :
    vec n (l.flatMap g) = (l.map fun a => vec n (g a)).sum := by
  induction l with
  | nil => funext i; simp [vec]
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem vec_zero_of_zeroOn (n : ℕ) {coordinates : List ℕ} {v : SV}
    (h : zeroOnCheck coordinates v = true) : vec n v = 0 := by
  funext i
  simp [vec, coeff_zero_of_zeroOn h i]

/-- A checked, denominator-cleared relation gives an actual complex
vector equality. The denominator will be checked nonzero before division. -/
theorem vec_eq_of_zeroOn (n : ℕ) (a : ℤ) (v w : SV) (coordinates : List ℕ)
    (h : zeroOnCheck coordinates (scale a v ++ scale (-1) w) = true) :
    (a : ℂ) • vec n v = vec n w := by
  apply sub_eq_zero.mp
  simpa only [vec_append, vec_scale, Int.cast_neg, Int.cast_one, neg_one_smul,
    sub_eq_add_neg] using vec_zero_of_zeroOn n h

end VOA.DeligneAudit.D4Two.Certificate

#print axioms VOA.DeligneAudit.D4Two.Certificate.vec_eq_of_zeroOn
