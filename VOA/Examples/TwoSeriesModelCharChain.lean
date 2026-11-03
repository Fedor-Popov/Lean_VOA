/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesModelCharProfile

/-!
# Independence along a chain of copies, and degrees of the FS functions

* `linearIndependent_mixed'` — `e^{(γ,0)}(t) · rename(f_κ)(t_B)` is independent for any
  independent family `f_κ` in the last variables (the mixed lemma with an arbitrary family);
* `FamL_linearIndependent` — **the elementary-symmetric family of a profile is linearly
  independent** (induction along the nested copies);
* `fFS_isHomogeneous` — the FS function of a profile is homogeneous of degree `degG P x`, and
  `degG + awt(top) = (sqL - tsL) + awtE` (`degG_add_degTop`).

Everything is proved outright.
-/

namespace VOA.TwoSeries.ModelChar

open MvPolynomial VOA.SymbolModel VOA.TwoSeries.StrictModel VOA.JetProduct
open scoped BigOperators

noncomputable section

/-- The mixed lemma with an arbitrary independent family on the last variables. -/
theorem linearIndependent_mixed' {m s : ℕ} {κ : Type*} {f : κ → MvPolynomial (Fin s) ℂ}
    (hf : LinearIndependent ℂ f) :
    LinearIndependent ℂ (fun p : (Fin m → ℕ) × κ =>
      esymmPow (Fin.append p.1 (fun _ : Fin s => 0)) * rename (Fin.natAdd m) (f p.2)) := by
  classical
  have htens := linearIndependent_rename_mul (m := m) (s := s) (esymmPow_linearIndependent m) hf
  rw [linearIndependent_iff']
  intro S c hS p0 hp0
  by_contra hne
  set S' := S.filter (fun p => c p ≠ 0) with hS'
  have hS'ne : S'.Nonempty := ⟨p0, Finset.mem_filter.mpr ⟨hp0, hne⟩⟩
  obtain ⟨p1, hp1, hmax⟩ := Finset.exists_max_image S' (fun p => awt p.1) hS'ne
  set D := awt p1.1
  let c' : (Fin m → ℕ) × κ → ℂ := fun p => if awt p.1 = D then c p else 0
  have hrel : ∑ p ∈ S, c' p • (rename (Fin.castAdd s) (esymmPow p.1) *
      rename (Fin.natAdd m) (f p.2)) = 0 := by
    have h := congrArg (fun P => (hz m s P).coeff D) hS
    simp only [map_sum, map_smul, Polynomial.finsetSum_coeff, Polynomial.coeff_smul, map_mul,
      hz_natAdd, Polynomial.coeff_mul_C, map_zero, Polynomial.coeff_zero] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hc : c p = 0
    · simp [c', hc]
    · have hle : awt p.1 ≤ D := hmax p (Finset.mem_filter.mpr ⟨hp, hc⟩)
      have hz1 := hz_esymmPow (s := s) p.1
      by_cases hD : awt p.1 = D
      · simp only [c', if_pos hD]
        rw [← hD, hz1.2]
      · simp only [c', if_neg hD, zero_smul]
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_ne (hz1.1.trans hle)
          (by intro h'; exact hD (le_antisymm hle (h' ▸ hz1.1)) |>.elim)), zero_mul, smul_zero]
  have := (linearIndependent_iff'.mp htens) S c' hrel p1 (Finset.mem_filter.mp hp1).1
  simp only [c'] at this
  rw [if_pos rfl] at this
  exact (Finset.mem_filter.mp hp1).2 this

/-- **The elementary-symmetric family of a profile is linearly independent.** -/
theorem FamL_linearIndependent : ∀ P : List ℕ, LinearIndependent ℂ (FamL P)
  | [] => by
    have : (FamL [] : ExpL [] → MvPolynomial (Fin (nbL [])) ℂ) = fun _ => 1 := rfl
    rw [this]
    haveI : Unique (ExpL []) := inferInstanceAs (Unique Unit)
    exact linearIndependent_unique_iff.mpr one_ne_zero
  | r :: P => linearIndependent_mixed' (m := r) (s := nbL P) (FamL_linearIndependent P)

/-! ### Degrees -/

theorem awt_append' {m s : ℕ} (γ : Fin m → ℕ) :
    awt (Fin.append γ (fun _ : Fin s => 0)) = awt γ := by
  rw [awt, awt, Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

/-- The degree of the top monomial of the copy exponents. -/
def degTop : (P : List ℕ) → ExpL P → ℕ
  | [], _ => 0
  | _ :: _, x => awt x.1

/-- The degree of `gFS P x`. -/
def degG : (P : List ℕ) → ExpL P → ℕ
  | [], _ => 0
  | _ :: P, x => (nbL P * nbL P - nbL P) + degTop P x.2 + degG P x.2

/-- `Σ` of the squared copy sizes. -/
def sqL : List ℕ → ℕ
  | [] => 0
  | _ :: P => nbL P * nbL P + sqL P

/-- The total weight of the exponents. -/
def awtE : (P : List ℕ) → ExpL P → ℕ
  | [], _ => 0
  | _ :: P, x => awt x.1 + awtE P x.2

theorem topL_isHomogeneous : ∀ (P : List ℕ) (x : ExpL P), (topL P x).IsHomogeneous (degTop P x)
  | [], _ => isHomogeneous_one _ _
  | r :: P, x => by
    have := esymmPow_isHomogeneous (r := r + nbL P) (Fin.append x.1 (fun _ : Fin (nbL P) => 0))
    rw [awt_append'] at this
    exact this

theorem gFS_isHomogeneous : ∀ (P : List ℕ) (x : ExpL P), (gFS P x).IsHomogeneous (degG P x)
  | [], _ => isHomogeneous_one _ _
  | r :: P, x => by
    have h1 := ((vdm_isHomogeneous (nbL P)).mul (topL_isHomogeneous P x.2)).rename_isHomogeneous
      (f := Fin.castAdd (tsL P))
    have h2 := (gFS_isHomogeneous P x.2).rename_isHomogeneous (f := Fin.natAdd (nbL P))
    exact h1.mul h2

theorem fFS_isHomogeneous (P : List ℕ) (x : ExpL P) : (fFS P x).IsHomogeneous (degG P x) := by
  rw [fFS]
  exact IsHomogeneous.sum _ _ _ fun σ _ => (gFS_isHomogeneous P x).rename_isHomogeneous

theorem tsL_le_sqL : ∀ P : List ℕ, tsL P ≤ sqL P
  | [] => le_rfl
  | _ :: P => by
    have := tsL_le_sqL P
    have := Nat.le_mul_self (nbL P)
    simp only [tsL, sqL]
    omega

theorem degG_add_degTop : ∀ (P : List ℕ) (x : ExpL P),
    degG P x + degTop P x = (sqL P - tsL P) + awtE P x
  | [], _ => rfl
  | _ :: P, x => by
    have ih := degG_add_degTop P x.2
    have h1 := tsL_le_sqL P
    have h2 := Nat.le_mul_self (nbL P)
    show (nbL P * nbL P - nbL P) + degTop P x.2 + degG P x.2 + awt x.1 =
      (nbL P * nbL P + sqL P - (nbL P + tsL P)) + (awt x.1 + awtE P x.2)
    omega

end

end VOA.TwoSeries.ModelChar
