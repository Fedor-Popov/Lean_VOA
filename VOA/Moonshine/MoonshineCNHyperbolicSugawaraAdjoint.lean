import VOA.Moonshine.MoonshineCNHyperbolicPositiveCreation
import VOA.Moonshine.MoonshineCNHyperbolicNegativeVirasoro
import VOA.Moonshine.MoonshineCNHyperbolicForm
import Mathlib.Algebra.DirectSum.Decomposition

/-! # Adjointness of every explicit Sugawara mode

Creation induction uses the already established negative mixed commutator
and the positive creation commutator. No Virasoro form datum is assumed.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open MvPolynomial

theorem hypForm_sugawara_negative_adjoint (κ ell : ℂ) (j : ℕ) (p q : hypFock) :
    hypForm (hypSugawara κ ell (-(j + 1 : ℤ)) p) q =
      hypForm p (hypSugawara κ ell (j + 1 : ℤ) q) := by
  have hright (t : ℕ) (a : Fin 2) (charge : ℂ) (p q : hypFock) :
      hypForm p (X (t, a) * q) = hypForm (hypOscillator a charge (t + 1 : ℤ) p) q := by
    rw [hypForm_oscillator_adjoint, hypOscillator_negative_apply]
  suffices h : ∀ q p : hypFock,
      hypForm (hypSugawara κ ell (-(j + 1 : ℤ)) p) q =
        hypForm p (hypSugawara κ ell (j + 1 : ℤ) q) from h q p
  intro q
  induction q using MvPolynomial.induction_on with
  | C c =>
    intro p
    rw [show MvPolynomial.C c = c • (1 : hypFock) by simp [smul_eq_C_mul],
      map_smul, map_smul, hypSugawara_positive_vacuum, smul_zero, map_zero,
      hypForm_symm _ 1, hypForm_one]
    change c • constantCoeff (hypSugawara κ ell (-(j + 1 : ℤ)) p) = 0
    rw [hypSugawara_negative_constantCoeff, smul_zero]
  | add q r hq hr =>
    intro p
    rw [map_add, map_add, map_add, hq, hr]
  | mul_X q v ih =>
    intro p
    obtain ⟨t, a⟩ := v
    rw [mul_comm q (X (t, a))]
    have hc := LinearMap.congr_fun
      (hypSugawara_negative_oscillator_comm κ ell j a (t + 1 : ℤ)) p
    simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
      LinearMap.smul_apply, Int.cast_add, Int.cast_natCast, Int.cast_one] at hc
    have he : hypOscillator a (if a = 0 then κ else ell) (t + 1 : ℤ)
        (hypSugawara κ ell (-(j + 1 : ℤ)) p) =
        hypSugawara κ ell (-(j + 1 : ℤ))
          (hypOscillator a (if a = 0 then κ else ell) (t + 1 : ℤ) p) +
        (t + 1 : ℂ) • hypOscillator a (if a = 0 then κ else ell) (t + 1 - (j + 1)) p := by
      calc
        _ = hypSugawara κ ell (-(j + 1 : ℤ))
              (hypOscillator a (if a = 0 then κ else ell) (t + 1 : ℤ) p) -
            (hypSugawara κ ell (-(j + 1 : ℤ))
              (hypOscillator a (if a = 0 then κ else ell) (t + 1 : ℤ) p) -
              hypOscillator a (if a = 0 then κ else ell) (t + 1 : ℤ)
                (hypSugawara κ ell (-(j + 1 : ℤ)) p)) := by abel
        _ = _ := by rw [hc, neg_smul, sub_neg_eq_add]
    rw [hright t a (if a = 0 then κ else ell), he, map_add, LinearMap.add_apply,
      ih, LinearMap.map_smul₂, hypForm_oscillator_adjoint, hypForm_oscillator_adjoint,
      hypOscillator_negative_apply,
      show -(t + 1 - (j + 1) : ℤ) = (j : ℤ) - t by omega]
    rw [← map_smul, ← map_add]
    congr 1
    have h := hypSugawara_positive_creation κ ell j t a q
    exact (add_comm _ _).trans (sub_eq_iff_eq_add.mp h).symm

theorem hypForm_sugawara_zero_adjoint (κ ell : ℂ) (p q : hypFock) :
    hypForm (hypSugawara κ ell 0 p) q = hypForm p (hypSugawara κ ell 0 q) := by
  letI : DirectSum.Decomposition hypLevel := hypLevel_isInternal.chooseDecomposition
  induction p using DirectSum.Decomposition.inductionOn hypLevel with
  | zero => simp
  | add p r hp hr => simp only [map_add, LinearMap.add_apply, hp, hr]
  | homogeneous p =>
    rename_i N
    induction q using DirectSum.Decomposition.inductionOn hypLevel with
    | zero => simp
    | add q r hq hr => simp only [map_add, hq, hr]
    | homogeneous q =>
      rename_i Q
      rw [hypSugawara_zero_level κ ell N p p.property,
        hypSugawara_zero_level κ ell Q q q.property, LinearMap.map_smul₂, map_smul]
      by_cases h : N = Q
      · simp only [h]
      · rw [hypForm_orthogonal N Q h p q p.property q.property, smul_zero, smul_zero]

/-- All signed modes are contravariant for the concrete hyperbolic form. -/
theorem hypForm_sugawara_adjoint (κ ell : ℂ) (n : ℤ) (p q : hypFock) :
    hypForm (hypSugawara κ ell n p) q = hypForm p (hypSugawara κ ell (-n) q) := by
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = -(j + 1 : ℤ) := ⟨(-n - 1).toNat, by omega⟩
    simpa only [neg_neg] using hypForm_sugawara_negative_adjoint κ ell j p q
  · exact hypForm_sugawara_zero_adjoint κ ell p q
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = (j + 1 : ℤ) := ⟨(n - 1).toNat, by omega⟩
    rw [hypForm_symm, hypForm_symm p, hypForm_sugawara_negative_adjoint]

end VOA.Moonshine.ConwayNorton
