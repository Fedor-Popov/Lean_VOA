import VOA.Moonshine.MoonshineCNHyperbolicNegativeModes
import VOA.Moonshine.MoonshineCNStringStraightening

/-! # The concrete negative Virasoro algebra and straightening

The commutator defect commutes with all oscillators, hence is scalar.
Its constant coefficient on the vacuum vanishes. This avoids expanding
or reindexing the quadratic potentials in a double commutator.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open MvPolynomial
open scoped BigOperators

theorem hypNegativePotential_constantCoeff (κ ell : ℂ) (j : ℕ) :
    constantCoeff (hypNegativePotential κ ell j) = 0 := by
  simp [hypNegativePotential, map_sum]

theorem hypRaisingDerivation_constantCoeff (n : ℕ) (p : hypFock) :
    constantCoeff (hypRaisingDerivation n p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp =>
    rw [Derivation.leibniz, hypRaisingDerivation_X]
    simp [smul_eq_mul, hp]

theorem hypSugawara_negative_constantCoeff (κ ell : ℂ) (j : ℕ) (p : hypFock) :
    constantCoeff (hypSugawara κ ell (-(j + 1 : ℤ)) p) = 0 := by
  rw [hypSugawara_negative]
  simp [hypNegativePotential_constantCoeff, hypRaisingDerivation_constantCoeff]

theorem hypNegativeVirasoroDefect_commutes (κ ell : ℂ) (i j : ℕ)
    (a : Fin 2) (n : ℤ) :
    ⁅⁅hypSugawara κ ell (-(i + 1 : ℤ)), hypSugawara κ ell (-(j + 1 : ℤ))⁆ -
      ((j : ℂ) - i) • hypSugawara κ ell (-((i + j + 1 : ℕ) + 1 : ℤ)),
      hypOscillator a (if a = 0 then κ else ell) n⁆ = 0 := by
  rw [sub_lie, lie_lie, smul_lie]
  simp only [hypSugawara_negative_oscillator_comm, lie_smul]
  rw [show n - (j + 1) - (i + 1) = n - ((i + j + 1 : ℕ) + 1 : ℤ) by omega,
    show n - (i + 1) - (j + 1) = n - ((i + j + 1 : ℕ) + 1 : ℤ) by omega]
  simp only [smul_smul, ← sub_smul]
  have hs : -(n : ℂ) * -((n - (j + 1) : ℤ) : ℂ) -
      -(n : ℂ) * -((n - (i + 1) : ℤ) : ℂ) - ((j : ℂ) - i) * -(n : ℂ) = 0 := by
    push_cast
    ring
  rw [hs, zero_smul]

/-- The negative Virasoro relation for the explicit hyperbolic operators. -/
theorem hypSugawara_negative_comm (κ ell : ℂ) (i j : ℕ) :
    hypSugawara κ ell (-(i + 1 : ℤ)) * hypSugawara κ ell (-(j + 1 : ℤ)) -
      hypSugawara κ ell (-(j + 1 : ℤ)) * hypSugawara κ ell (-(i + 1 : ℤ)) =
      ((j : ℂ) - i) • hypSugawara κ ell (-((i + j + 1 : ℕ) + 1 : ℤ)) := by
  let D := ⁅hypSugawara κ ell (-(i + 1 : ℤ)), hypSugawara κ ell (-(j + 1 : ℤ))⁆ -
    ((j : ℂ) - i) • hypSugawara κ ell (-((i + j + 1 : ℕ) + 1 : ℤ))
  have hcomm : ∀ a n, n ≠ 0 → D * hypOscillator a (if a = 0 then κ else ell) n =
      hypOscillator a (if a = 0 then κ else ell) n * D := by
    intro a n _
    exact sub_eq_zero.mp (hypNegativeVirasoroDefect_commutes κ ell i j a n)
  have hc : coeff 0 (D 1) = 0 := by
    change constantCoeff (D 1) = 0
    simp only [D, Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
      LinearMap.smul_apply, map_sub, constantCoeff_smul]
    simp only [hypSugawara_negative_constantCoeff, sub_self, smul_zero]
  have he := hypCommutant_scalar D (fun a => if a = 0 then κ else ell) hcomm
  rw [hc, zero_smul] at he
  exact sub_eq_zero.mp he

/-- All concrete negative words straighten, at precisely their original energy. -/
theorem hypSugawara_negative_straightening (κ ell : ℂ) (p : hypFock) (w : List ℕ) :
    stringNegativeWord (fun i => hypSugawara κ ell (-(i + 1 : ℤ))) p w ∈
      stringSortedSpan (fun i => hypSugawara κ ell (-(i + 1 : ℤ))) p
        (stringWordEnergy w) :=
  stringNegativeWord_mem_sortedSpan _ (hypSugawara_negative_comm κ ell) p w

theorem hypSugawara_negative_nonempty_straightening (κ ell : ℂ) (p : hypFock)
    (w : List ℕ) (hw : w ≠ []) :
    stringNegativeWord (fun i => hypSugawara κ ell (-(i + 1 : ℤ))) p w ∈
      Submodule.span ℂ {y | ∃ v : List ℕ,
        v ≠ [] ∧ stringSortedWord v ∧ stringWordEnergy v = stringWordEnergy w ∧
          stringNegativeWord (fun i => hypSugawara κ ell (-(i + 1 : ℤ))) p v = y} :=
  stringNegativeWord_mem_nonempty_sortedSpan _ (hypSugawara_negative_comm κ ell) p w hw

end VOA.Moonshine.ConwayNorton
