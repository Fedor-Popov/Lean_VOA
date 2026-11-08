import VOA.Moonshine.MoonshineCNHyperbolicCommutant
import VOA.Examples.HeisenbergNVOA

/-! # Explicit finite differential formulas for hyperbolic Sugawara modes

The infinite first-order sums are encoded by polynomial derivations. The
second-order part is a finite sum. This file constructs the operators and
proves their vacuum values and creation commutator for negative modes; it
does not yet assert the full Virasoro relations.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open MvPolynomial HeisenbergN
open scoped BigOperators

/-- The first-order part of `L_(-n)`: each variable of level `j+1` shifts up by `n`. -/
def hypRaisingDerivation (n : ℕ) : Derivation ℂ hypFock hypFock :=
  mkDerivation ℂ fun v => (v.1 + 1 : ℂ) • X (v.1 + n, v.2)

/-- The first-order part of `L_n`, including the two momentum derivatives. -/
def hypLoweringDerivation (κ ell : ℂ) (n : ℕ) : Derivation ℂ hypFock hypFock :=
  mkDerivation ℂ fun v =>
    if v.1 + 1 = n then (v.1 + 1 : ℂ) • MvPolynomial.C (if v.2 = 0 then κ else ell)
    else if n < v.1 + 1 then (v.1 + 1 : ℂ) • X (v.1 - n, v.2)
    else 0

def hypEnergyDerivation : Derivation ℂ hypFock hypFock := hypRaisingDerivation 0

/-- The multiplication part of `L_(-(j+1))`, with exactly `j` quadratic terms. -/
def hypNegativePotential (κ ell : ℂ) (j : ℕ) : hypFock :=
  κ • X (j, 1) + ell • X (j, 0) +
    ∑ k ∈ Finset.range j, X (j - 1 - k, 0) * X (k, 1)

/-- The finite second-order part of `L_(j+1)`. -/
def hypPositiveSecondOrder (j : ℕ) : Module.End ℂ hypFock :=
  ∑ k ∈ Finset.range j, ((k + 1 : ℂ) * (j - k : ℂ)) •
    ((pderiv (k, 0)).toLinearMap * (pderiv (j - 1 - k, 1)).toLinearMap)

/-- The explicit Sugawara operator at arbitrary momentum. -/
def hypSugawara (κ ell : ℂ) (n : ℤ) : Module.End ℂ hypFock :=
  if n < 0 then
    LinearMap.mul ℂ hypFock (hypNegativePotential κ ell (-n - 1).toNat) +
      (hypRaisingDerivation (-n).toNat).toLinearMap
  else if 0 < n then
    (hypLoweringDerivation κ ell n.toNat).toLinearMap +
      hypPositiveSecondOrder (n - 1).toNat
  else (κ * ell) • LinearMap.id + hypEnergyDerivation.toLinearMap

@[simp] theorem hypRaisingDerivation_X (n : ℕ) (v : ℕ × Fin 2) :
    hypRaisingDerivation n (X v) = (v.1 + 1 : ℂ) • X (v.1 + n, v.2) :=
  mkDerivation_X _ _ _

@[simp] theorem hypLoweringDerivation_X (κ ell : ℂ) (n : ℕ) (v : ℕ × Fin 2) :
    hypLoweringDerivation κ ell n (X v) =
      if v.1 + 1 = n then (v.1 + 1 : ℂ) • MvPolynomial.C (if v.2 = 0 then κ else ell)
      else if n < v.1 + 1 then (v.1 + 1 : ℂ) • X (v.1 - n, v.2) else 0 :=
  mkDerivation_X _ _ _

@[simp] theorem hypEnergyDerivation_X (v : ℕ × Fin 2) :
    hypEnergyDerivation (X v) = (v.1 + 1 : ℂ) • X v := by
  simp [hypEnergyDerivation]

theorem hypSugawara_negative (κ ell : ℂ) (j : ℕ) (p : hypFock) :
    hypSugawara κ ell (-(j + 1 : ℤ)) p =
      hypNegativePotential κ ell j * p + hypRaisingDerivation (j + 1) p := by
  rw [hypSugawara, if_pos (by omega)]
  simp

theorem hypSugawara_positive (κ ell : ℂ) (j : ℕ) (p : hypFock) :
    hypSugawara κ ell (j + 1 : ℤ) p =
      hypLoweringDerivation κ ell (j + 1) p + hypPositiveSecondOrder j p := by
  rw [hypSugawara, if_neg (by omega), if_pos (by omega)]
  simp

theorem hypSugawara_zero (κ ell : ℂ) (p : hypFock) :
    hypSugawara κ ell 0 p = (κ * ell) • p + hypEnergyDerivation p := by
  simp [hypSugawara]

theorem hypSugawara_negative_vacuum (κ ell : ℂ) (j : ℕ) :
    hypSugawara κ ell (-(j + 1 : ℤ)) 1 = hypNegativePotential κ ell j := by
  rw [hypSugawara_negative]
  simp

theorem hypSugawara_positive_vacuum (κ ell : ℂ) (j : ℕ) :
    hypSugawara κ ell (j + 1 : ℤ) 1 = 0 := by
  simp [hypSugawara_positive, hypPositiveSecondOrder, Module.End.mul_apply]

theorem hypSugawara_zero_vacuum (κ ell : ℂ) :
    hypSugawara κ ell 0 1 = (κ * ell) • (1 : hypFock) := by
  simp [hypSugawara_zero]

/-- The negative-mode creation commutator, in both isotropic families. -/
theorem hypSugawara_negative_mul_variable (κ ell : ℂ) (j : ℕ)
    (v : ℕ × Fin 2) (p : hypFock) :
    hypSugawara κ ell (-(j + 1 : ℤ)) (X v * p) -
      X v * hypSugawara κ ell (-(j + 1 : ℤ)) p =
    (v.1 + 1 : ℂ) • (X (v.1 + (j + 1), v.2) * p) := by
  rw [hypSugawara_negative, hypSugawara_negative, Derivation.leibniz,
    hypRaisingDerivation_X]
  simp only [smul_eq_mul, smul_eq_C_mul]
  ring

/-- Identification of the explicit Euler derivation with the existing Fock energy. -/
theorem hypEnergyDerivation_eq_Lvir_zero (p : hypFock) :
    hypEnergyDerivation p = LvirN 2 1 0 p := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [LvirN_zero_C]
    exact derivation_C _ _
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p v hp =>
    rw [mul_comm p (X v), Derivation.leibniz, hypEnergyDerivation_X,
      LvirN_zero_mulXN 2 1 one_ne_zero, hp]
    simp only [smul_eq_mul, smul_eq_C_mul]
    ring

/-- The explicit zero mode has the required shifted-energy eigenvalue. -/
theorem hypSugawara_zero_level (κ ell : ℂ) (N : ℤ) (p : hypFock)
    (hp : p ∈ hypLevel N) :
    hypSugawara κ ell 0 p = (κ * ell + (N : ℂ)) • p := by
  rw [hypSugawara_zero, hypEnergyDerivation_eq_Lvir_zero,
    LvirN_eq_mode_YN_omega, zero_add, conf_L0_gradingN 2 1 one_ne_zero p hp, add_smul]

/-- The exact leading multiplication term to be filtered in (F1a). -/
theorem hypSugawara_negative_leading_formula (κ ell : ℂ) (j : ℕ) (p : hypFock) :
    hypSugawara κ ell (-(j + 1 : ℤ)) p - κ • (X (j, 1) * p) =
      ell • (X (j, 0) * p) +
        (∑ k ∈ Finset.range j, X (j - 1 - k, 0) * X (k, 1)) * p +
          hypRaisingDerivation (j + 1) p := by
  rw [hypSugawara_negative, hypNegativePotential]
  simp only [smul_eq_C_mul]
  ring

end VOA.Moonshine.ConwayNorton
