import VOA.Moonshine.MoonshineCNSectorFrame

/-! All Heisenberg modes under the explicit hyperbolic complex frame. -/

noncomputable section
namespace VOA.Moonshine.ConwayNorton

open IntegralLattice HeisenbergN LatGen MvPolynomial
open scoped TensorProduct BigOperators

def lorentzianIsotropicVector (a : Fin 2) : lorentzianLattice.carrier :=
  if a = 0 then ![0, 1] else ![1, 0]

theorem lorentzianIsotropicVector_pairing (a b : Fin 2) :
    lorentzianLattice.form (lorentzianIsotropicVector a) (lorentzianIsotropicVector b) =
      if a = b.rev then 1 else 0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [lorentzianIsotropicVector, lorentzian_form_apply, Fin.rev, Fin.last]

theorem hypLorentzianPolynomial_variable (j : ℕ) (a : Fin 2) :
    hypLorentzianPolynomialEquiv (X (j, a)) =
      creationVariable lorentzianComplexFrame (lorentzianIsotropicVector a) j := by
  change _ = ∑ b, complexHyperbolicCoordinate (lorentzianIsotropicVector a)
    (finCongr lorentzian_rank b) • X (j, b)
  rw [← Equiv.sum_comp (finCongr lorentzian_rank).symm
    (fun b => complexHyperbolicCoordinate (lorentzianIsotropicVector a)
      (finCongr lorentzian_rank b) • (X (j, b) : FockN (rank lorentzianLattice)))]
  fin_cases a <;>
    simp [hypLorentzianPolynomial_X_zero, hypLorentzianPolynomial_X_one,
      Fin.sum_univ_two, lorentzianIsotropicVector, complexHyperbolicCoordinate,
      sub_eq_add_neg, neg_smul, div_eq_mul_inv]

theorem hypLorentzianPolynomial_creation (a : Fin 2) (q : ℂ) (j : ℕ) (p : hypFock) :
    hypLorentzianPolynomialEquiv (hypOscillator a q (-(j + 1 : ℤ)) p) =
      frameOscillator lorentzianComplexFrame (lorentzianIsotropicVector a)
        (-(j + 1 : ℤ)) (hypLorentzianPolynomialEquiv p) := by
  rw [hypOscillator_negative_apply, map_mul, hypLorentzianPolynomial_variable,
    frameOscillator_neg_eq_mulLeft_creationVariable, LinearMap.mulLeft_apply]

theorem hypLorentzianPolynomial_oscillator_positive (a : Fin 2) (n : ℤ)
    (hn : 0 < n) (p : hypFock) :
    hypLorentzianPolynomialEquiv (hypOscillator a 0 n p) =
      frameOscillator lorentzianComplexFrame (lorentzianIsotropicVector a) n
        (hypLorentzianPolynomialEquiv p) := by
  have hcreate (v : ℕ × Fin 2) (q : hypFock) :
      hypLorentzianPolynomialEquiv (X v * q) =
        frameOscillator lorentzianComplexFrame (lorentzianIsotropicVector v.2)
          (-(v.1 + 1 : ℤ)) (hypLorentzianPolynomialEquiv q) := by
    simpa only [hypOscillator_negative_apply] using
      hypLorentzianPolynomial_creation v.2 0 v.1 q
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [C_eq_smul_one, map_smul, hypOscillator_vacuum _ _ _ hn, smul_zero, map_zero,
      map_smul, map_one, map_smul]
    rw [show frameOscillator lorentzianComplexFrame (lorentzianIsotropicVector a) n 1 = 0
      from frameOscillator_vacuum _ _ _ (le_of_lt hn), smul_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    rw [mul_comm p (X v), hcreate]
    have hh := LinearMap.congr_fun (hypOscillator_comm a v.2 0 0 n (-(v.1 + 1 : ℤ))) p
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hypOscillator_negative_apply,
      LinearMap.smul_apply, LinearMap.id_apply] at hh
    have hf := LinearMap.congr_fun (frameOscillator_commutator lorentzianComplexFrame
      (lorentzianIsotropicVector a) (lorentzianIsotropicVector v.2)
        n (-(v.1 + 1 : ℤ))) (hypLorentzianPolynomialEquiv p)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      LinearMap.id_apply, lorentzianIsotropicVector_pairing] at hf
    rw [sub_eq_iff_eq_add] at hh hf
    rw [hh, map_add, hcreate, hp, hf]
    congr 1
    split_ifs <;> simp_all

/-- No zero-charge restriction on momentum is needed: this is the oscillator part. -/
theorem hypLorentzianPolynomial_oscillator (a : Fin 2) (n : ℤ) (p : hypFock) :
    hypLorentzianPolynomialEquiv (hypOscillator a 0 n p) =
      frameOscillator lorentzianComplexFrame (lorentzianIsotropicVector a) n
        (hypLorentzianPolynomialEquiv p) := by
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = -(j + 1 : ℤ) := ⟨(-n - 1).toNat, by omega⟩
    exact hypLorentzianPolynomial_creation a 0 j p
  · simp [frameOscillator]
  · exact hypLorentzianPolynomial_oscillator_positive a n hn p

theorem hypLorentzianPolynomial_constantCoeff (p : hypFock) :
    constantCoeff (hypLorentzianPolynomialEquiv p) = constantCoeff p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [C_eq_smul_one]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_mul, map_mul, hp]
    have hz : constantCoeff (hypLorentzianPolynomialEquiv (X v)) = 0 := by
      rcases v with ⟨j, a⟩
      fin_cases a <;>
        simp [hypLorentzianPolynomial_X_zero, hypLorentzianPolynomial_X_one]
    rw [hz, constantCoeff_X]

end VOA.Moonshine.ConwayNorton
