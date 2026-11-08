import VOA.Moonshine.MoonshineCNSectorFormComparison

/-! Polynomial formulas for the actual charged-sector Virasoro operators. -/

noncomputable section
namespace VOA.Moonshine.ConwayNorton

open IntegralLattice HeisenbergN LatGen Nondeg MvPolynomial
open scoped TensorProduct

theorem hypLorentzianPolynomial_chargedOscillator (a : Fin 2) (c : ℂ)
    (n : ℤ) (p : hypFock) :
    hypLorentzianPolynomialEquiv (hypOscillator a c n p) =
      frameOscillator lorentzianComplexFrame (lorentzianIsotropicVector a) n
        (hypLorentzianPolynomialEquiv p) +
      if n = 0 then c • hypLorentzianPolynomialEquiv p else 0 := by
  by_cases hn : n = 0
  · subst n
    simp [frameOscillator_zero]
  · rw [if_neg hn, add_zero, ← hypLorentzianPolynomial_oscillator]
    congr 1
    rcases lt_or_gt_of_ne hn with hn | hn
    · rw [hypOscillator_neg _ _ _ hn, hypOscillator_neg _ _ _ hn]
    · rw [hypOscillator_pos _ _ _ hn, hypOscillator_pos _ _ _ hn]

theorem lorentzianIsotropicVector_charge (x y : ℤ) (a : Fin 2) :
    (lorentzianLattice.form ![x, y] (lorentzianIsotropicVector a) : ℂ) =
      if a = 0 then (x : ℂ) else (y : ℂ) := by
  fin_cases a <;> simp [lorentzianIsotropicVector, lorentzian_form_apply]

def lorentzianSectorVirasoro (α : lorentzianLattice.carrier) (n : ℤ) :
    Module.End ℂ (FockN (rank lorentzianLattice)) :=
  LvirN (rank lorentzianLattice) 1 n + frameOscillator lorentzianComplexFrame α n +
    if n = 0 then ((1 / 2 : ℂ) * (lorentzianLattice.form α α : ℂ)) • LinearMap.id else 0

theorem lorentzianSectorVirasoro_apply (α : lorentzianLattice.carrier)
    (n : ℤ) (p : FockN (rank lorentzianLattice)) :
    lorentzianSectorVirasoro α n p =
      LvirN (rank lorentzianLattice) 1 n p + frameOscillator lorentzianComplexFrame α n p +
        if n = 0 then ((1 / 2 : ℂ) * (lorentzianLattice.form α α : ℂ)) • p else 0 := by
  simp only [lorentzianSectorVirasoro, LinearMap.add_apply]
  split_ifs <;> rfl

theorem lorentzianSectorVirasoro_tmul (α : lorentzianLattice.carrier)
    (n : ℤ) (p : FockN (rank lorentzianLattice)) :
    lorentzianNearVOA.L n (latStateGen lorentzianLattice p α) =
      latStateGen lorentzianLattice (lorentzianSectorVirasoro α n p) α := by
  rw [show lorentzianNearVOA.L n = frameVirasoroMode lorentzianComplexFrame n from
    mode_frameStateField_omega_eq_frameVirasoroMode _ lorentzian_even n,
    frameVirasoroMode_tmul, lorentzianSectorVirasoro_apply]
  split_ifs <;> simp [latStateGen, TensorProduct.add_tmul, TensorProduct.smul_tmul']

theorem lorentzianSectorVirasoro_nonnegative_one (x y n : ℤ) (hn : 0 ≤ n) :
    lorentzianSectorVirasoro ![x, y] n 1 =
      if n = 0 then ((x : ℂ) * y) • (1 : FockN (rank lorentzianLattice)) else 0 := by
  rw [lorentzianSectorVirasoro_apply,
    show LvirN (rank lorentzianLattice) 1 n 1 = 0 from LvirN_vacuum _ _ (by omega),
    show frameOscillator lorentzianComplexFrame ![x, y] n 1 = 0 from
      frameOscillator_vacuum _ _ _ hn, zero_add, zero_add]
  congr 1
  congr 1
  push_cast [lorentzian_form_apply]
  ring

theorem lorentzianSectorVirasoro_creation (x y m : ℤ) (a : Fin 2) (j : ℕ)
    (p : hypFock) :
    lorentzianSectorVirasoro ![x, y] m
      (hypLorentzianPolynomialEquiv (X (j, a) * p)) =
      (j + 1 : ℂ) • hypLorentzianPolynomialEquiv
        (hypOscillator a (if a = 0 then (x : ℂ) else y) (m - (j + 1 : ℤ)) p) +
      frameOscillator lorentzianComplexFrame (lorentzianIsotropicVector a)
        (-(j + 1 : ℤ)) (lorentzianSectorVirasoro ![x, y] m
          (hypLorentzianPolynomialEquiv p)) := by
  have hc := hypLorentzianPolynomial_creation a 0 j p
  rw [hypOscillator_negative_apply] at hc
  rw [hc, hypLorentzianPolynomial_chargedOscillator,
    lorentzianSectorVirasoro_apply, lorentzianSectorVirasoro_apply,
    LvirN_frameOscillator]
  have hf := LinearMap.congr_fun (frameOscillator_commutator lorentzianComplexFrame
    ![x, y] (lorentzianIsotropicVector a) m (-(j + 1 : ℤ)))
      (hypLorentzianPolynomialEquiv p)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    LinearMap.id_apply, lorentzianIsotropicVector_charge] at hf
  rw [sub_eq_iff_eq_add] at hf
  rw [hf]
  simp only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
    neg_neg, ← sub_eq_add_neg, map_add]
  by_cases hmj : m - (j + 1 : ℤ) = 0
  · have hm : m ≠ 0 := by omega
    rw [if_pos hmj, if_pos hmj, if_neg hm, if_neg hm, map_zero]
    have he : (m : ℂ) = (j + 1 : ℂ) := by exact_mod_cast (show m = j + 1 by omega)
    rw [he]
    simp only [smul_add, smul_smul]
    module
  · rw [if_neg hmj, if_neg hmj]
    by_cases hm : m = 0
    · rw [if_pos hm, if_pos hm, map_smul]
      simp only [smul_zero, add_zero, zero_smul, zero_add]
      module
    · rw [if_neg hm, if_neg hm, map_zero]
      simp only [smul_zero, add_zero, zero_smul, zero_add]
      module

/-- The oscillator sign in reversal cancels the anti-adjoint charge term. -/
theorem lorentzianSectorVirasoro_adjoint (α : lorentzianLattice.carrier) (n : ℤ)
    (p q : FockN (rank lorentzianLattice)) :
    uForm (rank lorentzianLattice)
      (sigmaN (rank lorentzianLattice) (lorentzianSectorVirasoro α n p)) q =
      uForm (rank lorentzianLattice) (sigmaN (rank lorentzianLattice) p)
        (lorentzianSectorVirasoro α (-n) q) := by
  rw [lorentzianSectorVirasoro_apply, lorentzianSectorVirasoro_apply]
  simp only [map_add, LinearMap.add_apply, sigmaN_virasoro, sigmaN_frameOscillator,
    map_neg, LinearMap.neg_apply, uForm_virasoro_adjoint,
    uForm_frameOscillator_adjoint, neg_neg]
  by_cases hn : n = 0
  · subst n
    simp only [neg_zero, if_true, map_smul, LinearMap.smul_apply]
  · rw [if_neg hn, if_neg (neg_ne_zero.mpr hn)]
    simp only [map_zero, LinearMap.zero_apply]

end VOA.Moonshine.ConwayNorton
