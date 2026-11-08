import VOA.Moonshine.MoonshineCNMonsterForm

/-! The exact lattice normalization of the descended form on zero momentum. -/

noncomputable section
namespace VOA.Moonshine.ConwayNorton

open AutMonster LatGen Nondeg MvPolynomial IntegralLattice HeisenbergN
open scoped TensorProduct

attribute [local instance] vnatStringWeightAddCommGroup vnatStringSliceAddCommGroup
attribute [local instance] monsterPhysicalAddCommGroup

theorem moonshineMatterReversal_zeroBasis (a : Fin 2) :
    moonshineMatterReversal (moonshineMatterSectorMap ![0, 0] (vnatZeroBasisVector a)) =
      -moonshineMatterSectorMap ![0, 0] (vnatZeroBasisVector a) := by
  change moonshineMatterReversal
    (moonshineMatterSectorMap ![0, 0] (VnatVOA.vacuum ⊗ₜ X (0, a))) = _
  rw [moonshineMatterSectorMap_tmul, moonshineMatterReversal_tmul]
  have hσ : sigmaN (rank lorentzianLattice) (hypLorentzianPolynomialEquiv (X (0, a))) =
      -hypLorentzianPolynomialEquiv (X (0, a)) := by
    fin_cases a <;> simp [hypLorentzianPolynomial_X_zero, hypLorentzianPolynomial_X_one,
      sigmaN_X, smul_neg, neg_sub] <;> abel
  have hz : (-![0, 0] : lorentzianLattice.carrier) = ![0, 0] := by
    change (-![0, 0] : Fin 2 → ℤ) = ![0, 0]
    funext a; fin_cases a <;> rfl
  rw [hσ]
  change VnatVOA.vacuum ⊗ₜ latStateGen lorentzianLattice
      (-hypLorentzianPolynomialEquiv (X (0, a))) (-![0, 0]) =
    -(VnatVOA.vacuum ⊗ₜ latStateGen lorentzianLattice
      (hypLorentzianPolynomialEquiv (X (0, a))) ![0, 0])
  simpa only [latStateGen, TensorProduct.neg_tmul, TensorProduct.tmul_neg] using
    congrArg (fun α : lorentzianLattice.carrier =>
      -(VnatVOA.vacuum ⊗ₜ latStateGen lorentzianLattice
        (hypLorentzianPolynomialEquiv (X (0, a))) α)) hz

theorem moonshineMatterReversal_zeroWeight (u : vnatSectorWeight 0 0 1) :
    moonshineMatterReversal (moonshineMatterSectorMap ![0, 0] u.val) =
      -moonshineMatterSectorMap ![0, 0] u.val := by
  obtain ⟨c, rfl⟩ := vnatZeroWeightEquiv.surjective u
  change moonshineMatterReversal (moonshineMatterSectorMap ![0, 0]
    (c 0 • vnatZeroBasisVector 0 + c 1 • vnatZeroBasisVector 1)) = _
  simp only [LinearMap.map_add, LinearMap.map_smul,
    LinearEquiv.map_add, LinearEquiv.map_smul, moonshineMatterReversal_zeroBasis,
    smul_neg]
  abel

theorem moonshineMatterSector_zeroWeight_form (u v : vnatSectorWeight 0 0 1) :
    -moonshineMatterForm (moonshineMatterSectorMap ![0, 0] u.val)
      (moonshineMatterSectorMap ![0, 0] v.val) = vnatHypForm u.val v.val := by
  have h := moonshineMatterSector_form ![0, 0] u.val v.val
  change moonshineMatterForm (moonshineMatterReversal (moonshineMatterSectorMap ![0, 0] u.val))
    (moonshineMatterSectorMap ![0, 0] v.val) = _ at h
  have hz : (![0, 0] : lorentzianLattice.carrier) = 0 := by
    change (![0, 0] : Fin 2 → ℤ) = 0
    funext a; fin_cases a <;> rfl
  have hs : chSign lorentzianLattice ![0, 0] = 1 :=
    (congrArg (chSign lorentzianLattice) hz).trans (chSign_zero lorentzianLattice)
  rw [moonshineMatterReversal_zeroWeight, LinearMap.map_neg, LinearMap.neg_apply,
    hs, one_mul] at h
  exact h

def monsterLieZeroQuotientEquiv :
    (vnatStringModule 0 0 0).weightRadicalQuotient (vnatStringModule 0 0 0).physical 1 ≃ₗ[ℂ]
      monsterLieMomentum 0 :=
  (monsterLieSectorQuotientEquiv 0 0 0).trans monsterLieZeroMomentumTransport

theorem monsterLieZeroQuotientEquiv_coe
    (u : (vnatStringModule 0 0 0).weightRadicalQuotient (vnatStringModule 0 0 0).physical 1) :
    (monsterLieZeroQuotientEquiv u : monsterLieAlgebra) =
      monsterLieSectorQuotientEquiv 0 0 0 u := by
  exact monsterLieZeroMomentumTransport_coe (monsterLieSectorQuotientEquiv 0 0 0 u)

theorem monsterLieZeroQuotientEquiv_coordinates
    (u : (vnatStringModule 0 0 0).weightRadicalQuotient (vnatStringModule 0 0 0).physical 1) :
    monsterLieZeroMomentumEquiv (monsterLieZeroQuotientEquiv u) = vnatZeroNoGhostEquiv u := by
  simp only [monsterLieZeroMomentumEquiv, monsterLieZeroQuotientEquiv,
    LinearEquiv.trans_apply, monsterLieZeroMomentumTransport.symm_apply_apply,
    (monsterLieSectorQuotientEquiv 0 0 0).symm_apply_apply]

theorem monsterLieZeroQuotientEquiv_form
    (u v : (vnatStringModule 0 0 0).weightRadicalQuotient (vnatStringModule 0 0 0).physical 1) :
    monsterLieBilinearForm (monsterLieZeroQuotientEquiv u) (monsterLieZeroQuotientEquiv v) =
      (vnatStringModule 0 0 0).radicalQuotientForm (vnatStringModule 0 0 0).physical 1 u v := by
  refine (congrArg₂ (fun a b : monsterLieAlgebra => monsterLieBilinearForm a b)
    (monsterLieZeroQuotientEquiv_coe u) (monsterLieZeroQuotientEquiv_coe v)).trans ?_
  induction u using Submodule.Quotient.induction_on with | _ u =>
  induction v using Submodule.Quotient.induction_on with | _ v =>
  exact moonshineMatterSector_zeroWeight_form u.val v.val

/-- The invariant form on the zero-momentum part is the lattice form, in repository
coordinates: the form is exactly `c₀*d₁ + c₁*d₀`. -/
theorem monsterLieBilinearForm_zeroMomentum (u v : monsterLieMomentum 0) :
    monsterLieBilinearForm u v =
      monsterLieZeroMomentumEquiv u 0 * monsterLieZeroMomentumEquiv v 1 +
      monsterLieZeroMomentumEquiv u 1 * monsterLieZeroMomentumEquiv v 0 := by
  obtain ⟨p, hp⟩ := monsterLieZeroQuotientEquiv.surjective u
  obtain ⟨q, hq⟩ := monsterLieZeroQuotientEquiv.surjective v
  have hcp : vnatZeroNoGhostEquiv p = monsterLieZeroMomentumEquiv u :=
    (monsterLieZeroQuotientEquiv_coordinates p).symm.trans
      (congrArg monsterLieZeroMomentumEquiv hp)
  have hcq : vnatZeroNoGhostEquiv q = monsterLieZeroMomentumEquiv v :=
    (monsterLieZeroQuotientEquiv_coordinates q).symm.trans
      (congrArg monsterLieZeroMomentumEquiv hq)
  exact (congrArg₂ (fun a b : monsterLieMomentum 0 => monsterLieBilinearForm a b)
    hp hq).symm.trans ((monsterLieZeroQuotientEquiv_form p q).trans
      ((vnatZeroNoGhostEquiv_isometry p q).trans
        (congrArg₂ (fun a b : Fin 2 → ℂ => a 0 * b 1 + a 1 * b 0) hcp hcq)))

theorem monsterLieZeroMomentum_aut_trivial (g : AutVnat) (u : monsterLieMomentum 0) :
    monsterLieAut g u = (u : monsterLieAlgebra) := by
  obtain ⟨p, hp⟩ := monsterLieZeroQuotientEquiv.surjective u
  have ht := vnatZeroNoGhostEquiv.injective (vnatZeroNoGhostEquiv_equivariant g p)
  have he := monsterLieSectorQuotientEquiv_equivariant 0 0 0 g p
  rw [ht] at he
  rw [← hp, monsterLieZeroQuotientEquiv_coe p]
  exact he.symm

end VOA.Moonshine.ConwayNorton
