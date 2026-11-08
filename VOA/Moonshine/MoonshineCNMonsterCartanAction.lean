import VOA.Moonshine.MoonshineCNMonsterZeroForm
import VOA.Moonshine.MoonshineCNCurrentAdjoint
import VOA.Moonshine.MoonshineCNRealization

/-! The Cartan action on the Monster Lie algebra.

A zero-momentum element with no-ghost coordinates `(c₀, c₁)` acts on the momentum-`(x, y)`
space by the scalar `c₀ x + c₁ y`.  The proof evaluates the two hyperbolic Heisenberg currents
of the actual Lorentzian lattice vertex algebra: their zero modes are combinations of the
complex-frame momentum operators, and the frame change produces exactly `x` and `y`. -/

noncomputable section
namespace VOA.Moonshine.ConwayNorton

open AutMonster LatGen IntegralLattice HeisenbergN MvPolynomial
open scoped TensorProduct

attribute [local instance] vnatStringWeightAddCommGroup vnatStringSliceAddCommGroup
attribute [local instance] monsterPhysicalAddCommGroup

/-- The one-oscillator frame word state is the corresponding polynomial state. -/
theorem frameWordState_single_oscillator (b : Fin (rank lorentzianLattice)) :
    frameWordState lorentzianLattice [(0, b)] 0 = latStateGen lorentzianLattice (X (0, b)) 0 := by
  simp only [frameWordState, latChargeGen, latStateGen, LinearMap.rTensor_tmul, currentN_apply,
    vacuumN]
  rw [oscN_neg _ _ _ (by norm_num), mulXN_apply]
  simp

theorem lorentzianFrame_coordinate_zero (β : lorentzianLattice.carrier) :
    lorentzianComplexFrame.coordinate β ((finCongr lorentzian_rank).symm 0) =
      (β 0 : ℂ) + (β 1 : ℂ) / 2 := by
  change complexHyperbolicCoordinate β (finCongr lorentzian_rank
    ((finCongr lorentzian_rank).symm 0)) = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem lorentzianFrame_coordinate_one (β : lorentzianLattice.carrier) :
    lorentzianComplexFrame.coordinate β ((finCongr lorentzian_rank).symm 1) =
      Complex.I * ((β 0 : ℂ) - (β 1 : ℂ) / 2) := by
  change complexHyperbolicCoordinate β (finCongr lorentzian_rank
    ((finCongr lorentzian_rank).symm 1)) = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- The zero mode of a complex-frame current is the frame momentum. -/
theorem lorentzianFrameCurrent_zeroMode (b : Fin (rank lorentzianLattice))
    (p : FockN (rank lorentzianLattice)) (β : lorentzianLattice.carrier) :
    lorentzianNearVOA.Y (latStateGen lorentzianLattice (X (0, b)) 0) (-1)
        (latStateGen lorentzianLattice p β) =
      lorentzianComplexFrame.coordinate β b • latStateGen lorentzianLattice p β := by
  rw [← frameWordState_single_oscillator]
  change frameStateField lorentzianComplexFrame lorentzian_even
    (frameWordState lorentzianLattice [(0, b)] 0) (-1) _ = _
  rw [frameStateField_currentState, frameCurrent_apply, if_pos rfl, currentN_apply]
  simp only [show -(-1 : ℤ) - 1 = 0 by norm_num, oscN_zero, LinearMap.rTensor_zero, zero_add,
    frameMomentum_latStateGen]
  rfl

theorem latStateGen_add_smul (q r : FockN (rank lorentzianLattice)) (c d : ℂ)
    (α : lorentzianLattice.carrier) :
    latStateGen lorentzianLattice (c • q + d • r) α =
      c • latStateGen lorentzianLattice q α + d • latStateGen lorentzianLattice r α := by
  simp only [latStateGen, TensorProduct.add_tmul, TensorProduct.smul_tmul']

/-- The zero mode of the `a`-th hyperbolic current multiplies momentum `β` by `β a`. -/
theorem lorentzianHyperbolicCurrent_zeroMode (a : Fin 2) (p : FockN (rank lorentzianLattice))
    (β : lorentzianLattice.carrier) :
    lorentzianNearVOA.Y (latStateGen lorentzianLattice (hypLorentzianPolynomialEquiv (X (0, a))) 0)
        (-1) (latStateGen lorentzianLattice p β) =
      ((β a : ℤ) : ℂ) • latStateGen lorentzianLattice p β := by
  fin_cases a
  · have h : hypLorentzianPolynomialEquiv (X (0, (0 : Fin 2))) =
        (1 / 2 : ℂ) • X (0, (finCongr lorentzian_rank).symm 0) +
          (-(Complex.I / 2)) • X (0, (finCongr lorentzian_rank).symm 1) := by
      rw [hypLorentzianPolynomial_X_zero, neg_smul, sub_eq_add_neg]
    simp only [Fin.zero_eta]
    rw [h, latStateGen_add_smul, map_add, map_smul, map_smul]
    change (1 / 2 : ℂ) • lorentzianNearVOA.Y _ (-1) _ +
      (-(Complex.I / 2)) • lorentzianNearVOA.Y _ (-1) _ = _
    rw [lorentzianFrameCurrent_zeroMode, lorentzianFrameCurrent_zeroMode,
      lorentzianFrame_coordinate_zero, lorentzianFrame_coordinate_one, smul_smul, smul_smul,
      ← add_smul]
    congr 1
    linear_combination (-(1 / 2) * ((β 0 : ℂ) - (β 1 : ℂ) / 2)) * Complex.I_mul_I
  · have h : hypLorentzianPolynomialEquiv (X (0, (1 : Fin 2))) =
        (1 : ℂ) • X (0, (finCongr lorentzian_rank).symm 0) +
          Complex.I • X (0, (finCongr lorentzian_rank).symm 1) := by
      rw [hypLorentzianPolynomial_X_one, one_smul]
    simp only [Fin.mk_one]
    rw [h, latStateGen_add_smul, map_add, map_smul, map_smul]
    change (1 : ℂ) • lorentzianNearVOA.Y _ (-1) _ + Complex.I • lorentzianNearVOA.Y _ (-1) _ = _
    rw [lorentzianFrameCurrent_zeroMode, lorentzianFrameCurrent_zeroMode,
      lorentzianFrame_coordinate_zero, lorentzianFrame_coordinate_one, smul_smul, smul_smul,
      ← add_smul]
    congr 1
    linear_combination ((β 0 : ℂ) - (β 1 : ℂ) / 2) * Complex.I_mul_I

theorem lorentzianZero_eq_vector : (![0, 0] : lorentzianLattice.carrier) = 0 := by
  funext a
  fin_cases a <;> rfl

/-- On matter states of momentum `β`, the zero product with the `a`-th zero-momentum basis state
is multiplication by `β a`. -/
theorem moonshineMatter_zeroBasis_zeroMode (a : Fin 2) (β : lorentzianLattice.carrier)
    {v : moonshineMatterSpace} (hv : v ∈ moonshineMatterMomentum β) :
    moonshineMatterNearVOA.Y (moonshineMatterSectorMap ![0, 0] (vnatZeroBasisVector a)) (-1) v =
      ((β a : ℤ) : ℂ) • v := by
  rw [vnatZeroBasisVector, moonshineMatterSectorMap_tmul, lorentzianZero_eq_vector]
  refine TensorVA.tenSub_induction (P := ⊤) (Q := latticeMomentumGrading lorentzianLattice β)
    (motive := fun v => moonshineMatterNearVOA.Y (VnatVOA.vacuum ⊗ₜ latStateGen lorentzianLattice
      (hypLorentzianPolynomialEquiv (X (0, a))) 0) (-1) v = ((β a : ℤ) : ℂ) • v)
    ?_ ?_ ?_ ?_ hv
  · simp
  · intro x y hx hy
    rw [map_add, hx, hy, smul_add]
  · intro c x hx
    rw [map_smul, hx, smul_comm]
  · intro x _ y hy
    rw [latticeMomentumGrading_eq_range] at hy
    obtain ⟨p, rfl⟩ := hy
    rw [moonshineMatterNearVOA_tmul_field, finsum_eq_single _ 0]
    · rw [VnatVOA.vacuum_Y, FormalDist.one_apply, if_pos rfl, Module.End.one_apply,
        show (-1 : ℤ) - 0 = -1 by norm_num, mkEα_apply]
      change x ⊗ₜ[ℂ] lorentzianNearVOA.Y _ (-1) (latStateGen lorentzianLattice p β) = _
      rw [lorentzianHyperbolicCurrent_zeroMode, TensorProduct.tmul_smul]
      rfl
    · intro m hm
      rw [VnatVOA.vacuum_Y, FormalDist.one_apply, if_neg hm, LinearMap.zero_apply,
        TensorProduct.zero_tmul]


/-- A zero-momentum physical state with coordinates `c` acts on momentum `β` by
`c₀ β₀ + c₁ β₁`, before passing to the Lie quotient. -/
theorem moonshineMatter_zeroWeight_zeroProduct (c : Fin 2 → ℂ) (β : lorentzianLattice.carrier)
    {v : moonshineMatterSpace} (hv : v ∈ moonshineMatterMomentum β) :
    moonshineMatterNearVOA.Y (moonshineMatterSectorMap ![0, 0]
        (c 0 • vnatZeroBasisVector 0 + c 1 • vnatZeroBasisVector 1)) (-1) v =
      (c 0 * (β 0 : ℂ) + c 1 * (β 1 : ℂ)) • v := by
  rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul]
  change c 0 • moonshineMatterNearVOA.Y _ (-1) v + c 1 • moonshineMatterNearVOA.Y _ (-1) v = _
  rw [moonshineMatter_zeroBasis_zeroMode 0 β hv, moonshineMatter_zeroBasis_zeroMode 1 β hv,
    smul_smul, smul_smul, ← add_smul]

/-- The bracket of a zero-momentum physical class with a momentum-`β` class. -/
theorem monsterLie_zeroSector_bracket
    (u : (vnatStringModule 0 0 0).weightSlice (vnatStringModule 0 0 0).physical 1)
    (β : lorentzianLattice.carrier) (w : moonshineMatterNearVOA.primaryWeightOne)
    (hw : (w : moonshineMatterSpace) ∈ moonshineMatterMomentum β) :
    ⁅monsterLieProjection (moonshineMatterPhysicalSectorMap 0 0 0 u), monsterLieProjection w⁆ =
      (vnatZeroWeightCoordinates u.val 0 * (β 0 : ℂ) +
        vnatZeroWeightCoordinates u.val 1 * (β 1 : ℂ)) • monsterLieProjection w := by
  have hu : (u.val.val : Vnat ⊗[ℂ] hypFock) =
      vnatZeroWeightCoordinates u.val 0 • vnatZeroBasisVector 0 +
        vnatZeroWeightCoordinates u.val 1 • vnatZeroBasisVector 1 := by
    have h1 : vnatZeroWeightEquiv (vnatZeroWeightCoordinates u.val) = u.val :=
      vnatZeroWeightEquiv.apply_symm_apply u.val
    exact (congrArg Subtype.val h1).symm
  have hz : moonshineMatterNearVOA.primaryZeroProduct
      (moonshineMatterPhysicalSectorMap 0 0 0 u) w =
        (vnatZeroWeightCoordinates u.val 0 * (β 0 : ℂ) +
          vnatZeroWeightCoordinates u.val 1 * (β 1 : ℂ)) • w := by
    apply Subtype.ext
    change moonshineMatterNearVOA.Y (moonshineMatterSectorMap ![0, 0] u.val.val) (-1)
      (w : moonshineMatterSpace) = _
    rw [hu, moonshineMatter_zeroWeight_zeroProduct _ β hw]
    rfl
  rw [monsterLieProjection_bracket, hz, map_smul]

/-- The zero-momentum space acts on momentum `β` by `c₀ β₀ + c₁ β₁`, where `c` are the no-ghost
coordinates of the zero-momentum element. -/
theorem monsterLie_zeroMomentum_bracket (h : monsterLieMomentum 0)
    (β : lorentzianLattice.carrier) (x : monsterLieAlgebra) (hx : x ∈ monsterLieMomentum β) :
    ⁅(h : monsterLieAlgebra), x⁆ =
      (monsterLieZeroMomentumEquiv h 0 * (β 0 : ℂ) + monsterLieZeroMomentumEquiv h 1 * (β 1 : ℂ)) •
        x := by
  obtain ⟨p, rfl⟩ := monsterLieZeroQuotientEquiv.surjective h
  induction p using Submodule.Quotient.induction_on with | _ u =>
  obtain ⟨w, hw, rfl⟩ := hx
  have hcoord :
      monsterLieZeroMomentumEquiv (monsterLieZeroQuotientEquiv (Submodule.Quotient.mk u)) =
      vnatZeroWeightCoordinates u.val :=
    monsterLieZeroQuotientEquiv_coordinates (Submodule.Quotient.mk u)
  have hval : ((monsterLieZeroQuotientEquiv (Submodule.Quotient.mk u) : monsterLieMomentum 0) :
      monsterLieAlgebra) = monsterLieProjection (moonshineMatterPhysicalSectorMap 0 0 0 u) :=
    monsterLieZeroQuotientEquiv_coe (Submodule.Quotient.mk u)
  rw [hcoord, hval]
  exact monsterLie_zeroSector_bracket u β w hw

end VOA.Moonshine.ConwayNorton
