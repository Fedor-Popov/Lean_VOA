import VOA.Moonshine.MoonshineCNFockAdjoint
import VOA.Moonshine.MoonshineCNRealization
import VOA.Moonshine.MoonshineCNTensorConformal

/-! The Lorentzian lattice bilinear form: nondegeneracy and Virasoro adjointness.

`NearInvariantForm` uses precisely the Virasoro-adjointness convention of
`VertexOperatorAlgebra.InvariantForm`. Full FHL invariance is a separate property.
-/

namespace VOA.Moonshine.ConwayNorton

open Module (End)
open IntegralLattice LatGen HeisenbergN Nondeg

/-- The existing invariant-form convention, extended to a near-VOA. -/
structure NearInvariantForm {M : Type*} [AddCommGroup M] [Module ℂ M] (V : NearVOA M) where
  form : LinearMap.BilinForm ℂ M
  virasoro_adj : ∀ (n : ℤ) (a b : M),
    form (nearVirasoroMode V n a) b = form a (nearVirasoroMode V (-n) b)

theorem frameLatticeForm_virasoro_state {L : IntegralLattice} (F : ComplexLatticeFrame L)
    (n : ℤ) (p q : FockN (rank L)) (α β : L.carrier) :
    latForm L (frameVirasoroMode F n (latStateGen L p α)) (latStateGen L q β) =
      latForm L (latStateGen L p α) (frameVirasoroMode F (-n) (latStateGen L q β)) := by
  classical
  rw [frameVirasoroMode_tmul, frameVirasoroMode_tmul]
  simp only [map_add, LinearMap.add_apply, apply_ite, map_zero, LinearMap.zero_apply,
    map_smul, LinearMap.smul_apply, smul_eq_mul, latForm_state, neg_eq_zero]
  by_cases hab : α + β = 0
  · have hb : β = -α := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hab
    subst β
    have hneg : frameOscillator F (-α) (-n) = -frameOscillator F α (-n) := by
      simp [frameOscillator, map_neg, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
    simp only [add_neg_cancel, if_true, hneg, LinearMap.neg_apply, map_neg,
      map_neg, neg_neg, uForm_virasoro_adjoint, uForm_frameOscillator_adjoint]
    split_ifs <;>
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply,
        latForm_state, add_neg_cancel, if_true, uForm_virasoro_adjoint,
        uForm_frameOscillator_adjoint, smul_eq_mul] <;> ring
  · simp only [hab, if_false, zero_mul, mul_zero]
    split_ifs <;>
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply,
        latForm_state, hab, if_false, zero_mul, smul_zero, add_zero] <;> ring

theorem frameLatticeForm_virasoro_adjoint {L : IntegralLattice} (F : ComplexLatticeFrame L)
    (n : ℤ) (x y : LatModuleGen L) :
    latForm L (frameVirasoroMode F n x) y = latForm L x (frameVirasoroMode F (-n) y) := by
  induction x using induction_latState L with
  | h0 => simp
  | hadd x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | hsmul c x hx => simp only [map_smul, LinearMap.smul_apply, hx]
  | hst p α =>
      induction y using induction_latState L with
      | h0 => simp
      | hadd y y' hy hy' => simp only [map_add, hy, hy']
      | hsmul c y hy => simp only [map_smul, hy]
      | hst q β => exact frameLatticeForm_virasoro_state F n p q α β

/-- The explicit Fock form paired across opposite lattice charges. -/
noncomputable def lorentzianBilinearForm : LinearMap.BilinForm ℂ LorentzianFockSpace :=
  latForm lorentzianLattice

theorem lorentzianBilinearForm_symmetric (x y : LorentzianFockSpace) :
    lorentzianBilinearForm x y = lorentzianBilinearForm y x := latForm_symm _ x y

theorem lorentzianBilinearForm_nondegenerate (x : LorentzianFockSpace) (hx : x ≠ 0) :
    ∃ y, lorentzianBilinearForm x y ≠ 0 := latForm_nondeg _ x hx

theorem lorentzianBilinearForm_normalized :
    lorentzianBilinearForm lorentzianNearVOA.vacuum lorentzianNearVOA.vacuum = 1 := by
  change latForm lorentzianLattice (latVacuumGen _) (latVacuumGen _) = 1
  rw [latVacuumGen, latForm_state, add_zero, if_pos rfl, chSign_zero,
    one_mul, vacuumN, uForm_one]
  simp

theorem lorentzianBilinearForm_virasoro_adjoint (n : ℤ) (x y : LorentzianFockSpace) :
    lorentzianBilinearForm (nearVirasoroMode lorentzianNearVOA n x) y =
      lorentzianBilinearForm x (nearVirasoroMode lorentzianNearVOA (-n) y) := by
  change latForm lorentzianLattice
    (mode (frameStateField lorentzianComplexFrame lorentzian_even
      (latticeConformalVector lorentzianLattice)) (n + 1) x) y =
    latForm lorentzianLattice x
    (mode (frameStateField lorentzianComplexFrame lorentzian_even
      (latticeConformalVector lorentzianLattice)) (-n + 1) y)
  rw [mode_frameStateField_omega_eq_frameVirasoroMode,
    mode_frameStateField_omega_eq_frameVirasoroMode]
  exact frameLatticeForm_virasoro_adjoint lorentzianComplexFrame n x y

noncomputable def lorentzianInvariantForm : NearInvariantForm lorentzianNearVOA where
  form := lorentzianBilinearForm
  virasoro_adj := lorentzianBilinearForm_virasoro_adjoint

end VOA.Moonshine.ConwayNorton
