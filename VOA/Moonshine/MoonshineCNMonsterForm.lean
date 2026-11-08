import VOA.Moonshine.MoonshineCNRootRadical
import VOA.Moonshine.MoonshineCNRootSpaceAction

/-! Descent of the symmetric matter form. The sign is chosen for the lattice
normalization on the Cartan space. Lie invariance is a separate FHL obligation. -/

noncomputable section
namespace VOA.Moonshine.ConwayNorton

open AutMonster Nondeg SimpleNat LatGen
open scoped TensorProduct

attribute [local instance] monsterPhysicalAddCommGroup

theorem moonshineMatterForm_spurious_primary (u : moonshineMatterSpace)
    (hu : u ∈ moonshineMatterNearVOA.spurious)
    (v : moonshineMatterNearVOA.primaryWeightOne) : moonshineMatterForm u v = 0 := by
  refine Submodule.iSup_induction
    (fun n : ℕ => LinearMap.range (moonshineMatterNearVOA.L (-(n + 1 : ℤ))))
    (motive := fun u => moonshineMatterForm u v = 0) hu ?_ ?_ ?_
  · intro n w hw
    obtain ⟨z, rfl⟩ := hw
    rw [show moonshineMatterForm (moonshineMatterNearVOA.L (-(n + 1 : ℤ)) z) v =
      moonshineMatterForm z (moonshineMatterNearVOA.L (-(-(n + 1 : ℤ))) v) from
        moonshineMatterForm_virasoro_adjoint _ _ _, neg_neg,
      v.property.2 (n + 1 : ℤ) (by omega), LinearMap.map_zero]
  · change moonshineMatterForm 0 v = 0
    simp only [LinearMap.map_zero, LinearMap.zero_apply]
  · intro u w hu hw
    rw [LinearMap.map_add, LinearMap.add_apply, hu, hw, add_zero]

theorem moonshineMatterForm_aut (g : AutVnat) (u v : moonshineMatterSpace) :
    moonshineMatterForm (moonshineMatterAut g u) (moonshineMatterAut g v) =
      moonshineMatterForm u v := by
  induction u using TensorProduct.induction_on with
  | zero => simp only [LinearEquiv.map_zero, LinearMap.map_zero, LinearMap.zero_apply]
  | add u w hu hw =>
    simp only [LinearEquiv.map_add, LinearMap.map_add, LinearMap.add_apply, hu, hw]
  | tmul a p =>
    induction v using TensorProduct.induction_on with
    | zero => simp only [LinearEquiv.map_zero, LinearMap.map_zero]
    | add v w hv hw => simp only [LinearEquiv.map_add, LinearMap.map_add, hv, hw]
    | tmul b q =>
      change lorentzianBilinearForm p q * natForm (g a) (g b) =
        lorentzianBilinearForm p q * natForm a b
      rw [vnatAut_preserves_natForm]

theorem moonshineMatterReversal_isometry (u v : moonshineMatterSpace) :
    moonshineMatterForm (moonshineMatterReversal u) (moonshineMatterReversal v) =
      moonshineMatterForm u v := by
  induction u using TensorProduct.induction_on with
  | zero => simp only [LinearEquiv.map_zero, LinearMap.map_zero, LinearMap.zero_apply]
  | add u w hu hw =>
    simp only [LinearEquiv.map_add, LinearMap.map_add, LinearMap.add_apply, hu, hw]
  | tmul a p =>
    induction v using TensorProduct.induction_on with
    | zero => simp only [LinearEquiv.map_zero, LinearMap.map_zero]
    | add v w hv hw => simp only [LinearEquiv.map_add, LinearMap.map_add, hv, hw]
    | tmul b q =>
      change latForm lorentzianLattice (thetaLat lorentzianLattice p)
        (thetaLat lorentzianLattice q) * natForm a b = latForm lorentzianLattice p q * natForm a b
      rw [latForm_thetaLat]

theorem moonshineMatterReversal_selfAdjoint (u v : moonshineMatterSpace) :
    moonshineMatterForm (moonshineMatterReversal u) v =
      moonshineMatterForm u (moonshineMatterReversal v) := by
  have h := moonshineMatterReversal_isometry u (moonshineMatterReversal v)
  rwa [moonshineMatterReversal_involutive v] at h

theorem moonshineMatterReversal_primary (u : moonshineMatterSpace)
    (hu : u ∈ moonshineMatterNearVOA.primaryWeightOne) :
    moonshineMatterReversal u ∈ moonshineMatterNearVOA.primaryWeightOne := by
  constructor
  · rw [← moonshineMatterReversal_virasoro, hu.1]
  · intro n hn
    rw [← moonshineMatterReversal_virasoro, hu.2 n hn, LinearEquiv.map_zero]

def monsterPhysicalBilinearForm : LinearMap.BilinForm ℂ moonshineMatterNearVOA.primaryWeightOne :=
  -(moonshineMatterForm.restrict moonshineMatterNearVOA.primaryWeightOne)

theorem monsterPhysicalBilinearForm_left_null :
    moonshineMatterNearVOA.primarySpurious ≤ LinearMap.ker monsterPhysicalBilinearForm := by
  intro u hu
  apply LinearMap.ext
  intro v
  change -moonshineMatterForm u v = 0
  rw [moonshineMatterForm_spurious_primary u hu v, neg_zero]

theorem monsterPhysicalBilinearForm_right_null :
    moonshineMatterNearVOA.primarySpurious ≤ LinearMap.ker monsterPhysicalBilinearForm.flip := by
  intro u hu
  apply LinearMap.ext
  intro v
  change -moonshineMatterForm v u = 0
  rw [moonshineMatterForm_symmetric, moonshineMatterForm_spurious_primary u hu v, neg_zero]

/-- The descended bilinear form; invariance under the Lie bracket is not asserted here. -/
def monsterLieBilinearForm : LinearMap.BilinForm ℂ monsterLieAlgebra :=
  monsterPhysicalBilinearForm.liftQ₂ moonshineMatterNearVOA.primarySpurious
    moonshineMatterNearVOA.primarySpurious
    monsterPhysicalBilinearForm_left_null monsterPhysicalBilinearForm_right_null

theorem monsterLieBilinearForm_mk (u v : moonshineMatterNearVOA.primaryWeightOne) :
    monsterLieBilinearForm (monsterLieProjection u) (monsterLieProjection v) =
      -moonshineMatterForm u v := rfl

theorem monsterLieBilinearForm_symmetric (u v : monsterLieAlgebra) :
    monsterLieBilinearForm u v = monsterLieBilinearForm v u := by
  induction u using Submodule.Quotient.induction_on with | _ u =>
  induction v using Submodule.Quotient.induction_on with | _ v =>
  exact congrArg Neg.neg (moonshineMatterForm_symmetric u v)

theorem monsterLieBilinearForm_aut (g : AutVnat) (u v : monsterLieAlgebra) :
    monsterLieBilinearForm (monsterLieAut g u) (monsterLieAut g v) =
      monsterLieBilinearForm u v := by
  induction u using Submodule.Quotient.induction_on with | _ u =>
  induction v using Submodule.Quotient.induction_on with | _ v =>
  exact congrArg Neg.neg (moonshineMatterForm_aut g u v)

end VOA.Moonshine.ConwayNorton
