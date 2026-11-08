import VOA.Moonshine.MoonshineCNPhysicalMaps
import VOA.Moonshine.MoonshineCNTensorMomentum

/-! The form-free Monster Lie algebra on the actual matter vertex algebra. -/

noncomputable section
namespace VOA.Moonshine.ConwayNorton

open AutMonster TensorFieldLift
open scoped TensorProduct

local instance monsterPhysicalAddCommGroup :
    AddCommGroup moonshineMatterNearVOA.primaryWeightOne := Submodule.addCommGroup _

/-- The actual physical-spurious quotient of `V♮ ⊗ V_{II_{1,1}}`. -/
abbrev monsterLieAlgebra := moonshineMatterNearVOA.primaryLieQuotient

instance monsterLieRing : LieRing monsterLieAlgebra := inferInstance
instance monsterLieAlgebraComplex : LieAlgebra ℂ monsterLieAlgebra := inferInstance

def monsterLieProjection : moonshineMatterNearVOA.primaryWeightOne →ₗ[ℂ] monsterLieAlgebra :=
  moonshineMatterNearVOA.primarySpurious.mkQ

theorem monsterLieProjection_ker :
    LinearMap.ker monsterLieProjection = moonshineMatterNearVOA.primarySpurious :=
  Submodule.ker_mkQ _

theorem monsterLieProjection_bracket (u v : moonshineMatterNearVOA.primaryWeightOne) :
    ⁅monsterLieProjection u, monsterLieProjection v⁆ =
      monsterLieProjection (moonshineMatterNearVOA.primaryZeroProduct u v) := rfl

/-- The momentum subspaces, as images of homogeneous physical representatives. -/
def monsterLieMomentum (α : lorentzianLattice.carrier) : Submodule ℂ monsterLieAlgebra :=
  ((moonshineMatterMomentum α).comap moonshineMatterNearVOA.primaryWeightOne.subtype).map
    monsterLieProjection

theorem monsterLieMomentum_bracket (α β : lorentzianLattice.carrier)
    (u v : monsterLieAlgebra) (hu : u ∈ monsterLieMomentum α)
    (hv : v ∈ monsterLieMomentum β) : ⁅u, v⁆ ∈ monsterLieMomentum (α + β) := by
  obtain ⟨a, ha, rfl⟩ := hu
  obtain ⟨b, hb, rfl⟩ := hv
  exact ⟨moonshineMatterNearVOA.primaryZeroProduct a b,
    moonshineMatterMomentum_mode α β a b ha hb 0, rfl⟩

/-- The existing automorphism action on the first tensor factor. -/
def moonshineMatterAut : AutVnat →* (moonshineMatterSpace ≃ₗ[ℂ] moonshineMatterSpace) where
  toFun g := g.toLinearEquiv.rTensor LorentzianFockSpace
  map_one' := by
    apply LinearEquiv.toLinearMap_injective
    apply TensorProduct.ext'
    intro v p
    rfl
  map_mul' g h := by
    apply LinearEquiv.toLinearMap_injective
    apply TensorProduct.ext'
    intro v p
    rfl

theorem moonshineMatterAut_field (g : AutVnat) (u v : moonshineMatterSpace) (s : ℤ) :
    moonshineMatterAut g (moonshineMatterNearVOA.Y u s v) =
      moonshineMatterNearVOA.Y (moonshineMatterAut g u) s (moonshineMatterAut g v) := by
  let C := nearTensorCoefficient VnatVOA.toNearVOA lorentzianNearVOA s
  change moonshineMatterAut g (C u v) = C (moonshineMatterAut g u) (moonshineMatterAut g v)
  induction u using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero, LinearMap.zero_apply]
  | add u w hu hw =>
    simp only [LinearMap.map_add, LinearEquiv.map_add, LinearMap.add_apply, hu, hw]
  | tmul a b =>
    induction v using TensorProduct.induction_on with
    | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero]
    | add v w hv hw => simp only [LinearMap.map_add, LinearEquiv.map_add, hv, hw]
    | tmul x y =>
      change moonshineMatterAut g (moonshineMatterNearVOA.Y (a ⊗ₜ b) s (x ⊗ₜ y)) =
        moonshineMatterNearVOA.Y (g a ⊗ₜ b) s (g x ⊗ₜ y)
      rw [moonshineMatterNearVOA_tmul_field, moonshineMatterNearVOA_tmul_field]
      have hf := (moonshineMatterAut g).toLinearMap.toAddMonoidHom.map_finsum_of_injective
        (moonshineMatterAut g).injective
        (fun m : ℤ => (VnatVOA.Y a m x) ⊗ₜ[ℂ] (lorentzianNearVOA.Y b (s - m) y))
      change moonshineMatterAut g (∑ᶠ m : ℤ, _) = _ at hf
      rw [hf]
      apply finsum_congr
      intro m
      change g (VnatVOA.Y a m x) ⊗ₜ _ = (VnatVOA.Y (g a) m (g x)) ⊗ₜ _
      congr 1
      have h := g.map_smul a (-m - 1) x
      simpa only [PreVertexAlgebra.smul_def, mode_apply,
        show -(-m - 1) - 1 = m by omega] using h

theorem moonshineMatterAut_virasoro (g : AutVnat) (n : ℤ) (u : moonshineMatterSpace) :
    moonshineMatterAut g (moonshineMatterNearVOA.L n u) =
      moonshineMatterNearVOA.L n (moonshineMatterAut g u) := by
  have he : moonshineMatterAut g moonshineMatterNearVOA.conformalVector =
      moonshineMatterNearVOA.conformalVector := by
    rw [moonshineMatterNearVOA_conformalVector, LinearEquiv.map_add]
    change g VnatVOA.conformalVector ⊗ₜ _ + g VnatVOA.vacuum ⊗ₜ _ = _
    rw [g.map_omega, g.map_vacuum]
    rfl
  change moonshineMatterAut g
    (moonshineMatterNearVOA.Y moonshineMatterNearVOA.conformalVector (-(n + 1) - 1) u) = _
  rw [moonshineMatterAut_field, he]
  rfl

theorem moonshineMatterAut_momentum (g : AutVnat) (α : lorentzianLattice.carrier)
    (u : moonshineMatterSpace) (hu : u ∈ moonshineMatterMomentum α) :
    moonshineMatterAut g u ∈ moonshineMatterMomentum α := by
  refine TensorVA.tenSub_induction (P := ⊤)
    (Q := latticeMomentumGrading lorentzianLattice α)
    (motive := fun u => moonshineMatterAut g u ∈ moonshineMatterMomentum α) ?_ ?_ ?_ ?_ hu
  · change moonshineMatterAut g 0 ∈ moonshineMatterMomentum α
    rw [LinearEquiv.map_zero]; exact Submodule.zero_mem _
  · intro x y hx hy
    rw [LinearEquiv.map_add]; exact Submodule.add_mem _ hx hy
  · intro c x hx
    rw [LinearEquiv.map_smul]; exact Submodule.smul_mem _ c hx
  · intro a _ b hb
    exact moonshineMatterMomentum_tmul α (g a) hb

instance monsterLieAutomorphismGroup : Group (monsterLieAlgebra ≃ₗ⁅ℂ⁆ monsterLieAlgebra) where
  mul f g := g.trans f
  one := LieEquiv.refl
  inv := LieEquiv.symm
  mul_assoc f g h := by ext x; rfl
  one_mul f := by ext x; rfl
  mul_one f := by ext x; rfl
  inv_mul_cancel f := by ext x; exact f.symm_apply_apply x

/-- Automorphisms of V♮ act on the Monster Lie algebra by `g ⊗ id`. -/
def monsterLieAut : AutVnat →* (monsterLieAlgebra ≃ₗ⁅ℂ⁆ monsterLieAlgebra) where
  toFun g := moonshineMatterNearVOA.primaryQuotientLieEquiv (moonshineMatterAut g)
    (moonshineMatterAut_virasoro g) (fun u v => by
      simpa only [NearVOA.smul_def, mode_apply, neg_zero, zero_sub]
        using moonshineMatterAut_field g u v (-1))
  map_one' := by
    ext x
    induction x using Submodule.Quotient.induction_on with
    | _ v =>
      change monsterLieProjection _ = monsterLieProjection v
      congr 1
      apply Subtype.ext
      exact LinearEquiv.congr_fun (moonshineMatterAut.map_one) (v : moonshineMatterSpace)
  map_mul' g h := by
    ext x
    induction x using Submodule.Quotient.induction_on with
    | _ v =>
      change monsterLieProjection _ = monsterLieProjection _
      congr 1
      apply Subtype.ext
      exact LinearEquiv.congr_fun (moonshineMatterAut.map_mul g h) (v : moonshineMatterSpace)

theorem monsterLieAut_mk (g : AutVnat) (v : moonshineMatterNearVOA.primaryWeightOne) :
    monsterLieAut g (monsterLieProjection v) =
      monsterLieProjection
        (moonshineMatterNearVOA.primaryLinearMap (moonshineMatterAut g).toLinearMap
          (moonshineMatterAut_virasoro g) v) := rfl

theorem monsterLieAut_momentum (g : AutVnat) (α : lorentzianLattice.carrier)
    (u : monsterLieAlgebra) (hu : u ∈ monsterLieMomentum α) :
    monsterLieAut g u ∈ monsterLieMomentum α := by
  obtain ⟨v, hv, rfl⟩ := hu
  exact ⟨_, moonshineMatterAut_momentum g α v hv, rfl⟩

end VOA.Moonshine.ConwayNorton
