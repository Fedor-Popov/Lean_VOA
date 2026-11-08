import VOA.Moonshine.MoonshineCNVnatZeroWeight
import VOA.Moonshine.MoonshineCNVnatLongitudinalQuotient

/-! # The zero-momentum physical quotient is the hyperbolic plane -/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open AutMonster SimpleNat MvPolynomial
open scoped TensorProduct

attribute [local instance] vnatStringWeightAddCommGroup vnatStringSliceAddCommGroup

def vnatZeroWeightMap : (Fin 2 → ℂ) →ₗ[ℂ] vnatSectorWeight 0 0 1 where
  toFun c := ⟨c 0 • vnatZeroBasisVector 0 + c 1 • vnatZeroBasisVector 1,
    Submodule.add_mem _ (Submodule.smul_mem _ _ (vnatZeroBasisVector_mem 0))
      (Submodule.smul_mem _ _ (vnatZeroBasisVector_mem 1))⟩
  map_add' c d := by
    apply Subtype.ext
    change (c 0 + d 0) • vnatZeroBasisVector 0 + (c 1 + d 1) • vnatZeroBasisVector 1 =
      (c 0 • vnatZeroBasisVector 0 + c 1 • vnatZeroBasisVector 1) +
        (d 0 • vnatZeroBasisVector 0 + d 1 • vnatZeroBasisVector 1)
    module
  map_smul' c d := by
    apply Subtype.ext
    change (c * d 0) • vnatZeroBasisVector 0 + (c * d 1) • vnatZeroBasisVector 1 =
      c • (d 0 • vnatZeroBasisVector 0 + d 1 • vnatZeroBasisVector 1)
    module

def vnatZeroWeightCoordinates (u : vnatSectorWeight 0 0 1) : Fin 2 → ℂ :=
  fun a => natForm VnatVOA.vacuum (hypTensorCoordinates u.val (Finsupp.single (0, a) 1))

theorem vnatZeroWeightMap_coordinates (c : Fin 2 → ℂ) :
    vnatZeroWeightCoordinates (vnatZeroWeightMap c) = c := by
  funext a
  change natForm VnatVOA.vacuum
    (hypTensorCoordinates (c 0 • vnatZeroBasisVector 0 + c 1 • vnatZeroBasisVector 1)
      (Finsupp.single (0, a) 1)) = c a
  have hn : natForm VnatVOA.vacuum VnatVOA.vacuum = 1 :=
    natInvForm_normalized vnat_twistedLocality
  simp only [LinearEquiv.map_add, LinearEquiv.map_smul, Finsupp.add_apply,
    Finsupp.smul_apply, vnatZeroBasisVector, X, hypTensorCoordinates_monomial]
  simp only [Finsupp.single_apply, Finsupp.single_left_inj (by decide : (1 : ℕ) ≠ 0),
    Prod.mk.injEq, true_and, Fin.ext_iff]
  fin_cases a <;>
    norm_num only [Fin.val_zero, Fin.val_one, Fin.val_mk, if_true, if_false,
      smul_zero, zero_add, add_zero, LinearMap.map_smul, smul_eq_mul, hn, mul_one]
  all_goals exact congrArg c (Fin.ext rfl)

theorem vnatZeroWeightMap_single (a : Fin 2) :
    (vnatZeroWeightMap (Pi.single a 1)).val = vnatZeroBasisVector a := by
  fin_cases a <;> simp [vnatZeroWeightMap]

theorem vnatZeroWeightMap_surjective : Function.Surjective vnatZeroWeightMap := by
  have hr : vnatSectorWeight 0 0 1 ≤
      LinearMap.range ((vnatSectorWeight 0 0 1).subtype.comp vnatZeroWeightMap) := by
    rw (occs := .pos [1]) [vnatZeroWeight_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact ⟨Pi.single a 1, vnatZeroWeightMap_single a⟩
  intro u
  obtain ⟨c, hc⟩ := hr u.property
  exact ⟨c, Subtype.ext hc⟩

def vnatZeroWeightEquiv : (Fin 2 → ℂ) ≃ₗ[ℂ] vnatSectorWeight 0 0 1 where
  toLinearMap := vnatZeroWeightMap
  invFun := vnatZeroWeightCoordinates
  left_inv := vnatZeroWeightMap_coordinates
  right_inv u := by
    obtain ⟨c, rfl⟩ := vnatZeroWeightMap_surjective u
    rw [vnatZeroWeightMap_coordinates]
    rfl

theorem vnatZeroBasisVector_form (a b : Fin 2) :
    vnatHypForm (vnatZeroBasisVector a) (vnatZeroBasisVector b) =
      if a = b.rev then 1 else 0 := by
  change hypForm (X (0, a)) (X (0, b)) * natForm VnatVOA.vacuum VnatVOA.vacuum = _
  rw [show natForm VnatVOA.vacuum VnatVOA.vacuum = 1 from
    natInvForm_normalized vnat_twistedLocality, mul_one]
  rw [show (X (0, a) : hypFock) = X (0, a) * 1 by simp, hypForm_creation_adjoint]
  fin_cases a <;> fin_cases b <;> simp [hypForm_one]

theorem vnatZeroWeightEquiv_isometry (c d : Fin 2 → ℂ) :
    vnatHypForm (vnatZeroWeightEquiv c) (vnatZeroWeightEquiv d) = c 0 * d 1 + c 1 * d 0 := by
  change vnatHypForm (c 0 • vnatZeroBasisVector 0 + c 1 • vnatZeroBasisVector 1)
    (d 0 • vnatZeroBasisVector 0 + d 1 • vnatZeroBasisVector 1) = _
  simp only [LinearMap.map_add, LinearMap.add_apply, LinearMap.map_smul,
    LinearMap.smul_apply, smul_eq_mul]
  rw [vnatZeroBasisVector_form 0 0, vnatZeroBasisVector_form 1 0,
    vnatZeroBasisVector_form 0 1, vnatZeroBasisVector_form 1 1]
  norm_num [Fin.rev, Fin.last]
  ring

def vnatZeroPhysicalEquiv :
    (vnatStringModule 0 0 0).weightSlice (vnatStringModule 0 0 0).physical 1 ≃ₗ[ℂ]
      vnatSectorWeight 0 0 1 where
  toFun u := u.val
  invFun u := ⟨u, vnatZeroWeight_physical u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem vnatZeroPhysicalRadical :
    (vnatStringModule 0 0 0).weightRadical (vnatStringModule 0 0 0).physical 1 = ⊥ := by
  apply bot_unique
  intro u hu
  apply Subtype.ext
  apply Subtype.ext
  apply vnatSectorWeight_nondegenerate 0 0 1 u.val u.val.property
  intro v hv
  exact ((vnatStringModule 0 0 0).mem_weightRadical_iff _ _ u).mp hu
    ⟨⟨v, hv⟩, vnatZeroWeight_physical hv⟩

/-- Zero momentum: the actual physical radical quotient is ℂ². -/
def vnatZeroNoGhostEquiv :
    (vnatStringModule 0 0 0).weightRadicalQuotient (vnatStringModule 0 0 0).physical 1 ≃ₗ[ℂ]
      (Fin 2 → ℂ) :=
  ((vnatStringModule 0 0 0).weightRadical _ 1).quotEquivOfEqBot vnatZeroPhysicalRadical |>.trans
    (vnatZeroPhysicalEquiv.trans vnatZeroWeightEquiv.symm)

theorem vnatZeroNoGhostEquiv_mk
    (u : (vnatStringModule 0 0 0).weightSlice (vnatStringModule 0 0 0).physical 1) :
    vnatZeroNoGhostEquiv (Submodule.Quotient.mk u) = vnatZeroWeightCoordinates u.val := rfl

theorem vnatZeroNoGhostEquiv_isometry
    (u v : (vnatStringModule 0 0 0).weightRadicalQuotient (vnatStringModule 0 0 0).physical 1) :
    (vnatStringModule 0 0 0).radicalQuotientForm (vnatStringModule 0 0 0).physical 1 u v =
      vnatZeroNoGhostEquiv u 0 * vnatZeroNoGhostEquiv v 1 +
        vnatZeroNoGhostEquiv u 1 * vnatZeroNoGhostEquiv v 0 := by
  induction u using Submodule.Quotient.induction_on with | _ u =>
  induction v using Submodule.Quotient.induction_on with | _ v =>
  have h := vnatZeroWeightEquiv_isometry (vnatZeroWeightEquiv.symm u.val)
    (vnatZeroWeightEquiv.symm v.val)
  simpa only [LinearEquiv.apply_symm_apply] using h

theorem vnatZeroSectorAction_trivial (g : AutVnat) (u : vnatSectorWeight 0 0 1) :
    vnatSectorAction g u.val = u.val := by
  obtain ⟨c, rfl⟩ := vnatZeroWeightEquiv.surjective u
  change vnatSectorAction g (c 0 • vnatZeroBasisVector 0 + c 1 • vnatZeroBasisVector 1) = _
  have hb (a : Fin 2) : vnatSectorAction g (vnatZeroBasisVector a) = vnatZeroBasisVector a := by
    change g VnatVOA.vacuum ⊗ₜ[ℂ] X (0, a) = VnatVOA.vacuum ⊗ₜ[ℂ] X (0, a)
    rw [show g VnatVOA.vacuum = VnatVOA.vacuum from g.map_vacuum]
  rw [LinearEquiv.map_add, LinearEquiv.map_smul, LinearEquiv.map_smul, hb, hb]
  rfl

theorem vnatZeroNoGhostEquiv_equivariant (g : AutVnat)
    (u : (vnatStringModule 0 0 0).weightRadicalQuotient (vnatStringModule 0 0 0).physical 1) :
    vnatZeroNoGhostEquiv
      ((vnatStringGroupAction 0 0 0).stableWeightQuotientAction _
        (vnatStringGroupAction 0 0 0).action_preserves_physical 1 g u) =
      vnatZeroNoGhostEquiv u := by
  induction u using Submodule.Quotient.induction_on with | _ u =>
  rw [StringGroupAction.stableWeightQuotientAction_mk]
  congr 2
  apply Subtype.ext
  apply Subtype.ext
  exact vnatZeroSectorAction_trivial g u.val

end VOA.Moonshine.ConwayNorton
