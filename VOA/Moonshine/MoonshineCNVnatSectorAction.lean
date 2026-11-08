import VOA.Moonshine.MoonshineCNVnatStringModule
import VOA.Moonshine.MoonshineCNVnatFormAction

/-! # The actual Aut(V♮) action on the graded string sector -/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open AutMonster TensorFieldLift SimpleNat
open scoped TensorProduct

def vnatSectorAction : AutVnat →* ((Vnat ⊗[ℂ] hypFock) ≃ₗ[ℂ] (Vnat ⊗[ℂ] hypFock)) where
  toFun g := g.toLinearEquiv.rTensor hypFock
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

theorem vnatSectorAction_tmul (g : AutVnat) (v : Vnat) (p : hypFock) :
    vnatSectorAction g (v ⊗ₜ[ℂ] p) = g v ⊗ₜ[ℂ] p := rfl

theorem vnatSectorAction_weight (g : AutVnat) (x y N : ℤ)
    (u : Vnat ⊗[ℂ] hypFock) (hu : u ∈ vnatSectorWeight x y N) :
    vnatSectorAction g u ∈ vnatSectorWeight x y N := by
  induction hu using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨i, j, v, p, hv, hp, hij, rfl⟩ := ht
    rw [vnatSectorAction_tmul, ← hij]
    exact vnatSectorWeight_tmul x y i j (g v) p (GriessAut.aut_map_mem_grading g hv) hp
  | zero => rw [LinearEquiv.map_zero]; exact Submodule.zero_mem _
  | add u v _ _ hu hv => rw [LinearEquiv.map_add]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu => rw [LinearEquiv.map_smul]; exact Submodule.smul_mem _ c hu

theorem vnatSectorAction_mode (g : AutVnat) (κ ell : ℂ) (n : ℤ)
    (u : Vnat ⊗[ℂ] hypFock) :
    vnatSectorAction g (vnatHypMode κ ell n u) = vnatHypMode κ ell n (vnatSectorAction g u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp only [LinearEquiv.map_zero, LinearMap.map_zero]
  | add u v hu hv => simp only [LinearEquiv.map_add, LinearMap.map_add, hu, hv]
  | tmul v p =>
    simp only [vnatHypMode, tensorTranslation, LinearMap.add_apply,
      LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, LinearEquiv.map_add, vnatSectorAction_tmul]
    congr 2
    exact VertexOperatorAlgebra.aut_comm_L g n v

theorem vnatSectorAction_longitudinal (g : AutVnat) (a : Fin 2) (κ ell : ℂ) (n : ℤ)
    (u : Vnat ⊗[ℂ] hypFock) :
    vnatSectorAction g (vnatHypLongitudinal a κ ell n u) =
      vnatHypLongitudinal a κ ell n (vnatSectorAction g u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp only [LinearEquiv.map_zero, LinearMap.map_zero]
  | add u v hu hv => simp only [LinearEquiv.map_add, LinearMap.map_add, hu, hv]
  | tmul v p => rfl

theorem vnatSectorAction_isometry (g : AutVnat) (u v : Vnat ⊗[ℂ] hypFock) :
    vnatHypForm (vnatSectorAction g u) (vnatSectorAction g v) = vnatHypForm u v := by
  induction u using TensorProduct.induction_on with
  | zero => simp only [LinearEquiv.map_zero, LinearMap.map_zero, LinearMap.zero_apply]
  | add u w hu hw => simp only [LinearEquiv.map_add, LinearMap.map_add, LinearMap.add_apply, hu, hw]
  | tmul u p =>
    induction v using TensorProduct.induction_on with
    | zero => simp only [LinearEquiv.map_zero, LinearMap.map_zero]
    | add v w hv hw => simp only [LinearEquiv.map_add, LinearMap.map_add, hv, hw]
    | tmul v q =>
      change hypForm p q * natForm (g u) (g v) = hypForm p q * natForm u v
      rw [vnatAut_preserves_natForm]

def vnatStringGroupAction (x y : ℤ) (a : Fin 2) :
    StringGroupAction (vnatStringModule x y a) AutVnat where
  action := vnatSectorAction
  preserves_wt := fun g N u hu => vnatSectorAction_weight g x y N u hu
  commutes_L := fun g n u => vnatSectorAction_mode g x y n u
  commutes_K := fun g n u => vnatSectorAction_longitudinal g a x y n u
  isometry := vnatSectorAction_isometry

def stringSectorAction (x y : ℤ) (h : x ≠ 0 ∨ y ≠ 0) :
    StringGroupAction (stringSector x y h) AutVnat :=
  vnatStringGroupAction x y (stringSectorFamily x y h)

end VOA.Moonshine.ConwayNorton
