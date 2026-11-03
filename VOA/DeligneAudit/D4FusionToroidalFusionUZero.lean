import VOA.DeligneAudit.D4FusionToroidalFusionDimension
import VOA.DeligneAudit.DeligneFusionD1SiteGCyclic
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-!
# The pure coadjoint tensor inside the evaluation module

This is the raw `u`-degree-zero source space: every site lies in its
coadjoint summand. Its rank is `n^N`, with a split inclusion into the
full tensor product.
-/

namespace VOA.DeligneAudit.Toroidal.FusionUZero

open VOA.DeligneAudit.D1TensorG

noncomputable section

variable (n N : ℕ)

abbrev CoTensor := Tensor (K := ℂ) (ι := Fin N) (W := D1SiteG.Co n)

def siteProject : D1SiteG.Space n →ₗ[ℂ] D1SiteG.Co n where
  toFun v := v.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def embedCo : CoTensor n N →ₗ[ℂ] D1TensorG.Space n N :=
  PiTensorProduct.map (fun _ : Fin N => D1SiteG.inCo)

def project : D1TensorG.Space n N →ₗ[ℂ] CoTensor n N :=
  PiTensorProduct.map (fun _ : Fin N => siteProject n)

theorem project_embedCo : (project n N).comp (embedCo n N) = LinearMap.id := by
  rw [embedCo, project, ← PiTensorProduct.map_comp]
  have he : (fun _ : Fin N => (siteProject n).comp D1SiteG.inCo) =
      (fun _ : Fin N => (LinearMap.id : D1SiteG.Co n →ₗ[ℂ] D1SiteG.Co n)) := by
    funext q
    ext v c
    rfl
  rw [he, PiTensorProduct.map_id]

theorem embedCo_injective : Function.Injective (embedCo n N) := by
  intro x y h
  have hp := congrArg (project n N) h
  simpa only [← LinearMap.comp_apply, project_embedCo, LinearMap.id_apply] using hp

def coTensorBasis : Module.Basis (Fin N → Fin n) ℂ (CoTensor n N) :=
  Basis.piTensorProduct (fun _ : Fin N => Pi.basisFun ℂ (Fin n))

theorem finrank_coTensor : Module.finrank ℂ (CoTensor n N) = n ^ N := by
  rw [Module.finrank_eq_card_basis (coTensorBasis n N), Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin]

theorem finrank_zero_source :
    Module.finrank ℂ (LinearMap.range (embedCo n N)) = n ^ N := by
  rw [LinearMap.finrank_range_of_inj (embedCo_injective n N), finrank_coTensor]

end

end VOA.DeligneAudit.Toroidal.FusionUZero

#print axioms VOA.DeligneAudit.Toroidal.FusionUZero.project_embedCo
#print axioms VOA.DeligneAudit.Toroidal.FusionUZero.finrank_zero_source
