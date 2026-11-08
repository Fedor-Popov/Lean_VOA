import VOA.Foundations.PBWTheorem.LieRep
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Data.Complex.Basic

/-! Every complex Lie algebra embeds in its universal enveloping algebra.

The proof evaluates the repository's relative PBW representation, induced from the zero
subalgebra, on the bottom vector: a basis vector `y a` is sent to the monomial `{a}`. -/

noncomputable section
namespace VOA.Moonshine.ConwayNorton

open Module Finsupp

variable (L : Type*) [LieRing L] [LieAlgebra ℂ L]

/-- The canonical map of a Lie algebra into its universal enveloping algebra is injective. -/
theorem envelopingEmbedding_injective :
    Function.Injective (UniversalEnvelopingAlgebra.ι ℂ : L → UniversalEnvelopingAlgebra ℂ L) := by
  classical
  let B := Basis.ofVectorSpace ℂ L
  let A := Basis.ofVectorSpaceIndex ℂ L
  letI : LinearOrder A := WellOrderingRel.isWellOrder.linearOrder
  let bc : Basis A ℂ (⊤ : Submodule ℂ L) := B.map (Submodule.topEquiv).symm
  have hc : IsCompl (⊥ : LieSubalgebra ℂ L).toSubmodule (⊤ : Submodule ℂ L) := isCompl_bot_top
  let ρ := PBWTheorem.rep (⊥ : LieSubalgebra ℂ L) hc bc
    (0 : (⊥ : LieSubalgebra ℂ L) →ₗ⁅ℂ⁆ End ℂ ℂ)
  let Ψ : L →ₗ[ℂ] (Multiset A →₀ ℂ) :=
    (LinearMap.applyₗ (single (0 : Multiset A) (1 : ℂ))).comp ρ.toLinearMap
  have hΨ : Ψ = (Finsupp.lmapDomain ℂ ℂ (fun a : A => ({a} : Multiset A))).comp
      B.repr.toLinearMap := by
    apply B.ext
    intro a
    have hbc : ((bc a : (⊤ : Submodule ℂ L)) : L) = B a := by
      simp [bc, Basis.map_apply]
    change ρ (B a) (single 0 1) = _
    rw [← hbc, PBWTheorem.rep_apply,
      PBWTheorem.act_y_low (⊥ : LieSubalgebra ℂ L) hc bc 0 (m := 0) (by simp) (1 : ℂ)]
    simp only [LinearMap.comp_apply, Finsupp.lmapDomain_apply, LinearEquiv.coe_coe]
    rw [hbc, B.repr_self, Finsupp.mapDomain_single]
    rfl
  have hinj : Function.Injective Ψ := by
    rw [hΨ]
    exact (Finsupp.mapDomain_injective (fun a b h => Multiset.singleton_inj.mp h)).comp
      B.repr.injective
  intro x y hxy
  apply hinj
  have h := congrArg (fun a => UniversalEnvelopingAlgebra.lift ℂ ρ a (single 0 1)) hxy
  simpa only [UniversalEnvelopingAlgebra.lift_ι_apply] using h

end VOA.Moonshine.ConwayNorton
