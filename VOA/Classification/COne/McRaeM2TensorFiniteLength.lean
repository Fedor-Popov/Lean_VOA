import VOA.Classification.COne.McRaeM2SimpleRepresentatives
import VOA.Classification.COne.McRaeM2EnoughInjectives
import VOA.Classification.COne.McRaeM2RestrictedLength
import VOA.Modules.LogTensorPzSimpleHomFinite
import VOA.Classification.COne.McRaeO1FinitePhi

/-! # Finite length of the actual maximal compatible tensor-dual module

Actual logarithmic reconstruction bounds the simple Hom multiplicities.
Finite simple types make the genuine socle finite-length, and an injective
embedding of that essential socle bounds the whole canonical compatible
module. No finite-length or rationality assumption on that module is used.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.C2Rigid.LocalInjective
open VOA.Classification.COne VOA.LogTensor VOA.LogTensor.Pz VOA.LogTensor.LogFin
open VOA.VHat VOA.VHat.DLM3

universe u
variable {V M₁ M₂ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  {W : VertexOperatorAlgebra V}

/-- The actual maximal P(1)-compatible weak module has finite length when
the actual simple isomorphism classes are finite. -/
theorem finiteLength_maximal_of_finitePhi (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule) [Finite (Φ W)] :
    IsFiniteLength (modeAlg (maximalWeakModule N₁.toWeakModule N₂.toWeakModule))
      (maximalCarrier N₁.toWeakModule N₂.toWeakModule) := by
  let B := maximalWeakModule N₁.toWeakModule N₂.toWeakModule
  haveI : ∀ c : Φ W, FiniteDimensional ℂ
      (moduleHomSpace (canonicalIrrModule c).isMod.toWeakModule B) := fun c =>
    finiteDimensional_maximalHomSpace_from_simple hC2 N₁ N₂ h₁ h₂
      (canonicalIrrModule c).isMod.toWeakModule
      (simple_of_weak_irreducible _ (canonicalIrrModule c).irreducible)
  have hS := finiteLength_socle_of_canonical_hom hC2 B
  have hSr := Restriction.finiteLength_restricted_submodule B (socle B) hS
  obtain ⟨E,f,hf⟩ := finite_injective_embedding hC2
    (WeakModule.submodule B (ofR B (socle B))) hSr
  exact finiteLength_of_socle_embedding hC2 B E.act E.injective E.finiteLength f hf

/-- On McRae's semisimple-Zhu locus, the PBW bottom construction (theorem `VOA.pbw`)
discharges finiteness of the actual simple index. -/
theorem finiteLength_maximal_of_semisimpleZhu (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (A W))
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule) :
    IsFiniteLength (modeAlg (maximalWeakModule N₁.toWeakModule N₂.toWeakModule))
      (maximalCarrier N₁.toWeakModule N₂.toWeakModule) := by
  haveI := VOA.Huang.ZhuFiniteIrr.finite_Φ_of_C2Cofinite
    (voaPBWBottomProjection (parabolicRepOfAMod W (regularAMod W))) hC2 hss
  exact finiteLength_maximal_of_finitePhi hC2 N₁ N₂ h₁ h₂

/-- The actual maximal compatible module has finite length for every `C₂`-cofinite `W`:
no semisimple-Zhu hypothesis (finiteness of the simple index is
`VOA.Huang.ZhuFiniteIrr.finite_Φ_of_C2Cofinite_pbw`). -/
theorem finiteLength_maximal_of_c2 (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule) :
    IsFiniteLength (modeAlg (maximalWeakModule N₁.toWeakModule N₂.toWeakModule))
      (maximalCarrier N₁.toWeakModule N₂.toWeakModule) := by
  haveI := VOA.Huang.ZhuFiniteIrr.finite_Φ_of_C2Cofinite_pbw hC2
  exact finiteLength_maximal_of_finitePhi hC2 N₁ N₂ h₁ h₂

/-- The canonical maximal compatible module carries its actual
grading-restricted generalized-module structure, with the original weak action.
No semisimple-Zhu hypothesis. -/
def maximalLogModule (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule) :
    LogVModule W (maximalCarrier N₁.toWeakModule N₂.toWeakModule) :=
  logOfFiniteLength hC2 (maximalWeakModule N₁.toWeakModule N₂.toWeakModule)
    (finiteLength_maximal_of_c2 hC2 N₁ N₂ h₁ h₂)

end VOA.C2Rigid.LocalInjective
