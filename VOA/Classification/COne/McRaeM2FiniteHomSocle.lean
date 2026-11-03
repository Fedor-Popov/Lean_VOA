import VOA.Classification.COne.McRaeM2EssentialSocle
import VOA.Modules.LogTensorPzHomFinite

/-! # Finite simple types and finite Hom spaces bound the actual socle

For each simple representative, a finite basis of its actual weak-module Hom
space has finitely generated ranges. These finitely many ranges contain every
simple submodule, and so generate the genuine socle. No finite-length premise
on the ambient module is used.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.C2Rigid.LocalInjective
open VOA.Classification.COne VOA.Classification.COne.McRaeM1
open VOA.Classification.COne.PlusSplitting
open VOA.Classification.COne.PlusFiniteLength VOA.LogTensor VOA.LogTensor.Pz

universe u v
variable {V M X : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup X] [Module ℂ X]
  {W : VertexOperatorAlgebra V}

/-- A map out of a finitely generated weak module has finitely generated image
over the target's actual mode algebra. -/
theorem modeMap_fg_of_finGen {A : WeakModule W X} {B : WeakModule W M}
    (f : A.Hom B) (hA : FinGen A) : (modeMap f ⊤).FG := by
  obtain ⟨T,hT,hgen⟩ := hA
  let P : Submodule (modeAlg B) M := Submodule.span (modeAlg B) (f.toLinearMap '' T)
  let Q : Submodule ℂ X := (P.restrictScalars ℂ).comap f.toLinearMap
  have hQ : Q = ⊤ := hgen Q
    (fun x hx => Submodule.subset_span ⟨x,hx,rfl⟩) (by
      intro a n x hx
      change f.toLinearMap (A.act a n x) ∈ P
      rw [f.map_act]
      exact (ofR B P).act_mem a n hx)
  have he : P = modeMap f ⊤ := by
    apply le_antisymm
    · exact Submodule.span_le.mpr (by
        rintro _ ⟨x,-,rfl⟩
        exact ⟨x,Submodule.mem_top,rfl⟩)
    · rintro _ ⟨x,-,rfl⟩
      have hx : x ∈ Q := hQ ▸ Submodule.mem_top
      exact hx
  rw [← he]
  exact Submodule.fg_def.mpr ⟨_,hT.image _,rfl⟩

section OneType
variable (A : WeakModule W X) (B : WeakModule W M)
variable [FiniteDimensional ℂ (moduleHomSpace A B)]

/-- The sum of the ranges of a finite basis of the genuine Hom space. -/
def basisImageSum : Submodule (modeAlg B) M :=
  ⨆ j : Fin (Module.finrank ℂ (moduleHomSpace A B)),
    modeMap (homOfSpace (Module.finBasis ℂ (moduleHomSpace A B) j)) ⊤

theorem basisImageSum_fg (hA : FinGen A) : (basisImageSum A B).FG := by
  exact Submodule.fg_iSup _ (fun j => modeMap_fg_of_finGen
    (homOfSpace (Module.finBasis ℂ (moduleHomSpace A B) j)) hA)

/-- Every actual module-map range is contained in that finite basis sum. -/
theorem modeMap_le_basisImageSum (f : moduleHomSpace A B) :
    modeMap (homOfSpace f) ⊤ ≤ basisImageSum A B := by
  classical
  rintro _ ⟨x,-,rfl⟩
  let b := Module.finBasis ℂ (moduleHomSpace A B)
  have he : (∑ j, (b.repr f j) • (b j : X →ₗ[ℂ] M)) = f.1 :=
    by
      have h := congrArg (moduleHomSpace A B).subtype (b.sum_repr f)
      simpa only [map_sum,map_smul] using h
  have hv : (∑ j, (b.repr f j) • ((b j : X →ₗ[ℂ] M) x)) = f.1 x := by
    have h := DFunLike.congr_fun he x
    simpa only [LinearMap.sum_apply,LinearMap.smul_apply] using h
  change f.1 x ∈ basisImageSum A B
  rw [← hv]
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_of_tower_mem
  exact (le_iSup (fun j => modeMap (homOfSpace (b j)) ⊤) j)
    (show (b j : X →ₗ[ℂ] M) x ∈ modeMap (homOfSpace (b j)) ⊤ from
      ⟨x,Submodule.mem_top,rfl⟩)

end OneType

section Family
variable {ι : Type v} [Finite ι] (X : ι → Type u)
  [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
variable (As : ∀ i, WeakModule W (X i)) (B : WeakModule W M)
variable [∀ i, FiniteDimensional ℂ (moduleHomSpace (As i) B)]

/-- Finite Hom multiplicities for a finite exhaustive family of simple types
make the actual socle finitely generated. The exhaustiveness premise is a
map onto each genuine simple submodule, with its actual image specified. -/
theorem finiteLength_socle_of_finite_hom (hC2 : C2Cofinite W)
    (hfg : ∀ i, FinGen (As i))
    (hcover : ∀ A : Submodule (modeAlg B) M, IsAtom A →
      ∃ i, ∃ f : moduleHomSpace (As i) B, modeMap (homOfSpace f) ⊤ = A) :
    IsFiniteLength (modeAlg B) (socle B) := by
  let P : Submodule (modeAlg B) M := ⨆ i, basisImageSum (As i) B
  have hP : P.FG := Submodule.fg_iSup _ (fun i => basisImageSum_fg (As i) B (hfg i))
  have hs : socle B ≤ P := by
    apply sSup_le
    intro A hA
    obtain ⟨i,f,hf⟩ := hcover A hA
    rw [← hf]
    exact le_trans (modeMap_le_basisImageSum (As i) B f)
      (le_iSup (fun j => basisImageSum (As j) B) i)
  have hfl : IsFiniteLength (modeAlg B) P := finiteLength_fg_of_c2Cofinite hC2 B P hP
  exact hfl.of_injective (f := Submodule.inclusion hs) (Submodule.inclusion_injective hs)

end Family
end VOA.C2Rigid.LocalInjective
