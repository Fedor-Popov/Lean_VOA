/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2BoundaryVacuumCharacter
import VOA.Filtered.BoundaryArcLiMap
import VOA.Filtered.BoundaryArcConformalEquiv
import VOA.Filtered.BoundarySimpleArcPoisson
import VOA.Commutative.PoissonVertexEquiv

/-!
# Boundary classical freeness: character-to-geometry assembly

The current relations, actual arc Hilbert upper bound, current-word surjection,
and direct infinite conformal squeeze are proved. This assembly takes only the
independent equality between the actual simple-VOA character and the product.
The equality is an explicit input to these helpers and is proved and discharged
by the unconditional endpoints in `AffineSl2BoundaryMainTheorems`.
-/
namespace VOA.AffineSl2BoundaryClassicalFreeness
open VOA.BoundaryAuxiliary VOA.AffineSl2BoundarySingularFamily
open VOA.AffineSl2BoundaryCharacter
noncomputable section

/-- The canonical map from the actual presented boundary arc to the actual simple Li algebra. -/
def canonicalMap (m : ℕ) (hm : 1 ≤ m) :
    Source (R := ℂ) m →ₐ[ℂ] liAssociatedGraded (AffineSl2BoundaryCharacter.vacuum m) :=
  BoundaryArcConformalSqueeze.sourceMap
    (BoundaryArcLiMap.simpleVOA (uniformCandidate m hm))
    (BoundaryArcLiMap.gen (uniformCandidate m hm))
    (BoundaryArcLiMap.gen_mem (uniformCandidate m hm)) m
    (BoundaryArcLiMap.sourceIdeal_le_kernel (uniformCandidate m hm))

/-- The actual current-word spanning theorem supplies the global canonical surjection. -/
theorem canonicalMap_surjective (m : ℕ) (hm : 1 ≤ m) :
    Function.Surjective (canonicalMap m hm) :=
  BoundaryArcConformalSqueeze.sourceMap_surjective _ _ _ _ _
    (BoundaryArcLiMap.polynomialMap_surjective (uniformCandidate m hm))

/-- All geometric/combinatorial parts of the paper assembled for the actual
VOA; the input to this assembly helper is its full ordinary character formula. -/
theorem canonicalMap_bijective_of_character (m : ℕ) (hm : 1 ≤ m)
    (hcharacter : character m = product m) :
    Function.Bijective (canonicalMap m hm) := by
  refine ⟨?_, canonicalMap_surjective m hm⟩
  apply BoundaryArcConformalSqueeze.sourceMap_injective_of_hilbert_bound
    (BoundaryArcLiMap.simpleVOA (uniformCandidate m hm))
    (BoundaryArcLiMap.gen (uniformCandidate m hm))
    (BoundaryArcLiMap.gen_mem (uniformCandidate m hm)) m
    (BoundaryArcLiMap.sourceIdeal_le_kernel (uniformCandidate m hm))
    (BoundaryArcLiMap.polynomialMap_surjective (uniformCandidate m hm))
  exact sourcePiece_finrank_le_vacuum_of_character m hm hcharacter

/-- Algebra-equivalence assembly, visibly conditional on the independent character gate. -/
def arcAlgEquivOfCharacter (m : ℕ) (hm : 1 ≤ m)
    (hcharacter : character m = product m) :
    Source (R := ℂ) m ≃ₐ[ℂ] liAssociatedGraded (AffineSl2BoundaryCharacter.vacuum m) :=
  AlgEquiv.ofBijective (canonicalMap m hm) (canonicalMap_bijective_of_character m hm hcharacter)

/-- The intrinsic canonical arc PVA map is injective under precisely the same
character input as the direct conformal squeeze. -/
theorem arcLiPoissonHom_injective_of_character (m : ℕ) (hm : 1 ≤ m)
    (hcharacter : character m = product m) :
    Function.Injective (uniformCandidate m hm).arcLiPoissonHom.toAlgHom := by
  let C := uniformCandidate m hm
  apply (injective_iff_map_eq_zero C.arcLiPoissonHom.toAlgHom.toAddMonoidHom).mpr
  intro x hx
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  change C.arcLiPoissonHom.toAlgHom (InfiniteJet.presentedJetMk (baseIdeal (R := ℂ) m) f) = 0 at hx
  rw [Candidate.arcLiPoissonHom_mk] at hx
  have heval : canonicalMap m hm (Ideal.Quotient.mk (sourceIdeal (R := ℂ) m) f) = 0 := hx
  have hs : Ideal.Quotient.mk (sourceIdeal (R := ℂ) m) f = 0 :=
    (canonicalMap_bijective_of_character m hm hcharacter).injective
      (heval.trans (map_zero (canonicalMap m hm)).symm)
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hs
  rwa [sourceIdeal_eq_jetIdeal] at hmem

/-- Full PVA equivalence assembly: every operation, including those of the
inverse, is preserved. The character premise is discharged in the main theorem module. -/
def arcPoissonEquivOfCharacter (m : ℕ) (hm : 1 ≤ m)
    (hcharacter : character m = product m) :
    PoissonVertexAlgebra.Equiv (arcPVA m) (liPoissonVertexAlgebra (AffineSl2BoundaryCharacter.vacuum m)) :=
  PoissonVertexAlgebra.Equiv.ofBijective (uniformCandidate m hm).arcLiPoissonHom
    ⟨arcLiPoissonHom_injective_of_character m hm hcharacter,
      (uniformCandidate m hm).arcLiPoissonHom_surjective⟩

/-- Exact presentation of the actual C2 algebra, with no independent
maximal-ideal generation or presentation-equality premise. -/
def baseC2AlgEquivOfCharacter (m : ℕ) (hm : 1 ≤ m)
    (hcharacter : character m = product m) :
    (BasePoly ℂ ⧸ baseIdeal (R := ℂ) m) ≃ₐ[ℂ]
      A₂ (AffineSl2BoundaryCharacter.vacuum m) :=
  (uniformCandidate m hm).baseC2AlgEquiv
    (arcLiPoissonHom_injective_of_character m hm hcharacter)

/-- The source of the PVA equivalence is the intrinsic arc algebra of the actual C2 algebra: this
bijection is natural in the coefficient algebra (`actualC2ArcEquivOfCharacter_natural`), so the
presented jet algebra represents the arc functor of `A₂`. -/
def actualC2ArcEquivOfCharacter {A : Type*} [CommRing A] [Algebra ℂ A]
    (m : ℕ) (hm : 1 ≤ m) (hcharacter : character m = product m) :
    (InfiniteJet.PresentedJet (baseIdeal (R := ℂ) m) →ₐ[ℂ] A) ≃
      (A₂ (AffineSl2BoundaryCharacter.vacuum m) →ₐ[ℂ] PowerSeries A) :=
  (uniformCandidate m hm).actualC2ArcEquiv
    (arcLiPoissonHom_injective_of_character m hm hcharacter)

/-- Naturality of `actualC2ArcEquivOfCharacter` in the coefficient algebra. -/
theorem actualC2ArcEquivOfCharacter_natural {A B : Type*} [CommRing A] [Algebra ℂ A]
    [CommRing B] [Algebra ℂ B] (m : ℕ) (hm : 1 ≤ m) (hcharacter : character m = product m)
    (f : InfiniteJet.PresentedJet (baseIdeal (R := ℂ) m) →ₐ[ℂ] A) (g : A →ₐ[ℂ] B) :
    actualC2ArcEquivOfCharacter m hm hcharacter (g.comp f) =
      (PowerSeries.mapAlgHom g).comp (actualC2ArcEquivOfCharacter m hm hcharacter f) :=
  AffineSl2BoundarySingularFamily.Candidate.actualC2ArcEquiv_natural _ _ f g

/-- The equivalence and its inverse preserve the actual conformal grading. -/
theorem canonicalMap_conformal_iff (m : ℕ) (hm : 1 ≤ m)
    (hcharacter : character m = product m) (N : ℕ) (x : Source (R := ℂ) m) :
    canonicalMap m hm x ∈ BoundaryArcConformalSqueeze.liConformalPiece
        (AffineSl2BoundaryCharacter.vacuum m) N ↔
      x ∈ sourcePiece (K := ℂ) m N :=
  BoundaryArcConformalSqueeze.sourceMap_mem_liConformalPiece_iff
    (BoundaryArcLiMap.simpleVOA (uniformCandidate m hm))
    (BoundaryArcLiMap.gen (uniformCandidate m hm))
    (BoundaryArcLiMap.gen_mem (uniformCandidate m hm)) m
    (BoundaryArcLiMap.sourceIdeal_le_kernel (uniformCandidate m hm))
    (BoundaryArcLiMap.polynomialMap_surjective (uniformCandidate m hm))
    (canonicalMap_bijective_of_character m hm hcharacter).injective N x

/-- Intrinsic conformal grading on the presented arc PVA. -/
def arcConformalPiece (m N : ℕ) :
    Submodule ℂ (InfiniteJet.PresentedJet (baseIdeal (R := ℂ) m)) :=
  (MvPolynomial.weightedHomogeneousSubmodule ℂ conformalWeight N).map
    (InfiniteJet.presentedJetMk (baseIdeal (R := ℂ) m)).toLinearMap

/-- The full intrinsic PVA equivalence is conformally graded in both directions. -/
theorem arcPoissonEquivOfCharacter_conformal_iff (m : ℕ) (hm : 1 ≤ m)
    (hcharacter : character m = product m) (N : ℕ)
    (x : InfiniteJet.PresentedJet (baseIdeal (R := ℂ) m)) :
    (arcPoissonEquivOfCharacter m hm hcharacter).toAlgEquiv x ∈
      BoundaryArcConformalSqueeze.liConformalPiece (AffineSl2BoundaryCharacter.vacuum m) N ↔
      x ∈ arcConformalPiece m N := by
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective x
  have h := canonicalMap_conformal_iff m hm hcharacter N
    (Ideal.Quotient.mk (sourceIdeal (R := ℂ) m) f)
  change BoundaryArcLiMap.polynomialMap (uniformCandidate m hm) f ∈ _ ↔ _ at h
  change (uniformCandidate m hm).arcLiPoissonHom.toAlgHom
    (InfiniteJet.presentedJetMk (baseIdeal (R := ℂ) m) f) ∈ _ ↔ _
  rw [Candidate.arcLiPoissonHom_mk]
  rw [h]
  constructor
  · rintro ⟨g,hg,he⟩
    refine ⟨g,hg,?_⟩
    apply Ideal.Quotient.eq.mpr
    have he' := Ideal.Quotient.eq.mp he
    rwa [sourceIdeal_eq_jetIdeal] at he'
  · rintro ⟨g,hg,he⟩
    refine ⟨g,hg,?_⟩
    apply Ideal.Quotient.eq.mpr
    have he' := Ideal.Quotient.eq.mp he
    rwa [← sourceIdeal_eq_jetIdeal] at he' 

end
end VOA.AffineSl2BoundaryClassicalFreeness
