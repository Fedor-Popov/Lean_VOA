import VOA.Examples.AffineSl2BoundaryClassicalFreeness
import VOA.Examples.AffineSl2BoundaryDeterminantCharacter

/-! # Arakawa--Dai: boundary classical freeness and the actual vacuum character

The ordinary character is defined independently from actual simple-VOA graded
dimensions. Its upper bound comes from the arc Hilbert calculation; its reverse
bound comes from actual Gram ranks and determinant root orders. Both paper
theorems below are unconditional for every positive boundary index.
-/
namespace VOA.AffineSl2BoundaryCharacter
open AffineSl2BoundarySingularFamily AffineSl2GeneralRigidity
noncomputable section

private theorem simple_grade_finrank_congr (k l : ℂ) (hk : k+2 ≠ 0) (hl : l+2 ≠ 0)
    (h : k=l) (N : ℕ) :
    Module.finrank ℂ ((simple k hk).grading N) = Module.finrank ℂ ((simple l hl).grading N) := by
  subst l
  rfl

/-- The actual simple vacuum character is bounded below by the boundary product. -/
theorem coeff_product_le_character (m : ℕ) (hm : 1 ≤ m) (N : ℕ) :
    PowerSeries.coeff N (product m) ≤ PowerSeries.coeff N (character m) := by
  have hc : (denominator m).Coprime 2 := by simp [denominator]
  have hlevel : 2/(denominator m : ℂ)-2 = level m := by unfold level; ring
  have hk : 2/(denominator m : ℂ)-2+2 ≠ 0 := by
    simpa only [hlevel] using level_noncritical m
  have hbound := universal_grading_finrank_le_simple_add_rootOrder
    (2/(denominator m : ℂ)-2) hk N
  have hbound' :
      (Module.finrank ℂ ((universal (2/(denominator m : ℂ)-2) hk).grading N) : ℚ) ≤
      (Module.finrank ℂ ((simple (2/(denominator m : ℂ)-2) hk).grading N) : ℚ) +
        (vacuumRootOrderTotal (2/(denominator m : ℂ)-2) N : ℚ) := by
    exact_mod_cast hbound
  have horder := vacuumRootOrderTotal_add_product_eq_universal_finrank
    (denominator m) (denominator_pos m) hc hk N
  rw [← horder] at hbound'
  simp only [hlevel] at hbound'
  have hs : Module.finrank ℂ ((simple (2/(denominator m : ℂ)-2) hk).grading N) =
      Module.finrank ℂ ((simple (level m) (level_noncritical m)).grading N) := by
    exact simple_grade_finrank_congr _ _ hk (level_noncritical m) hlevel N
  rw [hs] at hbound'
  rw [coeff_character]
  change PowerSeries.coeff N (product m) ≤
    (Module.finrank ℂ ((simple (level m) (level_noncritical m)).grading N) : ℚ)
  change _ + PowerSeries.coeff N (product m) ≤ _ + _ at hbound'
  linarith

/-- The full actual boundary vacuum character formula, in every conformal weight. -/
theorem character_eq_product (m : ℕ) (hm : 1 ≤ m) :
    character m = product m := by
  apply PowerSeries.ext
  intro N
  exact le_antisymm (coeff_character_le_product m hm N) (coeff_product_le_character m hm N)

/-- Arakawa--Dai Theorem 1.2: the literal descending-chain expression is the
character of the actual simple affine VOA, with no character hypothesis. -/
theorem character_eq_chain (m : ℕ) (hm : 1 ≤ m) :
    character m = QSeries.hilbertBoundSeries m :=
  character_eq_chain_of_product m hm (character_eq_product m hm)

/-- The literal fermionic chain displayed in Arakawa--Dai Theorem 1.2,
including its external reciprocal Euler square and terminal finite q-factorial ratio. -/
theorem character_eq_fermionic_chain (m : ℕ) (hm : 1 ≤ m) :
    character m = (QSeries.reciprocalEuler : PowerSeries ℚ)^2 * QSeries.fermionicTrace m := by
  rw [character_eq_chain m hm,QSeries.hilbertBoundSeries_eq_trace]
  exact mul_comm _ _

end
end VOA.AffineSl2BoundaryCharacter

namespace VOA.AffineSl2BoundaryClassicalFreeness
open BoundaryAuxiliary AffineSl2BoundarySingularFamily AffineSl2BoundaryCharacter
noncomputable section

/-- The actual canonical map is bijective for every positive boundary index. -/
theorem canonicalMap_bijective (m : ℕ) (hm : 1 ≤ m) :
    Function.Bijective (canonicalMap m hm) :=
  canonicalMap_bijective_of_character m hm (character_eq_product m hm)

/-- The genuine intrinsic canonical arc PVA map is bijective. -/
theorem boundary_classically_free (m : ℕ) (hm : 1 ≤ m) :
    Function.Bijective (uniformCandidate m hm).arcLiPoissonHom.toAlgHom :=
  ⟨arcLiPoissonHom_injective_of_character m hm (character_eq_product m hm),
    (uniformCandidate m hm).arcLiPoissonHom_surjective⟩

/-- Arakawa--Dai Theorem 1.1 as a full PVA equivalence. -/
def arcPoissonEquiv (m : ℕ) (hm : 1 ≤ m) :
    PoissonVertexAlgebra.Equiv (arcPVA m)
      (liPoissonVertexAlgebra (AffineSl2BoundaryCharacter.vacuum m)) :=
  arcPoissonEquivOfCharacter m hm (character_eq_product m hm)

/-- Both directions preserve the actual conformal grading. -/
theorem arcPoissonEquiv_conformal_iff (m : ℕ) (hm : 1 ≤ m) (N : ℕ)
    (x : InfiniteJet.PresentedJet (baseIdeal (R := ℂ) m)) :
    (arcPoissonEquiv m hm).toAlgEquiv x ∈
      BoundaryArcConformalSqueeze.liConformalPiece (AffineSl2BoundaryCharacter.vacuum m) N ↔
      x ∈ arcConformalPiece m N :=
  arcPoissonEquivOfCharacter_conformal_iff m hm (character_eq_product m hm) N x

/-- The stated base relations are the exact presentation of the actual C2 algebra. -/
def baseC2AlgEquiv (m : ℕ) (hm : 1 ≤ m) :
    (BasePoly ℂ ⧸ baseIdeal (R := ℂ) m) ≃ₐ[ℂ] A₂ (AffineSl2BoundaryCharacter.vacuum m) :=
  baseC2AlgEquivOfCharacter m hm (character_eq_product m hm)

/-- The source of Theorem 1.1 is the intrinsic arc algebra of the actual C2 algebra: this bijection
is natural in the coefficient algebra (`actualC2ArcEquiv_natural`), so the presented jet algebra
represents the arc functor of `A₂`.  The universal arc itself, with existence and uniqueness of the
factorization, is `c2UniversalArc_universal` (`AffineSl2BoundaryTheorem11.lean`). -/
def actualC2ArcEquiv {A : Type*} [CommRing A] [Algebra ℂ A]
    (m : ℕ) (hm : 1 ≤ m) :
    (InfiniteJet.PresentedJet (baseIdeal (R := ℂ) m) →ₐ[ℂ] A) ≃
      (A₂ (AffineSl2BoundaryCharacter.vacuum m) →ₐ[ℂ] PowerSeries A) :=
  actualC2ArcEquivOfCharacter m hm (character_eq_product m hm)

/-- Naturality of `actualC2ArcEquiv` in the coefficient algebra. -/
theorem actualC2ArcEquiv_natural {A B : Type*} [CommRing A] [Algebra ℂ A]
    [CommRing B] [Algebra ℂ B] (m : ℕ) (hm : 1 ≤ m)
    (f : InfiniteJet.PresentedJet (baseIdeal (R := ℂ) m) →ₐ[ℂ] A) (g : A →ₐ[ℂ] B) :
    actualC2ArcEquiv m hm (g.comp f) = (PowerSeries.mapAlgHom g).comp (actualC2ArcEquiv m hm f) :=
  actualC2ArcEquivOfCharacter_natural m hm _ f g

end
end VOA.AffineSl2BoundaryClassicalFreeness
