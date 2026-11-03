/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.InverseDSGradedUnitarityTransfer

/-!
# Graded unitarity under filtered isometric isomorphisms

This is the linear-algebra transfer step [T] of the reduction of Lee–Yang graded unitarity
to the affine case, following the final, coset-injection steps of the BRST–Koszul transfer argument.

An isometric embedding which maps every source filtration piece onto the corresponding ambient
piece also maps the intrinsic orthogonal layers onto the ambient layers. Ambient piece
nondegeneracy then supplies the `OrthogonallyReducingAt` hypothesis of the inverse-DS API.
Consequently ambient graded unitarity transfers through a filtered isometric isomorphism
intertwining the real structures. Surjectivity on pieces is essential here: strictness only onto
the intersection with a proper image does not suffice.

No coset embedding, BRST construction, character identity, or graded unitarity of a concrete VOA
is constructed. The forms, real structures, flags, and their compatibility are explicit inputs.
-/

namespace VOA
namespace InverseDS.GradedIsometricEmbedding

open VOA.VertexOperatorAlgebra

universe u v

variable {Affine : Type u} {Ambient : Type v}
variable [AddCommGroup Affine] [Module ℂ Affine]
variable [AddCommGroup Ambient] [Module ℂ Ambient]
variable {A : VertexOperatorAlgebra Affine} {T : VertexOperatorAlgebra Ambient}
variable {BA : InvariantForm A} {BT : InvariantForm T}
variable {RA : RealStructure A} {RT : RealStructure T}

/-- Exact images of cumulative pieces give exact images of the strictly smaller pieces, including
the zero piece below filtration degree zero. -/
theorem pieceLT_map_eq_of_piece_map_eq
    (E : GradedIsometricEmbedding A T BA BT RA RT)
    (FA : GradedFlag A) (FT : GradedFlag T) (n : ℤ)
    (hpiece : ∀ p, (FA.pieceIn p n).map (E.weightMap n) = FT.pieceIn p n) (p : ℕ) :
    (FA.pieceLT p n).map (E.weightMap n) = FT.pieceLT p n := by
  cases p with
  | zero => simp
  | succ p => exact hpiece p

/-- An isometry mapping every filtration piece onto its ambient counterpart maps the intrinsic
orthogonal layers onto their counterparts. No nondegeneracy is needed for this identity. -/
theorem layer_map_eq_of_piece_map_eq
    (E : GradedIsometricEmbedding A T BA BT RA RT)
    (FA : GradedFlag A) (FT : GradedFlag T) (n : ℤ)
    (hpiece : ∀ p, (FA.pieceIn p n).map (E.weightMap n) = FT.pieceIn p n) (p : ℕ) :
    (FA.layer n (LiRadical.gradedForm BA n) p).map (E.weightMap n) =
      FT.layer n (LiRadical.gradedForm BT n) p := by
  have hlt := E.pieceLT_map_eq_of_piece_map_eq FA FT n hpiece p
  have hisom (x y : A.grading n) :
      LiRadical.gradedForm BA n x y =
        LiRadical.gradedForm BT n (E.weightMap n x) (E.weightMap n y) :=
    E.form_isometry x y
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← hpiece p]
      exact Submodule.mem_map.mpr ⟨x, hx.1, rfl⟩
    · intro z hz
      rw [← hlt] at hz
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hz
      exact (hisom w x).symm.trans (hx.2 w hw)
  · intro hy
    have hyPiece : y ∈ (FA.pieceIn p n).map (E.weightMap n) := by
      rw [hpiece p]
      exact hy.1
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hyPiece
    refine Submodule.mem_map.mpr ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro z hz
    apply (hisom z x).trans
    apply hy.2
    rw [← hlt]
    exact Submodule.mem_map.mpr ⟨z, hz, rfl⟩

/-- Surjectivity and exact images of filtration pieces supply orthogonal reduction whenever the
ambient cumulative pieces are nondegenerate. Injectivity is already part of the embedding. -/
theorem orthogonallyReducingAt_of_surjective
    (E : GradedIsometricEmbedding A T BA BT RA RT)
    (FA : GradedFlag A) (FT : GradedFlag T) (n : ℤ)
    (hsurj : Function.Surjective (E.weightMap n))
    (hpiece : ∀ p, (FA.pieceIn p n).map (E.weightMap n) = FT.pieceIn p n)
    (hnd : LayerNondegenerate FT n (LiRadical.gradedForm BT n)) :
    E.OrthogonallyReducingAt FA FT n := by
  have hrange : LinearMap.range (E.weightMap n) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  constructor
  · intro p
    rw [hrange, top_inf_eq]
    exact hpiece p
  · intro p
    rw [hpiece p]
    exact hnd p
  · intro p
    rw [hrange, top_inf_eq]
    exact E.layer_map_eq_of_piece_map_eq FA FT n hpiece p

/-- Exhaustivity of the ambient flag makes a map onto every piece surjective on the weight
space. This avoids carrying a separate surjectivity hypothesis in the global transfer theorem. -/
theorem weightMap_surjective_of_piece_map_eq
    (E : GradedIsometricEmbedding A T BA BT RA RT)
    (FA : GradedFlag A) (FT : GradedFlag T) (n : ℤ)
    (hpiece : ∀ p, (FA.pieceIn p n).map (E.weightMap n) = FT.pieceIn p n) :
    Function.Surjective (E.weightMap n) := by
  intro y
  have hy : y ∈ ⨆ p, FT.pieceIn p n := by rw [FT.iSup_pieceIn]; trivial
  have hdir : Directed (· ≤ ·) (fun p => FT.pieceIn p n) :=
    (show Monotone (fun p => FT.pieceIn p n) from fun _ _ h => FT.pieceIn_mono n h).directed_le
  obtain ⟨p, hp⟩ := (Submodule.mem_iSup_of_directed _ hdir).mp hy
  rw [← hpiece p] at hp
  obtain ⟨x, _, hxy⟩ := Submodule.mem_map.mp hp
  exact ⟨x, hxy⟩

/-- Graded unitarity transfers through a real isometric embedding that maps every filtration
piece onto its ambient counterpart. Exhaustivity proves that each weight map is an isomorphism;
the ambient graded-unitarity hypothesis supplies piece nondegeneracy. -/
theorem gradedUnitary_of_filteredIso
    (E : GradedIsometricEmbedding A T BA BT RA RT)
    (FA : GradedFlag A) (FT : GradedFlag T)
    (hpiece : ∀ n p, (FA.pieceIn p n).map (E.weightMap n) = FT.pieceIn p n)
    (hambient : GradedUnitary BT RT FT) : GradedUnitary BA RA FA := by
  apply E.gradedUnitary_of_ambient FA FT
  · intro n
    exact E.orthogonallyReducingAt_of_surjective FA FT n
      (E.weightMap_surjective_of_piece_map_eq FA FT n (hpiece n)) (hpiece n) (hambient n).1
  · exact hambient

end InverseDS.GradedIsometricEmbedding

namespace LeeYangCosetTransfer

open VOA.VertexOperatorAlgebra InverseDS

universe u v

variable {C : Type u} {H : Type v}
variable [AddCommGroup C] [Module ℂ C] [AddCommGroup H] [Module ℂ H]
variable {A : VertexOperatorAlgebra C} {T : VertexOperatorAlgebra H}
variable {BA : InvariantForm A} {BT : InvariantForm T}
variable {RA : RealStructure A} {RT : RealStructure T}

/-- An unbundled linear-equivalence version of the transfer theorem. The given equivalence
preserves weight, invariant forms, and real structures, and maps the source flag exactly onto
the target flag. These are linear and metric inputs, with no assumed VOA homomorphism. -/
theorem gradedUnitary_of_filteredLinearEquiv
    (e : C ≃ₗ[ℂ] H) (FA : GradedFlag A) (FT : GradedFlag T)
    (hgrading : ∀ n x, x ∈ A.grading n → e x ∈ T.grading n)
    (hform : ∀ x y, BA.form x y = BT.form (e x) (e y))
    (hrho : ∀ x, e (RA.rho x) = RT.rho (e x))
    (hpiece : ∀ n p, (FA.piece p n).map e.toLinearMap = FT.piece p n)
    (hambient : GradedUnitary BT RT FT) : GradedUnitary BA RA FA := by
  let E : GradedIsometricEmbedding A T BA BT RA RT :=
    { iota := e.toLinearMap
      iota_injective := e.injective
      map_grading := hgrading
      form_isometry := hform
      rho_compatible := hrho }
  apply E.gradedUnitary_of_filteredIso FA FT _ hambient
  intro n p
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change e (x : C) ∈ FT.piece p n
    rw [← hpiece n p]
    exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  · intro hy
    have hy' : (y : H) ∈ (FA.piece p n).map e.toLinearMap := by
      rw [hpiece n p]
      exact hy
    obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy'
    refine Submodule.mem_map.mpr ⟨⟨x, FA.le_grading p n hx⟩, hx, ?_⟩
    exact Subtype.ext hxy

end LeeYangCosetTransfer
end VOA
