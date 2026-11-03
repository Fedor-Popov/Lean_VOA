/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.LinearAlgebra.Quotient.Basic
import VOA.Core.GradedUnitarity

/-!
# Interface for a parameter-changing screened--Rees map

This file is intentionally hypothesis-only.  It separates the formal linear
algebra required by Program B from the missing analytic construction of a
charge-balanced screened vertex and its Selberg-cycle finite part.

`Length` always means the Virasoro PBW/R filtration here, not the Li
filtration.  Any comparison between the two must be supplied as a separate,
explicit reindexing hypothesis.
-/

namespace VOA
namespace ScreenedRees

variable {𝕜 V W A : Type*}
variable [CommRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
variable [AddCommGroup W] [Module 𝕜 W]

/-- A cumulative filtration indexed by Virasoro PBW length. -/
def IsCumulativeLengthFiltration (F : ℕ → Submodule 𝕜 V) : Prop :=
  Monotone F

/-- A named compatibility hypothesis for two filtrations.  The map `ρ` is
external data; in particular this does not identify a PBW/R filtration with
the Li filtration by definition. -/
def HasFiltrationReindexing (F G : ℕ → Submodule 𝕜 V) (ρ : ℕ → ℕ) : Prop :=
  ∀ p, F p = G (ρ p)

/-- A linear map preserves the cumulative length filtration. -/
def PreservesLengthFiltration (F : ℕ → Submodule 𝕜 V)
    (G : ℕ → Submodule 𝕜 W) (f : V →ₗ[𝕜] W) : Prop :=
  ∀ p, ∀ x : V, x ∈ F p → f x ∈ G p

/-- The formal condition needed for a finite part to descend through a
Felder kernel-modulo-boundary quotient. -/
def PreservesFelderData (sourceClosed sourceBoundary : Submodule 𝕜 V)
    (targetClosed targetBoundary : Submodule 𝕜 W) (f : V →ₗ[𝕜] W) : Prop :=
  sourceBoundary ≤ sourceClosed ∧
    targetBoundary ≤ targetClosed ∧
    (∀ x, x ∈ sourceClosed → f x ∈ targetClosed) ∧
    (∀ x, x ∈ sourceBoundary → f x ∈ targetBoundary)

/-- The boundary submodule regarded inside the closed subspace. -/
def boundaryInClosed (closed boundary : Submodule 𝕜 V) : Submodule 𝕜 closed :=
  boundary.comap closed.subtype

/-- Restrict a map preserving closed vectors to the closed subspaces. -/
def closedMap (sourceClosed sourceBoundary : Submodule 𝕜 V)
    (targetClosed targetBoundary : Submodule 𝕜 W) (f : V →ₗ[𝕜] W)
    (h : PreservesFelderData sourceClosed sourceBoundary targetClosed targetBoundary f) :
    sourceClosed →ₗ[𝕜] targetClosed where
  toFun x := ⟨f x, h.2.2.1 x x.property⟩
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

/-- The finite coefficient induced on Felder cohomology.  This is a construction, not an
existence assumption: the only input is preservation of closed vectors and boundaries. -/
def felderQuotientMap (sourceClosed sourceBoundary : Submodule 𝕜 V)
    (targetClosed targetBoundary : Submodule 𝕜 W) (f : V →ₗ[𝕜] W)
    (h : PreservesFelderData sourceClosed sourceBoundary targetClosed targetBoundary f) :
    sourceClosed ⧸ boundaryInClosed sourceClosed sourceBoundary →ₗ[𝕜]
      targetClosed ⧸ boundaryInClosed targetClosed targetBoundary :=
  (boundaryInClosed sourceClosed sourceBoundary).mapQ
    (boundaryInClosed targetClosed targetBoundary)
    (closedMap sourceClosed sourceBoundary targetClosed targetBoundary f h) (by
      intro x hx
      change f x ∈ targetBoundary
      exact h.2.2.2 x (by simpa [boundaryInClosed] using hx))

@[simp]
theorem felderQuotientMap_mkQ
    (sourceClosed sourceBoundary : Submodule 𝕜 V)
    (targetClosed targetBoundary : Submodule 𝕜 W) (f : V →ₗ[𝕜] W)
    (h : PreservesFelderData sourceClosed sourceBoundary targetClosed targetBoundary f)
    (x : sourceClosed) :
    felderQuotientMap sourceClosed sourceBoundary targetClosed targetBoundary f h
        ((boundaryInClosed sourceClosed sourceBoundary).mkQ x) =
      (boundaryInClosed targetClosed targetBoundary).mkQ
        (closedMap sourceClosed sourceBoundary targetClosed targetBoundary f h x) := by
  apply Submodule.mapQ_apply

/-- The preceding cumulative filtration piece, regarded as a submodule of the current piece.
At degree zero there is no preceding piece. -/
def previousFiltrationPiece (F : ℕ → Submodule 𝕜 V) :
    (p : ℕ) → Submodule 𝕜 (F p)
  | 0 => ⊥
  | p + 1 => (F p).comap (F (p + 1)).subtype

/-- The exact-length associated-graded layer of a cumulative filtration. -/
abbrev ExactFiltrationLayer (F : ℕ → Submodule 𝕜 V) (p : ℕ) :=
  F p ⧸ previousFiltrationPiece F p

/-- Restriction of a filtration-preserving map to one cumulative piece. -/
def filteredPieceMap (sourceLength : ℕ → Submodule 𝕜 V)
    (targetLength : ℕ → Submodule 𝕜 W) (f : V →ₗ[𝕜] W)
    (h : PreservesLengthFiltration sourceLength targetLength f) (p : ℕ) :
    sourceLength p →ₗ[𝕜] targetLength p where
  toFun x := ⟨f x, h p x x.property⟩
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

/-- A filtration-preserving map induces a map on each exact-length Rees layer. -/
def exactFiltrationLayerMap (sourceLength : ℕ → Submodule 𝕜 V)
    (targetLength : ℕ → Submodule 𝕜 W) (f : V →ₗ[𝕜] W)
    (h : PreservesLengthFiltration sourceLength targetLength f) (p : ℕ) :
    ExactFiltrationLayer sourceLength p →ₗ[𝕜] ExactFiltrationLayer targetLength p :=
  (previousFiltrationPiece sourceLength p).mapQ
    (previousFiltrationPiece targetLength p)
    (filteredPieceMap sourceLength targetLength f h p) (by
      cases p with
      | zero => simp [previousFiltrationPiece]
      | succ p =>
          intro x hx
          change f x ∈ targetLength p
          exact h p x (by simpa [previousFiltrationPiece] using hx))

@[simp]
theorem exactFiltrationLayerMap_mkQ
    (sourceLength : ℕ → Submodule 𝕜 V)
    (targetLength : ℕ → Submodule 𝕜 W) (f : V →ₗ[𝕜] W)
    (h : PreservesLengthFiltration sourceLength targetLength f) (p : ℕ)
    (x : sourceLength p) :
    exactFiltrationLayerMap sourceLength targetLength f h p
        ((previousFiltrationPiece sourceLength p).mkQ x) =
      (previousFiltrationPiece targetLength p).mkQ
        (filteredPieceMap sourceLength targetLength f h p x) := by
  apply Submodule.mapQ_apply

section RepresentativeGauge

variable {B C D H : Type*}
variable [AddCommGroup B] [Module 𝕜 B]
variable [AddCommGroup C] [Module 𝕜 C]
variable [AddCommGroup D] [Module 𝕜 D]
variable [AddCommGroup H] [Module 𝕜 H]

/-- A map which annihilates boundaries is unchanged when chosen cohomology representatives are
modified by a boundary.  Thus a contracting-homotopy gauge cannot create a missing shear in an
already descended map. -/
theorem descendedMap_invariant_under_boundaryChange
    (Q : B →ₗ[𝕜] C) (f : C →ₗ[𝕜] D)
    (i i' : H →ₗ[𝕜] C) (A : H →ₗ[𝕜] B)
    (hdesc : f.comp Q = 0) (hgauge : i' = i + Q.comp A) :
    f.comp i' = f.comp i := by
  subst i'
  ext x
  change f (i x + Q (A x)) = f (i x)
  rw [map_add]
  have hboundary : f (Q (A x)) = 0 := by
    exact LinearMap.congr_fun hdesc (A x)
  rw [hboundary, add_zero]

end RepresentativeGauge

/-- A matrix is upper triangular for an externally supplied dominance order. -/
def IsDominanceTriangular {ι : Type*} (lt : ι → ι → Prop)
    (M : ι → ι → 𝕜) : Prop :=
  ∀ i j, lt j i → M i j = 0

/-- The algebraic metric-transport condition.  The positive scalar and the
specific forms must be supplied by the screened construction. -/
def PullsBackForm (sourceForm : V → V → 𝕜) (targetForm : W → W → 𝕜)
    (f : V →ₗ[𝕜] W) (scale : 𝕜) : Prop :=
  ∀ x y, sourceForm x y = scale * targetForm (f x) (f y)

/-- Generator-level intertwining.  For Program B, `A` indexes symmetric
Dunkl generators on the target and the resonant free-field generators on the
source. -/
def IntertwinesActions (sourceAction : A → V →ₗ[𝕜] V)
    (targetAction : A → W →ₗ[𝕜] W) (f : V →ₗ[𝕜] W) : Prop :=
  ∀ a, f.comp (sourceAction a) = (targetAction a).comp f

/-- Explicit hypotheses required of a proposed parameter-changing
screened--Rees map.  This is an interface only: no field is postulated to
exist for the Lee--Yang or general boundary modules. -/
structure Hypotheses
    (sourceClosed sourceBoundary : Submodule 𝕜 V)
    (targetClosed targetBoundary : Submodule 𝕜 W)
    (sourceLength : ℕ → Submodule 𝕜 V)
    (targetLength : ℕ → Submodule 𝕜 W)
    (finitePart : V →ₗ[𝕜] W) where
  sourceFiltration : IsCumulativeLengthFiltration sourceLength
  targetFiltration : IsCumulativeLengthFiltration targetLength
  felderDescent : PreservesFelderData sourceClosed sourceBoundary
    targetClosed targetBoundary finitePart
  lengthFiltered : PreservesLengthFiltration sourceLength targetLength finitePart

section MetricTransfer

variable {E F : Type*}
variable [AddCommGroup E] [Module ℂ E]
variable [AddCommGroup F] [Module ℂ F]

/-- The formal last step of Program B on one exact-length layer.

Once the analytic construction supplies an injective screened--Rees map and a positive-scale
metric pullback identity, positivity of the Jack form transfers to the Virasoro form.  The proof
does not use oscillator-space positivity or any representation-theoretic axiom. -/
theorem isPosOn_of_metricTransport
    (sourceForm : SesqForm E) (targetForm : SesqForm F)
    (f : E →ₗ[ℂ] F) (scale : ℝ)
    (hf : Function.Injective f) (hscale : 0 < scale)
    (hmetric : PullsBackForm sourceForm targetForm f (scale : ℂ))
    (htarget : IsPosOn targetForm (⊤ : Submodule ℂ F)) :
    IsPosOn sourceForm (⊤ : Submodule ℂ E) := by
  intro x _ hx
  have hfx : f x ≠ 0 := by
    intro hzero
    apply hx
    apply hf
    simpa using hzero
  obtain ⟨r, hr, hdiag⟩ := htarget (f x) Submodule.mem_top hfx
  refine ⟨scale * r, mul_pos hscale hr, ?_⟩
  rw [hmetric x x, hdiag]
  exact_mod_cast rfl

end MetricTransfer

end ScreenedRees
end VOA
