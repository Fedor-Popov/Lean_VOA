/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Dual injection from a finite cost degeneration

This file isolates the linear-algebra mechanism used by auxiliary degenerations in fixed finite
bidegree.  A cost filtration separates the dual of the original source into a product of duals of
its associated sectors.  A tractable initial presentation then surjects onto every associated
sector.  Dualizing those surjections and composing with sectorwise carrier equivalences gives an
injective map from the original dual into the product carrier.

An actual exhaustive finite filtration automatically supplies the dual splitting by telescoping
the dimensions of its successive quotients; no character identity is needed for that step.  The
construction still does not assert that a particular affine filtration has the proposed initial
sectors.  That mathematical input remains visible in the surjectivity field of
`SectorwiseInitialPresentation`.
-/

namespace VOA.FiniteCostDegeneration

noncomputable section

universe u v w x y

variable (K : Type u) [Field K]
variable (Source : ModuleCat.{v} K) (ι : Type w)

/-- A cost decomposition in one finite bidegree, expressed on restricted duals.  In an
application, `Associated i` is the `i`th associated sector of an exhaustive finite filtration.
The equivalence is the finite-dimensional splitting of that filtration; it is deliberately
separate from the auxiliary initial presentation. -/
structure CostDualDecomposition where
  Associated : ι → ModuleCat.{x} K
  sourceDualEquiv :
    Module.Dual K Source ≃ₗ[K] ((i : ι) → Module.Dual K (Associated i))

namespace CostDualDecomposition

/-- Construct the noncanonical dual splitting once an independently proved finite-filtration
dimension identity is available.  In applications the equality must come from an exhaustive cost
filtration; using the desired character identity here would be circular. -/
noncomputable def ofFinrankEq
    [Fintype ι] [FiniteDimensional K Source]
    (Associated : ι → ModuleCat.{x} K)
    [∀ i, FiniteDimensional K (Associated i)]
    (h : Module.finrank K Source = ∑ i, Module.finrank K (Associated i)) :
    CostDualDecomposition K Source ι where
  Associated := Associated
  sourceDualEquiv := LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_pi_fintype]
    simpa only [Subspace.dual_finrank_eq] using h)

end CostDualDecomposition

/-- An exhaustive finite decreasing cost filtration.  `piece i` is allowed to remain nonzero for
arbitrary `i`, but the single bound `piece (maxCost + 1) = bot`, together with antitonicity,
records the finite support needed in a fixed bidegree. -/
structure FiniteCostFiltration (maxCost : ℕ) where
  piece : ℕ → Submodule K Source
  antitone : Antitone piece
  piece_zero : piece 0 = ⊤
  piece_succ_max : piece (maxCost + 1) = ⊥

namespace FiniteCostFiltration

variable {maxCost : ℕ}

/-- The `i`th associated sector of a decreasing cost filtration. -/
abbrev CostAssociated (F : FiniteCostFiltration K Source maxCost) (i : ℕ) :=
  F.piece i ⧸ (F.piece (i + 1)).comap (F.piece i).subtype

/-- One associated-sector dimension plus the next filtration dimension is the present filtration
dimension. -/
theorem associated_finrank_add_next
    [FiniteDimensional K Source]
    (F : FiniteCostFiltration K Source maxCost) (i : ℕ) :
    Module.finrank K (CostAssociated (K := K) (Source := Source) F i) +
        Module.finrank K (F.piece (i + 1)) =
      Module.finrank K (F.piece i) := by
  let lowerInUpper := (F.piece (i + 1)).comap (F.piece i).subtype
  have hle : F.piece (i + 1) ≤ F.piece i := F.antitone (Nat.le_succ i)
  have hquot := lowerInUpper.finrank_quotient_add_finrank
  have heq : Module.finrank K lowerInUpper = Module.finrank K (F.piece (i + 1)) :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle)
  simpa only [CostAssociated, lowerInUpper, heq] using hquot

/-- Telescoping the associated-sector dimensions through the first `k` filtration steps leaves
the dimension of `piece k`. -/
theorem sum_range_associated_finrank_add_piece
    [FiniteDimensional K Source]
    (F : FiniteCostFiltration K Source maxCost) (k : ℕ) :
    (∑ i ∈ Finset.range k,
        Module.finrank K (CostAssociated (K := K) (Source := Source) F i)) +
        Module.finrank K (F.piece k) =
      Module.finrank K Source := by
  induction k with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, zero_add]
      rw [F.piece_zero, finrank_top]
  | succ k ih =>
      rw [Finset.sum_range_succ]
      calc
        ((∑ i ∈ Finset.range k,
              Module.finrank K (CostAssociated (K := K) (Source := Source) F i)) +
              Module.finrank K (CostAssociated (K := K) (Source := Source) F k)) +
            Module.finrank K (F.piece (k + 1)) =
          (∑ i ∈ Finset.range k,
              Module.finrank K (CostAssociated (K := K) (Source := Source) F i)) +
            (Module.finrank K (CostAssociated (K := K) (Source := Source) F k) +
              Module.finrank K (F.piece (k + 1))) := by omega
        _ = (∑ i ∈ Finset.range k,
              Module.finrank K (CostAssociated (K := K) (Source := Source) F i)) +
            Module.finrank K (F.piece k) := by
          rw [associated_finrank_add_next (K := K) (Source := Source) F k]
        _ = Module.finrank K Source := ih

/-- The dimensions of all nonzero associated cost sectors sum to the source dimension. -/
theorem sum_associated_finrank
    [FiniteDimensional K Source]
    (F : FiniteCostFiltration K Source maxCost) :
    ∑ i : Fin (maxCost + 1),
        Module.finrank K (CostAssociated (K := K) (Source := Source) F i.1) =
      Module.finrank K Source := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    Module.finrank K (CostAssociated (K := K) (Source := Source) F i))]
  have h := sum_range_associated_finrank_add_piece
    (K := K) (Source := Source) (maxCost := maxCost) F (maxCost + 1)
  rw [F.piece_succ_max, finrank_bot, add_zero] at h
  exact h

/-- Every exhaustive finite cost filtration supplies the noncanonical dual splitting required by
`CostDualDecomposition`.  The construction uses only the telescoping associated-sector dimension
identity, not a character formula. -/
noncomputable def costDualDecomposition
    [FiniteDimensional K Source]
    (F : FiniteCostFiltration K Source maxCost) :
    CostDualDecomposition K Source (Fin (maxCost + 1)) :=
  CostDualDecomposition.ofFinrankEq
    (K := K) (Source := Source) (ι := Fin (maxCost + 1))
    (fun i => ModuleCat.of K
      (CostAssociated (K := K) (Source := Source) F i.1))
    F.sum_associated_finrank.symm

end FiniteCostFiltration

variable {K Source ι}

/-- A sectorwise initial presentation over a fixed cost decomposition.  Each tractable initial
sector surjects onto the corresponding true associated sector, while its dual is identified with
the concrete functional carrier. -/
structure SectorwiseInitialPresentation
    (D : CostDualDecomposition K Source ι)
    (Carrier : ι → ModuleCat.{y} K) where
  Initial : ι → ModuleCat.{x} K
  initialToAssociated : ∀ i, Initial i →ₗ[K] D.Associated i
  initialToAssociated_surjective : ∀ i, Function.Surjective (initialToAssociated i)
  initialDualCarrierEquiv : ∀ i, Module.Dual K (Initial i) ≃ₗ[K] Carrier i

namespace SectorwiseInitialPresentation

variable {D : CostDualDecomposition K Source ι}
variable {Carrier : ι → ModuleCat.{y} K}

/-- Dualize every initial-presentation quotient simultaneously. -/
def associatedDualToInitialDual
    (P : SectorwiseInitialPresentation D Carrier) :
    ((i : ι) → Module.Dual K (D.Associated i)) →ₗ[K]
      ((i : ι) → Module.Dual K (P.Initial i)) where
  toFun f i := (P.initialToAssociated i).dualMap (f i)
  map_add' f g := by
    funext i
    exact (P.initialToAssociated i).dualMap.map_add (f i) (g i)
  map_smul' k f := by
    funext i
    exact (P.initialToAssociated i).dualMap.map_smul k (f i)

/-- The product dual map is injective because every initial presentation is surjective. -/
theorem associatedDualToInitialDual_injective
    (P : SectorwiseInitialPresentation D Carrier) :
    Function.Injective P.associatedDualToInitialDual := by
  intro f g h
  funext i
  apply LinearMap.dualMap_injective_of_surjective
    (P.initialToAssociated_surjective i)
  exact congrFun h i

/-- Apply the proved coefficient/carrier equivalence in every cost sector. -/
def initialDualToCarrier
    (P : SectorwiseInitialPresentation D Carrier) :
    ((i : ι) → Module.Dual K (P.Initial i)) →ₗ[K] ((i : ι) → Carrier i) where
  toFun f i := P.initialDualCarrierEquiv i (f i)
  map_add' f g := by
    funext i
    exact (P.initialDualCarrierEquiv i).map_add (f i) (g i)
  map_smul' k f := by
    funext i
    exact (P.initialDualCarrierEquiv i).map_smul k (f i)

/-- A product of sectorwise linear equivalences is injective. -/
theorem initialDualToCarrier_injective
    (P : SectorwiseInitialPresentation D Carrier) :
    Function.Injective P.initialDualToCarrier := by
  intro f g h
  funext i
  apply (P.initialDualCarrierEquiv i).injective
  exact congrFun h i

/-- The canonical dual-to-carrier map attached to the separated degeneration data. -/
def sourceDualToCarrier
    (P : SectorwiseInitialPresentation D Carrier) :
    Module.Dual K Source →ₗ[K] ((i : ι) → Carrier i) :=
  P.initialDualToCarrier.comp
    (P.associatedDualToInitialDual.comp D.sourceDualEquiv.toLinearMap)

/-- The cost splitting, sectorwise quotient maps, and coefficient-pairing equivalences suffice
for source-dual injectivity.  There is no additional global injectivity hypothesis. -/
theorem sourceDualToCarrier_injective
    (P : SectorwiseInitialPresentation D Carrier) :
    Function.Injective P.sourceDualToCarrier :=
  P.initialDualToCarrier_injective.comp
    (P.associatedDualToInitialDual_injective.comp D.sourceDualEquiv.injective)

end SectorwiseInitialPresentation

end

end VOA.FiniteCostDegeneration

section AxiomAudit
namespace VOA.FiniteCostDegeneration.CostDualDecomposition
#print axioms ofFinrankEq
end VOA.FiniteCostDegeneration.CostDualDecomposition
namespace VOA.FiniteCostDegeneration.FiniteCostFiltration
#print axioms associated_finrank_add_next
#print axioms sum_associated_finrank
#print axioms costDualDecomposition
end VOA.FiniteCostDegeneration.FiniteCostFiltration
namespace VOA.FiniteCostDegeneration.SectorwiseInitialPresentation
#print axioms associatedDualToInitialDual_injective
#print axioms initialDualToCarrier_injective
#print axioms sourceDualToCarrier_injective
end VOA.FiniteCostDegeneration.SectorwiseInitialPresentation
end AxiomAudit
