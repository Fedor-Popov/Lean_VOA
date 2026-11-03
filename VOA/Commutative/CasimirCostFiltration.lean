/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.FiniteCostDegeneration
import VOA.Commutative.MvPolynomialFiniteHomogeneous
import VOA.Commutative.MvPolynomialMinimumWeight

/-!
# The finite-weight Casimir-adic filtration

Let `P` be a weighted polynomial ring, let `H_N` be its homogeneous piece of
weight `N`, and let `I` be an ideal supported in weights at least two.  This
file constructs the filtration induced on any linear quotient of `H_N` by
the powers of `I`.

The central result is literal finite-weight nilpotence: the depth-`d` piece
is zero when `N < 2 * d`.  Consequently the filtration has only the sectors
`0, ..., N / 2`, and its exact associated layers telescope to the dimension
of the quotient.  This is the formal content of the statement that the
Casimir-adic filtration preserves every fixed conformal-weight dimension.

No assertion is made about the presentation of an associated layer.  In
particular, the theorem does not assume that the reduced current equations,
the mixed current--Casimir equations, and the Casimir-square equations
exhaust the initial ideal.  A map from that explicit auxiliary presentation
onto the associated layers is separate mathematical data.
-/

namespace VOA.CasimirCostFiltration

open VOA.FiniteCostDegeneration
open VOA.MvPolynomialFiniteHomogeneous
open VOA.MvPolynomialMinimumWeight

noncomputable section

universe uK uσ uV

variable {K : Type uK} [Field K]
variable {σ : Type uσ}
variable {V : Type uV} [AddCommGroup V] [Module K V]

/-- The exact weighted-homogeneous polynomial source in conformal weight `N`. -/
abbrev HomogeneousSource (w : σ → ℕ) (N : ℕ) :=
  MvPolynomial.weightedHomogeneousSubmodule K w N

/-- Representatives in weight `N` which lie in the `d`th power of `I`. -/
def polynomialCostPiece (w : σ → ℕ) (N : ℕ)
    (I : Ideal (MvPolynomial σ K)) (d : ℕ) :
    Submodule K (HomogeneousSource (K := K) w N) :=
  ((I ^ d).restrictScalars K).comap
    (Submodule.subtype (HomogeneousSource (K := K) w N))

/-- Increasing the required ideal power decreases the representative piece. -/
theorem polynomialCostPiece_antitone (w : σ → ℕ) (N : ℕ)
    (I : Ideal (MvPolynomial σ K)) :
    Antitone (polynomialCostPiece (K := K) w N I) := by
  intro d e hde f hf
  exact Ideal.pow_le_pow_right hde hf

/-- If the ideal starts in weight two, its depth-`d` part has no nonzero
representative of weight below `2 * d`. -/
theorem polynomialCostPiece_eq_bot_of_lt
    (w : σ → ℕ) (N : ℕ) (I : Ideal (MvPolynomial σ K))
    (hI : I ≤ minimumWeightIdeal w 2) (d : ℕ) (hN : N < 2 * d) :
    polynomialCostPiece (K := K) w N I d = ⊥ := by
  apply le_antisymm
  · intro f hf
    rw [Submodule.mem_bot]
    apply Subtype.ext
    apply eq_zero_of_isWeightedHomogeneous_of_mem_minimumWeightIdeal f.2
    · apply ideal_pow_le_minimumWeightIdeal w 2 I hI d
      exact hf
    · simpa only [Nat.mul_comm] using hN
  · exact bot_le

/-- The image in a quotient (or any surjective linear target) of the
weight-`N`, depth-`d` representative piece. -/
def quotientCostPiece (w : σ → ℕ) (N : ℕ)
    (I : Ideal (MvPolynomial σ K))
    (q : HomogeneousSource (K := K) w N →ₗ[K] V) (d : ℕ) :
    Submodule K V :=
  (polynomialCostPiece (K := K) w N I d).map q

/-- The quotient Casimir-cost pieces form a decreasing filtration. -/
theorem quotientCostPiece_antitone (w : σ → ℕ) (N : ℕ)
    (I : Ideal (MvPolynomial σ K))
    (q : HomogeneousSource (K := K) w N →ₗ[K] V) :
    Antitone (quotientCostPiece (K := K) w N I q) := by
  intro d e hde
  exact Submodule.map_mono (polynomialCostPiece_antitone w N I hde)

/-- Depth zero exhausts the target whenever the homogeneous representative
map is onto. -/
theorem quotientCostPiece_zero (w : σ → ℕ) (N : ℕ)
    (I : Ideal (MvPolynomial σ K))
    (q : HomogeneousSource (K := K) w N →ₗ[K] V)
    (hq : Function.Surjective q) :
    quotientCostPiece (K := K) w N I q 0 = ⊤ := by
  rw [quotientCostPiece]
  have hpoly : polynomialCostPiece (K := K) w N I 0 = ⊤ := by
    ext f
    simp [polynomialCostPiece]
  rw [hpoly, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr hq

/-- Finite-weight nilpotence survives every linear quotient of the
homogeneous source. -/
theorem quotientCostPiece_eq_bot_of_lt
    (w : σ → ℕ) (N : ℕ) (I : Ideal (MvPolynomial σ K))
    (hI : I ≤ minimumWeightIdeal w 2)
    (q : HomogeneousSource (K := K) w N →ₗ[K] V)
    (d : ℕ) (hN : N < 2 * d) :
    quotientCostPiece (K := K) w N I q d = ⊥ := by
  rw [quotientCostPiece,
    polynomialCostPiece_eq_bot_of_lt w N I hI d hN]
  exact Submodule.map_bot q

/-- The largest possible number of weight-two Casimir factors in weight `N`. -/
def maxCost (N : ℕ) : ℕ := N / 2

/-- The concrete finite decreasing filtration induced by powers of a
weight-at-least-two ideal on a fixed homogeneous quotient. -/
def filtration (w : σ → ℕ) (N : ℕ)
    (I : Ideal (MvPolynomial σ K)) (hI : I ≤ minimumWeightIdeal w 2)
    (q : HomogeneousSource (K := K) w N →ₗ[K] V)
    (hq : Function.Surjective q) :
    FiniteCostFiltration K (ModuleCat.of K V) (maxCost N) where
  piece d := quotientCostPiece (K := K) w N I q d
  antitone := quotientCostPiece_antitone w N I q
  piece_zero := quotientCostPiece_zero w N I q hq
  piece_succ_max := by
    apply quotientCostPiece_eq_bot_of_lt w N I hI q
    dsimp [maxCost]
    omega

/-- The packaged finite filtration is the literal ideal-power filtration
at every depth. -/
theorem filtration_piece
    (w : σ → ℕ) (N : ℕ)
    (I : Ideal (MvPolynomial σ K)) (hI : I ≤ minimumWeightIdeal w 2)
    (q : HomogeneousSource (K := K) w N →ₗ[K] V)
    (hq : Function.Surjective q) (d : ℕ) :
    (filtration (K := K) w N I hI q hq).piece d =
      quotientCostPiece (K := K) w N I q d := by
  rfl

/-- The first ideal power beyond the physical range is already zero for
the literal filtration, before the finite-filtration packaging truncates it. -/
theorem quotientCostPiece_succ_max_eq_bot
    (w : σ → ℕ) (N : ℕ)
    (I : Ideal (MvPolynomial σ K)) (hI : I ≤ minimumWeightIdeal w 2)
    (q : HomogeneousSource (K := K) w N →ₗ[K] V) :
    quotientCostPiece (K := K) w N I q (maxCost N + 1) = ⊥ := by
  apply quotientCostPiece_eq_bot_of_lt w N I hI q
  dsimp [maxCost]
  omega

/-- One exact Casimir-cost layer of the concrete filtration. -/
abbrev Associated (w : σ → ℕ) (N : ℕ)
    (I : Ideal (MvPolynomial σ K)) (hI : I ≤ minimumWeightIdeal w 2)
    (q : HomogeneousSource (K := K) w N →ₗ[K] V)
    (hq : Function.Surjective q) (d : ℕ) :=
  FiniteCostFiltration.CostAssociated
    (K := K) (Source := ModuleCat.of K V)
    (filtration (K := K) w N I hI q hq) d

/-- Homogeneous representatives in `I ^ d` map onto the corresponding
filtration piece. -/
def polynomialCostPieceToFiltration
    (w : σ → ℕ) (N : ℕ)
    (I : Ideal (MvPolynomial σ K)) (hI : I ≤ minimumWeightIdeal w 2)
    (q : HomogeneousSource (K := K) w N →ₗ[K] V)
    (hq : Function.Surjective q) (d : ℕ) :
    polynomialCostPiece (K := K) w N I d →ₗ[K]
      (filtration (K := K) w N I hI q hq).piece d where
  toFun f := ⟨q f.1, by
    change q f.1 ∈ quotientCostPiece (K := K) w N I q d
    exact ⟨f.1, f.2, rfl⟩⟩
  map_add' f g := Subtype.ext (map_add q f.1 g.1)
  map_smul' c f := Subtype.ext (map_smul q c f.1)

/-- Every filtration element has a homogeneous representative in the
matching ideal power. -/
theorem polynomialCostPieceToFiltration_surjective
    (w : σ → ℕ) (N : ℕ)
    (I : Ideal (MvPolynomial σ K)) (hI : I ≤ minimumWeightIdeal w 2)
    (q : HomogeneousSource (K := K) w N →ₗ[K] V)
    (hq : Function.Surjective q) (d : ℕ) :
    Function.Surjective
      (polynomialCostPieceToFiltration (K := K) w N I hI q hq d) := by
  intro x
  have hx : x.1 ∈ quotientCostPiece (K := K) w N I q d := by
    exact x.2
  rcases hx with ⟨f, hf, hfx⟩
  refine ⟨⟨f, hf⟩, Subtype.ext ?_⟩
  exact hfx

/-- Canonical map from homogeneous representatives in `I ^ d` to the
true `d`th associated layer. -/
def polynomialCostToAssociated
    (w : σ → ℕ) (N : ℕ)
    (I : Ideal (MvPolynomial σ K)) (hI : I ≤ minimumWeightIdeal w 2)
    (q : HomogeneousSource (K := K) w N →ₗ[K] V)
    (hq : Function.Surjective q) (d : ℕ) :
    polynomialCostPiece (K := K) w N I d →ₗ[K]
      Associated (K := K) w N I hI q hq d :=
  (((filtration (K := K) w N I hI q hq).piece (d + 1)).comap
      ((filtration (K := K) w N I hI q hq).piece d).subtype).mkQ.comp
    (polynomialCostPieceToFiltration (K := K) w N I hI q hq d)

/-- The representative map onto every true associated layer is surjective.
This uses only the definition of the ideal-power filtration and quotient
surjectivity.  Further explicit auxiliary relations may be imposed on the
domain once one proves that they lie in its kernel. -/
theorem polynomialCostToAssociated_surjective
    (w : σ → ℕ) (N : ℕ)
    (I : Ideal (MvPolynomial σ K)) (hI : I ≤ minimumWeightIdeal w 2)
    (q : HomogeneousSource (K := K) w N →ₗ[K] V)
    (hq : Function.Surjective q) (d : ℕ) :
    Function.Surjective
      (polynomialCostToAssociated (K := K) w N I hI q hq d) :=
  (Submodule.mkQ_surjective _).comp
    (polynomialCostPieceToFiltration_surjective
      (K := K) w N I hI q hq d)

/-- Positive variable weights make the fixed-weight polynomial source
finite dimensional. -/
instance homogeneousSource_finiteDimensional [Finite σ]
    (w : σ → ℕ) (hw : ∀ i, w i ≠ 0) (N : ℕ) :
    FiniteDimensional K (HomogeneousSource (K := K) w N) :=
  finiteDimensional_weightedHomogeneousSubmodule w hw N

/-- A target generated by one fixed finite-variable homogeneous source is
finite dimensional. -/
theorem target_finiteDimensional [Finite σ]
    (w : σ → ℕ) (hw : ∀ i, w i ≠ 0) (N : ℕ)
    (q : HomogeneousSource (K := K) w N →ₗ[K] V)
    (hq : Function.Surjective q) :
    FiniteDimensional K V := by
  letI := homogeneousSource_finiteDimensional (K := K) w hw N
  exact FiniteDimensional.of_surjective q hq

/-- In finite variables, the dimensions of the Casimir-cost associated
layers telescope exactly to the target dimension. -/
theorem sum_associated_finrank [Finite σ]
    (w : σ → ℕ) (hw : ∀ i, w i ≠ 0) (N : ℕ)
    (I : Ideal (MvPolynomial σ K)) (hI : I ≤ minimumWeightIdeal w 2)
    (q : HomogeneousSource (K := K) w N →ₗ[K] V)
    (hq : Function.Surjective q) :
    (∑ d : Fin (maxCost N + 1),
        Module.finrank K
          (FiniteCostFiltration.CostAssociated
            (K := K) (Source := ModuleCat.of K V)
            (filtration (K := K) w N I hI q hq) d.1)) =
      Module.finrank K V := by
  letI : FiniteDimensional K V := target_finiteDimensional w hw N q hq
  exact (filtration (K := K) w N I hI q hq).sum_associated_finrank

end

end VOA.CasimirCostFiltration

section AxiomAudit
open VOA.CasimirCostFiltration
#print axioms polynomialCostPiece_eq_bot_of_lt
#print axioms quotientCostPiece_succ_max_eq_bot
#print axioms polynomialCostToAssociated_surjective
#print axioms sum_associated_finrank
end AxiomAudit
