/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Commutative.FullColoredSymmetricHilbert
import VOA.Commutative.GordonFullQuotient

/-! # Exact Hilbert coefficients of the full Gordon divided target -/
namespace VOA.GordonFullQuotient
open MvPolynomial GordonFiltration GordonFullDivisor GordonFullSymmetry ColoredSymmetricHilbert
noncomputable section
universe u
variable {K : Type*} [Field K] [CharZero K]
variable {ρ τ α β γ : Type u} [Fintype ρ] [Fintype τ] [Fintype α] [Fintype β] [Fintype γ]
variable [DecidableEq ρ] [LinearOrder τ] [LinearOrder α] [LinearOrder β] [LinearOrder γ]

/-- Finite cluster colors, including the harmless empty-block color. -/
def clusterColor (f : ρ → τ) (j : τ) : ULift.{u} (Fin (Fintype.card ρ + 1)) :=
  ⟨⟨blockSize f j, Nat.lt_succ_of_le (Finset.card_le_card (Finset.filter_subset _ _))⟩⟩

omit [Fintype τ] [DecidableEq ρ] in
theorem clusterColor_eq_iff (f : ρ → τ) (i j : τ) :
    clusterColor f i = clusterColor f j ↔ blockSize f i = blockSize f j := by
  simp [clusterColor, ULift.ext_iff, Fin.ext_iff]

omit [CharZero K] [Fintype α] [Fintype β] [Fintype γ]
  [LinearOrder α] [LinearOrder β] [LinearOrder γ] in
theorem fullInvariantPiece_eq_actionPiece (f : ρ → τ) (d : ℕ) :
    fullInvariantPiece (K := K) (α := α) (β := β) (γ := γ) f d =
      actionPiece (K := K) (fullColorAction (α := α) (β := β) (γ := γ) (clusterColor f)) d := by
  ext p
  change ((∀ e : Equiv.Perm τ, (∀ j, blockSize f (e j) = blockSize f j) →
      ∀ a : Equiv.Perm α, ∀ b : Equiv.Perm β, ∀ c : Equiv.Perm γ,
        rename (fullPerm e a b c) p = p) ∧ p.IsHomogeneous d) ↔ _
  constructor
  · intro hp
    refine ⟨?_, hp.2⟩
    intro h
    exact hp.1 h.1.val (fun j => (clusterColor_eq_iff f _ _).mp (h.1.property j))
      h.2.1 h.2.2.1 h.2.2.2
  · intro hp
    refine ⟨?_, hp.2⟩
    intro e he a b c
    exact hp.1 (⟨e, fun j => (clusterColor_eq_iff f _ _).mpr (he j)⟩, a, b, c)

/-- The exact, source-used Gordon invariant target has the predicted
cluster multiplicity and residual reciprocal-factorial Hilbert series. -/
theorem fullInvariantPiece_finrank_eq_coeff (f : ρ → τ) (d : ℕ) :
    (Module.finrank K (fullInvariantPiece (K := K) (α := α) (β := β) (γ := γ) f d) : ℚ) =
      PowerSeries.coeff d ((∏ i : Fin (Fintype.card ρ + 1),
        (QSeries.reciprocalQFactorial (Nat.card {j // blockSize f j = i.val}) : PowerSeries ℚ)) *
        QSeries.reciprocalQFactorial (Fintype.card α) *
        QSeries.reciprocalQFactorial (Fintype.card β) *
        QSeries.reciprocalQFactorial (Fintype.card γ)) := by
  classical
  rw [fullInvariantPiece_eq_actionPiece, fullColorPiece_finrank_eq_coeff]
  congr 4
  apply Fintype.prod_equiv (Equiv.ulift : ULift.{u} (Fin (Fintype.card ρ + 1)) ≃ _)
  intro i
  congr 1
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun j => by
    simp [clusterColor, ULift.ext_iff, Fin.ext_iff])

end
end VOA.GordonFullQuotient
