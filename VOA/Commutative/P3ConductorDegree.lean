/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.P3ResidualWindowPreservation
import Mathlib.Data.Sym.Card
import Mathlib.Data.Sym.Sym2.Order

/-!
# The explicit degree of the boundary `p = 3` conductor

The conductor contains one root factor for each `S` particle, two factors for every unordered
pair of `S` particles, and one factor for every current--`S` pair.  This file turns that geometric
description into an exact degree formula.
-/

namespace VOA.P3ResidualWindowPreservation

open VOA.MultispeciesParticlePolynomial
open VOA.P3RestrictedDualCommonFactor
open VOA.CollisionCommonFactors

noncomputable section

/-- Choosing the increasing orientation of a two-element set identifies increasing pairs with
off-diagonal points of the symmetric square. -/
def increasingPairEquivSym2OffDiag (I : Type*) [LinearOrder I] :
    IncreasingPair I ≃ {z : Sym2 I // ¬z.IsDiag} where
  toFun ij := ⟨s(ij.1.1, ij.1.2), by simpa using ij.2.ne⟩
  invFun z :=
    ⟨(Sym2.sortEquiv z.1).1,
      lt_of_le_of_ne (Sym2.sortEquiv z.1).2 (by
        intro h
        apply z.2
        have hz :
            z.1 = (Sym2.sortEquiv (α := I)).symm (Sym2.sortEquiv z.1) :=
          ((Sym2.sortEquiv (α := I)).symm_apply_apply z.1).symm
        rw [hz]
        simpa [Sym2.sortEquiv, h])⟩
  left_inv ij := by
    apply Subtype.ext
    apply Prod.ext
    · simp [ij.2.le]
    · simp [ij.2.le]
  right_inv z := by
    apply Subtype.ext
    exact (Sym2.sortEquiv (α := I)).symm_apply_apply z.1

/-- The increasing pairs in `Fin d` are counted by the binomial coefficient `d choose 2`. -/
theorem card_increasingPair_fin (d : ℕ) :
    Fintype.card (IncreasingPair (Fin d)) = d.choose 2 := by
  rw [Fintype.card_congr (increasingPairEquivSym2OffDiag (Fin d))]
  simpa using (Sym2.card_subtype_not_diag (α := Fin d))

/-- The collision contribution is twice the number of same-`S` pairs plus the number of
current--`S` pairs. -/
theorem sum_conductorCollisionMultiplicity (a b c d : ℕ) :
    (∑ i : ConductorCollisionIndex a b c d, conductorCollisionMultiplicity i) =
      2 * Fintype.card (IncreasingPair (Fin d)) + (a + b + c) * d := by
  classical
  simp [ConductorCollisionIndex, conductorCollisionMultiplicity,
    BoundaryCurrentLabel]
  ring

/-- The complete conductor degree before evaluating the cardinality of the unordered-pair
index. -/
theorem p3ConductorWeightedDegree_eq_card (a b c d : ℕ) :
    p3ConductorWeightedDegree a b c d =
      d + 2 * Fintype.card (IncreasingPair (Fin d)) + (a + b + c) * d := by
  rw [p3ConductorWeightedDegree, weight_boundarySpeciesShift,
    sum_conductorCollisionMultiplicity]
  omega

/-- The conductor has the clean total degree `d N`, where `d` is the number of `S` particles
and `N = a + b + c + d` is the total number of particles. -/
theorem p3ConductorWeightedDegree_eq (a b c d : ℕ) :
    p3ConductorWeightedDegree a b c d = d * (a + b + c + d) := by
  rw [p3ConductorWeightedDegree_eq_card, card_increasingPair_fin,
    Nat.choose_two_right]
  rw [Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self d)]
  cases d with
  | zero => simp
  | succ d =>
      simp
      ring

end

end VOA.P3ResidualWindowPreservation
