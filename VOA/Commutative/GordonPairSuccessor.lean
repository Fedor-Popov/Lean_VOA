/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.GordonPairIndexing

/-! # The next canonical pair supplies the actual residual collision kernel -/

namespace VOA.GordonPairSuccessor
open MvPolynomial VOA.GordonPairIndexing VOA.GordonPairedEvaluation
open VOA.GordonPairedRelations VOA.GordonCommonFactors
noncomputable section

/-- The first residual particle is the next canonical pair member. -/
def firstResidual (a R : ℕ) (ha : R < a) : ResidualIndex a R := ⟨⟨R, ha⟩, le_rfl⟩

def nextIndex (a b c R : ℕ) (ha : R < a) (hb : R < b) :=
  collisionIndex
    (eLabel (ρ := Fin R) (γ := Fin c) (firstResidual a R ha))
    (fLabel (α := ResidualIndex a R) (firstResidual b R hb))
    (by simp [eLabel, fLabel]) ∘ pairedIndex a b c R ha.le hb.le

/-- The successor merge is invisible after identifying the next residual pair. -/
theorem nextIndex_merge (a b c R : ℕ) (ha : R < a) (hb : R < b) :
    nextIndex a b c R ha hb ∘ mergeIndex a b c (R + 1) ha = nextIndex a b c R ha hb := by
  funext i
  rcases i with i | (i | i)
  · rfl
  · by_cases hi : i.val < R
    · simp [nextIndex, mergeIndex, pairedIndex, sourceEquiv, splitFin,
        pairIndex, hi, show i.val < R + 1 by omega]
    · by_cases hir : i.val = R
      · have hit : i = ⟨R, hb⟩ := Fin.ext hir
        subst i
        simp [nextIndex, mergeIndex, pairedIndex, sourceEquiv, splitFin,
          pairIndex, collisionIndex, eLabel, fLabel, firstResidual]
      · simp [mergeIndex, show ¬ i.val < R + 1 by omega]
  · rfl

variable {K : Type*} [Field K]

/-- Vanishing of the actual successor evaluation forces the next-pair collision to vanish. -/
theorem nextPairEval_eq_zero_of_successor (a b c R : ℕ) (ha : R < a) (hb : R < b)
    (F : MvPolynomial (Original a b c) K)
    (hF : rename (pairedIndex a b c (R + 1) ha hb) F = 0) :
    nextPairEval (firstResidual a R ha) (firstResidual b R hb)
      (rename (sourceEquiv a b c R ha.le hb.le) F) = 0 := by
  have hz := congrArg (rename (representative a b c (R + 1) ha)) hF
  simp only [rename_rename, representative_pairedIndex, map_zero] at hz
  have hz' := congrArg (rename (nextIndex a b c R ha hb)) hz
  simp only [rename_rename, nextIndex_merge, map_zero] at hz'
  simpa only [nextPairEval, AlgHom.comp_apply, collisionMap, pairEval,
    rename_rename, nextIndex, pairedIndex, Function.comp_assoc] using hz'

end
end VOA.GordonPairSuccessor
