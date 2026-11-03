/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.ConcreteHodgeLayers
import VOA.Examples.AffineSl2VacuumChevalleyGram
import VOA.Examples.AffineSl2BelowCriticalRigidity
import VOA.Examples.AffineSl2UniversalGram

/-!
# Symmetry of the affine `sl2` invariant forms

Discharges the Gram-reflexivity hypothesis `GramRefl` of `ConcreteHodgeLayers` for the two affine
factors of the Lee–Yang complex.

* `universalForm_isSymmetric`: the normalized form on `V^k(sl2)` is symmetric, for every
  noncritical `k`. Proof: the Chevalley-twisted form is symmetric
  (`vacuumChevalley_form_symm`), the form is Chevalley-invariant
  (`universalForm_vacuumChevalley`), and the Chevalley map is an involution, so
  `B(x,y) = B(θθx, y) = B(θy, θx) = B(y, x)`.
* `simpleForm_mkQ`: the simple form pulls back to the universal one along the quotient map
  (checked on the PBW basis, `universalWord_pairing_mkQ`).
* `simpleForm_isSymmetric`, and the `GramRefl` corollaries.

Everything is proved outright.
-/

namespace VOA.ConcreteHodge

open VOA.AffineSl2GeneralRigidity VOA.AffineSl2BelowCritical VOA.VertexOperatorAlgebra
open AffineVOA AffineVOA.HighestModule
open AffineSl2PBWWakimotoReduction

variable (k : ℂ) (hk : k + 2 ≠ 0)

/-- **The universal affine `sl2` form is symmetric.** -/
theorem universalForm_isSymmetric : (universalForm k hk).IsSymmetric := by
  intro x y
  have hinv := vacuumChevalley_involutive k hk
  calc (universalForm k hk).form x y
      = (universalForm k hk).form (vacuumChevalley k (vacuumChevalley k x)) y := by
        rw [hinv x]
    _ = (universalForm k hk).form (vacuumChevalley k y) (vacuumChevalley k x) :=
        vacuumChevalley_form_symm k hk _ y
    _ = (universalForm k hk).form y x := universalForm_vacuumChevalley hk y x

/-- A PBW basis vector is a current word applied to the vacuum. -/
theorem currentPBWBasis_eq_word (mu : CurrentIndex) :
    currentPBWBasis k hk mu = NormalOrdering.currentWord (J k)
      ((orderedPBWColorWord mu).map (fun an => (an.1, -(an.2 : ℤ) - 1)))
      (universal k hk).vacuum := by
  rw [currentPBWBasis_apply]
  generalize orderedPBWColorWord mu = w
  change wordStateA k w =
    NormalOrdering.currentWord (J k) (w.map (fun an => (an.1, -(an.2 : ℤ) - 1))) (vacuumA k)
  induction w with
  | nil => rfl
  | cons an w ih =>
      simp only [List.map_cons, NormalOrdering.currentWord, Module.End.mul_apply,
        wordStateA_cons, ih]

/-- **The simple form pulls back to the universal form** along the quotient map. -/
theorem simpleForm_mkQ (x y : WakModule k) :
    (simpleForm k hk).form ((QuotVOA.maxGradedIdeal (universal k hk)).mkQ x)
      ((QuotVOA.maxGradedIdeal (universal k hk)).mkQ y) = (universalForm k hk).form x y := by
  let I := QuotVOA.maxGradedIdeal (universal k hk)
  have h : ((simpleForm k hk).form.compl₁₂ I.mkQ I.mkQ).flip y =
      (universalForm k hk).form.flip y := by
    apply (currentPBWBasis k hk).ext
    intro mu
    change (simpleForm k hk).form (I.mkQ (currentPBWBasis k hk mu)) (I.mkQ y) =
      (universalForm k hk).form (currentPBWBasis k hk mu) y
    rw [currentPBWBasis_eq_word, universalWord_pairing_mkQ, universalWord_mkQ]
    rfl
  exact LinearMap.congr_fun h x

/-- **The simple affine `sl2` form is symmetric.** -/
theorem simpleForm_isSymmetric : (simpleForm k hk).IsSymmetric := by
  intro x y
  obtain ⟨x, rfl⟩ := (QuotVOA.maxGradedIdeal (universal k hk)).mkQ_surjective x
  obtain ⟨y, rfl⟩ := (QuotVOA.maxGradedIdeal (universal k hk)).mkQ_surjective y
  rw [simpleForm_mkQ, simpleForm_mkQ, universalForm_isSymmetric]

theorem gramRefl_universalForm : GramRefl (universalForm k hk) :=
  gramRefl_of_isSymmetric _ (universalForm_isSymmetric k hk)

theorem gramRefl_simpleForm : GramRefl (simpleForm k hk) :=
  gramRefl_of_isSymmetric _ (simpleForm_isSymmetric k hk)

end VOA.ConcreteHodge
