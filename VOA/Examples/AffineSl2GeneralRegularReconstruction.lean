/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2GeneralDeformationEvaluation
import VOA.Core.DeformationIteration

/-!
# Fixed-level reconstruction at arbitrary nonzero noncritical affine level

The actual evaluation image is mode closed, grade closed, surjective on
reduction and separated from the tangent vacuum. Thus every regular graded
deformation is trivial. Pole vanishing for arbitrary deformations remains a
separate mathematical problem; it is not assumed to prove reconstruction.
-/
namespace VOA.AffineSl2GeneralRigidity
open AffineVOA AffineVOA.Inst AffineLie Deform Deform.Reconstruction LQ43
variable (k : ℂ) (hk : k + 2 ≠ 0) (hk0 : k ≠ 0)
local notation "I" => QuotVOA.maxGradedIdeal (universal k hk)

/-- Acting by a pure current state agrees with the block current operator.
The tangent coordinate is the sum of the original action and its correction. -/
private theorem product_pure (D : FirstOrderDeformation (simple k hk))
    (a : WakModule k ⧸ I) (x : (WakModule k ⧸ I) × (WakModule k ⧸ I)) (n : ℤ) :
    product D (a, 0) n x = liftedMode D a n x := by
  apply Prod.ext <;> simp [product, liftedMode] <;> abel

/-- Every current mode preserves the cyclic evaluation image, by the universal
intertwining identity. This includes positive as well as creation modes. -/
theorem simple_eval_current_preserves (D : FirstOrderDeformation (simple k hk))
    (hD : D.IsGraded) (hreg : D.Regular) (a : Fin 3) :
    ((I).mkQ (currentState k a), 0) ∈
      modePreservers D (LinearMap.range ((simple_deformationEval k hk hk0) D hD hreg)) := by
  intro x hx n
  obtain ⟨v, rfl⟩ := hx
  rw [(product_pure k hk), ← (simple_deformationEval_J k hk hk0) D hD hreg]
  exact LinearMap.mem_range_self _ _

/-- All states in the cyclic image preserve that image under every deformed
mode. The iterate formula propagates preservation along current creation words. -/
theorem simple_eval_modeClosed (D : FirstOrderDeformation (simple k hk))
    (hD : D.IsGraded) (hreg : D.Regular) :
    ModeClosed D (LinearMap.range ((simple_deformationEval k hk hk0) D hD hreg)) := by
  let F := (simple_deformationEval k hk hk0) D hD hreg
  let S := LinearMap.range F
  have hw (l : List (Fin 3 × ℕ)) : F (wordStateA k l) ∈ modePreservers D S := by
    induction l with
    | nil =>
      change (simple_deformationEval k hk hk0) D hD hreg (vacuumA k) ∈ _
      rw [(simple_deformationEval_vacuum k hk hk0)]
      exact vacuum_mem_modePreservers D S
    | cons an l ih =>
      change (simple_deformationEval k hk hk0) D hD hreg (wordStateA k (an :: l)) ∈ _
      rw [wordStateA_cons, (simple_deformationEval_J k hk hk0), ← (product_pure k hk)]
      exact modePreservers_product D S ((simple_eval_current_preserves k hk hk0) D hD hreg an.1) ih _
  have hpre : (modePreservers D S).comap F = ⊤ := by
    apply top_unique
    rw [← wordStateA_span k]
    apply Submodule.span_le.mpr
    rintro _ ⟨l, rfl⟩
    exact hw l
  intro x hx y hy n
  obtain ⟨v, rfl⟩ := hx
  have hv : F v ∈ modePreservers D S := by
    change v ∈ (modePreservers D S).comap F
    rw [hpre]
    trivial
  exact hv y hy n

/-- A homogeneous universal state evaluates to two states of the same weight.
This follows from degree intertwining and the exact eigenspace description of grading. -/
theorem simple_eval_mem_grading (D : FirstOrderDeformation (simple k hk))
    (hD : D.IsGraded) (hreg : D.Regular) {n : ℤ} {v : WakModule k}
    (hv : v ∈ gradingZA k n) :
    ((simple_deformationEval k hk hk0) D hD hreg v).1 ∈ (simple k hk).grading n ∧
      ((simple_deformationEval k hk hk0) D hD hreg v).2 ∈ (simple k hk).grading n := by
  rw [gradingZA_def, Module.End.mem_eigenspace_iff] at hv
  have h := (simple_deformationEval_degree k hk hk0) D hD hreg v
  rw [hv, map_smul] at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [grading_eq_L_zero_eigenspace, Module.End.mem_eigenspace_iff]
  constructor
  · simpa [liftedDegree_apply] using congrArg Neg.neg h1.symm
  · simpa [liftedDegree_apply] using congrArg Neg.neg h2.symm

/-- A projection to a different weight kills an already homogeneous state. -/
private theorem gradePart_ne {n j : ℤ} {v : WakModule k ⧸ I}
    (hkn : j ≠ n) (hv : v ∈ (simple k hk).grading j) : gradePart (simple k hk) n v = 0 := by
  letI : DirectSum.Decomposition (simple k hk).grading := (simple k hk).isInternal.chooseDecomposition (simple k hk).grading
  unfold gradePart
  change ((simple k hk).gradedProj n v : WakModule k ⧸ I) = 0
  rw [(simple k hk).gradedProj_of_mem_ne hkn hv]
  rfl

/-- Homogeneous projection in both coordinates preserves the cyclic image.
Decompose a universal preimage into its finitely many weights and project each. -/
theorem simple_eval_gradeClosed (D : FirstOrderDeformation (simple k hk))
    (hD : D.IsGraded) (hreg : D.Regular) :
    GradeClosed (simple k hk) (LinearMap.range ((simple_deformationEval k hk hk0) D hD hreg)) := by
  let F := (simple_deformationEval k hk hk0) D hD hreg
  intro x hx n
  obtain ⟨v, rfl⟩ := hx
  let P := (gradePart (simple k hk) n).prodMap (gradePart (simple k hk) n)
  change P (F v) ∈ LinearMap.range F
  have hv : v ∈ ⨆ j, gradingZA k j := by rw [gradingZA_iSup_eq_top]; trivial
  refine Submodule.iSup_induction (gradingZA k)
    (motive := fun v => P (F v) ∈ LinearMap.range F) hv ?_ ?_ ?_
  · intro j v hv
    obtain ⟨h1, h2⟩ := (simple_eval_mem_grading k hk hk0) D hD hreg hv
    change (gradePart (simple k hk) n (F v).1, gradePart (simple k hk) n (F v).2) ∈ LinearMap.range F
    by_cases hkn : j = n
    · subst j
      rw [gradePart_of_mem h1, gradePart_of_mem h2]
      exact LinearMap.mem_range_self F v
    · rw [(gradePart_ne k hk) hkn h1, (gradePart_ne k hk) hkn h2]
      exact (LinearMap.range F).zero_mem
  · simpa only [map_zero] using (LinearMap.range F).zero_mem
  · intro x y hx hy
    rw [map_add, map_add]
    exact (LinearMap.range F).add_mem hx hy

/-- Every ordinary simple-quotient state is the constant coefficient of a
cyclic lifted state, because evaluation reduces to the original quotient map. -/
theorem simple_eval_reduction_surjective (D : FirstOrderDeformation (simple k hk))
    (hD : D.IsGraded) (hreg : D.Regular) :
    Function.Surjective (reduction (LinearMap.range ((simple_deformationEval k hk hk0) D hD hreg))) := by
  intro x
  obtain ⟨v, rfl⟩ := (I).mkQ_surjective x
  refine ⟨⟨(simple_deformationEval k hk hk0) D hD hreg v, LinearMap.mem_range_self _ _⟩, ?_⟩
  exact (simple_deformationEval_fst k hk hk0) D hD hreg v

include hk0 in
/-- Every regular graded deformation of the simple affine sl₂ algebra at every nonzero noncritical level is a grade-preserving, vacuum-preserving change of coordinates. The proof
constructs the coboundary from the cyclic image; no separation or reconstruction
hypothesis remains. This does not yet normalize arbitrary deformations to regular ones. -/
theorem simple_regular_isTrivial (D : FirstOrderDeformation (simple k hk))
    (hD : D.IsGraded) (hreg : D.Regular) : D.IsTrivial := by
  apply isTrivial_of_closed_lift D (LinearMap.range ((simple_deformationEval k hk hk0) D hD hreg))
    (simple_isSimple k hk) ((simple_eval_modeClosed k hk hk0) D hD hreg) ((simple_eval_reduction_surjective k hk hk0) D hD hreg)
    ((simple_deformationEval_separation k hk hk0) D hD hreg)
  · rw [← (simple_deformationEval_vacuum k hk hk0) D hD hreg]
    exact LinearMap.mem_range_self _ _
  · exact (simple_eval_gradeClosed k hk hk0) D hD hreg

include hk0 in
/-- The regular-deformation reconstruction input for (simple k hk) is discharged.
The only remaining input in the normalized rigidity assembly is pole vanishing. -/
theorem simple_regularImpliesTrivialGraded : RegularImpliesTrivialGraded (simple k hk) :=
  (simple_regular_isTrivial k hk hk0)

end VOA.AffineSl2GeneralRigidity
