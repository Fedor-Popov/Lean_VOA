/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2DeformationRepresentation
import VOA.Core.DeformationIteration

/-!
# Reconstruction for regular graded affine deformations

The cyclic image of universal vacuum evaluation has already been proved to
exclude the pure tangent vacuum. The iterate identity supplies closure under
all state products, not just current modes. Degree intertwining supplies closure
under homogeneous projections. These properties let the existing reconstruction
map produce a grade-preserving coboundary for every regular graded deformation.
Normalized pole vanishing is a separate remaining requirement for full rigidity.
-/
namespace VOA.LQ43
open AffineVOA AffineVOA.Inst AffineLie Deform Deform.Reconstruction
local notation "kk" => (-4 / 3 : ℂ)
local notation "I" => QuotVOA.maxGradedIdeal voaSl2Adm

/-- Acting by a pure current state agrees with the block current operator.
The tangent coordinate is the sum of the original action and its correction. -/
private theorem product_pure (D : FirstOrderDeformation L43)
    (a : WakModule kk ⧸ I) (x : (WakModule kk ⧸ I) × (WakModule kk ⧸ I)) (n : ℤ) :
    product D (a, 0) n x = liftedMode D a n x := by
  apply Prod.ext <;> simp [product, liftedMode] <;> abel

/-- Every current mode preserves the cyclic evaluation image, by the universal
intertwining identity. This includes positive as well as creation modes. -/
theorem L43_eval_current_preserves (D : FirstOrderDeformation L43)
    (hD : D.IsGraded) (hreg : D.Regular) (a : Fin 3) :
    ((I).mkQ (currentState kk a), 0) ∈
      modePreservers D (LinearMap.range (L43_deformationEval D hD hreg)) := by
  intro x hx n
  obtain ⟨v, rfl⟩ := hx
  rw [product_pure, ← L43_deformationEval_J D hD hreg]
  exact LinearMap.mem_range_self _ _

/-- All states in the cyclic image preserve that image under every deformed
mode. The iterate formula propagates preservation along current creation words. -/
theorem L43_eval_modeClosed (D : FirstOrderDeformation L43)
    (hD : D.IsGraded) (hreg : D.Regular) :
    ModeClosed D (LinearMap.range (L43_deformationEval D hD hreg)) := by
  let F := L43_deformationEval D hD hreg
  let S := LinearMap.range F
  have hw (l : List (Fin 3 × ℕ)) : F (wordStateA kk l) ∈ modePreservers D S := by
    induction l with
    | nil =>
      change L43_deformationEval D hD hreg (vacuumA kk) ∈ _
      rw [L43_deformationEval_vacuum]
      exact vacuum_mem_modePreservers D S
    | cons an l ih =>
      change L43_deformationEval D hD hreg (wordStateA kk (an :: l)) ∈ _
      rw [wordStateA_cons, L43_deformationEval_J, ← product_pure]
      exact modePreservers_product D S (L43_eval_current_preserves D hD hreg an.1) ih _
  have hpre : (modePreservers D S).comap F = ⊤ := by
    apply top_unique
    rw [← wordStateA_span kk]
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
theorem L43_eval_mem_grading (D : FirstOrderDeformation L43)
    (hD : D.IsGraded) (hreg : D.Regular) {n : ℤ} {v : WakModule kk}
    (hv : v ∈ gradingZA kk n) :
    (L43_deformationEval D hD hreg v).1 ∈ L43.grading n ∧
      (L43_deformationEval D hD hreg v).2 ∈ L43.grading n := by
  rw [gradingZA_def, Module.End.mem_eigenspace_iff] at hv
  have h := L43_deformationEval_degree D hD hreg v
  rw [hv, map_smul] at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [grading_eq_L_zero_eigenspace, Module.End.mem_eigenspace_iff]
  constructor
  · simpa [liftedDegree_apply] using congrArg Neg.neg h1.symm
  · simpa [liftedDegree_apply] using congrArg Neg.neg h2.symm

/-- A projection to a different weight kills an already homogeneous state. -/
private theorem gradePart_ne {n k : ℤ} {v : WakModule kk ⧸ I}
    (hkn : k ≠ n) (hv : v ∈ L43.grading k) : gradePart L43 n v = 0 := by
  letI : DirectSum.Decomposition L43.grading := L43.isInternal.chooseDecomposition L43.grading
  unfold gradePart
  change (L43.gradedProj n v : WakModule kk ⧸ I) = 0
  rw [L43.gradedProj_of_mem_ne hkn hv]
  rfl

/-- Homogeneous projection in both coordinates preserves the cyclic image.
Decompose a universal preimage into its finitely many weights and project each. -/
theorem L43_eval_gradeClosed (D : FirstOrderDeformation L43)
    (hD : D.IsGraded) (hreg : D.Regular) :
    GradeClosed L43 (LinearMap.range (L43_deformationEval D hD hreg)) := by
  let F := L43_deformationEval D hD hreg
  intro x hx n
  obtain ⟨v, rfl⟩ := hx
  let P := (gradePart L43 n).prodMap (gradePart L43 n)
  change P (F v) ∈ LinearMap.range F
  have hv : v ∈ ⨆ k, gradingZA kk k := by rw [gradingZA_iSup_eq_top]; trivial
  refine Submodule.iSup_induction (gradingZA kk)
    (motive := fun v => P (F v) ∈ LinearMap.range F) hv ?_ ?_ ?_
  · intro k v hv
    obtain ⟨h1, h2⟩ := L43_eval_mem_grading D hD hreg hv
    change (gradePart L43 n (F v).1, gradePart L43 n (F v).2) ∈ LinearMap.range F
    by_cases hkn : k = n
    · subst k
      rw [gradePart_of_mem h1, gradePart_of_mem h2]
      exact LinearMap.mem_range_self F v
    · rw [gradePart_ne hkn h1, gradePart_ne hkn h2]
      exact (LinearMap.range F).zero_mem
  · simpa only [map_zero] using (LinearMap.range F).zero_mem
  · intro x y hx hy
    rw [map_add, map_add]
    exact (LinearMap.range F).add_mem hx hy

/-- Every ordinary simple-quotient state is the constant coefficient of a
cyclic lifted state, because evaluation reduces to the original quotient map. -/
theorem L43_eval_reduction_surjective (D : FirstOrderDeformation L43)
    (hD : D.IsGraded) (hreg : D.Regular) :
    Function.Surjective (reduction (LinearMap.range (L43_deformationEval D hD hreg))) := by
  intro x
  obtain ⟨v, rfl⟩ := (I).mkQ_surjective x
  refine ⟨⟨L43_deformationEval D hD hreg v, LinearMap.mem_range_self _ _⟩, ?_⟩
  exact L43_deformationEval_fst D hD hreg v

/-- Every regular graded deformation of the simple affine sl₂ algebra at level
−4/3 is a grade-preserving, vacuum-preserving change of coordinates. The proof
constructs the coboundary from the cyclic image; no separation or reconstruction
hypothesis remains. This does not yet normalize arbitrary deformations to regular ones. -/
theorem L43_regular_isTrivial (D : FirstOrderDeformation L43)
    (hD : D.IsGraded) (hreg : D.Regular) : D.IsTrivial := by
  apply isTrivial_of_closed_lift D (LinearMap.range (L43_deformationEval D hD hreg))
    L43_isSimple (L43_eval_modeClosed D hD hreg) (L43_eval_reduction_surjective D hD hreg)
    (L43_deformationEval_separation D hD hreg)
  · rw [← L43_deformationEval_vacuum D hD hreg]
    exact LinearMap.mem_range_self _ _
  · exact L43_eval_gradeClosed D hD hreg

/-- The regular-deformation reconstruction input for L43 is discharged.
The only remaining input in the normalized rigidity assembly is pole vanishing. -/
theorem L43_regularImpliesTrivialGraded : RegularImpliesTrivialGraded L43 :=
  L43_regular_isTrivial

/-- The affine rigidity assembly with its remaining pole obstruction exposed.
This conditional result is not a proof that the normalized pole actually vanishes. -/
theorem L43_isRigidGraded_of_normalisedPoleVanishes (h2 : NormalisedPoleVanishes L43) :
    Deform.IsRigidGraded L43 :=
  L43_isRigidGraded_of_deformation_inputs L43_regularImpliesTrivialGraded h2

end VOA.LQ43
