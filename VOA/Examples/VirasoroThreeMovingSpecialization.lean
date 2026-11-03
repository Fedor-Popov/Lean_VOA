/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroThreeMovingSource

/-!
# Specialization and finite coordinates of the moving q=3 source

The new explicit recursion agrees with the already constructed actual
minimal-model source. Fixed-level PBW coordinates express the entire family
using finitely many fixed words, as needed for ordinary differentiation.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule

/-- At the minimal parameter, every earlier moving state is the
actual coefficient constructed earlier, by triangular uniqueness. -/
theorem threeMovingState_at_minimal (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3)
    (c : ℂ) (r : ℕ) (hr : r<(p-1)*2) :
    threeMovingState c ((3:ℂ)/(p:ℂ)) r=(minimalThreeChargeKernel p hp hcop c).val r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases hz : r=0
    · subst r
      simp [threeMovingState,minimalThreeChargeKernel_zero]
    · have hd := minimalThree_state_diagonal_ne_zero p hp hcop r (by omega) hr
      have hS := threeMovingState_equation c ((3:ℂ)/(p:ℂ)) r (by omega) hd
      have hK := minimalThreeChargeKernel_below p hp hcop c r hr
      rw [wardSourceAt_three_state_recursion,minimalThree_incoming_eq_field p hp] at hK
      unfold threeMovingSource at hS
      have hi (j : Fin r) := ih j j.isLt (by omega)
      simp only [hi] at hS
      apply smul_right_injective _ hd
      exact add_right_cancel (hS.trans hK.symm)

/-- The terminal diagonal vanishes at precisely the actual minimal level
needed here; no inverse of this scalar is taken. -/
theorem threeMovingDiagonal_minimal_terminal (p : ℕ) (hp : 2≤p) :
    threeMovingDiagonal ((3:ℂ)/(p:ℂ)) ((p-1)*2)=0 := by
  rw [threeMovingDiagonal,threeStateDiagonal_vacuum_factor _
    (minimal_three_parameter_ne_zero p (by omega))]
  have ht := minimalThree_terminal_index p hp
  have he : (((p-1)*2:ℕ):ℂ)-3*vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))-1=0 := by
    linear_combination -ht
  rw [he,mul_zero]

/-- The undivided moving source agrees with the genuine terminal source
at the minimal parameter, at every actual central charge. -/
theorem threeMovingSource_at_minimal (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) (c : ℂ) :
    threeMovingSource c ((3:ℂ)/(p:ℂ)) ((p-1)*2)=minimalThreeChargeSource p hp hcop c := by
  rw [minimalThreeChargeSource,wardSourceAt_three_state_recursion,
    minimalThree_incoming_eq_field p hp]
  change _=threeMovingDiagonal ((3:ℂ)/(p:ℂ)) ((p-1)*2) • _+_
  rw [threeMovingDiagonal_minimal_terminal p hp,zero_smul,zero_add]
  unfold threeMovingSource threeMovingCoefficient
  apply Finset.sum_congr rfl
  intro j hj
  rw [threeMovingState_at_minimal p hp hcop c j j.isLt]

/-- Equality holds for the fixed literal word expression as well, so the
moving family passes through exactly the source used by the norm polynomial. -/
theorem threeMovingExpression_at_minimal (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) :
    threeMovingExpression ((3:ℂ)/(p:ℂ)) ((p-1)*2)=minimalThreeExpression p hp hcop := by
  rw [threeMovingExpression,threeMovingSource_at_minimal,minimalThreeExpression]

/-- Full PBW coordinate at a fixed level, viewed as a scalar linear map
on the whole charge-zero Verma space. This avoids any variable choice of support. -/
noncomputable def threeLevelCoordinate (r : ℕ) (w : VermaPartitions r) : Verma 0 0 →ₗ[ℂ] ℂ :=
  ((vermaSortedBasis 0 0).coord ⟨w.val,w.property.1⟩)

/-- Reconstructing only the coordinates of one level defines a fixed
linear projection onto its finite PBW word span. -/
noncomputable def threeLevelReconstruct (r : ℕ) : Verma 0 0 →ₗ[ℂ] Verma 0 0 :=
  ∑ w : VermaPartitions r, (threeLevelCoordinate r w).smulRight (negWord 0 0 w.val)

/-- The finite reconstruction fixes every PBW word of its indicated level. -/
theorem threeLevelReconstruct_word (r : ℕ) (w : VermaPartitions r) :
    threeLevelReconstruct r (negWord 0 0 w.val)=negWord 0 0 w.val := by
  classical
  simp only [threeLevelReconstruct,LinearMap.sum_apply,LinearMap.smulRight_apply,
    threeLevelCoordinate,Module.Basis.coord_apply]
  have hb : negWord 0 0 w.val=(vermaSortedBasis 0 0) ⟨w.val,w.property.1⟩ :=
    (vermaSortedBasis_apply 0 0 ⟨w.val,w.property.1⟩).symm
  conv_lhs => arg 2; intro u; rw [hb,Module.Basis.repr_self]
  have he (u : VermaPartitions r) :
      (⟨w.val,w.property.1⟩ : {w : List ℕ // SortedWord w})=⟨u.val,u.property.1⟩ ↔ w=u := by
    constructor
    · intro h
      exact Subtype.ext (congrArg (fun z : {w : List ℕ // SortedWord w} => z.val) h)
    · rintro rfl
      rfl
  simp only [Finsupp.single_apply,he,ite_smul,one_smul,zero_smul]
  simp

/-- Every state of a fixed actual level has a finite expansion in that
level's fixed words and full PBW coordinate functionals. -/
theorem threeLevelReconstruct_eq (r : ℕ) (v : Verma 0 0) (hv : v∈sortedSpan 0 0 r) :
    threeLevelReconstruct r v=v := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w,hw,he,rfl⟩ := hx
    exact threeLevelReconstruct_word r ⟨w,hw,he⟩
  | zero => simp
  | add x y hx hy h1 h2 => simp [map_add,h1,h2]
  | smul z x hx hi => simp [map_smul,hi]

/-- The moving source is a finite family of fixed literal word expressions
with explicitly differentiable scalar coordinates. -/
theorem threeMovingExpression_finite (t : ℂ) (r : ℕ) :
    threeMovingExpression t r=∑ w : VermaPartitions r,
      threeLevelCoordinate r w (threeMovingSource 0 t r) •
        chargeWordExpression (negWord 0 0 w.val) := by
  have he := congrArg chargeWordExpression
    (threeLevelReconstruct_eq r (threeMovingSource 0 t r) (threeMovingSource_level 0 t r))
  simpa only [threeLevelReconstruct,LinearMap.sum_apply,LinearMap.smulRight_apply,
    map_sum,map_smul,threeMovingExpression] using he.symm

/-- The actual moving norm is differentiable at the minimal parameter,
and radical cancellation identifies its derivative with charge velocity
times the fixed singular norm derivative. The finite word family and its
regularity are constructed here rather than assumed. -/
theorem threeMovingNorm_hasDerivAt (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3)
    (c : ℂ → ℂ) (c' : ℂ) (hc : HasDerivAt c c' ((3:ℂ)/(p:ℂ)))
    (hc0 : c ((3:ℂ)/(p:ℂ))=vermaBSACharge ((3:ℂ)/(p:ℂ))) :
    HasDerivAt (fun t => (VirGram4.canB (c t)).form
      (vacuumProjection (c t) (threeMovingSource (c t) t ((p-1)*2)))
      (vacuumProjection (c t) (threeMovingSource (c t) t ((p-1)*2))))
      (c'*(minimalThreeNormPolynomial p hp hcop).derivative.eval
        (vermaBSACharge ((3:ℂ)/(p:ℂ)))) ((3:ℂ)/(p:ℂ)) := by
  classical
  let R := (p-1)*2
  let v (w : VermaPartitions R) (t : ℂ) := threeLevelCoordinate R w (threeMovingSource 0 t R)
  have hv (w : VermaPartitions R) : DifferentiableAt ℂ (v w) ((3:ℂ)/(p:ℂ)) :=
    threeMovingSource_coordinate_differentiable _ (minimal_three_parameter_ne_zero p (by omega)) R
      (fun j hj hjR => minimalThree_state_diagonal_ne_zero p hp hcop j hj hjR) _
  have he := minimalThree_moving_norm_hasDerivAt p hp hcop
    (fun w : VermaPartitions R => chargeWordExpression (negWord 0 0 w.val)) v
    (fun w => _root_.deriv (v w) ((3:ℂ)/(p:ℂ))) c c' ((3:ℂ)/(p:ℂ))
    (fun w => (hv w).hasDerivAt) hc hc0
    ((threeMovingExpression_finite _ R).symm.trans (threeMovingExpression_at_minimal p hp hcop))
  simpa only [v,← threeMovingExpression_finite,threeMovingExpression_eval] using he

end VOA.InverseDS.VirasoroVerma
