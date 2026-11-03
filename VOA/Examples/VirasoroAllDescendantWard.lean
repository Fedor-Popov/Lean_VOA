/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroDescendantTower

/-!
# All negative descendants on actual Verma level sequences

A field-weight variable makes the shifts in the Ward formulas into ordinary
endomorphism compositions. The initial operators act on genuine Verma states,
not formal symbols. Jacobi then propagates their positive commutators to all
negative indices. A full negative-mode representation and fusion construction
remain separate obligations.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule LeeYangWardClosure

/-- The vector space of sequences whose rth coefficient lies in actual
Verma level r. This incorporates all needed truncation conditions. -/
def wardSequenceSpace (c h : ℂ) : Submodule ℂ (ℕ → Verma c h) where
  carrier := {f | WardLevel c h f}
  zero_mem' := fun r => (sortedSpan c h r).zero_mem
  add_mem' hf hg := fun r => (sortedSpan c h r).add_mem (hf r) (hg r)
  smul_mem' z f hf := fun r => (sortedSpan c h r).smul_mem z (hf r)

/-- The first negative Ward operator as a linear map on actual level sequences. -/
noncomputable def wardD1Map (c h b a : ℂ) : Module.End ℂ (wardSequenceSpace c h) where
  toFun f := ⟨wardDescendant1 c h b a f, wardDescendant1_level c h b a f f.property⟩
  map_add' f g := by
    apply Subtype.ext
    funext r
    simp [wardDescendant1,smul_add]
    <;> module
  map_smul' z f := by
    apply Subtype.ext
    funext r
    simp [wardDescendant1,smul_smul,mul_comm]
    <;> module

/-- The second negative Ward operator as a linear map on actual level sequences. -/
noncomputable def wardD2Map (c h b a : ℂ) : Module.End ℂ (wardSequenceSpace c h) where
  toFun f := ⟨wardDescendant2 c h b a f, wardDescendant2_level c h b a f f.property⟩
  map_add' f g := by
    apply Subtype.ext
    funext r
    simp [wardDescendant2,wardSource,Finset.sum_add_distrib,smul_add]
    <;> module
  map_smul' z f := by
    apply Subtype.ext
    funext r
    simp [wardDescendant2,wardSource,Finset.smul_sum,smul_add,smul_smul]
    <;> module

/-- The first positive Ward operator as a linear map on actual level sequences. -/
noncomputable def wardP1Map (c h b a : ℂ) : Module.End ℂ (wardSequenceSpace c h) where
  toFun f := ⟨wardPositive1 c h b a f, wardPositive1_level c h b a f f.property⟩
  map_add' f g := by
    apply Subtype.ext
    funext r
    simp [wardPositive1,smul_add]
    <;> module
  map_smul' z f := by
    apply Subtype.ext
    funext r
    simp [wardPositive1,smul_sub,smul_smul]
    <;> module

/-- The second positive Ward operator as a linear map on actual level sequences. -/
noncomputable def wardP2Map (c h b a : ℂ) : Module.End ℂ (wardSequenceSpace c h) where
  toFun f := ⟨wardPositive2 c h b a f, wardPositive2_level c h b a f f.property⟩
  map_add' f g := by
    apply Subtype.ext
    funext r
    simp [wardPositive2,wardPositive1,wardCovariance2,smul_add]
    <;> module
  map_smul' z f := by
    apply Subtype.ext
    funext r
    simp [wardPositive2,wardPositive1,wardCovariance2,smul_sub,smul_smul]
    <;> module

/-- Shift field weight by d while applying the operator at the input
weight. This converts weight-shifted compositions into ordinary composition. -/
noncomputable def wardShift (c h : ℂ) (d : ℂ)
    (T : ℂ → Module.End ℂ (wardSequenceSpace c h)) :
    Module.End ℂ (ℂ → wardSequenceSpace c h) where
  toFun f a := T (a-d) (f (a-d))
  map_add' f g := by ext a; simp
  map_smul' z f := by ext a; simp

/-- The weight operator multiplies each field-weight component by its weight. -/
noncomputable def wardWeight (c h : ℂ) : Module.End ℂ (ℂ → wardSequenceSpace c h) where
  toFun f a := a • f a
  map_add' f g := by ext a; simp [smul_add]
  map_smul' z f := by ext a; simp [smul_smul,mul_comm]

/-- Every shifted linear operator has its indicated degree under the weight
commutator, independently of its coefficient formula. -/
theorem wardWeight_shift (c h d : ℂ) (T : ℂ → Module.End ℂ (wardSequenceSpace c h)) :
    ⁅wardWeight c h,wardShift c h d T⁆=d • wardShift c h d T := by
  apply LinearMap.ext
  intro f
  funext a
  change a • T (a-d) (f (a-d))-T (a-d) ((a-d) • f (a-d))=d • T (a-d) (f (a-d))
  rw [map_smul]
  module

/-- The first global negative operator raises field weight by one. -/
noncomputable def wardA (c h b : ℂ) := wardShift c h 1 (wardD1Map c h b)
/-- The second global negative operator raises field weight by two. -/
noncomputable def wardB (c h b : ℂ) := wardShift c h 2 (wardD2Map c h b)
/-- The first global positive operator lowers field weight by one. -/
noncomputable def wardP (c h b : ℂ) := wardShift c h (-1) (wardP1Map c h b)
/-- The second global positive operator lowers field weight by two. -/
noncomputable def wardQ (c h b : ℂ) := wardShift c h (-2) (wardP2Map c h b)

/-- The weight commutator of the first actual negative operator. -/
theorem wardWeight_A (c h b : ℂ) : ⁅wardWeight c h,wardA c h b⁆=wardA c h b := by
  simpa [wardA] using wardWeight_shift c h 1 (wardD1Map c h b)
/-- The weight commutator of the second actual negative operator. -/
theorem wardWeight_B (c h b : ℂ) : ⁅wardWeight c h,wardB c h b⁆=(2:ℂ) • wardB c h b :=
  wardWeight_shift c h 2 (wardD2Map c h b)

/-- First positive/first negative commutation on the genuine sequence space. -/
theorem wardP_A (c h b : ℂ) : ⁅wardP c h b,wardA c h b⁆=(2:ℂ) • wardWeight c h := by
  ext f a r
  change wardPositive1 c h b (a-(-1)) (wardDescendant1 c h b (a-(-1)-1) (f (a-(-1)-1))) r-
    wardDescendant1 c h b (a-1) (wardPositive1 c h b (a-1-(-1)) (f (a-1-(-1)))) r= _
  simp only [sub_neg_eq_add,add_sub_cancel_right,sub_add_cancel]
  rw [wardPositive1_descendant1 c h b a (f a) r]
  change (2*a) • (f a).val r=(2:ℂ) • (a • (f a).val r)
  rw [smul_smul]

/-- First positive/second negative commutation, with field shifts absorbed. -/
theorem wardP_B (c h b : ℂ) : ⁅wardP c h b,wardB c h b⁆=(3:ℂ) • wardA c h b := by
  ext f a r
  change wardPositive1 c h b (a-(-1)) (wardDescendant2 c h b (a-(-1)-2) (f (a-(-1)-2))) r-
    wardDescendant2 c h b (a-2) (wardPositive1 c h b (a-2-(-1)) (f (a-2-(-1)))) r= _
  convert wardPositive1_descendant2 c h b (a-1) (f (a-1)) (f (a-1)).property r using 1 <;>
    congr 1 <;> congr 1 <;> ring

/-- Second positive/first negative commutation on actual sequences. -/
theorem wardQ_A (c h b : ℂ) : ⁅wardQ c h b,wardA c h b⁆=(3:ℂ) • wardP c h b := by
  ext f a r
  change wardPositive2 c h b (a-(-2)) (wardDescendant1 c h b (a-(-2)-1) (f (a-(-2)-1))) r-
    wardDescendant1 c h b (a-1) (wardPositive2 c h b (a-1-(-2)) (f (a-1-(-2)))) r=
      (3:ℂ) • wardPositive1 c h b (a-(-1)) (f (a-(-1))) r
  convert wardPositive2_descendant1 c h b (a+1) (f (a+1)) r using 1 <;>
    congr 1 <;> congr 1 <;> ring

/-- Second positive/second negative commutation includes exactly the central
scalar c/2. Both compositions preserve field weight. -/
theorem wardQ_B (c h b : ℂ) : ⁅wardQ c h b,wardB c h b⁆=
    (4:ℂ) • wardWeight c h+(c/2) • LinearMap.id := by
  ext f a r
  change wardPositive2 c h b (a-(-2)) (wardDescendant2 c h b (a-(-2)-2) (f (a-(-2)-2))) r-
    wardDescendant2 c h b (a-2) (wardPositive2 c h b (a-2-(-2)) (f (a-2-(-2)))) r= _
  simp only [sub_neg_eq_add,add_sub_cancel_right,sub_add_cancel]
  rw [wardPositive2_descendant2 c h b a (f a) (f a).property r]
  change (4*a+c/2) • (f a).val r= (4:ℂ) • (a • (f a).val r)+(c/2) • (f a).val r
  module

/-- Every higher negative operator is generated from the actual first two.
Index n denotes mode -(n+2). The construction stays in actual level sequences. -/
noncomputable def wardNegative (c h b : ℂ) (n : ℕ) :
    Module.End ℂ (ℂ → wardSequenceSpace c h) :=
  DescendantTower.tower (wardA c h b) (wardB c h b) n

/-- Index zero recovers the already constructed second negative operator. -/
@[simp] theorem wardNegative_zero (c h b : ℂ) : wardNegative c h b 0=wardB c h b := rfl

/-- Commuting with the first negative operator generates the next one. -/
theorem wardA_negative (c h b : ℂ) (n : ℕ) :
    ⁅wardA c h b,wardNegative c h b n⁆=((n:ℂ)+1) • wardNegative c h b (n+1) :=
  DescendantTower.bracket_tower _ _ n

/-- Every generated negative operator has the required field-weight degree. -/
theorem wardWeight_negative (c h b : ℂ) (n : ℕ) :
    ⁅wardWeight c h,wardNegative c h b n⁆=((n:ℂ)+2) • wardNegative c h b n :=
  DescendantTower.weight_tower _ _ _ (wardWeight_A c h b) (wardWeight_B c h b) n

/-- The actual first positive Ward operator commutes correctly with ALL
negative operators, beyond the separately proved first two cases. -/
theorem wardP_negative (c h b : ℂ) (n : ℕ) :
    ⁅wardP c h b,wardNegative c h b (n+1)⁆=((n:ℂ)+4) • wardNegative c h b n :=
  DescendantTower.positive1_tower _ _ _ _ (wardWeight_A c h b)
    (wardWeight_B c h b) (wardP_A c h b) (wardP_B c h b) n

/-- The central scalar commutes with the first negative operator. -/
theorem wardA_central (c h b : ℂ) :
    ⁅wardA c h b,(c/2) • (LinearMap.id : Module.End ℂ (ℂ → wardSequenceSpace c h))⁆=0 := by
  ext f a r
  change ((wardA c h b) ((c/2) • f) a).val r - ((c/2) • (wardA c h b) f a).val r = 0
  rw [map_smul]
  simp

/-- At negative index three the second positive commutator is five times
the first negative operator. -/
theorem wardQ_negative_one (c h b : ℂ) :
    ⁅wardQ c h b,wardNegative c h b 1⁆=(5:ℂ) • wardA c h b :=
  DescendantTower.positive2_tower_one _ _ _ _ _ _ (wardWeight_A c h b)
    (wardP_B c h b) (wardQ_A c h b) (wardQ_B c h b) (wardA_central c h b)

/-- The actual second positive Ward operator commutes correctly with ALL
negative indices at least four. This requires no fusion or singular-state input. -/
theorem wardQ_negative (c h b : ℂ) (n : ℕ) :
    ⁅wardQ c h b,wardNegative c h b (n+2)⁆=((n:ℂ)+6) • wardNegative c h b n :=
  DescendantTower.positive2_tower _ _ _ _ _ _ (wardWeight_A c h b)
    (wardWeight_B c h b) (wardP_A c h b) (wardP_B c h b)
    (wardQ_A c h b) (wardQ_B c h b) (wardA_central c h b) n

end VOA.InverseDS.VirasoroVerma
