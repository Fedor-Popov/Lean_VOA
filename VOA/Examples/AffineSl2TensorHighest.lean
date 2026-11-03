/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.WakimotoVacuumProjection
import VOA.Examples.WakimotoShiftedIndependence

/-!
# Actual highest-current models at arbitrary affine parameters

Three shifted vacuum actions at dilation two, three and four realize any
prescribed level and highest weight. A free auxiliary scalar avoids the
three critical factor levels. Projection to the first vacuum factor proves
independence of ALL occupation words, including horizontal lowering.
-/
namespace VOA.Wak.Charged
open Module (End)
open MvPolynomial AffineVOA
open AffineVOA.HighestNormalOrdering
open AffineVOA.NormalOrdering (currentWord)
open scoped TensorProduct
noncomputable section

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Actions on different tensor factors commute as actual endomorphisms. -/
theorem current_tensor_factors_commute (a : End ℂ V) (b : End ℂ W) :
    Commute (a.rTensor W) (b.lTensor V) := by
  show (a.rTensor W).comp (b.lTensor V)=(b.lTensor V).comp (a.rTensor W)
  rw [LinearMap.rTensor_comp_lTensor,LinearMap.lTensor_comp_rTensor]

/-- Tensoring affine actions adds their central levels. This checks every
commutator and its scalar central term on the actual tensor carrier. -/
theorem tensorCurrent_comm (A : Fin 3→ℤ→End ℂ V) (B : Fin 3→ℤ→End ℂ W) (k l : ℂ)
    (hA : ∀ a b m n,⁅A a m,A b n⁆=(∑ c,fabc a b c • A c (m+n))+
      if m+n=0 then ((m : ℂ)*k*kappa a b) • (1 : End ℂ V) else 0)
    (hB : ∀ a b m n,⁅B a m,B b n⁆=(∑ c,fabc a b c • B c (m+n))+
      if m+n=0 then ((m : ℂ)*l*kappa a b) • (1 : End ℂ W) else 0)
    (a b : Fin 3) (m n : ℤ) :
    ⁅tensorCurrent A B a m,tensorCurrent A B b n⁆=
      (∑ c,fabc a b c • tensorCurrent A B c (m+n))+
      if m+n=0 then ((m : ℂ)*(k+l)*kappa a b) • (1 : End ℂ (V ⊗[ℂ] W)) else 0 := by
  let F := End.rTensorAlgHom ℂ V W
  let G := End.lTensorAlgHom ℂ W V
  have ha := congrArg F (hA a b m n)
  have hb := congrArg G (hB a b m n)
  simp only [Ring.lie_def,map_sub,map_mul,map_add,map_sum,map_smul] at ha hb
  have h1 := (current_tensor_factors_commute (A a m) (B b n)).eq
  have h2 := (current_tensor_factors_commute (A b n) (B a m)).eq
  change F (A a m)*G (B b n)=G (B b n)*F (A a m) at h1
  change F (A b n)*G (B a m)=G (B a m)*F (A b n) at h2
  have he : (F (A a m)+G (B a m))*(F (A b n)+G (B b n))-
      (F (A b n)+G (B b n))*(F (A a m)+G (B a m))=
      (F (A a m)*F (A b n)-F (A b n)*F (A a m))+
      (G (B a m)*G (B b n)-G (B b n)*G (B a m)) := by
    simp only [add_mul,mul_add]
    rw [h1,h2]
    abel
  change (F (A a m)+G (B a m))*(F (A b n)+G (B b n))-
    (F (A b n)+G (B b n))*(F (A a m)+G (B a m))=_
  rw [he,ha,hb]
  change (∑ c,fabc a b c • F (A c (m+n)))+F (if m+n=0 then _ else 0)+
    ((∑ c,fabc a b c • G (B c (m+n)))+G (if m+n=0 then _ else 0))=_
  simp only [tensorCurrent,smul_add,Finset.sum_add_distrib]
  by_cases hz : m+n=0
  · simp only [if_pos hz,map_smul,map_one]
    dsimp [F,G,End.rTensorAlgHom,End.lTensorAlgHom]
    module
  · simp only [if_neg hz,map_zero,add_zero]
    rfl

/-- Highest-vector equations tensor together with addition of the Cartan
weights, while every other positive generator still kills the tensor. -/
theorem tensorCurrent_highest (A : Fin 3→ℤ→End ℂ V) (B : Fin 3→ℤ→End ℂ W)
    (v : V) (w : W) (h l : ℂ)
    (hv : ∀ a n,¬IsLower a n → A a n v=if n=0 ∧ a=2 then h • v else 0)
    (hw : ∀ a n,¬IsLower a n → B a n w=if n=0 ∧ a=2 then l • w else 0)
    (a : Fin 3) (n : ℤ) (hn : ¬IsLower a n) :
    tensorCurrent A B a n (v ⊗ₜ[ℂ] w)=if n=0 ∧ a=2 then (h+l) • (v ⊗ₜ[ℂ] w) else 0 := by
  rw [tensorCurrent_tmul,hv a n hn,hw a n hn]
  split_ifs <;> simp [TensorProduct.smul_tmul,TensorProduct.tmul_smul,add_smul]

/-- The actual triple polynomial carrier for arbitrary affine highest data. -/
abbrev HighestTensorFock := (WakFock ⊗[ℂ] WakFock) ⊗[ℂ] WakFock

/-- Its normalized highest tensor is independent of the level parameters. -/
def highestTensorVacuum : HighestTensorFock := ((1 : WakFock) ⊗ₜ[ℂ] (1 : WakFock)) ⊗ₜ[ℂ] (1 : WakFock)

/-- The three shifted current actions, before selecting their levels. -/
def highestTensorJ (a b c : ℂ) : Fin 3→ℤ→End ℂ HighestTensorFock :=
  tensorCurrent (tensorCurrent (shiftedJ 2 a) (shiftedJ 3 b)) (shiftedJ 4 c)

/-- The actual triple action has central level 2a+3b+4c. -/
theorem highestTensorJ_comm (a b c : ℂ) (ha : a+2≠0) (hb : b+2≠0) (hc : c+2≠0)
    (i j : Fin 3) (m n : ℤ) :
    ⁅highestTensorJ a b c i m,highestTensorJ a b c j n⁆=
      (∑ e,fabc i j e • highestTensorJ a b c e (m+n))+
      if m+n=0 then ((m : ℂ)*(2*a+3*b+4*c)*kappa i j) • (1 : End ℂ HighestTensorFock) else 0 := by
  exact tensorCurrent_comm _ _ (2*a+3*b) (4*c)
    (tensorCurrent_comm _ _ (2*a) (3*b) (shiftedJ_comm 2 (by decide) a ha)
      (shiftedJ_comm 3 (by decide) b hb)) (shiftedJ_comm 4 (by decide) c hc) i j m n

/-- The actual tensor vacuum has highest Cartan weight a+b+c. -/
theorem highestTensorJ_highest (a b c : ℂ) (i : Fin 3) (n : ℤ) (hn : ¬IsLower i n) :
    highestTensorJ a b c i n highestTensorVacuum=
      if n=0 ∧ i=2 then (a+b+c) • highestTensorVacuum else 0 := by
  exact tensorCurrent_highest _ _ _ _ (a+b) c
    (tensorCurrent_highest _ _ _ _ a b (shiftedJ_one_highest 2 (by decide) a)
      (shiftedJ_one_highest 3 (by decide) b)) (shiftedJ_one_highest 4 (by decide) c) i n hn

/-- Successively project the two last actual vacuum factors to constants. -/
def highestTensorProjection : HighestTensorFock→ₗ[ℂ]WakFock :=
  rightVacuumProjection.comp rightVacuumProjection

/-- The actual tensor highest vector projects to the original nonzero one. -/
theorem highestTensorProjection_vacuum : highestTensorProjection highestTensorVacuum=1 := by
  simp [highestTensorProjection,highestTensorVacuum,rightVacuumProjection_tmul]

/-- All general creation words project exactly to the first shifted vacuum
word. This excludes cancellation from the auxiliary tensor factors. -/
theorem highestTensorProjection_word (a b c : ℂ) (w : List (Fin 3×ℤ))
    (hw : ∀ an∈w,IsLower an.1 an.2) :
    highestTensorProjection (currentWord (highestTensorJ a b c) w highestTensorVacuum)=
      currentWord (shiftedJ 2 a) w (1 : WakFock) := by
  change rightVacuumProjection (rightVacuumProjection (currentWord
    (tensorCurrent (tensorCurrent (shiftedJ 2 a) (shiftedJ 3 b)) (shiftedJ 4 c)) w
      (((1 : WakFock) ⊗ₜ[ℂ] (1 : WakFock)) ⊗ₜ[ℂ] (1 : WakFock))))=_
  rw [rightVacuumProjection_word _ 4 (by decide) c w hw,rightVacuumProjection_tmul]
  simp only [map_one,one_smul]
  rw [rightVacuumProjection_word _ 3 (by decide) b w hw,rightVacuumProjection_tmul]
  simp

/-- ACTUAL general creation occupation words are independent in the triple
model, for every choice of factor levels. This includes all F_0 powers. -/
theorem highestTensor_words_independent (a b c : ℂ) :
    LinearIndependent ℂ (fun d : Occupation => currentWord (highestTensorJ a b c)
      (occupationWord d) highestTensorVacuum) := by
  have h := shiftedOccupationWord_independent a
  have he : (fun d : Occupation => highestTensorProjection
      (currentWord (highestTensorJ a b c) (occupationWord d) highestTensorVacuum))=
      (fun d : Occupation => currentWord (shiftedJ 2 a) (occupationWord d) (1 : WakFock)) := by
    funext d
    exact highestTensorProjection_word a b c _ (occupationWord_lower d)
  rw [← he] at h
  exact LinearIndependent.of_comp highestTensorProjection h

/-- Avoiding only three explicitly listed complex values selects noncritical
factor levels for ANY prescribed total level and highest weight. -/
theorem exists_highest_tensor_levels (k h : ℂ) : ∃ a b c : ℂ,
    a+2≠0 ∧ b+2≠0 ∧ c+2≠0 ∧ 2*a+3*b+4*c=k ∧ a+b+c=h := by
  classical
  obtain ⟨z,hz⟩ := Infinite.exists_notMem_finset ({k-3*h-2,(k-2*h+2)/2,-2} : Finset ℂ)
  have hz1 : z≠k-3*h-2 := by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hz; exact hz.1
  have hz2 : z≠(k-2*h+2)/2 := by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hz; exact hz.2.1
  have hz3 : z≠-2 := by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hz; exact hz.2.2
  refine ⟨3*h-k+z,k-2*h-2*z,z,?_,?_,?_,?_,?_⟩
  · intro he; apply hz1; linear_combination he
  · intro he; apply hz2; linear_combination -(1/2 : ℂ)*he
  · intro he; apply hz3; linear_combination he
  · ring
  · ring

end
end VOA.Wak.Charged
