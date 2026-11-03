/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2NormalOrdering
import VOA.Examples.AffineSl2ScreeningSingular

/-!
# General highest-weight affine normal ordering

Unlike vacuum normal ordering, this reduction retains the horizontal
lowering mode F_0 and records powers of the highest Cartan weight as well
as the central level. It computes actual words on any highest-weight vector,
including the genuine charged Wakimoto representation.
-/
namespace VOA.AffineVOA.HighestNormalOrdering
open Module (End)
open NormalOrdering (currentWord)
noncomputable section

/-- Negative affine modes and the horizontal lowering mode are creation
operators in a general highest-weight module. -/
def IsLower (a : Fin 3) (m : ℤ) : Prop := m<0 ∨ (m=0 ∧ a=1)
instance (a : Fin 3) (m : ℤ) : Decidable (IsLower a m) := inferInstanceAs
  (Decidable (m<0 ∨ (m=0 ∧ a=1)))

/-- Two scalar powers and a literal creation word label a normal term. -/
abbrev Label := ℕ × ℕ × List (Fin 3 × ℤ)

/-- Finite linear combinations of the general highest-weight normal terms. -/
abbrev NormalForm := Label →₀ ℂ

/-- Prefix a creation letter without modifying either scalar exponent. -/
def prepend (i : Fin 3 × ℤ) : NormalForm →ₗ[ℂ] NormalForm :=
  Finsupp.lmapDomain ℂ ℂ (fun t => (t.1,t.2.1,i::t.2.2))

/-- Multiply every term by prescribed powers of level and highest weight. -/
def scalarShift (p h : ℕ) : NormalForm →ₗ[ℂ] NormalForm :=
  Finsupp.lmapDomain ℂ ℂ (fun t => (p+t.1,h+t.2.1,t.2.2))

/-- Commute a noncreation mode to the highest vector. At the bottom H_0
acts by the recorded highest weight; E_0 and all positive modes kill it. -/
def modeNormal (a : Fin 3) (m : ℤ) : List (Fin 3 × ℤ) → NormalForm
  | [] => if IsLower a m then Finsupp.single (0,0,[(a,m)]) 1 else
      if m=0 ∧ a=2 then Finsupp.single (0,1,[]) 1 else 0
  | i::w => if IsLower a m then Finsupp.single (0,0,(a,m)::i::w) 1 else
      prepend i (modeNormal a m w)+
        (∑ c : Fin 3,fabc a i.1 c • modeNormal c (m+i.2) w)+
        if m+i.2=0 then Finsupp.single (1,0,w) ((m : ℂ)*kappa a i.1) else 0

/-- Extend the recursive current action over finite scalar-power terms. -/
def actNormal (a : Fin 3) (m : ℤ) : NormalForm →ₗ[ℂ] NormalForm :=
  Finsupp.linearCombination ℂ (fun t => scalarShift t.1 t.2.1 (modeNormal a m t.2.2))

/-- Normalize any finite current word on a general highest vector. -/
def wordNormal : List (Fin 3 × ℤ) → NormalForm
  | [] => Finsupp.single (0,0,[]) 1
  | an::w => actNormal an.1 an.2 (wordNormal w)

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- Interpret the two recorded powers as the actual central level and
highest weight, and the remaining word as literal current operators. -/
def evaluate (J : Fin 3→ℤ→End ℂ E) (k h : ℂ) (v : E) : NormalForm →ₗ[ℂ] E :=
  Finsupp.linearCombination ℂ (fun t => (k^t.1*h^t.2.1) • currentWord J t.2.2 v)

/-- Evaluation of one finite normal term uses its exact two scalar powers. -/
theorem evaluate_single (J : Fin 3→ℤ→End ℂ E) (k h : ℂ) (v : E) (t : Label) (z : ℂ) :
    evaluate J k h v (Finsupp.single t z)=z • ((k^t.1*h^t.2.1) • currentWord J t.2.2 v) :=
  Finsupp.linearCombination_single ℂ z t

/-- Prefixing a normal form agrees with the actual creation action. -/
theorem evaluate_prepend (J : Fin 3→ℤ→End ℂ E) (k h : ℂ) (v : E)
    (i : Fin 3×ℤ) (f : NormalForm) :
    evaluate J k h v (prepend i f)=J i.1 i.2 (evaluate J k h v f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add,hf,hg]
  | single t z =>
      simp only [prepend,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,
        evaluate_single,currentWord,Module.End.mul_apply,map_smul]

/-- Shifting both scalar powers is multiplication by their actual values. -/
theorem evaluate_scalarShift (J : Fin 3→ℤ→End ℂ E) (k h : ℂ) (v : E)
    (p s : ℕ) (f : NormalForm) :
    evaluate J k h v (scalarShift p s f)=(k^p*h^s) • evaluate J k h v f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add,hf,hg,smul_add]
  | single t z =>
      simp only [scalarShift,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,
        evaluate_single,pow_add,smul_smul]
      congr 1
      ring

/-- Scalar affine commutators give the actual push-through identity. -/
theorem push (J : Fin 3→ℤ→End ℂ E) (k : ℂ)
    (hJ : ∀ a b m n,⁅J a m,J b n⁆=
      (∑ c,fabc a b c • J c (m+n))+
      if m+n=0 then ((m : ℂ)*k*kappa a b) • (1 : End ℂ E) else 0)
    (a b : Fin 3) (m n : ℤ) (x : E) :
    J a m (J b n x)=J b n (J a m x)+
      (∑ c,fabc a b c • J c (m+n) x)+
      if m+n=0 then ((m : ℂ)*k*kappa a b) • x else 0 := by
  have hc := congrArg (fun T : End ℂ E => T x) (hJ a b m n)
  dsimp only at hc
  rw [Ring.lie_def,LinearMap.sub_apply,Module.End.mul_apply,Module.End.mul_apply,
    LinearMap.add_apply,LinearMap.sum_apply] at hc
  simp only [LinearMap.smul_apply] at hc
  split_ifs at hc ⊢ <;> simp only [LinearMap.smul_apply,Module.End.one_apply,
    LinearMap.zero_apply] at hc
  all_goals rw [sub_eq_iff_eq_add] at hc
  all_goals rw [hc]; abel

/-- Recursive general highest-weight normal ordering equals the ACTUAL
current action. Only the stated affine commutator and highest-vector equations
are used; no PBW basis, determinant or singular-state existence is assumed. -/
theorem evaluate_modeNormal (J : Fin 3→ℤ→End ℂ E) (k h : ℂ) (v : E)
    (hJ : ∀ a b m n,⁅J a m,J b n⁆=
      (∑ c,fabc a b c • J c (m+n))+
      if m+n=0 then ((m : ℂ)*k*kappa a b) • (1 : End ℂ E) else 0)
    (hv : ∀ a m,¬IsLower a m → J a m v=if m=0 ∧ a=2 then h • v else 0)
    (a : Fin 3) (m : ℤ) (w : List (Fin 3×ℤ)) :
    evaluate J k h v (modeNormal a m w)=J a m (currentWord J w v) := by
  induction w generalizing a m with
  | nil =>
      by_cases hm : IsLower a m
      · simp only [modeNormal,if_pos hm,evaluate_single,pow_zero,mul_one,one_smul,
          currentWord,Module.End.mul_apply,Module.End.one_apply]
      · rw [modeNormal,if_neg hm]
        simp only [currentWord,Module.End.one_apply,hv a m hm]
        split_ifs <;> simp only [evaluate_single,pow_zero,pow_one,one_mul,
          currentWord,Module.End.one_apply,one_smul,map_zero]
  | cons i w ih =>
      by_cases hm : IsLower a m
      · simp only [modeNormal,if_pos hm,evaluate_single,pow_zero,mul_one,one_smul,
          currentWord,Module.End.mul_apply]
      · rw [modeNormal,if_neg hm,map_add,map_add,evaluate_prepend,ih,map_sum]
        simp only [map_smul,ih,currentWord,Module.End.mul_apply]
        rw [push J k hJ a i.1 m i.2]
        split_ifs <;> simp only [evaluate_single,pow_one,pow_zero,mul_one,map_zero]
        · rw [smul_smul]
          congr 2
          ring

/-- Finite scalar-power normal forms evaluate under every actual current. -/
theorem evaluate_actNormal (J : Fin 3→ℤ→End ℂ E) (k h : ℂ) (v : E)
    (hJ : ∀ a b m n,⁅J a m,J b n⁆=
      (∑ c,fabc a b c • J c (m+n))+
      if m+n=0 then ((m : ℂ)*k*kappa a b) • (1 : End ℂ E) else 0)
    (hv : ∀ a m,¬IsLower a m → J a m v=if m=0 ∧ a=2 then h • v else 0)
    (a : Fin 3) (m : ℤ) (f : NormalForm) :
    evaluate J k h v (actNormal a m f)=J a m (evaluate J k h v f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add,hf,hg]
  | single t z =>
      simp only [actNormal,Finsupp.linearCombination_single,map_smul,
        evaluate_scalarShift,evaluate_modeNormal J k h v hJ hv,evaluate_single]

/-- The complete reduction computes every actual finite word at general
level and highest weight, including words containing horizontal lowering. -/
theorem evaluate_wordNormal (J : Fin 3→ℤ→End ℂ E) (k h : ℂ) (v : E)
    (hJ : ∀ a b m n,⁅J a m,J b n⁆=
      (∑ c,fabc a b c • J c (m+n))+
      if m+n=0 then ((m : ℂ)*k*kappa a b) • (1 : End ℂ E) else 0)
    (hv : ∀ a m,¬IsLower a m → J a m v=if m=0 ∧ a=2 then h • v else 0)
    (w : List (Fin 3×ℤ)) :
    evaluate J k h v (wordNormal w)=currentWord J w v := by
  induction w with
  | nil => simp [wordNormal,evaluate_single,currentWord]
  | cons an w ih => rw [wordNormal,evaluate_actNormal J k h v hJ hv,ih]; rfl

end
end VOA.AffineVOA.HighestNormalOrdering
