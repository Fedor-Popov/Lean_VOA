/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2SingularNorm
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Uniform affine sl₂ normal ordering with an operator-valued level

A finite normal form records powers of the central operator and negative current
words. Nonnegative modes are commuted to the vacuum, using the actual sl₂
structure constants. The algorithm terminates on word length and works in every
affine vacuum representation, including an actual first-order deformation.
-/
namespace VOA.AffineVOA.NormalOrdering
open Module (End)
open SingularNorm

/-- A basis label records a power of the central operator and a creation word. -/
abbrev Label := ℕ × List (Fin 3 × ℕ)

/-- Finite coefficient data for central powers times creation words. -/
abbrev NormalForm := Label →₀ ℂ

/-- Add a creation mode to the front of every term, without changing its
central power. Equal labels are combined by finite-support addition. -/
noncomputable def prepend (i : Fin 3 × ℕ) : NormalForm →ₗ[ℂ] NormalForm :=
  Finsupp.lmapDomain ℂ ℂ (fun t => (t.1,i::t.2))

/-- Multiply every term by a power of the central operator. -/
noncomputable def centralShift (p : ℕ) : NormalForm →ₗ[ℂ] NormalForm :=
  Finsupp.lmapDomain ℂ ℂ (fun t => (p+t.1,t.2))

/-- Commute a colour-basis current through a negative word. The sum over
three colours is the ordinary sl₂ bracket; the last term retains the full
central operator. Every recursive call shortens the creation word. -/
noncomputable def modeNormal (a : Fin 3) (m : ℤ) : List (Fin 3 × ℕ) → NormalForm
  | [] => if m < 0 then Finsupp.single (0,[(a,(-m-1).toNat)]) 1 else 0
  | i::w => if m < 0 then Finsupp.single (0,(a,(-m-1).toNat)::i::w) 1 else
      prepend i (modeNormal a m w) +
        (∑ c : Fin 3, fabc a i.1 c • modeNormal c (m-(i.2:ℤ)-1) w) +
        if m-(i.2:ℤ)-1=0 then Finsupp.single (1,w) ((m:ℂ)*kappa a i.1) else 0

/-- Act on a finite normal form by one current, commuting past its central
power and extending the word algorithm by linearity. -/
noncomputable def actNormal (a : Fin 3) (m : ℤ) : NormalForm →ₗ[ℂ] NormalForm :=
  Finsupp.linearCombination ℂ (fun t => centralShift t.1 (modeNormal a m t.2))

/-- Normalize an arbitrary finite current word on the vacuum; each letter
contains its colour and literal integer mode index. -/
noncomputable def wordNormal : List (Fin 3 × ℤ) → NormalForm
  | [] => Finsupp.single (0,[]) 1
  | an::w => actNormal an.1 an.2 (wordNormal w)

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- An ordered word in the actual current operators. The leftmost letter
acts last on a vector, as in ordinary composition of operators. -/
noncomputable def currentWord (J : Fin 3 → ℤ → End ℂ E) :
    List (Fin 3 × ℤ) → End ℂ E
  | [] => 1
  | an::w => J an.1 an.2 * currentWord J w

/-- A natural creation index i denotes the strictly negative mode −i−1. -/
noncomputable def creationWord (J : Fin 3 → ℤ → End ℂ E)
    (w : List (Fin 3 × ℕ)) : End ℂ E :=
  currentWord J (w.map (fun i => (i.1,-(i.2:ℤ)-1)))

/-- Evaluate a normal form in an arbitrary representation on a chosen vacuum. -/
noncomputable def evaluate (A : AffineCentralCurrentData E) (v : E) : NormalForm →ₗ[ℂ] E :=
  Finsupp.linearCombination ℂ (fun t => (A.central^t.1) (creationWord (SingularNorm.J A) t.2 v))

/-- One normal-form term has its literal operator meaning. -/
theorem evaluate_single (A : AffineCentralCurrentData E) (v : E) (t : Label) (a : ℂ) :
    evaluate A v (Finsupp.single t a) = a • (A.central^t.1) (creationWord (SingularNorm.J A) t.2 v) :=
  Finsupp.linearCombination_single ℂ a t

/-- Prefixing a normal form agrees with the corresponding creation-mode action. -/
theorem evaluate_prepend (A : AffineCentralCurrentData E) (v : E) (i : Fin 3 × ℕ) (f : NormalForm) :
    evaluate A v (prepend i f) = SingularNorm.J A i.1 (-(i.2:ℤ)-1) (evaluate A v f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single t a =>
    simp only [prepend, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      evaluate_single, creationWord, List.map_cons, currentWord, Module.End.mul_apply,
      map_smul, J_central_pow]

/-- Shifting central degree agrees with applying a central power. -/
theorem evaluate_centralShift (A : AffineCentralCurrentData E) (v : E) (p : ℕ) (f : NormalForm) :
    evaluate A v (centralShift p f) = (A.central^p) (evaluate A v f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single t a =>
    simp only [centralShift, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      evaluate_single, map_smul, pow_add, Module.End.mul_apply]

/-- The recursive reduction equals the actual action in every affine vacuum
representation. Neither a scalar central action nor PBW independence is used. -/
theorem evaluate_modeNormal (A : AffineCentralCurrentData E) (v : E)
    (hv : ∀ a (n : ℤ), 0 ≤ n → SingularNorm.J A a n v = 0)
    (a : Fin 3) (m : ℤ) (w : List (Fin 3 × ℕ)) :
    evaluate A v (modeNormal a m w) = SingularNorm.J A a m (creationWord (SingularNorm.J A) w v) := by
  induction w generalizing a m with
  | nil =>
    by_cases hm : m < 0
    · have he : -(((-m-1).toNat : ℕ):ℤ)-1=m := by omega
      simp only [modeNormal, if_pos hm, evaluate_single, creationWord, List.map_cons,
        List.map_nil, currentWord, Module.End.mul_apply, pow_zero, Module.End.one_apply,
        one_smul, he]
    · simp [modeNormal, hm, creationWord, currentWord, hv a m (by omega)]
  | cons i w ih =>
    by_cases hm : m < 0
    · have he : -(((-m-1).toNat : ℕ):ℤ)-1=m := by omega
      simp only [modeNormal, if_pos hm, evaluate_single, creationWord, List.map_cons,
        List.map_nil, currentWord, Module.End.mul_apply, pow_zero, Module.End.one_apply,
        one_smul, he]
    · rw [modeNormal, if_neg hm, map_add, map_add, evaluate_prepend, ih, map_sum]
      simp only [map_smul, ih]
      simp only [creationWord, List.map_cons, currentWord, Module.End.mul_apply]
      rw [push A a i.1 m (-(i.2:ℤ)-1)]
      have he : m + (-(i.2:ℤ)-1) = m-(i.2:ℤ)-1 := by omega
      rw [he]
      split_ifs <;> simp only [evaluate_single, pow_one, map_zero, creationWord, one_smul]

/-- The linear mode action on normal forms evaluates to the actual mode. -/
theorem evaluate_actNormal (A : AffineCentralCurrentData E) (v : E)
    (hv : ∀ a (n : ℤ), 0 ≤ n → SingularNorm.J A a n v = 0) (a : Fin 3) (m : ℤ) (f : NormalForm) :
    evaluate A v (actNormal a m f) = SingularNorm.J A a m (evaluate A v f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single t a =>
    simp only [actNormal, Finsupp.linearCombination_single, map_smul,
      evaluate_centralShift, evaluate_modeNormal A v hv, evaluate_single, J_central_pow]

/-- Every finite mode word has the computed central-power normal form in
EVERY affine vacuum representation. No scalar level or PBW basis is assumed. -/
theorem evaluate_wordNormal (A : AffineCentralCurrentData E) (v : E)
    (hv : ∀ a (n : ℤ), 0 ≤ n → SingularNorm.J A a n v = 0) (w : List (Fin 3 × ℤ)) :
    evaluate A v (wordNormal w) = currentWord (SingularNorm.J A) w v := by
  induction w with
  | nil => simp [wordNormal, evaluate_single, creationWord, currentWord]
  | cons m w ih => rw [wordNormal, evaluate_actNormal A v hv, ih]; rfl

end VOA.AffineVOA.NormalOrdering
