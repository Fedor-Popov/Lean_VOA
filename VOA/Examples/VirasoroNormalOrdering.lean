/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroWordPairing
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Uniform Virasoro normal ordering with an operator-valued center

A normal form is a finite linear combination of K^p times creation words.
Creation indices are natural numbers: i means mode −i−2, so all normal words
are built from genuine creation modes. The recursive algorithm terminates on
the creation-word length. Its evaluation theorem holds in every central
Virasoro mode representation with a vacuum, independently of the charge.
-/
namespace VOA.VirDeformModes.NormalOrdering
open Module (End)

/-- A basis label records a power of the central operator and a creation word. -/
abbrev Label := ℕ × List ℕ

/-- Finite coefficient data for central powers times creation words. -/
abbrev NormalForm := Label →₀ ℂ

/-- Add a creation mode to the front of every term, without changing its
central power. Equal labels are combined by finite-support addition. -/
noncomputable def prepend (i : ℕ) : NormalForm →ₗ[ℂ] NormalForm :=
  Finsupp.lmapDomain ℂ ℂ (fun t => (t.1,i::t.2))

/-- Multiply every term by a power of the central operator. -/
noncomputable def centralShift (p : ℕ) : NormalForm →ₗ[ℂ] NormalForm :=
  Finsupp.lmapDomain ℂ ℂ (fun t => (p+t.1,t.2))

/-- Commute a mode through a creation word. Negative creation modes stay on
the left; other modes are pushed to the vacuum using the Virasoro relation.
The recursive calls always shorten the creation word, even when indices change. -/
noncomputable def modeNormal (m : ℤ) : List ℕ → NormalForm
  | [] => if m < -1 then Finsupp.single (0,[(-m-2).toNat]) 1 else 0
  | i::w => if m < -1 then Finsupp.single (0,(-m-2).toNat::i::w) 1 else
      prepend i (modeNormal m w) + ((m : ℂ)+(i : ℂ)+2) • modeNormal (m-(i:ℤ)-2) w +
        if m-(i:ℤ)-2=0 then Finsupp.single (1,w) (((m:ℂ)^3-m)/12) else 0

/-- Extend mode normalization linearly to normal forms, commuting through
central powers before normalizing the creation word. -/
noncomputable def actNormal (m : ℤ) : NormalForm →ₗ[ℂ] NormalForm :=
  Finsupp.linearCombination ℂ (fun t => centralShift t.1 (modeNormal m t.2))

/-- Normalize an arbitrary finite mode word acting on the vacuum. This is one
recursive construction for all word lengths and all conformal weights. -/
noncomputable def wordNormal : List ℤ → NormalForm
  | [] => Finsupp.single (0,[]) 1
  | m::w => actNormal m (wordNormal w)

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- Interpret natural creation indices as actual negative Virasoro modes. -/
noncomputable def creationWord (L : ℤ → End ℂ E) (w : List ℕ) : End ℂ E :=
  virWord L (w.map (fun (i : ℕ) => -(i:ℤ)-2))

/-- Evaluate a normal form in an arbitrary representation on a chosen vacuum. -/
noncomputable def evaluate (A : CentralVirasoroData E) (v : E) : NormalForm →ₗ[ℂ] E :=
  Finsupp.linearCombination ℂ (fun t => (A.central^t.1) (creationWord A.L t.2 v))

/-- One normal-form term has its literal operator meaning. -/
theorem evaluate_single (A : CentralVirasoroData E) (v : E) (t : Label) (a : ℂ) :
    evaluate A v (Finsupp.single t a) = a • (A.central^t.1) (creationWord A.L t.2 v) :=
  Finsupp.linearCombination_single ℂ a t

/-- Central commutation extends from one central factor to any power. -/
theorem mode_central_pow (A : CentralVirasoroData E) (m : ℤ) (p : ℕ) (x : E) :
    A.L m ((A.central^p) x) = (A.central^p) (A.L m x) :=
  (LinearMap.congr_fun ((A.central_comm m).pow_left p) x).symm

/-- Prefixing a normal form agrees with the corresponding creation-mode action. -/
theorem evaluate_prepend (A : CentralVirasoroData E) (v : E) (i : ℕ) (f : NormalForm) :
    evaluate A v (prepend i f) = A.L (-(i:ℤ)-2) (evaluate A v f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single t a =>
    simp only [prepend, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      evaluate_single, creationWord, List.map_cons, virWord, Module.End.mul_apply,
      map_smul, mode_central_pow]

/-- Shifting central degree agrees with applying a central power. -/
theorem evaluate_centralShift (A : CentralVirasoroData E) (v : E) (p : ℕ) (f : NormalForm) :
    evaluate A v (centralShift p f) = (A.central^p) (evaluate A v f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single t a =>
    simp only [centralShift, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      evaluate_single, map_smul, pow_add, Module.End.mul_apply]

/-- The one-mode algorithm is correct for every creation word and every
Virasoro vacuum. This is a uniform proof, not a family of generated tests. -/
theorem evaluate_modeNormal (A : CentralVirasoroData E) (v : E)
    (hv : ∀ n : ℤ, -1 ≤ n → A.L n v = 0) (m : ℤ) (w : List ℕ) :
    evaluate A v (modeNormal m w) = A.L m (creationWord A.L w v) := by
  induction w generalizing m with
  | nil =>
    by_cases hm : m < -1
    · have he : -(((-m-2).toNat : ℕ):ℤ)-2=m := by omega
      simp only [modeNormal, if_pos hm, evaluate_single, creationWord, List.map_cons,
        List.map_nil, virWord, Module.End.mul_apply, pow_zero, Module.End.one_apply, one_smul, he]
    · simp [modeNormal, hm, creationWord, virWord, hv m (by omega)]
  | cons i w ih =>
    by_cases hm : m < -1
    · have he : -(((-m-2).toNat : ℕ):ℤ)-2=m := by omega
      simp only [modeNormal, if_pos hm, evaluate_single, creationWord, List.map_cons,
        List.map_nil, virWord, Module.End.mul_apply, pow_zero, Module.End.one_apply, one_smul, he]
    · rw [modeNormal, if_neg hm, map_add, map_add, map_smul, evaluate_prepend, ih, ih]
      simp only [creationWord, List.map_cons, virWord, Module.End.mul_apply]
      rw [vir_push A m (-(i:ℤ)-2)]
      have he : m + (-(i:ℤ)-2) = m-(i:ℤ)-2 := by omega
      rw [he]
      split_ifs <;> simp only [evaluate_single, pow_one, map_zero, creationWord]
      all_goals push_cast
      all_goals module

/-- The linear mode action on normal forms evaluates to the actual mode. -/
theorem evaluate_actNormal (A : CentralVirasoroData E) (v : E)
    (hv : ∀ n : ℤ, -1 ≤ n → A.L n v = 0) (m : ℤ) (f : NormalForm) :
    evaluate A v (actNormal m f) = A.L m (evaluate A v f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single t a =>
    simp only [actNormal, Finsupp.linearCombination_single, map_smul,
      evaluate_centralShift, evaluate_modeNormal A v hv, evaluate_single, mode_central_pow]

/-- Every finite mode word has the computed central-power normal form in
EVERY Virasoro vacuum representation. No scalar charge or PBW basis is assumed. -/
theorem evaluate_wordNormal (A : CentralVirasoroData E) (v : E)
    (hv : ∀ n : ℤ, -1 ≤ n → A.L n v = 0) (w : List ℤ) :
    evaluate A v (wordNormal w) = virWord A.L w v := by
  induction w with
  | nil => simp [wordNormal, evaluate_single, creationWord, virWord]
  | cons m w ih => rw [wordNormal, evaluate_actNormal A v hv, ih]; rfl

end VOA.VirDeformModes.NormalOrdering
