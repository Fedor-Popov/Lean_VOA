/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroAllDescendantWard

/-!
# Triangularity of all negative descendant operators

Earlier coefficient vanishing is preserved by every negative descendant.
On the first possibly nonzero coefficient, the operator is an explicit
scalar and a field-weight shift. This computes the diagonal needed for a
future fusion recursion, without assuming that its scalar is nonzero.
-/
namespace VOA.InverseDS.VirasoroVerma

/-- All coefficients strictly below r vanish at every field weight. -/
def WardBelow {c h : ℂ} (f : ℂ → wardSequenceSpace c h) (r : ℕ) : Prop :=
  ∀ a j, j<r → (f a).val j=0

/-- The first negative operator acts diagonally in the coefficient index
and shifts field weight by one. -/
theorem wardA_apply (c h b : ℂ) (f : ℂ → wardSequenceSpace c h) (a : ℂ) (r : ℕ) :
    ((wardA c h b) f a).val r=(h-b-(a-1)+(r:ℂ)) • (f (a-1)).val r := rfl

/-- The first negative operator preserves any initial segment of zeros. -/
theorem wardA_below (c h b : ℂ) (f : ℂ → wardSequenceSpace c h) (r : ℕ)
    (hf : WardBelow f r) : WardBelow ((wardA c h b) f) r := by
  intro a j hj
  rw [wardA_apply,hf (a-1) j hj,smul_zero]

/-- If all earlier coefficients vanish, the second negative operator has
only its explicit scalar diagonal term at the current coefficient. -/
theorem wardB_diagonal (c h b : ℂ) (f : ℂ → wardSequenceSpace c h) (r : ℕ)
    (hf : WardBelow f r) (a : ℂ) :
    ((wardB c h b) f a).val r=(2*b+(a-2)-h-(r:ℂ)) • (f (a-2)).val r := by
  change wardSource c h (f (a-2)) r+_=_
  have hs : wardSource c h (f (a-2)) r=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hf (a-2) j j.isLt,map_zero]
  rw [hs,zero_add]

/-- The second negative operator also preserves initial zero segments. -/
theorem wardB_below (c h b : ℂ) (f : ℂ → wardSequenceSpace c h) (r : ℕ)
    (hf : WardBelow f r) : WardBelow ((wardB c h b) f) r := by
  intro a j hj
  rw [wardB_diagonal c h b f j (fun z i hi => hf z i (lt_trans hi hj)),hf _ j hj,smul_zero]

/-- Every generated negative operator is triangular in coefficient level.
This follows from closure under composition and commutators. -/
theorem wardNegative_below (c h b : ℂ) (n : ℕ) (f : ℂ → wardSequenceSpace c h) (r : ℕ)
    (hf : WardBelow f r) : WardBelow ((wardNegative c h b n) f) r := by
  induction n generalizing f with
  | zero => exact wardB_below c h b f r hf
  | succ n ih =>
    intro a j hj
    change ((n:ℂ)+1)⁻¹ •
      (((wardA c h b) ((wardNegative c h b n) f) a).val j-
       ((wardNegative c h b n) ((wardA c h b) f) a).val j)=0
    rw [wardA_below c h b _ r (ih f hf) a j hj,
      ih ((wardA c h b) f) (wardA_below c h b f r hf) a j hj]
    simp

/-- The scalar diagonal at negative index n+2. The sign alternates and
its zero is a real obstruction to dividing in the future triangular recursion. -/
theorem wardNegative_diagonal (c h b : ℂ) (n : ℕ) (f : ℂ → wardSequenceSpace c h) (r : ℕ)
    (hf : WardBelow f r) (a : ℂ) :
    ((wardNegative c h b n) f a).val r=
      ((-1:ℂ)^n*(((n:ℂ)+2)*b+a-((n:ℂ)+2)-h-(r:ℂ))) •
        (f (a-((n:ℂ)+2))).val r := by
  induction n generalizing f a with
  | zero =>
    rw [wardNegative_zero,wardB_diagonal c h b f r hf a]
    simp only [Nat.cast_zero,pow_zero,zero_add,one_mul]
    congr 1
    ring
  | succ n ih =>
    change ((n:ℂ)+1)⁻¹ •
      (((wardA c h b) ((wardNegative c h b n) f) a).val r-
       ((wardNegative c h b n) ((wardA c h b) f) a).val r)=_
    rw [wardA_apply,ih f hf (a-1),
      ih ((wardA c h b) f) (wardA_below c h b f r hf) a,wardA_apply]
    have hi : a-1-((n:ℂ)+2)=a-((n:ℂ)+2)-1 := by ring
    have hj : a-((n:ℂ)+2)-1=a-(((n:ℂ)+1)+2) := by ring
    simp only [hi,hj,Nat.cast_add,Nat.cast_one,pow_succ,smul_sub,smul_smul,← sub_smul]
    congr 1
    field_simp [show (n:ℂ)+1≠0 by exact_mod_cast (Nat.succ_ne_zero n)]
    <;> ring
end VOA.InverseDS.VirasoroVerma
