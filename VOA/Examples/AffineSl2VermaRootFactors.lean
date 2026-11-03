/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2VermaDescendantGrading
import VOA.Examples.VirasoroGramDivisibility

/-!
# Unconditional real-root factors of actual affine Verma determinants

Screening roots give actual radical vectors. Their full occupation families
of descendants are independent, and their coordinates are actual Gram null
rows. Thus both real-root families have the expected descendant lower
multiplicities. No Kac factorization or simple vacuum root is assumed here.
-/
namespace VOA.AffineVOA.HighestModule
open Module (End)
open Wak.Charged (Occupation JointIndex)
noncomputable section
local instance (n : ℕ) (c : ℤ) : Fintype (JointIndex n c) := Wak.Charged.jointIndexFintype n c
local instance (n : ℕ) (c : ℤ) : DecidableEq (JointIndex n c) := Classical.decEq _

/-- Fix the level and leave highest weight as the ordinary polynomial X
in the actual two-parameter Gram matrix. -/
def weightGramPolynomial (k : ℂ) (n : ℕ) (c : ℤ) :
    Matrix (JointIndex n c) (JointIndex n c) (Polynomial ℂ) :=
  (Wak.Charged.highestGramPolynomial n c).map
    (MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.C k,Polynomial.X])

/-- The actual highest-weight determinant polynomial at fixed central level. -/
def weightDeterminant (k : ℂ) (n : ℕ) (c : ℤ) : Polynomial ℂ :=
  (weightGramPolynomial k n c).det

/-- Substitution into the weight-polynomial matrix gives exactly the
canonical actual Verma form matrix at that weight. -/
theorem weightGramPolynomial_eval (k h : ℂ) (n : ℕ) (c : ℤ) :
    (weightGramPolynomial k n c).map (Polynomial.eval h)=gramMatrix k h n c := by
  rw [← highestGramPolynomial_verma]
  ext i j
  change Polynomial.evalRingHom h (MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.C k,Polynomial.X] _)=_
  rw [MvPolynomial.map_eval₂Hom]
  have hc : (Polynomial.evalRingHom h).comp Polynomial.C=RingHom.id ℂ := by ext z; simp
  rw [hc]
  have hx : (fun a : Fin 2 => Polynomial.evalRingHom h (![Polynomial.C k,Polynomial.X] a))=![k,h] := by
    funext a
    fin_cases a <;> simp
  rw [hx]
  rfl

/-- Actual coordinates of a radical descendant annihilate every column
of the evaluated highest-weight Gram polynomial matrix. -/
theorem jointDescendant_null_row (k h : ℂ) (n m : ℕ) (c d : ℤ)
    (v : jointSpace k h n c) (hv : contravariant k h v=0)
    (i : JointIndex m d) (j : JointIndex (n+m) (c+d)) :
    ∑ e,(jointBasis k h (n+m) (c+d)).equivFun (jointDescendant k h n m c d v i) e *
      (weightGramPolynomial k (n+m) (c+d) e j).eval h=0 := by
  let b := jointBasis k h (n+m) (c+d)
  have he : ∀ e,(weightGramPolynomial k (n+m) (c+d) e j).eval h=
      contravariant k h (b e : Verma k h) (b j : Verma k h) := by
    intro e
    have hh := congrArg (fun A => A e j) (weightGramPolynomial_eval k h (n+m) (c+d))
    simpa only [Matrix.map_apply,gramMatrix,b,jointBasis_apply] using hh
  simp_rw [he]
  have hs := congrArg (jointSpace k h (n+m) (c+d)).subtype
    (b.sum_equivFun (jointDescendant k h n m c d v i))
  simp only [map_sum,map_smul] at hs
  have hh := congrArg (fun u => contravariant k h u (b j : Verma k h)) hs
  have hz := LinearMap.congr_fun (descendant_radical k h (Wak.Charged.occupationWord i.val) v hv) (b j)
  simpa only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,smul_eq_mul,
    LinearMap.zero_apply,jointDescendant] using hh.trans hz

/-- A nonzero actual radical vector forces the FULL occupation descendant
multiplicity in every higher joint determinant. Singularity is unnecessary
for this lower bound, because the radical itself is mode-stable. -/
theorem weightDeterminant_factor_of_radical (k h : ℂ) (n m : ℕ) (c d : ℤ)
    (v : jointSpace k h n c) (hne : v≠0) (hv : contravariant k h v=0) :
    (Polynomial.X-Polynomial.C h)^(Fintype.card (JointIndex m d)) ∣
      weightDeterminant k (n+m) (c+d) := by
  classical
  have hi := (jointDescendants_independent k h n m c d v hne).map'
    (jointBasis k h (n+m) (c+d)).equivFun.toLinearMap
    (LinearMap.ker_eq_bot.mpr (jointBasis k h (n+m) (c+d)).equivFun.injective)
  exact VirDeformModes.NormalOrdering.pow_X_sub_C_dvd_det_of_independent_null_rows _ h _ hi
    (fun i j => jointDescendant_null_row k h n m c d v hv i j)

/-- Every positive real-root Kac label supplies its expected descendant
factor at EVERY complex parameter. All representation inputs are proved
by screening, actual Gram identification and descendant independence. -/
theorem weightDeterminant_positive_factor (r q m : ℕ) (hr : 0<r) (hq : 0<q)
    (d : ℤ) (t : ℂ) :
    (Polynomial.X-Polynomial.C ((q : ℂ)*t-r-1))^(Fintype.card (JointIndex m d)) ∣
      weightDeterminant (t-2) (r*q+m) ((r : ℤ)+d) := by
  obtain ⟨v,hne,hv,hr⟩ := kac_positive_nonzero_radical r q hr hq t
  exact weightDeterminant_factor_of_radical (t-2) _ (r*q) m (r : ℤ) d ⟨v,hv⟩
    (fun he => hne (congrArg Subtype.val he)) hr

/-- Every opposite real-root Kac label has the full descendant lower
multiplicity, including the horizontal q=0 factors. This is still a
factor-divisibility result, not yet exhaustion or a vacuum simple-root theorem. -/
theorem weightDeterminant_negative_factor (r q m : ℕ) (hr : 0<r) (d : ℤ) (t : ℂ) :
    (Polynomial.X-Polynomial.C ((r : ℂ)-1-q*t))^(Fintype.card (JointIndex m d)) ∣
      weightDeterminant (t-2) (r*q+m) (-(r : ℤ)+d) := by
  obtain ⟨v,hne,hv,hr⟩ := kac_negative_nonzero_radical r q hr t
  exact weightDeterminant_factor_of_radical (t-2) _ (r*q) m (-(r : ℤ)) d ⟨v,hv⟩
    (fun he => hne (congrArg Subtype.val he)) hr

end
end VOA.AffineVOA.HighestModule
