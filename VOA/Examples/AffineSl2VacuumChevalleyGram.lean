/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2VacuumFormComparison
import VOA.Examples.AffineSl2VacuumDeterminantCoefficient
import VOA.Examples.AffineSl2JointSimpleRoot

/-!
# The vacuum Chevalley Gram polynomial in the actual VOA convention

The fixed colour involution turns every row into an ordinary current word,
with one minus sign for each letter. Polynomial equality follows from the
actual normalized forms at infinitely many noncritical levels.
-/
namespace VOA.AffineSl2GeneralRigidity
open AffineVOA AffineVOA.HighestModule
noncomputable section

/-- Flip every current colour, keeping its mode and word order unchanged. -/
def flipCurrentWord (w : List (Fin 3×ℤ)) : List (Fin 3×ℤ) :=
  w.map (fun an => (adjointColour an.1,an.2))

/-- The actual involution on a current word has precisely one minus sign
per letter, with no reordering or lower-word correction. -/
theorem vacuumChevalley_word (k : ℂ) (w : List (Fin 3×ℤ)) :
    vacuumChevalley k (NormalOrdering.currentWord (J k) w (vacuumA k))=
      ((-1 : ℂ)^w.length) • NormalOrdering.currentWord (J k) (flipCurrentWord w) (vacuumA k) := by
  induction w with
  | nil => simp only [NormalOrdering.currentWord,Module.End.one_apply,
      vacuumChevalley_vacuum,List.length_nil,pow_zero,one_smul,flipCurrentWord,List.map_nil]
  | cons an w ih =>
    simp only [NormalOrdering.currentWord,Module.End.mul_apply,flipCurrentWord,List.map_cons,
      List.length_cons,vacuumChevalley_current,ih,map_smul,pow_succ,neg_smul,smul_smul]
    simp [mul_comm]

/-- The twisted canonical form is symmetric, because it is the actual
symmetric weight-zero Verma form pulled through a surjective projection. -/
theorem vacuumChevalley_form_symm (k : ℂ) (hk : k+2≠0) (x y : WakModule k) :
    (universalForm k hk).form (vacuumChevalley k x) y=
      (universalForm k hk).form (vacuumChevalley k y) x := by
  obtain ⟨u,rfl⟩ := vacuumProjection_surjective k x
  obtain ⟨v,rfl⟩ := vacuumProjection_surjective k y
  rw [← contravariant_vacuum_form,← contravariant_vacuum_form]
  exact contravariant_symm k 0 u v

/-- Each Chevalley polynomial entry evaluates to its actual twisted
canonical VOA pairing, at every noncritical level. -/
theorem vacuumChevalleyPolynomial_actual (k : ℂ) (hk : k+2≠0) (n : ℕ) (c : ℤ)
    (i j : JointIndex n (2*c)) :
    (vacuumChevalleyPolynomial n c i j).eval k=
      (universalForm k hk).form (vacuumChevalley k (currentPBWBasis k hk i.val))
        (currentPBWBasis k hk j.val) := by
  rw [vacuumChevalleyPolynomial_eval,contravariant_vacuum_form k hk,
    vacuumProjection_lift k hk,vacuumProjection_lift k hk]

/-- There are infinitely many nonzero noncritical levels where actual
pairing evaluation can identify a central polynomial. -/
theorem polynomial_eq_of_nonzero_noncritical (P Q : Polynomial ℂ)
    (h : ∀k : ℂ,k≠0 → k+2≠0 → P.eval k=Q.eval k) : P=Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hinj : Function.Injective (fun n : ℕ => (n : ℂ)+1) := by
    intro n m he
    exact_mod_cast add_right_cancel he
  apply (Set.infinite_range_of_injective hinj).mono
  rintro k ⟨n,rfl⟩
  apply h
  · change (n : ℂ)+1≠0
    exact_mod_cast (show (n : ℤ)+1≠0 by omega)
  · change ((n : ℂ)+1)+2≠0
    exact_mod_cast (show ((n : ℤ)+1)+2≠0 by omega)

/-- The central Chevalley entry is exactly an ordinary universal word
pairing polynomial with its explicit row sign. This is the polynomial
used by the actual graded deformation obstruction. -/
theorem vacuumChevalleyPolynomial_word (n : ℕ) (c : ℤ)
    (i j : JointIndex n (2*c)) :
    vacuumChevalleyPolynomial n c i j=
      ((-1 : ℂ)^(jointWord n (2*c) i).length) •
        wordGramPolynomial (flipCurrentWord (jointWord n (2*c) i)) (jointWord n (2*c) j) := by
  apply polynomial_eq_of_nonzero_noncritical
  intro k hk0 hk
  rw [vacuumChevalleyPolynomial_actual k hk,Polynomial.eval_smul,
    wordGramPolynomial_universal k hk hk0,← jointWord_state k hk n (2*c) i,
    ← jointWord_state k hk n (2*c) j]
  change (universalForm k hk).form
    (vacuumChevalley k (NormalOrdering.currentWord (J k) _ (vacuumA k))) _=_
  rw [vacuumChevalley_word,map_smul,LinearMap.smul_apply]
  rfl

end
end VOA.AffineSl2GeneralRigidity
