/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2UniformObstruction

/-!
# The constructed affine polynomial Gram matrix is the actual ordinary form

The normalized canonical form on the universal vacuum module and the form on
its simple quotient have identical vacuum functionals. Current adjointness
then proves equality on arbitrary word pairings. Hence the
constructed level polynomials are genuine universal Gram entries, not merely
polynomials attached to the quotient or to a hypothetical deformation.
-/
namespace VOA.AffineSl2GeneralRigidity
open AffineVOA AffineVOA.Inst Deform VertexOperatorAlgebra
open Module (End)
variable (k : ℂ) (hk : k + 2 ≠ 0)
local notation "I" => QuotVOA.maxGradedIdeal (universal k hk)

/-- The actual normalized canonical form on the universal affine VOA. Vacuum
nonvanishing uses the proved concrete PBW basis, not a project PBW axiom. -/
noncomputable def universalForm : InvariantForm (universal k hk) :=
  canonicalInvariantForm (AffineSl2BoundaryMaximalIdeal.affineSl2_vacuum_ne_zero k hk)
    (LQ43.L1_grading_one k hk)

/-- Universal and quotient vacuum pairings agree on every state: positive
or negative nonzero grades pair to zero, and grade zero is the vacuum line. -/
theorem vacuum_pairing_mkQ (x : WakModule k) :
    (simpleForm k hk).form (simple k hk).vacuum ((I).mkQ x) =
      (universalForm k hk).form (universal k hk).vacuum x := by
  have hx : x ∈ ⨆ n, (universal k hk).grading n := by
    rw [(universal k hk).isInternal.submodule_iSup_eq_top]; trivial
  refine Submodule.iSup_induction (universal k hk).grading
    (motive := fun y => (simpleForm k hk).form (simple k hk).vacuum ((I).mkQ y) =
      (universalForm k hk).form (universal k hk).vacuum y) hx ?_ ?_ ?_
  · intro n y hy
    by_cases hn : n = 0
    · subst n
      have he := eq_vacCoord_smul_of_mem_zero (universal k hk)
        (AffineSl2BoundaryMaximalIdeal.affineSl2_vacuum_ne_zero k hk) hy
      rw [he]
      simp only [map_smul, smul_eq_mul]
      change _ * (simpleForm k hk).form (simple k hk).vacuum (simple k hk).vacuum = _
      rw [simpleForm_normalized k hk]
      change _ * 1 = _ * (canonicalInvariantForm
        (AffineSl2BoundaryMaximalIdeal.affineSl2_vacuum_ne_zero k hk)
        (LQ43.L1_grading_one k hk)).form _ _
      rw [
        canonicalInvariantForm_normalized
          (AffineSl2BoundaryMaximalIdeal.affineSl2_vacuum_ne_zero k hk)
          (LQ43.L1_grading_one k hk)]
    · have hq : (I).mkQ y ∈ (simple k hk).grading n :=
        Submodule.mem_map.mpr ⟨y,hy,rfl⟩
      rw [(simpleForm k hk).orthogonal_of_ne (Ne.symm hn) (simple k hk).vacuum_mem hq,
        (universalForm k hk).orthogonal_of_ne (Ne.symm hn) (universal k hk).vacuum_mem hy]
  · simp
  · intro a b ea eb
    simp only [map_add, ea, eb]

/-- Quotient projection intertwines every finite universal current word,
including words that contain zero or positive modes. -/
theorem universalWord_mkQ (w : List (Fin 3 × ℤ)) (x : WakModule k) :
    (I).mkQ (NormalOrdering.currentWord (J k) w x) = currentWord k hk w ((I).mkQ x) := by
  induction w with
  | nil => rfl
  | cons an w ih =>
    simp only [NormalOrdering.currentWord, currentWord, Module.End.mul_apply]
    rw [← simpleCurrent_mode_mkQ, ih]
    rfl

/-- Current adjointness determines every universal word pairing from its
vacuum functional. Thus passing to the actual simple quotient preserves the
canonical bilinear pairing, even when the universal form is degenerate. -/
theorem universalWord_pairing_mkQ (w : List (Fin 3 × ℤ)) (y : WakModule k) :
    (universalForm k hk).form
      (NormalOrdering.currentWord (J k) w (universal k hk).vacuum) y =
    (simpleForm k hk).form (currentWord k hk w (simple k hk).vacuum) ((I).mkQ y) := by
  have hU : (universalForm k hk).IsFullyInvariant :=
    canonicalInvariantForm_isFullyInvariant
      (AffineSl2BoundaryMaximalIdeal.affineSl2_vacuum_ne_zero k hk) (LQ43.L1_grading_one k hk)
  have hS : (simpleForm k hk).IsFullyInvariant :=
    canonicalInvariantForm_isFullyInvariant (simple_vacuum_ne_zero k hk) (simple_quasiPrimary k hk)
  induction w generalizing y with
  | nil => exact (vacuum_pairing_mkQ k hk y).symm
  | cons an w ih =>
    change (universalForm k hk).form
      (J k an.1 an.2 (NormalOrdering.currentWord (J k) w (universal k hk).vacuum)) y =
      (simpleForm k hk).form ((simple k hk).smul (simpleCurrent k hk an.1) an.2
        (currentWord k hk w (simple k hk).vacuum)) ((I).mkQ y)
    rw [← smul_currentState_eq_J k hk]
    rw [LQ43.weightOne_adj hU (currentState_mem_grading k hk an.1)
      (LQ43.L1_grading_one k hk _ (currentState_mem_grading k hk an.1))]
    rw [LQ43.weightOne_adj hS (simpleCurrent_mem k hk an.1)
      (simple_quasiPrimary k hk _ (simpleCurrent_mem k hk an.1))]
    rw [ih, smul_currentState_eq_J, simpleCurrent_mode_mkQ]

/-- The universal polynomial Gram entry agrees with the actual canonical
universal form at every nonzero noncritical level, with its exact normalization. -/
theorem wordGramPolynomial_universal (hk0 : k ≠ 0) (u v : List (Fin 3 × ℤ)) :
    (wordGramPolynomial u v).eval k = (universalForm k hk).form
      (NormalOrdering.currentWord (J k) u (universal k hk).vacuum)
      (NormalOrdering.currentWord (J k) v (universal k hk).vacuum) := by
  rw [universalWord_pairing_mkQ, universalWord_mkQ, wordGramPolynomial_eval k hk hk0]
  rfl

/-- The polynomial Gram matrix of any finite family of literal current words.
Choosing a joint energy/Cartan-weight family is allowed; no basis or determinant
nonvanishing is asserted by this definition. -/
noncomputable def wordGramMatrix {ι κ : Type*}
    (u : ι → List (Fin 3 × ℤ)) (v : κ → List (Fin 3 × ℤ)) :
    Matrix ι κ (Polynomial ℂ) := fun i j => wordGramPolynomial (u i) (v j)

/-- Entrywise evaluation gives the actual universal Gram matrix on the chosen
row and column words. In particular no normalization factor is left unspecified. -/
theorem wordGramMatrix_eval (hk0 : k ≠ 0) {ι κ : Type*}
    (u : ι → List (Fin 3 × ℤ)) (v : κ → List (Fin 3 × ℤ)) :
    (wordGramMatrix u v).map (Polynomial.eval k) = fun i j =>
      (universalForm k hk).form
        (NormalOrdering.currentWord (J k) (u i) (universal k hk).vacuum)
        (NormalOrdering.currentWord (J k) (v j) (universal k hk).vacuum) := by
  ext i j
  exact wordGramPolynomial_universal k hk hk0 (u i) (v j)

end VOA.AffineSl2GeneralRigidity
