/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Foundations.AffineLie
import Mathlib.Algebra.Lie.Classical
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The actual matrix Lie algebra for the affine sl3 rigidity project

We use trace-zero three by three matrices, so the Lie identities are inherited
from matrix commutators. The form is tr(XY), with root-vector pairing one and
Cartan matrix [[2,-1],[-1,2]]. These normalizations specify the affine level.
This module constructs neither a VOA nor an admissible-level determinant root.
-/
namespace VOA.AffineSl3
noncomputable section
open LieAlgebra.SpecialLinear

/-- The concrete complex Lie algebra of trace-zero three by three matrices. -/
abbrev Sl3 := LieAlgebra.SpecialLinear.sl (Fin 3) ℂ

/-- The first positive simple-root vector is the matrix unit E12. -/
def e1 : Sl3 := single 0 1 (by decide) 1
/-- The second positive simple-root vector is E23. -/
def e2 : Sl3 := single 1 2 (by decide) 1
/-- The highest-root vector is E13, with sign fixed by [e1,e2]. -/
def e12 : Sl3 := single 0 2 (by decide) 1
/-- The first negative simple-root vector is E21. -/
def f1 : Sl3 := single 1 0 (by decide) 1
/-- The second negative simple-root vector is E32. -/
def f2 : Sl3 := single 2 1 (by decide) 1
/-- The negative highest-root vector is E31, with sign fixed by [f2,f1]. -/
def f12 : Sl3 := single 2 0 (by decide) 1
/-- The first simple coroot is diag(1,-1,0). -/
def h1 : Sl3 := singleSubSingle 0 1 1
/-- The second simple coroot is diag(0,1,-1). -/
def h2 : Sl3 := singleSubSingle 1 2 1

/-- The normalized invariant bilinear form is the ordinary trace of XY,
not the Hermitian trace of the conjugate transpose times Y. -/
def form : LinearMap.BilinForm ℂ Sl3 where
  toFun x :=
    { toFun := fun y => Matrix.trace (x.val * y.val)
      map_add' := by intros; simp [Matrix.mul_add, Matrix.trace_add]
      map_smul' := by intros; simp }
  map_add' := by intros; ext; simp [Matrix.add_mul, Matrix.trace_add]
  map_smul' := by intros; ext; simp

/-- Evaluation of the form is literally the trace in the defining representation. -/
theorem form_apply (x y : Sl3) : form x y = Matrix.trace (x.val * y.val) := rfl

/-- Cyclicity of matrix trace proves symmetry and Lie invariance of the level form. -/
theorem form_invariant : form.IsInvariant where
  symm x y := by
    change Matrix.trace (x.val * y.val) = Matrix.trace (y.val * x.val)
    exact Matrix.trace_mul_comm _ _
  invariant x y z := by
    simp only [form_apply, sl_bracket, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]
    rw [Matrix.mul_assoc]
    congr 1
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm y.val (x.val * z.val), Matrix.mul_assoc]

/-- The positive simple-root bracket fixes the highest-root sign. -/
theorem e1_e2 : ⁅e1, e2⁆ = e12 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl_bracket, Ring.lie_def, e1, e2, e12, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single, Fin.reduceFinMk, Fin.mk.injEq,
    show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]

/-- Negative-root signs are chosen so that [f2,f1]=f12. -/
theorem f2_f1 : ⁅f2, f1⁆ = f12 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl_bracket, Ring.lie_def, f1, f2, f12, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single, Fin.reduceFinMk, Fin.mk.injEq,
    show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]

/-- The first simple-root pair has coroot h1. -/
theorem e1_f1 : ⁅e1, f1⁆ = h1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl_bracket, Ring.lie_def, e1, f1, h1, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single, Fin.reduceFinMk, Fin.mk.injEq,
    show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]

/-- The second simple-root pair has coroot h2. -/
theorem e2_f2 : ⁅e2, f2⁆ = h2 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl_bracket, Ring.lie_def, e2, f2, h2, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single, Fin.reduceFinMk, Fin.mk.injEq,
    show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]

/-- The highest-root pair has coroot h1+h2. -/
theorem e12_f12 : ⁅e12, f12⁆ = h1 + h2 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl_bracket, Ring.lie_def, e12, f12, h1, h2, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single, Fin.reduceFinMk, Fin.mk.injEq,
    show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]

/-- Ordered Chevalley generators: the three positive roots, their negatives,
then the two simple coroots. -/
def generator : Fin 8 → Sl3 := ![e1, e2, e12, f1, f2, f12, h1, h2]

/-- Coordinates in this ordered family. The second Cartan coefficient is
minus the last diagonal entry, using the trace-zero condition. -/
def coordinates (x : Sl3) : Fin 8 → ℂ :=
  ![x.val 0 1, x.val 1 2, x.val 0 2, x.val 1 0, x.val 2 1, x.val 2 0,
    x.val 0 0, -x.val 2 2]

/-- Coordinate extraction is complex linear. -/
def coordinatesLinear : Sl3 →ₗ[ℂ] (Fin 8 → ℂ) where
  toFun := coordinates
  map_add' x y := by ext i; fin_cases i <;> simp [coordinates] <;> ring
  map_smul' a x := by ext i; fin_cases i <;> simp [coordinates] <;> ring

/-- Each generator has its corresponding unit coordinate vector. -/
theorem coordinates_generator (i : Fin 8) :
    coordinates (generator i) = Pi.single i 1 := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [coordinates, generator, e1, e2, e12, f1, f2, f12, h1, h2,
      Matrix.single, Pi.single_apply]

/-- Every trace-zero matrix is exactly reconstructed from the eight coordinates;
this is spanning, with no abstract PBW premise. -/
theorem reconstruct (x : Sl3) : ∑ i, coordinates x i • generator i = x := by
  have ht : x.val 0 0 + x.val 1 1 + x.val 2 2 = 0 := by
    have hx := x.property
    change Matrix.trace x.val = 0 at hx
    simpa [Matrix.trace, Fin.sum_univ_three, add_assoc] using hx
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_succ, coordinates, generator, e1, e2, e12, f1, f2, f12,
      h1, h2, Matrix.single] <;> linear_combination -ht

/-- The eight matrix coordinates give an explicit linear equivalence with C^8. -/
def coordinateEquiv : Sl3 ≃ₗ[ℂ] (Fin 8 → ℂ) :=
  { coordinatesLinear with
    invFun := fun v => ∑ i, v i • generator i
    left_inv := reconstruct
    right_inv := fun v => by
      change coordinatesLinear (∑ i, v i • generator i) = v
      rw [map_sum]
      simp only [map_smul]
      change (∑ i, v i • coordinates (generator i)) = v
      simp_rw [coordinates_generator]
      ext j
      simp [Pi.single_apply] }

/-- A genuine eight-element basis of the actual trace-zero Lie algebra. -/
def chevalleyBasis : Module.Basis (Fin 8) ℂ Sl3 := Module.Basis.ofEquivFun coordinateEquiv

/-- The defining Lie algebra has complex dimension eight. -/
theorem finrank_sl3 : Module.finrank ℂ Sl3 = 8 := by
  simpa using Module.finrank_eq_card_basis chevalleyBasis

/-- All root-vector pairings are normalized to one. This fixes the level scale. -/
theorem root_pairings : form e1 f1 = 1 ∧ form e2 f2 = 1 ∧ form e12 f12 = 1 := by
  simp [form_apply, e1, e2, e12, f1, f2, f12, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_three, Matrix.single, Fin.reduceFinMk, Fin.mk.injEq,
    show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]

/-- The Gram matrix on the simple coroots is the A2 Cartan matrix. -/
theorem cartan_pairings : form h1 h1 = 2 ∧ form h1 h2 = -1 ∧ form h2 h2 = 2 := by
  norm_num [form_apply, h1, h2, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_three, Matrix.single, Fin.reduceFinMk, Fin.mk.injEq,
    show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]

/-- Affinization of this actual Lie algebra with the proved invariant form. -/
abbrev Algebra := VOA.AffineLie Sl3 form form_invariant

/-- The loop generator at Fourier index m, in the actual central extension. -/
abbrev current (x : Sl3) (m : ℤ) : Algebra :=
  VOA.AffineLie.ofLoop form form_invariant x m

/-- The actual current bracket has matrix-commutator term and the normalized
trace cocycle. This does not assume the existence of any vacuum representation. -/
theorem current_bracket (x y : Sl3) (m n : ℤ) :
    ⁅current x m, current y n⁆ = current ⁅x,y⁆ (m+n) +
      (if m+n=0 then ((m : ℂ)*form x y) •
        VOA.AffineLie.C form form_invariant else 0) :=
  VOA.AffineLie.affine_bracket form form_invariant x y m n

end
end VOA.AffineSl3
