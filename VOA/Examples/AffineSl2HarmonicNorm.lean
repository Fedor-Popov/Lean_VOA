/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.AffineSl2NotSimple85
import VOA.Examples.AffineSl2VOAInstance
import VOA.Core.InvariantFormAdjoint
import VOA.Core.InvariantFormFHL2

/-!
# The multiplicity-free affine `sl2` harmonic norm

This file isolates the all-rank positive branch detected by the exact affine graded-unitarity
experiments.  It uses only current commutators, vacuum annihilation, and full FHL invariance.
-/

namespace VOA.AffineVOA.HarmonicNorm

open VOA.VertexOperatorAlgebra
open VOA.AffineVOA.Inst
open VOA.Sl2Sing
open VOA.Sl2NotSimple85
open VOA.WakLY

noncomputable section

/-- The highest horizontal harmonic `e_{-1}^r 1`. -/
noncomputable def eHarmonic (k : ℂ) : ℕ → WakModule k
  | 0 => vacuumA k
  | r + 1 => J k colE (-1) (eHarmonic k r)

/-- The lowest horizontal harmonic `f_{-1}^r 1`. -/
noncomputable def fHarmonic (k : ℂ) : ℕ → WakModule k
  | 0 => vacuumA k
  | r + 1 => J k colF (-1) (fHarmonic k r)

@[simp] theorem eHarmonic_zero (k : ℂ) : eHarmonic k 0 = vacuumA k := rfl

@[simp] theorem eHarmonic_succ (k : ℂ) (r : ℕ) :
    eHarmonic k (r + 1) = J k colE (-1) (eHarmonic k r) := rfl

@[simp] theorem fHarmonic_zero (k : ℂ) : fHarmonic k 0 = vacuumA k := rfl

@[simp] theorem fHarmonic_succ (k : ℂ) (r : ℕ) :
    fHarmonic k (r + 1) = J k colF (-1) (fHarmonic k r) := rfl

/-- The horizontal Cartan weight of `e_{-1}^r 1` is `2r`. -/
theorem H0_eHarmonic (k : ℂ) (r : ℕ) :
    J k colH 0 (eHarmonic k r) = (2 * (r : ℂ)) • eHarmonic k r := by
  induction r with
  | zero => simp [H_vac0]
  | succ r ih =>
      rw [eHarmonic_succ, HEs k 0 (-1) (-1) (by norm_num), ih, map_smul]
      rw [← add_smul]
      congr 1
      push_cast
      ring

/-- The lowering mode `f_1` gives the standard harmonic recurrence. -/
theorem F1_eHarmonic_succ (k : ℂ) (r : ℕ) :
    J k colF 1 (eHarmonic k (r + 1)) =
      (((r + 1 : ℕ) : ℂ) * (k - (r : ℂ))) • eHarmonic k r := by
  induction r with
  | zero =>
      simpa using F1E1 k
  | succ r ih =>
      rw [eHarmonic_succ, FEz k 1 (-1) (by norm_num), ih, map_smul,
        H0_eHarmonic]
      rw [← eHarmonic_succ k r]
      rw [← sub_smul, ← add_smul]
      congr 1
      push_cast
      ring

/-- For a weight-one quasi-primary current, full FHL invariance says that `J_{-1}` is adjoint to
`-J_1` for the invariant bilinear form. -/
theorem form_J_negOne_left {k : ℂ} (hk : k + 2 ≠ 0)
    (B : InvariantForm (affineSl2VOA_closed k hk)) (hB : B.IsFullyInvariant)
    (hqp : ∀ v, v ∈ (affineSl2VOA_closed k hk).grading 1 →
      (affineSl2VOA_closed k hk).L 1 v = 0)
    (a : Fin 3) (x y : WakModule k) :
    B.form (J k a (-1) x) y = -B.form x (J k a 1 y) := by
  have hu := currentState_mem_grading k hk a
  have hadj := adjMode_eq_fullInvariant_rhs B hB (currentState k a) hu (-1) x y
  rw [smul_currentState_eq_J] at hadj
  have hL1 : (affineSl2VOA_closed k hk).L 1 (currentState k a) = 0 := hqp _ hu
  rw [hadj]
  simp [adjMode_def, Finset.sum_range_succ, hL1, smul_currentState_eq_J]

/-- Successive lowest/highest harmonic pairings differ by the explicit linear factor
`-(r+1)(k-r)`. -/
theorem form_fHarmonic_eHarmonic_succ {k : ℂ} (hk : k + 2 ≠ 0)
    (B : InvariantForm (affineSl2VOA_closed k hk)) (hB : B.IsFullyInvariant)
    (hqp : ∀ v, v ∈ (affineSl2VOA_closed k hk).grading 1 →
      (affineSl2VOA_closed k hk).L 1 v = 0)
    (r : ℕ) :
    B.form (fHarmonic k (r + 1)) (eHarmonic k (r + 1)) =
      -(((r + 1 : ℕ) : ℂ) * (k - (r : ℂ))) *
        B.form (fHarmonic k r) (eHarmonic k r) := by
  rw [fHarmonic_succ, form_J_negOne_left hk B hB hqp, F1_eHarmonic_succ]
  simp only [map_smul, smul_eq_mul]
  ring

/-- Closed product formula for the invariant bilinear pairing of the lowest and highest
horizontal harmonics. -/
theorem form_fHarmonic_eHarmonic {k : ℂ} (hk : k + 2 ≠ 0)
    (B : InvariantForm (affineSl2VOA_closed k hk)) (hB : B.IsFullyInvariant)
    (hn : B.Normalized)
    (hqp : ∀ v, v ∈ (affineSl2VOA_closed k hk).grading 1 →
      (affineSl2VOA_closed k hk).L 1 v = 0)
    (r : ℕ) :
    B.form (fHarmonic k r) (eHarmonic k r) =
      (-1 : ℂ) ^ r * (Nat.factorial r : ℂ) *
        ∏ j ∈ Finset.range r, (k - (j : ℂ)) := by
  induction r with
  | zero =>
      simpa using hn.vacuum_self
  | succ r ih =>
      rw [form_fHarmonic_eHarmonic_succ hk B hB hqp, ih,
        Finset.prod_range_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
        Nat.cast_one, pow_succ]
      ring

/-- The diagonal obtained from the compact rule `rho(e)=-f`: the factor `(-1)^r` is precisely
the scalar contributed by applying `rho` to `e_{-1}^r 1`.  A global affine real structure is not
needed to state this one-dimensional diagonal. -/
noncomputable def compactHarmonicDiagonal {k : ℂ} {hk : k + 2 ≠ 0}
    (B : InvariantForm (affineSl2VOA_closed k hk)) (r : ℕ) : ℂ :=
  (-1 : ℂ) ^ r * B.form (fHarmonic k r) (eHarmonic k r)

/-- Exact compact harmonic norm. -/
theorem compactHarmonicDiagonal_eq {k : ℂ} (hk : k + 2 ≠ 0)
    (B : InvariantForm (affineSl2VOA_closed k hk)) (hB : B.IsFullyInvariant)
    (hn : B.Normalized)
    (hqp : ∀ v, v ∈ (affineSl2VOA_closed k hk).grading 1 →
      (affineSl2VOA_closed k hk).L 1 v = 0)
    (r : ℕ) :
    compactHarmonicDiagonal B r =
      (Nat.factorial r : ℂ) * ∏ j ∈ Finset.range r, (k - (j : ℂ)) := by
  rw [compactHarmonicDiagonal, form_fHarmonic_eHarmonic hk B hB hn hqp]
  have hsign : (-1 : ℂ) ^ r * (-1 : ℂ) ^ r = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc
    (-1 : ℂ) ^ r *
        ((-1 : ℂ) ^ r * (Nat.factorial r : ℂ) *
          ∏ j ∈ Finset.range r, (k - (j : ℂ))) =
        ((-1 : ℂ) ^ r * (-1 : ℂ) ^ r) *
          ((Nat.factorial r : ℂ) * ∏ j ∈ Finset.range r, (k - (j : ℂ))) := by ring
    _ = (Nat.factorial r : ℂ) * ∏ j ∈ Finset.range r, (k - (j : ℂ)) := by
      rw [hsign, one_mul]

/-- Moving the sign into every factor reverses all `k-j` factors. -/
theorem neg_one_pow_mul_prod_sub (k : ℂ) (r : ℕ) :
    (-1 : ℂ) ^ r * ∏ j ∈ Finset.range r, (k - (j : ℂ)) =
      ∏ j ∈ Finset.range r, ((j : ℂ) - k) := by
  symm
  calc
    (∏ j ∈ Finset.range r, ((j : ℂ) - k)) =
        ∏ j ∈ Finset.range r, -(k - (j : ℂ)) := by
      apply Finset.prod_congr rfl
      intro j _
      ring
    _ = (-1 : ℂ) ^ r * ∏ j ∈ Finset.range r, (k - (j : ℂ)) := by
      simpa using
        (Finset.prod_neg (s := Finset.range r) (f := fun j : ℕ => k - (j : ℂ)))

/-- After the corrected sign `(-1)^r`, the compact diagonal at a real level is a product of the
positive candidates `j-k`. -/
theorem signed_compactHarmonicDiagonal_eq_real {k : ℝ}
    (hk : (k : ℂ) + 2 ≠ 0)
    (B : InvariantForm (affineSl2VOA_closed (k : ℂ) hk)) (hB : B.IsFullyInvariant)
    (hn : B.Normalized)
    (hqp : ∀ v, v ∈ (affineSl2VOA_closed (k : ℂ) hk).grading 1 →
      (affineSl2VOA_closed (k : ℂ) hk).L 1 v = 0)
    (r : ℕ) :
    (-1 : ℂ) ^ r * compactHarmonicDiagonal B r =
      (((Nat.factorial r : ℝ) * ∏ j ∈ Finset.range r, ((j : ℝ) - k) : ℝ) : ℂ) := by
  rw [compactHarmonicDiagonal_eq hk B hB hn hqp]
  push_cast
  calc
    (-1 : ℂ) ^ r *
        ((Nat.factorial r : ℂ) * ∏ j ∈ Finset.range r, ((k : ℂ) - (j : ℂ))) =
        (Nat.factorial r : ℂ) *
          ((-1 : ℂ) ^ r * ∏ j ∈ Finset.range r, ((k : ℂ) - (j : ℂ))) := by ring
    _ = (Nat.factorial r : ℂ) *
        ∏ j ∈ Finset.range r, ((j : ℂ) - (k : ℂ)) := by
      rw [neg_one_pow_mul_prod_sub]

/-- For every negative real level, the corrected compact harmonic diagonal is strictly positive
as a real scalar. -/
theorem signed_compactHarmonicDiagonal_real_pos {k : ℝ} (hkneg : k < 0) (r : ℕ) :
    0 < (Nat.factorial r : ℝ) * ∏ j ∈ Finset.range r, ((j : ℝ) - k) := by
  apply mul_pos
  · exact_mod_cast Nat.factorial_pos r
  · apply Finset.prod_pos
    intro j _
    exact sub_pos.mpr (lt_of_lt_of_le hkneg (Nat.cast_nonneg j))

/-- The product formula specialized to the canonical normalized invariant form. -/
theorem canonical_compactHarmonicDiagonal_eq {k : ℂ} (hk : k + 2 ≠ 0)
    (hne : (affineSl2VOA_closed k hk).vacuum ≠ 0)
    (hqp : ∀ v, v ∈ (affineSl2VOA_closed k hk).grading 1 →
      (affineSl2VOA_closed k hk).L 1 v = 0)
    (r : ℕ) :
    compactHarmonicDiagonal (canonicalInvariantForm hne hqp) r =
      (Nat.factorial r : ℂ) * ∏ j ∈ Finset.range r, (k - (j : ℂ)) :=
  compactHarmonicDiagonal_eq hk (canonicalInvariantForm hne hqp)
    (canonicalInvariantForm_isFullyInvariant hne hqp)
    (canonicalInvariantForm_normalized hne hqp) hqp r

/-- Packaged canonical harmonic signed positivity at a negative real noncritical level.  The
first conjunct is the exact complex diagonal identity; the second is its strictly positive real
value. -/
theorem canonical_signed_compactHarmonicDiagonal_eq_and_pos {k : ℝ} (hkneg : k < 0)
    (hk : (k : ℂ) + 2 ≠ 0)
    (hne : (affineSl2VOA_closed (k : ℂ) hk).vacuum ≠ 0)
    (hqp : ∀ v, v ∈ (affineSl2VOA_closed (k : ℂ) hk).grading 1 →
      (affineSl2VOA_closed (k : ℂ) hk).L 1 v = 0)
    (r : ℕ) :
    (-1 : ℂ) ^ r *
        compactHarmonicDiagonal (canonicalInvariantForm hne hqp) r =
          (((Nat.factorial r : ℝ) *
            ∏ j ∈ Finset.range r, ((j : ℝ) - k) : ℝ) : ℂ) ∧
      0 < (Nat.factorial r : ℝ) * ∏ j ∈ Finset.range r, ((j : ℝ) - k) := by
  constructor
  · exact signed_compactHarmonicDiagonal_eq_real hk
      (canonicalInvariantForm hne hqp)
      (canonicalInvariantForm_isFullyInvariant hne hqp)
      (canonicalInvariantForm_normalized hne hqp) hqp r
  · exact signed_compactHarmonicDiagonal_real_pos hkneg r

/-- The canonical compact harmonic diagonal at the Lee--Yang partner level `k=-8/5`. -/
theorem canonical_compactHarmonicDiagonal85_eq (r : ℕ) :
    compactHarmonicDiagonal (canonicalInvariantForm vacuum85_ne_zero qp85) r =
      (Nat.factorial r : ℂ) *
        ∏ j ∈ Finset.range r, ((-8 / 5 : ℂ) - (j : ℂ)) :=
  canonical_compactHarmonicDiagonal_eq hk85 vacuum85_ne_zero qp85 r

/-- Unconditional all-rank signed positivity of the canonical harmonic diagonal at `k=-8/5`. -/
theorem canonical_signed_compactHarmonicDiagonal85_eq_and_pos (r : ℕ) :
    (-1 : ℂ) ^ r *
        compactHarmonicDiagonal (canonicalInvariantForm vacuum85_ne_zero qp85) r =
          (((Nat.factorial r : ℝ) *
            ∏ j ∈ Finset.range r, ((j : ℝ) - (-8 / 5 : ℝ)) : ℝ) : ℂ) ∧
      0 < (Nat.factorial r : ℝ) *
        ∏ j ∈ Finset.range r, ((j : ℝ) - (-8 / 5 : ℝ)) := by
  constructor
  · rw [canonical_compactHarmonicDiagonal85_eq]
    push_cast
    calc
      (-1 : ℂ) ^ r *
          ((Nat.factorial r : ℂ) *
            ∏ j ∈ Finset.range r, ((-8 / 5 : ℂ) - (j : ℂ))) =
          (Nat.factorial r : ℂ) *
            ((-1 : ℂ) ^ r *
              ∏ j ∈ Finset.range r, ((-8 / 5 : ℂ) - (j : ℂ))) := by ring
      _ = (Nat.factorial r : ℂ) *
          ∏ j ∈ Finset.range r, ((j : ℂ) - (-8 / 5 : ℂ)) := by
        rw [neg_one_pow_mul_prod_sub]
  · exact signed_compactHarmonicDiagonal_real_pos (k := (-8 / 5 : ℝ)) (by norm_num) r

end

end VOA.AffineVOA.HarmonicNorm
