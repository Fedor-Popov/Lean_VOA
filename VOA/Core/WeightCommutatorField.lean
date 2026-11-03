/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Core.FieldOps

/-!
# Fields homogeneous for a weight operator

This operator-first predicate says that the coefficient `a j` has degree `D+j` for a fixed
endomorphism `W`.  It is the precise amount of grading structure needed by current realizations:
no positivity, finite-dimensionality, or vertex-algebra instance is required.  The main result is
closure under the normal product.
-/

namespace VOA

open Module (End)

noncomputable section

universe u

variable {A : Type u} [AddCommGroup A] [Module ℂ A]

/-- A formal field whose coefficient `j` has degree `D+j` for the operator `W`. -/
def WeightCommutatorField (W : End ℂ A) (a : FormalDist (End ℂ A)) (D : ℤ) : Prop :=
  ∀ j : ℤ, W * a j - a j * W = ((D + j : ℤ) : ℂ) • a j

namespace WeightCommutatorField

theorem add {W : End ℂ A} {a b : FormalDist (End ℂ A)} {D : ℤ}
    (ha : WeightCommutatorField W a D) (hb : WeightCommutatorField W b D) :
    WeightCommutatorField W (a + b) D := by
  intro j
  change W * (a j + b j) - (a j + b j) * W =
    ((D + j : ℤ) : ℂ) • (a j + b j)
  calc
    W * (a j + b j) - (a j + b j) * W =
        (W * a j - a j * W) + (W * b j - b j * W) := by
          rw [mul_add, add_mul]
          abel
    _ = ((D + j : ℤ) : ℂ) • a j + ((D + j : ℤ) : ℂ) • b j := by
      rw [ha j, hb j]
    _ = ((D + j : ℤ) : ℂ) • (a j + b j) := (smul_add _ _ _).symm

theorem smul {W : End ℂ A} {a : FormalDist (End ℂ A)} {D : ℤ}
    (ha : WeightCommutatorField W a D) (r : ℂ) :
    WeightCommutatorField W (r • a) D := by
  intro j
  change W * (r • a j) - (r • a j) * W =
    ((D + j : ℤ) : ℂ) • (r • a j)
  calc
    W * (r • a j) - (r • a j) * W = r • (W * a j - a j * W) := by
      rw [mul_smul_comm, smul_mul_assoc, smul_sub]
    _ = r • (((D + j : ℤ) : ℂ) • a j) := by rw [ha j]
    _ = ((D + j : ℤ) : ℂ) • (r • a j) := by module

theorem neg {W : End ℂ A} {a : FormalDist (End ℂ A)} {D : ℤ}
    (ha : WeightCommutatorField W a D) : WeightCommutatorField W (-a) D := by
  simpa only [neg_one_smul] using ha.smul (-1)

theorem deriv {W : End ℂ A} {a : FormalDist (End ℂ A)} {D : ℤ}
    (ha : WeightCommutatorField W a D) :
    WeightCommutatorField W (VOA.deriv a) (D + 1) := by
  intro j
  rw [deriv_apply]
  have hcast : (j + 1) • a (j + 1) = (((j + 1 : ℤ) : ℂ) • a (j + 1)) :=
    (Int.cast_smul_eq_zsmul ℂ (j + 1) (a (j + 1))).symm
  rw [hcast]
  calc
    W * (((j + 1 : ℤ) : ℂ) • a (j + 1))
        - (((j + 1 : ℤ) : ℂ) • a (j + 1)) * W =
      (((j + 1 : ℤ) : ℂ) • (W * a (j + 1) - a (j + 1) * W)) := by
        rw [mul_smul_comm, smul_mul_assoc, smul_sub]
    _ = (((j + 1 : ℤ) : ℂ) •
        (((D + (j + 1) : ℤ) : ℂ) • a (j + 1))) := by
      rw [ha (j + 1)]
    _ = (((D + 1 + j : ℤ) : ℂ) •
        (((j + 1 : ℤ) : ℂ) • a (j + 1))) := by
      push_cast
      module

/-- The commutator with `W` is a derivation on each normally ordered summand. -/
theorem normalOrdered_comm {W : End ℂ A} {a b : FormalDist (End ℂ A)} {Da Db : ℤ}
    (ha : WeightCommutatorField W a Da) (hb : WeightCommutatorField W b Db)
    (m n : ℤ) :
    W * normalOrdered a b m n - normalOrdered a b m n * W =
      (((Da + Db) + (m + n) : ℤ) : ℂ) • normalOrdered a b m n := by
  rw [normalOrdered_apply]
  by_cases hm : 0 ≤ m
  · rw [if_pos hm]
    calc
      W * (a m * b n) - a m * b n * W =
          (W * a m - a m * W) * b n + a m * (W * b n - b n * W) := by
            noncomm_ring
      _ = (((Da + m : ℤ) : ℂ) • a m) * b n
          + a m * (((Db + n : ℤ) : ℂ) • b n) := by rw [ha m, hb n]
      _ = (((Da + Db) + (m + n) : ℤ) : ℂ) • (a m * b n) := by
        rw [smul_mul_assoc, mul_smul_comm, ← add_smul]
        congr 1
        push_cast
        ring
  · rw [if_neg hm]
    calc
      W * (b n * a m) - b n * a m * W =
          (W * b n - b n * W) * a m + b n * (W * a m - a m * W) := by
            noncomm_ring
      _ = (((Db + n : ℤ) : ℂ) • b n) * a m
          + b n * (((Da + m : ℤ) : ℂ) • a m) := by rw [ha m, hb n]
      _ = (((Da + Db) + (m + n) : ℤ) : ℂ) • (b n * a m) := by
        rw [smul_mul_assoc, mul_smul_comm, ← add_smul]
        congr 1
        push_cast
        ring

/-- Normal products add operator weights. -/
theorem nprod {W : End ℂ A} {a b : FormalDist (End ℂ A)}
    (haf : IsField a) (hbf : IsField b) {Da Db : ℤ}
    (ha : WeightCommutatorField W a Da) (hb : WeightCommutatorField W b Db) :
    WeightCommutatorField W (VOA.nprod haf hbf) (Da + Db) := by
  intro s
  apply LinearMap.ext
  intro x
  have hdiag := normalOrdered_diag_support_finite haf hbf s x
  have hWdiag : (Function.support (fun m : ℤ =>
      W (normalOrdered a b m (s - m) x))).Finite :=
    hdiag.subset (fun m hm => by
      rw [Function.mem_support] at hm ⊢
      exact fun hz => hm (by rw [hz, map_zero]))
  have hdiagW := normalOrdered_diag_support_finite haf hbf s (W x)
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    nprod_apply, nprod_apply, map_finsum W hdiag,
    ← finsum_sub_distrib hWdiag hdiagW]
  rw [show (∑ᶠ m : ℤ,
      (W (normalOrdered a b m (s - m) x) - normalOrdered a b m (s - m) (W x))) =
      ∑ᶠ m : ℤ, ((((Da + Db) + s : ℤ) : ℂ) •
        normalOrdered a b m (s - m)) x from
    finsum_congr fun m => by
      have h := congrArg (fun T : End ℂ A => T x) (normalOrdered_comm ha hb m (s - m))
      simpa only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
        show m + (s - m) = s by ring] using h]
  rw [show (∑ᶠ m : ℤ, ((((Da + Db) + s : ℤ) : ℂ) •
      normalOrdered a b m (s - m)) x) =
      (((Da + Db + s : ℤ) : ℂ) • VOA.nprod haf hbf s) x by
    simp only [LinearMap.smul_apply]
    rw [VOA.nprod_apply, smul_finsum' _ hdiag]]

end WeightCommutatorField

end

end VOA
