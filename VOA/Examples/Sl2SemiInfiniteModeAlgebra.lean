/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteModes
import VOA.Examples.Sl2SemiInfiniteGhostCAR

/-!
# The current part of the semi-infinite mode computation

The anticommutator of two actual `J_n c_{-n}` summands is computed from
the matter affine commutator and the proved ghost Clifford relation.
Summing it gives the square of every finite truncation, with the matter
level visible in the central summand.

OPEN: finish the locally finite infinite-sum rearrangement and cubic cross
terms to obtain operator nilpotency for bare affine matter without translation.
The separate finite-state route in `Sl2SemiInfiniteNilpotency` proves the
operator square for translated matter; it does not complete this pure-mode route.
-/

namespace VOA.Sl2SemiInfinite

open Module (End)
open AffineVOA
open scoped BigOperators TensorProduct

universe u
variable {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {V : SuperVertexAlgebra M} {k : ℂ}

/-- A single sign-free summand `J_n ⊗ c_{-n}` of `matterModeCharge`. -/
noncomputable def matterGhostMode (A : AffineSl2Action V k) (a : Fin 3) (n : ℤ) :
    End ℂ (M ⊗[ℂ] Sl2GhostSpace) :=
  TensorProduct.map (mode (V.Y (A.current a)) n)
    (mode (sl2GhostSVA.Y (cGhost a)) (-n - 1))

/-- The actual termwise anticommutator, with the affine simple and central terms explicit. -/
theorem matterGhostMode_anticomm (A : AffineSl2Action V k) (a b : Fin 3) (m n : ℤ) :
    matterGhostMode A a m * matterGhostMode A b n +
      matterGhostMode A b n * matterGhostMode A a m =
    TensorProduct.map
      ((∑ c, fabc a b c • mode (V.Y (A.current c)) (m + n)) +
        if m + n = 0 then ((m : ℂ) * k * kappa a b) • LinearMap.id else 0)
      (mode (sl2GhostSVA.Y (cGhost a)) (-m - 1) *
        mode (sl2GhostSVA.Y (cGhost b)) (-n - 1)) := by
  apply TensorProduct.ext'
  intro x y
  have hc := congrArg (fun f : End ℂ Sl2GhostSpace => f y)
    (cGhost_modes_anticomm b a (-n - 1) (-m - 1))
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] at hc
  rw [add_eq_zero_iff_eq_neg] at hc
  simp only [matterGhostMode, LinearMap.add_apply, Module.End.mul_apply,
    TensorProduct.map_tmul]
  rw [hc, TensorProduct.tmul_neg, ← sub_eq_add_neg, ← TensorProduct.sub_tmul]
  have hm := congrArg (fun f : End ℂ M => f x) (A.current_comm a b m n)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at hm
  rw [hm]
  rfl

/-- The finite current-mode cutoff used before any infinite-sum rearrangement. -/
noncomputable def truncatedMatterCharge (A : AffineSl2Action V k)
    (s : Finset (Fin 3 × ℤ)) : End ℂ (M ⊗[ℂ] Sl2GhostSpace) :=
  ∑ p ∈ s, matterGhostMode A p.1 p.2

set_option maxHeartbeats 800000 in
-- Elaborating the two finite sums of tensor endomorphisms exceeds the default limit.
/-- Twice the square of every finite cutoff is the sum of the affine brackets.
This is a mode-algebra identity; the central term still has matter level `k`. -/
theorem truncatedMatterCharge_square (A : AffineSl2Action V k)
    (s : Finset (Fin 3 × ℤ)) :
    (2 : ℂ) • (truncatedMatterCharge A s * truncatedMatterCharge A s) =
      ∑ p ∈ s, ∑ q ∈ s, TensorProduct.map
        ((∑ c, fabc p.1 q.1 c • mode (V.Y (A.current c)) (p.2 + q.2)) +
          if p.2 + q.2 = 0 then ((p.2 : ℂ) * k * kappa p.1 q.1) • LinearMap.id
          else 0)
        (mode (sl2GhostSVA.Y (cGhost p.1)) (-p.2 - 1) *
          mode (sl2GhostSVA.Y (cGhost q.1)) (-q.2 - 1)) := by
  classical
  simp_rw [← matterGhostMode_anticomm A]
  rw [two_smul]
  simp only [truncatedMatterCharge, Finset.sum_mul, Finset.mul_sum]
  simp only [Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm

end VOA.Sl2SemiInfinite
