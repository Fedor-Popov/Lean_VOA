/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2Character

/-!
# Weight two of `L_{-3/2}(sl₃)`: a Gram-matrix lower bound

The character input of the A₂ Deligne case is the lower bound
`dim L_{-3/2}(sl₃)_N ≥ [q^N] ∏_{r ≥ 1} (1+q^r)^8` (see `A2Character.lean`).  This file proves it at conformal weight two,
`36 ≤ dim L_{-3/2}(sl₃)_2`, by a finite Gram-matrix certificate on the actual simple quotient
`AffineSl3.simpleVOA`.

Method.  For the quadratic states `J^a_{-1} J^b_{-1} |0⟩` (`a ≤ b`, 36 of them) and the test
operators `J^c_1 J^d_1` (`c ≤ d`), the universal vacuum module gives
`J^c_1 J^d_1 J^a_{-1} J^b_{-1}|0⟩ = G_{cd,ab} |0⟩` with the explicit entry `gramC`
(`J_one_J_one_quad`, at every level).  Current modes descend to the simple quotient
(`simpleProjection_product`) and the quotient vacuum is nonzero, so any linear relation among the
images of the states forces `G c = 0`.  At `k = -3/2` the integer matrix `4G` (`gramLit`) has the
explicit left inverse `gramInvLit / 810`, checked by kernel `decide`.  No determinant, singular
vector or character formula is used.

Together with the weight-two singular vectors (upper bound `44 - 8`), this gives
`dim L_{-3/2}(sl₃)_2 = 36`, the `q²` coefficient `28 + 8` of `∏(1+q^r)^8`.
-/

namespace VOA.DeligneAudit.A2Gram

open VOA.AffineSl3 VOA.AffineLie

noncomputable section

section Universal

variable (k : ℂ)

theorem J_vac (a : Fin 8) (n : ℤ) (hn : 0 ≤ n) : J k a n (vacuumA k) = 0 :=
  vacuum_pos_annihilate form form_invariant k _ n hn

/-- The affine commutator applied to a vector. -/
theorem J_comm_apply (a b : Fin 8) (m n : ℤ) (v : Vacuum k) :
    J k a m (J k b n v) = J k b n (J k a m v) + (∑ c, structureConstant a b c • J k c (m + n) v)
      + (if m + n = 0 then ((m : ℂ) * k * formTable a b) • v else 0) := by
  have h := congrArg (fun T : Module.End ℂ (Vacuum k) => T v) (current_comm k a b m n)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply] at h
  split_ifs at h ⊢
  · simp only [LinearMap.smul_apply, LinearMap.id_apply] at h
    rw [add_assoc, ← h]; abel
  · simp only [LinearMap.zero_apply, add_zero] at h ⊢
    rw [← h]; abel

/-- `J^d_0 J^b_{-1}|0⟩ = ∑_g f^{db}_g J^g_{-1}|0⟩`. -/
theorem J_zero_current (d b : Fin 8) :
    J k d 0 (J k b (-1) (vacuumA k)) =
      ∑ g, structureConstant d b g • J k g (-1) (vacuumA k) := by
  rw [J_comm_apply, J_vac k d 0 le_rfl, map_zero, zero_add, if_neg (by norm_num), add_zero]
  simp

/-- `J^c_1 J^b_{-1}|0⟩ = k κ(c,b) |0⟩`. -/
theorem J_one_current (c b : Fin 8) :
    J k c 1 (J k b (-1) (vacuumA k)) = (k * formTable c b) • vacuumA k := by
  rw [J_comm_apply, J_vac k c 1 (by norm_num), map_zero, zero_add, if_pos (by norm_num)]
  have h0 : ∀ g, J k g 0 (vacuumA k) = 0 := fun g => J_vac k g 0 le_rfl
  simp [h0]

/-- The quadratic state `J^a_{-1} J^b_{-1} |0⟩`. -/
def quad (a b : Fin 8) : Vacuum k := J k a (-1) (J k b (-1) (vacuumA k))

/-- `J^d_1` on a quadratic state. -/
theorem J_one_quad (d a b : Fin 8) :
    J k d 1 (quad k a b) =
      (k * formTable d b) • J k a (-1) (vacuumA k)
        + (∑ e, structureConstant d a e • ∑ g, structureConstant e b g • J k g (-1) (vacuumA k))
        + (k * formTable d a) • J k b (-1) (vacuumA k) := by
  unfold quad
  rw [J_comm_apply, J_one_current, map_smul, if_pos (by norm_num)]
  simp only [show (1 : ℤ) + -1 = 0 by norm_num, J_zero_current]
  simp

/-- The Gram entry `⟨J^c_1 J^d_1 | J^a_{-1} J^b_{-1}⟩` as a function of the level. -/
def gramC (c d a b : Fin 8) : ℂ :=
  (k * formTable d b) * (k * formTable c a)
    + ∑ e, structureConstant d a e * ∑ g, structureConstant e b g * (k * formTable c g)
    + (k * formTable d a) * (k * formTable c b)

/-- **The weight-two Gram formula** in the universal vacuum module, at every level. -/
theorem J_one_J_one_quad (c d a b : Fin 8) :
    J k c 1 (J k d 1 (quad k a b)) = gramC k c d a b • vacuumA k := by
  rw [J_one_quad]
  simp only [map_add, map_smul, map_sum, J_one_current, gramC, add_smul, Finset.sum_smul,
    Finset.smul_sum, smul_smul, Finset.mul_sum]
  congr 2
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun g _ => ?_
  rw [mul_assoc]

/-- The quadratic states have conformal weight two. -/
theorem quad_mem (a b : Fin 8) : quad k a b ∈ gradingZA k 2 := by
  have h0 := vacuumA_mem_gradingZA_zero k
  have h1 := J_mem_gradingZA k b (-1) 0 h0
  have h2 := J_mem_gradingZA k a (-1) _ h1
  simpa [quad] using h2

end Universal

/-! ## Integer tables -/

/-- The Chevalley structure constants as integers (same literal as `bracketTable`). -/
def bracketZ : Fin 8 → Fin 8 → Fin 8 → ℤ :=
  ![![![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 1, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, -1, 0, 0, 0],
      ![-2, 0, 0, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, -1, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 1],
      ![0, 0, 0, 1, 0, 0, 0, 0],
      ![0, 1, 0, 0, 0, 0, 0, 0],
      ![0, -2, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, -1, 0, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 1, 1],
      ![0, 0, -1, 0, 0, 0, 0, 0],
      ![0, 0, -1, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 1, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, -1, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 2, 0, 0, 0, 0],
      ![0, 0, 0, -1, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, -1],
      ![-1, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 1, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, -1, 0, 0, 0],
      ![0, 0, 0, 0, 2, 0, 0, 0]],
    ![![0, 0, 0, 0, 1, 0, 0, 0],
      ![0, 0, 0, -1, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, -1, -1],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 1, 0, 0],
      ![0, 0, 0, 0, 0, 1, 0, 0]],
    ![![2, 0, 0, 0, 0, 0, 0, 0],
      ![0, -1, 0, 0, 0, 0, 0, 0],
      ![0, 0, 1, 0, 0, 0, 0, 0],
      ![0, 0, 0, -2, 0, 0, 0, 0],
      ![0, 0, 0, 0, 1, 0, 0, 0],
      ![0, 0, 0, 0, 0, -1, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0]],
    ![![-1, 0, 0, 0, 0, 0, 0, 0],
      ![0, 2, 0, 0, 0, 0, 0, 0],
      ![0, 0, 1, 0, 0, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0, 0],
      ![0, 0, 0, 0, -2, 0, 0, 0],
      ![0, 0, 0, 0, 0, -1, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0]]]

/-- The trace form as integers (same literal as `formTable`). -/
def formZ : Fin 8 → Fin 8 → ℤ :=
  ![![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 2, -1],
    ![0, 0, 0, 0, 0, 0, -1, 2]]

/-- The 36 unordered pairs `a ≤ b` of Chevalley indices. -/
def pairs : Fin 36 → Fin 8 × Fin 8 :=
  ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 4), (4, 5), (4, 6), (4, 7), (5, 5), (5, 6), (5, 7), (6, 6), (6, 7), (7, 7)]

/-- Four times the weight-two Gram matrix at `k = -3/2` (rows: tests, columns: states). -/
def gramLit : Fin 36 → Fin 36 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, -12, 6, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -24, 12, -6],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, -6, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 42, -21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -21, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -6, 12, -24],
    ![0, 0, 0, 0, 0, 0, 6, -12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, -21, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -21, 42, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 6, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -6, -6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -6, -6, -6],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -12, 0, 0, 0, 0, 0, 0, 0, 0, 24, -3, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, -3, 24, 0, 0, 0],
    ![30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -12, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 42, -21, 0, 0, 0, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, -21, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, -21, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -21, 42, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, -12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -24, 0, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 72, -36, 18],
    ![0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -36, 45, -36],
    ![0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 0, -24, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, -36, 72]]

/-- `810 ×` the inverse of `gramLit`. -/
def gramInvLit : Fin 36 → Fin 36 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 378, 0, 0, 0, 0, 0, 0, 0, 0, 180, -72, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 54, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -342, 0, 0, 0, 0, 0, 0, 0, -252, 0, 0, 0, 0, 0, 0, 432, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30, 288, 60],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 54, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 252, 180, 0, -378, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -180, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -90, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -252, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -18, -108, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 54, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 54, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -252, 0, 0, 0, 0, 0, 0, 0, -342, 0, 0, 0, 0, 0, 0, 432, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 60, 288, 30],
    ![0, 0, 0, 0, 0, 0, -180, -252, 0, 0, 0, 0, 0, 0, 0, 0, 0, -378, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 252, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -108, -18, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 180, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -90, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, -378, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 252, 72, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -378, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -72, -252, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 432, 0, 0, 0, 0, 0, 0, 0, 432, 0, 0, 0, 0, 0, 0, -702, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -90, -468, -90],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 180, 0, 0, 0, 0, 0, 0, 0, 0, 120, -30, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -72, 0, 0, 0, 0, 0, 0, 0, 0, -30, 48, 0, 0, 0],
    ![27, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 378, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 180, -72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 54, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -18, 0, 0, 0, 0, 0, 0, 0, 0, 0, -72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, -90, -108, 0, 0, 0, 0, 0, 0, 0, 0, 0, -252, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 27, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 54, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -108, -90, 0, 252, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -18, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 180, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 120, -30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, -72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -30, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 30, 0, 0, 0, 0, 0, 0, 0, 60, 0, 0, 0, 0, 0, 0, -90, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -40, -5],
    ![0, 0, 0, 288, 0, 0, 0, 0, 0, 0, 0, 288, 0, 0, 0, 0, 0, 0, -468, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -40, -262, -40],
    ![0, 0, 0, 60, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 0, 0, 0, -90, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -5, -40, 0]]

set_option maxHeartbeats 0 in
theorem bracketTable_eq_cast (a b c : Fin 8) : bracketTable a b c = (bracketZ a b c : ℂ) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> norm_num [bracketTable, bracketZ]

theorem formTable_eq_cast (a b : Fin 8) : formTable a b = (formZ a b : ℂ) := by
  fin_cases a <;> fin_cases b <;> norm_num [formTable, formZ]

/-- Four times the Gram entry at `k = -3/2`, as an integer. -/
def gramZ (c d a b : Fin 8) : ℤ :=
  -6 * (∑ e, ∑ g, bracketZ d a e * bracketZ e b g * formZ c g)
    + 9 * (formZ d b * formZ c a + formZ d a * formZ c b)

theorem four_gramC (c d a b : Fin 8) : 4 * gramC (-3 / 2) c d a b = (gramZ c d a b : ℂ) := by
  have hsum : ∀ k : ℂ, (∑ e, structureConstant d a e *
      ∑ g, structureConstant e b g * (k * formTable c g)) =
      k * ∑ e, ∑ g, (bracketZ d a e * bracketZ e b g * formZ c g : ℂ) := by
    intro k
    simp only [Finset.mul_sum, structureConstant_eq_table, bracketTable_eq_cast,
      formTable_eq_cast]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun g _ => ?_
    ring
  rw [gramC, hsum]
  simp only [gramZ, formTable_eq_cast]
  push_cast
  ring

theorem gramZ_eq_lit : ∀ t s : Fin 36,
    gramZ (pairs t).1 (pairs t).2 (pairs s).1 (pairs s).2 = gramLit t s := by
  decide +kernel

theorem gramInv_mul : ∀ u s : Fin 36,
    (∑ t, gramInvLit u t * gramLit t s) = if u = s then 810 else 0 := by
  decide +kernel

/-! ## The simple quotient at `k = -3/2` -/

/-- The nonzero noncritical level. -/
theorem hk : (-3 / 2 : ℂ) + 3 ≠ 0 := by norm_num

/-- The image of the `s`-th quadratic state in `L_{-3/2}(sl₃)`. -/
def state (s : Fin 36) : SimpleSpace (-3 / 2) hk :=
  simpleProjection (-3 / 2) hk (quad (-3 / 2) (pairs s).1 (pairs s).2)

/-- Current mode `J^a_n` of the simple quotient VOA. -/
def SJ (a : Fin 8) (n : ℤ) (x : SimpleSpace (-3 / 2) hk) : SimpleSpace (-3 / 2) hk :=
  (simpleVOA (-3 / 2) hk).smul (simpleCurrentState (-3 / 2) hk (generator a)) n x

/-- Simple-quotient current modes are the projections of the universal ones. -/
theorem SJ_proj (a : Fin 8) (n : ℤ) (v : Vacuum (-3 / 2)) :
    SJ a n (simpleProjection (-3 / 2) hk v) = simpleProjection (-3 / 2) hk (J (-3 / 2) a n v) := by
  unfold SJ simpleCurrentState
  rw [LinearMap.comp_apply, simpleProjection_product]
  change simpleProjection (-3 / 2) hk
    (mode (YA (-3 / 2) hk (currentState (-3 / 2) (generator a))) n v) = _
  rw [mode_YA_currentState]
  rfl

theorem proj_vacuum_ne_zero : simpleProjection (-3 / 2) hk (vacuumA (-3 / 2)) ≠ 0 :=
  simple_vacuum_ne_zero (-3 / 2) hk

/-- **The 36 quadratic states are linearly independent in `L_{-3/2}(sl₃)`.** -/
theorem state_linearIndependent : LinearIndependent ℂ state := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  -- Push the relation through each test operator.
  have hrow : ∀ t : Fin 36, ∑ s, g s * (gramLit t s : ℂ) = 0 := by
    intro t
    have hzero : simpleProjection (-3 / 2) hk
        (∑ s, g s • quad (-3 / 2) (pairs s).1 (pairs s).2) = 0 := by
      simpa [state, map_sum, map_smul] using hg
    have happ := congrArg (fun x => SJ (pairs t).1 1 (SJ (pairs t).2 1 x)) hzero
    simp only at happ
    have h0 : SJ (pairs t).1 1 (SJ (pairs t).2 1 (0 : SimpleSpace (-3 / 2) hk)) = 0 := by
      rw [← map_zero (simpleProjection (-3 / 2) hk), SJ_proj, map_zero, SJ_proj, map_zero,
        map_zero]
    rw [h0, SJ_proj, SJ_proj] at happ
    simp only [map_sum, map_smul, J_one_J_one_quad, smul_smul, ← Finset.sum_smul] at happ
    have hsum : ∑ s, g s * gramC (-3 / 2) (pairs t).1 (pairs t).2 (pairs s).1 (pairs s).2 = 0 :=
      (smul_eq_zero.mp happ).resolve_right proj_vacuum_ne_zero
    calc ∑ s, g s * (gramLit t s : ℂ)
        = 4 * ∑ s, g s * gramC (-3 / 2) (pairs t).1 (pairs t).2 (pairs s).1 (pairs s).2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [← gramZ_eq_lit, ← four_gramC]; ring
      _ = 0 := by rw [hsum, mul_zero]
  -- Invert the Gram matrix with the integer certificate.
  intro u
  have hinv : ∀ s, (∑ t, (gramInvLit u t : ℂ) * (gramLit t s : ℂ)) = if u = s then 810 else 0 := by
    intro s
    have := congrArg (fun z : ℤ => (z : ℂ)) (gramInv_mul u s)
    push_cast at this
    rw [this]
  have key : (810 : ℂ) * g u = 0 := by
    calc (810 : ℂ) * g u = ∑ s, (if u = s then (810 : ℂ) else 0) * g s := by
          rw [Finset.sum_eq_single u (fun s _ hs => by rw [if_neg (Ne.symm hs), zero_mul])
            (by simp)]
          simp
      _ = ∑ s, (∑ t, (gramInvLit u t : ℂ) * (gramLit t s : ℂ)) * g s := by
          simp only [hinv]
      _ = ∑ t, (gramInvLit u t : ℂ) * ∑ s, g s * (gramLit t s : ℂ) := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
          ring
      _ = 0 := by simp [hrow]
  exact (mul_eq_zero.mp key).resolve_left (by norm_num)

/-- The quadratic states lie in conformal weight two of the simple quotient. -/
theorem state_mem (s : Fin 36) : state s ∈ (simpleVOA (-3 / 2) hk).grading 2 := by
  change state s ∈ (gradingZA (-3 / 2) 2).map (simpleProjection (-3 / 2) hk)
  exact Submodule.mem_map_of_mem (quad_mem _ _ _)

/-- **Weight two of `L_{-3/2}(sl₃)` has dimension at least 36.** -/
theorem finrank_grading_two_ge :
    36 ≤ Module.finrank ℂ ((simpleVOA (-3 / 2) hk).grading 2) := by
  haveI : FiniteDimensional ℂ (gradingZA (-3 / 2) 2) := gradingZA_finiteDimensional _ _
  haveI : FiniteDimensional ℂ ((simpleVOA (-3 / 2) hk).grading 2) := by
    change FiniteDimensional ℂ ((gradingZA (-3 / 2) 2).map (simpleProjection (-3 / 2) hk))
    infer_instance
  let f : Fin 36 → (simpleVOA (-3 / 2) hk).grading 2 := fun s => ⟨state s, state_mem s⟩
  have hf : LinearIndependent ℂ f :=
    LinearIndependent.of_comp (Submodule.subtype _) state_linearIndependent
  simpa using hf.fintype_card_le_finrank

end

end VOA.DeligneAudit.A2Gram

namespace VOA.DeligneAudit.A2

/-- **The A₂ character lower bound at conformal weight two**, on the capstone's VOA `A2.W`:
`dim W_2 ≥ 36 = [q²] ∏(1+q^r)^8`. -/
theorem finrank_grading_two_ge : 36 ≤ Module.finrank ℂ (W.grading (2 : ℕ)) :=
  A2Gram.finrank_grading_two_ge

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2Gram.J_one_J_one_quad
#print axioms VOA.DeligneAudit.A2Gram.gramInv_mul
#print axioms VOA.DeligneAudit.A2Gram.state_linearIndependent
#print axioms VOA.DeligneAudit.A2.finrank_grading_two_ge
end AxiomAudit
