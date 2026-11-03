/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.SingularQuad

/-!
# Generic singular-current APIs re-exported for the D4 case

These wrappers use the already proved type-generic affine lemmas and keep
concrete root tables, carrier data and sl3-specific imports out of this layer.
-/
namespace VOA.DeligneAudit.D4Lie

open VOA VOA.AffineGeneral VOA.AffineGeneral.LieData
open Module (End)

noncomputable section

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [FiniteDimensional ℂ 𝔤]
variable {κ : LinearMap.BilinForm ℂ 𝔤} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (D : LieData κ ι) (k : ℂ) (hk : k + D.h ≠ 0)

theorem smulJ (a : ι) (m : ℤ) (v : Vacuum D k) :
    (affineVOA D k hk).smul (J D k a (-1) (vacuumA D k)) m v = J D k a m v :=
  VOA.AffineGeneral.smul_currentState D k hk a m v

/-- Every strictly positive current mode kills the vector. -/
def SingP (t : Vacuum D k) : Prop := ∀ (a : ι) (i : ℤ), 1 ≤ i → J D k a i t = 0

variable {D k} in
theorem SingP.zeroMode {t : Vacuum D k} (ht : SingP D k t) (a : ι) :
    SingP D k (J D k a 0 t) :=
  VOA.AffineGeneral.SingP.zeroMode ht a

theorem word_ann (l : List (ι × ℕ)) :
    ∀ (t : Vacuum D k), SingP D k t → ∀ N : ℤ, wordDegA l ≤ N →
      (affineVOA D k hk).smul (wordStateA D k l) N t = 0 :=
  VOA.AffineGeneral.word_ann D k hk l

theorem hspan_ann {t : Vacuum D k} (ht : SingP D k t) (m : ℤ) :
    ∀ u ∈ HSpan D k m, ∀ N : ℤ, m ≤ N → (affineVOA D k hk).smul u N t = 0 :=
  VOA.AffineGeneral.hspan_ann D k hk ht m

theorem affine_qp :
    ∀ v, v ∈ (affineVOA D k hk).grading 1 → (affineVOA D k hk).L 1 v = 0 :=
  VOA.AffineGeneral.affine_qp D k hk

theorem mem_maxIdeal_of_SingP {t : Vacuum D k} (ht : SingP D k t)
    {w : ℤ} (hw : 0 < w) (hmem : t ∈ gradingZA D k w) : t ∈ maxIdeal D k hk :=
  VOA.AffineGeneral.mem_maxIdeal_of_SingP D k hk ht hw hmem

theorem J_J_comm (a b : ι) (m n : ℤ) (w : Vacuum D k) :
    J D k a m (J D k b n w) =
      J D k b n (J D k a m w) + (∑ c, structureConstant D a b c • J D k c (m + n) w)
        + (if m + n = 0 then ((m : ℂ) * k * formTable D a b) • w else 0) :=
  VOA.AffineGeneral.J_comm_apply D k a b m n w

theorem J_vac_nonneg (a : ι) {m : ℤ} (hm : 0 ≤ m) : J D k a m (vacuumA D k) = 0 :=
  J_vacuum_nonneg D k a hm

theorem J_one_word2 (c a b : ι) :
    J D k c 1 (J D k a (-1) (J D k b (-1) (vacuumA D k))) =
      ∑ e, (k * formTable D c b * (if a = e then 1 else 0) +
        k * formTable D c a * (if b = e then 1 else 0) +
        ∑ d, structureConstant D c a d * structureConstant D d b e) •
          J D k e (-1) (vacuumA D k) := by
  simpa only [st2, st1, mul_ite, mul_one, mul_zero] using
    VOA.AffineGeneral.J_one_st2_coord D k c a b

theorem J_two_word2 (c a b : ι) :
    J D k c 2 (J D k a (-1) (J D k b (-1) (vacuumA D k))) =
      (∑ d, structureConstant D c a d * (k * formTable D d b)) • vacuumA D k := by
  simpa only [st2, st1, Finset.mul_sum, mul_left_comm] using
    VOA.AffineGeneral.J_two_st2 D k c a b

include hk in
theorem J_mem_gradingZA (a : ι) (m : ℤ) {q : ℤ} {x : Vacuum D k}
    (hx : x ∈ gradingZA D k q) : J D k a m x ∈ gradingZA D k (q - m) := by
  rw [← smulJ D k hk]
  have h := (affineVOA D k hk).smul_mem_grading
    (currentState_mem_grading D k (D.generator a)) hx m
  rwa [show (1 : ℤ) + q - m - 1 = q - m by ring] at h

include hk in
theorem word2_mem (a b : ι) :
    J D k a (-1) (J D k b (-1) (vacuumA D k)) ∈ gradingZA D k 2 := by
  have := J_mem_gradingZA D k hk a (-1)
    (J_mem_gradingZA D k hk b (-1) (vacuumA_mem_gradingZA_zero D k))
  simpa using this

end

end VOA.DeligneAudit.D4Lie

#print axioms VOA.DeligneAudit.D4Lie.mem_maxIdeal_of_SingP
#print axioms VOA.DeligneAudit.D4Lie.J_one_word2
