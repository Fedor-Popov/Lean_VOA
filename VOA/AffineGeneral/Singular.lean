/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.SimpleQuotient
import VOA.AffineGeneral.DeligneInstance
import VOA.Examples.AffineSimpleQuotient
import VOA.Core.BorcherdsIdentity

/-!
# Singular vectors of `V^k(𝔤)` lie in the maximal ideal (general `𝔤`)

The general-`𝔤` version of REL's A₂ argument (`DeligneAudit/A2RelationsSingular`, §1):

* `SingP D k t`: every strictly positive current mode kills `t`;
* `word_ann`: then every non-weight-raising mode of every current word kills `t` (Dong-type induction);
* `strongly_singular_of_SingP`, `affine_qp` (weight-one states are quasi-primary);
* **`mem_maxIdeal_of_SingP`**: a homogeneous `SingP` vector of positive weight lies in `maxIdeal D k hk`,
  so its image in `L_k(𝔤) = simpleVOA D k hk` is zero.
-/

namespace VOA.AffineGeneral

open VOA.AffineGeneral.LieData
open Module (End)

noncomputable section

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [FiniteDimensional ℂ 𝔤]
variable {κ : LinearMap.BilinForm ℂ 𝔤} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (D : LieData κ ι) (k : ℂ) (hk : k + D.h ≠ 0)

theorem smul_currentState (a : ι) (m : ℤ) (v : Vacuum D k) :
    (affineVOA D k hk).smul (currentState D k (D.generator a)) m v = J D k a m v := by
  change mode (YA D k hk (J D k a (-1) (vacuumA D k))) m v = _
  rw [YA_current_state, mode_Jfield]

/-- Positive-mode singularity: every strictly positive current mode kills `t`. -/
def SingP (t : Vacuum D k) : Prop := ∀ (a : ι) (i : ℤ), 1 ≤ i → J D k a i t = 0

variable {D k} in
theorem SingP.zeroMode {t : Vacuum D k} (ht : SingP D k t) (a : ι) : SingP D k (J D k a 0 t) := by
  intro b i hi
  have hcomm := LinearMap.congr_fun (current_comm D k b a i 0) t
  rw [if_neg (by omega : ¬ (i + (0 : ℤ) = 0))] at hcomm
  simp only [LinearMap.sub_apply, Module.End.mul_apply, add_zero,
    LinearMap.sum_apply, LinearMap.smul_apply] at hcomm
  rw [ht b i hi, map_zero, sub_zero] at hcomm
  rw [hcomm]
  refine Finset.sum_eq_zero (fun c _ => ?_)
  rw [ht c i hi, smul_zero]

/-- The Dong-type induction over creation words. -/
theorem word_ann (l : List (ι × ℕ)) :
    ∀ (t : Vacuum D k), SingP D k t → ∀ N : ℤ, wordDegA l ≤ N →
      (affineVOA D k hk).smul (wordStateA D k l) N t = 0 := by
  induction l with
  | nil =>
      intro t _ N hN
      rw [wordDegA_nil] at hN
      rw [wordStateA_nil]
      change (affineVOA D k hk).smul (affineVOA D k hk).vacuum N t = 0
      rw [PreVertexAlgebra.smul_vacuum_left, if_neg (by omega)]
  | cons ai rest ih =>
      obtain ⟨a, n⟩ := ai
      intro t ht N hN
      rw [wordDegA_cons] at hN
      have hdn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg _
      rw [wordStateA_cons]
      change (affineVOA D k hk).smul (J D k a (-(n : ℤ) - 1) (wordStateA D k rest)) N t = 0
      rw [← smul_currentState D k hk a (-(n : ℤ) - 1) (wordStateA D k rest),
        VertexOperatorAlgebra.mode_iterate]
      have hterm : ∀ i : ℕ,
          (((-1 : ℂ) ^ i * gBinom (-(n : ℤ) - 1) i) •
            ((affineVOA D k hk).smul (currentState D k (D.generator a)) (-(n : ℤ) - 1 - (i : ℤ))
                ((affineVOA D k hk).smul (wordStateA D k rest) (N + (i : ℤ)) t)
              - ((-1 : ℂ) ^ (-(n : ℤ) - 1)) •
                (affineVOA D k hk).smul (wordStateA D k rest)
                  ((-(n : ℤ) - 1) + N - (i : ℤ))
                  ((affineVOA D k hk).smul (currentState D k (D.generator a)) (i : ℤ) t)))
          = 0 := by
        intro i
        have hi0 : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg _
        have h1 : (affineVOA D k hk).smul (wordStateA D k rest) (N + (i : ℤ)) t = 0 :=
          ih t ht (N + (i : ℤ)) (by omega)
        rcases Nat.eq_zero_or_pos i with rfl | hipos
        · have h2 : (affineVOA D k hk).smul (wordStateA D k rest)
              ((-(n : ℤ) - 1) + N - ((0 : ℕ) : ℤ)) (J D k a 0 t) = 0 :=
            ih _ (ht.zeroMode a) _ (by push_cast; omega)
          simp only [smul_currentState, Nat.cast_zero, sub_zero, add_zero] at h1 h2 ⊢
          rw [h1, h2]
          simp
        · have h2 : (affineVOA D k hk).smul (currentState D k (D.generator a)) (i : ℤ) t = 0 := by
            rw [smul_currentState]
            exact ht a (i : ℤ) (by exact_mod_cast hipos)
          rw [h1, h2]
          simp
      rw [finsum_congr hterm, finsum_zero]

theorem hspan_ann {t : Vacuum D k} (ht : SingP D k t) (m : ℤ) :
    ∀ u ∈ HSpan D k m, ∀ N : ℤ, m ≤ N → (affineVOA D k hk).smul u N t = 0 := by
  intro u hu
  rw [HSpan] at hu
  induction hu using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, hl, rfl⟩ := hz
      intro N hN
      exact word_ann D k hk l t ht N (by rw [hl]; exact hN)
  | zero => intro N _; simp
  | add x y _ _ ihx ihy =>
      intro N hN
      rw [PreVertexAlgebra.smul_add_left, ihx N hN, ihy N hN, add_zero]
  | smul c x _ ihx =>
      intro N hN
      rw [PreVertexAlgebra.smul_smul_left, ihx N hN, smul_zero]

/-- Positive current singularity implies that every non-weight-raising mode of every homogeneous
state kills `t`. -/
theorem strongly_singular_of_SingP {t : Vacuum D k} (ht : SingP D k t)
    {m : ℤ} {u : Vacuum D k} (hu : u ∈ (affineVOA D k hk).grading m) :
    ∀ N : ℤ, m ≤ N → (affineVOA D k hk).smul u N t = 0 :=
  hspan_ann D k hk ht m u (gradingZA_le_hspan D k m hu)

/-- **Weight-one states of `V^k(𝔤)` are quasi-primary**: `L₁ v = 0` on `V₁`. -/
theorem affine_qp :
    ∀ v, v ∈ (affineVOA D k hk).grading 1 → (affineVOA D k hk).L 1 v = 0 := by
  intro v hv
  change v ∈ gradingZA D k 1 at hv
  rw [grading_one_eq_range] at hv
  obtain ⟨x, rfl⟩ := hv
  have hL : (affineVOA D k hk).L 1 = mode (YA D k hk (omegaA D k)) 2 := by
    rw [VertexOperatorAlgebra.L_def]
    norm_num
    rfl
  rw [hL, ← D.reconstruct x, map_sum, map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [map_smul, map_smul]
  have e : currentState D k (D.basis c) = J D k c (-1) (vacuumA D k) := rfl
  rw [e, current_primary D k hk c, smul_zero]

/-- A nonzero homogeneous `SingP` vector of positive weight is strongly singular. -/
theorem isStronglySingular_of_SingP {t : Vacuum D k} (ht : SingP D k t) (hne : t ≠ 0)
    {w : ℤ} (hw : 0 < w) (hmem : t ∈ gradingZA D k w) :
    SingVec.IsStronglySingularOfWeight (affineVOA D k hk) w t where
  ne_zero := hne
  weight_pos := hw
  homogeneous := hmem
  annihilated := fun _ _ hu n hn => strongly_singular_of_SingP D k hk ht hu n hn

/-- **Every homogeneous `SingP` vector of positive weight lies in the maximal ideal.** -/
theorem mem_maxIdeal_of_SingP {t : Vacuum D k} (ht : SingP D k t)
    {w : ℤ} (hw : 0 < w) (hmem : t ∈ gradingZA D k w) : t ∈ maxIdeal D k hk := by
  by_cases h0 : t = 0
  · rw [h0]; exact Submodule.zero_mem _
  · exact SimpleQuot.mem_maxGradedIdeal_of_stronglySingular (vacuumA_ne_zero D k)
      (affine_qp D k hk) (isStronglySingular_of_SingP D k hk ht h0 hw hmem)

/-- Its image in `L_k(𝔤)` vanishes. -/
theorem simpleProjection_eq_zero_of_SingP {t : Vacuum D k} (ht : SingP D k t)
    {w : ℤ} (hw : 0 < w) (hmem : t ∈ gradingZA D k w) : simpleProjection D k hk t = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (mem_maxIdeal_of_SingP D k hk ht hw hmem)

end

end VOA.AffineGeneral
