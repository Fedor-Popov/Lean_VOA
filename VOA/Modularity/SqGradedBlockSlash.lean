/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.SqModeWeight

/-!
# Slash covariance for source-correct square-bracket blocks

The square-weight slash is globally linear.  The all-input square-mode weight theorem supplies the
matching weights in Zhu's two square-mode relations, so those relations are preserved by slash.
-/

namespace VOA

open Complex
open scoped BigOperators MatrixGroups

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- Induction over the proved natural square-weight decomposition. -/
theorem sqWeightNat_induction (W : VertexOperatorAlgebra V) {P : V → Prop}
    (hhom : ∀ n : ℕ, ∀ v ∈ sqWeightSpace W (n : ℂ), P v) (hzero : P 0)
    (hadd : ∀ v w, P v → P w → P (v + w)) (v : V) : P v := by
  have hv : v ∈ ⨆ n : ℕ, sqWeightSpace W (n : ℂ) := by
    rw [sqWeightSpace_nat_spans_top]
    exact Submodule.mem_top
  exact Submodule.iSup_induction (fun n : ℕ ↦ sqWeightSpace W (n : ℂ))
    (motive := P) hv hhom hzero hadd

section

variable {W : VertexOperatorAlgebra V} {F : V → ℂ → ℂ}

@[simp] theorem sqBlockSlash_zero (W : VertexOperatorAlgebra V)
    {F : V → ℂ → ℂ} (hF : IsSqGradedBlock W F) (gamma : SL(2, ℤ)) :
    sqBlockSlash W hF gamma 0 = 0 :=
  map_zero (sqBlockSlashLinear W hF gamma)

private theorem sqNegTwoTerm_support_finite_of_zero (G : V → ℂ → ℂ)
    (hG0 : ∀ z, G 0 z = 0) (a v : V) (z : ℂ) :
    (Function.support fun m : ℕ ↦ sqNegTwoTerm W G a v z m).Finite := by
  obtain ⟨K, hK⟩ := sqMode_tail_eventually_zero W a v
  refine Set.Finite.subset (Set.finite_Iio K) (fun m hm ↦ ?_)
  simp only [Function.mem_support, ne_eq] at hm
  simp only [Set.mem_Iio]
  by_contra hlt
  push Not at hlt
  exact hm (by rw [sqNegTwoTerm, hK m hlt, hG0]; ring)

private theorem sqBlockSlash_vanish_hom (hF : IsSqGradedBlock W F)
    (gamma : SL(2, ℤ)) {K n : ℕ} {a v : V}
    (ha : a ∈ sqWeightSpace W (K : ℂ)) (hv : v ∈ sqWeightSpace W (n : ℂ)) :
    sqBlockSlash W hF gamma (sqMode W 0 a v) = 0 := by
  have hout := sqMode_mem_sqWeightSpace W ha hv 0
  by_cases hKn : K + n = 0
  · have hout0 : sqMode W 0 a v = 0 := by
      have hneg : (K : ℤ) + (n : ℤ) - 0 - 1 < 0 := by omega
      rw [sqWeightSpace_eq_bot_of_neg W hneg, Submodule.mem_bot] at hout
      exact hout
    rw [hout0, sqBlockSlash_zero]
  · have hpos : 1 ≤ K + n := by omega
    have hout' : sqMode W 0 a v ∈ sqWeightSpace W (((K + n - 1 : ℕ) : ℕ) : ℂ) := by
      convert hout using 1
      push_cast
      rw [Nat.cast_sub hpos]
      push_cast
      ring
    rw [sqBlockSlash_of_mem W hF gamma hout', hF.vanish a v]
    funext z
    simp [slashC]

private theorem sqBlockSlash_vanish (hF : IsSqGradedBlock W F) (gamma : SL(2, ℤ)) :
    ∀ a v : V, sqBlockSlash W hF gamma (sqMode W 0 a v) = 0 := by
  intro a
  refine sqWeightNat_induction W (P := fun a ↦
    ∀ v : V, sqBlockSlash W hF gamma (sqMode W 0 a v) = 0) ?_ ?_ ?_ a
  · intro K x hx v
    refine sqWeightNat_induction W (P := fun v ↦
      sqBlockSlash W hF gamma (sqMode W 0 x v) = 0) ?_ ?_ ?_ v
    · intro n y hy
      exact sqBlockSlash_vanish_hom hF gamma hx hy
    · simp
    · intro y z hy hz
      rw [map_add, sqBlockSlash_add, hy, hz, add_zero]
  · intro v
    simp
  · intro x y hx hy v
    rw [map_add, LinearMap.add_apply, sqBlockSlash_add, hx v, hy v, add_zero]

private theorem sqBlockSlash_negTwo_hom (hF : IsSqGradedBlock W F)
    (gamma : SL(2, ℤ)) {K n : ℕ} {a v : V}
    (ha : a ∈ sqWeightSpace W (K : ℂ)) (hv : v ∈ sqWeightSpace W (n : ℂ))
    (z : ℂ) (hz : z ∈ imGT 0) :
    sqBlockSlash W hF gamma (sqMode W (-2) a v) z
      + ∑ᶠ m : ℕ, sqNegTwoTerm W (sqBlockSlash W hF gamma) a v z m = 0 := by
  have hslash := isSlashOf_sqBlockSlash W hF gamma
  have hmz := mobiusC_mem_imGT gamma hz
  have hw0 := sqMode_mem_sqWeightSpace W ha hv (-2)
  have hwm : ∀ m : ℕ, sqMode W (2 * (m + 2) - 2 : ℤ) a v ∈
      sqWeightSpace W ((((K : ℤ) + (n : ℤ) - 2 * (m : ℤ) - 3 : ℤ)) : ℂ) := by
    intro m
    convert sqMode_mem_sqWeightSpace W ha hv (2 * (m + 2) - 2 : ℤ) using 1 <;>
      push_cast <;> ring
  have hw0' : sqMode W (-2) a v ∈
      sqWeightSpace W ((((K : ℤ) + (n : ℤ) + 1 : ℤ)) : ℂ) := by
    convert hw0 using 1 <;> push_cast <;> ring
  have hlaw := hF.negTwo a v (mobiusC gamma z) hmz
  have htail : ∀ m : ℕ,
      sqNegTwoTerm W F a v (mobiusC gamma z) m
          * denomC gamma z ^ (-((K : ℤ) + (n : ℤ) + 1))
        = sqNegTwoTerm W (sqBlockSlash W hF gamma) a v z m := by
    intro m
    rw [sqNegTwoTerm, sqNegTwoTerm,
      hslash _ _ (hwm m) z hz, slashC]
    have h := slashC_zhuGC_mul (j := m + 2) (by omega) gamma
      ((K : ℤ) + (n : ℤ) - 2 * (m : ℤ) - 3)
      (F (sqMode W (2 * (m + 2) - 2 : ℤ) a v)) hz
    rw [show 2 * (((m + 2 : ℕ)) : ℤ)
        + ((K : ℤ) + (n : ℤ) - 2 * (m : ℤ) - 3)
        = (K : ℤ) + (n : ℤ) + 1 by push_cast; ring] at h
    rw [← h]
    ring
  have hsum : (∑ᶠ m : ℕ, sqNegTwoTerm W F a v (mobiusC gamma z) m)
          * denomC gamma z ^ (-((K : ℤ) + (n : ℤ) + 1))
      = ∑ᶠ m : ℕ, sqNegTwoTerm W (sqBlockSlash W hF gamma) a v z m := by
    rw [finsum_mul]
    exact finsum_congr htail
  rw [hslash _ _ hw0' z hz, slashC, ← hsum, ← add_mul, hlaw, zero_mul]

private theorem sqBlockSlash_negTwo (hF : IsSqGradedBlock W F)
    (gamma : SL(2, ℤ)) : ∀ a v : V, ∀ z ∈ imGT 0,
    sqBlockSlash W hF gamma (sqMode W (-2) a v) z
      + ∑ᶠ m : ℕ, sqNegTwoTerm W (sqBlockSlash W hF gamma) a v z m = 0 := by
  intro a
  refine sqWeightNat_induction W (P := fun a ↦ ∀ v : V, ∀ z ∈ imGT 0,
    sqBlockSlash W hF gamma (sqMode W (-2) a v) z
      + ∑ᶠ m : ℕ, sqNegTwoTerm W (sqBlockSlash W hF gamma) a v z m = 0) ?_ ?_ ?_ a
  · intro K x hx v
    refine sqWeightNat_induction W (P := fun v ↦ ∀ z ∈ imGT 0,
      sqBlockSlash W hF gamma (sqMode W (-2) x v) z
        + ∑ᶠ m : ℕ, sqNegTwoTerm W (sqBlockSlash W hF gamma) x v z m = 0) ?_ ?_ ?_ v
    · intro n y hy z hz
      exact sqBlockSlash_negTwo_hom hF gamma hx hy z hz
    · intro z hz
      have hterm : ∀ m : ℕ,
          sqNegTwoTerm W (sqBlockSlash W hF gamma) x 0 z m = 0 := by
        intro m
        rw [sqNegTwoTerm, map_zero, sqBlockSlash_zero, Pi.zero_apply]
        ring
      rw [map_zero, sqBlockSlash_zero, Pi.zero_apply,
        finsum_congr hterm, finsum_zero, add_zero]
    · intro y t hy ht z hz
      have hsy := sqNegTwoTerm_support_finite_of_zero (W := W)
        (sqBlockSlash W hF gamma) (fun z ↦ by simp) x y z
      have hst := sqNegTwoTerm_support_finite_of_zero (W := W)
        (sqBlockSlash W hF gamma) (fun z ↦ by simp) x t z
      have hterm : ∀ m : ℕ,
          sqNegTwoTerm W (sqBlockSlash W hF gamma) x (y + t) z m =
            sqNegTwoTerm W (sqBlockSlash W hF gamma) x y z m
              + sqNegTwoTerm W (sqBlockSlash W hF gamma) x t z m := by
        intro m
        rw [sqNegTwoTerm, sqNegTwoTerm, sqNegTwoTerm, map_add,
          sqBlockSlash_add, Pi.add_apply]
        ring
      rw [map_add, sqBlockSlash_add, Pi.add_apply,
        finsum_congr hterm, finsum_add_distrib hsy hst]
      linear_combination hy z hz + ht z hz
  · intro v z hz
    have hterm : ∀ m : ℕ,
        sqNegTwoTerm W (sqBlockSlash W hF gamma) 0 v z m = 0 := by
      intro m
      rw [sqNegTwoTerm, map_zero, LinearMap.zero_apply, sqBlockSlash_zero, Pi.zero_apply]
      ring
    rw [map_zero, LinearMap.zero_apply, sqBlockSlash_zero, Pi.zero_apply,
      finsum_congr hterm, finsum_zero, add_zero]
  · intro x y hx hy v z hz
    have hsx := sqNegTwoTerm_support_finite_of_zero (W := W)
      (sqBlockSlash W hF gamma) (fun z ↦ by simp) x v z
    have hsy := sqNegTwoTerm_support_finite_of_zero (W := W)
      (sqBlockSlash W hF gamma) (fun z ↦ by simp) y v z
    have hterm : ∀ m : ℕ,
        sqNegTwoTerm W (sqBlockSlash W hF gamma) (x + y) v z m =
          sqNegTwoTerm W (sqBlockSlash W hF gamma) x v z m
            + sqNegTwoTerm W (sqBlockSlash W hF gamma) y v z m := by
      intro m
      rw [sqNegTwoTerm, sqNegTwoTerm, sqNegTwoTerm, map_add,
        LinearMap.add_apply, sqBlockSlash_add, Pi.add_apply]
      ring
    rw [map_add, LinearMap.add_apply, sqBlockSlash_add, Pi.add_apply,
      finsum_congr hterm, finsum_add_distrib hsx hsy]
    linear_combination hx v z hz + hy v z hz

/-- The globally linear square-weight slash preserves the source-correct block
conditions. -/
theorem IsSqGradedBlock.sqBlockSlash (hF : IsSqGradedBlock W F) (gamma : SL(2, ℤ)) :
    IsSqGradedBlock W (sqBlockSlash W hF gamma) where
  holo := fun v ↦ by
    refine sqWeightNat_induction W (P := fun v ↦
      DifferentiableOn ℂ (_root_.VOA.sqBlockSlash W hF gamma v) (imGT 0)) ?_ ?_ ?_ v
    · intro n x hx
      rw [sqBlockSlash_of_mem W hF gamma hx]
      exact differentiableOn_slashC (n : ℤ) gamma (hF.holo x)
    · change DifferentiableOn ℂ
        (_root_.VOA.sqBlockSlash W hF gamma (0 : V)) (imGT 0)
      rw [sqBlockSlash_zero]
      exact differentiableOn_const 0
    · intro x y hx hy
      rw [sqBlockSlash_add]
      exact hx.add hy
  addv := fun v w z ↦ congrFun (sqBlockSlash_add W hF gamma v w) z
  smulv := fun c v z ↦ by
    have h := congrFun (sqBlockSlash_smul W hF gamma c v) z
    simpa only [Pi.smul_apply, smul_eq_mul] using h
  vanish := sqBlockSlash_vanish hF gamma
  negTwo := sqBlockSlash_negTwo hF gamma
  omega := fun n v hv z hz ↦
    omega_serre_slash (F := F) (G := _root_.VOA.sqBlockSlash W hF gamma) hF.holo
      (fun k u hu w hw ↦ hF.omega k u hu w hw)
      (isSlashOf_sqBlockSlash W hF gamma) hv hz

end

end VOA
