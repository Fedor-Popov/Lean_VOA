/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesArakawaClosure

/-!
# The horizontal triplet of a weight-two highest vector

On the universal affine vacuum module `V^k(sl₂)` the horizontal lowering zero mode `f₀` is
locally nilpotent (`horizontalLowering_locallyNilpotent`; the elementary current-word argument of
`AffineSl2BoundaryMaximalIdeal.horizontalRaisingLocallyNilpotent_universal`, run for `f₀`).
Consequently a horizontal highest vector of `sl₂`-weight `2` spans a triplet:

* `f0_cube_eq_zero` — `e₀ s = 0`, `h₀ s = 2 s` imply `f₀³ s = 0`.

(The vector `u = f₀³ s` is horizontal-highest of weight `-4`; the `sl₂` string identity
`e₀ f₀^{j+1} u = (j+1)(-4-j) f₀^j u` and local nilpotence of `f₀` force `u = 0`.)

Everything here is proved; no new axiom.
-/

namespace VOA.TwoSeries.SliceMap

open VOA.AffineVOA VOA.AffineVOA.SugawaraCov VOA.AffineVOA.Strong
open scoped BigOperators

noncomputable section

variable {k : ℂ}

/-! ## §1  Local nilpotence of `f₀` -/

/-- `f₀` kills some power-image of `v`. -/
def FKilled (v : WakModule k) : Prop := ∃ r : ℕ, (J k 1 0 ^ r) v = 0

theorem FKilled.zero : FKilled (0 : WakModule k) := ⟨0, by simp⟩

theorem FKilled.add {u v : WakModule k} (hu : FKilled u) (hv : FKilled v) : FKilled (u + v) := by
  obtain ⟨r, hr⟩ := hu
  obtain ⟨q, hq⟩ := hv
  refine ⟨r + q, ?_⟩
  rw [map_add]
  have hru : (J k 1 0 ^ (r + q)) u = 0 := by
    rw [add_comm, pow_add, Module.End.mul_apply, hr, map_zero]
  have hqv : (J k 1 0 ^ (r + q)) v = 0 := by
    rw [pow_add, Module.End.mul_apply, hq, map_zero]
  rw [hru, hqv, add_zero]

theorem FKilled.smul {v : WakModule k} (hv : FKilled v) (c : ℂ) : FKilled (c • v) := by
  obtain ⟨r, hr⟩ := hv
  exact ⟨r, by rw [map_smul, hr, smul_zero]⟩

theorem FKilled.of_apply {v : WakModule k} (hv : FKilled (J k 1 0 v)) : FKilled v := by
  obtain ⟨r, hr⟩ := hv
  exact ⟨r + 1, by rw [pow_succ, Module.End.mul_apply, hr]⟩

theorem FKilled.f_neg (μ : ℤ) {v : WakModule k} (hv : FKilled v) : FKilled (J k 1 μ v) := by
  obtain ⟨r, hr⟩ := hv
  induction r generalizing v with
  | zero =>
      have hv0 : v = 0 := by simpa using hr
      rw [hv0, map_zero]; exact FKilled.zero
  | succ r ih =>
      apply FKilled.of_apply
      rw [f_f_comm]
      exact ih (by simpa only [pow_succ, Module.End.mul_apply] using hr)

theorem FKilled.h_neg (μ : ℤ) {v : WakModule k} (hv : FKilled v) : FKilled (J k 2 μ v) := by
  obtain ⟨r, hr⟩ := hv
  induction r generalizing v with
  | zero =>
      have hv0 : v = 0 := by simpa using hr
      rw [hv0, map_zero]; exact FKilled.zero
  | succ r ih =>
      apply FKilled.of_apply
      rw [f_h_comm, zero_add]
      exact FKilled.add (ih (by simpa only [pow_succ, Module.End.mul_apply] using hr))
        (FKilled.smul (FKilled.f_neg μ ⟨r + 1, hr⟩) _)

theorem FKilled.e_neg (μ : ℤ) (hμ : μ ≠ 0) {v : WakModule k} (hv : FKilled v) :
    FKilled (J k 0 μ v) := by
  obtain ⟨r, hr⟩ := hv
  induction r generalizing v with
  | zero =>
      have hv0 : v = 0 := by simpa using hr
      rw [hv0, map_zero]; exact FKilled.zero
  | succ r ih =>
      apply FKilled.of_apply
      rw [f0_e_comm k μ hμ]
      exact FKilled.add (ih (by simpa only [pow_succ, Module.End.mul_apply] using hr))
        (FKilled.smul (FKilled.h_neg μ ⟨r + 1, hr⟩) _)

theorem fin3_cases' (a : Fin 3) : a = 0 ∨ a = 1 ∨ a = 2 := by
  fin_cases a <;> simp

theorem FKilled.wordStateA : ∀ l : List (Fin 3 × ℕ), FKilled (wordStateA k l)
  | [] => ⟨1, by simpa using J_vacuum_nonneg k 1 (le_refl (0 : ℤ))⟩
  | (a, n) :: l => by
      rw [wordStateA_cons]
      have ih := FKilled.wordStateA l
      rcases fin3_cases' a with rfl | rfl | rfl
      · exact FKilled.e_neg _ (by omega) ih
      · exact FKilled.f_neg _ ih
      · exact FKilled.h_neg _ ih

/-- **`f₀` is locally nilpotent on `V^k(sl₂)`.** -/
theorem horizontalLowering_locallyNilpotent (v : WakModule k) : FKilled v := by
  have hv : v ∈ Submodule.span ℂ (Set.range (wordStateA k)) := by
    rw [wordStateA_span]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      exact FKilled.wordStateA l
  | zero => exact FKilled.zero
  | add u v _ _ hu hv => exact FKilled.add hu hv
  | smul c v _ hv => exact FKilled.smul hv c

/-! ## §2  `sl₂` strings -/

theorem h0_fpow (u : WakModule k) (μ : ℂ) (hh : J k 2 0 u = μ • u) (j : ℕ) :
    J k 2 0 ((J k 1 0 ^ j) u) = (μ - 2 * j) • (J k 1 0 ^ j) u := by
  induction j with
  | zero => simpa using hh
  | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, h_f_comm, zero_add, ih, map_smul]
      push_cast
      module

theorem e0_fpow (u : WakModule k) (μ : ℂ) (he : J k 0 0 u = 0) (hh : J k 2 0 u = μ • u)
    (j : ℕ) :
    J k 0 0 ((J k 1 0 ^ (j + 1)) u) = (((j : ℂ) + 1) * (μ - j)) • (J k 1 0 ^ j) u := by
  induction j with
  | zero => simp [e0_f0_comm, he, hh]
  | succ j ih =>
      rw [pow_succ' _ (j + 1), Module.End.mul_apply, e0_f0_comm, ih, h0_fpow u μ hh, map_smul,
        ← Module.End.mul_apply, ← pow_succ']
      push_cast
      module

/-- A horizontal highest vector of non-natural weight is zero. -/
theorem eq_zero_of_highest (u : WakModule k) (μ : ℂ) (he : J k 0 0 u = 0)
    (hh : J k 2 0 u = μ • u) (hμ : ∀ j : ℕ, μ ≠ j) : u = 0 := by
  obtain ⟨N, hN⟩ := horizontalLowering_locallyNilpotent u
  have key : ∀ i, (J k 1 0 ^ (i + 1)) u = 0 → (J k 1 0 ^ i) u = 0 := by
    intro i hi
    have h := e0_fpow u μ he hh i
    rw [hi, map_zero] at h
    have hc : ((i : ℂ) + 1) * (μ - i) ≠ 0 :=
      mul_ne_zero (Nat.cast_add_one_ne_zero i) (sub_ne_zero.mpr (hμ i))
    exact (smul_eq_zero.mp h.symm).resolve_left hc
  have : ∀ j ≤ N, (J k 1 0 ^ (N - j)) u = 0 := by
    intro j hj
    induction j with
    | zero => simpa using hN
    | succ j ih =>
        apply key
        rw [show N - (j + 1) + 1 = N - j by omega]
        exact ih (by omega)
  simpa using this N le_rfl

/-- **A weight-two horizontal highest vector spans a triplet:** `f₀³ s = 0`. -/
theorem f0_cube_eq_zero (s : WakModule k) (he : J k 0 0 s = 0) (hh : J k 2 0 s = (2 : ℂ) • s) :
    J k 1 0 (J k 1 0 (J k 1 0 s)) = 0 := by
  have h3 : J k 1 0 (J k 1 0 (J k 1 0 s)) = (J k 1 0 ^ 3) s := by
    simp [pow_succ, Module.End.mul_apply]
  rw [h3]
  apply eq_zero_of_highest _ (-4)
  · have := e0_fpow s 2 he hh 2
    rw [this]
    norm_num
  · rw [h0_fpow s 2 hh 3]; norm_num
  · intro j hj
    have : ((j : ℂ)).re = -4 := by rw [← hj]; norm_num
    simp at this
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

end

end VOA.TwoSeries.SliceMap
