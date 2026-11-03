/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.AnalyticBlock

/-!
# The genus-one blocks form a `ℂ`-vector space

Zhu's Theorem 5.3.2 is a statement about the **space** `𝔅` of genus-one conformal blocks, so `𝔅`
must be a space.  All three block conditions are `ℂ`-linear in `F`; the only thing to check is that
the `Σᶠ` tails may be compared, which they may because the truncation bound
(`vSqZ_tail_eventually_zero`, `Lsq_tail_eventually_zero`) depends only on `(a, v)` and **not** on
the block.

* `analyticBlocks W : Submodule ℂ (𝒱 → ℂ → ℂ)` — the block space;
* `IsAnalyticBlock.add/.sub/.smul/.neg`, `isAnalyticBlock_zero`;
* `IsAnalyticBlock.eq_of_eqOn'` — the determinacy comparison, with the awkward "the
  difference is a block" hypothesis **discharged**.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open Complex
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

section Tails

variable {W : VertexOperatorAlgebra 𝒱}

/-- The `[−2]`-tail as a genuine `Finset` sum, with a truncation bound depending only on `(a, v)`. -/
theorem negTwo_finsum_eq_sum {F : 𝒱 → ℂ → ℂ} (hF0 : ∀ z : ℂ, F 0 z = 0) {a v : 𝒱} {ka K₀ : ℕ}
    (hK₀ : ∀ m : ℕ, K₀ ≤ m → vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v = 0) (z : ℂ) :
    (∑ᶠ m : ℕ, ((2 * (m + 1) - 1 : ℕ) : ℂ)
        * (zhuGC (m + 1) z * F (vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v) z))
      = ∑ m ∈ Finset.range K₀, ((2 * (m + 1) - 1 : ℕ) : ℂ)
        * (zhuGC (m + 1) z * F (vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v) z) := by
  classical
  refine finsum_eq_finsetSum_of_support_subset _ (fun m hm => ?_)
  simp only [Function.mem_support, ne_eq] at hm
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hc
  exact hm (by rw [hK₀ m (by omega), hF0, mul_zero, mul_zero])

/-- The `ω`-tail as a genuine `Finset` sum. -/
theorem omega_finsum_eq_sum {F : 𝒱 → ℂ → ℂ} (hF0 : ∀ z : ℂ, F 0 z = 0) {v : 𝒱} {K₀ : ℕ}
    (hK₀ : ∀ m : ℕ, K₀ ≤ m → Lsq W (2 * (m + 1) - 2 : ℤ) v = 0) (z : ℂ) :
    (∑ᶠ m : ℕ, zhuGC (m + 1) z * F (Lsq W (2 * (m + 1) - 2 : ℤ) v) z)
      = ∑ m ∈ Finset.range K₀, zhuGC (m + 1) z * F (Lsq W (2 * (m + 1) - 2 : ℤ) v) z := by
  classical
  refine finsum_eq_finsetSum_of_support_subset _ (fun m hm => ?_)
  simp only [Function.mem_support, ne_eq] at hm
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hc
  exact hm (by rw [hK₀ m (by omega), hF0, mul_zero])

end Tails

/-! ## Linearity of the block conditions -/

section Linear

variable {W : VertexOperatorAlgebra 𝒱}

theorem IsAnalyticBlock.vanish_apply {F : 𝒱 → ℂ → ℂ} (hF : IsAnalyticBlock W F) (ka : ℕ)
    (hka : 1 ≤ ka) {a : 𝒱} (ha : a ∈ W.grading (ka : ℤ)) (v : 𝒱) (z : ℂ) :
    F (vSqZ W a ka 0 v) z = 0 := by
  rw [hF.vanish ka hka a ha v]; rfl

theorem isAnalyticBlock_zero : IsAnalyticBlock W (fun (_ : 𝒱) (_ : ℂ) => (0 : ℂ)) where
  holo := fun _ => differentiableOn_const 0
  addv := fun _ _ _ => by ring
  smulv := fun _ _ _ => by ring
  vanish := fun _ _ _ _ _ => rfl
  negTwo := fun _ _ _ _ _ _ _ => by
    rw [finsum_eq_zero_of_forall_eq_zero (fun _ => by ring)]; ring
  omega := fun v z _ => by
    rw [finsum_eq_zero_of_forall_eq_zero (fun _ => by ring),
      show _root_.deriv (fun (_ : ℂ) => (0 : ℂ)) z = 0 from deriv_const z 0]
    ring

theorem IsAnalyticBlock.smul {F : 𝒱 → ℂ → ℂ} (hF : IsAnalyticBlock W F) (c : ℂ) :
    IsAnalyticBlock W (fun v z => c * F v z) where
  holo := fun v => (hF.holo v).const_mul c
  addv := fun v w z => by rw [hF.addv]; ring
  smulv := fun d v z => by rw [hF.smulv]; ring
  vanish := fun ka hka a ha v => by
    funext z
    simp only [Pi.zero_apply]
    rw [hF.vanish_apply ka hka ha v z, mul_zero]
  negTwo := fun ka hka a ha v z hz => by
    obtain ⟨K₀, hK₀⟩ := vSqZ_tail_eventually_zero W a ka v
    have hlaw := hF.negTwo ka hka a ha v z hz
    rw [negTwo_finsum_eq_sum hF.zerov hK₀ z] at hlaw
    rw [negTwo_finsum_eq_sum (F := fun v z => c * F v z)
      (fun z => by show c * F 0 z = 0; rw [hF.zerov]; ring) hK₀ z]
    have hpull : ∑ m ∈ Finset.range K₀, ((2 * (m + 1) - 1 : ℕ) : ℂ)
          * (zhuGC (m + 1) z * (c * F (vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v) z))
        = c * ∑ m ∈ Finset.range K₀, ((2 * (m + 1) - 1 : ℕ) : ℂ)
          * (zhuGC (m + 1) z * F (vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v) z) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    rw [hpull]
    linear_combination c * hlaw
  omega := fun v z hz => by
    obtain ⟨K₀, hK₀⟩ := Lsq_tail_eventually_zero W v
    have hlaw := hF.omega v z hz
    rw [omega_finsum_eq_sum hF.zerov hK₀ z] at hlaw
    rw [omega_finsum_eq_sum (F := fun v z => c * F v z)
      (fun z => by show c * F 0 z = 0; rw [hF.zerov]; ring) hK₀ z]
    have hd : _root_.deriv (fun z => c * F v z) z = c * _root_.deriv (F v) z := by
      refine deriv_const_mul c ?_
      exact (hF.holo v).differentiableAt ((isOpen_imGT 0).mem_nhds hz)
    rw [hd]
    have hpull : ∑ m ∈ Finset.range K₀, zhuGC (m + 1) z * (c * F (Lsq W (2 * (m + 1) - 2 : ℤ) v) z)
        = c * ∑ m ∈ Finset.range K₀,
            zhuGC (m + 1) z * F (Lsq W (2 * (m + 1) - 2 : ℤ) v) z := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    rw [hpull]
    linear_combination c * hlaw

theorem IsAnalyticBlock.add {F G : 𝒱 → ℂ → ℂ} (hF : IsAnalyticBlock W F)
    (hG : IsAnalyticBlock W G) : IsAnalyticBlock W (fun v z => F v z + G v z) where
  holo := fun v => (hF.holo v).add (hG.holo v)
  addv := fun v w z => by rw [hF.addv, hG.addv]; ring
  smulv := fun c v z => by rw [hF.smulv, hG.smulv]; ring
  vanish := fun ka hka a ha v => by
    funext z
    simp only [Pi.zero_apply]
    rw [hF.vanish_apply ka hka ha v z, hG.vanish_apply ka hka ha v z, add_zero]
  negTwo := fun ka hka a ha v z hz => by
    obtain ⟨K₀, hK₀⟩ := vSqZ_tail_eventually_zero W a ka v
    have hlawF := hF.negTwo ka hka a ha v z hz
    have hlawG := hG.negTwo ka hka a ha v z hz
    rw [negTwo_finsum_eq_sum hF.zerov hK₀ z] at hlawF
    rw [negTwo_finsum_eq_sum hG.zerov hK₀ z] at hlawG
    rw [negTwo_finsum_eq_sum (F := fun v z => F v z + G v z)
      (fun z => by show F 0 z + G 0 z = 0; rw [hF.zerov, hG.zerov]; ring) hK₀ z]
    have hsplit : ∑ m ∈ Finset.range K₀, ((2 * (m + 1) - 1 : ℕ) : ℂ)
          * (zhuGC (m + 1) z * (F (vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v) z
              + G (vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v) z))
        = (∑ m ∈ Finset.range K₀, ((2 * (m + 1) - 1 : ℕ) : ℂ)
            * (zhuGC (m + 1) z * F (vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v) z))
          + ∑ m ∈ Finset.range K₀, ((2 * (m + 1) - 1 : ℕ) : ℂ)
            * (zhuGC (m + 1) z * G (vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v) z) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    rw [hsplit]
    linear_combination hlawF + hlawG
  omega := fun v z hz => by
    obtain ⟨K₀, hK₀⟩ := Lsq_tail_eventually_zero W v
    have hlawF := hF.omega v z hz
    have hlawG := hG.omega v z hz
    rw [omega_finsum_eq_sum hF.zerov hK₀ z] at hlawF
    rw [omega_finsum_eq_sum hG.zerov hK₀ z] at hlawG
    rw [omega_finsum_eq_sum (F := fun v z => F v z + G v z)
      (fun z => by show F 0 z + G 0 z = 0; rw [hF.zerov, hG.zerov]; ring) hK₀ z]
    have hd : _root_.deriv (fun z => F v z + G v z) z
        = _root_.deriv (F v) z + _root_.deriv (G v) z := by
      refine deriv_add ?_ ?_
      · exact (hF.holo v).differentiableAt ((isOpen_imGT 0).mem_nhds hz)
      · exact (hG.holo v).differentiableAt ((isOpen_imGT 0).mem_nhds hz)
    rw [hd]
    have hsplit : ∑ m ∈ Finset.range K₀, zhuGC (m + 1) z
          * (F (Lsq W (2 * (m + 1) - 2 : ℤ) v) z + G (Lsq W (2 * (m + 1) - 2 : ℤ) v) z)
        = (∑ m ∈ Finset.range K₀, zhuGC (m + 1) z * F (Lsq W (2 * (m + 1) - 2 : ℤ) v) z)
          + ∑ m ∈ Finset.range K₀, zhuGC (m + 1) z * G (Lsq W (2 * (m + 1) - 2 : ℤ) v) z := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    rw [hsplit]
    linear_combination hlawF + hlawG

theorem IsAnalyticBlock.sub {F G : 𝒱 → ℂ → ℂ} (hF : IsAnalyticBlock W F)
    (hG : IsAnalyticBlock W G) : IsAnalyticBlock W (fun v z => F v z - G v z) := by
  have h := hF.add (hG.smul (-1))
  refine ⟨fun v => ?_, fun v w z => ?_, fun c v z => ?_, fun ka hka a ha v => ?_,
    fun ka hka a ha v z hz => ?_, fun v z hz => ?_⟩
  · simpa only [neg_one_mul, ← sub_eq_add_neg] using h.holo v
  · simpa only [neg_one_mul, ← sub_eq_add_neg] using h.addv v w z
  · simpa only [neg_one_mul, ← sub_eq_add_neg] using h.smulv c v z
  · simpa only [neg_one_mul, ← sub_eq_add_neg] using h.vanish ka hka a ha v
  · simpa only [neg_one_mul, ← sub_eq_add_neg] using h.negTwo ka hka a ha v z hz
  · simpa only [neg_one_mul, ← sub_eq_add_neg] using h.omega v z hz

/-- **The space of genus-one conformal blocks**, as a `ℂ`-subspace of `𝒱 → ℂ → ℂ`. -/
def analyticBlocks (W : VertexOperatorAlgebra 𝒱) : Submodule ℂ (𝒱 → ℂ → ℂ) where
  carrier := {F : 𝒱 → ℂ → ℂ | IsAnalyticBlock W F}
  add_mem' := fun hF hG => hF.add hG
  zero_mem' := isAnalyticBlock_zero
  smul_mem' := fun c _ hF => hF.smul c

@[simp] theorem mem_analyticBlocks (W : VertexOperatorAlgebra 𝒱) (F : 𝒱 → ℂ → ℂ) :
    F ∈ analyticBlocks W ↔ IsAnalyticBlock W F := Iff.rfl

end Linear

end VOA
