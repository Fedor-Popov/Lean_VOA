import VOA.Huang.GenusOneDetermination

/-! # The vector space of analytic insertion blocks

The finite-tail and linearity proofs are the module analogues of
`VOA.Modularity.BlockSpace`. Restricting to the upper half-plane is essential:
values outside it are not analytically constrained by the block definition.
-/
namespace VOA.Huang.GenusOne
open VOA Complex
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {A : OrdVModule W M}

section Tails

/-- The `[−2]`-tail as a finite sum, with a bound depending only on `(a, v)`. -/
theorem insertionNegTwoSum {F : M → ℂ → ℂ} (hF0 : ∀ z : ℂ, F 0 z = 0) {a : V} {v : M} {ka K₀ : ℕ}
    (hK₀ : ∀ m : ℕ, K₀ ≤ m → sqAct A a ka (2 * (m + 1) - 2 : ℤ) v = 0) (z : ℂ) :
    (∑ᶠ m : ℕ, ((2 * (m + 1) - 1 : ℕ) : ℂ)
        * (zhuGC (m + 1) z * F (sqAct A a ka (2 * (m + 1) - 2 : ℤ) v) z))
      = ∑ m ∈ Finset.range K₀, ((2 * (m + 1) - 1 : ℕ) : ℂ)
        * (zhuGC (m + 1) z * F (sqAct A a ka (2 * (m + 1) - 2 : ℤ) v) z) := by
  classical
  refine finsum_eq_finsetSum_of_support_subset _ (fun m hm => ?_)
  simp only [Function.mem_support, ne_eq] at hm
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hc
  exact hm (by rw [hK₀ m (by omega), hF0, mul_zero, mul_zero])

/-- The `ω`-tail as a genuine `Finset` sum. -/
theorem insertionOmegaSum {F : M → ℂ → ℂ} (hF0 : ∀ z : ℂ, F 0 z = 0) {v : M} {K₀ : ℕ}
    (hK₀ : ∀ m : ℕ, K₀ ≤ m → sqL A (2 * (m + 1) - 2 : ℤ) v = 0) (z : ℂ) :
    (∑ᶠ m : ℕ, zhuGC (m + 1) z * F (sqL A (2 * (m + 1) - 2 : ℤ) v) z)
      = ∑ m ∈ Finset.range K₀, zhuGC (m + 1) z * F (sqL A (2 * (m + 1) - 2 : ℤ) v) z := by
  classical
  refine finsum_eq_finsetSum_of_support_subset _ (fun m hm => ?_)
  simp only [Function.mem_support, ne_eq] at hm
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hc
  exact hm (by rw [hK₀ m (by omega), hF0, mul_zero])

end Tails

/-! ## Linearity of the block conditions -/

section Linear

theorem IsInsertionAnalyticBlock.vanish_apply {F : M → ℂ → ℂ} (hF : IsInsertionAnalyticBlock A F)
    (ka : ℕ)
    (hka : 1 ≤ ka) {a : V} (ha : a ∈ W.grading (ka : ℤ)) (v : M) (z : ℂ) :
    F (sqAct A a ka 0 v) z = 0 := by
  rw [hF.vanish ka hka a ha v]; rfl

theorem isInsertionAnalyticBlock_zero :
    IsInsertionAnalyticBlock A (fun (_ : M) (_ : ℂ) => (0 : ℂ)) where
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

theorem IsInsertionAnalyticBlock.smul {F : M → ℂ → ℂ} (hF : IsInsertionAnalyticBlock A F) (c : ℂ) :
    IsInsertionAnalyticBlock A (fun v z => c * F v z) where
  holo := fun v => (hF.holo v).const_mul c
  addv := fun v w z => by rw [hF.addv]; ring
  smulv := fun d v z => by rw [hF.smulv]; ring
  vanish := fun ka hka a ha v => by
    funext z
    simp only [Pi.zero_apply]
    rw [hF.vanish_apply ka hka ha v z, mul_zero]
  negTwo := fun ka hka a ha v z hz => by
    obtain ⟨K₀, hK₀⟩ := sqAct_tail_eventually_zero A a ka v
    have hlaw := hF.negTwo ka hka a ha v z hz
    rw [insertionNegTwoSum hF.zerov hK₀ z] at hlaw
    rw [insertionNegTwoSum (F := fun v z => c * F v z)
      (fun z => by change c * F 0 z = 0; rw [hF.zerov]; ring) hK₀ z]
    have hpull : ∑ m ∈ Finset.range K₀, ((2 * (m + 1) - 1 : ℕ) : ℂ)
          * (zhuGC (m + 1) z * (c * F (sqAct A a ka (2 * (m + 1) - 2 : ℤ) v) z))
        = c * ∑ m ∈ Finset.range K₀, ((2 * (m + 1) - 1 : ℕ) : ℂ)
          * (zhuGC (m + 1) z * F (sqAct A a ka (2 * (m + 1) - 2 : ℤ) v) z) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    rw [hpull]
    linear_combination c * hlaw
  omega := fun v z hz => by
    obtain ⟨K₀, hK₀⟩ := sqL_tail_eventually_zero A v
    have hlaw := hF.omega v z hz
    rw [insertionOmegaSum hF.zerov hK₀ z] at hlaw
    rw [insertionOmegaSum (F := fun v z => c * F v z)
      (fun z => by change c * F 0 z = 0; rw [hF.zerov]; ring) hK₀ z]
    have hd : _root_.deriv (fun z => c * F v z) z = c * _root_.deriv (F v) z := by
      refine deriv_const_mul c ?_
      exact (hF.holo v).differentiableAt ((isOpen_imGT 0).mem_nhds hz)
    rw [hd]
    have hpull : ∑ m ∈ Finset.range K₀, zhuGC (m + 1) z * (c * F (sqL A (2 * (m + 1) - 2 : ℤ) v) z)
        = c * ∑ m ∈ Finset.range K₀,
            zhuGC (m + 1) z * F (sqL A (2 * (m + 1) - 2 : ℤ) v) z := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    rw [hpull]
    linear_combination c * hlaw

theorem IsInsertionAnalyticBlock.add {F G : M → ℂ → ℂ} (hF : IsInsertionAnalyticBlock A F)
    (hG : IsInsertionAnalyticBlock A G) :
    IsInsertionAnalyticBlock A (fun v z => F v z + G v z) where
  holo := fun v => (hF.holo v).add (hG.holo v)
  addv := fun v w z => by rw [hF.addv, hG.addv]; ring
  smulv := fun c v z => by rw [hF.smulv, hG.smulv]; ring
  vanish := fun ka hka a ha v => by
    funext z
    simp only [Pi.zero_apply]
    rw [hF.vanish_apply ka hka ha v z, hG.vanish_apply ka hka ha v z, add_zero]
  negTwo := fun ka hka a ha v z hz => by
    obtain ⟨K₀, hK₀⟩ := sqAct_tail_eventually_zero A a ka v
    have hlawF := hF.negTwo ka hka a ha v z hz
    have hlawG := hG.negTwo ka hka a ha v z hz
    rw [insertionNegTwoSum hF.zerov hK₀ z] at hlawF
    rw [insertionNegTwoSum hG.zerov hK₀ z] at hlawG
    rw [insertionNegTwoSum (F := fun v z => F v z + G v z)
      (fun z => by change F 0 z + G 0 z = 0; rw [hF.zerov, hG.zerov]; ring) hK₀ z]
    have hsplit : ∑ m ∈ Finset.range K₀, ((2 * (m + 1) - 1 : ℕ) : ℂ)
          * (zhuGC (m + 1) z * (F (sqAct A a ka (2 * (m + 1) - 2 : ℤ) v) z
              + G (sqAct A a ka (2 * (m + 1) - 2 : ℤ) v) z))
        = (∑ m ∈ Finset.range K₀, ((2 * (m + 1) - 1 : ℕ) : ℂ)
            * (zhuGC (m + 1) z * F (sqAct A a ka (2 * (m + 1) - 2 : ℤ) v) z))
          + ∑ m ∈ Finset.range K₀, ((2 * (m + 1) - 1 : ℕ) : ℂ)
            * (zhuGC (m + 1) z * G (sqAct A a ka (2 * (m + 1) - 2 : ℤ) v) z) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    rw [hsplit]
    linear_combination hlawF + hlawG
  omega := fun v z hz => by
    obtain ⟨K₀, hK₀⟩ := sqL_tail_eventually_zero A v
    have hlawF := hF.omega v z hz
    have hlawG := hG.omega v z hz
    rw [insertionOmegaSum hF.zerov hK₀ z] at hlawF
    rw [insertionOmegaSum hG.zerov hK₀ z] at hlawG
    rw [insertionOmegaSum (F := fun v z => F v z + G v z)
      (fun z => by change F 0 z + G 0 z = 0; rw [hF.zerov, hG.zerov]; ring) hK₀ z]
    have hd : _root_.deriv (fun z => F v z + G v z) z
        = _root_.deriv (F v) z + _root_.deriv (G v) z := by
      refine deriv_add ?_ ?_
      · exact (hF.holo v).differentiableAt ((isOpen_imGT 0).mem_nhds hz)
      · exact (hG.holo v).differentiableAt ((isOpen_imGT 0).mem_nhds hz)
    rw [hd]
    have hsplit : ∑ m ∈ Finset.range K₀, zhuGC (m + 1) z
          * (F (sqL A (2 * (m + 1) - 2 : ℤ) v) z + G (sqL A (2 * (m + 1) - 2 : ℤ) v) z)
        = (∑ m ∈ Finset.range K₀, zhuGC (m + 1) z * F (sqL A (2 * (m + 1) - 2 : ℤ) v) z)
          + ∑ m ∈ Finset.range K₀, zhuGC (m + 1) z * G (sqL A (2 * (m + 1) - 2 : ℤ) v) z := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    rw [hsplit]
    linear_combination hlawF + hlawG

theorem IsInsertionAnalyticBlock.sub {F G : M → ℂ → ℂ} (hF : IsInsertionAnalyticBlock A F)
    (hG : IsInsertionAnalyticBlock A G) :
    IsInsertionAnalyticBlock A (fun v z => F v z - G v z) := by
  have h := hF.add (hG.smul (-1))
  refine ⟨fun v => ?_, fun v w z => ?_, fun c v z => ?_, fun ka hka a ha v => ?_,
    fun ka hka a ha v z hz => ?_, fun v z hz => ?_⟩
  · simpa only [neg_one_mul, ← sub_eq_add_neg] using h.holo v
  · simpa only [neg_one_mul, ← sub_eq_add_neg] using h.addv v w z
  · simpa only [neg_one_mul, ← sub_eq_add_neg] using h.smulv c v z
  · simpa only [neg_one_mul, ← sub_eq_add_neg] using h.vanish ka hka a ha v
  · simpa only [neg_one_mul, ← sub_eq_add_neg] using h.negTwo ka hka a ha v z hz
  · simpa only [neg_one_mul, ← sub_eq_add_neg] using h.omega v z hz

/-- **The space of genus-one conformal blocks**, as a `ℂ`-subspace of `M → ℂ → ℂ`. -/
def insertionAnalyticBlocks (A : OrdVModule W M) : Submodule ℂ (M → ℂ → ℂ) where
  carrier := {F : M → ℂ → ℂ | IsInsertionAnalyticBlock A F}
  add_mem' := fun hF hG => hF.add hG
  zero_mem' := isInsertionAnalyticBlock_zero
  smul_mem' := fun c _ hF => hF.smul c

@[simp] theorem mem_insertionAnalyticBlocks (A : OrdVModule W M) (F : M → ℂ → ℂ) :
    F ∈ insertionAnalyticBlocks A ↔ IsInsertionAnalyticBlock A F := Iff.rfl

end Linear

end VOA.Huang.GenusOne
