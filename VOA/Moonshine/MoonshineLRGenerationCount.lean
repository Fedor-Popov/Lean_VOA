import VOA.Moonshine.MoonshineLRM5Product
import Mathlib.Data.Finsupp.Order
import Mathlib.Order.Interval.Finset.Nat

/-!
# Counting exponent vectors by weight

Let `ι` be a set of basis vectors with degrees `deg i ∈ ℕ × ℕ` in the open cone (`1 ≤` both
coordinates), finitely many of each degree. An exponent vector `f : ι →₀ ℕ` has weight
`wt f = Σ_i f(i) • deg i`. Then `N(Γ) = #{f : wt f = Γ}` is finite (`expVectors Γ`), and satisfies
the logarithmic-derivative recursion (`count_recursion`):
`Γ.1 · N(Γ) = Σ_i Σ_{k ≥ 1, k • deg i ≤ Γ} (deg i).1 · N(Γ − k • deg i)`.
Double count the triples `(f, i, k)` with `wt f = Γ`, `1 ≤ k ≤ f i`; then `f ↦ f − k • eᵢ` is a
bijection onto the exponent vectors of weight `Γ − k • deg i`.

This is the combinatorial half of `Π (1 − e^γ)^{−d(γ)} = Σ_Γ N(Γ) e^Γ` (PBW character of `U(𝔲⁺)`).
-/

namespace VOA.Moonshine.ConwayNorton.M8

open Finset

variable {ι : Type*} (deg : ι → ℕ × ℕ)

/-- The weight `Σ_i f(i) • deg i` of an exponent vector. -/
def expWeight (f : ι →₀ ℕ) : ℕ × ℕ := f.sum fun i k => k • deg i

theorem expWeight_add (f g : ι →₀ ℕ) : expWeight deg (f + g) = expWeight deg f + expWeight deg g :=
  Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)

theorem expWeight_single (i : ι) (k : ℕ) : expWeight deg (Finsupp.single i k) = k • deg i :=
  Finsupp.sum_single_index (zero_smul _ _)

/-- Each basis vector in the support contributes `f i • deg i ≤ wt f`. -/
theorem smul_deg_le_expWeight (f : ι →₀ ℕ) (i : ι) : f i • deg i ≤ expWeight deg f := by
  by_cases hi : i ∈ f.support
  · unfold expWeight Finsupp.sum
    exact Finset.single_le_sum (f := fun i => f i • deg i)
      (fun _ _ => Prod.le_def.mpr ⟨Nat.zero_le _, Nat.zero_le _⟩) hi
  · rw [Finsupp.notMem_support_iff.mp hi, zero_smul]
    exact Prod.le_def.mpr ⟨Nat.zero_le _, Nat.zero_le _⟩

theorem le_nsmul_prod (x : ℕ × ℕ) {n : ℕ} (hn : 1 ≤ n) : x ≤ n • x := by
  refine ⟨?_, ?_⟩ <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
    exact Nat.le_mul_of_pos_left _ hn

theorem nsmul_le_nsmul_prod (x : ℕ × ℕ) {k n : ℕ} (hkn : k ≤ n) : k • x ≤ n • x := by
  refine ⟨?_, ?_⟩ <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
    exact Nat.mul_le_mul_right _ hkn

variable (hdeg : ∀ i, 1 ≤ (deg i).1 ∧ 1 ≤ (deg i).2)
variable (low : (ℕ × ℕ) → Finset ι) (hlow : ∀ Γ i, i ∈ low Γ ↔ deg i ≤ Γ)

/-- The `p`-weight is `Σ_i f(i) · (deg i).1`. -/
theorem expWeight_fst (f : ι →₀ ℕ) : (expWeight deg f).1 = f.sum fun i k => k * (deg i).1 := by
  unfold expWeight Finsupp.sum
  rw [Prod.fst_sum]
  rfl

/-- The finite set of exponent vectors of weight `Γ`. -/
noncomputable def expVectors (Γ : ℕ × ℕ) : Finset (ι →₀ ℕ) := by
  classical
  exact (Finset.finsupp (low Γ) (fun _ => Finset.range (Γ.1 + 1))).filter
    fun f => expWeight deg f = Γ

include hdeg hlow in
theorem mem_expVectors (Γ : ℕ × ℕ) (f : ι →₀ ℕ) :
    f ∈ expVectors deg low Γ ↔ expWeight deg f = Γ := by
  classical
  unfold expVectors
  rw [Finset.mem_filter, Finset.mem_finsupp_iff]
  constructor
  · exact fun h => h.2
  · intro hw
    refine ⟨⟨fun i hi => ?_, fun i _ => ?_⟩, hw⟩
    · rw [hlow]
      have h1 := smul_deg_le_expWeight deg f i
      rw [hw] at h1
      have hfi : 1 ≤ f i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
      exact le_trans (le_nsmul_prod (deg i) hfi) h1
    · rw [Finset.mem_range, Nat.lt_succ_iff]
      have h1 := (smul_deg_le_expWeight deg f i).1
      rw [hw] at h1
      simp only [Prod.smul_fst, smul_eq_mul] at h1
      exact le_trans (Nat.le_mul_of_pos_right _ (hdeg i).1) h1

/-- `N(Γ)`: the number of exponent vectors of weight `Γ`. -/
noncomputable def expCount (Γ : ℕ × ℕ) : ℕ := (expVectors deg low Γ).card

include hdeg hlow in
/-- The exponent vectors of weight `Γ` with `f i ≥ k` correspond to those of weight
`Γ − k • deg i`, via `f ↦ f − k • eᵢ` (when `k • deg i ≤ Γ`; otherwise there are none). -/
theorem card_filter_le_eq (Γ : ℕ × ℕ) (i : ι) (k : ℕ) :
    ((expVectors deg low Γ).filter fun f => k ≤ f i).card =
      if k • deg i ≤ Γ then expCount deg low (Γ - k • deg i) else 0 := by
  classical
  split_ifs with hle
  · refine Finset.card_nbij' (fun f => f - Finsupp.single i k) (fun g => g + Finsupp.single i k)
      ?_ ?_ ?_ ?_
    · intro f hf
      rw [Finset.mem_coe, Finset.mem_filter, mem_expVectors deg hdeg low hlow] at hf
      rw [Finset.mem_coe, mem_expVectors deg hdeg low hlow]
      have hdec : f = (f - Finsupp.single i k) + Finsupp.single i k := by
        ext j
        simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
        by_cases hj : j = i
        · subst hj
          rw [Finsupp.single_eq_same]
          omega
        · rw [Finsupp.single_eq_of_ne hj]
          omega
      have h := hf.1
      rw [hdec, expWeight_add, expWeight_single] at h
      rw [← h, add_tsub_cancel_right]
    · intro g hg
      rw [Finset.mem_coe, mem_expVectors deg hdeg low hlow] at hg
      rw [Finset.mem_coe, Finset.mem_filter, mem_expVectors deg hdeg low hlow, expWeight_add,
        expWeight_single, hg, tsub_add_cancel_of_le hle]
      refine ⟨rfl, ?_⟩
      simp
    · intro f hf
      rw [Finset.mem_coe, Finset.mem_filter] at hf
      ext j
      simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
      by_cases hj : j = i
      · subst hj
        rw [Finsupp.single_eq_same]
        have := hf.2
        omega
      · rw [Finsupp.single_eq_of_ne hj]
        omega
    · intro g _
      ext j
      simp
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro f hf hk
    rw [mem_expVectors deg hdeg low hlow] at hf
    apply hle
    rw [← hf]
    exact le_trans (nsmul_le_nsmul_prod (deg i) hk) (smul_deg_le_expWeight deg f i)

include hdeg hlow in
/-- **The logarithmic-derivative recursion for the counts:**
`Γ.1 · N(Γ) = Σ_{i ∈ low Γ} Σ_{1 ≤ k ≤ Γ.1} [k • deg i ≤ Γ] (deg i).1 · N(Γ − k • deg i)`. -/
theorem count_recursion (Γ : ℕ × ℕ) :
    Γ.1 * expCount deg low Γ =
      ∑ i ∈ low Γ, ∑ k ∈ Finset.Icc 1 Γ.1,
        if k • deg i ≤ Γ then (deg i).1 * expCount deg low (Γ - k • deg i) else 0 := by
  classical
  -- LHS: sum over f of Γ.1 = Σ_i f(i) (deg i).1
  have h1 : Γ.1 * expCount deg low Γ =
      ∑ f ∈ expVectors deg low Γ, ∑ i ∈ low Γ, f i * (deg i).1 := by
    rw [expCount, Finset.card_eq_sum_ones, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f hf => ?_
    rw [mul_one]
    rw [mem_expVectors deg hdeg low hlow] at hf
    conv_lhs => rw [← hf]
    rw [expWeight_fst deg]
    refine Finsupp.sum_of_support_subset f (fun j hj => ?_) _ (fun j _ => by simp)
    rw [hlow]
    have h2 := smul_deg_le_expWeight deg f j
    rw [hf] at h2
    have hfj : 1 ≤ f j := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
    exact le_trans (le_nsmul_prod (deg j) hfj) h2
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  -- Σ_f f(i) (deg i).1 = (deg i).1 · Σ_{k ∈ [1, Γ.1]} #{f : f i ≥ k}
  have h2 : ∀ f ∈ expVectors deg low Γ,
      f i * (deg i).1 = ∑ k ∈ Finset.Icc 1 Γ.1, if k ≤ f i then (deg i).1 else 0 := by
    intro f hf
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
    congr 1
    have hfi : f i ≤ Γ.1 := by
      rw [mem_expVectors deg hdeg low hlow] at hf
      have h3 := (smul_deg_le_expWeight deg f i).1
      rw [hf] at h3
      simp only [Prod.smul_fst, smul_eq_mul] at h3
      exact le_trans (Nat.le_mul_of_pos_right _ (hdeg i).1) h3
    rw [show (Finset.Icc 1 Γ.1).filter (fun k => k ≤ f i) = Finset.Icc 1 (f i) by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega]
    simp
  rw [Finset.sum_congr rfl h2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, card_filter_le_eq deg hdeg low hlow]
  split_ifs <;> ring

end VOA.Moonshine.ConwayNorton.M8
