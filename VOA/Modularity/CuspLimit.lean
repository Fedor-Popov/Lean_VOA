/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.CuspDegeneration
import VOA.Modularity.CuspFunctionalCount

/-!
# The `q → 0` limit of Zhu's relation space **is** `O(𝒱) + span{a[0]v}`

`Modularity.CuspDegeneration` proved DLM Lemma 9.2(c) as an identity of vectors.  Here it is used
to identify the cusp specialisation of `blockRelSpan` — the same two generator families with
`G_{2n}(z₀)` replaced by its constant term `zhuG n 0` — with the algebraic object
`cuspRelSpan W = O(𝒱) ⊔ span{a[0]v}`, whose quotient is `A(𝒱)/[A(𝒱),A(𝒱)]`
(`cuspRelSpanQuotEquiv`).

## Main results

* `blockRelSpanAtCusp W` — the `q → 0` specialisation of `blockRelSpan`;
* `blockRelSpanAtCusp_le_cuspRelSpan` — **unconditional** (`⊆`, from `negTwoFamily_cusp`);
* `cuspRelSpan_le_blockRelSpanAtCusp` — the reverse, using `zhuMul_L_base`
  (`O(𝒱)`'s generators *are* Zhu's `a ∘ b`) and `VacuumGradeZero` for the grade-`0` slot;
* `blockRelSpanAtCusp_eq_cuspRelSpan` and `finrank_quot_blockRelSpanAtCusp_eq` —
  `dim (𝒱 ⧸ blockRelSpanAtCusp W) = dim (A(𝒱)/[A(𝒱),A(𝒱)])`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  Sole carried hypothesis: `VacuumGradeZero`.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

section

variable (W : VertexOperatorAlgebra 𝒱)

/-- **The `q → 0` specialisation of `blockRelSpan`** — literally `blockRelSpan`'s two generator
families with the Eisenstein values `zhuGC (m+2) z₀` replaced by the constant terms
`zhuG (m+2) 0`. -/
def blockRelSpanAtCusp : Submodule ℂ 𝒱 :=
  Submodule.span ℂ
    ({x : 𝒱 | ∃ (ka : ℕ) (a v : 𝒱), 1 ≤ ka ∧ a ∈ W.grading (ka : ℤ) ∧ x = vSqZ W a ka 0 v} ∪
     {x : 𝒱 | ∃ (ka K : ℕ) (a v : 𝒱), 1 ≤ ka ∧ a ∈ W.grading (ka : ℤ) ∧
        (∀ m : ℕ, K ≤ m → vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v = 0) ∧
        x = vSqZ W a ka (-2) v + ∑ m ∈ Finset.range K,
              (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0)
                • vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v})

variable {W}

theorem vSqZ_zero_mem_blockRelSpanAtCusp {ka : ℕ} (hka : 1 ≤ ka) {a : 𝒱}
    (ha : a ∈ W.grading (ka : ℤ)) (v : 𝒱) : vSqZ W a ka 0 v ∈ blockRelSpanAtCusp W :=
  Submodule.subset_span (Or.inl ⟨ka, a, v, hka, ha, rfl⟩)

/-- The truncated tail sum is the `finsum` of `negTwoFamily_cusp`. -/
theorem negTwo_cusp_finsum_eq_sum {ka K : ℕ} {a v : 𝒱}
    (hK : ∀ m : ℕ, K ≤ m → vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v = 0) :
    (∑ᶠ m : ℕ, (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0)
        • vSqZ W a ka (2 * ((m : ℤ) + 2) - 2) v)
      = ∑ m ∈ Finset.range K, (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0)
        • vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v := by
  classical
  refine finsum_eq_finsetSum_of_support_subset _ (fun m hm => ?_)
  simp only [Function.mem_support, ne_eq] at hm
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hc
  push_neg at hc
  have h := hK (m + 1) (by omega)
  rw [show (2 * ((((m : ℕ) + 1 : ℕ) : ℤ) + 1) - 2) = 2 * ((m : ℤ) + 2) - 2 from by
    push_cast; ring] at h
  exact hm (by rw [h, smul_zero])

/-- **`⊆`, unconditional**: every cusp relation lies in `O(𝒱) ⊔ span{a[0]v}`. -/
theorem blockRelSpanAtCusp_le_cuspRelSpan :
    blockRelSpanAtCusp W ≤ cuspRelSpan W := by
  rw [blockRelSpanAtCusp, Submodule.span_le]
  rintro x (⟨ka, a, v, hka, ha, rfl⟩ | ⟨ka, K, a, v, hka, ha, hK, rfl⟩)
  · exact vSqZ_zero_mem_cuspRelSpan hka ha v
  · rw [← negTwo_cusp_finsum_eq_sum hK, negTwoFamily_cusp W hka a v]
    exact (cuspRelSpan W).add_mem (O_le_cuspRelSpan (Pres_mem_O W ha v 0))
      (Submodule.smul_mem _ _ (vSqZ_zero_mem_cuspRelSpan hka ha v))

/-- Zhu's `a ∘ v` lies in the cusp relation space. -/
theorem pres_zero_mem_blockRelSpanAtCusp {ka : ℕ} (hka : 1 ≤ ka) {a : 𝒱}
    (ha : a ∈ W.grading (ka : ℤ)) (v : 𝒱) : Pres W ka a v 0 ∈ blockRelSpanAtCusp W := by
  obtain ⟨K, hK⟩ := vSqZ_tail_eventually_zero W a ka v
  have hmem : vSqZ W a ka (-2) v + ∑ m ∈ Finset.range K,
      (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0)
        • vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v ∈ blockRelSpanAtCusp W :=
    Submodule.subset_span (Or.inr ⟨ka, K, a, v, hka, ha, hK, rfl⟩)
  rw [← negTwo_cusp_finsum_eq_sum hK, negTwoFamily_cusp W hka a v] at hmem
  have hsub := (blockRelSpanAtCusp W).sub_mem hmem
    (Submodule.smul_mem _ (1 / 12 : ℂ) (vSqZ_zero_mem_blockRelSpanAtCusp hka ha v))
  simpa using hsub

theorem pres_eq_sum_range (W : VertexOperatorAlgebra 𝒱) (M : ℕ) (a b : 𝒱) :
    Pres W M a b 0
      = ∑ i ∈ Finset.range (M + 1), cbz (M : ℤ) (i : ℤ) • W.smul a ((i : ℤ) - 2) b := by
  rw [Pres, Nat.add_zero]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show ((M : ℤ) + ((0 : ℕ) : ℤ)) = (M : ℤ) from by push_cast; ring,
    show ((i : ℤ) - 2 - ((0 : ℕ) : ℤ)) = (i : ℤ) - 2 from by push_cast; ring]

/-- **The reverse inclusion.**  `O(𝒱)`'s generators *are* Zhu's `a ∘ v` (`zhuMul_L_base`), and
the grade-`0` slot contributes nothing because `𝟙₍₋₂₎ = 0`. -/
theorem cuspRelSpan_le_blockRelSpanAtCusp :
    cuspRelSpan W ≤ blockRelSpanAtCusp W := by
  have hzero : VacuumGradeZero W := vacuumGradeZero_holds W
  refine sup_le ?_ ?_
  · rw [O_eq_span, Submodule.span_le]
    rintro _ ⟨u, v, rfl⟩
    refine reduce_homogeneous W
      (P := fun u => zhuMul W (W.L (-1) u + W.L 0 u) v ∈ blockRelSpanAtCusp W) ?_ ?_ ?_ u
    · intro M w hw
      rcases lt_trichotomy M 0 with hM | hM | hM
      · have hw0 : w = 0 := by
          rw [W.positivity M hM] at hw
          simpa using hw
        subst hw0
        simpa using (blockRelSpanAtCusp W).zero_mem
      · subst hM
        have hw0 : w ∈ W.grading (((0 : ℕ) : ℕ) : ℤ) := by simpa using hw
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (hzero (by simpa using hw))
        rw [zhuMul_L_base W hw0 v, Finset.sum_range_one]
        have : W.smul (c • W.vacuum) ((0 : ℕ) - 2 : ℤ) v = 0 := by
          rw [PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_vacuum_left, if_neg (by decide),
            smul_zero]
        rw [this, smul_zero]
        exact (blockRelSpanAtCusp W).zero_mem
      · have hka : 1 ≤ M.toNat := by omega
        have hw' : w ∈ W.grading ((M.toNat : ℕ) : ℤ) := by
          rwa [show ((M.toNat : ℕ) : ℤ) = M from by omega]
        rw [zhuMul_L_base W hw' v, ← pres_eq_sum_range W M.toNat w v]
        exact pres_zero_mem_blockRelSpanAtCusp hka hw' v
    · simp only [map_zero, add_zero, zhuMul_zero_left]
      exact (blockRelSpanAtCusp W).zero_mem
    · intro x y hx hy
      rw [show (W.L (-1)) (x + y) + (W.L 0) (x + y)
          = ((W.L (-1)) x + (W.L 0) x) + ((W.L (-1)) y + (W.L 0) y) from by
        simp only [map_add]; abel, zhuMul_add_left]
      exact (blockRelSpanAtCusp W).add_mem hx hy
  · rw [Submodule.span_le]
    rintro _ ⟨ka, a, v, hka, ha, rfl⟩
    exact vSqZ_zero_mem_blockRelSpanAtCusp hka ha v

/-- **The `q → 0` limit of Zhu's genus-one relation space IS `O(𝒱) + span{a[0]v}`.** -/
theorem blockRelSpanAtCusp_eq_cuspRelSpan :
    blockRelSpanAtCusp W = cuspRelSpan W :=
  le_antisymm blockRelSpanAtCusp_le_cuspRelSpan (cuspRelSpan_le_blockRelSpanAtCusp)

/-- Hence the cusp fibre of the genus-one relations has the intrinsic dimension
`dim A(𝒱)/[A(𝒱),A(𝒱)]`. -/
theorem finrank_quot_blockRelSpanAtCusp_eq :
    letI := instRingA W
    letI := instAlgebraA W
    Module.finrank ℂ (𝒱 ⧸ blockRelSpanAtCusp W)
      = Module.finrank ℂ (A W ⧸ commSpan ℂ (A W)) := by
  letI := instRingA W
  letI := instAlgebraA W
  rw [blockRelSpanAtCusp_eq_cuspRelSpan]
  exact finrank_quot_cuspRelSpan_eq

end

end VOA
