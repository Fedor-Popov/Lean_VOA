/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuRingResidue

/-!
# `ZhuHR.right_ideal_core` — the Zhu right-ideal residue core (Zhu Thm 2.1.1) — unconditional

## Status
`sorry`-free, with no project axioms. **`right_ideal_core`** (`u*((L₋₁a+L₀a)*b) ∈ O W`, via
`right_target_expand` + `mode_commutator_uniform` split + the `Pres` collapse through
`ZhuRes.zhu_right_binom`) is *unconditional*, consumed directly by the proved Zhu two-sided-ideal
theorem and hence the unconditional `Ring (A 𝒱)` (`ZhuRingInstance`).
`#print axioms = [propext, Classical.choice, Quot.sound]`.
-/

open VOA VertexOperatorAlgebra
open scoped BigOperators
open Classical

set_option autoImplicit false

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace ZhuHR

/-! ## Step 1: right-target expansion. -/

/-- `zhuMul W u (a∘b) = ∑_p ∑_i (cbz K p * cbz M i) • u₍ₚ₋₁₎(a₍ᵢ₋₂₎b)`. -/
theorem right_target_expand (W : VertexOperatorAlgebra 𝒱) {K M : ℕ} {u a : 𝒱}
    (hu : u ∈ W.grading (K : ℤ)) (ha : a ∈ W.grading (M : ℤ)) (b : 𝒱) :
    zhuMul W u (zhuMul W (W.L (-1) a + W.L 0 a) b)
      = ∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
          (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ))
            • W.smul u ((p : ℤ) - 1) (W.smul a ((i : ℤ) - 2) b) := by
  rw [zhuMul_homogeneous' W hu, show ((K : ℤ).toNat + 1) = K + 1 from by simp]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [zhuMul_L_base W ha b]
  -- distribute the linear map `W.smul u (p-1)` over the i-sum and scalars
  rw [show W.smul u ((p : ℤ) - 1) (∑ i ∈ Finset.range (M + 1),
            cbz (M : ℤ) (i : ℤ) • W.smul a ((i : ℤ) - 2) b)
        = ∑ i ∈ Finset.range (M + 1),
            cbz (M : ℤ) (i : ℤ) • W.smul u ((p : ℤ) - 1) (W.smul a ((i : ℤ) - 2) b) from by
      rw [PreVertexAlgebra.smul_def, map_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [LinearMap.map_smul]; rfl,
    Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]

/-! ## Step 2: the commutator split. -/

/-- `u₍ₚ₋₁₎(a₍ᵢ₋₂₎b) = a₍ᵢ₋₂₎(u₍ₚ₋₁₎b) + ⁅u₍ₚ₋₁₎, a₍ᵢ₋₂₎⁆ b`. -/
theorem mode_split (W : VertexOperatorAlgebra 𝒱) (u a b : 𝒱) (p i : ℤ) :
    W.smul u (p - 1) (W.smul a (i - 2) b)
      = W.smul a (i - 2) (W.smul u (p - 1) b)
        + ⁅mode (W.Y u) (p - 1), mode (W.Y a) (i - 2)⁆ b := by
  rw [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply]
  simp only [PreVertexAlgebra.smul_def, mode_apply]
  abel

/-! ## Uniform commutator expansion (single `N` valid for all modes). -/

/-- **Uniform commutator.**  A single `N` (the locality bound, mode-independent) such that for
ALL modes `α β` and all `b`, `⁅u₍α₎, a₍β₎⁆ b = ∑_{s<N} C(α,s) • (u₍ₛ₎a)₍α+β−s₎ b`.  Mirrors
`mode_commutator` but lifts the `∃N` outside the `∀ α β`. -/
theorem mode_commutator_uniform (W : VertexOperatorAlgebra 𝒱) (u a : 𝒱) :
    ∃ N : ℕ, ∀ (α β : ℤ) (b : 𝒱),
      ⁅mode (W.Y u) α, mode (W.Y a) β⁆ b
        = ∑ s ∈ Finset.range N,
            cbz α (s : ℤ) • W.smul (W.smul u s a) (α + β - (s : ℤ)) b := by
  obtain ⟨N, c, hdecomp⟩ := bracket_deltaSum W.toPreVertexAlgebra u a
  refine ⟨N, fun α β b => ?_⟩
  -- per-(α,β) commutator from `mode_bracket_ope`
  have hbr := mode_bracket_ope W.toPreVertexAlgebra u a hdecomp α β
  -- recover `c j = (j!)⁻¹ • Y(u₍ⱼ₎a)` (mode-independent)
  have hcj : ∀ j : Fin N, c j = (((j : ℕ).factorial : ℂ)⁻¹) • W.Y (W.smul u (j : ℕ) a) := by
    intro j
    have hne : ((j : ℕ).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hrec := cCoeff_deltaSum c j
    rw [← hdecomp, nth_product] at hrec
    rw [hrec, ← Int.cast_smul_eq_zsmul ℂ ((j : ℕ).factorial : ℤ), Int.cast_natCast, smul_smul,
      inv_mul_cancel₀ hne, one_smul]
  -- convert the `Fin N` falling-factorial form into the `cbz`/`smul` form, then to `range N`
  rw [hbr, LinearMap.sum_apply,
    Finset.sum_range (fun s : ℕ =>
        cbz α (s : ℤ) • W.smul (W.smul u s a) (α + β - (s : ℤ)) b)]
  refine Finset.sum_congr rfl fun j _ => ?_
  -- term-by-term: falling-factorial • mode (c j) = cbz α j • (u₍ⱼ₎a)₍α+β−j₎  (as operators)
  have hop : (∏ i ∈ Finset.range (j : ℕ), (α - (i : ℤ))) • mode (c j) (α + β - ((j : ℕ) : ℤ))
      = cbz α ((j : ℕ) : ℤ) • mode (W.Y (W.smul u (j : ℕ) a)) (α + β - ((j : ℕ) : ℤ)) := by
    rw [hcj j, mode_smul,
      ← Int.cast_smul_eq_zsmul ℂ (∏ i ∈ Finset.range (j : ℕ), (α - (i : ℤ))), smul_smul]
    congr 1
    rw [cbz_apply_nonneg α (by positivity), Int.toNat_natCast, gBinom, div_eq_mul_inv]
    push_cast
    ring
  rw [hop, LinearMap.smul_apply, ← PreVertexAlgebra.smul_def]

/-- `∑_{p,i} (cbz K p * cbz M i) • a₍ᵢ₋₂₎(u₍ₚ₋₁₎b) ∈ O W`. -/
theorem first_family_mem_O (W : VertexOperatorAlgebra 𝒱) {K M : ℕ} {a : 𝒱}
    (ha : a ∈ W.grading (M : ℤ)) (u b : 𝒱) :
    (∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
        (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ))
          • W.smul a ((i : ℤ) - 2) (W.smul u ((p : ℤ) - 1) b)) ∈ O W := by
  apply Submodule.sum_mem
  intro p _
  have hrow : (∑ i ∈ Finset.range (M + 1),
        (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ))
          • W.smul a ((i : ℤ) - 2) (W.smul u ((p : ℤ) - 1) b))
      = cbz (K : ℤ) (p : ℤ) • zhuMul W (W.L (-1) a + W.L 0 a) (W.smul u ((p : ℤ) - 1) b) := by
    rw [zhuMul_L_base W ha (W.smul u ((p : ℤ) - 1) b), Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]
  rw [hrow]
  exact Submodule.smul_mem _ _ (gen_mem_O W a (W.smul u ((p : ℤ) - 1) b))

/-! ## Step 4 infrastructure: vector finsums over the mode value. -/

/-- A `finsum` of `𝒱`-valued terms lying in a submodule lies in it. -/
theorem finsum_mem_O {ι : Type*} (W : VertexOperatorAlgebra 𝒱) (F : ι → 𝒱)
    (hF : ∀ i, F i ∈ O W) : (∑ᶠ i, F i) ∈ O W := by
  by_cases hfin : (Function.support F).Finite
  · rw [finsum_eq_finsetSum_of_support_subset F (s := hfin.toFinset)
        (fun i hi => hfin.mem_toFinset.mpr hi)]
    exact Submodule.sum_mem _ (fun i _ => hF i)
  · rw [finsum_of_infinite_support (by rwa [Set.not_finite] at hfin)]
    exact (O W).zero_mem

/-- Convert a finite-range `•`-sum `∑_{p<N} C p • g (p + d)` (with `C` vanishing for `p<0`
and `p≥N`) into the `ℤ`-finsum `∑ᶠ q, C q • g (q + d)`. -/
theorem rangeSmul_eq_finsumZ (C : ℤ → ℂ) (g : ℤ → 𝒱) (d : ℤ) {N : ℕ}
    (hlo : ∀ p : ℤ, p < 0 → C p = 0) (hhi : ∀ p : ℤ, (N : ℤ) ≤ p → C p = 0) :
    (∑ p ∈ Finset.range N, C (p : ℤ) • g ((p : ℤ) + d)) = ∑ᶠ q : ℤ, C q • g (q + d) := by
  rw [finsum_eq_finsetSum_of_support_subset (fun q : ℤ => C q • g (q + d))
      (s := (Finset.range N).map ⟨(Int.ofNat ·), by intro x y h; simpa using h⟩) ?_]
  · rw [Finset.sum_map]; rfl
  · intro q hq
    rw [Function.mem_support] at hq
    have hC : C q ≠ 0 := fun h => hq (by rw [h, zero_smul])
    have hq0 : 0 ≤ q := by by_contra h; exact hC (hlo q (by omega))
    have hqN : q < (N : ℤ) := by by_contra h; exact hC (hhi q (by omega))
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Finset.mem_range,
      Function.Embedding.coeFn_mk]
    exact ⟨q.toNat, by omega, by simp [Int.toNat_of_nonneg hq0]⟩

/-- Per-`p` reindex of the inner `i`-sum to a `∑ᶠ m` over the mode value (`m = p+i-3-s`). -/
theorem inner_reindex (W : VertexOperatorAlgebra 𝒱) (M : ℕ) (w b : 𝒱) (s p : ℤ) :
    (∑ i ∈ Finset.range (M + 1), cbz (M : ℤ) (i : ℤ) • W.smul w (p + (i : ℤ) - 3 - s) b)
      = ∑ᶠ m : ℤ, cbz (M : ℤ) (m + 3 + s - p) • W.smul w m b := by
  rw [show (∑ i ∈ Finset.range (M + 1), cbz (M : ℤ) (i : ℤ) • W.smul w (p + (i : ℤ) - 3 - s) b)
        = ∑ i ∈ Finset.range (M + 1),
            cbz (M : ℤ) (i : ℤ) • W.smul w ((i : ℤ) + (p - 3 - s)) b from
      Finset.sum_congr rfl fun i _ => by rw [show p + (i : ℤ) - 3 - s = (i : ℤ) + (p - 3 - s) from by ring]]
  rw [rangeSmul_eq_finsumZ (fun q : ℤ => cbz (M : ℤ) q) (fun q => W.smul w q b) (p - 3 - s)
      (fun q hq => cbz_apply_neg (M : ℤ) hq)
      (fun q hq => cbz_lt (by positivity) (by exact_mod_cast hq))]
  rw [← finsum_comp_equiv (Equiv.addRight (p - 3 - s))
      (f := fun m : ℤ => cbz (M : ℤ) (m + 3 + s - p) • W.smul w m b)]
  refine finsum_congr fun q => ?_
  simp only [Equiv.coe_addRight]
  rw [show (q + (p - 3 - s)) + 3 + s - p = q from by ring]

/-- If a scalar function `C : ℤ → ℂ` has finite support, so does `m ↦ C m • w₍ₘ₎b`. -/
theorem smul_support_of_scalar (W : VertexOperatorAlgebra 𝒱) (w b : 𝒱) (C : ℤ → ℂ)
    (hC : (Function.support C).Finite) :
    Function.HasFiniteSupport (fun m : ℤ => C m • W.smul w m b) := by
  apply Set.Finite.subset hC
  intro m hm
  rw [Function.mem_support] at hm ⊢
  intro h; apply hm; rw [h, zero_smul]

/-- For `0 ≤ d`, the scalar `m ↦ cbz d (m + e)` has finite support (nonzero only on
`0 ≤ m+e ≤ d`, a finite interval). -/
theorem cbz_shift_support_fin {d : ℤ} (hd : 0 ≤ d) (e : ℤ) :
    (Function.support (fun m : ℤ => cbz d (m + e))).Finite := by
  apply Set.Finite.subset (Set.finite_Icc (-e) (-e + d))
  intro m hm
  rw [Function.mem_support] at hm
  simp only [Set.mem_Icc]
  constructor
  · by_contra h; exact hm (cbz_apply_neg d (by omega))
  · by_contra h; exact hm (cbz_lt hd (by omega))

/-- The per-`s` scalar coefficient (LHS of `zhu_right_binom` at `j = s`). -/
noncomputable def coeffS (K M : ℕ) (s m : ℤ) : ℂ :=
  ∑ p ∈ Finset.range (K + 1),
    cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (m + 3 + s - (p : ℤ)) * cbz ((p : ℤ) - 1) s

/-- `S_s` collapses to the single `∑ᶠ m, coeffS(m) • w₍ₘ₎b`. -/
theorem S_eq_finsum (W : VertexOperatorAlgebra 𝒱) (K M : ℕ) (w b : 𝒱) (s : ℤ) :
    (∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
        (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ) * cbz ((p : ℤ) - 1) s)
          • W.smul w ((p : ℤ) + (i : ℤ) - 3 - s) b)
      = ∑ᶠ m : ℤ, coeffS K M s m • W.smul w m b := by
  -- pull the `p`-only scalars out of the inner `i`-sum, then apply `inner_reindex`
  rw [show (∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
            (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ) * cbz ((p : ℤ) - 1) s)
              • W.smul w ((p : ℤ) + (i : ℤ) - 3 - s) b)
        = ∑ p ∈ Finset.range (K + 1),
            (cbz (K : ℤ) (p : ℤ) * cbz ((p : ℤ) - 1) s)
              • ∑ᶠ m : ℤ, cbz (M : ℤ) (m + 3 + s - (p : ℤ)) • W.smul w m b from
      Finset.sum_congr rfl fun p _ => by
        rw [← inner_reindex W M w b s (p : ℤ), Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]; ring_nf]
  -- push the `p`-scalar into the finsum and swap the finite `p`-sum past `∑ᶠ m`
  rw [show (∑ p ∈ Finset.range (K + 1),
            (cbz (K : ℤ) (p : ℤ) * cbz ((p : ℤ) - 1) s)
              • ∑ᶠ m : ℤ, cbz (M : ℤ) (m + 3 + s - (p : ℤ)) • W.smul w m b)
        = ∑ p ∈ Finset.range (K + 1),
            ∑ᶠ m : ℤ,
              (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (m + 3 + s - (p : ℤ)) * cbz ((p : ℤ) - 1) s)
                • W.smul w m b from
      Finset.sum_congr rfl fun p _ => by
        have hfin : Function.HasFiniteSupport
            (fun m : ℤ => cbz (M : ℤ) (m + 3 + s - (p : ℤ)) • W.smul w m b) :=
          smul_support_of_scalar W w b _
            (Set.Finite.subset (cbz_shift_support_fin (d := (M : ℤ)) (by positivity) (3 + s - (p : ℤ)))
              (fun m hm => by
                rw [Function.mem_support] at hm ⊢
                intro h; apply hm
                rw [show m + 3 + s - (p : ℤ) = m + (3 + s - (p : ℤ)) from by ring]; exact h))
        rw [smul_finsum' (cbz (K : ℤ) (p : ℤ) * cbz ((p : ℤ) - 1) s) hfin]
        refine finsum_congr fun m => ?_
        rw [smul_smul]; ring_nf]
  rw [← finsum_sum_comm (Finset.range (K + 1))
      (fun m p => (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (m + 3 + s - (p : ℤ)) * cbz ((p : ℤ) - 1) s)
        • W.smul w m b)
      (fun p _ => ?_)]
  · refine finsum_congr fun m => ?_
    rw [coeffS, Finset.sum_smul]
  · -- finite support of `m ↦ (...)• w₍ₘ₎b` for fixed p
    refine smul_support_of_scalar W w b _ (Set.Finite.subset
      (cbz_shift_support_fin (d := (M : ℤ)) (by positivity) (3 + s - (p : ℤ))) ?_)
    intro m hm
    rw [Function.mem_support] at hm ⊢
    intro h; apply hm
    rw [show (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (m + 3 + s - (p : ℤ)) * cbz ((p : ℤ) - 1) s)
          = (cbz (K : ℤ) (p : ℤ) * cbz ((p : ℤ) - 1) s) * cbz (M : ℤ) (m + (3 + s - (p : ℤ))) from by
        rw [show m + (3 + s - (p : ℤ)) = m + 3 + s - (p : ℤ) from by ring]; ring,
      h, mul_zero]

/-- `Pres W Ws w b n` in the mode-value finsum form (`m = r-2-n`). -/
theorem Pres_eq_finsum (W : VertexOperatorAlgebra 𝒱) (Ws : ℕ) (w b : 𝒱) (n : ℕ) :
    Pres W Ws w b n
      = ∑ᶠ m : ℤ, cbz ((Ws : ℤ) + n) (m + 2 + n) • W.smul w m b := by
  unfold Pres
  rw [show (∑ r ∈ Finset.range (Ws + n + 1),
            cbz ((Ws : ℤ) + n) (r : ℤ) • W.smul w ((r : ℤ) - 2 - n) b)
        = ∑ r ∈ Finset.range (Ws + n + 1),
            cbz ((Ws : ℤ) + n) (r : ℤ) • W.smul w ((r : ℤ) + (-2 - n)) b from
      Finset.sum_congr rfl fun r _ => by rw [show (r : ℤ) - 2 - n = (r : ℤ) + (-2 - n) from by ring]]
  rw [rangeSmul_eq_finsumZ (fun q : ℤ => cbz ((Ws : ℤ) + n) q) (fun q => W.smul w q b) (-2 - n)
      (fun q hq => cbz_apply_neg _ hq)
      (fun q hq => cbz_lt (by positivity) (by omega))]
  rw [← finsum_comp_equiv (Equiv.addRight (-2 - (n : ℤ)))
      (f := fun m : ℤ => cbz ((Ws : ℤ) + n) (m + 2 + n) • W.smul w m b)]
  refine finsum_congr fun q => ?_
  simp only [Equiv.coe_addRight]
  rw [show (q + (-2 - (n : ℤ))) + 2 + n = q from by ring]

/-- The per-`s` scalar coefficient (RHS of `zhu_right_binom` at `j = s`). -/
noncomputable def coeffP (K M : ℕ) (s : ℕ) (m : ℤ) : ℂ :=
  ∑ t ∈ Finset.range (s + 1),
    (-1 : ℂ) ^ t * cbz (K : ℤ) ((s : ℤ) - (t : ℤ))
      * cbz ((K : ℤ) + (M : ℤ) - (s : ℤ) + (t : ℤ)) (m + 3 + (t : ℤ))

/-- The `Pres`-combination collapses to the single `∑ᶠ m, coeffP(m) • w₍ₘ₎b`.  Here
`w := u₍ₛ₎a ∈ 𝒱_{Ws}` with `Ws = K+M-s-1`. -/
theorem PresCombo_eq_finsum (W : VertexOperatorAlgebra 𝒱) (K M s Ws : ℕ) (w b : 𝒱)
    (hWs : (Ws : ℤ) = (K : ℤ) + (M : ℤ) - (s : ℤ) - 1) :
    (∑ t ∈ Finset.range (s + 1),
        ((-1 : ℂ) ^ t * cbz (K : ℤ) ((s : ℤ) - (t : ℤ))) • Pres W Ws w b (t + 1))
      = ∑ᶠ m : ℤ, coeffP K M s m • W.smul w m b := by
  rw [show (∑ t ∈ Finset.range (s + 1),
            ((-1 : ℂ) ^ t * cbz (K : ℤ) ((s : ℤ) - (t : ℤ))) • Pres W Ws w b (t + 1))
        = ∑ t ∈ Finset.range (s + 1),
            ∑ᶠ m : ℤ,
              ((-1 : ℂ) ^ t * cbz (K : ℤ) ((s : ℤ) - (t : ℤ))
                * cbz ((K : ℤ) + (M : ℤ) - (s : ℤ) + (t : ℤ)) (m + 3 + (t : ℤ)))
                • W.smul w m b from
      Finset.sum_congr rfl fun t _ => by
        rw [Pres_eq_finsum W Ws w b (t + 1), Nat.cast_add, Nat.cast_one]
        have hfin : Function.HasFiniteSupport
            (fun m : ℤ =>
              cbz ((Ws : ℤ) + ((t : ℤ) + 1)) (m + 2 + ((t : ℤ) + 1)) • W.smul w m b) :=
          smul_support_of_scalar W w b _
            (Set.Finite.subset
              (cbz_shift_support_fin (d := (Ws : ℤ) + ((t : ℤ) + 1)) (by positivity)
                (2 + ((t : ℤ) + 1)))
              (fun m hm => by
                rw [Function.mem_support] at hm ⊢
                intro h; apply hm
                rw [show m + 2 + ((t : ℤ) + 1) = m + (2 + ((t : ℤ) + 1)) from by ring]; exact h))
        rw [smul_finsum' ((-1 : ℂ) ^ t * cbz (K : ℤ) ((s : ℤ) - (t : ℤ))) hfin]
        refine finsum_congr fun m => ?_
        rw [smul_smul,
          show ((Ws : ℤ) + ((t : ℤ) + 1)) = (K : ℤ) + (M : ℤ) - (s : ℤ) + (t : ℤ) from by
            rw [hWs]; ring,
          show m + 2 + ((t : ℤ) + 1) = m + 3 + (t : ℤ) from by ring,
          mul_assoc]]
  rw [← finsum_sum_comm (Finset.range (s + 1))
      (fun m t => ((-1 : ℂ) ^ t * cbz (K : ℤ) ((s : ℤ) - (t : ℤ))
          * cbz ((K : ℤ) + (M : ℤ) - (s : ℤ) + (t : ℤ)) (m + 3 + (t : ℤ)))
        • W.smul w m b)
      (fun t _ => ?_)]
  · refine finsum_congr fun m => ?_
    rw [coeffP, Finset.sum_smul]
  · -- finite support for fixed `t`
    refine smul_support_of_scalar W w b _ (Set.Finite.subset
      (cbz_shift_support_fin (d := (K : ℤ) + (M : ℤ) - (s : ℤ) + (t : ℤ)) (by omega) (3 + (t : ℤ))) ?_)
    intro m hm
    rw [Function.mem_support] at hm ⊢
    intro h; apply hm
    rw [show ((-1 : ℂ) ^ t * cbz (K : ℤ) ((s : ℤ) - (t : ℤ))
            * cbz ((K : ℤ) + (M : ℤ) - (s : ℤ) + (t : ℤ)) (m + 3 + (t : ℤ)))
          = ((-1 : ℂ) ^ t * cbz (K : ℤ) ((s : ℤ) - (t : ℤ)))
              * cbz ((K : ℤ) + (M : ℤ) - (s : ℤ) + (t : ℤ)) (m + (3 + (t : ℤ))) from by
        rw [show m + (3 + (t : ℤ)) = m + 3 + (t : ℤ) from by ring, mul_assoc],
      h, mul_zero]

/-! ## Step 4: each per-commutator-index term `S_s` lies in `O`. -/

/-- `coeffS = coeffP` (this is exactly `zhu_right_binom`). -/
theorem coeffS_eq_coeffP (K M s : ℕ) (m : ℤ) : coeffS K M (s : ℤ) m = coeffP K M s m := by
  rw [coeffS, coeffP]
  exact ZhuRes.zhu_right_binom K M s m

/-- **The per-commutator-index term lies in `O`.**  For `s : ℕ`, `w := u₍ₛ₎a ∈ 𝒱_{K+M-s-1}`,
`S_s := ∑_{p,i} (cbz K p · cbz M i · cbz(p-1,s)) • w₍ₚ₊ᵢ₋₃₋ₛ₎b ∈ O W`. -/
theorem S_mem_O (W : VertexOperatorAlgebra 𝒱) {K M : ℕ} {u a : 𝒱}
    (hu : u ∈ W.grading (K : ℤ)) (ha : a ∈ W.grading (M : ℤ)) (b : 𝒱) (s : ℕ) :
    (∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
        (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ) * cbz ((p : ℤ) - 1) (s : ℤ))
          • W.smul (W.smul u (s : ℤ) a) ((p : ℤ) + (i : ℤ) - 3 - (s : ℤ)) b) ∈ O W := by
  set w := W.smul u (s : ℤ) a with hw
  have hwmem : w ∈ W.grading ((K : ℤ) + (M : ℤ) - (s : ℤ) - 1) := by
    have h := W.smul_mem_grading hu ha (s : ℤ)
    rwa [show (K : ℤ) + (M : ℤ) - (s : ℤ) - 1 = (K : ℤ) + (M : ℤ) - (s : ℤ) - 1 from rfl] at h
  -- collapse the double sum to a single finsum over the mode value
  rw [S_eq_finsum W K M w b (s : ℤ)]
  rcases lt_or_ge ((K : ℤ) + (M : ℤ) - (s : ℤ) - 1) 0 with hneg | hpos
  · -- `w ∈ 𝒱_{<0} = ⊥`, so `w = 0` and the finsum is `0`
    rw [W.positivity _ hneg, Submodule.mem_bot] at hwmem
    rw [show (∑ᶠ m : ℤ, coeffS K M (s : ℤ) m • W.smul w m b) = 0 from by
      refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
      rw [hwmem, PreVertexAlgebra.smul_zero_left, smul_zero]]
    exact (O W).zero_mem
  · -- `Ws := K+M-s-1 : ℕ`; rewrite the finsum as the `Pres`-combination, in `O`
    obtain ⟨Ws, hWs⟩ : ∃ Ws : ℕ, (Ws : ℤ) = (K : ℤ) + (M : ℤ) - (s : ℤ) - 1 :=
      ⟨((K : ℤ) + (M : ℤ) - (s : ℤ) - 1).toNat, by omega⟩
    have hwmem' : w ∈ W.grading (Ws : ℤ) := by rwa [hWs]
    rw [show (∑ᶠ m : ℤ, coeffS K M (s : ℤ) m • W.smul w m b)
          = ∑ᶠ m : ℤ, coeffP K M s m • W.smul w m b from
        finsum_congr fun m => by rw [coeffS_eq_coeffP],
      ← PresCombo_eq_finsum W K M s Ws w b hWs]
    apply Submodule.sum_mem
    intro t _
    exact Submodule.smul_mem _ _ (Pres_mem_O W hwmem' b (t + 1))

/-! ## The commutator family lies in `O`. -/

/-- `∑_{p,i} (cbz K p · cbz M i) • ⁅u₍ₚ₋₁₎, a₍ᵢ₋₂₎⁆ b ∈ O W`. -/
theorem commutator_family_mem_O (W : VertexOperatorAlgebra 𝒱) {K M : ℕ} {u a : 𝒱}
    (hu : u ∈ W.grading (K : ℤ)) (ha : a ∈ W.grading (M : ℤ)) (b : 𝒱) :
    (∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
        (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ))
          • ⁅mode (W.Y u) ((p : ℤ) - 1), mode (W.Y a) ((i : ℤ) - 2)⁆ b) ∈ O W := by
  obtain ⟨N, hN⟩ := mode_commutator_uniform W u a
  -- expand each bracket and merge the `s`-sum into each `(p,i)` summand
  rw [show (∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
            (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ))
              • ⁅mode (W.Y u) ((p : ℤ) - 1), mode (W.Y a) ((i : ℤ) - 2)⁆ b)
        = ∑ s ∈ Finset.range N, ∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
            (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ) * cbz ((p : ℤ) - 1) (s : ℤ))
              • W.smul (W.smul u (s : ℤ) a) ((p : ℤ) + (i : ℤ) - 3 - (s : ℤ)) b from ?_]
  · apply Submodule.sum_mem
    intro s _
    exact S_mem_O W hu ha b s
  · -- the reindexing identity: merge the `s`-sum into each `(p,i)`-summand, then pull `s` out front
    rw [show (∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
              (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ))
                • ⁅mode (W.Y u) ((p : ℤ) - 1), mode (W.Y a) ((i : ℤ) - 2)⁆ b)
          = ∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1), ∑ s ∈ Finset.range N,
              (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ) * cbz ((p : ℤ) - 1) (s : ℤ))
                • W.smul (W.smul u (s : ℤ) a) ((p : ℤ) + (i : ℤ) - 3 - (s : ℤ)) b from
        Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun i _ => by
          rw [hN ((p : ℤ) - 1) ((i : ℤ) - 2) b, Finset.smul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [smul_smul,
            show (p : ℤ) - 1 + ((i : ℤ) - 2) - (s : ℤ) = (p : ℤ) + (i : ℤ) - 3 - (s : ℤ) from by ring]]
    -- pull the `∑_s` outermost: first swap `i,s` (inner), then `p,s` (outer)
    rw [show (∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1), ∑ s ∈ Finset.range N,
              (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ) * cbz ((p : ℤ) - 1) (s : ℤ))
                • W.smul (W.smul u (s : ℤ) a) ((p : ℤ) + (i : ℤ) - 3 - (s : ℤ)) b)
          = ∑ p ∈ Finset.range (K + 1), ∑ s ∈ Finset.range N, ∑ i ∈ Finset.range (M + 1),
              (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ) * cbz ((p : ℤ) - 1) (s : ℤ))
                • W.smul (W.smul u (s : ℤ) a) ((p : ℤ) + (i : ℤ) - 3 - (s : ℤ)) b from
        Finset.sum_congr rfl fun p _ =>
          Finset.sum_comm (s := Finset.range (M + 1)) (t := Finset.range N)]
    rw [Finset.sum_comm (s := Finset.range (K + 1)) (t := Finset.range N)]

/-! ## The right-ideal core of Zhu Thm 2.1.1. -/

/-- **The right-ideal core of Zhu's two-sided-ideal theorem (Zhu Thm 2.1.1).**  For homogeneous
`u ∈ 𝒱_K`, `a ∈ 𝒱_M`, the right Zhu-product of `u` with a generator of `O` is again in `O`:
`u * ((L₋₁a + L₀a) * b) ∈ O W`. -/
theorem right_ideal_core (W : VertexOperatorAlgebra 𝒱) {K M : ℕ} {u a : 𝒱}
    (hu : u ∈ W.grading (K : ℤ)) (ha : a ∈ W.grading (M : ℤ)) (b : 𝒱) :
    zhuMul W u (zhuMul W (W.L (-1) a + W.L 0 a) b) ∈ O W := by
  rw [right_target_expand W hu ha b]
  -- split each summand via the commutator formula
  rw [show (∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
            (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ))
              • W.smul u ((p : ℤ) - 1) (W.smul a ((i : ℤ) - 2) b))
        = (∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
            (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ))
              • W.smul a ((i : ℤ) - 2) (W.smul u ((p : ℤ) - 1) b))
          + (∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
              (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ))
                • ⁅mode (W.Y u) ((p : ℤ) - 1), mode (W.Y a) ((i : ℤ) - 2)⁆ b) from by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mode_split W u a b (p : ℤ) (i : ℤ), smul_add]]
  exact Submodule.add_mem _ (first_family_mem_O W ha u b) (commutator_family_mem_O W hu ha b)

end ZhuHR
