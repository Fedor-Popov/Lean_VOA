/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.SuperZhuResidue

/-!
# `right_ideal_coreε` — the super Zhu right-ideal residue core (Dong–Zhao Thm 3.1)

The super analogue of `ZhuHR.right_ideal_core` (`Modules/ZhuRightIdeal`): for **bi-homogeneous**
`u ∈ 𝒱_K ∩ 𝒱_p` and `a ∈ 𝒱_M ∩ 𝒱_q`,
`u ∗ ((L₋₁a + L₀a) ∗ b) ∈ O(V)`.

## Where the Koszul sign goes, and where it does not

The proof runs exactly as the bosonic one, through the double-residue expansion and the
commutator split
`u₍ₚ₋₁₎(a₍ᵢ₋₂₎b) = ε · a₍ᵢ₋₂₎(u₍ₚ₋₁₎b) + ⁅u₍ₚ₋₁₎, a₍ᵢ₋₂₎⁆_ε b`,  `ε := koszul p q`,
with two observations:

* the **first family** picks up the single constant scalar `ε`, and `O(V)` is a `ℂ`-submodule, so
  `ε • (first family) ∈ O(V)` for free;
* the **commutator family** picks up *nothing*: `commBoundε` (`Core.SuperNthProduct`) puts all of
  the `ε` into the twisted bracket on the left and leaves the right-hand side
  `∑_{s<N} C(α,s) (u₍ₛ₎a)₍α+β−s₎ b` sign-free.  So the entire `coeffS = coeffP` collapse — the
  linchpin `ZhuRes.zhu_right_binom`, a pure generalized-binomial identity — is reused **verbatim
  by import**, not ported.

The one genuinely new hypothesis is `hpos` (negative weight spaces vanish); `SuperNearVOA` has no
`positivity` field, so it is a named argument.

## Status
`sorry`-free, with no project axioms.

## References
* Dong–Zhao, arXiv:math/0601571, Thm 3.1; Zhu [574] Thm 2.1.1; Frenkel–Zhu.
-/

open VOA
open scoped BigOperators
open Classical

set_option autoImplicit false

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace SuperZhuHR

open VOA.SuperNearVOA

/-! ## Step 1: right-target expansion (sign-free). -/

/-- `u ∗ (a∘b) = ∑_p ∑_i (cbz K p * cbz M i) • u₍ₚ₋₁₎(a₍ᵢ₋₂₎b)`. -/
theorem right_target_expandε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) {K M : ℕ} {u a : 𝒱}
    (hu : u ∈ V.gradingZ (K : ℤ)) (ha : a ∈ V.gradingZ (M : ℤ)) (b : 𝒱) :
    V.superZhuMul hV u (V.superZhuMul hV (V.L (-1) a + V.L 0 a) b)
      = ∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
          (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ))
            • V.smul u ((p : ℤ) - 1) (V.smul a ((i : ℤ) - 2) b) := by
  rw [V.superZhuMul_homogeneous hV hu, show ((K : ℤ).toNat + 1) = K + 1 from by simp]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [V.superZhuMul_L_base hV ha b]
  rw [show V.smul u ((p : ℤ) - 1) (∑ i ∈ Finset.range (M + 1),
            cbz (M : ℤ) (i : ℤ) • V.smul a ((i : ℤ) - 2) b)
        = ∑ i ∈ Finset.range (M + 1),
            cbz (M : ℤ) (i : ℤ) • V.smul u ((p : ℤ) - 1) (V.smul a ((i : ℤ) - 2) b) from by
      rw [SuperVertexAlgebra.smul_def, map_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [LinearMap.map_smul]; rfl,
    Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]

/-! ## Step 2: the super commutator split. -/

/-- `u₍ₚ₋₁₎(a₍ᵢ₋₂₎b) = ε · a₍ᵢ₋₂₎(u₍ₚ₋₁₎b) + ⁅u₍ₚ₋₁₎, a₍ᵢ₋₂₎⁆_ε b`.  This is the *only* place a
Koszul sign enters the right-ideal argument, and it enters as the single constant `ε`. -/
theorem mode_splitε (V : SuperNearVOA 𝒱) (ε : ℂ) (u a b : 𝒱) (p i : ℤ) :
    V.smul u (p - 1) (V.smul a (i - 2) b)
      = ε • V.smul a (i - 2) (V.smul u (p - 1) b)
        + modeBracketε ε (V.Y u) (V.Y a) (p - 1) (i - 2) b := by
  rw [modeBracketε_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    Module.End.mul_apply]
  simp only [SuperVertexAlgebra.smul_def]
  abel

/-! ## Uniform super commutator expansion (single `N` valid for all modes). -/

/-- **Uniform twisted commutator.**  A single `N` (the super-locality bound, mode-independent)
such that for ALL modes `α β` and all `b`,
`⁅u₍α₎, a₍β₎⁆_ε b = ∑_{s<N} C(α,s) • (u₍ₛ₎a)₍α+β−s₎ b`.  **No sign on the right.** -/
theorem mode_commutator_uniformε (V : SuperNearVOA 𝒱) {p q : ZMod 2} {u a : 𝒱}
    (hu : u ∈ V.parity p) (ha : a ∈ V.parity q) :
    ∃ N : ℕ, ∀ (α β : ℤ) (b : 𝒱),
      modeBracketε (koszul p q) (V.Y u) (V.Y a) α β b
        = ∑ s ∈ Finset.range N,
            cbz α (s : ℤ) • V.smul (V.smul u s a) (α + β - (s : ℤ)) b := by
  obtain ⟨N, c, hdecomp⟩ := bracket_deltaSumε V hu ha
  refine ⟨N, fun α β b => ?_⟩
  have hbr := mode_bracket_opeε V (koszul p q) u a hdecomp α β
  have hcj : ∀ j : Fin N, c j = (((j : ℕ).factorial : ℂ)⁻¹) • V.Y (V.smul u (j : ℕ) a) := by
    intro j
    have hne : ((j : ℕ).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hrec := cCoeff_deltaSum c j
    rw [← hdecomp, nth_productε V hu ha] at hrec
    rw [hrec, ← Int.cast_smul_eq_zsmul ℂ ((j : ℕ).factorial : ℤ), Int.cast_natCast, smul_smul,
      inv_mul_cancel₀ hne, one_smul]
  rw [hbr, LinearMap.sum_apply,
    Finset.sum_range (fun s : ℕ =>
        cbz α (s : ℤ) • V.smul (V.smul u s a) (α + β - (s : ℤ)) b)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hop : (∏ i ∈ Finset.range (j : ℕ), (α - (i : ℤ))) • mode (c j) (α + β - ((j : ℕ) : ℤ))
      = cbz α ((j : ℕ) : ℤ) • mode (V.Y (V.smul u (j : ℕ) a)) (α + β - ((j : ℕ) : ℤ)) := by
    rw [hcj j, mode_smul,
      ← Int.cast_smul_eq_zsmul ℂ (∏ i ∈ Finset.range (j : ℕ), (α - (i : ℤ))), smul_smul]
    congr 1
    rw [cbz_apply_nonneg α (by positivity), Int.toNat_natCast, gBinom, div_eq_mul_inv]
    push_cast
    ring
  rw [hop, LinearMap.smul_apply, ← SuperVertexAlgebra.smul_def]

/-! ## Step 3: the first family lies in `O(V)` (sign-free statement). -/

/-- `∑_{p,i} (cbz K p * cbz M i) • a₍ᵢ₋₂₎(u₍ₚ₋₁₎b) ∈ O(V)`.  Each `p`-row is a `cbz`-multiple of
an `O(V)` generator. -/
theorem first_family_mem_superO (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) {K M : ℕ} {a : 𝒱}
    (ha : a ∈ V.gradingZ (M : ℤ)) (u b : 𝒱) :
    (∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
        (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ))
          • V.smul a ((i : ℤ) - 2) (V.smul u ((p : ℤ) - 1) b)) ∈ V.superO hV := by
  apply Submodule.sum_mem
  intro p _
  have hrow : (∑ i ∈ Finset.range (M + 1),
        (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ))
          • V.smul a ((i : ℤ) - 2) (V.smul u ((p : ℤ) - 1) b))
      = cbz (K : ℤ) (p : ℤ)
          • V.superZhuMul hV (V.L (-1) a + V.L 0 a) (V.smul u ((p : ℤ) - 1) b) := by
    rw [V.superZhuMul_L_base hV ha (V.smul u ((p : ℤ) - 1) b), Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]
  rw [hrow]
  exact Submodule.smul_mem _ _ (V.superO_mem_of_L hV a (V.smul u ((p : ℤ) - 1) b))

/-! ## Step 4 infrastructure: vector finsums over the mode value. -/

/-- Per-`p` reindex of the inner `i`-sum to a `∑ᶠ m` over the mode value (`m = p+i-3-s`). -/
theorem inner_reindexε (V : SuperNearVOA 𝒱) (M : ℕ) (w b : 𝒱) (s p : ℤ) :
    (∑ i ∈ Finset.range (M + 1), cbz (M : ℤ) (i : ℤ) • V.smul w (p + (i : ℤ) - 3 - s) b)
      = ∑ᶠ m : ℤ, cbz (M : ℤ) (m + 3 + s - p) • V.smul w m b := by
  rw [show (∑ i ∈ Finset.range (M + 1), cbz (M : ℤ) (i : ℤ) • V.smul w (p + (i : ℤ) - 3 - s) b)
        = ∑ i ∈ Finset.range (M + 1),
            cbz (M : ℤ) (i : ℤ) • V.smul w ((i : ℤ) + (p - 3 - s)) b from
      Finset.sum_congr rfl fun i _ => by
        rw [show p + (i : ℤ) - 3 - s = (i : ℤ) + (p - 3 - s) from by ring]]
  rw [ZhuHR.rangeSmul_eq_finsumZ (fun q : ℤ => cbz (M : ℤ) q) (fun q => V.smul w q b) (p - 3 - s)
      (fun q hq => cbz_apply_neg (M : ℤ) hq)
      (fun q hq => cbz_lt (by positivity) (by exact_mod_cast hq))]
  rw [← finsum_comp_equiv (Equiv.addRight (p - 3 - s))
      (f := fun m : ℤ => cbz (M : ℤ) (m + 3 + s - p) • V.smul w m b)]
  refine finsum_congr fun q => ?_
  simp only [Equiv.coe_addRight]
  rw [show (q + (p - 3 - s)) + 3 + s - p = q from by ring]

/-- `S_s` collapses to the single `∑ᶠ m, coeffS(m) • w₍ₘ₎b`. -/
theorem S_eq_finsumε (V : SuperNearVOA 𝒱) (K M : ℕ) (w b : 𝒱) (s : ℤ) :
    (∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
        (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ) * cbz ((p : ℤ) - 1) s)
          • V.smul w ((p : ℤ) + (i : ℤ) - 3 - s) b)
      = ∑ᶠ m : ℤ, ZhuHR.coeffS K M s m • V.smul w m b := by
  rw [show (∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
            (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ) * cbz ((p : ℤ) - 1) s)
              • V.smul w ((p : ℤ) + (i : ℤ) - 3 - s) b)
        = ∑ p ∈ Finset.range (K + 1),
            (cbz (K : ℤ) (p : ℤ) * cbz ((p : ℤ) - 1) s)
              • ∑ᶠ m : ℤ, cbz (M : ℤ) (m + 3 + s - (p : ℤ)) • V.smul w m b from
      Finset.sum_congr rfl fun p _ => by
        rw [← inner_reindexε V M w b s (p : ℤ), Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]; ring_nf]
  rw [show (∑ p ∈ Finset.range (K + 1),
            (cbz (K : ℤ) (p : ℤ) * cbz ((p : ℤ) - 1) s)
              • ∑ᶠ m : ℤ, cbz (M : ℤ) (m + 3 + s - (p : ℤ)) • V.smul w m b)
        = ∑ p ∈ Finset.range (K + 1),
            ∑ᶠ m : ℤ,
              (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (m + 3 + s - (p : ℤ)) * cbz ((p : ℤ) - 1) s)
                • V.smul w m b from
      Finset.sum_congr rfl fun p _ => by
        have hfin : Function.HasFiniteSupport
            (fun m : ℤ => cbz (M : ℤ) (m + 3 + s - (p : ℤ)) • V.smul w m b) :=
          smul_support_of_scalar_gen _ _
            (Set.Finite.subset
              (ZhuHR.cbz_shift_support_fin (d := (M : ℤ)) (by positivity) (3 + s - (p : ℤ)))
              (fun m hm => by
                rw [Function.mem_support] at hm ⊢
                intro h; apply hm
                rw [show m + 3 + s - (p : ℤ) = m + (3 + s - (p : ℤ)) from by ring]; exact h))
        rw [smul_finsum' (cbz (K : ℤ) (p : ℤ) * cbz ((p : ℤ) - 1) s) hfin]
        refine finsum_congr fun m => ?_
        rw [smul_smul]; ring_nf]
  rw [← finsum_sum_comm (Finset.range (K + 1))
      (fun m p => (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (m + 3 + s - (p : ℤ)) * cbz ((p : ℤ) - 1) s)
        • V.smul w m b)
      (fun p _ => ?_)]
  · refine finsum_congr fun m => ?_
    rw [ZhuHR.coeffS, Finset.sum_smul]
  · refine smul_support_of_scalar_gen _ _ (Set.Finite.subset
      (ZhuHR.cbz_shift_support_fin (d := (M : ℤ)) (by positivity) (3 + s - (p : ℤ))) ?_)
    intro m hm
    rw [Function.mem_support] at hm ⊢
    intro h; apply hm
    rw [show (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (m + 3 + s - (p : ℤ)) * cbz ((p : ℤ) - 1) s)
          = (cbz (K : ℤ) (p : ℤ) * cbz ((p : ℤ) - 1) s)
              * cbz (M : ℤ) (m + (3 + s - (p : ℤ))) from by
        rw [show m + (3 + s - (p : ℤ)) = m + 3 + s - (p : ℤ) from by ring]; ring,
      h, mul_zero]

/-- `superPres V Ws w b n` in the mode-value finsum form (`m = r-2-n`). -/
theorem superPres_eq_finsum (V : SuperNearVOA 𝒱) (Ws : ℕ) (w b : 𝒱) (n : ℕ) :
    V.superPres Ws w b n
      = ∑ᶠ m : ℤ, cbz ((Ws : ℤ) + n) (m + 2 + n) • V.smul w m b := by
  unfold SuperNearVOA.superPres
  rw [show (∑ r ∈ Finset.range (Ws + n + 1),
            cbz ((Ws : ℤ) + n) (r : ℤ) • V.smul w ((r : ℤ) - 2 - n) b)
        = ∑ r ∈ Finset.range (Ws + n + 1),
            cbz ((Ws : ℤ) + n) (r : ℤ) • V.smul w ((r : ℤ) + (-2 - n)) b from
      Finset.sum_congr rfl fun r _ => by
        rw [show (r : ℤ) - 2 - n = (r : ℤ) + (-2 - n) from by ring]]
  rw [ZhuHR.rangeSmul_eq_finsumZ (fun q : ℤ => cbz ((Ws : ℤ) + n) q) (fun q => V.smul w q b)
      (-2 - n)
      (fun q hq => cbz_apply_neg _ hq)
      (fun q hq => cbz_lt (by positivity) (by omega))]
  rw [← finsum_comp_equiv (Equiv.addRight (-2 - (n : ℤ)))
      (f := fun m : ℤ => cbz ((Ws : ℤ) + n) (m + 2 + n) • V.smul w m b)]
  refine finsum_congr fun q => ?_
  simp only [Equiv.coe_addRight]
  rw [show (q + (-2 - (n : ℤ))) + 2 + n = q from by ring]

/-- The `superPres`-combination collapses to the single `∑ᶠ m, coeffP(m) • w₍ₘ₎b`.  Here
`w := u₍ₛ₎a ∈ 𝒱_{Ws}` with `Ws = K+M-s-1`. -/
theorem PresCombo_eq_finsumε (V : SuperNearVOA 𝒱) (K M s Ws : ℕ) (w b : 𝒱)
    (hWs : (Ws : ℤ) = (K : ℤ) + (M : ℤ) - (s : ℤ) - 1) :
    (∑ t ∈ Finset.range (s + 1),
        ((-1 : ℂ) ^ t * cbz (K : ℤ) ((s : ℤ) - (t : ℤ))) • V.superPres Ws w b (t + 1))
      = ∑ᶠ m : ℤ, ZhuHR.coeffP K M s m • V.smul w m b := by
  rw [show (∑ t ∈ Finset.range (s + 1),
            ((-1 : ℂ) ^ t * cbz (K : ℤ) ((s : ℤ) - (t : ℤ))) • V.superPres Ws w b (t + 1))
        = ∑ t ∈ Finset.range (s + 1),
            ∑ᶠ m : ℤ,
              ((-1 : ℂ) ^ t * cbz (K : ℤ) ((s : ℤ) - (t : ℤ))
                * cbz ((K : ℤ) + (M : ℤ) - (s : ℤ) + (t : ℤ)) (m + 3 + (t : ℤ)))
                • V.smul w m b from
      Finset.sum_congr rfl fun t _ => by
        rw [superPres_eq_finsum V Ws w b (t + 1), Nat.cast_add, Nat.cast_one]
        have hfin : Function.HasFiniteSupport
            (fun m : ℤ =>
              cbz ((Ws : ℤ) + ((t : ℤ) + 1)) (m + 2 + ((t : ℤ) + 1)) • V.smul w m b) :=
          smul_support_of_scalar_gen _ _
            (Set.Finite.subset
              (ZhuHR.cbz_shift_support_fin (d := (Ws : ℤ) + ((t : ℤ) + 1)) (by positivity)
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
        • V.smul w m b)
      (fun t _ => ?_)]
  · refine finsum_congr fun m => ?_
    rw [ZhuHR.coeffP, Finset.sum_smul]
  · refine smul_support_of_scalar_gen _ _ (Set.Finite.subset
      (ZhuHR.cbz_shift_support_fin (d := (K : ℤ) + (M : ℤ) - (s : ℤ) + (t : ℤ)) (by omega)
        (3 + (t : ℤ))) ?_)
    intro m hm
    rw [Function.mem_support] at hm ⊢
    intro h; apply hm
    rw [show ((-1 : ℂ) ^ t * cbz (K : ℤ) ((s : ℤ) - (t : ℤ))
            * cbz ((K : ℤ) + (M : ℤ) - (s : ℤ) + (t : ℤ)) (m + 3 + (t : ℤ)))
          = ((-1 : ℂ) ^ t * cbz (K : ℤ) ((s : ℤ) - (t : ℤ)))
              * cbz ((K : ℤ) + (M : ℤ) - (s : ℤ) + (t : ℤ)) (m + (3 + (t : ℤ))) from by
        rw [show m + (3 + (t : ℤ)) = m + 3 + (t : ℤ) from by ring, mul_assoc],
      h, mul_zero]

/-! ## Step 5: each per-commutator-index term `S_s` lies in `O(V)`. -/

/-- **The per-commutator-index term lies in `O(V)`.**  For `s : ℕ`, `w := u₍ₛ₎a ∈ 𝒱_{K+M-s-1}`,
`S_s := ∑_{p,i} (cbz K p · cbz M i · cbz(p-1,s)) • w₍ₚ₊ᵢ₋₃₋ₛ₎b ∈ O(V)`.  The collapse
`coeffS = coeffP` is `ZhuRes.zhu_right_binom`, reused verbatim. -/
theorem S_mem_superO (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights)
    (hpos : ∀ k : ℤ, k < 0 → V.gradingZ k = ⊥) {K M : ℕ} {u a : 𝒱}
    (hu : u ∈ V.gradingZ (K : ℤ)) (ha : a ∈ V.gradingZ (M : ℤ)) (b : 𝒱) (s : ℕ) :
    (∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
        (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ) * cbz ((p : ℤ) - 1) (s : ℤ))
          • V.smul (V.smul u (s : ℤ) a) ((p : ℤ) + (i : ℤ) - 3 - (s : ℤ)) b) ∈ V.superO hV := by
  set w := V.smul u (s : ℤ) a with hw
  have hwmem : w ∈ V.gradingZ ((K : ℤ) + (M : ℤ) - (s : ℤ) - 1) :=
    V.smul_mem_gradingZ hu ha (s : ℤ)
  rw [S_eq_finsumε V K M w b (s : ℤ)]
  rcases lt_or_ge ((K : ℤ) + (M : ℤ) - (s : ℤ) - 1) 0 with hneg | hposk
  · rw [hpos _ hneg, Submodule.mem_bot] at hwmem
    rw [show (∑ᶠ m : ℤ, ZhuHR.coeffS K M (s : ℤ) m • V.smul w m b) = 0 from by
      refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
      rw [hwmem, SuperVertexAlgebra.smul_zero_left, smul_zero]]
    exact (V.superO hV).zero_mem
  · obtain ⟨Ws, hWs⟩ : ∃ Ws : ℕ, (Ws : ℤ) = (K : ℤ) + (M : ℤ) - (s : ℤ) - 1 :=
      ⟨((K : ℤ) + (M : ℤ) - (s : ℤ) - 1).toNat, by omega⟩
    have hwmem' : w ∈ V.gradingZ (Ws : ℤ) := by rwa [hWs]
    rw [show (∑ᶠ m : ℤ, ZhuHR.coeffS K M (s : ℤ) m • V.smul w m b)
          = ∑ᶠ m : ℤ, ZhuHR.coeffP K M s m • V.smul w m b from
        finsum_congr fun m => by rw [ZhuHR.coeffS_eq_coeffP],
      ← PresCombo_eq_finsumε V K M s Ws w b hWs]
    apply Submodule.sum_mem
    intro t _
    exact Submodule.smul_mem _ _ (V.superPres_mem_superO hV hwmem' b (t + 1))

/-! ## The commutator family lies in `O(V)`. -/

/-- `∑_{p,i} (cbz K p · cbz M i) • ⁅u₍ₚ₋₁₎, a₍ᵢ₋₂₎⁆_ε b ∈ O(V)`.  **No sign appears**: the
right-hand side of `mode_commutator_uniformε` is sign-free. -/
theorem commutator_family_mem_superO (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights)
    (hpos : ∀ k : ℤ, k < 0 → V.gradingZ k = ⊥) {K M : ℕ} {p q : ZMod 2} {u a : 𝒱}
    (hu : u ∈ V.gradingZ (K : ℤ)) (hup : u ∈ V.parity p)
    (ha : a ∈ V.gradingZ (M : ℤ)) (haq : a ∈ V.parity q) (b : 𝒱) :
    (∑ pp ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
        (cbz (K : ℤ) (pp : ℤ) * cbz (M : ℤ) (i : ℤ))
          • modeBracketε (koszul p q) (V.Y u) (V.Y a) ((pp : ℤ) - 1) ((i : ℤ) - 2) b)
      ∈ V.superO hV := by
  obtain ⟨N, hN⟩ := mode_commutator_uniformε V hup haq
  rw [show (∑ pp ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
            (cbz (K : ℤ) (pp : ℤ) * cbz (M : ℤ) (i : ℤ))
              • modeBracketε (koszul p q) (V.Y u) (V.Y a) ((pp : ℤ) - 1) ((i : ℤ) - 2) b)
        = ∑ s ∈ Finset.range N, ∑ pp ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
            (cbz (K : ℤ) (pp : ℤ) * cbz (M : ℤ) (i : ℤ) * cbz ((pp : ℤ) - 1) (s : ℤ))
              • V.smul (V.smul u (s : ℤ) a) ((pp : ℤ) + (i : ℤ) - 3 - (s : ℤ)) b from ?_]
  · apply Submodule.sum_mem
    intro s _
    exact S_mem_superO V hV hpos hu ha b s
  · rw [show (∑ pp ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
              (cbz (K : ℤ) (pp : ℤ) * cbz (M : ℤ) (i : ℤ))
                • modeBracketε (koszul p q) (V.Y u) (V.Y a) ((pp : ℤ) - 1) ((i : ℤ) - 2) b)
          = ∑ pp ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1), ∑ s ∈ Finset.range N,
              (cbz (K : ℤ) (pp : ℤ) * cbz (M : ℤ) (i : ℤ) * cbz ((pp : ℤ) - 1) (s : ℤ))
                • V.smul (V.smul u (s : ℤ) a) ((pp : ℤ) + (i : ℤ) - 3 - (s : ℤ)) b from
        Finset.sum_congr rfl fun pp _ => Finset.sum_congr rfl fun i _ => by
          rw [hN ((pp : ℤ) - 1) ((i : ℤ) - 2) b, Finset.smul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [smul_smul,
            show (pp : ℤ) - 1 + ((i : ℤ) - 2) - (s : ℤ) = (pp : ℤ) + (i : ℤ) - 3 - (s : ℤ) from by
              ring]]
    rw [show (∑ pp ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1), ∑ s ∈ Finset.range N,
              (cbz (K : ℤ) (pp : ℤ) * cbz (M : ℤ) (i : ℤ) * cbz ((pp : ℤ) - 1) (s : ℤ))
                • V.smul (V.smul u (s : ℤ) a) ((pp : ℤ) + (i : ℤ) - 3 - (s : ℤ)) b)
          = ∑ pp ∈ Finset.range (K + 1), ∑ s ∈ Finset.range N, ∑ i ∈ Finset.range (M + 1),
              (cbz (K : ℤ) (pp : ℤ) * cbz (M : ℤ) (i : ℤ) * cbz ((pp : ℤ) - 1) (s : ℤ))
                • V.smul (V.smul u (s : ℤ) a) ((pp : ℤ) + (i : ℤ) - 3 - (s : ℤ)) b from
        Finset.sum_congr rfl fun pp _ =>
          Finset.sum_comm (s := Finset.range (M + 1)) (t := Finset.range N)]
    rw [Finset.sum_comm (s := Finset.range (K + 1)) (t := Finset.range N)]

/-! ## The super right-ideal core. -/

/-- **The right-ideal core of Dong–Zhao Thm 3.1.**  For **bi-homogeneous** `u ∈ 𝒱_K ∩ 𝒱_p` and
`a ∈ 𝒱_M ∩ 𝒱_q`, the right super-Zhu product of `u` with a generator of `O(V)` is again in
`O(V)`: `u ∗ ((L₋₁a + L₀a) ∗ b) ∈ O(V)`.

The Koszul sign `ε = koszul p q` appears exactly once, as a constant multiple of the first
family; `O(V)` is a `ℂ`-submodule, so it is absorbed. -/
theorem right_ideal_coreε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights)
    (hpos : ∀ k : ℤ, k < 0 → V.gradingZ k = ⊥) {K M : ℕ} {p q : ZMod 2} {u a : 𝒱}
    (hu : u ∈ V.gradingZ (K : ℤ)) (hup : u ∈ V.parity p)
    (ha : a ∈ V.gradingZ (M : ℤ)) (haq : a ∈ V.parity q) (b : 𝒱) :
    V.superZhuMul hV u (V.superZhuMul hV (V.L (-1) a + V.L 0 a) b) ∈ V.superO hV := by
  rw [right_target_expandε V hV hu ha b]
  rw [show (∑ pp ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
            (cbz (K : ℤ) (pp : ℤ) * cbz (M : ℤ) (i : ℤ))
              • V.smul u ((pp : ℤ) - 1) (V.smul a ((i : ℤ) - 2) b))
        = (koszul p q) • (∑ pp ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
            (cbz (K : ℤ) (pp : ℤ) * cbz (M : ℤ) (i : ℤ))
              • V.smul a ((i : ℤ) - 2) (V.smul u ((pp : ℤ) - 1) b))
          + (∑ pp ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
              (cbz (K : ℤ) (pp : ℤ) * cbz (M : ℤ) (i : ℤ))
                • modeBracketε (koszul p q) (V.Y u) (V.Y a) ((pp : ℤ) - 1) ((i : ℤ) - 2) b) from by
      rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun pp _ => ?_
      rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mode_splitε V (koszul p q) u a b (pp : ℤ) (i : ℤ), smul_add, smul_comm]]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_)
    (commutator_family_mem_superO V hV hpos hu hup ha haq b)
  exact first_family_mem_superO V hV ha u b

end SuperZhuHR
