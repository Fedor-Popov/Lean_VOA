/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuRingResidue
import VOA.Modules.ZhuMuIdentity
import VOA.Modules.ZhuUCore
import VOA.Modules.ZhuVCore
import VOA.Modules.ZhuRightIdeal

/-!
# Zhu-product associator membership (Zhu Thm 2.1.2 crux) — unconditional.

`associator_core`: `(u*v)*w − u*(v*w) ∈ O W` for homogeneous `u ∈ 𝒱_K`, `v ∈ 𝒱_L`.

All hard sub-lemmas (`ZhuMu.mu_identity`, `ZhuUCore.u_core`, `ZhuVCore.v_core`) are imported.

## Status
`sorry`-free, with no project axioms. **`associator_core`** — the two-family `mode_iterate`
decomposition `Σμ(L,b,n)·Pres(u,K,v₍ᵦ₎w,n) + Σμ(K,a,n)·Pres(v,L,u₍ₐ₎w,n)` off `u_core`/`v_core`/
`mu_identity` — is *unconditional*; it is the crux input to the proved Zhu associativity-mod-`O`
theorem and hence the unconditional `Ring (A 𝒱)` (`ZhuRingInstance`).
`#print axioms = [propext, Classical.choice, Quot.sound]`.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators
open Classical

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The two `Pres`-tower target families and their membership in `O W`. -/

/-- The **u-outer family**: `∑_{b<Bv} ∑_{n=0}^{b} μ(L,b,n) • Pres(u, K, v₍b₎w, n)`. -/
noncomputable def Ufam (W : VertexOperatorAlgebra 𝒱) (K L : ℕ) (u v w : 𝒱) (Bv : ℕ) : 𝒱 :=
  ∑ b ∈ Finset.range Bv, ∑ n ∈ Finset.range (b + 1),
    ZhuMu.muCoeff L b n • Pres W K u (W.smul v (b : ℤ) w) n

/-- The **v-outer (swap) family**: `∑_{a<Bu} ∑_{n=0}^{a} μ(K,a,n) • Pres(v, L, u₍a₎w, n)`. -/
noncomputable def Vfam (W : VertexOperatorAlgebra 𝒱) (K L : ℕ) (u v w : 𝒱) (Bu : ℕ) : 𝒱 :=
  ∑ a ∈ Finset.range Bu, ∑ n ∈ Finset.range (a + 1),
    ZhuMu.muCoeff K a n • Pres W L v (W.smul u (a : ℤ) w) n

/-- `Ufam ∈ O W` (each `Pres(u,K,·,n) ∈ O` by `Pres_mem_O`, `u ∈ 𝒱_K`). -/
theorem Ufam_mem_O (W : VertexOperatorAlgebra 𝒱) {K L : ℕ} {u : 𝒱}
    (hu : u ∈ W.grading (K : ℤ)) (v w : 𝒱) (Bv : ℕ) : Ufam W K L u v w Bv ∈ O W := by
  refine Submodule.sum_mem _ (fun b _ => Submodule.sum_mem _ (fun n _ => ?_))
  exact Submodule.smul_mem _ _ (Pres_mem_O W hu (W.smul v (b : ℤ) w) n)

/-- `Vfam ∈ O W` (each `Pres(v,L,·,n) ∈ O` by `Pres_mem_O`, `v ∈ 𝒱_L`). -/
theorem Vfam_mem_O (W : VertexOperatorAlgebra 𝒱) {K L : ℕ} {v : 𝒱}
    (hv : v ∈ W.grading (L : ℤ)) (u w : 𝒱) (Bu : ℕ) : Vfam W K L u v w Bu ∈ O W := by
  refine Submodule.sum_mem _ (fun a _ => Submodule.sum_mem _ (fun n _ => ?_))
  exact Submodule.smul_mem _ _ (Pres_mem_O W hv (W.smul u (a : ℤ) w) n)

/-! ## Finite-sum infrastructure
(general `Finset` sum lemmas used below). -/

/-- A `finsum` of `𝒱`-valued terms lying in a submodule lies in it. -/
theorem finsum_mem_O' {ι : Type*} (W : VertexOperatorAlgebra 𝒱) (F : ι → 𝒱)
    (hF : ∀ i, F i ∈ O W) : (∑ᶠ i, F i) ∈ O W := by
  by_cases hfin : (Function.support F).Finite
  · rw [finsum_eq_finsetSum_of_support_subset F (s := hfin.toFinset)
        (fun i hi => hfin.mem_toFinset.mpr hi)]
    exact Submodule.sum_mem _ (fun i _ => hF i)
  · rw [finsum_of_infinite_support (by rwa [Set.not_finite] at hfin)]
    exact (O W).zero_mem

/-- Convert a finite-range `•`-sum into a `ℤ`-finsum. -/
theorem rangeSmul_eq_finsumZ' (C : ℤ → ℂ) (g : ℤ → 𝒱) (d : ℤ) {N : ℕ}
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

/-- If a scalar function has finite support, so does `m ↦ C m • w₍ₘ₎b`. -/
theorem smul_support_of_scalar' (W : VertexOperatorAlgebra 𝒱) (w b : 𝒱) (C : ℤ → ℂ)
    (hC : (Function.support C).Finite) :
    Function.HasFiniteSupport (fun m : ℤ => C m • W.smul w m b) := by
  apply Set.Finite.subset hC
  intro m hm
  rw [Function.mem_support] at hm ⊢
  intro h; apply hm; rw [h, zero_smul]

/-- Generic: if a scalar function `C` has finite support, so does `x ↦ C x • g x`. -/
theorem smul_support_of_scalar_gen {ι : Type*} (C : ι → ℂ) (g : ι → 𝒱)
    (hC : (Function.support C).Finite) :
    Function.HasFiniteSupport (fun x : ι => C x • g x) := by
  apply Set.Finite.subset hC
  intro x hx
  rw [Function.mem_support] at hx ⊢
  intro h; apply hx; rw [h, zero_smul]

/-- For `0 ≤ d`, `m ↦ cbz d (m + e)` has finite support. -/
theorem cbz_shift_support_fin' {d : ℤ} (hd : 0 ≤ d) (e : ℤ) :
    (Function.support (fun m : ℤ => cbz d (m + e))).Finite := by
  apply Set.Finite.subset (Set.finite_Icc (-e) (-e + d))
  intro m hm
  rw [Function.mem_support] at hm
  simp only [Set.mem_Icc]
  refine ⟨by by_contra h; exact hm (cbz_apply_neg d (by omega)),
    by by_contra h; exact hm (cbz_lt hd (by omega))⟩

/-- `Pres W Ws w b n` in the mode-value finsum form (`m = r-2-n`). -/
theorem Pres_eq_finsum' (W : VertexOperatorAlgebra 𝒱) (Ws : ℕ) (w b : 𝒱) (n : ℕ) :
    Pres W Ws w b n
      = ∑ᶠ m : ℤ, cbz ((Ws : ℤ) + n) (m + 2 + n) • W.smul w m b := by
  unfold Pres
  rw [show (∑ r ∈ Finset.range (Ws + n + 1),
            cbz ((Ws : ℤ) + n) (r : ℤ) • W.smul w ((r : ℤ) - 2 - n) b)
        = ∑ r ∈ Finset.range (Ws + n + 1),
            cbz ((Ws : ℤ) + n) (r : ℤ) • W.smul w ((r : ℤ) + (-2 - n)) b from
      Finset.sum_congr rfl fun r _ => by rw [show (r : ℤ) - 2 - n = (r : ℤ) + (-2 - n) from by ring]]
  rw [rangeSmul_eq_finsumZ' (fun q : ℤ => cbz ((Ws : ℤ) + n) q) (fun q => W.smul w q b) (-2 - n)
      (fun q hq => cbz_apply_neg _ hq)
      (fun q hq => cbz_lt (by positivity) (by omega))]
  rw [← finsum_comp_equiv (Equiv.addRight (-2 - (n : ℤ)))
      (f := fun m : ℤ => cbz ((Ws : ℤ) + n) (m + 2 + n) • W.smul w m b)]
  refine finsum_congr fun q => ?_
  simp only [Equiv.coe_addRight]
  rw [show (q + (-2 - (n : ℤ))) + 2 + n = q from by ring]

/-! ## Expansions of the two products. -/

/-- **RHS expansion**: `u*(v*w) = ∑_{p≤K} ∑_{c≤L} cbz K p · cbz L c • u₍ₚ₋₁₎(v₍ᵢ₋₁₎w)`. -/
theorem uvw_expand (W : VertexOperatorAlgebra 𝒱) {K L : ℕ} {u v : 𝒱}
    (hu : u ∈ W.grading (K : ℤ)) (hv : v ∈ W.grading (L : ℤ)) (w : 𝒱) :
    zhuMul W u (zhuMul W v w)
      = ∑ p ∈ Finset.range (K + 1), ∑ c ∈ Finset.range (L + 1),
          (cbz (K : ℤ) (p : ℤ) * cbz (L : ℤ) (c : ℤ))
            • W.smul u ((p : ℤ) - 1) (W.smul v ((c : ℤ) - 1) w) := by
  rw [zhuMul_homogeneous' W hu, show (K : ℤ).toNat + 1 = K + 1 from by simp]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [zhuMul_homogeneous' W hv, show (L : ℤ).toNat + 1 = L + 1 from by simp]
  rw [show W.smul u ((p : ℤ) - 1) (∑ c ∈ Finset.range (L + 1), cbz (L : ℤ) (c : ℤ) • W.smul v ((c : ℤ) - 1) w)
        = ∑ c ∈ Finset.range (L + 1), cbz (L : ℤ) (c : ℤ) • W.smul u ((p : ℤ) - 1) (W.smul v ((c : ℤ) - 1) w) from by
      rw [PreVertexAlgebra.smul_def, map_sum]
      exact Finset.sum_congr rfl fun c _ => by rw [LinearMap.map_smul]; rfl,
    Finset.smul_sum]
  exact Finset.sum_congr rfl fun c _ => by rw [smul_smul]

/-- `u₍ₐ₋₁₎v ∈ 𝒱_{K+L-a}` for `a ≤ K` (grade `K+L-a ≥ 0`). -/
theorem inner_uv_mem (W : VertexOperatorAlgebra 𝒱) {K L : ℕ} {u v : 𝒱}
    (hu : u ∈ W.grading (K : ℤ)) (hv : v ∈ W.grading (L : ℤ)) (a : ℕ) :
    W.smul u ((a : ℤ) - 1) v ∈ W.grading ((K : ℤ) + (L : ℤ) - (a : ℤ)) := by
  have h := W.smul_mem_grading hu hv ((a : ℤ) - 1)
  rwa [show (K : ℤ) + (L : ℤ) - ((a : ℤ) - 1) - 1 = (K : ℤ) + (L : ℤ) - (a : ℤ) from by ring] at h

/-- **LHS expansion (one step)**: `(u*v)*w = ∑_{a≤K} cbz K a • ((u₍ₐ₋₁₎v) * w)`. -/
theorem uvw_lhs_step (W : VertexOperatorAlgebra 𝒱) {K : ℕ} {u v : 𝒱}
    (hu : u ∈ W.grading (K : ℤ)) (w : 𝒱) :
    zhuMul W (zhuMul W u v) w
      = ∑ a ∈ Finset.range (K + 1),
          cbz (K : ℤ) (a : ℤ) • zhuMul W (W.smul u ((a : ℤ) - 1) v) w := by
  rw [zhuMul_homogeneous' W hu, show (K : ℤ).toNat + 1 = K + 1 from by simp]
  rw [show zhuMul W (∑ a ∈ Finset.range (K + 1), cbz (K : ℤ) (a : ℤ) • W.smul u ((a : ℤ) - 1) v) w
        = zhuL W w (∑ a ∈ Finset.range (K + 1), cbz (K : ℤ) (a : ℤ) • W.smul u ((a : ℤ) - 1) v) from rfl,
    map_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [map_smul]; rfl

/-! ## `Ufam` as a u-word collection. -/

/-- The net u-word coefficient (residue tower) of `u₍ₘ₎(v₍ᵦ₎w)` in `Ufam`. -/
noncomputable def uCoeffTower (K L b : ℕ) (m : ℤ) : ℂ :=
  ∑ k ∈ Finset.range (b + 1), cbz (K : ℤ) (m + 2 + (k : ℤ)) * cbz (L : ℤ) ((b : ℤ) - (k : ℤ))

/-- Per-`b` inner collapse: `∑_{n≤b} μ(L,b,n) • Pres(u,K,v₍b₎w,n) = ∑ᶠ m, uCoeffTower • u₍ₘ₎(v₍b₎w)`. -/
theorem Ufam_inner (W : VertexOperatorAlgebra 𝒱) (K L b : ℕ) (u v w : 𝒱) :
    (∑ n ∈ Finset.range (b + 1), ZhuMu.muCoeff L b n • Pres W K u (W.smul v (b : ℤ) w) n)
      = ∑ᶠ m : ℤ, uCoeffTower K L b m • W.smul u m (W.smul v (b : ℤ) w) := by
  -- expand each Pres into a finsum, pull the muCoeff scalar inside
  rw [show (∑ n ∈ Finset.range (b + 1), ZhuMu.muCoeff L b n • Pres W K u (W.smul v (b : ℤ) w) n)
        = ∑ n ∈ Finset.range (b + 1),
            ∑ᶠ m : ℤ, (ZhuMu.muCoeff L b n * cbz ((K : ℤ) + n) (m + 2 + n))
              • W.smul u m (W.smul v (b : ℤ) w) from
      Finset.sum_congr rfl fun n _ => by
        rw [Pres_eq_finsum' W K u (W.smul v (b : ℤ) w) n]
        have hfin : Function.HasFiniteSupport
            (fun m : ℤ => cbz ((K : ℤ) + n) (m + 2 + n) • W.smul u m (W.smul v (b : ℤ) w)) :=
          smul_support_of_scalar' W u (W.smul v (b : ℤ) w) _
            (Set.Finite.subset (cbz_shift_support_fin' (d := (K : ℤ) + n) (by positivity) (2 + n))
              (fun m hm => by
                rw [Function.mem_support] at hm ⊢
                intro h; apply hm
                rw [show m + 2 + (n : ℤ) = m + (2 + (n : ℤ)) from by ring]; exact h))
        rw [smul_finsum' (ZhuMu.muCoeff L b n) hfin]
        refine finsum_congr fun m => ?_
        rw [smul_smul]]
  -- swap the finite n-sum past the finsum
  rw [← finsum_sum_comm (Finset.range (b + 1))
      (fun m n => (ZhuMu.muCoeff L b n * cbz ((K : ℤ) + n) (m + 2 + n))
        • W.smul u m (W.smul v (b : ℤ) w))
      (fun n _ => ?_)]
  · refine finsum_congr fun m => ?_
    rw [← Finset.sum_smul]
    congr 1
    rw [uCoeffTower]
    -- ∑_n μ(L,b,n)·cbz(K+n)(m+2+n) = ∑_k cbz K (m+2+k)·cbz L (b-k)  (mu_identity, s = m+2)
    rw [← ZhuMu.mu_identity K L b (m + 2)]
  · -- finite support of m ↦ (μ·cbz)• u₍ₘ₎(...) for fixed n
    refine smul_support_of_scalar' W u (W.smul v (b : ℤ) w) _ (Set.Finite.subset
      (cbz_shift_support_fin' (d := (K : ℤ) + n) (by positivity) (2 + n)) ?_)
    intro m hm
    rw [Function.mem_support] at hm ⊢
    intro h; apply hm
    rw [show (ZhuMu.muCoeff L b n * cbz ((K : ℤ) + n) (m + 2 + n))
          = (ZhuMu.muCoeff L b n) * cbz ((K : ℤ) + n) (m + (2 + (n : ℤ))) from by
        rw [show m + (2 + (n : ℤ)) = m + 2 + (n : ℤ) from by ring], h, mul_zero]

/-- The net v-word coefficient (residue tower) of `v₍ᵧ₎(u₍ₐ₎w)` in `Vfam`. -/
noncomputable def vCoeffTower (K L a : ℕ) (γ : ℤ) : ℂ :=
  ∑ k ∈ Finset.range (a + 1), cbz (L : ℤ) (γ + 2 + (k : ℤ)) * cbz (K : ℤ) ((a : ℤ) - (k : ℤ))

/-- Per-`a` inner collapse: `∑_{n≤a} μ(K,a,n) • Pres(v,L,u₍a₎w,n) = ∑ᶠ γ, vCoeffTower • v₍ᵧ₎(u₍ₐ₎w)`. -/
theorem Vfam_inner (W : VertexOperatorAlgebra 𝒱) (K L a : ℕ) (u v w : 𝒱) :
    (∑ n ∈ Finset.range (a + 1), ZhuMu.muCoeff K a n • Pres W L v (W.smul u (a : ℤ) w) n)
      = ∑ᶠ γ : ℤ, vCoeffTower K L a γ • W.smul v γ (W.smul u (a : ℤ) w) := by
  rw [show (∑ n ∈ Finset.range (a + 1), ZhuMu.muCoeff K a n • Pres W L v (W.smul u (a : ℤ) w) n)
        = ∑ n ∈ Finset.range (a + 1),
            ∑ᶠ γ : ℤ, (ZhuMu.muCoeff K a n * cbz ((L : ℤ) + n) (γ + 2 + n))
              • W.smul v γ (W.smul u (a : ℤ) w) from
      Finset.sum_congr rfl fun n _ => by
        rw [Pres_eq_finsum' W L v (W.smul u (a : ℤ) w) n]
        have hfin : Function.HasFiniteSupport
            (fun γ : ℤ => cbz ((L : ℤ) + n) (γ + 2 + n) • W.smul v γ (W.smul u (a : ℤ) w)) :=
          smul_support_of_scalar' W v (W.smul u (a : ℤ) w) _
            (Set.Finite.subset (cbz_shift_support_fin' (d := (L : ℤ) + n) (by positivity) (2 + n))
              (fun γ hγ => by
                rw [Function.mem_support] at hγ ⊢
                intro h; apply hγ
                rw [show γ + 2 + (n : ℤ) = γ + (2 + (n : ℤ)) from by ring]; exact h))
        rw [smul_finsum' (ZhuMu.muCoeff K a n) hfin]
        refine finsum_congr fun γ => ?_
        rw [smul_smul]]
  rw [← finsum_sum_comm (Finset.range (a + 1))
      (fun γ n => (ZhuMu.muCoeff K a n * cbz ((L : ℤ) + n) (γ + 2 + n))
        • W.smul v γ (W.smul u (a : ℤ) w))
      (fun n _ => ?_)]
  · refine finsum_congr fun γ => ?_
    rw [← Finset.sum_smul]
    congr 1
    rw [vCoeffTower]
    rw [← ZhuMu.mu_identity L K a (γ + 2)]
  · refine smul_support_of_scalar' W v (W.smul u (a : ℤ) w) _ (Set.Finite.subset
      (cbz_shift_support_fin' (d := (L : ℤ) + n) (by positivity) (2 + n)) ?_)
    intro γ hγ
    rw [Function.mem_support] at hγ ⊢
    intro h; apply hγ
    rw [show (ZhuMu.muCoeff K a n * cbz ((L : ℤ) + n) (γ + 2 + n))
          = (ZhuMu.muCoeff K a n) * cbz ((L : ℤ) + n) (γ + (2 + (n : ℤ))) from by
        rw [show γ + (2 + (n : ℤ)) = γ + 2 + (n : ℤ) from by ring], h, mul_zero]

/-! ## LHS expansion via homogeneity + mode_iterate. -/

/-- For `a ≤ K`, expand `(u₍ₐ₋₁₎v)*w` via homogeneity (grade `K+L-a`) and `mode_iterate`,
extending the `r`-range to the fixed `range (K+L+1)` (extra terms vanish via `cbz`). -/
theorem lhs_per_a (W : VertexOperatorAlgebra 𝒱) {K L : ℕ} {u v : 𝒱}
    (hu : u ∈ W.grading (K : ℤ)) (hv : v ∈ W.grading (L : ℤ)) (w : 𝒱) {a : ℕ} (haK : a ≤ K) :
    zhuMul W (W.smul u ((a : ℤ) - 1) v) w
      = ∑ r ∈ Finset.range (K + L + 1),
          ∑ᶠ i : ℕ, (cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
              * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
            • (W.smul u ((a : ℤ) - 1 - (i : ℤ)) (W.smul v ((r : ℤ) - 1 + (i : ℤ)) w)
              - ((-1 : ℂ) ^ ((a : ℤ) - 1))
                • W.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (W.smul u (i : ℤ) w)) := by
  have hmem := inner_uv_mem W hu hv a
  rw [zhuMul_homogeneous' W hmem]
  -- the toNat of K+L-a is K+L-a since a ≤ K
  have htn : ((K : ℤ) + (L : ℤ) - (a : ℤ)).toNat = K + L - a := by
    have : ((K : ℤ) + (L : ℤ) - (a : ℤ)) = ((K + L - a : ℕ) : ℤ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [this, Int.toNat_natCast]
  -- rewrite the range index and apply mode_iterate inside each summand
  rw [show (∑ m ∈ Finset.range (((K : ℤ) + (L : ℤ) - (a : ℤ)).toNat + 1),
            cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (m : ℤ)
              • W.smul (W.smul u ((a : ℤ) - 1) v) ((m : ℤ) - 1) w)
        = ∑ r ∈ Finset.range (K + L + 1),
            cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
              • W.smul (W.smul u ((a : ℤ) - 1) v) ((r : ℤ) - 1) w from ?_]
  · -- now expand the composite mode via mode_iterate per r
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [mode_iterate W u v ((a : ℤ) - 1) ((r : ℤ) - 1) w]
    rw [show ((a : ℤ) - 1) + ((r : ℤ) - 1) = ((a : ℤ) - 1) + ((r : ℤ) - 1) from rfl]
    -- distribute the cbz scalar into the finsum
    have hfin : Function.HasFiniteSupport
        (fun i : ℕ => ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i)
          • (W.smul u (((a : ℤ) - 1) - (i : ℤ)) (W.smul v (((r : ℤ) - 1) + (i : ℤ)) w)
            - ((-1 : ℂ) ^ ((a : ℤ) - 1))
              • W.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (W.smul u (i : ℤ) w))) := by
      -- both v₍ᵣ₋₁₊ᵢ₎w and u₍ᵢ₎w vanish for large i (regularity)
      obtain ⟨Nv, hNv⟩ := W.regularity v w
      obtain ⟨Nu, hNu⟩ := W.regularity u w
      apply Set.Finite.subset (Set.finite_Icc (0 : ℕ) (Nv.toNat + Nu.toNat))
      intro i hi
      rw [Function.mem_support] at hi
      simp only [Set.mem_Icc]
      refine ⟨Nat.zero_le _, ?_⟩
      by_contra hbig
      apply hi
      have hNvle : Nv ≤ (Nv.toNat : ℤ) := Int.self_le_toNat Nv
      have hNule : Nu ≤ (Nu.toNat : ℤ) := Int.self_le_toNat Nu
      have hige : Nv.toNat + Nu.toNat + 1 ≤ i := by omega
      have hige' : ((Nv.toNat : ℤ) + (Nu.toNat : ℤ) + 1) ≤ (i : ℤ) := by exact_mod_cast hige
      have hv0 : W.smul v (((r : ℤ) - 1) + (i : ℤ)) w = 0 := hNv _ (by omega)
      have hu0 : W.smul u (i : ℤ) w = 0 := hNu _ (by omega)
      rw [hv0, hu0]
      simp
    rw [smul_finsum' (cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)) hfin]
    refine finsum_congr fun i => ?_
    rw [smul_smul]
  · -- extend the r-range; extra terms r > K+L-a vanish (cbz = 0)
    refine Finset.sum_subset ?_ ?_
    · intro x hx
      rw [Finset.mem_range, htn] at hx
      rw [Finset.mem_range]; omega
    · intro r hr hrni
      have hrlo : (K + L - a) + 1 ≤ r := by
        rw [htn] at hrni; exact Nat.le_of_not_lt (fun h => hrni (Finset.mem_range.mpr h))
      rw [cbz_lt (by omega) (by
        have : ((K + L - a : ℕ) : ℤ) < (r : ℤ) := by exact_mod_cast (by omega : K + L - a < r)
        rw [Nat.cast_sub (by omega)] at this; push_cast at this ⊢; omega :
        ((K : ℤ) + (L : ℤ) - (a : ℤ)) < (r : ℤ)),
        zero_smul]

/-! ## The U-side and V-side of `(u*v)*w`. -/

/-- The **U-side** of `(u*v)*w`: all `u₍ₐ₋₁₋ᵢ₎(v₍ᵣ₋₁₊ᵢ₎w)` terms. -/
noncomputable def USide (W : VertexOperatorAlgebra 𝒱) (K L : ℕ) (u v w : 𝒱) : 𝒱 :=
  ∑ a ∈ Finset.range (K + 1), ∑ r ∈ Finset.range (K + L + 1),
    ∑ᶠ i : ℕ, (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
        * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
      • W.smul u ((a : ℤ) - 1 - (i : ℤ)) (W.smul v ((r : ℤ) - 1 + (i : ℤ)) w)

/-- The **V-side** of `(u*v)*w`: all `v₍ₐ₊ᵣ₋₂₋ᵢ₎(u₍ᵢ₎w)` terms (carrying the sign `(-1)^(a-1)`). -/
noncomputable def VSide (W : VertexOperatorAlgebra 𝒱) (K L : ℕ) (u v w : 𝒱) : 𝒱 :=
  ∑ a ∈ Finset.range (K + 1), ∑ r ∈ Finset.range (K + L + 1),
    ∑ᶠ i : ℕ, (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
        * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
      • W.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (W.smul u (i : ℤ) w)

/-- Finiteness of the per-`(a,r)` u-side `i`-finsum (regularity of `v` on `w`). -/
theorem uside_fin (W : VertexOperatorAlgebra 𝒱) (K L : ℕ) (u v w : 𝒱) (a r : ℕ) :
    Function.HasFiniteSupport (fun i : ℕ =>
      (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
          * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
        • W.smul u ((a : ℤ) - 1 - (i : ℤ)) (W.smul v ((r : ℤ) - 1 + (i : ℤ)) w)) := by
  obtain ⟨Nv, hNv⟩ := W.regularity v w
  apply Set.Finite.subset (Set.finite_Icc (0 : ℕ) Nv.toNat)
  intro i hi
  rw [Function.mem_support] at hi
  simp only [Set.mem_Icc]
  refine ⟨Nat.zero_le _, ?_⟩
  by_contra hbig
  apply hi
  have hNvle : Nv ≤ (Nv.toNat : ℤ) := Int.self_le_toNat Nv
  have hi' : (Nv.toNat : ℤ) + 1 ≤ (i : ℤ) := by exact_mod_cast (by omega : Nv.toNat + 1 ≤ i)
  rw [show W.smul v ((r : ℤ) - 1 + (i : ℤ)) w = (0 : 𝒱) from hNv _ (by omega)]
  simp

/-- Finiteness of the per-`(a,r)` v-side `i`-finsum (regularity of `u` on `w`). -/
theorem vside_fin (W : VertexOperatorAlgebra 𝒱) (K L : ℕ) (u v w : 𝒱) (a r : ℕ) :
    Function.HasFiniteSupport (fun i : ℕ =>
      (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
          * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
        • W.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (W.smul u (i : ℤ) w)) := by
  obtain ⟨Nu, hNu⟩ := W.regularity u w
  apply Set.Finite.subset (Set.finite_Icc (0 : ℕ) Nu.toNat)
  intro i hi
  rw [Function.mem_support] at hi
  simp only [Set.mem_Icc]
  refine ⟨Nat.zero_le _, ?_⟩
  by_contra hbig
  apply hi
  have hNule : Nu ≤ (Nu.toNat : ℤ) := Int.self_le_toNat Nu
  have hi' : (Nu.toNat : ℤ) + 1 ≤ (i : ℤ) := by exact_mod_cast (by omega : Nu.toNat + 1 ≤ i)
  rw [show W.smul u (i : ℤ) w = (0 : 𝒱) from hNu _ (by omega)]
  simp

/-- **Master split**: `(u*v)*w = USide − VSide`. -/
theorem lhs_split (W : VertexOperatorAlgebra 𝒱) {K L : ℕ} {u v : 𝒱}
    (hu : u ∈ W.grading (K : ℤ)) (hv : v ∈ W.grading (L : ℤ)) (w : 𝒱) :
    zhuMul W (zhuMul W u v) w = USide W K L u v w - VSide W K L u v w := by
  rw [uvw_lhs_step W hu w]
  rw [show (∑ a ∈ Finset.range (K + 1),
            cbz (K : ℤ) (a : ℤ) • zhuMul W (W.smul u ((a : ℤ) - 1) v) w)
        = ∑ a ∈ Finset.range (K + 1), cbz (K : ℤ) (a : ℤ) •
            (∑ r ∈ Finset.range (K + L + 1),
              ∑ᶠ i : ℕ, (cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                  * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
                • (W.smul u ((a : ℤ) - 1 - (i : ℤ)) (W.smul v ((r : ℤ) - 1 + (i : ℤ)) w)
                  - ((-1 : ℂ) ^ ((a : ℤ) - 1))
                    • W.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (W.smul u (i : ℤ) w))) from
      Finset.sum_congr rfl fun a ha =>
        by rw [lhs_per_a W hu hv w (Finset.mem_range.mp ha |> Nat.lt_succ_iff.mp)]]
  -- distribute and split each summand into u-part minus v-part
  rw [USide, VSide, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r hr => ?_
  -- split the i-finsum: scalar•(uword - sv•vword) = scalar•uword - (scalar·sv)•vword
  rw [smul_finsum' (cbz (K : ℤ) (a : ℤ)) (by
    -- finite support of the per-(a,r) inner finsum
    obtain ⟨Nv, hNv⟩ := W.regularity v w
    obtain ⟨Nu, hNu⟩ := W.regularity u w
    apply Set.Finite.subset (Set.finite_Icc (0 : ℕ) (Nv.toNat + Nu.toNat))
    intro i hi
    rw [Function.mem_support] at hi
    simp only [Set.mem_Icc]
    refine ⟨Nat.zero_le _, ?_⟩
    by_contra hbig
    apply hi
    have hNvle : Nv ≤ (Nv.toNat : ℤ) := Int.self_le_toNat Nv
    have hNule : Nu ≤ (Nu.toNat : ℤ) := Int.self_le_toNat Nu
    have hi' : ((Nv.toNat : ℤ) + (Nu.toNat : ℤ) + 1) ≤ (i : ℤ) := by
      exact_mod_cast (by omega : Nv.toNat + Nu.toNat + 1 ≤ i)
    have e1 : W.smul v ((r : ℤ) - 1 + (i : ℤ)) w = 0 := hNv _ (by omega)
    have e2 : W.smul u (i : ℤ) w = 0 := hNu _ (by omega)
    rw [show W.smul v ((r : ℤ) - 1 + (i : ℤ)) w = (0 : 𝒱) from e1,
      show W.smul u (i : ℤ) w = (0 : 𝒱) from e2]
    simp)]
  rw [show (∑ᶠ i : ℕ, cbz (K : ℤ) (a : ℤ) •
            ((cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
              • (W.smul u ((a : ℤ) - 1 - (i : ℤ)) (W.smul v ((r : ℤ) - 1 + (i : ℤ)) w)
                - ((-1 : ℂ) ^ ((a : ℤ) - 1))
                  • W.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (W.smul u (i : ℤ) w))))
        = ∑ᶠ i : ℕ,
            ((cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
              • W.smul u ((a : ℤ) - 1 - (i : ℤ)) (W.smul v ((r : ℤ) - 1 + (i : ℤ)) w)
            - (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
              • W.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (W.smul u (i : ℤ) w)) from
      finsum_congr fun i => by rw [smul_smul, smul_sub, smul_smul]; ring_nf]
  rw [finsum_sub_distrib (uside_fin W K L u v w a r) (vside_fin W K L u v w a r)]

/-! ## V-side reindex: collect v-words by mode value. -/

/-- Per-`(a,i)` reindex of the `r`-sum to a `∑ᶠ γ` over the v-mode value (`γ = a+r-2-i`). -/
theorem vside_r_reindex (W : VertexOperatorAlgebra 𝒱) (K L : ℕ) (u v w : 𝒱) (a i : ℕ)
    (haK : a ≤ K) :
    (∑ r ∈ Finset.range (K + L + 1),
        cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
          • W.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (W.smul u (i : ℤ) w))
      = ∑ᶠ γ : ℤ, cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (γ - (a : ℤ) + 2 + (i : ℤ))
          • W.smul v γ (W.smul u (i : ℤ) w) := by
  rw [show (∑ r ∈ Finset.range (K + L + 1),
            cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
              • W.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (W.smul u (i : ℤ) w))
        = ∑ r ∈ Finset.range (K + L + 1),
            cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
              • W.smul v ((r : ℤ) + ((a : ℤ) - 2 - (i : ℤ))) (W.smul u (i : ℤ) w) from
      Finset.sum_congr rfl fun r _ => by
        rw [show ((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ) = (r : ℤ) + ((a : ℤ) - 2 - (i : ℤ)) from by ring]]
  rw [rangeSmul_eq_finsumZ' (fun q : ℤ => cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) q)
      (fun q => W.smul v q (W.smul u (i : ℤ) w)) ((a : ℤ) - 2 - (i : ℤ))
      (fun q hq => cbz_apply_neg _ hq)
      (fun q hq => cbz_lt (by omega) (by omega))]
  rw [← finsum_comp_equiv (Equiv.addRight ((a : ℤ) - 2 - (i : ℤ)))
      (f := fun γ : ℤ => cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (γ - (a : ℤ) + 2 + (i : ℤ))
        • W.smul v γ (W.smul u (i : ℤ) w))]
  refine finsum_congr fun q => ?_
  simp only [Equiv.coe_addRight]
  rw [show (q + ((a : ℤ) - 2 - (i : ℤ))) - (a : ℤ) + 2 + (i : ℤ) = q from by ring]

/-- The per-`(γ,i)` v-side coefficient (sum over `a`). -/
noncomputable def vSideCoeff (K L : ℕ) (γ : ℤ) (i : ℕ) : ℂ :=
  ∑ a ∈ Finset.range (K + 1),
    cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (γ - (a : ℤ) + 2 + (i : ℤ))
      * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1))

/-- Per-`i` V-side collapse: the `(a,r)` double sum collapses to `∑ᶠ γ, vSideCoeff • v₍ᵧ₎(u₍ᵢ₎w)`. -/
theorem vside_per_i (W : VertexOperatorAlgebra 𝒱) (K L : ℕ) (u v w : 𝒱) (i : ℕ) :
    (∑ a ∈ Finset.range (K + 1), ∑ r ∈ Finset.range (K + L + 1),
        (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
            * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
          • W.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (W.smul u (i : ℤ) w))
      = ∑ᶠ γ : ℤ, vSideCoeff K L γ i • W.smul v γ (W.smul u (i : ℤ) w) := by
  -- pull the a-only scalars out of the r-sum and reindex via vside_r_reindex
  rw [show (∑ a ∈ Finset.range (K + 1), ∑ r ∈ Finset.range (K + L + 1),
            (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
              • W.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (W.smul u (i : ℤ) w))
        = ∑ a ∈ Finset.range (K + 1),
            (cbz (K : ℤ) (a : ℤ) * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i)
                * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
              • ∑ᶠ γ : ℤ, cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (γ - (a : ℤ) + 2 + (i : ℤ))
                  • W.smul v γ (W.smul u (i : ℤ) w) from
      Finset.sum_congr rfl fun a ha => by
        rw [← vside_r_reindex W K L u v w a i (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)),
          Finset.smul_sum]
        exact Finset.sum_congr rfl fun r _ => by rw [smul_smul]; ring_nf]
  -- push the a-scalar into each finsum and swap the finite a-sum past ∑ᶠ γ
  rw [show (∑ a ∈ Finset.range (K + 1),
            (cbz (K : ℤ) (a : ℤ) * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i)
                * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
              • ∑ᶠ γ : ℤ, cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (γ - (a : ℤ) + 2 + (i : ℤ))
                  • W.smul v γ (W.smul u (i : ℤ) w))
        = ∑ a ∈ Finset.range (K + 1),
            ∑ᶠ γ : ℤ,
              (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (γ - (a : ℤ) + 2 + (i : ℤ))
                  * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
                • W.smul v γ (W.smul u (i : ℤ) w) from
      Finset.sum_congr rfl fun a ha => by
        have haK : a ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        have hfin : Function.HasFiniteSupport
            (fun γ : ℤ => cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (γ - (a : ℤ) + 2 + (i : ℤ))
              • W.smul v γ (W.smul u (i : ℤ) w)) :=
          smul_support_of_scalar' W v (W.smul u (i : ℤ) w) _
            (Set.Finite.subset
              (cbz_shift_support_fin' (d := (K : ℤ) + (L : ℤ) - (a : ℤ)) (by omega)
                (-(a : ℤ) + 2 + (i : ℤ)))
              (fun γ hγ => by
                rw [Function.mem_support] at hγ ⊢
                intro h; apply hγ
                rwa [show γ + (-(a : ℤ) + 2 + (i : ℤ)) = γ - (a : ℤ) + 2 + (i : ℤ) from by ring] at h))
        rw [smul_finsum' _ hfin]
        refine finsum_congr fun γ => ?_
        rw [smul_smul]; ring_nf]
  rw [← finsum_sum_comm (Finset.range (K + 1))
      (fun γ a => (cbz (K : ℤ) (a : ℤ)
          * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (γ - (a : ℤ) + 2 + (i : ℤ))
          * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
        • W.smul v γ (W.smul u (i : ℤ) w))
      (fun a ha => ?_)]
  · refine finsum_congr fun γ => ?_
    rw [vSideCoeff, Finset.sum_smul]
  · -- finite support of γ ↦ (...)• v₍ᵧ₎(...) for fixed a
    have haK : a ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    refine smul_support_of_scalar' W v (W.smul u (i : ℤ) w) _ (Set.Finite.subset
      (cbz_shift_support_fin' (d := (K : ℤ) + (L : ℤ) - (a : ℤ)) (by omega)
        (-(a : ℤ) + 2 + (i : ℤ))) ?_)
    intro γ hγ
    rw [Function.mem_support] at hγ ⊢
    intro h; apply hγ
    rw [show (cbz (K : ℤ) (a : ℤ)
            * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (γ - (a : ℤ) + 2 + (i : ℤ))
            * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
          = (cbz (K : ℤ) (a : ℤ) * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i)
              * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
              * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (γ + (-(a : ℤ) + 2 + (i : ℤ))) from by
        rw [show γ + (-(a : ℤ) + 2 + (i : ℤ)) = γ - (a : ℤ) + 2 + (i : ℤ) from by ring]; ring,
      h, mul_zero]

/-- The v-side coefficient equals `-vCoeffTower` (via `ZhuVCore.v_core`). -/
theorem vSideCoeff_eq (K L : ℕ) (γ : ℤ) (i : ℕ) :
    vSideCoeff K L γ i = - vCoeffTower K L i γ := by
  rw [vSideCoeff, vCoeffTower]
  rw [← ZhuVCore.v_core K L γ i]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show γ - (a : ℤ) + 2 + (i : ℤ) = γ + 2 + (i : ℤ) - (a : ℤ) from by ring]
  ring

/-- Finite support in `i` of the r-summed v-side term (for fixed `a`). -/
theorem vside_a_fin (W : VertexOperatorAlgebra 𝒱) (K L : ℕ) (u v w : 𝒱) (a : ℕ) :
    Function.HasFiniteSupport (fun i : ℕ => ∑ r ∈ Finset.range (K + L + 1),
      (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
          * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
        • W.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (W.smul u (i : ℤ) w)) := by
  obtain ⟨Nu, hNu⟩ := W.regularity u w
  apply Set.Finite.subset (Set.finite_Icc (0 : ℕ) Nu.toNat)
  intro i hi
  rw [Function.mem_support] at hi
  simp only [Set.mem_Icc]
  refine ⟨Nat.zero_le _, ?_⟩
  by_contra hbig
  apply hi
  have hNule : Nu ≤ (Nu.toNat : ℤ) := Int.self_le_toNat Nu
  have hi' : (Nu.toNat : ℤ) + 1 ≤ (i : ℤ) := by exact_mod_cast (by omega : Nu.toNat + 1 ≤ i)
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [show W.smul u (i : ℤ) w = (0 : 𝒱) from hNu _ (by omega)]
  simp

/-- `VSide` as a double finsum over `(i, γ)`. -/
theorem VSide_eq (W : VertexOperatorAlgebra 𝒱) (K L : ℕ) (u v w : 𝒱) :
    VSide W K L u v w
      = ∑ᶠ i : ℕ, ∑ᶠ γ : ℤ, vSideCoeff K L γ i • W.smul v γ (W.smul u (i : ℤ) w) := by
  rw [VSide]
  -- step 1: per a, swap the r-sum past the i-finsum (innermost)
  rw [show (∑ a ∈ Finset.range (K + 1), ∑ r ∈ Finset.range (K + L + 1),
            ∑ᶠ i : ℕ, (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
              • W.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (W.smul u (i : ℤ) w))
        = ∑ a ∈ Finset.range (K + 1),
            ∑ᶠ i : ℕ, ∑ r ∈ Finset.range (K + L + 1),
              (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                  * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
                • W.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (W.smul u (i : ℤ) w) from
      Finset.sum_congr rfl fun a _ => by
        rw [← finsum_sum_comm (Finset.range (K + L + 1))
            (fun i r => (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
              • W.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (W.smul u (i : ℤ) w))
            (fun r _ => vside_fin W K L u v w a r)]]
  -- step 2: swap the a-sum past the i-finsum
  rw [← finsum_sum_comm (Finset.range (K + 1))
      (fun i a => ∑ r ∈ Finset.range (K + L + 1),
        (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
            * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
          • W.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (W.smul u (i : ℤ) w))
      (fun a _ => vside_a_fin W K L u v w a)]
  -- step 3: apply vside_per_i per i
  refine finsum_congr fun i => ?_
  rw [vside_per_i W K L u v w i]

/-- `Vfam` as a double finsum over `(i, γ)` (extending the `i`-range to all `ℕ`). -/
theorem Vfam_eq (W : VertexOperatorAlgebra 𝒱) (K L : ℕ) (u v w : 𝒱) {Bu : ℕ}
    (hBu : ∀ a : ℕ, Bu ≤ a → W.smul u (a : ℤ) w = 0) :
    Vfam W K L u v w Bu
      = ∑ᶠ i : ℕ, ∑ᶠ γ : ℤ, vCoeffTower K L i γ • W.smul v γ (W.smul u (i : ℤ) w) := by
  rw [Vfam]
  rw [show (∑ a ∈ Finset.range Bu, ∑ n ∈ Finset.range (a + 1),
            ZhuMu.muCoeff K a n • Pres W L v (W.smul u (a : ℤ) w) n)
        = ∑ a ∈ Finset.range Bu,
            ∑ᶠ γ : ℤ, vCoeffTower K L a γ • W.smul v γ (W.smul u (a : ℤ) w) from
      Finset.sum_congr rfl fun a _ => Vfam_inner W K L a u v w]
  -- extend the range to all ℕ: terms with i ≥ Bu vanish (u₍ᵢ₎w = 0)
  refine (finsum_eq_finsetSum_of_support_subset _ (s := Finset.range Bu) ?_).symm
  intro i hi
  rw [Function.mem_support] at hi
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hge
  apply hi
  rw [show W.smul u (i : ℤ) w = (0 : 𝒱) from hBu i (by omega)]
  refine finsum_eq_zero_of_forall_eq_zero fun γ => ?_
  rw [PreVertexAlgebra.smul_zero_right, smul_zero]

/-- **The v-family matches**: `-VSide = Vfam`. -/
theorem neg_VSide_eq_Vfam (W : VertexOperatorAlgebra 𝒱) (K L : ℕ) (u v w : 𝒱) {Bu : ℕ}
    (hBu : ∀ a : ℕ, Bu ≤ a → W.smul u (a : ℤ) w = 0) :
    - VSide W K L u v w = Vfam W K L u v w Bu := by
  rw [VSide_eq, Vfam_eq W K L u v w hBu, ← finsum_neg_distrib]
  refine finsum_congr fun i => ?_
  rw [← finsum_neg_distrib]
  refine finsum_congr fun γ => ?_
  rw [vSideCoeff_eq, neg_smul, neg_neg]

/-! ## U-side reindex: collect u-words by mode value. -/

/-- Per-`(b,i)` reindex of the `a`-sum to a `∑ᶠ m` over the u-mode value (`m = a-1-i`),
for a fixed inner vector `v₍ᵦ₎w`. -/
theorem uside_a_reindex (W : VertexOperatorAlgebra 𝒱) (K L : ℕ) (u v w : 𝒱) (i : ℕ) (b : ℤ) :
    (∑ a ∈ Finset.range (K + 1),
        (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (b + 1 - (i : ℤ))
            * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
          • W.smul u ((a : ℤ) - 1 - (i : ℤ)) (W.smul v b w))
      = ∑ᶠ m : ℤ, (cbz (K : ℤ) (m + 1 + (i : ℤ))
            * cbz ((K : ℤ) + (L : ℤ) - (m + 1 + (i : ℤ))) (b + 1 - (i : ℤ))
            * ((-1 : ℂ) ^ i * gBinom (m + (i : ℤ)) i))
          • W.smul u m (W.smul v b w) := by
  rw [show (∑ a ∈ Finset.range (K + 1),
            (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (b + 1 - (i : ℤ))
                * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
              • W.smul u ((a : ℤ) - 1 - (i : ℤ)) (W.smul v b w))
        = ∑ a ∈ Finset.range (K + 1),
            (fun p : ℤ => cbz (K : ℤ) p * cbz ((K : ℤ) + (L : ℤ) - p) (b + 1 - (i : ℤ))
                * ((-1 : ℂ) ^ i * gBinom (p - 1) i)) (a : ℤ)
              • W.smul u ((a : ℤ) + (-1 - (i : ℤ))) (W.smul v b w) from
      Finset.sum_congr rfl fun a _ => by
        simp only
        rw [show (a : ℤ) + (-1 - (i : ℤ)) = (a : ℤ) - 1 - (i : ℤ) from by ring]]
  rw [rangeSmul_eq_finsumZ'
      (fun p : ℤ => cbz (K : ℤ) p * cbz ((K : ℤ) + (L : ℤ) - p) (b + 1 - (i : ℤ))
        * ((-1 : ℂ) ^ i * gBinom (p - 1) i))
      (fun x => W.smul u x (W.smul v b w)) (-1 - (i : ℤ))
      (fun p hp => by dsimp only; rw [cbz_apply_neg (K : ℤ) hp]; ring)
      (fun p hp => by dsimp only; rw [cbz_lt (by positivity) (by omega)]; ring)]
  -- reindex the summation variable q (= old a) to the mode m via q = m+1+i
  rw [← finsum_comp_equiv (Equiv.addRight (1 + (i : ℤ)))
      (f := fun q : ℤ => (cbz (K : ℤ) q * cbz ((K : ℤ) + (L : ℤ) - q) (b + 1 - (i : ℤ))
          * ((-1 : ℂ) ^ i * gBinom (q - 1) i)) • W.smul u (q + (-1 - (i : ℤ))) (W.smul v b w))]
  refine finsum_congr fun m => ?_
  simp only [Equiv.coe_addRight]
  rw [show (m + (1 + (i : ℤ))) + (-1 - (i : ℤ)) = m from by ring,
    show (m + (1 + (i : ℤ))) = m + 1 + (i : ℤ) from by ring,
    show (m + 1 + (i : ℤ)) - 1 = m + (i : ℤ) from by ring]

/-- Per-`(a,i)` reindex of the `r`-sum to a `∑ᶠ b` over the inner v-mode value (`b = r-1+i`). -/
theorem uside_r_reindex (W : VertexOperatorAlgebra 𝒱) (K L : ℕ) (u v w : 𝒱) (a i : ℕ)
    (haK : a ≤ K) :
    (∑ r ∈ Finset.range (K + L + 1),
        cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
          • W.smul u ((a : ℤ) - 1 - (i : ℤ)) (W.smul v ((r : ℤ) - 1 + (i : ℤ)) w))
      = ∑ᶠ b : ℤ, cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (b + 1 - (i : ℤ))
          • W.smul u ((a : ℤ) - 1 - (i : ℤ)) (W.smul v b w) := by
  rw [show (∑ r ∈ Finset.range (K + L + 1),
            cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
              • W.smul u ((a : ℤ) - 1 - (i : ℤ)) (W.smul v ((r : ℤ) - 1 + (i : ℤ)) w))
        = ∑ r ∈ Finset.range (K + L + 1),
            cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
              • W.smul u ((a : ℤ) - 1 - (i : ℤ)) (W.smul v ((r : ℤ) + ((i : ℤ) - 1)) w) from
      Finset.sum_congr rfl fun r _ => by
        rw [show (r : ℤ) - 1 + (i : ℤ) = (r : ℤ) + ((i : ℤ) - 1) from by ring]]
  rw [rangeSmul_eq_finsumZ' (fun q : ℤ => cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) q)
      (fun x => W.smul u ((a : ℤ) - 1 - (i : ℤ)) (W.smul v x w)) ((i : ℤ) - 1)
      (fun q hq => cbz_apply_neg _ hq)
      (fun q hq => cbz_lt (by omega) (by omega))]
  rw [← finsum_comp_equiv (Equiv.addRight ((i : ℤ) - 1))
      (f := fun b : ℤ => cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (b + 1 - (i : ℤ))
        • W.smul u ((a : ℤ) - 1 - (i : ℤ)) (W.smul v b w))]
  refine finsum_congr fun q => ?_
  simp only [Equiv.coe_addRight]
  rw [show (q + ((i : ℤ) - 1)) + 1 - (i : ℤ) = q from by ring]

/-- Per-`i` U-side collapse: `∑_a ∑_r [...] • u₍ₐ₋₁₋ᵢ₎(v₍ᵣ₋₁₊ᵢ₎w)
    = ∑ᶠ b ∑ᶠ m, [...] • u₍ₘ₎(v₍ᵦ₎w)`. -/
theorem uside_per_i (W : VertexOperatorAlgebra 𝒱) (K L : ℕ) (u v w : 𝒱) (i : ℕ) :
    (∑ a ∈ Finset.range (K + 1), ∑ r ∈ Finset.range (K + L + 1),
        (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
            * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
          • W.smul u ((a : ℤ) - 1 - (i : ℤ)) (W.smul v ((r : ℤ) - 1 + (i : ℤ)) w))
      = ∑ᶠ b : ℤ, ∑ᶠ m : ℤ,
          (cbz (K : ℤ) (m + 1 + (i : ℤ))
              * cbz ((K : ℤ) + (L : ℤ) - (m + 1 + (i : ℤ))) (b + 1 - (i : ℤ))
              * ((-1 : ℂ) ^ i * gBinom (m + (i : ℤ)) i))
            • W.smul u m (W.smul v b w) := by
  -- step 1: per a, factor the a-scalar and reindex the r-sum to ∑ᶠ b
  rw [show (∑ a ∈ Finset.range (K + 1), ∑ r ∈ Finset.range (K + L + 1),
            (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
              • W.smul u ((a : ℤ) - 1 - (i : ℤ)) (W.smul v ((r : ℤ) - 1 + (i : ℤ)) w))
        = ∑ a ∈ Finset.range (K + 1),
            ∑ᶠ b : ℤ, (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (b + 1 - (i : ℤ))
                * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
              • W.smul u ((a : ℤ) - 1 - (i : ℤ)) (W.smul v b w) from
      Finset.sum_congr rfl fun a ha => by
        have haK : a ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        rw [show (∑ r ∈ Finset.range (K + L + 1),
                (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                    * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
                  • W.smul u ((a : ℤ) - 1 - (i : ℤ)) (W.smul v ((r : ℤ) - 1 + (i : ℤ)) w))
              = (cbz (K : ℤ) (a : ℤ) * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
                  • ∑ r ∈ Finset.range (K + L + 1),
                      cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                        • W.smul u ((a : ℤ) - 1 - (i : ℤ)) (W.smul v ((r : ℤ) - 1 + (i : ℤ)) w) from by
            rw [Finset.smul_sum]
            exact Finset.sum_congr rfl fun r _ => by rw [smul_smul]; ring_nf]
        rw [uside_r_reindex W K L u v w a i haK]
        -- push the a-scalar into the b-finsum
        have hfin : Function.HasFiniteSupport
            (fun b : ℤ => cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (b + 1 - (i : ℤ))
              • W.smul u ((a : ℤ) - 1 - (i : ℤ)) (W.smul v b w)) :=
          smul_support_of_scalar_gen _ _
            (Set.Finite.subset
              (cbz_shift_support_fin' (d := (K : ℤ) + (L : ℤ) - (a : ℤ)) (by omega)
                (1 - (i : ℤ)))
              (fun b hb => by
                rw [Function.mem_support] at hb ⊢
                intro h; apply hb
                rwa [show b + (1 - (i : ℤ)) = b + 1 - (i : ℤ) from by ring] at h))
        rw [smul_finsum' _ hfin]
        refine finsum_congr fun b => ?_
        rw [smul_smul]; ring_nf]
  -- step 2: swap the a-sum past the b-finsum, then reindex a→m
  rw [← finsum_sum_comm (Finset.range (K + 1))
      (fun b a => (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (b + 1 - (i : ℤ))
          * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
        • W.smul u ((a : ℤ) - 1 - (i : ℤ)) (W.smul v b w))
      (fun a ha => ?_)]
  · refine finsum_congr fun b => ?_
    rw [uside_a_reindex W K L u v w i b]
  · -- finite support in b for fixed a
    have haK : a ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    refine smul_support_of_scalar_gen _ _ (Set.Finite.subset
      (cbz_shift_support_fin' (d := (K : ℤ) + (L : ℤ) - (a : ℤ)) (by omega) (1 - (i : ℤ))) ?_)
    intro b hb
    rw [Function.mem_support] at hb ⊢
    intro h; apply hb
    rw [show (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (b + 1 - (i : ℤ))
            * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
          = (cbz (K : ℤ) (a : ℤ) * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
              * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (b + (1 - (i : ℤ))) from by
        rw [show b + (1 - (i : ℤ)) = b + 1 - (i : ℤ) from by ring]; ring,
      h, mul_zero]

/-- The full `USide` summand. -/
noncomputable def uTerm (W : VertexOperatorAlgebra 𝒱) (K L : ℕ) (u v w : 𝒱)
    (i : ℕ) (b m : ℤ) : 𝒱 :=
  (cbz (K : ℤ) (m + 1 + (i : ℤ))
      * cbz ((K : ℤ) + (L : ℤ) - (m + 1 + (i : ℤ))) (b + 1 - (i : ℤ))
      * ((-1 : ℂ) ^ i * gBinom (m + (i : ℤ)) i))
    • W.smul u m (W.smul v b w)

/-- `uTerm` vanishes unless `0 ≤ b+1-i` (i.e. `i ≤ b+1`). -/
theorem uTerm_eq_zero_of_lt (W : VertexOperatorAlgebra 𝒱) (K L : ℕ) (u v w : 𝒱)
    (i : ℕ) (b m : ℤ) (h : b + 1 - (i : ℤ) < 0) : uTerm W K L u v w i b m = 0 := by
  rw [uTerm, cbz_apply_neg _ h]; simp

/-- Finite support in `i` of the r-summed u-side term (for fixed `a`). -/
theorem uside_a_fin (W : VertexOperatorAlgebra 𝒱) (K L : ℕ) (u v w : 𝒱) (a : ℕ) :
    Function.HasFiniteSupport (fun i : ℕ => ∑ r ∈ Finset.range (K + L + 1),
      (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
          * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
        • W.smul u ((a : ℤ) - 1 - (i : ℤ)) (W.smul v ((r : ℤ) - 1 + (i : ℤ)) w)) := by
  obtain ⟨Nv, hNv⟩ := W.regularity v w
  apply Set.Finite.subset (Set.finite_Icc (0 : ℕ) Nv.toNat)
  intro i hi
  rw [Function.mem_support] at hi
  simp only [Set.mem_Icc]
  refine ⟨Nat.zero_le _, ?_⟩
  by_contra hbig
  apply hi
  have hNvle : Nv ≤ (Nv.toNat : ℤ) := Int.self_le_toNat Nv
  have hi' : (Nv.toNat : ℤ) + 1 ≤ (i : ℤ) := by exact_mod_cast (by omega : Nv.toNat + 1 ≤ i)
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [show W.smul v ((r : ℤ) - 1 + (i : ℤ)) w = (0 : 𝒱) from hNv _ (by omega)]
  simp

/-- `USide` as a triple finsum over `(i, b, m)`. -/
theorem USide_eq (W : VertexOperatorAlgebra 𝒱) (K L : ℕ) (u v w : 𝒱) :
    USide W K L u v w
      = ∑ᶠ i : ℕ, ∑ᶠ b : ℤ, ∑ᶠ m : ℤ, uTerm W K L u v w i b m := by
  simp only [uTerm]
  rw [USide]
  -- step 1: per a, swap the r-sum past the i-finsum
  rw [show (∑ a ∈ Finset.range (K + 1), ∑ r ∈ Finset.range (K + L + 1),
            ∑ᶠ i : ℕ, (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
              • W.smul u ((a : ℤ) - 1 - (i : ℤ)) (W.smul v ((r : ℤ) - 1 + (i : ℤ)) w))
        = ∑ a ∈ Finset.range (K + 1),
            ∑ᶠ i : ℕ, ∑ r ∈ Finset.range (K + L + 1),
              (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                  * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
                • W.smul u ((a : ℤ) - 1 - (i : ℤ)) (W.smul v ((r : ℤ) - 1 + (i : ℤ)) w) from
      Finset.sum_congr rfl fun a _ => by
        rw [← finsum_sum_comm (Finset.range (K + L + 1))
            (fun i r => (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
              • W.smul u ((a : ℤ) - 1 - (i : ℤ)) (W.smul v ((r : ℤ) - 1 + (i : ℤ)) w))
            (fun r _ => uside_fin W K L u v w a r)]]
  -- step 2: swap the a-sum past the i-finsum
  rw [← finsum_sum_comm (Finset.range (K + 1))
      (fun i a => ∑ r ∈ Finset.range (K + L + 1),
        (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
            * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
          • W.smul u ((a : ℤ) - 1 - (i : ℤ)) (W.smul v ((r : ℤ) - 1 + (i : ℤ)) w))
      (fun a _ => uside_a_fin W K L u v w a)]
  -- step 3: apply uside_per_i per i
  refine finsum_congr fun i => ?_
  rw [uside_per_i W K L u v w i]

/-! ## Finsum swap helpers. -/

omit [Module ℂ 𝒱] in
/-- Swap a `ℕ`- and `ℤ`-finsum given joint finite support. -/
theorem swap_finsum_NZ (F : ℕ → ℤ → 𝒱)
    (hfin : (Function.support (fun p : ℕ × ℤ => F p.1 p.2)).Finite) :
    (∑ᶠ i : ℕ, ∑ᶠ b : ℤ, F i b) = ∑ᶠ b : ℤ, ∑ᶠ i : ℕ, F i b := by
  rw [← finsum_curry (fun p : ℕ × ℤ => F p.1 p.2) hfin]
  rw [← finsum_curry (fun p : ℤ × ℕ => F p.2 p.1) (by
    apply Set.Finite.subset (hfin.image Prod.swap)
    intro p hp
    rw [Function.mem_support] at hp
    refine ⟨(p.2, p.1), ?_, rfl⟩
    rw [Function.mem_support]; exact hp)]
  rw [← finsum_comp_equiv (Equiv.prodComm ℤ ℕ)
      (f := fun p : ℕ × ℤ => F p.1 p.2)]
  rfl

/-- For fixed `(i,b)`, `m ↦ uTerm` has finite support (bounded by `cbz K (m+1+i)`). -/
theorem uTerm_m_fin (W : VertexOperatorAlgebra 𝒱) (K L : ℕ) (u v w : 𝒱) (i : ℕ) (b : ℤ) :
    (Function.support (fun m : ℤ => uTerm W K L u v w i b m)).Finite := by
  apply Set.Finite.subset (Set.finite_Icc (-(i : ℤ) - 1) ((K : ℤ) - (i : ℤ)))
  intro m hm
  rw [Function.mem_support] at hm
  simp only [Set.mem_Icc]
  constructor
  · by_contra h
    apply hm; rw [uTerm, cbz_apply_neg (K : ℤ) (by omega), zero_mul, zero_mul, zero_smul]
  · by_contra h
    apply hm; rw [uTerm, cbz_lt (by positivity) (by omega), zero_mul, zero_mul, zero_smul]

/-- For fixed `b`, the pair `(i,m) ↦ uTerm` has finite support. -/
theorem uTerm_im_fin (W : VertexOperatorAlgebra 𝒱) (K L : ℕ) (u v w : 𝒱) (b : ℤ) :
    (Function.support (fun p : ℕ × ℤ => uTerm W K L u v w p.1 b p.2)).Finite := by
  apply Set.Finite.subset
    ((Set.finite_Icc (0 : ℕ) (b.toNat + 1)).prod (Set.finite_Icc (-(b) - 2) (K : ℤ)))
  intro p hp
  rw [Function.mem_support] at hp
  simp only [Set.mem_prod, Set.mem_Icc]
  -- from cbz K (m+1+i) ≠ 0: 0 ≤ m+1+i ≤ K; from cbz(...)(b+1-i) ≠ 0: 0 ≤ b+1-i
  have hc1 : cbz (K : ℤ) (p.2 + 1 + (p.1 : ℤ)) ≠ 0 := by
    intro h; apply hp; rw [uTerm, h, zero_mul, zero_mul, zero_smul]
  have hc2 : cbz ((K : ℤ) + (L : ℤ) - (p.2 + 1 + (p.1 : ℤ))) (b + 1 - (p.1 : ℤ)) ≠ 0 := by
    intro h; apply hp; rw [uTerm, h, mul_zero, zero_mul, zero_smul]
  have h1lo : (0 : ℤ) ≤ p.2 + 1 + (p.1 : ℤ) := by
    by_contra h; exact hc1 (cbz_apply_neg (K : ℤ) (by omega))
  have h1hi : p.2 + 1 + (p.1 : ℤ) ≤ (K : ℤ) := by
    by_contra h; exact hc1 (cbz_lt (by positivity) (by omega))
  have h2lo : (0 : ℤ) ≤ b + 1 - (p.1 : ℤ) := by
    by_contra h; exact hc2 (cbz_apply_neg _ (by omega))
  refine ⟨⟨Nat.zero_le _, ?_⟩, by omega, by omega⟩
  -- i ≤ b+1, so i ≤ b.toNat+1
  have : (p.1 : ℤ) ≤ b + 1 := by omega
  omega

/-- The pair `(i,b) ↦ ∑ᶠ m, uTerm` has finite support. -/
theorem uTerm_ib_fin (W : VertexOperatorAlgebra 𝒱) (K L : ℕ) (u v w : 𝒱) :
    (Function.support (fun p : ℕ × ℤ => ∑ᶠ m : ℤ, uTerm W K L u v w p.1 p.2 m)).Finite := by
  obtain ⟨Nv, hNv⟩ := W.regularity v w
  apply Set.Finite.subset
    ((Set.finite_Icc (0 : ℕ) Nv.toNat).prod (Set.finite_Icc (-1 : ℤ) (Nv - 1)))
  intro p hp
  rw [Function.mem_support] at hp
  simp only [Set.mem_prod, Set.mem_Icc]
  -- nonzero finsum ⟹ ∃ m, uTerm ≠ 0 ⟹ b+1-i ≥ 0 and v₍b₎w ≠ 0
  have hex : ∃ m : ℤ, uTerm W K L u v w p.1 p.2 m ≠ 0 := by
    by_contra hall
    exact hp (finsum_eq_zero_of_forall_eq_zero fun m => not_not.mp (not_exists.mp hall m))
  obtain ⟨m, hm⟩ := hex
  -- from uTerm ≠ 0: cbz(...)(b+1-i) ≠ 0 ⟹ b+1-i ≥ 0
  have h2lo : (0 : ℤ) ≤ p.2 + 1 - (p.1 : ℤ) := by
    by_contra h
    exact hm (uTerm_eq_zero_of_lt W K L u v w p.1 p.2 m (by omega))
  -- from uTerm ≠ 0: v₍b₎w ≠ 0 ⟹ p.2 < Nv
  have hvb : W.smul v p.2 w ≠ 0 := by
    intro h
    apply hm
    rw [uTerm, h, PreVertexAlgebra.smul_zero_right, smul_zero]
  have hbNv : p.2 < Nv := by
    by_contra h
    exact hvb (hNv p.2 (by omega))
  have hNvle : Nv ≤ (Nv.toNat : ℤ) := Int.self_le_toNat Nv
  refine ⟨⟨Nat.zero_le _, ?_⟩, by omega, by omega⟩
  -- i ≤ b+1 ≤ Nv, so i ≤ Nv.toNat
  have hib : (p.1 : ℤ) ≤ p.2 + 1 := by omega
  have : (p.1 : ℤ) ≤ Nv := by omega
  omega

/-- `USide` with the `i`-finsum innermost: `∑ᶠ b ∑ᶠ m ∑ᶠ i, uTerm`. -/
theorem USide_eq2 (W : VertexOperatorAlgebra 𝒱) (K L : ℕ) (u v w : 𝒱) :
    USide W K L u v w
      = ∑ᶠ b : ℤ, ∑ᶠ m : ℤ, ∑ᶠ i : ℕ, uTerm W K L u v w i b m := by
  rw [USide_eq]
  -- swap i and b (outermost two)
  rw [swap_finsum_NZ (fun i b => ∑ᶠ m : ℤ, uTerm W K L u v w i b m) (uTerm_ib_fin W K L u v w)]
  -- per b, swap i and m
  refine finsum_congr fun b => ?_
  rw [swap_finsum_NZ (fun i m => uTerm W K L u v w i b m) (uTerm_im_fin W K L u v w b)]

/-- The `i`-summed U-side scalar coefficient (for `u₍ₘ₎(v₍ᵦ₎w)`). -/
noncomputable def uSideScalar (K L : ℕ) (b m : ℤ) : ℂ :=
  ∑ᶠ i : ℕ, cbz (K : ℤ) (m + 1 + (i : ℤ))
      * cbz ((K : ℤ) + (L : ℤ) - (m + 1 + (i : ℤ))) (b + 1 - (i : ℤ))
      * ((-1 : ℂ) ^ i * gBinom (m + (i : ℤ)) i)

/-- The `i`-scalar has finite support (`cbz K (m+1+i)` bounds `i ≤ K-m-1`). -/
theorem uScalar_i_fin (K L : ℕ) (b m : ℤ) :
    (Function.support (fun i : ℕ => cbz (K : ℤ) (m + 1 + (i : ℤ))
        * cbz ((K : ℤ) + (L : ℤ) - (m + 1 + (i : ℤ))) (b + 1 - (i : ℤ))
        * ((-1 : ℂ) ^ i * gBinom (m + (i : ℤ)) i))).Finite := by
  apply Set.Finite.subset (Set.finite_Icc (0 : ℕ) ((K : ℤ) - m - 1).toNat)
  intro i hi
  rw [Function.mem_support] at hi
  simp only [Set.mem_Icc]
  refine ⟨Nat.zero_le _, ?_⟩
  by_contra h
  apply hi
  -- i > (K-m-1).toNat ⟹ m+1+i > K ⟹ cbz K (m+1+i) = 0
  have hile : ((K : ℤ) - m - 1).toNat + 1 ≤ i := by omega
  have : ((K : ℤ) - m - 1) < (i : ℤ) := by
    have := Int.self_le_toNat ((K : ℤ) - m - 1)
    have hc : (((K : ℤ) - m - 1).toNat : ℤ) + 1 ≤ (i : ℤ) := by exact_mod_cast hile
    omega
  rw [cbz_lt (by positivity) (by omega : (K : ℤ) < m + 1 + (i : ℤ)), zero_mul, zero_mul]

/-- Pull `u₍ₘ₎(v₍ᵦ₎w)` out of the `i`-finsum. -/
theorem uTerm_i_collapse (W : VertexOperatorAlgebra 𝒱) (K L : ℕ) (u v w : 𝒱) (b m : ℤ) :
    (∑ᶠ i : ℕ, uTerm W K L u v w i b m)
      = uSideScalar K L b m • W.smul u m (W.smul v b w) := by
  rw [uSideScalar, finsum_smul]
  refine finsum_congr fun i => ?_
  rw [uTerm]

/-- For `b = β ≥ 0`, the U-side scalar collapses (via `u_core`) to the residue tower. -/
theorem uSideScalar_pos (K L : ℕ) (β : ℕ) (m : ℤ) :
    uSideScalar K L (β : ℤ) m
      = ∑ j ∈ Finset.range (β + 2), cbz (K : ℤ) (m + 1 + (j : ℤ)) * cbz (L : ℤ) ((β : ℤ) + 1 - (j : ℤ)) := by
  rw [uSideScalar]
  -- the i-finsum truncates to range (β+2): cbz(...)(β+1-i) = 0 for i ≥ β+2
  rw [show (∑ᶠ i : ℕ, cbz (K : ℤ) (m + 1 + (i : ℤ))
            * cbz ((K : ℤ) + (L : ℤ) - (m + 1 + (i : ℤ))) ((β : ℤ) + 1 - (i : ℤ))
            * ((-1 : ℂ) ^ i * gBinom (m + (i : ℤ)) i))
        = ∑ i ∈ Finset.range (β + 2), cbz (K : ℤ) (m + 1 + (i : ℤ))
            * cbz ((K : ℤ) + (L : ℤ) - (m + 1 + (i : ℤ))) ((β : ℤ) + 1 - (i : ℤ))
            * ((-1 : ℂ) ^ i * gBinom (m + (i : ℤ)) i) from by
      refine finsum_eq_finsetSum_of_support_subset _ (fun i hi => ?_)
      rw [Function.mem_support] at hi
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra hge
      apply hi
      rw [cbz_apply_neg _ (by omega : (β : ℤ) + 1 - (i : ℤ) < 0), mul_zero, zero_mul]]
  -- match to u_core LHS, then rewrite via u_core
  rw [← ZhuUCore.u_core K L β m]
  refine Finset.sum_congr rfl fun i _ => by
    rw [show ((K : ℤ) + (L : ℤ) - (m + 1 + (i : ℤ))) = (K : ℤ) + (L : ℤ) - m - 1 - (i : ℤ) from by ring]
    ring

/-- For `b = β ≥ 0`: `uSideScalar = cbz K (m+1)·cbz L (β+1) + uCoeffTower`. -/
theorem uSideScalar_split (K L : ℕ) (β : ℕ) (m : ℤ) :
    uSideScalar K L (β : ℤ) m
      = cbz (K : ℤ) (m + 1) * cbz (L : ℤ) ((β : ℤ) + 1) + uCoeffTower K L β m := by
  rw [uSideScalar_pos K L β m, Finset.sum_range_succ'
      (fun j => cbz (K : ℤ) (m + 1 + (j : ℤ)) * cbz (L : ℤ) ((β : ℤ) + 1 - (j : ℤ))) (β + 1),
    add_comm]
  congr 1
  · -- the j=0 term
    rw [Nat.cast_zero]; ring
  · -- the reindexed body equals uCoeffTower
    rw [uCoeffTower]
    refine Finset.sum_congr rfl fun k _ => by
      push_cast
      rw [show m + 1 + ((k : ℤ) + 1) = m + 2 + (k : ℤ) from by ring,
        show (β : ℤ) + 1 - ((k : ℤ) + 1) = (β : ℤ) - (k : ℤ) from by ring]

/-- For `b < 0`: the U-side scalar equals the RHS coefficient `cbz K (m+1)·cbz L (b+1)`. -/
theorem uSideScalar_neg (K L : ℕ) (b m : ℤ) (hb : b < 0) :
    uSideScalar K L b m = cbz (K : ℤ) (m + 1) * cbz (L : ℤ) (b + 1) := by
  rw [uSideScalar]
  -- support ⊆ {0}: for i ≥ 1, b+1-i < 0
  rw [finsum_eq_single _ 0 (fun i hi => by
    rw [cbz_apply_neg _ (by omega : b + 1 - (i : ℤ) < 0), mul_zero, zero_mul])]
  -- evaluate at i = 0
  simp only [Nat.cast_zero, add_zero, pow_zero, one_mul, sub_zero]
  -- cbz (K+L-(m+1)) (b+1) = cbz L (b+1) since b+1 ≤ 0
  have hcbz : cbz ((K : ℤ) + (L : ℤ) - (m + 1)) (b + 1) = cbz (L : ℤ) (b + 1) := by
    rcases lt_or_eq_of_le (by omega : b + 1 ≤ 0) with hlt | heq
    · rw [cbz_apply_neg _ hlt, cbz_apply_neg _ hlt]
    · rw [heq, cbz_zero, cbz_zero]
  rw [hcbz, gBinom, Finset.range_zero, Finset.prod_empty, Nat.factorial_zero]
  norm_num

/-! ## RHS `u*(v*w)` as a double finsum. -/

/-- Inner reindex (per `p`) of the `c`-sum to `∑ᶠ b` over the inner v-mode. -/
theorem rhs_c_reindex (W : VertexOperatorAlgebra 𝒱) (K L : ℕ) (u v w : 𝒱) (p : ℕ) :
    (∑ c ∈ Finset.range (L + 1),
        (cbz (K : ℤ) (p : ℤ) * cbz (L : ℤ) (c : ℤ))
          • W.smul u ((p : ℤ) - 1) (W.smul v ((c : ℤ) - 1) w))
      = ∑ᶠ b : ℤ, (cbz (K : ℤ) (p : ℤ) * cbz (L : ℤ) (b + 1))
          • W.smul u ((p : ℤ) - 1) (W.smul v b w) := by
  rw [show (∑ c ∈ Finset.range (L + 1),
            (cbz (K : ℤ) (p : ℤ) * cbz (L : ℤ) (c : ℤ))
              • W.smul u ((p : ℤ) - 1) (W.smul v ((c : ℤ) - 1) w))
        = ∑ c ∈ Finset.range (L + 1),
            (fun q : ℤ => cbz (K : ℤ) (p : ℤ) * cbz (L : ℤ) q) (c : ℤ)
              • W.smul u ((p : ℤ) - 1) (W.smul v ((c : ℤ) + (-1)) w) from
      Finset.sum_congr rfl fun c _ => by
        simp only
        rw [show (c : ℤ) + (-1) = (c : ℤ) - 1 from by ring]]
  rw [rangeSmul_eq_finsumZ'
      (fun q : ℤ => cbz (K : ℤ) (p : ℤ) * cbz (L : ℤ) q)
      (fun x => W.smul u ((p : ℤ) - 1) (W.smul v x w)) (-1)
      (fun q hq => by dsimp only; rw [cbz_apply_neg (L : ℤ) hq, mul_zero])
      (fun q hq => by dsimp only
                      rw [cbz_lt (show (0:ℤ) ≤ (L:ℤ) by positivity) (show (L:ℤ) < q by omega),
                        mul_zero])]
  rw [← finsum_comp_equiv (Equiv.addRight (1 : ℤ))
      (f := fun q : ℤ => (cbz (K : ℤ) (p : ℤ) * cbz (L : ℤ) q)
        • W.smul u ((p : ℤ) - 1) (W.smul v (q + (-1)) w))]
  refine finsum_congr fun b => ?_
  simp only [Equiv.coe_addRight]
  rw [show (b + (1 : ℤ)) + (-1) = b from by ring]

/-- The full `u*(v*w)` as `∑ᶠ b ∑ᶠ m, cbz K (m+1)·cbz L (b+1) • u₍ₘ₎(v₍ᵦ₎w)`. -/
theorem RHS_eq (W : VertexOperatorAlgebra 𝒱) {K L : ℕ} {u v : 𝒱}
    (hu : u ∈ W.grading (K : ℤ)) (hv : v ∈ W.grading (L : ℤ)) (w : 𝒱) :
    zhuMul W u (zhuMul W v w)
      = ∑ᶠ b : ℤ, ∑ᶠ m : ℤ,
          (cbz (K : ℤ) (m + 1) * cbz (L : ℤ) (b + 1)) • W.smul u m (W.smul v b w) := by
  rw [uvw_expand W hu hv w]
  -- reindex each inner c-sum to ∑ᶠ b
  rw [show (∑ p ∈ Finset.range (K + 1), ∑ c ∈ Finset.range (L + 1),
            (cbz (K : ℤ) (p : ℤ) * cbz (L : ℤ) (c : ℤ))
              • W.smul u ((p : ℤ) - 1) (W.smul v ((c : ℤ) - 1) w))
        = ∑ p ∈ Finset.range (K + 1),
            ∑ᶠ b : ℤ, (cbz (K : ℤ) (p : ℤ) * cbz (L : ℤ) (b + 1))
              • W.smul u ((p : ℤ) - 1) (W.smul v b w) from
      Finset.sum_congr rfl fun p _ => rhs_c_reindex W K L u v w p]
  -- swap the finite p-sum past ∑ᶠ b
  rw [← finsum_sum_comm (Finset.range (K + 1))
      (fun b p => (cbz (K : ℤ) (p : ℤ) * cbz (L : ℤ) (b + 1))
        • W.smul u ((p : ℤ) - 1) (W.smul v b w))
      (fun p _ => ?_)]
  · -- per b, reindex the p-sum to ∑ᶠ m
    refine finsum_congr fun b => ?_
    rw [show (∑ p ∈ Finset.range (K + 1),
              (cbz (K : ℤ) (p : ℤ) * cbz (L : ℤ) (b + 1))
                • W.smul u ((p : ℤ) - 1) (W.smul v b w))
          = ∑ p ∈ Finset.range (K + 1),
              (fun q : ℤ => cbz (K : ℤ) q * cbz (L : ℤ) (b + 1)) (p : ℤ)
                • W.smul u ((p : ℤ) + (-1)) (W.smul v b w) from
        Finset.sum_congr rfl fun p _ => by
          simp only; rw [show (p : ℤ) + (-1) = (p : ℤ) - 1 from by ring]]
    rw [rangeSmul_eq_finsumZ'
        (fun q : ℤ => cbz (K : ℤ) q * cbz (L : ℤ) (b + 1))
        (fun x => W.smul u x (W.smul v b w)) (-1)
        (fun q hq => by dsimp only; rw [cbz_apply_neg (K : ℤ) hq, zero_mul])
        (fun q hq => by dsimp only; rw [cbz_lt (by positivity) (by omega), zero_mul])]
    rw [← finsum_comp_equiv (Equiv.addRight (1 : ℤ))
        (f := fun q : ℤ => (cbz (K : ℤ) q * cbz (L : ℤ) (b + 1))
          • W.smul u (q + (-1)) (W.smul v b w))]
    refine finsum_congr fun m => ?_
    simp only [Equiv.coe_addRight]
    rw [show (m + (1 : ℤ)) + (-1) = m from by ring]
  · -- finite support in b for fixed p
    refine smul_support_of_scalar_gen _ _ (Set.Finite.subset
      (cbz_shift_support_fin' (d := (L : ℤ)) (by positivity) 1) ?_)
    intro b hb
    rw [Function.mem_support] at hb ⊢
    intro h; apply hb
    rw [show (cbz (K : ℤ) (p : ℤ) * cbz (L : ℤ) (b + 1))
          = cbz (K : ℤ) (p : ℤ) * cbz (L : ℤ) (b + 1) from rfl, h, mul_zero]

/-- `USide` collapsed: `∑ᶠ b ∑ᶠ m, uSideScalar • u₍ₘ₎(v₍ᵦ₎w)`. -/
theorem USide_eq3 (W : VertexOperatorAlgebra 𝒱) (K L : ℕ) (u v w : 𝒱) :
    USide W K L u v w
      = ∑ᶠ b : ℤ, ∑ᶠ m : ℤ, uSideScalar K L b m • W.smul u m (W.smul v b w) := by
  rw [USide_eq2]
  refine finsum_congr fun b => ?_
  refine finsum_congr fun m => ?_
  rw [uTerm_i_collapse W K L u v w b m]

/-- `Ufam` as a double `ℤ`-finsum with the extended coefficient. -/
theorem Ufam_eq (W : VertexOperatorAlgebra 𝒱) (K L : ℕ) (u v w : 𝒱) {Bv : ℕ}
    (hBv : ∀ b : ℕ, Bv ≤ b → W.smul v (b : ℤ) w = 0) :
    Ufam W K L u v w Bv
      = ∑ᶠ b : ℤ, ∑ᶠ m : ℤ,
          (if 0 ≤ b then uCoeffTower K L b.toNat m else 0) • W.smul u m (W.smul v b w) := by
  rw [Ufam]
  rw [show (∑ b ∈ Finset.range Bv, ∑ n ∈ Finset.range (b + 1),
            ZhuMu.muCoeff L b n • Pres W K u (W.smul v (b : ℤ) w) n)
        = ∑ b ∈ Finset.range Bv,
            ∑ᶠ m : ℤ, uCoeffTower K L b m • W.smul u m (W.smul v (b : ℤ) w) from
      Finset.sum_congr rfl fun b _ => Ufam_inner W K L b u v w]
  -- convert the finite ℕ-sum over b to a ℤ-finsum (extend by the if-coefficient)
  -- first: ∑_{b∈range Bv} F b = ∑ᶠ b:ℕ F b  (tail vanishes since v₍b₎w = 0)
  rw [show (∑ b ∈ Finset.range Bv,
            ∑ᶠ m : ℤ, uCoeffTower K L b m • W.smul u m (W.smul v (b : ℤ) w))
        = ∑ᶠ b : ℕ, ∑ᶠ m : ℤ, uCoeffTower K L b m • W.smul u m (W.smul v (b : ℤ) w) from by
      refine (finsum_eq_finsetSum_of_support_subset _ (s := Finset.range Bv) ?_).symm
      intro b hb
      rw [Function.mem_support] at hb
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra hge
      apply hb
      rw [show W.smul v (b : ℤ) w = (0 : 𝒱) from hBv b (by omega)]
      refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
      rw [PreVertexAlgebra.smul_zero_right, smul_zero]]
  -- second: ∑ᶠ b:ℕ G b = ∑ᶠ b:ℤ (if 0≤b then G b.toNat else 0)
  rw [finsum_nat_to_int
      (fun b : ℕ => ∑ᶠ m : ℤ, uCoeffTower K L b m • W.smul u m (W.smul v (b : ℤ) w))
      (fun b : ℤ => ∑ᶠ m : ℤ, (if 0 ≤ b then uCoeffTower K L b.toNat m else 0)
        • W.smul u m (W.smul v b w))
      (fun p hp => by
        refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
        rw [if_neg (by omega), zero_smul])
      (fun j => by
        refine finsum_congr fun m => ?_
        rw [if_pos (by positivity), Int.toNat_natCast])]

/-- The net U-side coefficient (after subtracting RHS) equals the extended `uCoeffTower`. -/
theorem uSideScalar_sub_rhs (K L : ℕ) (b m : ℤ) :
    uSideScalar K L b m - cbz (K : ℤ) (m + 1) * cbz (L : ℤ) (b + 1)
      = if 0 ≤ b then uCoeffTower K L b.toNat m else 0 := by
  rcases lt_or_ge b 0 with hb | hb
  · rw [uSideScalar_neg K L b m hb, if_neg (by omega), sub_self]
  · obtain ⟨β, rfl⟩ : ∃ β : ℕ, b = (β : ℤ) := ⟨b.toNat, by omega⟩
    rw [uSideScalar_split K L β m, if_pos (by positivity), Int.toNat_natCast]
    ring

/-! ## b-support finiteness for the final assembly. -/

/-- For fixed `b`, the `m`-finsum scalar `m ↦ rhsCoeff` has finite support. -/
theorem rhsCoeff_m_fin (K L : ℕ) (b : ℤ) :
    (Function.support (fun m : ℤ => cbz (K : ℤ) (m + 1) * cbz (L : ℤ) (b + 1))).Finite := by
  apply Set.Finite.subset (Set.finite_Icc (-1 : ℤ) ((K : ℤ) - 1))
  intro m hm
  rw [Function.mem_support] at hm
  simp only [Set.mem_Icc]
  constructor
  · by_contra h; exact hm (by rw [cbz_apply_neg (K : ℤ) (by omega), zero_mul])
  · by_contra h; exact hm (by rw [cbz_lt (by positivity) (by omega), zero_mul])

/-- For fixed `b`, the `m`-finsum scalar `m ↦ uCoeffExt` has finite support. -/
theorem uCoeffExt_m_fin (K L : ℕ) (b : ℤ) :
    (Function.support
      (fun m : ℤ => if 0 ≤ b then uCoeffTower K L b.toNat m else 0)).Finite := by
  by_cases hb : 0 ≤ b
  · simp only [if_pos hb]
    apply Set.Finite.subset (Set.finite_Icc (-(b.toNat : ℤ) - 2) ((K : ℤ) - 1))
    intro m hm
    rw [Function.mem_support] at hm
    simp only [Set.mem_Icc]
    constructor
    · by_contra h
      apply hm; rw [uCoeffTower]
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [cbz_apply_neg (K : ℤ) (by have := Finset.mem_range.mp hk; omega), zero_mul]
    · by_contra h
      apply hm; rw [uCoeffTower]
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [cbz_lt (by positivity) (by have := Finset.mem_range.mp hk; omega), zero_mul]
  · simp only [if_neg hb]
    exact Set.finite_empty.subset (by intro m hm; rw [Function.mem_support] at hm; exact absurd rfl hm)

/-- The RHS-term `b ↦ ∑ᶠ m, rhsCoeff • u₍ₘ₎(v₍ᵦ₎w)` has finite support in `b`. -/
theorem rhs_b_fin (W : VertexOperatorAlgebra 𝒱) (K L : ℕ) (u v w : 𝒱) :
    (Function.support (fun b : ℤ =>
      ∑ᶠ m : ℤ, (cbz (K : ℤ) (m + 1) * cbz (L : ℤ) (b + 1))
        • W.smul u m (W.smul v b w))).Finite := by
  apply Set.Finite.subset (Set.finite_Icc (-1 : ℤ) ((L : ℤ) - 1))
  intro b hb
  rw [Function.mem_support] at hb
  simp only [Set.mem_Icc]
  -- nonzero ⟹ cbz L (b+1) ≠ 0 ⟹ 0 ≤ b+1 ≤ L
  have hex : ∃ m : ℤ, (cbz (K : ℤ) (m + 1) * cbz (L : ℤ) (b + 1))
      • W.smul u m (W.smul v b w) ≠ 0 := by
    by_contra hall
    exact hb (finsum_eq_zero_of_forall_eq_zero fun m => not_not.mp (not_exists.mp hall m))
  obtain ⟨m, hm⟩ := hex
  have hcL : cbz (L : ℤ) (b + 1) ≠ 0 := by
    intro h; apply hm; rw [h, mul_zero, zero_smul]
  constructor
  · by_contra h; exact hcL (cbz_apply_neg (L : ℤ) (by omega))
  · by_contra h; exact hcL (cbz_lt (by positivity) (by omega))

/-- The Ufam-term `b ↦ ∑ᶠ m, uCoeffExt • u₍ₘ₎(v₍ᵦ₎w)` has finite support in `b`
(needs `v₍ᵦ₎w = 0` for `b ≥ Nv`). -/
theorem ufam_b_fin (W : VertexOperatorAlgebra 𝒱) (K L : ℕ) (u v w : 𝒱) :
    (Function.support (fun b : ℤ =>
      ∑ᶠ m : ℤ, (if 0 ≤ b then uCoeffTower K L b.toNat m else 0)
        • W.smul u m (W.smul v b w))).Finite := by
  obtain ⟨Nv, hNv⟩ := W.regularity v w
  apply Set.Finite.subset (Set.finite_Icc (0 : ℤ) (Nv - 1))
  intro b hb
  rw [Function.mem_support] at hb
  simp only [Set.mem_Icc]
  have hex : ∃ m : ℤ, (if 0 ≤ b then uCoeffTower K L b.toNat m else 0)
      • W.smul u m (W.smul v b w) ≠ 0 := by
    by_contra hall
    exact hb (finsum_eq_zero_of_forall_eq_zero fun m => not_not.mp (not_exists.mp hall m))
  obtain ⟨m, hm⟩ := hex
  have hb0 : 0 ≤ b := by
    by_contra h; apply hm; rw [if_neg h, zero_smul]
  have hvb : W.smul v b w ≠ 0 := by
    intro h; apply hm; rw [h, PreVertexAlgebra.smul_zero_right, smul_zero]
  have hNvle : Nv ≤ (Nv.toNat : ℤ) := Int.self_le_toNat Nv
  refine ⟨hb0, ?_⟩
  by_contra h
  exact hvb (hNv b (by omega))

/-- **The U-family matches**: `USide = Ufam + u*(v*w)`. -/
theorem USide_eq_Ufam_add_RHS (W : VertexOperatorAlgebra 𝒱) {K L : ℕ} {u v : 𝒱}
    (hu : u ∈ W.grading (K : ℤ)) (hv : v ∈ W.grading (L : ℤ)) (w : 𝒱) {Bv : ℕ}
    (hBv : ∀ b : ℕ, Bv ≤ b → W.smul v (b : ℤ) w = 0) :
    USide W K L u v w = Ufam W K L u v w Bv + zhuMul W u (zhuMul W v w) := by
  rw [USide_eq3, Ufam_eq W K L u v w hBv, RHS_eq W hu hv w]
  -- combine Ufam + RHS into a single double finsum (add at b-level then m-level)
  rw [← finsum_add_distrib (ufam_b_fin W K L u v w) (rhs_b_fin W K L u v w)]
  refine finsum_congr fun b => ?_
  rw [← finsum_add_distrib
      (smul_support_of_scalar_gen _ _ (uCoeffExt_m_fin K L b))
      (smul_support_of_scalar_gen _ _ (rhsCoeff_m_fin K L b))]
  refine finsum_congr fun m => ?_
  rw [← add_smul]
  congr 1
  -- uSideScalar = uCoeffExt + rhsCoeff
  linear_combination uSideScalar_sub_rhs K L b m

/-- **The associator decomposition equality.** -/
theorem assoc_eq (W : VertexOperatorAlgebra 𝒱) {K L : ℕ} {u v : 𝒱}
    (hu : u ∈ W.grading (K : ℤ)) (hv : v ∈ W.grading (L : ℤ)) (w : 𝒱)
    {Bu Bv : ℕ}
    (hBv : ∀ b : ℕ, Bv ≤ b → W.smul v (b : ℤ) w = 0)
    (hBu : ∀ a : ℕ, Bu ≤ a → W.smul u (a : ℤ) w = 0) :
    zhuMul W (zhuMul W u v) w - zhuMul W u (zhuMul W v w)
      = Ufam W K L u v w Bv + Vfam W K L u v w Bu := by
  rw [lhs_split W hu hv w, USide_eq_Ufam_add_RHS W hu hv w hBv,
    ← neg_VSide_eq_Vfam W K L u v w hBu]
  abel

/-- **The associator core (Zhu Thm 2.1.2 crux).** -/
theorem associator_core (W : VertexOperatorAlgebra 𝒱) {K L : ℕ} {u v : 𝒱}
    (hu : u ∈ W.grading (K : ℤ)) (hv : v ∈ W.grading (L : ℤ)) (w : 𝒱) :
    zhuMul W (zhuMul W u v) w - zhuMul W u (zhuMul W v w) ∈ O W := by
  obtain ⟨Nv, hNv⟩ := W.regularity v w
  obtain ⟨Nu, hNu⟩ := W.regularity u w
  refine assoc_eq W hu hv w (Bu := Nu.toNat) (Bv := Nv.toNat)
    (fun b hb => hNv (b : ℤ) (by omega)) (fun a ha => hNu (a : ℤ) (by omega)) ▸ ?_
  exact Submodule.add_mem _ (Ufam_mem_O W hu v w _) (Vfam_mem_O W hv u w _)

end VOA
