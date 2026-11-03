/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnDescent20

/-!
# `RightCircTowerEq_holds`: the circle predicate from the two proven scalar cores.

Wiring the depth-`n` U-core (`UgammaModeColl_eq_towerCoeff`, `ZhuVermaAnDescent19`) and V-core
(`VgammaModeColl_eq_towerCoeff`, `ZhuVermaAnDescent20`) through `RightCircTowerEq_of_sides`
(`ZhuVermaAnDescent10`): the per-`(γ,μ)` scalar matchings `HU`/`HV` are discharged by the two cores,
giving `RightCircTowerEq W n M P c d a` for ALL homogeneous `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, `a ∈ 𝒱_K` —
i.e. the `RightDescends.on_mem` / `AnBimoduleInputs.circTow` field, unconditional.

## Key bookkeeping
* `wU_vanish`/`wV_vanish` — the core weights vanish past their natural depth (`cbz(k,δ)=0` for `k<δ`),
  so `towerCoeff_pad` reconciles the two cores' different γ-dependent depths to one common `Δ`.
* common base-mode window `γ₀ = -(2n+1)`, `Γ` covering the regularity bound of both `W.smul d · a`
  and `W.smul c · a`; `finsum_window` collapses the outer `∑ᶠ γ` to the finite range.
* `USideR_eq_UfamOn` / `VSideR_eq_neg_VfamOn` — the two side collapses (per-`(γ,μ)` core matching),
  fed to `RightCircTowerEq_of_sides`.

## References
* Gannon §5.3.2, Thm 5.3.4; Zhu Thm 2.1.1/2.1.2; Frenkel–Zhu Lemma 2.1.2; Dong–Li–Mason.
-/
open scoped BigOperators
open Finset

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators
open Classical

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Helper 1: the U-weight `wU P n γ` vanishes past its tower depth. -/

/-- `wtJ P n j γ ν = 0` once `(2n+2+γ).toNat ≤ ν`: every `k` in the `range (2n+2+γ).toNat` sum has
`k < (2n+2+γ).toNat ≤ ν`, so `cbz (k:ℤ) (ν:ℤ) = 0`. -/
theorem wtJ_vanish (P n j : ℕ) (γ : ℤ) {ν : ℕ} (hν : (2 * n + 2 + γ).toNat ≤ ν) :
    wtJ P n j γ ν = 0 := by
  rw [wtJ]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hk' : k < (2 * n + 2 + γ).toNat := Finset.mem_range.mp hk
  rw [cbz_lt (by positivity) (by exact_mod_cast (by omega : k < ν)), mul_zero, zero_mul]

/-- `wU P n γ δ = 0` once `(2n+2+γ).toNat ≤ δ`. -/
theorem wU_vanish (P n : ℕ) (γ : ℤ) {δ : ℕ} (hδ : (2 * n + 2 + γ).toNat ≤ δ) :
    wU P n γ δ = 0 := by
  rw [wU]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [wtJ_vanish P n j γ hδ, mul_zero]

/-! ## Helper 2: the V-weight `wV M n γ` vanishes past its tower depth. -/

/-- `vtJ M n j γ ν = 0` once `(2n+2+max γ 0).toNat ≤ ν`: every `kp` in `range (2n+2+γ).toNat`
has `kp < (2n+2+γ).toNat ≤ (2n+2+max γ 0).toNat ≤ ν`, so `cbz (kp:ℤ) (ν:ℤ) = 0`. -/
theorem vtJ_vanish (M n j : ℕ) (γ : ℤ) {ν : ℕ} (hν : (2 * n + 2 + max γ 0).toNat ≤ ν) :
    vtJ M n j γ ν = 0 := by
  rw [vtJ]
  refine Finset.sum_eq_zero fun kp hkp => ?_
  have hkp' : kp < (2 * n + 2 + γ).toNat := Finset.mem_range.mp hkp
  have hmono : (2 * n + 2 + γ).toNat ≤ (2 * n + 2 + max γ 0).toNat := by
    apply Int.toNat_le_toNat; omega
  rw [cbz_lt (by positivity) (by exact_mod_cast (by omega : kp < ν)), mul_zero, zero_mul]

/-- `wV M n γ δ = 0` once `(2n+2+max γ 0).toNat ≤ δ`. -/
theorem wV_vanish (M n : ℕ) (γ : ℤ) {δ : ℕ} (hδ : (2 * n + 2 + max γ 0).toNat ≤ δ) :
    wV M n γ δ = 0 := by
  rw [wV]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [vtJ_vanish M n j γ hδ, mul_zero]

/-! ## Helper 3: `towerCoeff` is unchanged by padding a weight that vanishes past `Δ₀`. -/

/-- If `wt δ = 0` for all `δ ≥ Δ₀` and `Δ₀ ≤ Δ`, then `towerCoeff M n wt Δ μ = towerCoeff M n wt Δ₀ μ`. -/
theorem towerCoeff_pad (M n : ℕ) (wt : ℕ → ℂ) (Δ₀ Δ : ℕ) (μ : ℤ)
    (hle : Δ₀ ≤ Δ) (hvan : ∀ δ : ℕ, Δ₀ ≤ δ → wt δ = 0) :
    towerCoeff M n wt Δ μ = towerCoeff M n wt Δ₀ μ := by
  rw [towerCoeff, towerCoeff]
  symm
  refine Finset.sum_subset (Finset.range_subset_range.mpr hle) ?_
  intro δ _ hδ
  rw [hvan δ (by rw [Finset.mem_range] at hδ; omega), zero_mul]

/-! ## Helper 4: `towerCoeff` is linear in the weight (negation). -/

theorem towerCoeff_neg (M n : ℕ) (wt : ℕ → ℂ) (Δ : ℕ) (μ : ℤ) :
    towerCoeff M n (fun δ => -(wt δ)) Δ μ = -towerCoeff M n wt Δ μ := by
  rw [towerCoeff, towerCoeff, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun δ _ => by ring

/-! ## Helper 5: the `∑ᶠ γ : ℤ → ∑ g ∈ range Γ` bridge over a window `[γ₀, γ₀+Γ)`. -/

/-- If a family `F : ℤ → 𝒱` is supported inside the window `[γ₀, γ₀+Γ)`, then its `∑ᶠ` over `ℤ`
equals the finite range sum `∑ g ∈ range Γ, F (γ₀+g)`. -/
theorem finsum_window (F : ℤ → 𝒱) (γ₀ : ℤ) (Γ : ℕ)
    (hsupp : ∀ γ : ℤ, F γ ≠ 0 → γ₀ ≤ γ ∧ γ < γ₀ + Γ) :
    (∑ᶠ γ : ℤ, F γ) = ∑ g ∈ Finset.range Γ, F (γ₀ + (g : ℤ)) := by
  set emb : ℕ ↪ ℤ := ⟨fun g => γ₀ + (g : ℤ), fun a b h => by simpa using h⟩ with hemb
  rw [finsum_eq_sum_of_support_subset F (s := (Finset.range Γ).map emb) ?_]
  · rw [Finset.sum_map]; rfl
  · intro γ hγ
    rw [Function.mem_support] at hγ
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Finset.mem_range, hemb,
      Function.Embedding.coeFn_mk]
    obtain ⟨hlb, hub⟩ := hsupp γ hγ
    exact ⟨(γ - γ₀).toNat, by omega, by omega⟩

/-! ## The grade witness `G` and its (unrestricted) `hG`. -/

/-- The canonical grade witness `G i = (M+P-(i-2n-2)-1).toNat`. -/
noncomputable def Gwit (M P n : ℕ) (i : ℕ) : ℕ :=
  ((M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1).toNat

/-- The unrestricted grade-witness obligation (consumed by the cores). -/
theorem Gwit_spec (M P n : ℕ) :
    ∀ i : ℕ, 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 →
      (Gwit M P n i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 := by
  intro i hi
  rw [Gwit, Int.toNat_of_nonneg hi]

/-! ## The two side equalities (with a common window `γ₀, Γ` and depth `Δ`). -/

/-- **U-side collapse.**  For the canonical witness, `USideR` equals the `UfamOn` tower family with
weights `wU P n`, over ANY window `[γ₀, γ₀+Γ)` that contains the regularity-bounded contributing
base-modes and ANY depth `Δ` past every contributing tower height. -/
theorem USideR_eq_UfamOn (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d a : 𝒱)
    (γ₀ : ℤ) (Γ Δ : ℕ) {Nd : ℤ} (hNd : ∀ γ : ℤ, Nd ≤ γ → W.smul d γ a = 0)
    (hγ₀ : γ₀ ≤ -(2 * (n : ℤ) + 1)) (hΓ : Nd ≤ γ₀ + Γ)
    (hΔ : ∀ γ : ℤ, γ₀ ≤ γ → γ < γ₀ + Γ → (2 * n + 2 + γ).toNat ≤ Δ) :
    USideR W M P n c d a (Gwit M P n) = UfamOn W M n c d a (wU P n) γ₀ Γ Δ := by
  rw [USideR_eq_gammaModeFinsum, UfamOn_eq_finsum]
  rw [finsum_window
      (fun γ : ℤ => ∑ᶠ μ : ℤ, UgammaModeColl M P n (Gwit M P n) γ μ • W.smul c μ (W.smul d γ a))
      γ₀ Γ ?_]
  · refine Finset.sum_congr rfl fun g hg => ?_
    refine finsum_congr fun μ => ?_
    congr 1
    -- per-(γ,μ): collected scalar = padded tower coefficient.
    rw [UgammaModeColl_eq_towerCoeff M P n (Gwit M P n) (Gwit_spec M P n) (γ₀ + (g : ℤ)) μ]
    rw [towerCoeff_pad M n (wU P n (γ₀ + (g : ℤ))) (2 * n + 2 + (γ₀ + (g : ℤ))).toNat Δ μ
        (hΔ (γ₀ + (g : ℤ)) (by omega) (by have := Finset.mem_range.mp hg; omega))
        (fun δ hδ => wU_vanish P n (γ₀ + (g : ℤ)) hδ)]
  · -- support window of the U-side body.
    intro γ hγ
    refine ⟨?_, ?_⟩
    · by_contra h
      apply hγ
      refine finsum_eq_zero_of_forall_eq_zero fun μ => ?_
      rw [UgammaModeColl_zero_below M P n (Gwit M P n) γ μ (by omega), zero_smul]
    · by_contra h
      apply hγ
      exact USide_gammaBody_zero_above W M P n c d a (Gwit M P n) hNd γ (by omega)

/-- **V-side collapse.**  `VSideR` equals the *negated* `VfamOn` tower family with weights
`fun γ => -(wV M n γ)`, over the same window/depth (the V family is supported on `γ ≥ 0`). -/
theorem VSideR_eq_neg_VfamOn (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d a : 𝒱)
    (γ₀ : ℤ) (Γ Δ : ℕ) {Nc : ℤ} (hNc : ∀ γ : ℤ, Nc ≤ γ → W.smul c γ a = 0)
    (hγ₀ : γ₀ ≤ 0) (hΓ : Nc ≤ γ₀ + Γ)
    (hΔ : ∀ γ : ℤ, γ₀ ≤ γ → γ < γ₀ + Γ → (2 * n + 2 + max γ 0).toNat ≤ Δ) :
    VSideR W M P n c d a (Gwit M P n)
      = -VfamOn W P n c d a (fun γ => fun δ => -(wV M n γ δ)) γ₀ Γ Δ := by
  rw [VSideR_eq_gammaModeFinsum, VfamOn_eq_finsum, ← Finset.sum_neg_distrib]
  rw [finsum_window
      (fun γ : ℤ => ∑ᶠ μ : ℤ, VgammaModeColl M P n (Gwit M P n) γ μ • W.smul d μ (W.smul c γ a))
      γ₀ Γ ?_]
  · refine Finset.sum_congr rfl fun g hg => ?_
    rw [← finsum_neg_distrib]
    refine finsum_congr fun μ => ?_
    rw [← neg_smul]
    congr 1
    -- per-(γ,μ): collected scalar = -(padded tower coefficient with weight `-wV`).
    rw [VgammaModeColl_eq_towerCoeff M P n (Gwit M P n) (Gwit_spec M P n) (γ₀ + (g : ℤ)) μ,
      towerCoeff_neg, neg_neg]
    rw [towerCoeff_pad P n (wV M n (γ₀ + (g : ℤ))) (2 * n + 2 + max (γ₀ + (g : ℤ)) 0).toNat Δ μ
        (hΔ (γ₀ + (g : ℤ)) (by omega) (by have := Finset.mem_range.mp hg; omega))
        (fun δ hδ => wV_vanish M n (γ₀ + (g : ℤ)) hδ)]
  · -- support window of the V-side body.
    intro γ hγ
    refine ⟨?_, ?_⟩
    · by_contra h
      apply hγ
      refine finsum_eq_zero_of_forall_eq_zero fun μ => ?_
      rw [VgammaModeColl_zero_below M P n (Gwit M P n) γ μ (by omega), zero_smul]
    · by_contra h
      apply hγ
      exact VSide_gammaBody_zero_above W M P n c d a (Gwit M P n) hNc γ (by omega)

/-! ## The assembled `RightCircTowerEq_holds`. -/

/-- **`RightCircTowerEq_holds`**.  For every grade `M, P, K` and homogeneous
`c ∈ 𝒱_M`, `d ∈ 𝒱_P`, `a ∈ 𝒱_K`, the right-product tower decomposition `RightCircTowerEq W n M P c d a`
holds.  Assembled from the master split (`RightCircTowerEq_of_sides`, `ZhuVermaAnDescent10`) and the two
PROVEN scalar cores `UgammaModeColl_eq_towerCoeff`/`VgammaModeColl_eq_towerCoeff`
(`ZhuVermaAnDescent19`/`20`) via the depth-padding + finite-base-mode-window bookkeeping above.  The
`a ∈ 𝒱_K` hypothesis is unused (it matches the shape `rightDescends_holds`'s `Htow` consumes). -/
theorem RightCircTowerEq_holds (W : VertexOperatorAlgebra 𝒱) (n : ℕ) :
    ∀ (M P K : ℕ) {c d a : 𝒱}, c ∈ W.grading (M : ℤ) → d ∈ W.grading (P : ℤ) →
      a ∈ W.grading (K : ℤ) → RightCircTowerEq W n M P c d a := by
  intro M P K c d a hc hd _ha
  obtain ⟨Nd, hNd⟩ := W.regularity d a
  obtain ⟨Nc, hNc⟩ := W.regularity c a
  set γ₀ : ℤ := -(2 * (n : ℤ) + 1) with hγ₀
  set Γ : ℕ := (max Nd Nc - γ₀).toNat with hΓdef
  set Δ : ℕ := (2 * (n : ℤ) + 2 + max (γ₀ + (Γ : ℤ)) 0).toNat with hΔdef
  -- `max Nd Nc ≤ γ₀ + Γ` (`Int.self_le_toNat`), so the window contains both regularity windows.
  have hmaxle : max Nd Nc ≤ γ₀ + (Γ : ℤ) := by
    have := Int.self_le_toNat (max Nd Nc - γ₀)
    rw [hΓdef]; omega
  have hΓU : Nd ≤ γ₀ + (Γ : ℤ) := le_trans (le_max_left _ _) hmaxle
  have hΓV : Nc ≤ γ₀ + (Γ : ℤ) := le_trans (le_max_right _ _) hmaxle
  refine RightCircTowerEq_of_sides W n hc hd a (Gwit M P n)
    (fun i _ => Gwit_spec M P n i) (wU P n) (fun γ => fun δ => -(wV M n γ δ)) γ₀ Γ Δ ?_ ?_
  · -- U-side.
    refine USideR_eq_UfamOn W M P n c d a γ₀ Γ Δ hNd (le_refl _) hΓU ?_
    intro γ _ hub
    rw [hΔdef]
    refine Int.toNat_le_toNat ?_
    have : γ ≤ γ₀ + (Γ : ℤ) := by omega
    omega
  · -- V-side.
    refine VSideR_eq_neg_VfamOn W M P n c d a γ₀ Γ Δ hNc (by rw [hγ₀]; omega) hΓV ?_
    intro γ _ hub
    rw [hΔdef]
    refine Int.toNat_le_toNat ?_
    have : γ ≤ γ₀ + (Γ : ℤ) := by omega
    omega

end VOA
