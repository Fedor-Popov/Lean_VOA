/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.Twisted
import VOA.Modules.WeakModule

/-!
# The `+`-part of an order-two twisted module is an ordinary `𝒱^g`-module  (Moonshine step M8a, part 2)

Let `T` be a `g`-twisted `𝒱`-module of order `N = 2` (`TwistedModule g 2 M`), and let `θ_M` be an
involution of `M` lifting `g`: `Y_M(gu)₍k/2₎ = θ_M ∘ Y_M(u)₍k/2₎ ∘ θ_M`, preserving the
`L₀`-weight spaces (`ThetaLift`).  Then `M⁺ := ker(θ_M − 1)` is an **ordinary module**
(`OrdVModule`) for the fixed-point VOA `𝒱^⟨g⟩ = orbifoldVOA (zpowers g)`, with

  `Y_{M⁺}(u)₍ₙ₎ := Y_M(u)₍2n/2₎ = T.YM u (2n)`     (`mode_plusModule`).

* For `u ∈ 𝒱^⟨g⟩` (eigenspace `j = 0`) the support condition kills the odd fractional modes
  (`YM_odd_eq_zero`), so nothing is lost in passing to the integral modes.
* The modes of `u ∈ 𝒱^⟨g⟩` commute with `θ_M`, hence preserve `M⁺` (`YM_mem_plusSub`).
* The Jacobi identity of `M⁺` is the twisted Jacobi identity at `N = 2`, `j = 0`, indices
  `k = 2m`, `m = 2n` (`C(2m/2, i) = C(m, i)`, the `ℕ`-indexed right side re-indexed over `ℤ`).
* The grading is `M⁺_α := M⁺ ∩ M_α` (`plusWeight`); it is internal because `θ_M` preserves each
  `M_α` (`plusWeight_isInternal`).

## Status
All declarations `sorry`-free.  `plusModule` is conditional only on its explicit data
(`T`, and a `ThetaLift` of `g` to `M`); for the Leech twisted module both are constructed
(`TwistedPlus.lean`).
-/

namespace VOA

open Module (End)
open scoped BigOperators

universe u

namespace TwistedPlus

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {g : Aut W} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **A lift of `g` to an order-two twisted module**: an involution of `M` conjugating
`Y_M(u)` into `Y_M(gu)` and preserving the `L₀`-weight spaces. -/
structure ThetaLift (T : TwistedModule g 2 M) where
  /-- The involution `θ_M`. -/
  op : End ℂ M
  op_op : ∀ x, op (op x) = x
  conj : ∀ (u : 𝒱) (k : ℤ), T.YM (g u) k = op ∘ₗ T.YM u k ∘ₗ op
  map_weight : ∀ (α : ℂ) (x : M), x ∈ T.weight α → op x ∈ T.weight α

variable {T : TwistedModule g 2 M} (θ : ThetaLift T)

/-- The `+`-part `M⁺ = ker(θ_M − 1)`. -/
def plusSub : Submodule ℂ M := LinearMap.ker (θ.op - LinearMap.id)

theorem mem_plusSub {x : M} : x ∈ plusSub θ ↔ θ.op x = x := by
  simp [plusSub, sub_eq_zero]

/-- The fixed-point VOA `𝒱^⟨g⟩`. -/
noncomputable abbrev fixedVOA (g : Aut W) :
    VertexOperatorAlgebra (orbifold (Subgroup.zpowers g)).carrier :=
  orbifoldVOA (Subgroup.zpowers g)

theorem fixed_of_mem {u : 𝒱} (hu : u ∈ (orbifold (Subgroup.zpowers g)).carrier) : g u = u :=
  hu g (Subgroup.mem_zpowers g)

/-- A `g`-fixed state lies in the eigenspace `j = 0`. -/
theorem mem_twistedEigenspace_zero {u : 𝒱} (hu : g u = u) : u ∈ g.twistedEigenspace 2 0 := by
  rw [Aut.twistedEigenspace, Module.End.mem_eigenspace_iff]
  simp only [Nat.cast_zero, mul_zero, neg_zero, zero_div, Complex.exp_zero, one_smul]
  exact hu

/-- The odd fractional modes of a `g`-fixed state vanish. -/
theorem YM_odd_eq_zero {u : 𝒱} (hu : g u = u) (n : ℤ) : T.YM u (2 * n + 1) = 0 :=
  T.support 0 u (mem_twistedEigenspace_zero hu) _ (by push_cast; omega)

/-- The modes of a `g`-fixed state commute with `θ_M`. -/
theorem op_YM {u : 𝒱} (hu : g u = u) (k : ℤ) (x : M) :
    θ.op (T.YM u k x) = T.YM u k (θ.op x) := by
  have h := θ.conj u k
  rw [hu] at h
  conv_lhs => rw [h]
  simp only [LinearMap.comp_apply, θ.op_op]

theorem YM_mem_plusSub {u : 𝒱} (hu : g u = u) (k : ℤ) {x : M} (hx : x ∈ plusSub θ) :
    T.YM u k x ∈ plusSub θ := by
  rw [mem_plusSub] at hx ⊢
  rw [op_YM θ hu, hx]

/-- The vertex operator of `M⁺`: `Y_{M⁺}(u)` has `n`-th mode `T.YM u (2n)`. -/
noncomputable def YMp :
    (orbifold (Subgroup.zpowers g)).carrier →ₗ[ℂ] FormalDist (End ℂ (plusSub θ)) where
  toFun u := fun m => (T.YM u.1 (2 * (-m - 1))).restrict
    (fun x hx => YM_mem_plusSub θ (fixed_of_mem u.2) _ hx)
  map_add' u v := by
    funext m
    ext x
    simp only [Submodule.coe_add, map_add, LinearMap.restrict_apply]
    rfl
  map_smul' c u := by
    funext m
    ext x
    simp only [Submodule.coe_smul, map_smul, LinearMap.restrict_apply, RingHom.id_apply]
    rfl

@[simp] theorem YMp_apply_coe (u : (orbifold (Subgroup.zpowers g)).carrier) (m : ℤ)
    (x : plusSub θ) : ((YMp θ u m x : plusSub θ) : M) = T.YM u.1 (2 * (-m - 1)) x := rfl

/-- The `n`-th mode of `Y_{M⁺}(u)` is the fractional mode `u₍2n/2₎ = T.YM u (2n)`. -/
@[simp] theorem mode_YMp_coe (u : (orbifold (Subgroup.zpowers g)).carrier) (n : ℤ)
    (x : plusSub θ) : ((mode (YMp θ u) n x : plusSub θ) : M) = T.YM u.1 (2 * n) x := by
  rw [mode_apply, YMp_apply_coe, show 2 * (-(-n - 1) - 1) = 2 * n by ring]

theorem coe_finsum {ι : Type*} (f : ι → plusSub θ) :
    ((∑ᶠ i, f i : plusSub θ) : M) = ∑ᶠ i, (f i : M) :=
  AddMonoidHom.map_finsum_of_injective (plusSub θ).subtype.toAddMonoidHom Subtype.coe_injective f

/-- The weak-module structure of `M⁺` over `𝒱^⟨g⟩`. -/
noncomputable def plusWeakModule : WeakModule (fixedVOA g) (plusSub θ) where
  YM := YMp θ
  vacuum_YM := by
    funext m
    ext x
    rw [YMp_apply_coe]
    change T.YM W.vacuum (2 * (-m - 1)) x = _
    rw [T.vacuum_YM, FormalDist.one_apply]
    by_cases hm : m = 0
    · rw [if_pos (by subst hm; norm_num), if_pos hm]; rfl
    · rw [if_neg (by push_cast; omega), if_neg hm]; rfl
  truncation u x := by
    obtain ⟨K, hK⟩ := T.truncation u.1 x.1
    exact ⟨K.natAbs, fun n hn => Subtype.ext (by
      rw [mode_YMp_coe, hK _ (by omega)]; rfl)⟩
  jacobi u v x ℓ m n := by
    apply Subtype.ext
    rw [coe_finsum, coe_finsum]
    have hJ := T.jacobi 0 u.1 (mem_twistedEigenspace_zero (fixed_of_mem u.2)) v.1 x.1 ℓ
      (2 * m) (2 * n) (by omega)
    have hL : (∑ᶠ i : ℤ, (((negOnePow i * cbz ℓ i) •
        (mode (YMp θ u) (ℓ + m - i) (mode (YMp θ v) (n + i) x)
          - negOnePow ℓ • mode (YMp θ v) (ℓ + n - i) (mode (YMp θ u) (m + i) x)) :
          plusSub θ) : M))
        = ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
          (T.YM u.1 (ℓ * ((2 : ℕ) : ℤ) + 2 * m - i * ((2 : ℕ) : ℤ))
              (T.YM v.1 (2 * n + i * ((2 : ℕ) : ℤ)) x.1)
            - negOnePow ℓ • T.YM v.1 (ℓ * ((2 : ℕ) : ℤ) + 2 * n - i * ((2 : ℕ) : ℤ))
              (T.YM u.1 (2 * m + i * ((2 : ℕ) : ℤ)) x.1)) := by
      refine finsum_congr fun i => ?_
      simp only [Submodule.coe_smul, Submodule.coe_sub, mode_YMp_coe]
      push_cast
      ring_nf
    have hR : (∑ᶠ i : ℤ, ((cbz m i • mode (YMp θ ((fixedVOA g).smul u (ℓ + i) v)) (m + n - i) x :
          plusSub θ) : M))
        = ∑ᶠ i : ℕ, cbinom (((2 * m : ℤ) : ℂ) / ((2 : ℕ) : ℂ)) i •
          T.YM (W.smul u.1 (ℓ + i) v.1) (2 * m + 2 * n - i * ((2 : ℕ) : ℤ)) x.1 := by
      rw [← finsum_mem_univ,
        finsum_mem_inter_support_eq' _ Set.univ (Set.range (Nat.cast : ℕ → ℤ)) ?_,
        finsum_mem_range Nat.cast_injective]
      · refine finsum_congr fun i => ?_
        rw [Submodule.coe_smul, mode_YMp_coe, cbz_apply_nonneg _ (by positivity),
          Int.toNat_natCast,
          show (((2 * m : ℤ) : ℂ) / ((2 : ℕ) : ℂ)) = (m : ℂ) by push_cast; ring,
          show 2 * (m + n - (i : ℤ)) = 2 * m + 2 * n - (i : ℤ) * ((2 : ℕ) : ℤ) by push_cast; ring]
        rfl
      · intro i hi
        simp only [Set.mem_univ, Set.mem_range, true_iff]
        rw [Function.mem_support] at hi
        by_cases h0 : 0 ≤ i
        · exact ⟨i.toNat, by omega⟩
        · exact absurd (by rw [cbz_apply_neg _ (not_le.mp h0), zero_smul]; rfl) hi
    rw [hL, hR]
    exact hJ

/-! ## The grading -/

/-- The weight spaces `M⁺_α = M⁺ ∩ M_α`. -/
def plusWeight (α : ℂ) : Submodule ℂ (plusSub θ) := (T.weight α).comap (plusSub θ).subtype

theorem mem_plusWeight {α : ℂ} {x : plusSub θ} : x ∈ plusWeight θ α ↔ (x : M) ∈ T.weight α :=
  Iff.rfl

theorem map_plusWeight (α : ℂ) :
    (plusWeight θ α).map (plusSub θ).subtype = plusSub θ ⊓ T.weight α := by
  rw [plusWeight, Submodule.map_comap_subtype]

theorem plusWeight_iSupIndep : iSupIndep (plusWeight θ) := by
  have hW := T.isInternal.submodule_iSupIndep
  refine iSupIndep_def.mpr (fun i => ?_)
  rw [Submodule.disjoint_def]
  intro x hxi hxrest
  have h1 : (x : M) ∈ T.weight i := hxi
  have h2 : (x : M) ∈ ⨆ (j) (_ : j ≠ i), T.weight j := by
    have hmap : Submodule.map (plusSub θ).subtype (⨆ (j) (_ : j ≠ i), plusWeight θ j)
        ≤ ⨆ (j) (_ : j ≠ i), T.weight j := by
      rw [Submodule.map_iSup]
      refine iSup_mono (fun j => ?_)
      rw [Submodule.map_iSup]
      refine iSup_mono (fun _ => ?_)
      exact Submodule.map_comap_le _ _
    exact hmap ⟨x, hxrest, rfl⟩
  have := (iSupIndep_def.mp hW i)
  rw [Submodule.disjoint_def] at this
  exact Subtype.ext (this _ h1 h2)

theorem plusWeight_iSup : ⨆ α, plusWeight θ α = ⊤ := by
  classical
  rw [eq_top_iff]
  intro x _
  have hx : θ.op x = x := (mem_plusSub θ).mp x.2
  letI : DirectSum.Decomposition T.weight := T.isInternal.chooseDecomposition
  have hdec := DirectSum.sum_support_decompose T.weight (x : M)
  set s := (DirectSum.decompose T.weight (x : M)).support
  let d : ℂ → M := fun α => (DirectSum.decompose T.weight (x : M) α : M)
  have hd : ∀ α, d α ∈ T.weight α := fun α => (DirectSum.decompose T.weight (x : M) α).2
  let y : ℂ → M := fun α => (1 / 2 : ℂ) • (d α + θ.op (d α))
  have hyw : ∀ α, y α ∈ T.weight α := fun α =>
    Submodule.smul_mem _ _ (Submodule.add_mem _ (hd α) (θ.map_weight α _ (hd α)))
  have hyp : ∀ α, y α ∈ plusSub θ := fun α => by
    rw [mem_plusSub]
    simp only [y, map_smul, map_add, θ.op_op, add_comm]
  have hsum : x = ∑ α ∈ s, (⟨y α, hyp α⟩ : plusSub θ) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [y, ← Finset.smul_sum, Finset.sum_add_distrib, ← map_sum]
    change (x : M) = (1 / 2 : ℂ) • (∑ α ∈ s, d α + θ.op (∑ α ∈ s, d α))
    have : ∑ α ∈ s, d α = (x : M) := hdec
    rw [this, hx, ← two_smul ℂ (x : M), smul_smul]
    norm_num
  rw [hsum]
  exact Submodule.sum_mem _ fun α _ => Submodule.mem_iSup_of_mem α (hyw α)

theorem plusWeight_isInternal : DirectSum.IsInternal (plusWeight θ) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  exact ⟨plusWeight_iSupIndep θ, plusWeight_iSup θ⟩

instance plusWeight_finiteDimensional (α : ℂ) : FiniteDimensional ℂ (plusWeight θ α) := by
  haveI := T.finrank α
  refine Module.Finite.of_injective (LinearMap.codRestrict (T.weight α)
    ((plusSub θ).subtype.comp (plusWeight θ α).subtype) (fun x => x.2)) ?_
  intro x y hxy
  have := congrArg Subtype.val hxy
  simp only [LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply] at this
  exact Subtype.ext (Subtype.ext this)

/-- **`M⁺` is an ordinary `𝒱^⟨g⟩`-module** (`OrdVModule`), with `Y_{M⁺}(u)₍ₙ₎ = T.YM u (2n)`
and `M⁺_α = M⁺ ∩ M_α`. -/
noncomputable def plusModule : OrdVModule (fixedVOA g) (plusSub θ) where
  toWeakModule := plusWeakModule θ
  weight := plusWeight θ
  isInternal := plusWeight_isInternal θ
  L0_weight α x hx := by
    apply Subtype.ext
    change ((mode (YMp θ (fixedVOA g).conformalVector) 1 x : plusSub θ) : M) = _
    rw [mode_YMp_coe, Submodule.coe_smul]
    change T.YM W.conformalVector ((2 : ℕ) : ℤ) x = α • (x : M)
    exact T.L0_weight α x hx
  finrank := plusWeight_finiteDimensional θ
  boundedBelow := by
    obtain ⟨B, hB⟩ := T.boundedBelow
    refine ⟨B, fun α hα => hB α fun h => hα ?_⟩
    rw [plusWeight, h, Submodule.comap_bot, Submodule.ker_subtype]

@[simp] theorem plusModule_weight (α : ℂ) : (plusModule θ).weight α = plusWeight θ α := rfl

/-- The modes of `M⁺`: `u₍ₙ₎ x = T.YM u (2n) x`. -/
theorem mode_plusModule (u : (orbifold (Subgroup.zpowers g)).carrier) (n : ℤ) (x : plusSub θ) :
    ((mode ((plusModule θ).YM u) n x : plusSub θ) : M) = T.YM u.1 (2 * n) x :=
  mode_YMp_coe θ u n x

end TwistedPlus

end VOA
