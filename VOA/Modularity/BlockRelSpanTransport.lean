/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.BlockRelSpanE
import Mathlib.RingTheory.Finiteness.Nakayama

/-!
# Residual (a): transporting Zhu's count from the cusp into `ℍ`

`Modularity.ZhuCount` proves Zhu Thm 5.3.3 **at the cusp**:
`dim (𝒱 ⧸ blockRelSpanAtCusp 𝒱) = dim A(𝒱)/[A(𝒱),A(𝒱)] ≤ #Φ(𝒱)`.  The remaining step is to move
that bound to a point `z₀ ∈ ℍ`, where the block space actually lives.

`Modularity.BlockRelSpanE` supplies Zhu Lemma 4.4.1 / DLM Lemma 5.2: the relation module is
finitely generated over `E46 = ℂ[E₄,E₆]`.  This file runs the specialization.

## The argument — no fibre tensor products

A natural plan would ask for two fibre identifications
`(𝒱E ⧸ blockRelSpanE) ⊗_{E46, ev} ℂ ≃ 𝒱 ⧸ blockRelSpan …`.  They are **not needed**.  What is
needed is only a `ℂ`-linear *evaluation* `blockEvalAt z₀ : E46 ⊗[ℂ] 𝒱 →ₗ[ℂ] 𝒱`, `f ⊗ v ↦ f(z₀) • v`,
which is `TensorProduct.lift` of an evident bilinear map and is semilinear along `evAt z₀`.  Then:

1. `blockEvalAt z₀` carries `blockRelSpanE 𝒱` into `blockRelSpan 𝒱 z₀` and `span_{E46}(ιE '' T)` into
   `span_ℂ T` — because `evAt z₀ (coefE m) = (2(m+2)−1)·G_{2(m+2)}(z₀)` **on the nose**.
2. At the cusp the two relation families differ by scalars in `𝔪 = ker evInfty`
   (`evInfty_zhuGC`), so a cusp-spanning family `T` gives `𝒱E = N + 𝔪·𝒱E` where
   `N = span_{E46}(ιE '' T) ⊔ blockRelSpanE 𝒱`.
3. **Nakayama, FG form** (`Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`) yields
   `r ∈ E46` with `r − 1 ∈ 𝔪` and `r · (𝒱E ⧸ N) = 0`.
4. `evInfty r = 1`, so `r → 1` at the cusp (`tendsto_of_mem_E46`) and some `z₀ ∈ ℍ` has
   `r(z₀) ≠ 0`.  Applying `blockEvalAt z₀` to `r • ιE v ∈ N` gives `r(z₀) • v ∈ span_ℂ T ⊔ blockRelSpan z₀`,
   and `r(z₀)` is invertible.

**No localization, no `IsLocalRing`, no spreading out, no upper semicontinuity of fibre
dimension** (which is absent from Mathlib), **no Noetherianity of `E46`, and no `E46 ≅ ℂ[X,Y]`**
(also absent from Mathlib, and a theory-sized detour).

## Main results

* `blockEvalAt`, `evalAt_ιE`, `evalAt_smul` — the semilinear specialization map;
* `evalAt_mem_blockRelSpan`, `evalAt_mem_span_image`;
* `ιE_mem_sup_ker_smul_of_mem_blockRelSpanAtCusp` — the cusp comparison;
* `exists_interior_span_sup_blockRelSpan_of_cusp` (the transport).

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  Carried: `VacuumGradeZero`, `C2Cofinite`.
-/

namespace VOA

open scoped BigOperators TensorProduct
open ModularForm UpperHalfPlane Filter Module
open scoped Topology

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The specialization map -/

/-- **Evaluate the coefficient at `z₀`**: the `ℂ`-linear map `f ⊗ v ↦ f(z₀) • v`. -/
noncomputable def blockEvalAt (z₀ : UpperHalfPlane) : 𝒱E 𝒱 →ₗ[ℂ] 𝒱 :=
  TensorProduct.lift
    ((LinearMap.toSpanSingleton ℂ (𝒱 →ₗ[ℂ] 𝒱) LinearMap.id).comp (evAt z₀).toLinearMap)

@[simp] theorem evalAt_tmul (z₀ : UpperHalfPlane) (f : ↥E46) (v : 𝒱) :
    blockEvalAt z₀ (f ⊗ₜ[ℂ] v) = (evAt z₀ f) • v := rfl

@[simp] theorem evalAt_ιE (z₀ : UpperHalfPlane) (v : 𝒱) :
    blockEvalAt z₀ ((ιE v : 𝒱E 𝒱)) = v := by
  rw [ιE_apply, evalAt_tmul]
  show (1 : ℂ) • v = v
  rw [one_smul]

/-- `blockEvalAt z₀` is semilinear along the `ℂ`-point `evAt z₀`. -/
theorem evalAt_smul (z₀ : UpperHalfPlane) (a : ↥E46) (x : 𝒱E 𝒱) :
    blockEvalAt z₀ (a • x) = (evAt z₀ a) • blockEvalAt z₀ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f v =>
      have hsm : a • (f ⊗ₜ[ℂ] v) = (a * f) ⊗ₜ[ℂ] v := by
        rw [TensorProduct.smul_tmul', smul_eq_mul]
      rw [hsm, evalAt_tmul, evalAt_tmul, map_mul, mul_smul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem evAt_coefE (z₀ : UpperHalfPlane) (m : ℕ) :
    evAt z₀ (coefE m) = ((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuGC (m + 2) (z₀ : ℂ) := by
  rw [coefE, map_smul, smul_eq_mul]
  rfl

section

variable (W : VertexOperatorAlgebra 𝒱)

/-! ## Layer C — the specialization respects both spans -/

/-- `blockEvalAt z₀` carries the `E46`-relation module into the relation space at `z₀`. -/
theorem evalAt_mem_blockRelSpan (z₀ : UpperHalfPlane) {x : 𝒱E 𝒱}
    (hx : x ∈ blockRelSpanE W) : blockEvalAt z₀ x ∈ blockRelSpan W (z₀ : ℂ) := by
  classical
  induction hx using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨ka, a, v, hka, ha, rfl⟩ | ⟨ka, K, a, v, hka, ha, hK, rfl⟩
      · rw [evalAt_ιE]
        exact Submodule.subset_span (Or.inl ⟨ka, a, v, hka, ha, rfl⟩)
      · rw [map_add, evalAt_ιE, map_sum]
        have hcong : ∀ m ∈ Finset.range K,
            blockEvalAt z₀ (coefE m • (ιE (vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v) : 𝒱E 𝒱))
              = (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuGC (m + 2) (z₀ : ℂ))
                  • vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v := by
          intro m _
          rw [evalAt_smul, evalAt_ιE, evAt_coefE]
        rw [Finset.sum_congr rfl hcong]
        exact Submodule.subset_span (Or.inr ⟨ka, K, a, v, hka, ha, hK, rfl⟩)
  | zero => simpa using Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
      rw [evalAt_smul]
      exact Submodule.smul_mem _ _ hx

/-- `blockEvalAt z₀` carries the `E46`-span of `ιE '' T` into the `ℂ`-span of `T`. -/
theorem evalAt_mem_span_image (z₀ : UpperHalfPlane) (T : Set 𝒱) {x : 𝒱E 𝒱}
    (hx : x ∈ Submodule.span (↥E46) ((ιE : 𝒱 →ₗ[ℂ] 𝒱E 𝒱) '' T)) :
    blockEvalAt z₀ x ∈ Submodule.span ℂ T := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨t, ht, rfl⟩ := hy
      rw [evalAt_ιE]
      exact Submodule.subset_span ht
  | zero => simpa using Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
      rw [evalAt_smul]
      exact Submodule.smul_mem _ _ hx

end

/-! ## Layer D — the cusp comparison and Nakayama -/

/-- The maximal ideal of the cusp point. -/
noncomputable def cuspIdeal : Ideal (↥E46) := RingHom.ker (evInfty : E46 →+* ℂ)

theorem mem_cuspIdeal {a : ↥E46} : a ∈ cuspIdeal ↔ evInfty a = 0 := RingHom.mem_ker

@[simp] theorem evInfty_zhuGE (j : ℕ) (hj : 2 ≤ j) : evInfty (zhuGE j hj) = zhuG j 0 :=
  evInfty_zhuGC hj

/-- `ιE` carries the `ℂ`-span of `T` into the `E46`-span of `ιE '' T`. -/
theorem ιE_mem_span_image_of_mem_span (T : Set 𝒱) {x : 𝒱} (hx : x ∈ Submodule.span ℂ T) :
    (ιE x : 𝒱E 𝒱) ∈ Submodule.span (↥E46) ((ιE : 𝒱 →ₗ[ℂ] 𝒱E 𝒱) '' T) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero => simpa using Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
      rw [map_smul, ← algebraMap_smul (↥E46) c]
      exact Submodule.smul_mem _ _ hx

/-- **The cusp comparison.**  The two relation families differ by scalars killed by `evInfty`
(`evInfty_zhuGC`), so `ιE` carries `blockRelSpanAtCusp` into `blockRelSpanE + 𝔪·𝒱E`. -/
theorem ιE_mem_sup_cuspIdeal_smul (W : VertexOperatorAlgebra 𝒱) {x : 𝒱}
    (hx : x ∈ blockRelSpanAtCusp W) :
    (ιE x : 𝒱E 𝒱)
      ∈ blockRelSpanE W ⊔ (cuspIdeal • (⊤ : Submodule (↥E46) (𝒱E 𝒱))) := by
  classical
  induction hx using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨ka, a, v, hka, ha, rfl⟩ | ⟨ka, K, a, v, hka, ha, hK, rfl⟩
      · exact Submodule.mem_sup_left
          (Submodule.subset_span (Or.inl ⟨ka, a, v, hka, ha, rfl⟩))
      · -- the `E46` generator
        set G : 𝒱E 𝒱 := (ιE (vSqZ W a ka (-2) v) : 𝒱E 𝒱) + ∑ m ∈ Finset.range K,
            coefE m • (ιE (vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v) : 𝒱E 𝒱) with hG
        have hGmem : G ∈ blockRelSpanE W :=
          Submodule.subset_span (Or.inr ⟨ka, K, a, v, hka, ha, hK, rfl⟩)
        have hdiff : (ιE (vSqZ W a ka (-2) v + ∑ m ∈ Finset.range K,
              (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0)
                • vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v) : 𝒱E 𝒱)
            = G + ∑ m ∈ Finset.range K,
                ((algebraMap ℂ (↥E46) (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0)) - coefE m)
                  • (ιE (vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v) : 𝒱E 𝒱) := by
          rw [hG, map_add, map_sum]
          rw [add_assoc, ← Finset.sum_add_distrib]
          congr 1
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [map_smul, ← algebraMap_smul (↥E46)
            (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0), sub_smul]
          abel
        rw [hdiff]
        refine Submodule.add_mem _ (Submodule.mem_sup_left hGmem) (Submodule.mem_sup_right ?_)
        refine Submodule.sum_mem _ fun m _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
        rw [mem_cuspIdeal, map_sub, AlgHom.commutes, coefE, map_smul, smul_eq_mul,
          evInfty_zhuGE]
        simp
  | zero => simpa using Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
      rw [map_smul, ← algebraMap_smul (↥E46) c]
      exact Submodule.smul_mem _ _ hx

section

variable (W : VertexOperatorAlgebra 𝒱)

-- The Nakayama specialization chains four `Submodule.mem_sup` destructurings through a
-- base-changed tensor product; unification is heavy but the proof is short.
set_option maxHeartbeats 1600000 in
/-- **THE TRANSPORT.**  A finite family spanning `𝒱` modulo the relations *at the cusp*
spans `𝒱` modulo the relations at some **interior** point `z₀ ∈ ℍ`. -/
theorem exists_interior_span_sup_blockRelSpan_of_cusp
    (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W) (T : Set 𝒱)
    (hT : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ T ⊔ blockRelSpanAtCusp W) :
    ∃ z₀ : UpperHalfPlane,
      (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ T ⊔ blockRelSpan W (z₀ : ℂ) := by
  classical
  set N : Submodule (↥E46) (𝒱E 𝒱) :=
    Submodule.span (↥E46) ((ιE : 𝒱 →ₗ[ℂ] 𝒱E 𝒱) '' T) ⊔ blockRelSpanE W with hN
  have hleN : blockRelSpanE W ≤ N := le_sup_right
  -- (i) the quotient is a finite `E46`-module
  haveI : Module.Finite (↥E46) ((𝒱E 𝒱) ⧸ blockRelSpanE W) :=
    moduleFinite_quot_blockRelSpanE W hzero hC2
  have hcomap : blockRelSpanE W ≤ Submodule.comap (LinearMap.id : 𝒱E 𝒱 →ₗ[↥E46] 𝒱E 𝒱) N := hleN
  haveI : Module.Finite (↥E46) ((𝒱E 𝒱) ⧸ N) := by
    refine Module.Finite.of_surjective
      (Submodule.mapQ (blockRelSpanE W) N LinearMap.id hcomap) ?_
    intro y
    obtain ⟨x, rfl⟩ := N.mkQ_surjective y
    exact ⟨(blockRelSpanE W).mkQ x, rfl⟩
  -- (ii) the cusp fibre vanishes: `⊤ ≤ 𝔪 • ⊤` in the quotient
  have hsp : Submodule.span (↥E46) (Set.range (ιE : 𝒱 →ₗ[ℂ] 𝒱E 𝒱))
      ≤ N ⊔ (cuspIdeal • (⊤ : Submodule (↥E46) (𝒱E 𝒱))) := by
    rw [Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ Submodule.span ℂ T ⊔ blockRelSpanAtCusp W := by rw [← hT]; trivial
    obtain ⟨t, ht, g, hg, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.mem_sup_left
        (Submodule.mem_sup_left (ιE_mem_span_image_of_mem_span T ht))
    · rcases Submodule.mem_sup.mp (ιE_mem_sup_cuspIdeal_smul W hg) with ⟨u, hu, w, hw, hsum⟩
      rw [← hsum]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_sup_right hu))
        (Submodule.mem_sup_right hw)
  have htopN : (⊤ : Submodule (↥E46) (𝒱E 𝒱))
      ≤ N ⊔ (cuspIdeal • (⊤ : Submodule (↥E46) (𝒱E 𝒱))) :=
    le_trans (le_of_eq (span_range_ιE_eq_top (𝒱 := 𝒱)).symm) hsp
  have hquot : (⊤ : Submodule (↥E46) ((𝒱E 𝒱) ⧸ N))
      ≤ cuspIdeal • (⊤ : Submodule (↥E46) ((𝒱E 𝒱) ⧸ N)) := by
    have hmap : Submodule.map N.mkQ (cuspIdeal • (⊤ : Submodule (↥E46) (𝒱E 𝒱)))
        = cuspIdeal • (⊤ : Submodule (↥E46) ((𝒱E 𝒱) ⧸ N)) := by
      rw [Submodule.map_smul'', Submodule.map_top, N.range_mkQ]
    rintro y -
    obtain ⟨x, rfl⟩ := N.mkQ_surjective y
    have hxmem : x ∈ N ⊔ (cuspIdeal • (⊤ : Submodule (↥E46) (𝒱E 𝒱))) := htopN Submodule.mem_top
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hxmem
    have hu0 : N.mkQ u = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hu
    rw [map_add, hu0, zero_add, ← hmap]
    exact Submodule.mem_map_of_mem hw
  -- (iii) Nakayama, FG form
  obtain ⟨r, hr1, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
    cuspIdeal (⊤ : Submodule (↥E46) ((𝒱E 𝒱) ⧸ N)) (Module.finite_def.mp inferInstance) hquot
  have hev : evInfty r = 1 := by
    have := (mem_cuspIdeal).mp hr1
    rw [map_sub, map_one, sub_eq_zero] at this
    exact this
  -- (iv) `r` is nonzero somewhere on `ℍ`
  have htend : Tendsto ((r : UpperHalfPlane → ℂ)) atImInfty (𝓝 (evInfty r)) := by
    have := tendsto_of_mem_E46 r.2
    rwa [show valueAtInfty ((r : UpperHalfPlane → ℂ)) = evInfty r from rfl] at this
  have hne : ∀ᶠ z in atImInfty, ((r : UpperHalfPlane → ℂ)) z ≠ 0 := by
    refine htend.eventually_ne ?_
    rw [hev]; exact one_ne_zero
  obtain ⟨z₀, hz₀⟩ := hne.exists
  refine ⟨z₀, le_antisymm ?_ le_top⟩
  intro v _
  -- (v) specialize
  have hrv : r • (ιE v : 𝒱E 𝒱) ∈ N := by
    have h0 : N.mkQ (r • (ιE v : 𝒱E 𝒱)) = 0 := by
      rw [map_smul]
      exact hr0 _ Submodule.mem_top
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
  have hspec : blockEvalAt z₀ (r • (ιE v : 𝒱E 𝒱))
      ∈ Submodule.span ℂ T ⊔ blockRelSpan W (z₀ : ℂ) := by
    obtain ⟨u, hu, w, hw, hsum⟩ := Submodule.mem_sup.mp hrv
    rw [← hsum, map_add]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (evalAt_mem_span_image z₀ T hu))
      (Submodule.mem_sup_right (evalAt_mem_blockRelSpan W z₀ hw))
  rw [evalAt_smul, evalAt_ιE] at hspec
  have hrz : evAt z₀ r ≠ 0 := hz₀
  have := Submodule.smul_mem (Submodule.span ℂ T ⊔ blockRelSpan W (z₀ : ℂ))
    (evAt z₀ r)⁻¹ hspec
  rwa [smul_smul, inv_mul_cancel₀ hrz, one_smul] at this

end

end VOA
