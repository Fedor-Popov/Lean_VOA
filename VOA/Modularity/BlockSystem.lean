/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.UniCollapse

/-!
# The block span is a `qDeriv`-stable, finitely generated `SubexpPS`-module

`Modularity.UniCollapse` refutes the *scalar-ODE* reading of Zhu Lemma 4.4.4.  The correct object is
the **first-order system** satisfied by a finite generating family of the block span.

Two rings do two jobs (see `Modularity.QDerivProductRule`):
* `GSeries = ℂ[G₂,G₄,G₆]` is Noetherian — it makes the span **finitely generated**
  (`fg_blockSpan`);
* `SubexpPS` (subexponential coefficient series) is **`θ`-stable** — it makes the span
  **`qDeriv`-stable**, which `GSeries` is not.

This file combines them: `blockSpanS`, the `SubexpPS`-span of a formal block's values inside
`QSeriesAt hbase`, is finitely generated **and** `qDeriv`-stable.  Hence `qDeriv` acts on a finite
generating family by a matrix over `SubexpPS` — the system that `Modularity.BlockSystemGrowth`
turns into the growth datum.

## Main results

* `qD` — `qDeriv` as a `ℂ`-endomorphism of `QSeriesAt h`;
* `blockSpanS`, `fg_blockSpanS` — finitely generated (via `fg_blockSpan`);
* `qD_mem_blockSpanS` — **`qDeriv`-stability**;
* `exists_system_matrix` — a finite family generating `blockSpanS` on which `qDeriv` acts by a
  matrix over `SubexpPS`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## `qDeriv` as an endomorphism of `QSeriesAt h` -/

/-- `qDeriv` restricted to the series based at `h`. -/
noncomputable def qD (h : ℂ) : ↥(QSeriesAt h) →ₗ[ℂ] ↥(QSeriesAt h) where
  toFun z := ⟨qDeriv (z : FormalQSeries), qDeriv_mem_QSeriesAt z.2⟩
  map_add' z w := by
    refine Subtype.ext ?_
    funext e
    change e * ((z : FormalQSeries) + (w : FormalQSeries)) e
      = e * (z : FormalQSeries) e + e * (w : FormalQSeries) e
    change e * ((z : FormalQSeries) e + (w : FormalQSeries) e) = _
    ring
  map_smul' c z := by
    refine Subtype.ext ?_
    funext e
    change e * (c • (z : FormalQSeries)) e = c * (e * (z : FormalQSeries) e)
    change e * (c * (z : FormalQSeries) e) = _
    ring

@[simp] theorem qD_coe (h : ℂ) (z : ↥(QSeriesAt h)) :
    ((qD h z : ↥(QSeriesAt h)) : FormalQSeries) = qDeriv (z : FormalQSeries) := rfl

/-! ## `SubexpPS` acts on `QSeriesAt h` -/

noncomputable instance instIsScalarTowerSubexpPSQSeriesAt (h : ℂ) :
    IsScalarTower ℂ ↥SubexpPS ↥(QSeriesAt h) where
  smul_assoc c F χ := by
    change ((c • F : ↥SubexpPS) : PowerSeries ℂ) • χ = c • ((F : PowerSeries ℂ) • χ)
    have hc : ((c • F : ↥SubexpPS) : PowerSeries ℂ) = c • (F : PowerSeries ℂ) := rfl
    rw [hc]
    exact smul_assoc c (F : PowerSeries ℂ) χ

/-- The `GSeries`-span sits inside the `SubexpPS`-span of the same set. -/
theorem span_GSeries_le_span_SubexpPS {h : ℂ} (X : Set ↥(QSeriesAt h)) :
    ∀ z ∈ Submodule.span (↥GSeries) X, z ∈ Submodule.span (↥SubexpPS) X := by
  intro z hz
  refine Submodule.span_induction (p := fun z _ => z ∈ Submodule.span (↥SubexpPS) X)
    (fun x hx => Submodule.subset_span hx) (Submodule.zero_mem _)
    (fun _ _ _ _ ha hb => Submodule.add_mem _ ha hb) ?_ hz
  intro g y _ hy
  have hg : (g : ↥GSeries) • y
      = (⟨(g : PowerSeries ℂ), GSeries_le_subexpPS g.2⟩ : ↥SubexpPS) • y := rfl
  rw [hg]
  exact Submodule.smul_mem _ _ hy

section Block

variable (W : VertexOperatorAlgebra 𝒱)

/-- The `SubexpPS`-span of a formal block's values. -/
noncomputable def blockSpanS {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) : Submodule (↥SubexpPS) ↥(QSeriesAt hbase) :=
  Submodule.span (↥SubexpPS) (Set.range (blockRestrict hsupp : 𝒱 →ₗ[ℂ] ↥(QSeriesAt hbase)))

theorem blockRestrict_mem_blockSpanS {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (v : 𝒱) :
    blockRestrict hsupp v ∈ blockSpanS hsupp :=
  Submodule.subset_span ⟨v, rfl⟩

/-- **The block span is finitely generated over `SubexpPS`** — inherited from `fg_blockSpan`
over the Noetherian ring `GSeries`. -/
theorem fg_blockSpanS {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (hS : IsFormalBlock W S)
    (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W) :
    (blockSpanS hsupp).FG := by
  classical
  obtain ⟨T, hT⟩ := fg_blockSpan W hsupp hS hzero hC2
  refine ⟨T, ?_⟩
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    intro z hz
    have hz' : z ∈ Submodule.span (↥GSeries)
        (Set.range (blockRestrict hsupp : 𝒱 →ₗ[ℂ] ↥(QSeriesAt hbase))) := by
      rw [← hT]; exact Submodule.subset_span hz
    exact span_GSeries_le_span_SubexpPS _ z hz'
  · rw [blockSpanS, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    refine span_GSeries_le_span_SubexpPS (X := (T : Set ↥(QSeriesAt hbase))) _ ?_
    rw [hT]
    exact Submodule.subset_span ⟨v, rfl⟩

/-- `qDeriv` of a block value lands in the block span: the `ω`-law expresses it as a
`SubexpPS`-combination of other block values. -/
theorem qD_blockRestrict_mem {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (hS : IsFormalBlock W S) (v : 𝒱) :
    qD hbase (blockRestrict hsupp v) ∈ blockSpanS hsupp := by
  classical
  by_cases hfin : (Function.support (fun m : ℕ =>
      qConv (zhuG (m + 1)) (S (Lsq W (2 * (m + 1) - 2 : ℤ) v)))).Finite
  · set B : ↥(QSeriesAt hbase) := ∑ m ∈ hfin.toFinset,
      (⟨PowerSeries.mk (zhuG (m + 1)), mk_zhuG_mem_subexpPS (m + 1)⟩ : ↥SubexpPS)
        • blockRestrict hsupp (Lsq W (2 * (m + 1) - 2 : ℤ) v) with hB
    have hBmem : B ∈ blockSpanS hsupp :=
      Submodule.sum_mem _ (fun m _ =>
        Submodule.smul_mem _ _ (blockRestrict_mem_blockSpanS hsupp _))
    have hBcoe : ((B : ↥(QSeriesAt hbase)) : FormalQSeries)
        = ∑ m ∈ hfin.toFinset,
            qConv (zhuG (m + 1)) (S (Lsq W (2 * (m + 1) - 2 : ℤ) v)) := by
      rw [hB, Submodule.coe_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      change psSMul (PowerSeries.mk (zhuG (m + 1)))
        (S (Lsq W (2 * (m + 1) - 2 : ℤ) v)) = _
      rw [psSMul_mk]
    have heq : qD hbase (blockRestrict hsupp v)
        = blockRestrict hsupp (Lsq W (-2) v) - B := by
      refine Subtype.ext ?_
      rw [qD_coe, Submodule.coe_sub, hBcoe]
      change qDeriv (S v) = S (Lsq W (-2) v) - _
      rw [hS.qDeriv_eq v]
      congr 1
      exact finsum_eq_sum_of_support_subset _ (by rw [hfin.coe_toFinset])
    rw [heq]
    exact Submodule.sub_mem _ (blockRestrict_mem_blockSpanS hsupp _) hBmem
  · have heq : qD hbase (blockRestrict hsupp v)
        = blockRestrict hsupp (Lsq W (-2) v) := by
      refine Subtype.ext ?_
      rw [qD_coe]
      change qDeriv (S v) = S (Lsq W (-2) v)
      rw [hS.qDeriv_eq v, finsum_of_infinite_support hfin, sub_zero]
    rw [heq]
    exact blockRestrict_mem_blockSpanS hsupp _

/-- **`qDeriv`-stability of the block span.**  The `SubexpPS`-smul case is the product rule
`qDeriv (F ⋆ z) = F ⋆ qDeriv z + (θF) ⋆ z`, and `θ` preserves `SubexpPS`. -/
theorem qD_mem_blockSpanS {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (hS : IsFormalBlock W S)
    {z : ↥(QSeriesAt hbase)} (hz : z ∈ blockSpanS hsupp) :
    qD hbase z ∈ blockSpanS hsupp := by
  refine Submodule.span_induction
    (p := fun z _ => qD hbase z ∈ blockSpanS hsupp) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨v, rfl⟩
    exact qD_blockRestrict_mem W hsupp hS v
  · simpa using Submodule.zero_mem (blockSpanS hsupp)
  · intro a b _ _ ha hb
    rw [map_add]
    exact Submodule.add_mem _ ha hb
  · intro F y hymem hy
    have hprod : qD hbase ((F : ↥SubexpPS) • y)
        = F • qD hbase y
          + (⟨theta (F : PowerSeries ℂ), theta_mem_subexpPS F.2⟩ : ↥SubexpPS) • y := by
      refine Subtype.ext ?_
      rw [qD_coe, Submodule.coe_add]
      change qDeriv (psSMul ((F : ↥SubexpPS) : PowerSeries ℂ) (y : FormalQSeries))
        = psSMul ((F : ↥SubexpPS) : PowerSeries ℂ) (qDeriv (y : FormalQSeries))
          + psSMul (theta ((F : ↥SubexpPS) : PowerSeries ℂ)) (y : FormalQSeries)
      exact qDeriv_psSMul _ y.2
    rw [hprod]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ hymem)

/-! ## The first-order system -/

/-- **The first-order system.**  A `C₂`-cofinite VOA's block span has a finite
`SubexpPS`-generating family `y` on which `qDeriv` acts by a matrix `A` over `SubexpPS`, and every
block value is a `SubexpPS`-combination of the `y`.  This replaces the scalar ODE of Zhu Lemma 4.4.4
— which `Modularity.UniCollapse` refutes — by the system it should have been all along. -/
theorem exists_system_matrix {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (hS : IsFormalBlock W S)
    (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W) :
    ∃ (g : ℕ) (y : Fin g → ↥(QSeriesAt hbase)) (A : Fin g → Fin g → ↥SubexpPS),
      (∀ k, qD hbase (y k) = ∑ l, A k l • y l) ∧
      (∀ v : 𝒱, ∃ c : Fin g → ↥SubexpPS,
        blockRestrict hsupp v = ∑ l, c l • y l) := by
  classical
  obtain ⟨g, y, hy⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (fg_blockSpanS W hsupp hS hzero hC2)
  have hmemy : ∀ k : Fin g, y k ∈ blockSpanS hsupp := by
    intro k
    rw [← hy]
    exact Submodule.subset_span ⟨k, rfl⟩
  have hA : ∀ k : Fin g, ∃ c : Fin g → ↥SubexpPS, ∑ l, c l • y l = qD hbase (y k) := by
    intro k
    refine (Submodule.mem_span_range_iff_exists_fun (↥SubexpPS)).mp ?_
    rw [hy]
    exact qD_mem_blockSpanS W hsupp hS (hmemy k)
  choose A hAeq using hA
  refine ⟨g, y, A, fun k => (hAeq k).symm, fun v => ?_⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (↥SubexpPS)).mp
    (by rw [hy]; exact blockRestrict_mem_blockSpanS hsupp v)
  exact ⟨c, hc.symm⟩

end Block

end VOA
