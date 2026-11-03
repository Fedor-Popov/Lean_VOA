/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.SystemGrowth

/-!
# Residual **(c)**: `OnePointSubexp` from `C₂`-cofiniteness alone

`Modularity.BlockSystem` produces the first-order system satisfied by a finite `SubexpPS`-generating
family of a formal block's span; `Modularity.SystemGrowth` shows such systems have subexponential
solutions.  Chaining them gives the growth datum `hgr` for **every** module with a conformal weight
over a `C₂`-cofinite VOA — with no unproved hypothesis.

The inhomogeneous case is free: every block value is a `SubexpPS`-combination of the generating
family, and `subexponential_qConv` propagates the bound.

## Main results

* `subexponential_block_of_c2` — every value of a formal block is subexponential;
* `onePointSubexp_of_c2` — **residual (c)**: `OnePointSubexp N (hw − c/24)`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  Carried: `HasConformalWeight`, `VacuumGradeZero`,
`C2Cofinite` — all legitimate hypotheses of Zhu's theorem.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

section Growth

variable (W : VertexOperatorAlgebra 𝒱)

set_option maxHeartbeats 1000000 in
/-- **Every value of a formal block over a `C₂`-cofinite VOA is subexponential.** -/
theorem subexponential_block_of_c2 {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (hS : IsFormalBlock W S)
    (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W) (v : 𝒱) :
    Subexponential (fun n : ℕ => ‖S v (hbase + (n : ℂ))‖) := by
  classical
  obtain ⟨g, y, A, hsys, hgen⟩ := exists_system_matrix W hsupp hS hzero hC2
  set z : Fin g → ℕ → ℂ := fun k n => ((y k : ↥(QSeriesAt hbase)) : FormalQSeries)
    (hbase + (n : ℂ)) with hz
  set a : Fin g → Fin g → ℕ → ℂ := fun k l j =>
    PowerSeries.coeff j ((A k l : ↥SubexpPS) : PowerSeries ℂ) with ha
  have haSub : ∀ k l, Subexponential (fun j => ‖a k l j‖) := fun k l => (A k l).2
  -- the coefficient form of the system
  have hrec : ∀ (k : Fin g) (Nn : ℕ),
      (hbase + (Nn : ℂ)) * z k Nn
        = ∑ l, ∑ j ∈ Finset.range (Nn + 1), a k l j * z l (Nn - j) := by
    intro k Nn
    have hco : ((qD hbase (y k) : ↥(QSeriesAt hbase)) : FormalQSeries)
        = ((∑ l, A k l • y l : ↥(QSeriesAt hbase)) : FormalQSeries) := by rw [hsys k]
    have hL : ((qD hbase (y k) : ↥(QSeriesAt hbase)) : FormalQSeries) (hbase + (Nn : ℂ))
        = (hbase + (Nn : ℂ)) * z k Nn := rfl
    have hR : ((∑ l, A k l • y l : ↥(QSeriesAt hbase)) : FormalQSeries) (hbase + (Nn : ℂ))
        = ∑ l, ∑ j ∈ Finset.range (Nn + 1), a k l j * z l (Nn - j) := by
      rw [Submodule.coe_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      change psSMul ((A k l : ↥SubexpPS) : PowerSeries ℂ)
        ((y l : ↥(QSeriesAt hbase)) : FormalQSeries) (hbase + (Nn : ℂ)) = _
      rw [psSMul_apply_coset _ (y l).2 Nn]
    rw [← hL, hco, hR]
  have hzSub : ∀ k, Subexponential (fun n => ‖z k n‖) :=
    subexponential_of_system z a haSub hrec
  -- transport to an arbitrary block value
  obtain ⟨c, hc⟩ := hgen v
  have hcoeff : ∀ n : ℕ, S v (hbase + (n : ℂ))
      = ∑ l, qConv (fun j => PowerSeries.coeff j ((c l : ↥SubexpPS) : PowerSeries ℂ))
          ((y l : ↥(QSeriesAt hbase)) : FormalQSeries) (hbase + (n : ℂ)) := by
    intro n
    have hcv : ((blockRestrict hsupp v : ↥(QSeriesAt hbase)) : FormalQSeries)
        = ((∑ l, c l • y l : ↥(QSeriesAt hbase)) : FormalQSeries) := by rw [hc]
    have hlhs : ((blockRestrict hsupp v : ↥(QSeriesAt hbase)) : FormalQSeries)
        (hbase + (n : ℂ)) = S v (hbase + (n : ℂ)) := rfl
    rw [← hlhs, hcv, Submodule.coe_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl (fun l _ => rfl)
  have hterm : ∀ l : Fin g, Subexponential (fun n : ℕ =>
      ‖qConv (fun j => PowerSeries.coeff j ((c l : ↥SubexpPS) : PowerSeries ℂ))
        ((y l : ↥(QSeriesAt hbase)) : FormalQSeries) (hbase + (n : ℂ))‖) :=
    fun l => subexponential_qConv (c l).2 (QSeriesAt.support_neg (y l).2) (hzSub l)
  refine Subexponential.of_le (fun n => ?_)
    (Subexponential.finsetSum Finset.univ (fun l n =>
      ‖qConv (fun j => PowerSeries.coeff j ((c l : ↥SubexpPS) : PowerSeries ℂ))
        ((y l : ↥(QSeriesAt hbase)) : FormalQSeries) (hbase + (n : ℂ))‖)
      (fun l _ => hterm l))
  rw [hcoeff n]
  exact norm_sum_le _ _

/-- **Residual (c).**  For a `C₂`-cofinite VOA, every module with a conformal
weight has subexponential one-point coefficients.  This is the `hgr` hypothesis of the modularity
theorem, as a theorem. -/
theorem onePointSubexp_of_c2 {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule W M) {hw : ℂ} (hcw : HasConformalWeight N hw)
    (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W) :
    OnePointSubexp N (hw - W.centralCharge / 24) := by
  intro v
  exact subexponential_block_of_c2 W (S := torusOnePointHom N)
    (torusOnePoint_mem_QSeriesAt W N hcw) (torusOnePointHom_isFormalBlock N) hzero hC2 v

end Growth

end VOA
