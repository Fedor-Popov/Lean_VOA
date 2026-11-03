import VOA.Huang.GenusOneCollected
import VOA.Huang.GenusOneConvergence

/-! # Unconditional differential closure of the intertwiner trace span -/
namespace VOA.Huang.GenusOne
open VOA
open scoped BigOperators
universe u
variable {V M₁ M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M] [Module ℂ M]
  {W : VertexOperatorAlgebra V} {A : OrdVModule W M₁} {N : OrdVModule W M}

theorem trace_qD_mem (Y : IntertwiningOperator A N N) {h : ℂ}
    (hcw : HasConformalWeight N h) (v : M₁) :
    qD (h - W.centralCharge / 24) (blockRestrict (trace_mem_QSeriesAt Y hcw) v) ∈
      blockSpanS (trace_mem_QSeriesAt Y hcw) := by
  classical
  let hsupp := trace_mem_QSeriesAt Y hcw
  let hbase := h - W.centralCharge / 24
  by_cases hfin : (Function.support (fun m : ℕ =>
      qConv (zhuG (m + 1)) (trace Y (sqL A (2 * (m + 1) - 2 : ℤ) v)))).Finite
  · set B : ↥(QSeriesAt hbase) := ∑ m ∈ hfin.toFinset,
      (⟨PowerSeries.mk (zhuG (m + 1)), mk_zhuG_mem_subexpPS (m + 1)⟩ : ↥SubexpPS)
        • blockRestrict hsupp (sqL A (2 * (m + 1) - 2 : ℤ) v) with hB
    have hBmem : B ∈ blockSpanS hsupp :=
      Submodule.sum_mem _ (fun m _ =>
        Submodule.smul_mem _ _ (blockRestrict_mem_blockSpanS hsupp _))
    have hBcoe : ((B : ↥(QSeriesAt hbase)) : FormalQSeries)
        = ∑ m ∈ hfin.toFinset,
            qConv (zhuG (m + 1)) (trace Y (sqL A (2 * (m + 1) - 2 : ℤ) v)) := by
      rw [hB, Submodule.coe_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      change psSMul (PowerSeries.mk (zhuG (m + 1)))
        (trace Y (sqL A (2 * (m + 1) - 2 : ℤ) v)) = _
      rw [psSMul_mk]
    have heq : qD hbase (blockRestrict hsupp v)
        = blockRestrict hsupp (sqL A (-2) v) - B := by
      refine Subtype.ext ?_
      rw [qD_coe, Submodule.coe_sub, hBcoe]
      change qDeriv (trace Y v) = trace Y (sqL A (-2) v) - _
      rw [show qDeriv (trace Y v) = trace Y (sqL A (-2) v) -
        ∑ᶠ m : ℕ, qConv (zhuG (m + 1)) (trace Y (sqL A (2 * (m + 1) - 2 : ℤ) v)) from
        (eq_sub_iff_add_eq.mpr (trace_sqL_negTwo Y v).symm)]
      congr 1
      exact finsum_eq_sum_of_support_subset _ (by rw [hfin.coe_toFinset])
    rw [heq]
    exact Submodule.sub_mem _ (blockRestrict_mem_blockSpanS hsupp _) hBmem
  · have heq : qD hbase (blockRestrict hsupp v)
        = blockRestrict hsupp (sqL A (-2) v) := by
      refine Subtype.ext ?_
      rw [qD_coe]
      change qDeriv (trace Y v) = trace Y (sqL A (-2) v)
      rw [show qDeriv (trace Y v) = trace Y (sqL A (-2) v) -
        ∑ᶠ m : ℕ, qConv (zhuG (m + 1)) (trace Y (sqL A (2 * (m + 1) - 2 : ℤ) v)) from
        (eq_sub_iff_add_eq.mpr (trace_sqL_negTwo Y v).symm),
        finsum_of_infinite_support hfin, sub_zero]
    rw [heq]
    exact blockRestrict_mem_blockSpanS hsupp _

/-- **`qDeriv`-stability of the block span.**  The `SubexpPS`-smul case is the product rule
`qDeriv (F ⋆ z) = F ⋆ qDeriv z + (θF) ⋆ z`, and `θ` preserves `SubexpPS`. -/
theorem traceDerivativeClosed_holds (Y : IntertwiningOperator A N N) {h : ℂ}
    (hcw : HasConformalWeight N h) : TraceDerivativeClosed Y hcw := by
  let hsupp := trace_mem_QSeriesAt Y hcw
  let hbase := h - W.centralCharge / 24
  intro z hz
  refine Submodule.span_induction
    (p := fun z _ => qD hbase z ∈ blockSpanS hsupp) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨v, rfl⟩
    exact trace_qD_mem Y hcw v
  · simp only [map_zero]; exact Submodule.zero_mem (blockSpanS hsupp)
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


end VOA.Huang.GenusOne
