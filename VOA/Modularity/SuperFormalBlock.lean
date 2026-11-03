/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.SuperSquareBracketVirasoro
import VOA.Modularity.SuperBlockRelSpanG
import VOA.Modules.SuperOrdVModule

/-!
# Formal genus-one super blocks

The relation part of a formal super block is defined by annihilation of the actual
`superBlockRelSpanG` under every supported base-change lift.  It is not an independent list of
desired identities.  The zero and minus-two identities are recovered from that kernel condition.

The omega identity is recorded separately because it is a differential identity, not an element
of the algebraic relation module.  No module supertrace is asserted to satisfy it in this file.
-/

namespace VOA

open scoped BigOperators

set_option autoImplicit false

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace SuperNearVOA

/-- A formal untwisted super block.  Its algebraic component is literally annihilation of
`superBlockRelSpanG`; the second component is Zhu's omega differential recursion. -/
def IsSuperFormalBlock (W : SuperVertexOperatorAlgebra 𝒱)
    (S : 𝒱 →ₗ[ℂ] FormalQSeries) : Prop :=
  (∀ (hbase : ℂ) (hsupp : ∀ v, S v ∈ QSeriesAt hbase),
      W.toSuperNearVOA.superBlockRelSpanG ≤ LinearMap.ker (blockLift hsupp)) ∧
    ∀ v : 𝒱,
      S (W.toSuperNearVOA.superLsq (-2) v) = qDeriv (S v)
        + ∑ᶠ m : ℕ, qConv (zhuG (m + 1))
            (S (W.toSuperNearVOA.superLsq (2 * (m + 1) - 2 : ℤ) v))

theorem IsSuperFormalBlock.relation {W : SuperVertexOperatorAlgebra 𝒱}
    {S : 𝒱 →ₗ[ℂ] FormalQSeries} (hS : IsSuperFormalBlock W S)
    (hbase : ℂ) (hsupp : ∀ v, S v ∈ QSeriesAt hbase) :
    W.toSuperNearVOA.superBlockRelSpanG ≤ LinearMap.ker (blockLift hsupp) :=
  hS.1 hbase hsupp

theorem IsSuperFormalBlock.omega {W : SuperVertexOperatorAlgebra 𝒱}
    {S : 𝒱 →ₗ[ℂ] FormalQSeries} (hS : IsSuperFormalBlock W S) (v : 𝒱) :
    S (W.toSuperNearVOA.superLsq (-2) v) = qDeriv (S v)
      + ∑ᶠ m : ℕ, qConv (zhuG (m + 1))
          (S (W.toSuperNearVOA.superLsq (2 * (m + 1) - 2 : ℤ) v)) :=
  hS.2 v

/-- Kernel annihilation gives the square-bracket zero relation. -/
theorem IsSuperFormalBlock.vanish {W : SuperVertexOperatorAlgebra 𝒱}
    {S : 𝒱 →ₗ[ℂ] FormalQSeries} (hS : IsSuperFormalBlock W S)
    {hbase : ℂ} (hsupp : ∀ v, S v ∈ QSeriesAt hbase)
    (k : ℕ) (hk : 1 ≤ k) {a : 𝒱}
    (ha : a ∈ W.toSuperNearVOA.gradingZ (k : ℤ)) (v : 𝒱) :
    S (W.toSuperNearVOA.superVSqZ a k 0 v) = 0 := by
  let V := W.toSuperNearVOA
  have hmem : (ιG (V.superVSqZ a k 0 v) : 𝒱G 𝒱) ∈ V.superBlockRelSpanG :=
    Submodule.subset_span (Or.inl ⟨k, a, v, hk, ha, rfl⟩)
  have hker := LinearMap.mem_ker.mp (hS.relation hbase hsupp hmem)
  rw [blockLift_ιG] at hker
  have hcoe := congrArg (fun z : ↥(QSeriesAt hbase) => (z : FormalQSeries)) hker
  simpa only [blockRestrict_coe, ZeroMemClass.coe_zero] using hcoe

/-- The locally finite omega tail with its zero term removed by the kernel relation. -/
theorem superNegTwo_tail_eq_range_of_vanish
    (V : SuperNearVOA 𝒱) {S : 𝒱 →ₗ[ℂ] FormalQSeries}
    (hvan : ∀ (k : ℕ), 1 ≤ k → ∀ a ∈ V.gradingZ (k : ℤ), ∀ b : 𝒱,
      S (V.superVSqZ a k 0 b) = 0)
    {k K : ℕ} (hk : 1 ≤ k) {a : 𝒱} (ha : a ∈ V.gradingZ (k : ℤ)) (b : 𝒱)
    (hK : ∀ m : ℕ, K ≤ m → V.superVSqZ a k (2 * (m + 1) - 2 : ℤ) b = 0) :
    (∑ᶠ m : ℕ, ((2 * (m + 1) - 1 : ℕ) : ℂ)
        • qConv (zhuG (m + 1))
          (S (V.superVSqZ a k (2 * (m + 1) - 2 : ℤ) b)))
      = ∑ m ∈ Finset.range K, ((2 * (m + 2) - 1 : ℕ) : ℂ)
          • qConv (zhuG (m + 2))
            (S (V.superVSqZ a k (2 * (m + 2) - 2 : ℤ) b)) := by
  classical
  set F : ℕ → FormalQSeries := fun m => ((2 * (m + 1) - 1 : ℕ) : ℂ)
    • qConv (zhuG (m + 1))
      (S (V.superVSqZ a k (2 * (m + 1) - 2 : ℤ) b)) with hFdef
  have hF0 : F 0 = 0 := by
    have hz : (2 * ((0 : ℕ) + 1) - 2 : ℤ) = 0 := by norm_num
    rw [hFdef]
    simp only [hz]
    rw [hvan k hk a ha b, qConv_zero_right, smul_zero]
  have hFK : ∀ m : ℕ, K ≤ m → F m = 0 := by
    intro m hm
    rw [hFdef]
    simp only [hK m hm, map_zero, qConv_zero_right, smul_zero]
  have hsupp : Function.support F ⊆ (Finset.range (K + 1) : Finset ℕ) := by
    intro m hm
    by_contra hc
    rw [Finset.mem_coe, Finset.mem_range] at hc
    exact hm (hFK m (by omega))
  rw [finsum_eq_sum_of_support_subset F hsupp, Finset.sum_range_succ', hF0, add_zero]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [hFdef]
  congr 2

/-- Kernel annihilation also recovers the full minus-two relation. -/
theorem IsSuperFormalBlock.negTwo {W : SuperVertexOperatorAlgebra 𝒱}
    {S : 𝒱 →ₗ[ℂ] FormalQSeries} (hS : IsSuperFormalBlock W S)
    {hbase : ℂ} (hsupp : ∀ v, S v ∈ QSeriesAt hbase)
    (k : ℕ) (hk : 1 ≤ k) {a : 𝒱}
    (ha : a ∈ W.toSuperNearVOA.gradingZ (k : ℤ)) (b : 𝒱) :
    S (W.toSuperNearVOA.superVSqZ a k (-2) b)
      + ∑ᶠ m : ℕ, ((2 * (m + 1) - 1 : ℕ) : ℂ)
          • qConv (zhuG (m + 1))
            (S (W.toSuperNearVOA.superVSqZ a k (2 * (m + 1) - 2 : ℤ) b)) = 0 := by
  classical
  let V := W.toSuperNearVOA
  obtain ⟨K, hK⟩ := V.superVSqZ_tail_eventually_zero a k b
  have hmem : (ιG (V.superVSqZ a k (-2) b) + ∑ m ∈ Finset.range K,
      coefG m • ιG (V.superVSqZ a k (2 * (m + 2) - 2 : ℤ) b) : 𝒱G 𝒱)
      ∈ V.superBlockRelSpanG :=
    Submodule.subset_span (Or.inr ⟨k, K, a, b, hk, ha, hK, rfl⟩)
  have hker := LinearMap.mem_ker.mp (hS.relation hbase hsupp hmem)
  rw [map_add, blockLift_ιG, map_sum] at hker
  have hcoe := congrArg (fun z : ↥(QSeriesAt hbase) => (z : FormalQSeries)) hker
  dsimp only at hcoe
  rw [Submodule.coe_add, blockRestrict_coe, AddSubmonoid.coe_finsetSum,
    ZeroMemClass.coe_zero] at hcoe
  have hterm : ∀ m ∈ Finset.range K,
      (((blockLift hsupp)
        (coefG m • ιG (V.superVSqZ a k (2 * (m + 2) - 2 : ℤ) b))
          : ↥(QSeriesAt hbase)) : FormalQSeries)
        = ((2 * (m + 2) - 1 : ℕ) : ℂ)
            • qConv (zhuG (m + 2))
              (S (V.superVSqZ a k (2 * (m + 2) - 2 : ℤ) b)) := by
    intro m _
    rw [map_smul, blockLift_ιG]
    change psSMul ((coefG m : ↥GSeries) : PowerSeries ℂ)
      ((blockRestrict hsupp
        (V.superVSqZ a k (2 * (m + 2) - 2 : ℤ) b) : ↥(QSeriesAt hbase)) :
        FormalQSeries) = _
    rw [blockRestrict_coe, coefG_coe, psSMul_smul_left _ _ (hsupp _), psSMul_mk]
  rw [Finset.sum_congr rfl hterm,
    ← superNegTwo_tail_eq_range_of_vanish V
      (fun j hj c hc d => hS.vanish hsupp j hj hc d) hk ha b hK] at hcoe
  exact hcoe

/-- The transparent kernel definition supplies the relation interface consumed by the
finite-generation theorem. -/
theorem IsSuperFormalBlock.toRelations {W : SuperVertexOperatorAlgebra 𝒱}
    {S : 𝒱 →ₗ[ℂ] FormalQSeries} (hS : IsSuperFormalBlock W S)
    {hbase : ℂ} (hsupp : ∀ v, S v ∈ QSeriesAt hbase) :
    W.toSuperNearVOA.IsSuperFormalBlockRelations S where
  vanish := fun k hk _a ha b => hS.vanish hsupp k hk ha b
  negTwo := fun k hk _a ha b => hS.negTwo hsupp k hk ha b

/-- Finite generation of the block-value span from the transparent formal-block interface. -/
theorem fg_superBlockSpan_of_superEtingofFinite
    (W : SuperVertexOperatorAlgebra 𝒱) (hV : W.toSuperNearVOA.IntegralWeights)
    {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (hS : IsSuperFormalBlock W S)
    (hE : SuperEtingofFinite W) :
    (Submodule.span (↥GSeries)
      (Set.range (blockRestrict hsupp : 𝒱 →ₗ[ℂ] ↥(QSeriesAt hbase)))).FG :=
  fg_blockSpan_of_superEtingofFinite W hV hsupp (hS.toRelations hsupp) hE

/-- A square-bracket primary vector in the super VOA.  No parity condition is imposed: the even
Virasoro operators preserve whichever parity the vector already has. -/
def IsSuperSqPrimary (V : SuperNearVOA 𝒱) (a : 𝒱) (Δ : ℂ) : Prop :=
  V.superLsq 0 a = Δ • a ∧ ∀ n : ℤ, 1 ≤ n → V.superLsq n a = 0

/-- Positive square-bracket modes kill the vacuum. -/
theorem superVSqZ_nonneg_vacuum (V : SuperNearVOA 𝒱) (k : ℕ) (a : 𝒱)
    {m : ℤ} (hm : 0 ≤ m) : V.superVSqZ a k m V.vacuum = 0 := by
  rw [V.superVSqZ_apply]
  refine finsum_eq_zero_of_forall_eq_zero (fun i => ?_)
  rcases lt_or_ge i m with hi | hi
  · rw [sqBracketCoeffZ_of_lt k hi, zero_smul]
  · rw [V.smul_vacuum_eq_zero a (le_trans hm hi), smul_zero]

/-- `L[n]` kills the vacuum for `n >= -1`. -/
theorem superLsq_vacuum_eq_zero (V : SuperNearVOA 𝒱) {n : ℤ} (hn : -1 ≤ n) :
    V.superLsq n V.vacuum = 0 := by
  rw [Lsq_apply, V.superVSqZ_nonneg_vacuum 2 V.conformalVector (by omega),
    sqBracketCoeffZ_vacuum_of_ne (n + 1) (by omega), mul_zero, zero_smul, sub_zero]

/-- The vacuum is square-bracket primary of weight zero. -/
theorem vacuum_isSuperSqPrimary (V : SuperNearVOA 𝒱) :
    V.IsSuperSqPrimary V.vacuum 0 :=
  ⟨by rw [V.superLsq_vacuum_eq_zero (by norm_num), zero_smul],
    fun n hn => V.superLsq_vacuum_eq_zero (by omega)⟩

end SuperNearVOA

end VOA
