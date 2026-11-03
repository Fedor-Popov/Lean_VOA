/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.BlockRelSpanG
import VOA.Modularity.QConvModule
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Zhu Lemma 4.4.2 — a **monic** `L[−2]`-relation with `ℂ[G₂,G₄,G₆]` coefficients

`Modularity.BlockRelSpanG` ports Zhu Lemma 4.4.1 to the formal ring `GSeries = ℂ[G₂,G₄,G₆]`.  This
file consumes it: a formal block `S` annihilates `blockRelSpanG` (that is exactly its `vanish` and
`negTwo` laws), so the `GSeries`-span of `S '' 𝒱` inside `QSeriesAt hbase` is a **finitely
generated** `GSeries`-module.  Since `GSeries` is Noetherian, the ascending chain
`⟨S v, S(L[−2]v), …, S(L[−2]^r v)⟩` stabilises, and the relation it produces is **monic** —
Zhu Lemma 4.4.2.

## Main results

* `psSMul_smul_left`, `instIsScalarTowerQSeriesAt` — the scalar towers making `QSeriesAt h` a
  `GSeries`-module compatibly with its `ℂ`-structure;
* `blockRestrict`, `blockLift` — the block, and its `GSeries`-linear extension to `𝒱G`;
* `blockRelSpanG_le_ker` — **a formal block kills the relation module**;
* `moduleFinite_blockSpan` — the block span is a finitely generated `GSeries`-module;
* `exists_monic_Lsq_relation` — **Zhu Lemma 4.4.2**, monic.  ⚠ **Not uniform in the block**:
  `s` and `G` are bound after `S` and `hbase`, because the chain runs inside `↥(QSeriesAt hbase)`.
  See `Modularity.AKUniformODE.exists_uniform_monic_Lsq_relation_of_C2Cofinite` for the version
  whose order and coefficients depend on `W` and `v` alone and hold for every block at once.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators TensorProduct

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## `ℂ`-linearity of `psSMul` in the power-series slot -/

theorem psSMul_smul_left (c : ℂ) (F : PowerSeries ℂ) {h : ℂ} {χ : FormalQSeries}
    (hχ : χ ∈ QSeriesAt h) : psSMul (c • F) χ = c • psSMul F χ := by
  refine QSeriesAt.ext (psSMul_mem _ hχ)
    (Submodule.smul_mem _ c (psSMul_mem F hχ)) (fun N => ?_)
  rw [psSMul_apply_coset _ hχ N]
  change _ = c * psSMul F χ (h + (N : ℂ))
  rw [psSMul_apply_coset _ hχ N, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [map_smul, smul_eq_mul, mul_assoc]

/-- `psSMul` by the power series of a sequence is exactly `qConv` by that sequence. -/
theorem psSMul_mk (f : ℕ → ℂ) (χ : FormalQSeries) :
    psSMul (PowerSeries.mk f) χ = qConv f χ := by
  rw [psSMul]
  congr 1
  funext n
  rw [PowerSeries.coeff_mk]

noncomputable instance instIsScalarTowerPowerSeriesQSeriesAt (h : ℂ) :
    IsScalarTower ℂ (PowerSeries ℂ) ↥(QSeriesAt h) where
  smul_assoc c F χ := Subtype.ext (psSMul_smul_left c F χ.2)

noncomputable instance instIsScalarTowerGSeriesQSeriesAt (h : ℂ) :
    IsScalarTower ℂ ↥GSeries ↥(QSeriesAt h) where
  smul_assoc c g χ := by
    change ((c • g : ↥GSeries) : PowerSeries ℂ) • χ = c • ((g : PowerSeries ℂ) • χ)
    have hc : ((c • g : ↥GSeries) : PowerSeries ℂ) = c • (g : PowerSeries ℂ) := rfl
    rw [hc]
    exact smul_assoc c (g : PowerSeries ℂ) χ

/-! ## A formal block, as a `GSeries`-linear map on the base change -/

section Block

variable (W : VertexOperatorAlgebra 𝒱)

/-- A formal block supported on `hbase + ℕ`, valued in the submodule `QSeriesAt hbase`. -/
noncomputable def blockRestrict {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) : 𝒱 →ₗ[ℂ] ↥(QSeriesAt hbase) where
  toFun v := ⟨S v, hsupp v⟩
  map_add' u v := Subtype.ext (S.map_add u v)
  map_smul' c v := Subtype.ext (S.map_smul c v)

@[simp] theorem blockRestrict_coe {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (v : 𝒱) :
    ((blockRestrict hsupp v : ↥(QSeriesAt hbase)) : FormalQSeries) = S v := rfl

/-- The `GSeries`-linear extension of a formal block to `𝒱G = GSeries ⊗_ℂ 𝒱`. -/
noncomputable def blockLift {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) : 𝒱G 𝒱 →ₗ[↥GSeries] ↥(QSeriesAt hbase) :=
  (blockRestrict hsupp).liftBaseChange (↥GSeries)

@[simp] theorem blockLift_ιG {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (v : 𝒱) :
    blockLift hsupp (ιG v) = blockRestrict hsupp v := by
  rw [blockLift, ιG_apply]
  exact LinearMap.liftBaseChange_one_tmul (↥GSeries) (blockRestrict hsupp) v

/-! ## A formal block annihilates the relation module -/

/-- The `negTwo` tail of a formal block, reindexed onto the `Finset.range K` shape used by
`blockRelSpanG`.  The `m = 0` term drops out by the `vanish` law, and the terms `m ≥ K` drop out by
the tail hypothesis. -/
theorem negTwo_tail_eq_range {S : 𝒱 →ₗ[ℂ] FormalQSeries} (hS : IsFormalBlock W S)
    {ka K : ℕ} (hka : 1 ≤ ka) {a : 𝒱} (ha : a ∈ W.grading (ka : ℤ)) (v : 𝒱)
    (hK : ∀ m : ℕ, K ≤ m → vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v = 0) :
    (∑ᶠ m : ℕ, ((2 * (m + 1) - 1 : ℕ) : ℂ)
        • qConv (zhuG (m + 1)) (S (vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v)))
      = ∑ m ∈ Finset.range K, ((2 * (m + 2) - 1 : ℕ) : ℂ)
          • qConv (zhuG (m + 2)) (S (vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v)) := by
  classical
  set T : ℕ → FormalQSeries := fun m => ((2 * (m + 1) - 1 : ℕ) : ℂ)
    • qConv (zhuG (m + 1)) (S (vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v)) with hTdef
  have hT0 : T 0 = 0 := by
    have hz : (2 * ((0 : ℕ) + 1) - 2 : ℤ) = 0 := by norm_num
    rw [hTdef]
    simp only [hz]
    rw [hS.vanish ka hka a ha v, qConv_zero_right, smul_zero]
  have hTK : ∀ m : ℕ, K ≤ m → T m = 0 := by
    intro m hm
    rw [hTdef]
    simp only [hK m hm, map_zero, qConv_zero_right, smul_zero]
  have hsupp : Function.support T ⊆ (Finset.range (K + 1) : Finset ℕ) := by
    intro m hm
    by_contra hc
    rw [Finset.mem_coe, Finset.mem_range] at hc
    exact hm (hTK m (by omega))
  rw [finsum_eq_sum_of_support_subset T hsupp, Finset.sum_range_succ', hT0, add_zero]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [hTdef]
  congr 2

/-- **A formal block kills the `GSeries`-relation module.**  Conditions (i) and (ii) of Zhu's
genus-one block are exactly the two generating families of `blockRelSpanG`. -/
theorem blockRelSpanG_le_ker {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (hS : IsFormalBlock W S) :
    blockRelSpanG W ≤ LinearMap.ker (blockLift hsupp) := by
  classical
  rw [blockRelSpanG, Submodule.span_le]
  rintro x (⟨ka, a, v, hka, ha, rfl⟩ | ⟨ka, K, a, v, hka, ha, hK, rfl⟩)
  · refine LinearMap.mem_ker.mpr ?_
    rw [blockLift_ιG]
    exact Subtype.ext (by rw [blockRestrict_coe, hS.vanish ka hka a ha v]; rfl)
  · refine LinearMap.mem_ker.mpr ?_
    rw [map_add, blockLift_ιG, map_sum]
    refine Subtype.ext ?_
    rw [Submodule.coe_add, blockRestrict_coe, AddSubmonoid.coe_finset_sum]
    have hterm : ∀ m ∈ Finset.range K,
        (((blockLift hsupp) (coefG m • ιG (vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v))
            : ↥(QSeriesAt hbase)) : FormalQSeries)
          = ((2 * (m + 2) - 1 : ℕ) : ℂ)
              • qConv (zhuG (m + 2)) (S (vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v)) := by
      intro m _
      rw [map_smul, blockLift_ιG]
      change psSMul ((coefG m : ↥GSeries) : PowerSeries ℂ)
        ((blockRestrict hsupp (vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v) : ↥(QSeriesAt hbase))
          : FormalQSeries) = _
      rw [blockRestrict_coe, coefG_coe, psSMul_smul_left _ _ (hsupp _), psSMul_mk]
    rw [Finset.sum_congr rfl hterm, ← negTwo_tail_eq_range W hS hka ha v hK]
    exact hS.negTwo ka hka a ha v

/-! ## The block span is finitely generated over `ℂ[G₂,G₄,G₆]` -/

/-- **The `GSeries`-span of a formal block's values is finitely generated.**  This is Zhu
Lemma 4.4.1 pushed forward along the block: `blockLift` kills the relation module, so the image of
the finite generating family already spans. -/
theorem fg_blockSpan {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (hS : IsFormalBlock W S)
    (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W) :
    (Submodule.span (↥GSeries)
      (Set.range (blockRestrict hsupp : 𝒱 →ₗ[ℂ] ↥(QSeriesAt hbase)))).FG := by
  classical
  obtain ⟨g, gen, wt, hwt, hgen, hdec⟩ := exists_homog_gen_of_C2Cofinite W hC2
  set Sset : Set 𝒱 := Set.range gen ∪ {W.vacuum} with hSdef
  have hShom : ∀ s ∈ Sset, IsHomog W s := by
    rintro s (⟨i, rfl⟩ | hs)
    · exact ⟨(wt i : ℤ), hgen i⟩
    · rw [Set.mem_singleton_iff] at hs
      exact ⟨0, hs ▸ W.vacuum_mem_grading_zero⟩
  have htop := span_sup_blockRelSpanG_eq_top W hzero Sset hShom hdec
  have hSfin : Sset.Finite := (Set.finite_range gen).union (Set.finite_singleton _)
  have hker := blockRelSpanG_le_ker W hsupp hS
  have hmapbot : Submodule.map (blockLift hsupp) (blockRelSpanG W) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact LinearMap.mem_ker.mp (hker hx)
  have himg : (blockLift hsupp) '' ((ιG : 𝒱 →ₗ[ℂ] 𝒱G 𝒱) '' Sset)
      = (blockRestrict hsupp) '' Sset := by
    rw [Set.image_image]
    exact Set.image_congr (fun v _ => blockLift_ιG hsupp v)
  have h1 : Submodule.span (↥GSeries)
      (Set.range (blockRestrict hsupp : 𝒱 →ₗ[ℂ] ↥(QSeriesAt hbase)))
      = LinearMap.range (blockLift hsupp) := by
    rw [blockLift, LinearMap.range_liftBaseChange, LinearMap.coe_range]
  have h2 : LinearMap.range (blockLift hsupp)
      = Submodule.span (↥GSeries) ((blockRestrict hsupp) '' Sset) := by
    rw [LinearMap.range_eq_map, htop, Submodule.map_sup, hmapbot, sup_bot_eq,
      Submodule.map_span, himg]
  rw [h1, h2]
  exact Submodule.fg_span (hSfin.image _)

/-! ## Zhu Lemma 4.4.2 — the monic `L[−2]`-relation -/

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **Zhu Lemma 4.4.2, formal form.**  For a `C₂`-cofinite VOA and any formal block `S`, the
iterates `S(L[−2]^i v)` satisfy a **monic** linear relation of some order `s ≥ 1` with coefficients
in `GSeries = ℂ[G₂, G₄, G₆]`.

Monicity is the point: it is what fixes the degree of the indicial polynomial downstream.  It comes
from Noetherian stabilisation of the ascending chain `⟨S v, …, S(L[−2]^r v)⟩` inside the finitely
generated module `fg_blockSpan`, **not** from a rank/linear-independence argument (which would give
only a non-monic relation).

⚠ **This statement is NOT uniform in the block.**  The chain is run inside
`Submodule.span (↥GSeries) (Set.range (blockRestrict hsupp))`, a submodule of `↥(QSeriesAt hbase)`,
so `S` and `hbase` are bound *before* `s` and `G`: the order and the coefficients produced here
depend on the block, hence on the module whose character is being constrained.  Zhu's own Lemma
4.4.2 produces one relation upstairs, in `V_A`, valid for all blocks at once.

The uniform repair is `Modularity.AKUniformODE.exists_uniform_monic_Lsq_relation_of_C2Cofinite`,
where `s` and `G` are bound *before* `hbase`, `S`, `hsupp` and `IsFormalBlock`; it runs the same
Noetherian argument in `𝒱G 𝒱` modulo `blockRelSpanG W` and then pushes the single resulting
relation forward along every block by `blockRelSpanG_le_ker`.  This theorem is kept as-is because
several downstream files consume it in exactly this form. -/
theorem exists_monic_Lsq_relation {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (hS : IsFormalBlock W S)
    (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W) (v : 𝒱) :
    ∃ (s : ℕ) (G : ℕ → PowerSeries ℂ), 1 ≤ s ∧ (∀ i, G i ∈ GSeries) ∧
      S ((⇑(Lsq W (-2)))^[s] v)
        = ∑ i ∈ Finset.range s, psSMul (G i) (S ((⇑(Lsq W (-2)))^[i] v)) := by
  classical
  set 𝔐 : Submodule (↥GSeries) ↥(QSeriesAt hbase) :=
    Submodule.span (↥GSeries)
      (Set.range (blockRestrict hsupp : 𝒱 →ₗ[ℂ] ↥(QSeriesAt hbase))) with h𝔐
  haveI : IsNoetherianRing (↥GSeries) := isNoetherianRing_GSeries
  haveI hnoe : IsNoetherian (↥GSeries) ↥𝔐 :=
    isNoetherian_of_fg_of_noetherian _ (fg_blockSpan W hsupp hS hzero hC2)
  set x : ℕ → ↥𝔐 := fun i =>
    ⟨blockRestrict hsupp ((⇑(Lsq W (-2)))^[i] v), Submodule.subset_span ⟨_, rfl⟩⟩ with hxdef
  have hmono : Monotone (fun r : ℕ =>
      Submodule.span (↥GSeries) (Set.range (fun i : Fin (r + 1) => x i))) := by
    intro r r' hrr
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨i.1, by omega⟩, rfl⟩
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr hnoe ⟨_, hmono⟩
  have hmem : x (n + 1) ∈ Submodule.span (↥GSeries)
      (Set.range (fun i : Fin (n + 1) => x i)) := by
    have := hn (n + 1) (by omega)
    change Submodule.span (↥GSeries) (Set.range (fun i : Fin (n + 1) => x i))
      = Submodule.span (↥GSeries) (Set.range (fun i : Fin (n + 1 + 1) => x i)) at this
    rw [this]
    exact Submodule.subset_span ⟨⟨n + 1, by omega⟩, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (↥GSeries)).mp hmem
  refine ⟨n + 1, fun i => if h : i < n + 1 then ((c ⟨i, h⟩ : ↥GSeries) : PowerSeries ℂ) else 0,
    by omega, ?_, ?_⟩
  · intro i
    dsimp only
    by_cases h : i < n + 1
    · rw [dif_pos h]; exact (c ⟨i, h⟩).2
    · rw [dif_neg h]; exact zero_mem _
  · set φ : ↥𝔐 →+ FormalQSeries :=
      ((QSeriesAt hbase).subtype.toAddMonoidHom).comp (𝔐.subtype.toAddMonoidHom) with hφ
    have hφsmul : ∀ (g : ↥GSeries) (i : ℕ),
        φ ((g • x i : ↥𝔐)) = psSMul ((g : PowerSeries ℂ)) (S ((⇑(Lsq W (-2)))^[i] v)) :=
      fun _ _ => rfl
    have hφx : ∀ i : ℕ, φ (x i) = S ((⇑(Lsq W (-2)))^[i] v) := fun _ => rfl
    have hL := congrArg φ hc
    rw [map_sum, hφx] at hL
    rw [← hL]
    dsimp only
    have hterm : ∀ i : Fin (n + 1),
        φ ((c i • x (i : ℕ) : ↥𝔐))
          = psSMul (if h : (i : ℕ) < n + 1 then ((c ⟨(i : ℕ), h⟩ : ↥GSeries) : PowerSeries ℂ)
              else 0) (S ((⇑(Lsq W (-2)))^[(i : ℕ)] v)) := by
      intro i
      rw [hφsmul (c i) (i : ℕ), dif_pos i.2]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hterm i)]
    exact Fin.sum_univ_eq_sum_range
      (fun i : ℕ => psSMul (if h : i < n + 1 then ((c ⟨i, h⟩ : ↥GSeries) : PowerSeries ℂ) else 0)
        (S ((⇑(Lsq W (-2)))^[i] v))) (n + 1)

end Block

end VOA
