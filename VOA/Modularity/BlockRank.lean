/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.RhoS
import VOA.Modularity.BlockSpace

/-!
# `BlockSpannedByTraces` **is** a dimension bound

`Modularity.RhoS` reduces Zhu's modularity theorem to `BlockSpannedByTraces`: every genus-one block
is a combination of the trace functions.  That is Zhu Thm 5.3.3, and stated as a spanning property
it looks like an open-ended condition.  It is not: the trace functions are already **linearly
independent** (that is `TraceIndependent`, itself discharged in `Modularity.TraceIndependence` from
the separation of the `T`-eigenvalues), so spanning is *equivalent* to the numerical statement

  `dim_ℂ 𝔅 ≤ #Φ(𝒱)`,

which is exactly what Zhu's Theorems 5.3.2–5.3.3 deliver.  This file makes that precise:

* `gradedBlocks W : Submodule ℂ (𝒱 → ℂ → ℂ)` — the graded blocks form a `ℂ`-space;
* `restrictImGT` — the (linear) restriction-by-indicator to `ℍ`, which is what identifies two
  blocks that agree where they mean anything;
* `linearIndependent_traceBlock` — the trace blocks are independent, from `TraceIndependent`;
* `blockSpannedByTraces_of_finrank_le` — **the reduction**: `BlockSpannedByTraces` follows
  from `dim ≤ #ι`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open Complex
open scoped BigOperators MatrixGroups

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Truncating the graded tails -/

section Tails

variable {W : VertexOperatorAlgebra 𝒱}

theorem negTwoTail_finsum_eq_sum {F : 𝒱 → ℂ → ℂ} (hF0 : ∀ z ∈ imGT 0, F 0 z = 0) {a v : 𝒱}
    {ka K₀ : ℕ} (hK₀ : ∀ m : ℕ, K₀ ≤ m → vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v = 0) {z : ℂ}
    (hz : z ∈ imGT 0) :
    (∑ᶠ m : ℕ, ((2 * (m + 2) - 1 : ℕ) : ℂ)
        * (zhuGC (m + 2) z * F (vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v) z))
      = ∑ m ∈ Finset.range K₀, ((2 * (m + 2) - 1 : ℕ) : ℂ)
        * (zhuGC (m + 2) z * F (vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v) z) := by
  classical
  refine finsum_eq_finsetSum_of_support_subset _ (fun m hm => ?_)
  simp only [Function.mem_support, ne_eq] at hm
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hc
  refine hm ?_
  have hz0 : vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v = 0 := by
    have hh := hK₀ (m + 1) (by omega)
    rw [show (2 * ((m : ℤ) + 2) - 2) = (2 * (((m + 1 : ℕ) : ℤ) + 1) - 2) from by push_cast; ring]
    exact hh
  rw [hz0, hF0 z hz, mul_zero, mul_zero]

theorem omegaTail_finsum_eq_sum {F : 𝒱 → ℂ → ℂ} (hF0 : ∀ z ∈ imGT 0, F 0 z = 0) {v : 𝒱} {K₀ : ℕ}
    (hK₀ : ∀ m : ℕ, K₀ ≤ m → Lsq W (2 * (m + 1) - 2 : ℤ) v = 0) {z : ℂ} (hz : z ∈ imGT 0) :
    (∑ᶠ m : ℕ, zhuGC (m + 2) z * F (Lsq W (2 * (m + 2) - 2 : ℤ) v) z)
      = ∑ m ∈ Finset.range K₀, zhuGC (m + 2) z * F (Lsq W (2 * (m + 2) - 2 : ℤ) v) z := by
  classical
  refine finsum_eq_finsetSum_of_support_subset _ (fun m hm => ?_)
  simp only [Function.mem_support, ne_eq] at hm
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hc
  refine hm ?_
  have hz0 : Lsq W (2 * (m + 2) - 2 : ℤ) v = 0 := by
    have hh := hK₀ (m + 1) (by omega)
    rw [show (2 * ((m : ℤ) + 2) - 2) = (2 * (((m + 1 : ℕ) : ℤ) + 1) - 2) from by push_cast; ring]
    exact hh
  rw [hz0, hF0 z hz, mul_zero]

end Tails

/-! ## The graded blocks form a `ℂ`-space -/

section Space

variable {W : VertexOperatorAlgebra 𝒱}

theorem isGradedBlock_zero : IsGradedBlock W (fun (_ : 𝒱) (_ : ℂ) => (0 : ℂ)) where
  holo := fun _ => differentiableOn_const 0
  zerov := by intro z _; rfl
  addv := by intro n v w _ _ z _; ring
  smulv := by intro n c v _ z _; ring
  vanish := by intro ka hka a ha v z _; rfl
  negTwo := by
    intro ka hka a ha K n haK v hv z hz
    rw [finsum_eq_zero_of_forall_eq_zero (fun _ => by ring)]; ring
  omega := by
    intro n v hv z hz
    rw [finsum_eq_zero_of_forall_eq_zero (fun _ => by ring), serreDerivC,
      show _root_.deriv (fun (_ : ℂ) => (0 : ℂ)) z = 0 from deriv_const z 0]
    ring

theorem IsGradedBlock.smul {F : 𝒱 → ℂ → ℂ} (hF : IsGradedBlock W F) (c : ℂ) :
    IsGradedBlock W (fun v z => c * F v z) where
  holo := fun v => (hF.holo v).const_mul c
  zerov := fun z hz => by rw [hF.zerov z hz]; ring
  addv := fun n v w hv hw z hz => by rw [hF.addv n v w hv hw z hz]; ring
  smulv := fun n d v hv z hz => by rw [hF.smulv n d v hv z hz]; ring
  vanish := fun ka hka a ha v z hz => by rw [hF.vanish ka hka a ha v z hz]; ring
  negTwo := fun ka hka a ha K n haK v hv z hz => by
    obtain ⟨K₀, hK₀⟩ := vSqZ_tail_eventually_zero W a ka v
    have hlaw := hF.negTwo ka hka a ha K n haK v hv z hz
    rw [negTwoTail_finsum_eq_sum hF.zerov hK₀ hz] at hlaw
    rw [negTwoTail_finsum_eq_sum (F := fun v z => c * F v z)
      (fun z hz => by show c * F 0 z = 0; rw [hF.zerov z hz]; ring) hK₀ hz]
    have hpull : ∑ m ∈ Finset.range K₀, ((2 * (m + 2) - 1 : ℕ) : ℂ)
          * (zhuGC (m + 2) z * (c * F (vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v) z))
        = c * ∑ m ∈ Finset.range K₀, ((2 * (m + 2) - 1 : ℕ) : ℂ)
          * (zhuGC (m + 2) z * F (vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v) z) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    rw [hpull]
    linear_combination c * hlaw
  omega := fun n v hv z hz => by
    obtain ⟨K₀, hK₀⟩ := Lsq_tail_eventually_zero W v
    have hlaw := hF.omega n v hv z hz
    rw [omegaTail_finsum_eq_sum hF.zerov hK₀ hz] at hlaw
    rw [omegaTail_finsum_eq_sum (F := fun v z => c * F v z)
      (fun z hz => by show c * F 0 z = 0; rw [hF.zerov z hz]; ring) hK₀ hz]
    have hd : _root_.deriv (fun z => c * F v z) z = c * _root_.deriv (F v) z :=
      deriv_const_mul c ((hF.holo v).differentiableAt ((isOpen_imGT 0).mem_nhds hz))
    have hpull : ∑ m ∈ Finset.range K₀,
          zhuGC (m + 2) z * (c * F (Lsq W (2 * (m + 2) - 2 : ℤ) v) z)
        = c * ∑ m ∈ Finset.range K₀,
            zhuGC (m + 2) z * F (Lsq W (2 * (m + 2) - 2 : ℤ) v) z := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    rw [serreDerivC] at hlaw
    rw [hpull, serreDerivC, hd]
    linear_combination c * hlaw

theorem IsGradedBlock.add {F G : 𝒱 → ℂ → ℂ} (hF : IsGradedBlock W F) (hG : IsGradedBlock W G) :
    IsGradedBlock W (fun v z => F v z + G v z) where
  holo := fun v => (hF.holo v).add (hG.holo v)
  zerov := fun z hz => by rw [hF.zerov z hz, hG.zerov z hz]; ring
  addv := fun n v w hv hw z hz => by rw [hF.addv n v w hv hw z hz, hG.addv n v w hv hw z hz]; ring
  smulv := fun n c v hv z hz => by rw [hF.smulv n c v hv z hz, hG.smulv n c v hv z hz]; ring
  vanish := fun ka hka a ha v z hz => by
    rw [hF.vanish ka hka a ha v z hz, hG.vanish ka hka a ha v z hz]; ring
  negTwo := fun ka hka a ha K n haK v hv z hz => by
    obtain ⟨K₀, hK₀⟩ := vSqZ_tail_eventually_zero W a ka v
    have hlawF := hF.negTwo ka hka a ha K n haK v hv z hz
    have hlawG := hG.negTwo ka hka a ha K n haK v hv z hz
    rw [negTwoTail_finsum_eq_sum hF.zerov hK₀ hz] at hlawF
    rw [negTwoTail_finsum_eq_sum hG.zerov hK₀ hz] at hlawG
    rw [negTwoTail_finsum_eq_sum (F := fun v z => F v z + G v z)
      (fun z hz => by show F 0 z + G 0 z = 0; rw [hF.zerov z hz, hG.zerov z hz]; ring) hK₀ hz]
    have hsplit : ∑ m ∈ Finset.range K₀, ((2 * (m + 2) - 1 : ℕ) : ℂ)
          * (zhuGC (m + 2) z * (F (vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v) z
            + G (vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v) z))
        = (∑ m ∈ Finset.range K₀, ((2 * (m + 2) - 1 : ℕ) : ℂ)
            * (zhuGC (m + 2) z * F (vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v) z))
          + ∑ m ∈ Finset.range K₀, ((2 * (m + 2) - 1 : ℕ) : ℂ)
            * (zhuGC (m + 2) z * G (vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v) z) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    rw [hsplit]
    linear_combination hlawF + hlawG
  omega := fun n v hv z hz => by
    obtain ⟨K₀, hK₀⟩ := Lsq_tail_eventually_zero W v
    have hlawF := hF.omega n v hv z hz
    have hlawG := hG.omega n v hv z hz
    rw [omegaTail_finsum_eq_sum hF.zerov hK₀ hz] at hlawF
    rw [omegaTail_finsum_eq_sum hG.zerov hK₀ hz] at hlawG
    rw [omegaTail_finsum_eq_sum (F := fun v z => F v z + G v z)
      (fun z hz => by show F 0 z + G 0 z = 0; rw [hF.zerov z hz, hG.zerov z hz]; ring) hK₀ hz]
    have hd : _root_.deriv (fun z => F v z + G v z) z
        = _root_.deriv (F v) z + _root_.deriv (G v) z :=
      deriv_add ((hF.holo v).differentiableAt ((isOpen_imGT 0).mem_nhds hz))
        ((hG.holo v).differentiableAt ((isOpen_imGT 0).mem_nhds hz))
    have hsplit : ∑ m ∈ Finset.range K₀, zhuGC (m + 2) z
          * (F (Lsq W (2 * (m + 2) - 2 : ℤ) v) z + G (Lsq W (2 * (m + 2) - 2 : ℤ) v) z)
        = (∑ m ∈ Finset.range K₀, zhuGC (m + 2) z * F (Lsq W (2 * (m + 2) - 2 : ℤ) v) z)
          + ∑ m ∈ Finset.range K₀, zhuGC (m + 2) z * G (Lsq W (2 * (m + 2) - 2 : ℤ) v) z := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    rw [serreDerivC] at hlawF hlawG
    rw [hsplit, serreDerivC, hd]
    linear_combination hlawF + hlawG

/-- **The space of graded genus-one blocks.** -/
def gradedBlocks (W : VertexOperatorAlgebra 𝒱) : Submodule ℂ (𝒱 → ℂ → ℂ) where
  carrier := {F : 𝒱 → ℂ → ℂ | IsGradedBlock W F}
  add_mem' := fun hF hG => hF.add hG
  zero_mem' := isGradedBlock_zero
  smul_mem' := fun c _ hF => hF.smul c

@[simp] theorem mem_gradedBlocks (W : VertexOperatorAlgebra 𝒱) (F : 𝒱 → ℂ → ℂ) :
    F ∈ gradedBlocks W ↔ IsGradedBlock W F := Iff.rfl

end Space

/-! ## Restriction to `ℍ` -/

/-- The linear "restrict to the upper half-plane" map: extend by zero off `imGT 0`.  Two blocks
represent the same object exactly when their restrictions agree. -/
noncomputable def restrictImGT : (𝒱 → ℂ → ℂ) →ₗ[ℂ] (𝒱 → ℂ → ℂ) where
  toFun F := fun v => Set.indicator (imGT 0) (F v)
  map_add' F G := by
    funext v z
    by_cases hz : z ∈ imGT 0
    · simp only [Pi.add_apply, Set.indicator_of_mem hz]
    · simp only [Pi.add_apply, Set.indicator_of_notMem hz, add_zero]
  map_smul' c F := by
    funext v z
    by_cases hz : z ∈ imGT 0
    · simp only [Pi.smul_apply, smul_eq_mul, Set.indicator_of_mem hz, RingHom.id_apply]
    · simp only [Pi.smul_apply, smul_eq_mul, Set.indicator_of_notMem hz, RingHom.id_apply,
        mul_zero]

theorem restrictImGT_apply (F : 𝒱 → ℂ → ℂ) {v : 𝒱} {z : ℂ} (hz : z ∈ imGT 0) :
    restrictImGT F v z = F v z := Set.indicator_of_mem hz _

theorem restrictImGT_eq_iff (F G : 𝒱 → ℂ → ℂ) :
    restrictImGT F = restrictImGT G ↔ ∀ (v : 𝒱), ∀ z ∈ imGT 0, F v z = G v z := by
  constructor
  · intro h v z hz
    have := congrFun (congrFun h v) z
    rwa [restrictImGT_apply _ hz, restrictImGT_apply _ hz] at this
  · intro h
    funext v z
    by_cases hz : z ∈ imGT 0
    · rw [restrictImGT_apply _ hz, restrictImGT_apply _ hz, h v z hz]
    · show Set.indicator (imGT 0) (F v) z = Set.indicator (imGT 0) (G v) z
      rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]

/-! ## The linear-algebra core -/

/-- If `𝔄` is spanned by nothing bigger than `#ι` and contains `#ι` independent vectors `t i`, then
those vectors span it. -/
theorem exists_coeff_of_rank_le {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ι : Type*} [Fintype ι] {𝔄 : Submodule ℂ V} {t : ι → V}
    (hmem : ∀ i, t i ∈ 𝔄) (hindep : LinearIndependent ℂ t)
    (hrank : Module.rank ℂ 𝔄 ≤ (Fintype.card ι : Cardinal)) :
    ∀ x ∈ 𝔄, ∃ c : ι → ℂ, x = ∑ i, c i • t i := by
  have hlt : Module.rank ℂ 𝔄 < Cardinal.aleph0 :=
    lt_of_le_of_lt hrank (Cardinal.nat_lt_aleph0 _)
  haveI : FiniteDimensional ℂ 𝔄 := by
    rw [FiniteDimensional, ← Module.rank_lt_aleph0_iff]; exact hlt
  have hsub : Submodule.span ℂ (Set.range t) ≤ 𝔄 := by
    rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact hmem i
  have hrk : Module.finrank ℂ (Submodule.span ℂ (Set.range t)) = Fintype.card ι :=
    finrank_span_eq_card hindep
  have heq : Submodule.span ℂ (Set.range t) = 𝔄 :=
    Submodule.eq_of_le_of_finrank_le hsub (by rw [hrk]; exact Module.finrank_le_of_rank_le hrank)
  intro x hx
  rw [← heq, Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, hc⟩ := hx
  exact ⟨c, hc.symm⟩

/-! ## `BlockSpannedByTraces` from a dimension bound -/

section Rank

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {W : VertexOperatorAlgebra 𝒱}
variable (Mfam : ι → IrrModule W) (h : ι → ℂ)

theorem restrictImGT_traceBlock (i : ι) :
    restrictImGT (traceBlock Mfam h i) = traceBlock Mfam h i := by
  funext v z
  by_cases hz : z ∈ imGT 0
  · exact restrictImGT_apply _ hz
  · show Set.indicator (imGT 0) (traceBlock Mfam h i v) z = _
    rw [Set.indicator_of_notMem hz, traceBlock, anEval, Set.indicator_of_notMem hz]

/-- **The trace blocks are linearly independent**, straight from `TraceIndependent`. -/
theorem linearIndependent_traceBlock (hind : TraceIndependent Mfam h) :
    LinearIndependent ℂ (traceBlock Mfam h) := by
  rw [linearIndependent_iff']
  intro s c hc i hi
  by_contra hne
  have hzero : ∀ (n : ℕ) (v : 𝒱), v ∈ sqWeightSpace W (n : ℂ) → ∀ τ : UpperHalfPlane,
      ∑ j, (if j ∈ s then c j else 0) * traceFun Mfam h j v τ = 0 := by
    intro n v _ τ
    have hpt : ∀ j : ι, (if j ∈ s then c j else 0) * traceFun Mfam h j v τ
        = if j ∈ s then c j * traceFun Mfam h j v τ else 0 := by
      intro j; by_cases hj : j ∈ s <;> simp [hj]
    have hcs : ∑ j, (if j ∈ s then c j else 0) * traceFun Mfam h j v τ
        = ∑ j ∈ s, c j * traceFun Mfam h j v τ := by
      rw [Finset.sum_congr rfl (fun j _ => hpt j), ← Finset.sum_filter,
        Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [hcs]
    have := congrFun (congrFun hc v) (τ : ℂ)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl (fun j _ => by rw [traceBlock_coe])
  have := hind (fun j => if j ∈ s then c j else 0) hzero
  have hi2 := congrFun this i
  simp only [Pi.zero_apply, if_pos hi] at hi2
  exact hne hi2

/-- **`BlockSpannedByTraces` IS a dimension bound.**

The trace blocks are linearly independent (`linearIndependent_traceBlock`), so they span a
subspace of dimension `#ι` inside the restricted graded blocks.  If that ambient space has
dimension at most `#ι` — Zhu's Theorems 5.3.2–5.3.3 — the two coincide, which is exactly
`BlockSpannedByTraces`. -/
theorem blockSpannedByTraces_of_finrank_le
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24))
    (hind : TraceIndependent Mfam h)
    (hfd : FiniteDimensional ℂ (Submodule.map restrictImGT (gradedBlocks W)))
    (hle : Module.finrank ℂ (Submodule.map restrictImGT (gradedBlocks W)) ≤ Fintype.card ι) :
    BlockSpannedByTraces Mfam h := by
  classical
  set 𝔅 : Submodule ℂ (𝒱 → ℂ → ℂ) := Submodule.map restrictImGT (gradedBlocks W) with h𝔅
  set 𝔗 : Submodule ℂ (𝒱 → ℂ → ℂ) := Submodule.span ℂ (Set.range (traceBlock Mfam h)) with h𝔗
  have htrmem : ∀ i : ι, traceBlock Mfam h i ∈ 𝔅 :=
    fun i => ⟨traceBlock Mfam h i, traceBlock_isGradedBlock Mfam h hcw hgr i,
      restrictImGT_traceBlock Mfam h i⟩
  have hsubT : 𝔗 ≤ 𝔅 := by
    rw [h𝔗, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact htrmem i
  have hrankT : Module.finrank ℂ 𝔗 = Fintype.card ι := by
    rw [h𝔗]
    exact finrank_span_eq_card (linearIndependent_traceBlock Mfam h hind)
  have heq : 𝔗 = 𝔅 :=
    Submodule.eq_of_le_of_finrank_le hsubT (by rw [hrankT]; exact hle)
  intro G hG
  have hGmem : restrictImGT G ∈ 𝔅 := ⟨G, hG, rfl⟩
  rw [← heq, h𝔗, Submodule.mem_span_range_iff_exists_fun] at hGmem
  obtain ⟨c, hc⟩ := hGmem
  refine ⟨c, fun n v hv z hz => ?_⟩
  have hval := congrFun (congrFun hc v) z
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hval
  rw [hval, restrictImGT_apply _ hz]

/-- **`BlockSpannedByTraces` from the single cardinal bound `rank 𝔅 ≤ #ι`.**  A rank bound by a
*finite* cardinal already forces finite-dimensionality, so this is the clean one-hypothesis form. -/
theorem blockSpannedByTraces_of_rank_le
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24))
    (hind : TraceIndependent Mfam h)
    (hrank : Module.rank ℂ (Submodule.map restrictImGT (gradedBlocks W))
      ≤ (Fintype.card ι : Cardinal)) :
    BlockSpannedByTraces Mfam h := by
  have hlt : Module.rank ℂ (Submodule.map restrictImGT (gradedBlocks W)) < Cardinal.aleph0 :=
    lt_of_le_of_lt hrank (Cardinal.nat_lt_aleph0 _)
  haveI : FiniteDimensional ℂ (Submodule.map restrictImGT (gradedBlocks W)) := by
    rw [FiniteDimensional, ← Module.rank_lt_aleph0_iff]
    exact hlt
  exact blockSpannedByTraces_of_finrank_le Mfam h hcw hgr hind inferInstance
    (Module.finrank_le_of_rank_le hrank)

/-! ## The `SqModeWeighted`-free route

`Modularity.RhoS.traceSpanning_of_slashSpannedAtS` needs the spanning statement only for the
`S`-slashes, and uses no slash-stability — hence no `SqModeWeighted`.  Enlarging the ambient space
so that it *contains* the `S`-slashes by fiat, the same rank bound delivers it. -/

/-- The graded blocks together with the `γ`-slashes of the trace blocks. -/
noncomputable def slashAmbient (γ : SL(2, ℤ)) : Submodule ℂ (𝒱 → ℂ → ℂ) :=
  Submodule.map restrictImGT (gradedBlocks W)
    ⊔ Submodule.span ℂ (Set.range fun i : ι => restrictImGT (blockSlash W γ (traceBlock Mfam h i)))

/-- **`SlashSpannedAtS` from a dimension bound — with NO `SqModeWeighted`.**  The ambient
space `𝔄` is *any* subspace containing the trace blocks and the `S`-slashes of the trace blocks, so
nothing has to be *recognised* as a block; the trace blocks are independent, so a rank bound by
`#ι` forces them to span. -/
theorem slashSpannedAtS_of_rank_le' (𝔄 : Submodule ℂ (𝒱 → ℂ → ℂ))
    (hind : TraceIndependent Mfam h)
    (htr : ∀ i : ι, traceBlock Mfam h i ∈ 𝔄)
    (hsl : ∀ i : ι, restrictImGT (blockSlash W ModularGroup.S (traceBlock Mfam h i)) ∈ 𝔄)
    (hrank : Module.rank ℂ 𝔄 ≤ (Fintype.card ι : Cardinal)) :
    SlashSpannedAtS Mfam h := by
  classical
  have hcoeff := exists_coeff_of_rank_le htr (linearIndependent_traceBlock Mfam h hind) hrank
  intro i
  obtain ⟨c, hc⟩ := hcoeff _ (hsl i)
  refine ⟨c, fun n v hv z hz => ?_⟩
  have hval := congrFun (congrFun hc v) z
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hval
  rw [← restrictImGT_apply (blockSlash W ModularGroup.S (traceBlock Mfam h i)) hz, hval]

theorem slashSpannedAtS_of_rank_le
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24))
    (hind : TraceIndependent Mfam h)
    (hrank : Module.rank ℂ (slashAmbient Mfam h ModularGroup.S) ≤ (Fintype.card ι : Cardinal)) :
    SlashSpannedAtS Mfam h := by
  refine slashSpannedAtS_of_rank_le' Mfam h _ hind (fun i => ?_) (fun i => ?_) hrank
  · exact Submodule.mem_sup_left ⟨traceBlock Mfam h i,
      traceBlock_isGradedBlock Mfam h hcw hgr i, restrictImGT_traceBlock Mfam h i⟩
  · exact Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)

/-- **Zhu's modularity from the dimension bound, `SqModeWeighted`-free.** -/
theorem zhu_modularity_of_slashRank_le
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24))
    (hinj : Function.Injective (tEigen W h))
    (hrank : Module.rank ℂ (slashAmbient Mfam h ModularGroup.S) ≤ (Fintype.card ι : Cardinal)) :
    ZhuModularityAnalytic
      (modularDataOf Mfam h
        (traceSpanning_of_slashSpannedAtS Mfam h hcw hgr
          (slashSpannedAtS_of_rank_le Mfam h hcw hgr
            (traceIndependent_of_tEigen_injective Mfam h hcw hinj
              (traceNonvanishing_of_onePointSubexp Mfam h hcw hgr)) hrank))
        (traceIndependent_of_tEigen_injective Mfam h hcw hinj
          (traceNonvanishing_of_onePointSubexp Mfam h hcw hgr)) hcw) :=
  zhu_modularity_of_spanning Mfam h _ _ hcw

/-- **ZHU'S MODULARITY THEOREM FROM A DIMENSION BOUND.**

This is the sharpest form the repo reaches: Zhu's law 5.3.18a for **every** `A ∈ SL₂(ℤ)`, every
homogeneous `v`, every `τ`, from

* the analytic theory proved here (the trace functions are blocks; the block conditions are
  `SL₂(ℤ)`-stable),
* the growth datum (`OnePointSubexp`, reduced in `Modularity.OnePointDescent` to `g+1` sequences),
* `SqModeWeighted` (Zhu's square-bracket mode grading),
* the `T`-eigenvalue separation (which discharges independence), and
* **`dim_ℂ 𝔅 ≤ #Φ(𝒱)`** — the numerical content of Zhu's Theorems 5.3.2–5.3.3, and the only
  remaining deep input. -/
theorem zhu_modularity_of_finrank_le
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24))
    (hwt : SqModeWeighted W)
    (hinj : Function.Injective (tEigen W h)) (hnv : TraceNonvanishing Mfam h)
    (hfd : FiniteDimensional ℂ (Submodule.map restrictImGT (gradedBlocks W)))
    (hle : Module.finrank ℂ (Submodule.map restrictImGT (gradedBlocks W)) ≤ Fintype.card ι) :
    ZhuModularityAnalytic
      (modularDataOf Mfam h
        (traceSpanning_of_blockSpanned Mfam h hcw hgr hwt
          (blockSpannedByTraces_of_finrank_le Mfam h hcw hgr
            (traceIndependent_of_tEigen_injective Mfam h hcw hinj hnv) hfd hle))
        (traceIndependent_of_tEigen_injective Mfam h hcw hinj hnv) hcw) :=
  zhu_modularity_of_blockSpanned Mfam h hcw hgr hwt
    (blockSpannedByTraces_of_finrank_le Mfam h hcw hgr
      (traceIndependent_of_tEigen_injective Mfam h hcw hinj hnv) hfd hle)
    hinj hnv

end Rank

end VOA
