/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.BlockFiniteDim

/-!
# The obstruction for the pointwise slash

`Modularity.BlockFiniteDim.zhu_modularity_of_analytic_finrank_le` reduces Zhu's modularity theorem
to the single numerical hypothesis

  `hle : dim_ℂ (analyticSlashAmbient Mfam h) ≤ #ι`,   where
  `analyticSlashAmbient = restrictImGT '' 𝔅  ⊔  span {restrictImGT (F_i ∣ S)}`.

This file proves that **the displayed `hle` cannot hold** for the pointwise `blockSlash` definition
when `𝒱` has two nonzero `L[0]`-weights carrying a nonvanishing trace.  This is a diagnosis of
that definition, not a vacuity theorem about Zhu's source slash action:

* every element of `restrictImGT '' 𝔅` is **additive in the vector slot** (`IsAnalyticBlock.addv`
  is unrestricted), hence so is every element of the span of the trace blocks;
* the slashed function `F ∣ S` is *not*: `blockSlash W γ F v = (F v)∣[wt v]γ` uses the **weight of
  `v`**, and `sqWtOf W u = 0` for an inhomogeneous `u`, so
  `(F∣S)(v + w) = (F∣S)(v)·D^{wt v} + (F∣S)(w)·D^{wt w}` fails whenever `wt v ≠ wt w`.

Since the trace blocks are `#ι` independent elements of that ambient, `hle` would force it to *be*
their span, hence to consist of additive functions — contradicting the previous point.  The
source-correct action in `SqGradedBlock` instead decomposes a vector into its square-weight
components and extends the slash linearly; this obstruction does not apply to it.

## Main results

* `addOnImGT` — the submodule of functions additive in the vector slot on `ℍ`;
* `map_restrictImGT_analyticBlocks_le_addOnImGT` — `restrictImGT '' 𝔅 ≤ addOnImGT`;
* `sqWtOf_add_eq_zero_of_ne` — the sum of two nonzero vectors of **distinct** `L[0]`-weights is
  inhomogeneous, so `sqWtOf` returns its junk value `0`;
* `not_rank_analyticSlashAmbient_le` / `not_finrank_analyticSlashAmbient_le` — the pointwise-slash
  `hle` is
  contradictory under their explicit hypotheses;
* `SqPt`/`sqRestrict`/`sqPtEval` and `slashSpannedAtS_of_sqRank_le`,
  `zhu_modularity_of_sqRank_le` — the earlier homogeneous-point workaround: the same argument in
  the space of functions
  *restricted to `L[0]`-homogeneous vectors*, where the obstruction disappears because `blockSlash`
  **is** additive inside a weight space.  This is the hypothesis Zhu's Theorem 5.3.3 should be
  attached to.  Two corresponding ambients are supplied:
  * `sqAnalyticSlashAmbient` (analytic blocks + the slashes) — keeps Zhu's Theorem 5.3.2:
    `finiteDimensional_sqAnalyticSlashAmbient` is unconditional in `C₂`-cofiniteness, so `hfd`
    stays discharged; both memberships are free; `zhu_modularity_of_sqAnalyticRank_le`.
  * `sqGradedAmbient` (graded blocks) — both memberships are *proved* from
    `isGradedBlock_blockSlash` (consuming the pre-existing `SqModeWeighted`), giving
    `zhu_modularity_of_sqGradedRank_le`; ⚠ but on this ambient finite-dimensionality is
    **open** (`IsAnalyticBlock.toGradedBlock` runs the wrong way, and `IsGradedBlock.negTwo`
    hypothesises `a` *bi*-homogeneous), so it trades `hfd` for the two memberships.

## Status
The theorems about the pointwise-slash definitions are proved and axiom-clean.  They record why
the `sqWtOf` design fails; they do not refute the linear square-decomposition slash.
-/

namespace VOA

open Complex
open scoped BigOperators MatrixGroups

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Additivity in the vector slot -/

/-- The functions `𝒱 → ℂ → ℂ` that are **additive in the vector slot** on the upper half-plane.
A submodule, and it contains every (restricted) analytic block. -/
def addOnImGT : Submodule ℂ (𝒱 → ℂ → ℂ) where
  carrier := {X : 𝒱 → ℂ → ℂ | ∀ v w : 𝒱, ∀ z ∈ imGT 0, X (v + w) z = X v z + X w z}
  add_mem' := fun {X Y} hX hY => by
    intro v w z hz
    show X (v + w) z + Y (v + w) z = _
    rw [hX v w z hz, hY v w z hz]
    show _ = X v z + Y v z + (X w z + Y w z)
    ring
  zero_mem' := fun _ _ _ _ => by show (0 : ℂ) = 0 + 0; ring
  smul_mem' := fun c X hX => by
    intro v w z hz
    show c * X (v + w) z = _
    rw [hX v w z hz]
    show _ = c * X v z + c * X w z
    ring

theorem mem_addOnImGT {X : 𝒱 → ℂ → ℂ} :
    X ∈ (addOnImGT : Submodule ℂ (𝒱 → ℂ → ℂ)) ↔
      ∀ v w : 𝒱, ∀ z ∈ imGT 0, X (v + w) z = X v z + X w z := Iff.rfl

variable {W : VertexOperatorAlgebra 𝒱}

/-- **Every restricted analytic block is additive in the vector slot.** -/
theorem map_restrictImGT_analyticBlocks_le_addOnImGT (W : VertexOperatorAlgebra 𝒱) :
    Submodule.map restrictImGT (analyticBlocks W) ≤ (addOnImGT : Submodule ℂ (𝒱 → ℂ → ℂ)) := by
  rintro _ ⟨F, hF, rfl⟩
  intro v w z hz
  rw [restrictImGT_apply _ hz, restrictImGT_apply _ hz, restrictImGT_apply _ hz]
  exact (hF : IsAnalyticBlock W F).addv v w z

/-! ## Two distinct weights force an inhomogeneous sum -/

/-- Eigenvectors of `L[0]` for **distinct** eigenvalues sum to something inhomogeneous, so the
chosen weight `sqWtOf` falls back to its junk value `0`. -/
theorem sqWtOf_add_eq_zero_of_ne {n m : ℤ} {v w : 𝒱}
    (hv : v ∈ sqWeightSpace W (n : ℂ)) (hw : w ∈ sqWeightSpace W (m : ℂ))
    (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hnm : n ≠ m) : sqWtOf W (v + w) = 0 := by
  classical
  have hnmC : (n : ℂ) ≠ (m : ℂ) := Int.cast_injective.ne hnm
  rw [mem_sqWeightSpace_iff] at hv hw
  have hnot : ¬ ∃ k : ℤ, (v + w) ∈ sqWeightSpace W (k : ℂ) ∧ (v + w) ≠ 0 := by
    rintro ⟨k, hk, -⟩
    rw [mem_sqWeightSpace_iff] at hk
    set a : ℂ := (n : ℂ) with ha
    set b : ℂ := (m : ℂ) with hb
    set c : ℂ := (k : ℂ) with hc
    set p : ℂ := a - c with hp
    set q : ℂ := b - c with hq
    have h3 : a • v + b • w = c • v + c • w := by
      rw [← hv, ← hw, ← map_add, hk, smul_add]
    have h5 : p • v + q • w = 0 := by
      rw [hp, hq, sub_smul, sub_smul, ← sub_eq_zero.mpr h3]
      abel
    have h6 : (p * a) • v + (q * b) • w = 0 := by
      have hcong := congrArg (Lsq W 0) h5
      rw [map_add, map_zero, map_smul, map_smul, hv, hw, smul_smul, smul_smul] at hcong
      exact hcong
    have h7 : (a * p) • v + (a * q) • w = 0 := by
      have hcong := congrArg (fun x : 𝒱 => a • x) h5
      simp only [smul_add, smul_zero, smul_smul] at hcong
      exact hcong
    have h8 : (q * b - a * q) • w = 0 := by
      have hd : (q * b - a * q) • w
          = ((p * a) • v + (q * b) • w) - ((a * p) • v + (a * q) • w) := by
        rw [sub_smul, mul_comm p a]
        abel
      rw [hd, h6, h7, sub_zero]
    have hq0 : q = 0 := by
      rcases smul_eq_zero.mp h8 with hz | hz
      · have hmul : q * (b - a) = 0 := by rw [mul_sub]; linear_combination hz
        rcases mul_eq_zero.mp hmul with h | h
        · exact h
        · exact absurd (sub_eq_zero.mp h).symm hnmC
      · exact absurd hz hw0
    rw [hq0, zero_smul, add_zero] at h5
    rcases smul_eq_zero.mp h5 with hz | hz
    · have hac : a = c := sub_eq_zero.mp hz
      have hbc : b = c := sub_eq_zero.mp hq0
      exact hnmC (hac.trans hbc.symm)
    · exact hv0 hz
  rw [sqWtOf, dif_neg hnot]

/-! ## The pointwise-slash obstruction -/

section Vacuous

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (Mfam : ι → IrrModule W) (h : ι → ℂ)

/-- The trace functions are analytic blocks (repackaged from `torusOnePoint_isAnalyticBlock`). -/
theorem traceBlock_isAnalyticBlock
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24)) (i : ι) :
    IsAnalyticBlock W (traceBlock Mfam h i) :=
  torusOnePoint_isAnalyticBlock (Mfam i).isMod _
    (onePointSupported_of_hasConformalWeight (Mfam i).isMod (hcw i)) (hgr i)

/-- **The rank hypothesis on the pointwise-slash `analyticSlashAmbient` is contradictory under the
stated
hypotheses.**

If it held, the `#ι` independent trace blocks would span the ambient, so the `S`-slash of a trace
block would be a linear combination of trace blocks — hence *additive in the vector slot*.  But
`blockSlash` weights each vector by its own `L[0]`-weight, and `sqWtOf` returns `0` on the
inhomogeneous vector `v + w`; comparing the three values gives `F(v)|S · (1 − D^{−n}) = 0`. -/
theorem not_rank_analyticSlashAmbient_le
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24))
    (hind : TraceIndependent Mfam h)
    {z : ℂ} (hz : z ∈ imGT 0) {n : ℤ} (hn : n ≠ 0) {v w : 𝒱}
    (hv : v ∈ sqWeightSpace W (n : ℂ)) (hv0 : v ≠ 0)
    (hw : w ∈ sqWeightSpace W ((0 : ℤ) : ℂ)) (hw0 : w ≠ 0)
    {i : ι} (hT : traceBlock Mfam h i v (mobiusC ModularGroup.S z) ≠ 0)
    (hD : denomC ModularGroup.S z ^ (-n) ≠ 1) :
    ¬ (Module.rank ℂ (analyticSlashAmbient Mfam h) ≤ (Fintype.card ι : Cardinal)) := by
  intro hrank
  obtain ⟨c, hc⟩ := exists_coeff_of_rank_le
    (traceBlock_mem_analyticSlashAmbient Mfam h hcw hgr)
    (linearIndependent_traceBlock Mfam h hind) hrank
    _ (slash_mem_analyticSlashAmbient Mfam h i)
  have hXadd : restrictImGT (blockSlash W ModularGroup.S (traceBlock Mfam h i))
      ∈ (addOnImGT : Submodule ℂ (𝒱 → ℂ → ℂ)) := by
    rw [hc]
    refine Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ ?_)
    intro x y zz _
    exact (traceBlock_isAnalyticBlock Mfam h hcw hgr j).addv x y zz
  have key := hXadd v w z hz
  rw [restrictImGT_apply _ hz, restrictImGT_apply _ hz, restrictImGT_apply _ hz] at key
  simp only [blockSlash, slashC] at key
  rw [sqWtOf_add_eq_zero_of_ne hv hw hv0 hw0 hn, sqWtOf_eq W hv0 hv, sqWtOf_eq W hw0 hw,
    (traceBlock_isAnalyticBlock Mfam h hcw hgr i).addv v w (mobiusC ModularGroup.S z)] at key
  simp only [neg_zero, zpow_zero, mul_one] at key
  have hfac : traceBlock Mfam h i v (mobiusC ModularGroup.S z)
      * (1 - denomC ModularGroup.S z ^ (-n)) = 0 := by linear_combination key
  rcases mul_eq_zero.mp hfac with hzz | hzz
  · exact hT hzz
  · exact hD (sub_eq_zero.mp hzz).symm

/-- ⚠⚠ **The `finrank` form of `hle` is contradictory too** (`C₂`-cofiniteness makes the ambient
finite-dimensional, so `finrank` and `rank` agree). -/
theorem not_finrank_analyticSlashAmbient_le (hC2 : C2Cofinite W) {z₀ : ℂ} (hz₀ : z₀ ∈ imGT 0)
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24))
    (hind : TraceIndependent Mfam h)
    {z : ℂ} (hz : z ∈ imGT 0) {n : ℤ} (hn : n ≠ 0) {v w : 𝒱}
    (hv : v ∈ sqWeightSpace W (n : ℂ)) (hv0 : v ≠ 0)
    (hw : w ∈ sqWeightSpace W ((0 : ℤ) : ℂ)) (hw0 : w ≠ 0)
    {i : ι} (hT : traceBlock Mfam h i v (mobiusC ModularGroup.S z) ≠ 0)
    (hD : denomC ModularGroup.S z ^ (-n) ≠ 1) :
    ¬ (Module.finrank ℂ (analyticSlashAmbient Mfam h) ≤ Fintype.card ι) := by
  intro hle
  haveI := finiteDimensional_analyticSlashAmbient Mfam h hC2 hz₀
  refine not_rank_analyticSlashAmbient_le Mfam h hcw hgr hind hz hn hv hv0 hw hw0 hT hD ?_
  rw [← Module.finrank_eq_rank]
  exact_mod_cast hle

end Vacuous

/-! ## The earlier workaround — restrict to `L[0]`-homogeneous vectors

`SlashSpannedAtS` only ever asserts an identity **on homogeneous `v`**, so nothing is lost by
running the whole rank argument in the space of functions on the homogeneous points.  There the
obstruction above evaporates: `blockSlash W γ F` *is* additive inside a weight space, because
`sqWtOf` is constant there.  The resulting rank hypothesis is therefore satisfiable — it is the
hypothesis Zhu's Theorems 5.3.2–5.3.3 are actually about. -/

section Repair

/-- The `L[0]`-**homogeneous points** of `𝒱`: an integer weight together with a vector of that
weight (`0` included, so this is a genuine index type, not a subtype of `𝒱`). -/
def SqPt (W : VertexOperatorAlgebra 𝒱) : Type u := Σ n : ℤ, (sqWeightSpace W (n : ℂ))

/-- **Restriction to `L[0]`-homogeneous vectors** (and to `ℍ`), as a `ℂ`-linear map.  This is
`restrictImGT` followed by evaluation at the homogeneous points. -/
noncomputable def sqRestrict (W : VertexOperatorAlgebra 𝒱) :
    (𝒱 → ℂ → ℂ) →ₗ[ℂ] (SqPt W → ℂ → ℂ) where
  toFun F := fun p z => restrictImGT F (p.2 : 𝒱) z
  map_add' F G := by funext p z; exact congrFun (congrFun (map_add restrictImGT F G) _) z
  map_smul' c F := by funext p z; exact congrFun (congrFun (map_smul restrictImGT c F) _) z

/-- Plain evaluation at the homogeneous points (no `ℍ`-restriction), as a linear map. -/
def sqPtEval (W : VertexOperatorAlgebra 𝒱) : (𝒱 → ℂ → ℂ) →ₗ[ℂ] (SqPt W → ℂ → ℂ) where
  toFun F := fun p z => F (p.2 : 𝒱) z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem sqRestrict_eq_comp (W : VertexOperatorAlgebra 𝒱) :
    sqRestrict W = (sqPtEval W).comp restrictImGT := rfl

theorem sqRestrict_apply (W : VertexOperatorAlgebra 𝒱) (F : 𝒱 → ℂ → ℂ) (p : SqPt W) {z : ℂ}
    (hz : z ∈ imGT 0) : sqRestrict W F p z = F (p.2 : 𝒱) z := by
  show restrictImGT F (p.2 : 𝒱) z = _
  exact restrictImGT_apply _ hz

section Traces

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (Mfam : ι → IrrModule W) (h : ι → ℂ)

/-- **The trace blocks stay independent after restriction to homogeneous vectors** — indeed
`TraceIndependent` is *already* a statement about homogeneous vectors only. -/
theorem linearIndependent_sqRestrict_traceBlock (hind : TraceIndependent Mfam h) :
    LinearIndependent ℂ (fun i : ι => sqRestrict W (traceBlock Mfam h i)) := by
  classical
  rw [linearIndependent_iff']
  intro s c hc i hi
  by_contra hne
  have hzero : ∀ (n : ℕ) (v : 𝒱), v ∈ sqWeightSpace W (n : ℂ) → ∀ τ : UpperHalfPlane,
      ∑ j, (if j ∈ s then c j else 0) * traceFun Mfam h j v τ = 0 := by
    intro n v hv τ
    have hpt : ∀ j : ι, (if j ∈ s then c j else 0) * traceFun Mfam h j v τ
        = if j ∈ s then c j * traceFun Mfam h j v τ else 0 := by
      intro j; by_cases hj : j ∈ s <;> simp [hj]
    have hcs : ∑ j, (if j ∈ s then c j else 0) * traceFun Mfam h j v τ
        = ∑ j ∈ s, c j * traceFun Mfam h j v τ := by
      rw [Finset.sum_congr rfl (fun j _ => hpt j), ← Finset.sum_filter,
        Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [hcs]
    have hvz : v ∈ sqWeightSpace W (((n : ℤ) : ℂ)) := by exact_mod_cast hv
    have hval := congrFun (congrFun hc (⟨(n : ℤ), ⟨v, hvz⟩⟩ : SqPt W)) (τ : ℂ)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hval
    refine Eq.trans ?_ hval
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [sqRestrict_apply W _ _ (coe_mem_imGT_zero τ), traceBlock_coe]
  have hzz := hind (fun j => if j ∈ s then c j else 0) hzero
  have hi2 := congrFun hzz i
  simp only [Pi.zero_apply, if_pos hi] at hi2
  exact hne hi2

/-- **`SlashSpannedAtS` from a rank bound — in the repaired (satisfiable) ambient.**

The ambient `𝔄` lives in the space of functions on the **homogeneous** points, which is exactly
where `SlashSpannedAtS` lives; `not_rank_analyticSlashAmbient_le` shows the corresponding
hypothesis on `analyticSlashAmbient` could never hold. -/
theorem slashSpannedAtS_of_sqRank_le (𝔄 : Submodule ℂ (SqPt W → ℂ → ℂ))
    (hind : TraceIndependent Mfam h)
    (htr : ∀ i : ι, sqRestrict W (traceBlock Mfam h i) ∈ 𝔄)
    (hsl : ∀ i : ι, sqRestrict W (blockSlash W ModularGroup.S (traceBlock Mfam h i)) ∈ 𝔄)
    (hrank : Module.rank ℂ 𝔄 ≤ (Fintype.card ι : Cardinal)) :
    SlashSpannedAtS Mfam h := by
  classical
  intro i
  obtain ⟨c, hc⟩ := exists_coeff_of_rank_le htr
    (linearIndependent_sqRestrict_traceBlock Mfam h hind) hrank _ (hsl i)
  refine ⟨c, fun n v hv z hz => ?_⟩
  have hval := congrFun (congrFun hc (⟨n, ⟨v, hv⟩⟩ : SqPt W)) z
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hval
  rw [sqRestrict_apply W _ _ hz] at hval
  rw [hval]
  exact Finset.sum_congr rfl (fun j _ => by rw [sqRestrict_apply W _ _ hz])

/-- **Zhu's modularity theorem from the repaired rank bound**, for every `A ∈ SL₂(ℤ)`. -/
theorem zhu_modularity_of_sqRank_le (𝔄 : Submodule ℂ (SqPt W → ℂ → ℂ))
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24))
    (hinj : Function.Injective (tEigen W h))
    (htr : ∀ i : ι, sqRestrict W (traceBlock Mfam h i) ∈ 𝔄)
    (hsl : ∀ i : ι, sqRestrict W (blockSlash W ModularGroup.S (traceBlock Mfam h i)) ∈ 𝔄)
    (hrank : Module.rank ℂ 𝔄 ≤ (Fintype.card ι : Cardinal)) :
    ZhuModularityAnalytic
      (modularDataOf Mfam h
        (traceSpanning_of_slashSpannedAtS Mfam h hcw hgr
          (slashSpannedAtS_of_sqRank_le Mfam h 𝔄
            (traceIndependent_of_tEigen_injective Mfam h hcw hinj
              (traceNonvanishing_of_onePointSubexp Mfam h hcw hgr)) htr hsl hrank))
        (traceIndependent_of_tEigen_injective Mfam h hcw hinj
          (traceNonvanishing_of_onePointSubexp Mfam h hcw hgr)) hcw) :=
  zhu_modularity_of_spanning Mfam h _ _ hcw

/-! ### The canonical repaired ambient: graded blocks, restricted to homogeneous vectors

`isGradedBlock_blockSlash` says the *graded* block conditions are `SL₂(ℤ)`-stable (with the carried
datum `SqModeWeighted`), so both membership hypotheses are **discharged** and exactly one numerical
residual is left. -/

/-- The graded blocks, restricted to the `L[0]`-homogeneous points. -/
noncomputable def sqGradedAmbient (W : VertexOperatorAlgebra 𝒱) : Submodule ℂ (SqPt W → ℂ → ℂ) :=
  Submodule.map (sqRestrict W) (gradedBlocks W)

theorem sqRestrict_traceBlock_mem_sqGradedAmbient
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24)) (i : ι) :
    sqRestrict W (traceBlock Mfam h i) ∈ sqGradedAmbient W :=
  ⟨traceBlock Mfam h i, traceBlock_isGradedBlock Mfam h hcw hgr i, rfl⟩

theorem sqRestrict_slash_mem_sqGradedAmbient (hwt : SqModeWeighted W)
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24)) (i : ι) :
    sqRestrict W (blockSlash W ModularGroup.S (traceBlock Mfam h i)) ∈ sqGradedAmbient W :=
  ⟨blockSlash W ModularGroup.S (traceBlock Mfam h i),
    isGradedBlock_blockSlash (traceBlock_isGradedBlock Mfam h hcw hgr i) hwt ModularGroup.S, rfl⟩

/-! ### The other canonical repaired ambient: analytic blocks + the slashes

This one keeps Zhu's Theorem 5.3.2: `sqRestrict = sqPtEval ∘ restrictImGT`, so the analytic
summand is the image of the space `exists_finrank_analyticBlocks_le` bounds, and adding `#ι`
slashes by fiat keeps it finite-dimensional.  Unlike `analyticSlashAmbient`, the rank hypothesis
here is **not** contradictory (`not_rank_analyticSlashAmbient_le` does not apply, because
`sqPtEval` forgets exactly the inhomogeneous vectors that carried the obstruction). -/

/-- The `L[0]`-homogeneous restrictions of the analytic blocks, together with the `S`-slashes. -/
noncomputable def sqAnalyticSlashAmbient : Submodule ℂ (SqPt W → ℂ → ℂ) :=
  Submodule.map (sqRestrict W) (analyticBlocks W)
    ⊔ Submodule.span ℂ (Set.range fun i : ι =>
        sqRestrict W (blockSlash W ModularGroup.S (traceBlock Mfam h i)))

theorem sqRestrict_traceBlock_mem_sqAnalyticSlashAmbient
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24)) (i : ι) :
    sqRestrict W (traceBlock Mfam h i) ∈ sqAnalyticSlashAmbient Mfam h :=
  Submodule.mem_sup_left ⟨traceBlock Mfam h i, traceBlock_isAnalyticBlock Mfam h hcw hgr i, rfl⟩

theorem sqRestrict_slash_mem_sqAnalyticSlashAmbient (i : ι) :
    sqRestrict W (blockSlash W ModularGroup.S (traceBlock Mfam h i))
      ∈ sqAnalyticSlashAmbient Mfam h :=
  Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)

/-- **Zhu's Theorem 5.3.2 survives the repair**: the repaired analytic ambient is still
finite-dimensional, unconditionally in `C₂`-cofiniteness. -/
theorem finiteDimensional_sqAnalyticSlashAmbient (hC2 : C2Cofinite W) {z₀ : ℂ}
    (hz₀ : z₀ ∈ imGT 0) : FiniteDimensional ℂ (sqAnalyticSlashAmbient Mfam h) := by
  obtain ⟨g, hfd, -⟩ := exists_finrank_analyticBlocks_le (W := W) hC2 hz₀
  haveI := hfd
  have hmapeq : Submodule.map (sqRestrict W) (analyticBlocks W)
      = Submodule.map (sqPtEval W) (Submodule.map restrictImGT (analyticBlocks W)) := by
    rw [sqRestrict_eq_comp, Submodule.map_comp]
  haveI : FiniteDimensional ℂ (Submodule.map (sqRestrict W) (analyticBlocks W)) := by
    rw [hmapeq]; infer_instance
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun i : ι =>
      sqRestrict W (blockSlash W ModularGroup.S (traceBlock Mfam h i)))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  exact Submodule.finiteDimensional_sup _ _

/-- **Zhu's modularity theorem from the repaired analytic rank bound.** -/
theorem zhu_modularity_of_sqAnalyticRank_le
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24))
    (hinj : Function.Injective (tEigen W h))
    (hrank : Module.rank ℂ (sqAnalyticSlashAmbient Mfam h) ≤ (Fintype.card ι : Cardinal)) :
    ZhuModularityAnalytic
      (modularDataOf Mfam h
        (traceSpanning_of_slashSpannedAtS Mfam h hcw hgr
          (slashSpannedAtS_of_sqRank_le Mfam h (sqAnalyticSlashAmbient Mfam h)
            (traceIndependent_of_tEigen_injective Mfam h hcw hinj
              (traceNonvanishing_of_onePointSubexp Mfam h hcw hgr))
            (sqRestrict_traceBlock_mem_sqAnalyticSlashAmbient Mfam h hcw hgr)
            (sqRestrict_slash_mem_sqAnalyticSlashAmbient Mfam h) hrank))
        (traceIndependent_of_tEigen_injective Mfam h hcw hinj
          (traceNonvanishing_of_onePointSubexp Mfam h hcw hgr)) hcw) :=
  zhu_modularity_of_spanning Mfam h _ _ hcw

/-- **Zhu's modularity theorem from one satisfiable numerical bound.**

Everything is discharged except `rank (sqGradedAmbient W) ≤ #Φ(𝒱)` — Zhu's Theorems 5.3.2–5.3.3
in the space they actually live in.  Compare `not_rank_analyticSlashAmbient_le`: the pointwise-slash
reduction attaches the same number to a space in which it can never hold. -/
theorem zhu_modularity_of_sqGradedRank_le
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24))
    (hwt : SqModeWeighted W)
    (hinj : Function.Injective (tEigen W h))
    (hrank : Module.rank ℂ (sqGradedAmbient W) ≤ (Fintype.card ι : Cardinal)) :
    ZhuModularityAnalytic
      (modularDataOf Mfam h
        (traceSpanning_of_slashSpannedAtS Mfam h hcw hgr
          (slashSpannedAtS_of_sqRank_le Mfam h (sqGradedAmbient W)
            (traceIndependent_of_tEigen_injective Mfam h hcw hinj
              (traceNonvanishing_of_onePointSubexp Mfam h hcw hgr))
            (sqRestrict_traceBlock_mem_sqGradedAmbient Mfam h hcw hgr)
            (sqRestrict_slash_mem_sqGradedAmbient Mfam h hwt hcw hgr) hrank))
        (traceIndependent_of_tEigen_injective Mfam h hcw hinj
          (traceNonvanishing_of_onePointSubexp Mfam h hcw hgr)) hcw) :=
  zhu_modularity_of_spanning Mfam h _ _ hcw

end Traces

end Repair

end VOA
