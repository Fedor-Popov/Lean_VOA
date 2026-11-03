/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.GradedBlock
import VOA.Modularity.TraceSpanningS
import VOA.Modularity.TraceNonvanish

/-!
# Reading off `ρ`: Zhu's modularity from a single spanning statement

Everything analytic is in place:

* the trace functions **are** genus-one blocks (`torusOnePoint_isAnalyticBlock`, `toGradedBlock`);
* the block conditions are **`SL₂(ℤ)`-stable** (`isGradedBlock_blockSlash`).

So the *only* thing separating this repo from Zhu's Theorem 5.3.8 is the **spanning half** of Zhu
Theorem 5.3.3: that every genus-one block is a linear combination of the trace functions
(`BlockSpannedByTraces`).  That is the statement whose proof consumes rationality and the
`A(𝒱)`-bijection; it is *not* an analytic statement, and it is carried here by name.

  `traceSpanning_of_blockSpanned` — `TraceSpanning` for **every** `A ∈ SL₂(ℤ)`;
  `zhu_modularity_of_blockSpanned` — Zhu's 5.3.18a for every `A`, every homogeneous `v`,
  every `τ`.

Both routes are provided.  `traceSpanning_of_blockSpanned` uses slash-stability at every `γ` and
the conceptual spanning statement `BlockSpannedByTraces`; `traceSpanning_of_slashSpannedAtS` uses
`Modularity.TraceSpanningS.traceSpanning_of_S` and needs the spanning statement **only for the
`S`-slashes** — on that route `SqModeWeighted` is not needed at all, since nothing has to be
recognised as a block.  `slashSpannedAtS_of_blockSpanned` connects them.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  Named data consumed: `HasConformalWeight`,
`OnePointSubexp` (growth), `SqModeWeighted` (Zhu's square-bracket mode grading),
`BlockSpannedByTraces` (Zhu Thm 5.3.3), and — for the *independence* half — `tEigen` injectivity
and `TraceNonvanishing`, already isolated in `Modularity.TraceIndependence`.
-/

namespace VOA

open Complex
open scoped BigOperators MatrixGroups

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {W : VertexOperatorAlgebra 𝒱}

/-- **The trace function of `M_i`, as a block**: the analytic evaluation of `v ↦ 𝒵_{M_i}(v; q)`. -/
noncomputable def traceBlock (Mfam : ι → IrrModule W) (h : ι → ℂ) (i : ι) : 𝒱 → ℂ → ℂ :=
  anEval (torusOnePointHom (Mfam i).isMod) (h i - W.centralCharge / 24)

variable (Mfam : ι → IrrModule W) (h : ι → ℂ)

/-- `traceBlock` restricted to `ℍ` **is** `traceFun`. -/
theorem traceBlock_coe (i : ι) (v : 𝒱) (τ : UpperHalfPlane) :
    traceBlock Mfam h i v (τ : ℂ) = traceFun Mfam h i v τ := by
  rw [traceBlock, anEval_of_mem _ _ _ (coe_mem_imGT_zero τ), qEvalC_coe]
  rfl

theorem denomC_coe (A : SL(2, ℤ)) (τ : UpperHalfPlane) :
    denomC A (τ : ℂ) = autFactor A τ := rfl

/-- **The trace functions are genus-one blocks in slash-stable normal form.** -/
theorem traceBlock_isGradedBlock (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hsub : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24)) (i : ι) :
    IsGradedBlock W (traceBlock Mfam h i) :=
  (torusOnePoint_isAnalyticBlock (Mfam i).isMod _
    (onePointSupported_of_hasConformalWeight (Mfam i).isMod (hcw i)) (hsub i)).toGradedBlock

/-- **The nonvanishing datum is free given the growth datum.**  `𝒵_M(𝟙;q)` *is* the character
(`torusOnePoint_vacuum`), so the `v = 𝟙` instance of `OnePointSubexp` is exactly
`SubexponentialCoeffs`, which makes the character summable and — its coefficients being dimensions
with a positive leading one — nonzero on the imaginary axis (`Modularity.TraceNonvanish`). -/
theorem traceNonvanishing_of_onePointSubexp (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hsub : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24)) :
    TraceNonvanishing Mfam h := by
  refine traceNonvanishing_of_qSummable Mfam h hcw (fun i t ht => ?_)
  refine qSummable_gradedDim (Mfam i).isMod (h i - W.centralCharge / 24) ?_ (imAxis t ht)
  have hvac := hsub i W.vacuum
  rwa [torusOnePoint_vacuum, torusPartition] at hvac

/-- The character is nonzero on the imaginary axis — the `hne` datum, also free from the growth
datum. -/
theorem traceFun_vacuum_ne_zero (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hsub : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24)) (i : ι) :
    ∃ τ : UpperHalfPlane, traceFun Mfam h i W.vacuum τ ≠ 0 := by
  refine ⟨imAxis 1 one_pos, ?_⟩
  rw [traceFun, torusOnePoint_vacuum, torusPartition]
  refine qEvalAt_gradedDim_ne_zero (Mfam i).isMod (h i) (hcw i) 1 one_pos ?_
  refine qSummable_gradedDim (Mfam i).isMod (h i - W.centralCharge / 24) ?_ (imAxis 1 one_pos)
  have hvac := hsub i W.vacuum
  rwa [torusOnePoint_vacuum, torusPartition] at hvac

/-- **The core read-off.**  If the `γ`-slash of each trace block lies in the span of the trace
blocks with coefficient matrix `c`, then `c` realises Zhu's transformation law at `γ`.  Everything
between the two statements is the dictionary `traceBlock_coe` / `mobiusC_coe` / `denomC_coe`. -/
theorem realisesLaw_of_slashSpanned (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hsub : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24))
    (A : SL(2, ℤ)) (c : ι → ι → ℂ)
    (hc : ∀ i : ι, ∀ (n : ℤ) (v : 𝒱), v ∈ sqWeightSpace W (n : ℂ) → ∀ z ∈ imGT 0,
      blockSlash W A (traceBlock Mfam h i) v z = ∑ j, c i j * traceBlock Mfam h j v z) :
    RealisesLaw Mfam h A c := by
  intro n v hv i τ
  have hvz : v ∈ sqWeightSpace W (((n : ℕ) : ℤ) : ℂ) := by
    have hcast : ((((n : ℕ) : ℤ)) : ℂ) = ((n : ℕ) : ℂ) := by push_cast; ring
    rwa [hcast]
  have hz : (τ : ℂ) ∈ imGT 0 := coe_mem_imGT_zero τ
  have hkey := hc i ((n : ℕ) : ℤ) v hvz (τ : ℂ) hz
  have hslash := isSlashOf_blockSlash W A
    (F := traceBlock Mfam h i) (traceBlock_isGradedBlock Mfam h hcw hsub i).zerov
  rw [hslash ((n : ℕ) : ℤ) v hvz (τ : ℂ) hz, slashC, mobiusC_coe, denomC_coe,
    traceBlock_coe] at hkey
  have hne : autFactor A τ ≠ 0 := autFactor_ne_zero A τ
  have hpow : autFactor A τ ^ (-(((n : ℕ) : ℤ))) = (autFactor A τ ^ n)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  rw [hpow] at hkey
  have hsum : ∑ j, c i j * traceBlock Mfam h j v (τ : ℂ)
      = ∑ j, c i j * traceFun Mfam h j v τ :=
    Finset.sum_congr rfl (fun j _ => by rw [traceBlock_coe])
  rw [hsum] at hkey
  have hnz : autFactor A τ ^ n ≠ 0 := pow_ne_zero _ hne
  field_simp at hkey
  rw [hkey]

/-- **Zhu's Theorem 5.3.3, spanning half**: every genus-one block is a linear combination of the
trace functions.  This is the one remaining input to Zhu's modularity theorem, and it is *not*
analytic — it is where rationality and the `A(𝒱)`-bijection enter. -/
def BlockSpannedByTraces (Mfam : ι → IrrModule W) (h : ι → ℂ) : Prop :=
  ∀ G : 𝒱 → ℂ → ℂ, IsGradedBlock W G → ∃ c : ι → ℂ,
    ∀ (n : ℤ) (v : 𝒱), v ∈ sqWeightSpace W (n : ℂ) → ∀ z ∈ imGT 0,
      G v z = ∑ j, c j * traceBlock Mfam h j v z

/-- **`TraceSpanning` for every `A ∈ SL₂(ℤ)`**, from the slash-stability of the block
conditions together with the spanning half of Zhu Thm 5.3.3. -/
theorem traceSpanning_of_blockSpanned (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hsub : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24))
    (hwt : SqModeWeighted W) (hspan : BlockSpannedByTraces Mfam h) :
    TraceSpanning Mfam h := by
  classical
  intro A
  have hblk : ∀ i : ι, IsGradedBlock W (blockSlash W A (traceBlock Mfam h i)) := fun i =>
    isGradedBlock_blockSlash (traceBlock_isGradedBlock Mfam h hcw hsub i) hwt A
  exact ⟨fun i => Classical.choose (hspan _ (hblk i)),
    realisesLaw_of_slashSpanned Mfam h hcw hsub A _
      (fun i => Classical.choose_spec (hspan _ (hblk i)))⟩

/-! ## The `S`-only route

`Modularity.TraceSpanningS.traceSpanning_of_S` shows that the law at the single matrix `S` already
gives `TraceSpanning`.  Feeding the core read-off at `γ = S` therefore gives Zhu's theorem from a
spanning statement needed **only for the `S`-slashes** — and, notably, **without `SqModeWeighted`**:
the slash-stability of the block conditions is not used, since nothing has to be recognised as a
block. -/

/-- The spanning statement, needed only at `γ = S`. -/
def SlashSpannedAtS (Mfam : ι → IrrModule W) (h : ι → ℂ) : Prop :=
  ∀ i : ι, ∃ c : ι → ℂ, ∀ (n : ℤ) (v : 𝒱), v ∈ sqWeightSpace W (n : ℂ) → ∀ z ∈ imGT 0,
    blockSlash W ModularGroup.S (traceBlock Mfam h i) v z
      = ∑ j, c j * traceBlock Mfam h j v z

/-- **`BlockSpannedByTraces` (with the mode grading) implies the `S`-only datum.** -/
theorem slashSpannedAtS_of_blockSpanned
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hsub : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24))
    (hwt : SqModeWeighted W) (hspan : BlockSpannedByTraces Mfam h) :
    SlashSpannedAtS Mfam h := fun i =>
  hspan _ (isGradedBlock_blockSlash (traceBlock_isGradedBlock Mfam h hcw hsub i) hwt
    ModularGroup.S)

/-- **`TraceSpanning` from the `S`-slash spanning statement alone** — `SqModeWeighted` is not
needed on this route. -/
theorem traceSpanning_of_slashSpannedAtS (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hsub : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24))
    (hS : SlashSpannedAtS Mfam h) : TraceSpanning Mfam h := by
  classical
  refine traceSpanning_of_S Mfam h hcw ⟨fun i => Classical.choose (hS i), ?_⟩
  exact realisesLaw_of_slashSpanned Mfam h hcw hsub ModularGroup.S _
    (fun i => Classical.choose_spec (hS i))

/-- **Zhu's modularity theorem 5.3.8 (5.3.18a) for every `A ∈ SL₂(ℤ)`**, from:
the analytic theory proved in this repo (the trace functions are blocks, and the block conditions
are `SL₂(ℤ)`-stable), plus the four named data — the growth datum, Zhu's square-bracket mode
grading, the spanning half of Zhu Thm 5.3.3, and the `T`-eigenvalue separation that discharges
independence. -/
theorem zhu_modularity_of_blockSpanned (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hsub : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24))
    (hwt : SqModeWeighted W) (hspan : BlockSpannedByTraces Mfam h)
    (hinj : Function.Injective (tEigen W h)) (hnv : TraceNonvanishing Mfam h) :
    ZhuModularityAnalytic
      (modularDataOf Mfam h (traceSpanning_of_blockSpanned Mfam h hcw hsub hwt hspan)
        (traceIndependent_of_tEigen_injective Mfam h hcw hinj hnv) hcw) :=
  zhu_modularity_of_spanning Mfam h (traceSpanning_of_blockSpanned Mfam h hcw hsub hwt hspan)
    (traceIndependent_of_tEigen_injective Mfam h hcw hinj hnv) hcw

/-- **Zhu's modularity from the `S`-slash spanning statement alone** — the minimal-hypothesis
form: no `SqModeWeighted`, no slash-stability, just the `S`-law plus the independence data. -/
theorem zhu_modularity_of_slashSpannedAtS (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hsub : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24))
    (hS : SlashSpannedAtS Mfam h)
    (hinj : Function.Injective (tEigen W h)) (hnv : TraceNonvanishing Mfam h) :
    ZhuModularityAnalytic
      (modularDataOf Mfam h (traceSpanning_of_slashSpannedAtS Mfam h hcw hsub hS)
        (traceIndependent_of_tEigen_injective Mfam h hcw hinj hnv) hcw) :=
  zhu_modularity_of_spanning Mfam h (traceSpanning_of_slashSpannedAtS Mfam h hcw hsub hS)
    (traceIndependent_of_tEigen_injective Mfam h hcw hinj hnv) hcw

/-- The `S`-matrix produced by the above — the one genuinely new piece of modular data. -/
noncomputable def rhoS_of_blockSpanned (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hsub : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24))
    (hwt : SqModeWeighted W) (hspan : BlockSpannedByTraces Mfam h) : ι → ι → ℂ :=
  rhoOf Mfam h (traceSpanning_of_blockSpanned Mfam h hcw hsub hwt hspan) ModularGroup.S

theorem rhoS_of_blockSpanned_spec (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hsub : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24))
    (hwt : SqModeWeighted W) (hspan : BlockSpannedByTraces Mfam h) :
    RealisesLaw Mfam h ModularGroup.S (rhoS_of_blockSpanned Mfam h hcw hsub hwt hspan) :=
  rhoOf_spec Mfam h (traceSpanning_of_blockSpanned Mfam h hcw hsub hwt hspan) ModularGroup.S

end

end VOA
