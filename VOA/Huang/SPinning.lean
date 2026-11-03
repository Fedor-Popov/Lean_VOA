/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.VerlindeRhoReduction
import VOA.Huang.ZhuModData

/-!
# The `S`-matrix of `COne.IsModularData` is unique

`VOA.Classification.COne.ModularData.IsModularData` carries the clause
`S_pinned : D.SPinned D.S` — Zhu's `S`-law on the one-point function of every square-bracket
homogeneous state (Zhu 1996, (5.3.18a) at `γ = S`):

`T_a(v, -1/τ) = τⁿ Σ_b S_ab T_b(v, τ)`, `v ∈ V_[n]`.

Characters alone (`S_transform`, the case `v = 𝟙`) do not determine `S`, since `ch_M = ch_{M'}`
(`VOA.Huang.HuangModular.isModularDataWeak_perturbS`). One-point functions do: those of
inequivalent irreducibles are linearly independent (`traceIndependent_of_bottomSeparation`,
with Zhu's bijection, hence PBW). This file proves the resulting uniqueness.

## Main results

* `famOf D hD` — the labelled modules of `D` as a bundled family of irreducibles;
  `D.trace = traceFun (famOf D hD) (hOf D)` definitionally (`trace_eq_traceFun`).
* `traceIndependent_of_isModularData` — `Pr`-parametric trace independence for `D.module`.
* `S_unique_of_pinned` — two matrices satisfying `D.SPinned` coincide (`Pr`, `C₂`).
* `S_eq_of_pinned` — for nice `V` (PBW from `VOA.pbw`): any `S` with `D.SPinned S` is `D.S`.
* `S_eq_repS` — if Zhu's modular data `D'` (library `VOA.ModularData`) has the same trace
  functions as `D`, then `D.S = D'.repS`: the `S`-matrix of `IsModularData` IS Zhu's `ρ(S)`.
* `S_transform_of_pinned` — the character law is the `v = 𝟙` case of the pinning clause.
-/

open Complex Finset Module

noncomputable section

namespace VOA.Huang.SPinning

open VOA VOA.Classification.COne VOA.VHat VOA.VHat.DLM3 VOA.Huang.ZhuModData
open scoped MatrixGroups

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}

/-! ## §1 The labelled family as bundled irreducibles -/

/-- The labelled modules of `D`, bundled as irreducibles. -/
def famOf (D : VOA.Classification.COne.ModularData V) (hD : D.IsModularData) :
    D.ι → IrrModule V :=
  fun a => ⟨D.carrier a, D.module a, hD.irred a⟩

/-- The conformal weights of `D`, as complex numbers. -/
def hOf (D : VOA.Classification.COne.ModularData V) : D.ι → ℂ := fun a => (D.h a : ℂ)

theorem hasConformalWeight_famOf (D : VOA.Classification.COne.ModularData V)
    (hD : D.IsModularData) (a : D.ι) :
    HasConformalWeight (famOf D hD a).isMod (hOf D a) :=
  ⟨hD.weight_lowest a, hD.weight_support a⟩

theorem trace_eq_traceFun (D : VOA.Classification.COne.ModularData V) (hD : D.IsModularData)
    (a : D.ι) (v : 𝒱) (τ : UpperHalfPlane) :
    D.trace a v τ = traceFun (famOf D hD) (hOf D) a v τ := rfl

/-- The lowest-weight module attached to a label. -/
def lwOfLabel (D : VOA.Classification.COne.ModularData V) (hD : D.IsModularData) (i : D.ι) :
    LWModule V where
  carrier := D.carrier i
  isMod := D.module i
  h := hOf D i
  isLow := (hasConformalWeight_famOf D hD i).2
  realized := (hasConformalWeight_famOf D hD i).1

/-! ## §2 Trace independence -/

/-- **Trace independence for the labelled family**, with the PBW datum explicit. -/
theorem traceIndependent_of_isModularData
    (Pr : BottomProjection (parabolicRepOfAMod V (regularAMod V)))
    (hC2 : C2Cofinite V) (D : VOA.Classification.COne.ModularData V) (hD : D.IsModularData) :
    TraceIndependent (famOf D hD) (hOf D) := by
  refine traceIndependent_of_bottomSeparation (famOf D hD) (hOf D)
    (hasConformalWeight_famOf D hD)
    (fun i => onePointSubexp_of_c2 V (famOf D hD i).isMod (hasConformalWeight_famOf D hD i)
      (vacuumGradeZero_holds V) hC2)
    (fun i => LWBottomRecovery.isSimpleAMod_toAMod_of_irreducible
      (lwOfLabel D hD i) (hD.irred i)) ?_
  intro j k hjk _
  constructor
  intro e
  let Pj : IrrLWModule V := ⟨lwOfLabel D hD j, hD.irred j⟩
  let Pk : IrrLWModule V := ⟨lwOfLabel D hD k, hD.irred k⟩
  have hf : forwardMapIrr V (Quotient.mk (IrrLWModule.setoid V) Pj) =
      forwardMapIrr V (Quotient.mk (IrrLWModule.setoid V) Pk) := by
    rw [forwardMapIrr_mk, forwardMapIrr_mk]
    exact Quotient.sound ⟨e⟩
  have he := Quotient.exact ((zhuBijective Pr).1 hf)
  exact hjk (hD.distinct j k he)

/-! ## §3 Uniqueness of `S` -/

theorem autFactor_S' (τ : UpperHalfPlane) : autFactor ModularGroup.S τ = τ := by
  simp [autFactor, ModularGroup.S]

/-- The pinning clause is Zhu's `RealisesLaw` at `γ = S` for the labelled family. -/
theorem realisesLaw_of_pinned (D : VOA.Classification.COne.ModularData V) (hD : D.IsModularData)
    {S : D.ι → D.ι → ℂ} (hS : D.SPinned S) :
    RealisesLaw (famOf D hD) (hOf D) ModularGroup.S S := by
  intro n v hv a τ
  rw [autFactor_S']
  exact hS n v hv a τ

/-- **The pinning clause determines `S`** (`Pr`-parametric, no project axiom). -/
theorem S_unique_of_pinned
    (Pr : BottomProjection (parabolicRepOfAMod V (regularAMod V)))
    (hC2 : C2Cofinite V) (D : VOA.Classification.COne.ModularData V) (hD : D.IsModularData)
    {S S' : D.ι → D.ι → ℂ} (hS : D.SPinned S) (hS' : D.SPinned S') : S = S' :=
  rho_unique (famOf D hD) (hOf D) (traceIndependent_of_isModularData Pr hC2 D hD)
    (realisesLaw_of_pinned D hD hS) (realisesLaw_of_pinned D hD hS')

/-- **For a nice VOA, the `S`-matrix of `IsModularData` is the unique pinned matrix**
(PBW discharged by `VOA.pbw`). -/
theorem S_eq_of_pinned (hV : Nice V) (D : VOA.Classification.COne.ModularData V)
    (hD : D.IsModularData) {S : D.ι → D.ι → ℂ} (hS : D.SPinned S) : S = D.S := by
  obtain ⟨Pr⟩ := zhuPBWBottomInput_of_pbw 𝒱 V
  exact S_unique_of_pinned Pr hV.1.c2Cofinite D hD hS hD.S_pinned

/-- **The `S`-matrix of `IsModularData` is Zhu's `ρ(S)`**: if a library Zhu modular data
`D'` on the same labels has the same trace functions as `D` (e.g. the same modules and weights),
then `D.S = D'.repS`. -/
theorem S_eq_repS (Pr : BottomProjection (parabolicRepOfAMod V (regularAMod V)))
    (hC2 : C2Cofinite V) (D : VOA.Classification.COne.ModularData V) (hD : D.IsModularData)
    (D' : VOA.ModularData V D.ι) (hZ : ZhuModularityAnalytic D')
    (htr : ∀ (a : D.ι) (v : 𝒱) (τ : UpperHalfPlane),
      traceFun D'.Mfam D'.h a v τ = D.trace a v τ) :
    D.S = D'.repS := by
  refine S_unique_of_pinned Pr hC2 D hD hD.S_pinned ?_
  intro n v hv a τ
  have hlaw := hZ ModularGroup.S n v hv a τ
  rw [autFactor_S', D'.rep_S] at hlaw
  simp only [Matrix.of_apply, htr] at hlaw
  exact hlaw

/-- The character law `S_transform` is the `v = 𝟙` case of the pinning clause (so the
`S_transform` field of `IsModularData` is redundant, kept for its consumers). -/
theorem S_transform_of_pinned (D : VOA.Classification.COne.ModularData V)
    (hD : D.IsModularData) {S : D.ι → D.ι → ℂ} (hS : D.SPinned S) (a : D.ι) (τ : ℂ)
    (hτ : 0 < τ.im) (hC2 : C2Cofinite V) :
    D.ch a (-1 / τ) = ∑ b, S a b * D.ch b τ := by
  have hτ' : 0 < (-1 / τ).im := by
    have := (ModularGroup.S • (⟨τ, hτ⟩ : UpperHalfPlane)).im_pos
    rw [UpperHalfPlane.modular_S_smul] at this
    rw [div_eq_mul_inv, neg_one_mul, ← inv_neg]
    exact this
  have hSτ : (ModularGroup.S • (⟨τ, hτ⟩ : UpperHalfPlane)) = ⟨-1 / τ, hτ'⟩ := by
    ext; rw [UpperHalfPlane.modular_S_smul]; change (-τ)⁻¹ = -1 / τ; field_simp
  -- `ch = trace at 𝟙`, by uniqueness of `HasSum`
  have hch : ∀ b (σ : ℂ) (hσ : 0 < σ.im), D.ch b σ = D.trace b V.vacuum ⟨σ, hσ⟩ := by
    intro b σ hσ
    refine (hD.char b σ hσ).unique ?_
    exact hasSum_character (D.module b) (hasConformalWeight_famOf D hD b) hC2 ⟨σ, hσ⟩
  have hlaw := hS 0 V.vacuum (vacuum_mem_sqWeightSpace_zero V) a ⟨τ, hτ⟩
  rw [hSτ, pow_zero, one_mul] at hlaw
  rw [hch a _ hτ', hlaw]
  exact Finset.sum_congr rfl fun b _ => by rw [hch b τ hτ]

end VOA.Huang.SPinning
