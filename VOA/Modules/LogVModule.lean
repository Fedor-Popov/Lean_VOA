/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.WeakModule
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Logarithmic `𝒱`-modules  (McRae Def. 2.4; Huang–Lepowsky–Zhang)

The **logarithmic** (grading-restricted generalized) `𝒱`-module: a weak module graded by
finite-dimensional *generalized* `L₀`-eigenspaces — `L₀` may have Jordan blocks — bounded below.
This is the "grading-restricted generalized module" of Huang–Lepowsky–Zhang (arXiv:1012.4193) and
McRae (Def. 2.4 of *On rationality for `C₂`-cofinite vertex operator algebras*), the objects of
the category `C` in McRae's rationality theorem, and the natural home of Miyamoto's pseudo-trace
modularity.  `OrdVModule` is the `L₀`-semisimple special case (`OrdVModule.toLog`;
characterization `LogVModule.IsL0Semisimple`).

## The module hierarchy (literature ⇆ this library)

weak ⊇ admissible (ℕ-gradable) ⊇ … ⊇ **logarithmic** ⊇ ordinary:

* `WeakModule` — no grading at all (McRae: "all axioms … except all properties related to the
  grading").
* *admissible* — an auxiliary `ℕ`-grading with the mode-shift axiom, **data** rather than
  property, and not unique; no library-wide structure (the auxiliary `ZGradedWeakModule`
  carries exactly this shape).
* `LogVModule` (this file) — `ℂ`-graded by generalized `L₀`-eigenspaces: the grading is
  **property**, not data (`weight_eq_maxGenEigenspace` below), finite-dimensional pieces,
  bounded below.
* `OrdVModule` — the same with honest eigenspaces (`L₀` semisimple).

HLZ's two intermediate relaxations (generalized modules with no finiteness, lower-bounded
generalized modules) are deliberately **not** defined here; they are scaffolding for
tensor-product constructions and can be added when a theorem consumes them.

## The boundedness convention (a recorded decision)

McRae's grading restriction is *per-coset* truncation: for each `h`, `W_[h+n] = 0` for `n ∈ ℤ`
sufficiently negative.  This file instead mirrors `OrdVModule.boundedBelow` — a **global** bound
`∃ B, Re α ≥ B` on nonzero pieces — which is strictly stronger (a direct sum over infinitely many
`ℤ`-cosets with lowest weights drifting to `−∞` is McRae-admissible but excluded here).  The two
agree on modules with weights in finitely many cosets, in particular whenever a
`HasConformalWeight`-type condition holds — the regime of every modularity application.  Chosen
for field-for-field parallelism with `OrdVModule`, so that `IsL0Semisimple` exactly characterizes
factoring through `OrdVModule` (`toOrd_toLog`/`toLog_toOrd`).  If McRae-fidelity ever bites,
per-coset truncation is a later Prop-level weakening.

## What is proved here (`sorry`-free / axiom-clean)

* `LogVModule` — the structure, one field changed from `OrdVModule`:
  `weight_le_maxGenEigenspace` replaces `L0_weight`.
* `maxGenEigenspace_le_weight` / `weight_eq_maxGenEigenspace` — the carried grading **is**
  the full generalized eigenspace decomposition (via `Module.End.independent_maxGenEigenspace`),
  so `weight` is canonical, not extra data.  In particular `L0op_mem_weight` (stability).
* `OrdVModule.toLog`, `LogVModule.IsL0Semisimple`, `LogVModule.toOrd` — the semisimple case
  embeds, and the roundtrips `toOrd_toLog` / `toLog_toOrd` are definitional.
* `L0ss` / `L0nil` — the semisimple/nilpotent decomposition `L₀ = L₀^ss + L₀^nil`
  (`L0ss_add_L0nil`), with `L0ss` acting as `α` on `M_[α]` (`L0ss_apply_of_mem`), `L0nil`
  locally nilpotent (`L0nil_locNilpotent`), and the two commuting (`L0ss_comm_L0nil`).
  This is the payload of the logarithmic theory: log characters are
  `tr q^{L₀^ss} e^{2πiτ·L₀^nil}` and pseudo-traces consume the split.
-/

namespace VOA

open Module (End)
open scoped BigOperators

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- A **logarithmic `𝒱`-module** (grading-restricted generalized module; McRae Def. 2.4, HLZ):
a weak module with an internal `ℂ`-grading by finite-dimensional *generalized*
`L₀`-eigenspaces, bounded below in the real part.  `L₀` may act with Jordan blocks; the
`L₀`-semisimple case is `OrdVModule` (see `OrdVModule.toLog`). -/
structure LogVModule (W : VertexOperatorAlgebra 𝒱) (M : Type v)
    [AddCommGroup M] [Module ℂ M] extends WeakModule W M where
  /-- The complex grading `M = ⊕_α M_[α]`, as a family of `ℂ`-subspaces. -/
  weight : ℂ → Submodule ℂ M
  /-- The grading is a genuine internal direct-sum decomposition. -/
  isInternal : DirectSum.IsInternal weight
  /-- **McRae Def. 2.4(5), one inclusion.**  Each piece lies in the generalized
  `L₀`-eigenspace: every `x ∈ M_[α]` satisfies `(L₀ − α)^k x = 0` for some `k`.
  The reverse inclusion is automatic (`maxGenEigenspace_le_weight`). -/
  weight_le_maxGenEigenspace :
    ∀ α : ℂ, weight α ≤ (mode (YM W.conformalVector) 1).maxGenEigenspace α
  /-- Each homogeneous piece `M_[α]` is finite-dimensional (grading restriction). -/
  finrank : ∀ α, FiniteDimensional ℂ (weight α)
  /-- Bounded below: `Re α` is bounded below on the nonzero pieces (see the module
  docstring for the comparison with McRae's per-coset truncation). -/
  boundedBelow : ∃ B : ℝ, ∀ α : ℂ, weight α ≠ ⊥ → B ≤ α.re

namespace LogVModule

variable {W : VertexOperatorAlgebra 𝒱} {M : Type v} [AddCommGroup M] [Module ℂ M]

/-- The `L₀` operator `mode (Y_M ω) 1 : End ℂ M` on a logarithmic module. -/
noncomputable def L0op (N : LogVModule W M) : Module.End ℂ M :=
  mode (N.YM W.conformalVector) 1

theorem weight_le_maxGenEigenspace' (N : LogVModule W M) (α : ℂ) :
    N.weight α ≤ N.L0op.maxGenEigenspace α :=
  N.weight_le_maxGenEigenspace α

/-- On `M_[α]`, `L₀ − α` is locally nilpotent. -/
theorem L0op_locNilpotent (N : LogVModule W M) {α : ℂ} {x : M} (hx : x ∈ N.weight α) :
    ∃ k : ℕ, ((N.L0op - α • (1 : Module.End ℂ M)) ^ k) x = 0 :=
  (Module.End.mem_maxGenEigenspace _ _ _).mp (N.weight_le_maxGenEigenspace' α hx)

/-- **The grading is canonical**: the carried piece `M_[α]` is the *full* generalized
`L₀`-eigenspace.  The proof decomposes a generalized eigenvector along the grading and kills
the foreign components with the independence of generalized eigenspaces. -/
theorem maxGenEigenspace_le_weight (N : LogVModule W M) (α : ℂ) :
    N.L0op.maxGenEigenspace α ≤ N.weight α := by
  classical
  intro y hy
  letI := DirectSum.IsInternal.chooseDecomposition N.weight N.isInternal
  set c : ℂ → M := fun j => ((DirectSum.decompose N.weight y j : N.weight j) : M) with hc
  set s : Finset ℂ := (DirectSum.decompose N.weight y).support with hs
  have hdecomp : (∑ j ∈ s, c j) = y := DirectSum.sum_support_decompose N.weight y
  have hmem : ∀ j, c j ∈ N.weight j := fun j => (DirectSum.decompose N.weight y j).2
  -- `y − c α` lies in the α-generalized eigenspace …
  have h1 : y - c α ∈ N.L0op.maxGenEigenspace α :=
    Submodule.sub_mem _ hy (N.weight_le_maxGenEigenspace' α (hmem α))
  -- … and in the span of the other generalized eigenspaces.
  have h2 : y - c α ∈ ⨆ (j) (_ : j ≠ α), N.L0op.maxGenEigenspace j := by
    have hsum : y - c α = ∑ j ∈ s.erase α, c j := by
      by_cases hα : α ∈ s
      · rw [← hdecomp, Finset.sum_erase_eq_sub hα]
      · have h0 : DirectSum.decompose N.weight y α = 0 := by
          by_contra h
          exact hα (by simpa [hs] using DFinsupp.mem_support_iff.mpr h)
        have hcα : c α = 0 := by simp [hc, h0]
        rw [Finset.erase_eq_of_notMem hα, hcα, sub_zero, hdecomp]
    rw [hsum]
    refine Submodule.sum_mem _ (fun j hj => ?_)
    exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem (Finset.mem_erase.mp hj).1
      (N.weight_le_maxGenEigenspace' j (hmem j)))
  have hzero : y - c α = 0 :=
    Submodule.disjoint_def.mp (Module.End.independent_maxGenEigenspace N.L0op α) _ h1 h2
  have : y = c α := by rwa [sub_eq_zero] at hzero
  rw [this]; exact hmem α

/-- The carried grading **is** the generalized eigenspace decomposition of `L₀`. -/
theorem weight_eq_maxGenEigenspace (N : LogVModule W M) (α : ℂ) :
    N.weight α = N.L0op.maxGenEigenspace α :=
  le_antisymm (N.weight_le_maxGenEigenspace' α) (N.maxGenEigenspace_le_weight α)

/-- `L₀` preserves each graded piece (stability is a theorem, not a field). -/
theorem L0op_mem_weight (N : LogVModule W M) {α : ℂ} {x : M} (hx : x ∈ N.weight α) :
    N.L0op x ∈ N.weight α := by
  rw [weight_eq_maxGenEigenspace] at hx ⊢
  exact Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl N.L0op) α hx

/-- `L₀` acts **semisimply**: every graded piece is an honest eigenspace.  This is the predicate
characterizing the image of `OrdVModule.toLog` (see `toOrd`/`toLog_toOrd`). -/
def IsL0Semisimple (N : LogVModule W M) : Prop :=
  ∀ (α : ℂ) (x : M), x ∈ N.weight α → N.L0op x = α • x

end LogVModule

/-! ## The semisimple case embeds, and the roundtrip -/

section Embed

variable {W : VertexOperatorAlgebra 𝒱} {M : Type v} [AddCommGroup M] [Module ℂ M]

/-- **An ordinary module is a logarithmic module**: honest `L₀`-eigenspaces sit inside the
generalized ones.  All other fields are copied verbatim. -/
def OrdVModule.toLog (N : OrdVModule W M) : LogVModule W M where
  toWeakModule := N.toWeakModule
  weight := N.weight
  isInternal := N.isInternal
  weight_le_maxGenEigenspace := fun α _x hx =>
    Module.End.eigenspace_le_maxGenEigenspace
      (Module.End.mem_eigenspace_iff.mpr (N.L0_weight α _ hx))
  finrank := N.finrank
  boundedBelow := N.boundedBelow

@[simp] theorem OrdVModule.toLog_weight (N : OrdVModule W M) :
    N.toLog.weight = N.weight := rfl

/-- The embedded module is `L₀`-semisimple. -/
theorem OrdVModule.toLog_isL0Semisimple (N : OrdVModule W M) :
    N.toLog.IsL0Semisimple :=
  fun α x hx => N.L0_weight α x hx

/-- **The converse**: an `L₀`-semisimple logarithmic module is an ordinary module. -/
def LogVModule.toOrd (N : LogVModule W M) (h : N.IsL0Semisimple) : OrdVModule W M where
  toWeakModule := N.toWeakModule
  weight := N.weight
  isInternal := N.isInternal
  L0_weight := fun α x hx => h α x hx
  finrank := N.finrank
  boundedBelow := N.boundedBelow

/-- Roundtrip: `toOrd ∘ toLog = id` — nothing is lost at `k = 1`. -/
theorem OrdVModule.toOrd_toLog (N : OrdVModule W M) :
    N.toLog.toOrd N.toLog_isL0Semisimple = N := rfl

/-- Roundtrip: `toLog ∘ toOrd = id` — nothing is gained at `k = 1`. -/
theorem LogVModule.toLog_toOrd (N : LogVModule W M) (h : N.IsL0Semisimple) :
    (N.toOrd h).toLog = N := rfl

end Embed

/-! ## The semisimple/nilpotent decomposition `L₀ = L₀ˢˢ + L₀ⁿⁱˡ`

The payload of the logarithmic theory: logarithmic characters are
`tr q^{L₀ˢˢ} e^{2πiτ·L₀ⁿⁱˡ}`, and pseudo-traces consume the split. -/

namespace LogVModule

variable {W : VertexOperatorAlgebra 𝒱} {M : Type v} [AddCommGroup M] [Module ℂ M]

/-- **The semisimple part of `L₀`**: acts as the scalar `β` on the piece `M_[β]`, assembled
through the internal decomposition. -/
noncomputable def L0ss (N : LogVModule W M) : Module.End ℂ M :=
  letI := DirectSum.IsInternal.chooseDecomposition N.weight N.isInternal
  (DirectSum.toModule ℂ ℂ M (fun β : ℂ => β • (N.weight β).subtype)) ∘ₗ
    (DirectSum.decomposeLinearEquiv N.weight).toLinearMap

/-- `L₀ˢˢ` acts as the scalar `α` on `M_[α]`. -/
theorem L0ss_apply_of_mem (N : LogVModule W M) {α : ℂ} {x : M} (hx : x ∈ N.weight α) :
    N.L0ss x = α • x := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition N.weight N.isInternal
  show (DirectSum.toModule ℂ ℂ M (fun β : ℂ => β • (N.weight β).subtype))
      (DirectSum.decompose N.weight x) = α • x
  rw [DirectSum.decompose_of_mem N.weight hx, ← DirectSum.lof_eq_of ℂ,
    DirectSum.toModule_lof]
  simp

/-- `L₀ˢˢ` preserves the grading. -/
theorem L0ss_mem_weight (N : LogVModule W M) {α : ℂ} {x : M} (hx : x ∈ N.weight α) :
    N.L0ss x ∈ N.weight α := by
  rw [N.L0ss_apply_of_mem hx]; exact (N.weight α).smul_mem _ hx

/-- **The nilpotent part of `L₀`**. -/
noncomputable def L0nil (N : LogVModule W M) : Module.End ℂ M := N.L0op - N.L0ss

/-- `L₀ = L₀ˢˢ + L₀ⁿⁱˡ`. -/
theorem L0ss_add_L0nil (N : LogVModule W M) : N.L0ss + N.L0nil = N.L0op := by
  rw [L0nil, add_sub_cancel]

/-- `L₀ⁿⁱˡ` preserves the grading. -/
theorem L0nil_mem_weight (N : LogVModule W M) {α : ℂ} {x : M} (hx : x ∈ N.weight α) :
    N.L0nil x ∈ N.weight α :=
  Submodule.sub_mem _ (N.L0op_mem_weight hx) (N.L0ss_mem_weight hx)

/-- On `M_[α]`, `L₀ⁿⁱˡ` agrees with `L₀ − α`. -/
theorem L0nil_apply_of_mem (N : LogVModule W M) {α : ℂ} {x : M} (hx : x ∈ N.weight α) :
    N.L0nil x = (N.L0op - α • (1 : Module.End ℂ M)) x := by
  simp [L0nil, N.L0ss_apply_of_mem hx]

/-- Iterates of `L₀ⁿⁱˡ` on `M_[α]` agree with iterates of `L₀ − α` (both preserve `M_[α]`). -/
theorem L0nil_pow_apply_of_mem (N : LogVModule W M) {α : ℂ} (k : ℕ) {x : M}
    (hx : x ∈ N.weight α) :
    (N.L0nil ^ k) x = ((N.L0op - α • (1 : Module.End ℂ M)) ^ k) x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have hx' : (N.L0op - α • (1 : Module.End ℂ M)) x ∈ N.weight α := by
      have : (N.L0op - α • (1 : Module.End ℂ M)) x = N.L0op x - α • x := by
        simp [LinearMap.sub_apply]
      rw [this]
      exact Submodule.sub_mem _ (N.L0op_mem_weight hx) ((N.weight α).smul_mem _ hx)
    calc (N.L0nil ^ (k + 1)) x
        = (N.L0nil ^ k) (N.L0nil x) := by
          rw [pow_succ, Module.End.mul_apply]
      _ = (N.L0nil ^ k) ((N.L0op - α • (1 : Module.End ℂ M)) x) := by
          rw [N.L0nil_apply_of_mem hx]
      _ = ((N.L0op - α • (1 : Module.End ℂ M)) ^ k)
            ((N.L0op - α • (1 : Module.End ℂ M)) x) := ih hx'
      _ = ((N.L0op - α • (1 : Module.End ℂ M)) ^ (k + 1)) x := by
          rw [pow_succ, Module.End.mul_apply]

/-- **`L₀ⁿⁱˡ` is locally nilpotent** — the Jordan-block content of the structure. -/
theorem L0nil_locNilpotent (N : LogVModule W M) {α : ℂ} {x : M} (hx : x ∈ N.weight α) :
    ∃ k : ℕ, (N.L0nil ^ k) x = 0 := by
  obtain ⟨k, hk⟩ := N.L0op_locNilpotent hx
  exact ⟨k, by rw [N.L0nil_pow_apply_of_mem k hx]; exact hk⟩

/-- Two endomorphisms agreeing on every graded piece are equal (the grading spans). -/
theorem ext_on_weight (N : LogVModule W M) {f g : Module.End ℂ M}
    (h : ∀ (β : ℂ) (x : M), x ∈ N.weight β → f x = g x) : f = g := by
  ext y
  have hy : y ∈ ⨆ β, N.weight β := by
    rw [N.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction N.weight (motive := fun y => f y = g y) hy h ?_ ?_
  · simp
  · intro a b ha hb; simp [map_add, ha, hb]

/-- `L₀ˢˢ` and `L₀ⁿⁱˡ` commute. -/
theorem L0ss_comm_L0nil (N : LogVModule W M) : N.L0ss * N.L0nil = N.L0nil * N.L0ss := by
  refine N.ext_on_weight (fun β x hx => ?_)
  have h1 : N.L0nil x ∈ N.weight β := N.L0nil_mem_weight hx
  show N.L0ss (N.L0nil x) = N.L0nil (N.L0ss x)
  rw [N.L0ss_apply_of_mem h1, N.L0ss_apply_of_mem hx, map_smul]

/-- Semisimplicity is exactly the vanishing of the nilpotent part. -/
theorem isL0Semisimple_iff_L0nil_eq_zero (N : LogVModule W M) :
    N.IsL0Semisimple ↔ N.L0nil = 0 := by
  constructor
  · intro h
    refine N.ext_on_weight (fun β x hx => ?_)
    show N.L0nil x = 0
    rw [N.L0nil_apply_of_mem hx]
    simp [LinearMap.sub_apply, h β x hx]
  · intro h α x hx
    have : N.L0op x = N.L0ss x := by
      have := congrArg (fun f => f x) (N.L0ss_add_L0nil)
      simpa [h] using this.symm
    rw [this, N.L0ss_apply_of_mem hx]

end LogVModule

end VOA
