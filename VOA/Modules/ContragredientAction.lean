/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.Contragredient
import VOA.Modules.Translation
import VOA.Modules.ZeroModeMult
import VOA.Core.Automorphism

/-!
# The contragredient field-mode endomorphism on the graded dual  (Gannon §5.3.1, eq. 5.1.11a)

The engine of the contragredient module action on `M* = RestrictedDual N` (the module analogue
of the invariant-form construction `Core.BilinearForm`): the adjoint twisted by
`e^{zL₁}(−z⁻²)^{L₀}`.

* **`dualModeEndo`** — the contragredient field mode `Y_{M*}(u,z)₍ₙ₎` as a genuine
  *endomorphism of the graded dual* `RestrictedDual N = ⨁_α (M_α)*`: the transpose of the
  twisted module mode `(twist u)₍ₙ₎` reindexed (via `DirectSum.toModule`) so each input piece
  `(M_γ)*` lands in the single output piece `(M_{γ+wt−n−1})*`. The graded landing is the
  spectral fact `twistMode_mem_weight` (off `Modules.ZeroModeMult.mode_mem_weight`), and the
  assembly loses nothing — `dualModeEndo_pairing_out` certifies the pairing against the output
  weight space reproduces the genuine contragredient functional.
* **Vacuum normalization** `Y_{M*}(𝟙,z) = id` (Gannon 5.3.1a): `dualModeEndo_vacuum_id`
  (`= id` at `n = −1`) and `dualModeEndo_vacuum_zero` (`= 0` otherwise).
* **`u`-linearity** (`dualModeEndo_add_u`/`dualModeEndo_smul_u`) — the per-weight building blocks
  for the bundled field `Y_{M*} : 𝒱 →ₗ (End M*)⟦z^±⟧` over the grade decomposition.

## Status
Axiom-clean for the **graded-dual action engine + vacuum normalization**: `dualModeEndo`,
`dualModeEndo_pairing_out`, `dualModeEndo_vacuum_id`/`_zero`, the `u`-linearity lemmas are all
`[propext, Classical.choice, Quot.sound]`. The surrounding module structure is assembled from this
engine (see below).

The **full module structure** `contragredient N hJac : OrdVModule W (RestrictedDual N)` is
**assembled** (`Modules.ContragredientJacobi`, parametric in `ContragredientJacobi N`): (i) field
truncation `YMdual_truncation` (the `boundedBelow` support argument), the internal grading / `L₀`
/ fin-dim / bound; (iii) the one-point refinement `χ_{M*}(τ,v)=(−1)ⁿχ_M(τ,v)` is **proved** for
quasi-primary `v` (`Modules.ContragredientCharacter`). The single remaining input here (a
hypothesis, not an axiom) is **(ii) the module Jacobi 5.3.1b** `ContragredientJacobi N`: the genuine
`ι_z` core, derived from the `𝒱`-level full-invariance `Core.BilinearForm`'s `IsFullyInvariant`.
That `𝒱`-level FHL is *reduced* (`Core.InvariantFormFHL` + `Core.InvariantFormDiagonal`) to a
single matching-mode identity `DiagonalFHL` — the full two-sided `L₋₁`-covariance recursion
(`form_mode_lower`, `fhlInner_recursion`, `fhlDiff_recursion`), off-diagonal vanishing, and
`isFullyInvariant_of_diagonal` are all proved axiom-free. So along this route `ContragredientJacobi`
is gated on exactly `DiagonalFHL` (and its transport to the module level) — a hypothesis, not an
axiom.  `ContragredientJacobi N` is proved unconditionally, by a module-level route, as
`contragredientJacobi_holds` (`Modules.ContragredientClose`).

## References
* Gannon §5.3.1, eqs. (5.3.4)–(5.3.5), (5.1.11a); Frenkel–Huang–Lepowsky [199]; Li [380].
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators
open Classical

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Recap: the local-nilpotence engine. -/

/-- `L₁` is locally nilpotent on `𝒱`. -/
theorem isLocNilp_L_one (W : VertexOperatorAlgebra 𝒱) :
    IsLocNilp (W.L 1) := by
  intro v
  have hvtop : v ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading (motive := fun v => ∃ N : ℕ, ((W.L 1) ^ N) v = 0)
    hvtop ?_ ?_ ?_
  · intro i x hx
    rcases le_or_gt i 0 with hi | hi
    · refine ⟨1, ?_⟩
      rw [pow_one]
      have h := L_one_pow_mem W hx 1
      rw [show (i - ((1 : ℕ) : ℤ)) = i - 1 by push_cast; ring] at h
      rw [W.positivity (i - 1) (by omega)] at h
      simpa using ((Submodule.mem_bot ℂ).mp h)
    · refine ⟨i.toNat + 1, ?_⟩
      apply VertexOperatorAlgebra.L_one_pow_eq_zero W hx
      have : (i.toNat : ℤ) = i := Int.toNat_of_nonneg (by omega)
      push_cast
      omega
  · exact ⟨1, by rw [pow_one]; exact map_zero _⟩
  · intro x y ⟨Nx, hx⟩ ⟨Ny, hy⟩
    refine ⟨max Nx Ny, ?_⟩
    rw [map_add, VOA.pow_apply_eq_zero_of_le hx (le_max_left _ _),
      VOA.pow_apply_eq_zero_of_le hy (le_max_right _ _), add_zero]

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## Recap: the evaluation pairing and the weight-shift (copied, build-clean). -/

/-- The `α`-component evaluation `g ↦ g(proj_α x)`, linear in the functional `g`. -/
noncomputable def evalProj (N : OrdVModule W M) (x : M) (α : ℂ) :
    Module.Dual ℂ (N.weight α) →ₗ[ℂ] ℂ where
  toFun g := g (internalProjTo N.isInternal α x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem evalProj_apply (N : OrdVModule W M) (x : M) (α : ℂ)
    (g : Module.Dual ℂ (N.weight α)) :
    evalProj N x α g = g (internalProjTo N.isInternal α x) := rfl

/-- The evaluation pairing `⟨f, x⟩ = ∑_α f_α(proj_α x)`, as a `ℂ`-linear functional in `f`. -/
noncomputable def dualPairing (N : OrdVModule W M) (x : M) : RestrictedDual N →ₗ[ℂ] ℂ :=
  DirectSum.toModule ℂ ℂ ℂ (fun α => evalProj N x α)

theorem dualPairing_lof (N : OrdVModule W M) (x : M) (α : ℂ)
    (g : Module.Dual ℂ (N.weight α)) :
    dualPairing N x (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α g)
      = g (internalProjTo N.isInternal α x) := by
  unfold dualPairing
  exact DirectSum.toModule_lof ℂ (φ := fun α => evalProj N x α) α g

/-! ## The graded-landing lemma (the engine of target (A)).

For `u ∈ 𝒱_wt` and `x ∈ M_α`, the module mode `(L₁ʲu)₍2wt−n−2−j₎ x` lands in the SINGLE weight
space `M_{α+n+1−wt}` — independent of `j`. From `L0_eigenvalue_shift` (the eigenvalue of `L₀`
on it is `α + n + 1 − wt`) plus `eigenvector_mem_weight` (eigenvector ⟹ membership). This is
the fact that makes the contragredient's transpose preserve the *graded* dual. -/

/-- **Graded landing.** For `u ∈ 𝒱_wt` and `x ∈ M_α`, `(L₁ʲu)₍2wt−n−2−j₎ x ∈ M_{α+n+1−wt}`. -/
theorem twistMode_mem_weight (N : OrdVModule W M) {wt : ℤ} {u : 𝒱} (hu : u ∈ W.grading wt)
    {α : ℂ} {x : M} (hx : x ∈ N.weight α) (n : ℤ) (j : ℕ) :
    mode (N.YM ((W.L 1 ^ j) u)) (2 * wt - n - 2 - (j : ℤ)) x
      ∈ N.weight (α + (n : ℂ) + 1 - (wt : ℂ)) := by
  have hjmem : (W.L 1 ^ j) u ∈ W.grading (wt - (j : ℤ)) := L_one_pow_mem W hu j
  have hmem := mode_mem_weight N hjmem hx (2 * wt - n - 2 - (j : ℤ))
  convert hmem using 2
  push_cast
  ring

/-! ## Target (A): the per-input-component map `(M_γ)* → (M_α)*`.

For `u ∈ 𝒱_wt`, the contragredient field mode at index `n` sends the input graded piece
`(M_γ)*` to the output piece `(M_α)*` with `α = γ + wt − n − 1` (the inverse of the landing
relation `γ = α + n + 1 − wt`). The output functional, on `x ∈ M_α`, is
`(−1)^wt ∑_{j ≤ wt} (1/j!) ⟨g, proj_γ ((L₁ʲu)₍2wt−n−2−j₎ x)⟩`. -/

/-- The output weight index `α = γ + wt − n − 1` for input piece `γ`. -/
def dualOutIdx (wt n : ℤ) (γ : ℂ) : ℂ := γ + (wt : ℂ) - (n : ℂ) - 1

/-- The transpose target operator `T_{γ,j} := proj_γ ∘ (L₁ʲu)₍2wt−n−2−j₎ : M → M_γ`. -/
noncomputable def dualTargetOp (N : OrdVModule W M) (wt : ℤ) (u : 𝒱) (n : ℤ) (γ : ℂ) (j : ℕ) :
    M →ₗ[ℂ] N.weight γ :=
  (internalProjTo N.isInternal γ).comp
    (modeLinear (2 * wt - n - 2 - (j : ℤ)) (N.YM ((W.L 1 ^ j) u)))

@[simp] theorem dualTargetOp_apply (N : OrdVModule W M) (wt : ℤ) (u : 𝒱) (n : ℤ) (γ : ℂ) (j : ℕ)
    (x : M) :
    (dualTargetOp N wt u n γ j x : M)
      = (internalProjTo N.isInternal γ
          (mode (N.YM ((W.L 1 ^ j) u)) (2 * wt - n - 2 - (j : ℤ)) x) : M) := rfl

/-- **The per-input-component map** `(M_γ)* →ₗ Module.Dual ℂ M` of the contragredient mode:
`g ↦ (−1)^wt ∑_{j ≤ wt} (1/j!) (g ∘ T_{γ,j})`. Linear in `g` automatically
(it is `lcomp`). -/
noncomputable def dualCompMap (N : OrdVModule W M) (wt : ℤ) (u : 𝒱) (n : ℤ) (γ : ℂ) :
    Module.Dual ℂ (N.weight γ) →ₗ[ℂ] Module.Dual ℂ M :=
  (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1),
    ((j.factorial : ℂ)⁻¹) • LinearMap.lcomp ℂ ℂ (dualTargetOp N wt u n γ j)

theorem dualCompMap_apply (N : OrdVModule W M) (wt : ℤ) (u : 𝒱) (n : ℤ) (γ : ℂ)
    (g : Module.Dual ℂ (N.weight γ)) (x : M) :
    dualCompMap N wt u n γ g x
      = (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1),
          ((j.factorial : ℂ)⁻¹) •
            g (internalProjTo N.isInternal γ
              (mode (N.YM ((W.L 1 ^ j) u)) (2 * wt - n - 2 - (j : ℤ)) x)) := by
  simp only [dualCompMap, LinearMap.smul_apply, LinearMap.coeFn_sum, Finset.sum_apply,
    LinearMap.lcomp_apply]
  rfl

/-! ## Assembling the endomorphism of the graded dual `RestrictedDual N`.

The per-input-component map `(M_γ)* → RestrictedDual N` puts the (restricted-to-`M_α`)
output functional into the single graded slot `α = dualOutIdx wt n γ`. Assembling over all
input pieces `γ` via `DirectSum.toModule` gives the genuine endomorphism. -/

/-- Restrict a functional on `M` to the weight space `M_α` (compose with the inclusion). -/
noncomputable def restrictToWeight (N : OrdVModule W M) (α : ℂ) :
    Module.Dual ℂ M →ₗ[ℂ] Module.Dual ℂ (N.weight α) :=
  LinearMap.lcomp ℂ ℂ (N.weight α).subtype

/-- **The per-input-component map into the graded dual**, `(M_γ)* →ₗ RestrictedDual N`:
`g ↦ lof_{α} ((dualCompMap … g)|_{M_α})` with `α = dualOutIdx wt n γ`. Linear in `g`. -/
noncomputable def dualPieceMap (N : OrdVModule W M) (wt : ℤ) (u : 𝒱) (n : ℤ) (γ : ℂ) :
    Module.Dual ℂ (N.weight γ) →ₗ[ℂ] RestrictedDual N :=
  (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) (dualOutIdx wt n γ)).comp
    ((restrictToWeight N (dualOutIdx wt n γ)).comp (dualCompMap N wt u n γ))

/-- **The contragredient field-mode endomorphism** of the graded dual (target (A)): the
transpose of `(twist u)₍ₙ₎` reindexed so that each input piece `(M_γ)*` lands in the single
output piece `(M_{γ+wt−n−1})*`. Assembled over all `γ` via `DirectSum.toModule`. -/
noncomputable def dualModeEndo (N : OrdVModule W M) (wt : ℤ) (u : 𝒱) (n : ℤ) :
    RestrictedDual N →ₗ[ℂ] RestrictedDual N :=
  DirectSum.toModule ℂ ℂ (RestrictedDual N) (fun γ => dualPieceMap N wt u n γ)

/-- The endomorphism on a single graded generator `lof γ g`: it lands in slot
`α = γ + wt − n − 1`, carrying the restricted functional `(dualCompMap … g)|_{M_α}`. -/
theorem dualModeEndo_lof (N : OrdVModule W M) (wt : ℤ) (u : 𝒱) (n : ℤ) (γ : ℂ)
    (g : Module.Dual ℂ (N.weight γ)) :
    dualModeEndo N wt u n
        (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) γ g)
      = DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) (dualOutIdx wt n γ)
          ((restrictToWeight N (dualOutIdx wt n γ)) (dualCompMap N wt u n γ g)) := by
  show DirectSum.toModule ℂ ℂ (RestrictedDual N) (fun γ => dualPieceMap N wt u n γ)
      (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) γ g) = _
  rw [DirectSum.toModule_lof ℂ (φ := fun γ => dualPieceMap N wt u n γ) γ g]
  rfl

/-! ## Correctness of the assembly (the graded-landing pays off).

The endomorphism `dualModeEndo` paired against the *output* weight space reproduces the
genuine contragredient functional `dualCompMap` — i.e. restricting to `M_α` loses nothing,
exactly because the relevant module modes already land in `M_α`'s dual partner (graded
landing). This certifies the construction. -/

/-- **Correctness on the output weight space.** For `x ∈ M_α` with `α = γ + wt − n − 1`, the
pairing `⟨dualModeEndo(lof γ g), x⟩` equals the genuine contragredient functional
`(dualCompMap … g) x`. -/
theorem dualModeEndo_pairing_out (N : OrdVModule W M) (wt : ℤ) (u : 𝒱) (n : ℤ) (γ : ℂ)
    (g : Module.Dual ℂ (N.weight γ)) {x : M} (hx : x ∈ N.weight (dualOutIdx wt n γ)) :
    dualPairing N x
        (dualModeEndo N wt u n
          (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) γ g))
      = dualCompMap N wt u n γ g x := by
  rw [dualModeEndo_lof, dualPairing_lof]
  show (restrictToWeight N (dualOutIdx wt n γ) (dualCompMap N wt u n γ g))
      (internalProjTo N.isInternal (dualOutIdx wt n γ) x) = _
  unfold restrictToWeight
  rw [LinearMap.lcomp_apply]
  have hcoe : ((internalProjTo N.isInternal (dualOutIdx wt n γ) x : N.weight _) : M) = x := by
    have := internalProjTo_coe N.isInternal (dualOutIdx wt n γ) ⟨x, hx⟩
    simpa using congrArg (Subtype.val) this
  show (dualCompMap N wt u n γ g)
      ((N.weight (dualOutIdx wt n γ)).subtype (internalProjTo N.isInternal (dualOutIdx wt n γ) x))
      = _
  rw [Submodule.subtype_apply, hcoe]

/-! ## Linearity of the dual mode in `u` (at fixed weight `wt`).

`dualCompMap`/`dualModeEndo` are `ℂ`-linear in `u` (through `N.YM`, `W.L 1 ^ j`, `modeLinear`,
all linear). This is the building block for packaging the dual field `Y_{M*}` and for the
grade-sum extension to a general `u`. -/

/-- The transpose target operator is **additive in `u`**. -/
theorem dualTargetOp_add (N : OrdVModule W M) (wt : ℤ) (u₁ u₂ : 𝒱) (n : ℤ) (γ : ℂ) (j : ℕ) :
    dualTargetOp N wt (u₁ + u₂) n γ j
      = dualTargetOp N wt u₁ n γ j + dualTargetOp N wt u₂ n γ j := by
  unfold dualTargetOp
  rw [map_add, map_add, map_add, LinearMap.comp_add]

/-- The transpose target operator is **homogeneous in `u`**. -/
theorem dualTargetOp_smul (N : OrdVModule W M) (wt : ℤ) (c : ℂ) (u : 𝒱) (n : ℤ) (γ : ℂ) (j : ℕ) :
    dualTargetOp N wt (c • u) n γ j = c • dualTargetOp N wt u n γ j := by
  unfold dualTargetOp
  rw [map_smul, map_smul, map_smul, LinearMap.comp_smul]

/-- **`dualCompMap` is additive in `u`** (at fixed weight). -/
theorem dualCompMap_add_u (N : OrdVModule W M) (wt : ℤ) (u₁ u₂ : 𝒱) (n : ℤ) (γ : ℂ) :
    dualCompMap N wt (u₁ + u₂) n γ
      = dualCompMap N wt u₁ n γ + dualCompMap N wt u₂ n γ := by
  refine LinearMap.ext (fun g => LinearMap.ext (fun x => ?_))
  simp only [dualCompMap_apply, LinearMap.add_apply]
  rw [← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← smul_add]
  congr 1
  -- g(proj((L₁ʲ(u₁+u₂))ₖ x)) = g(proj((L₁ʲu₁)ₖ x)) + g(proj((L₁ʲu₂)ₖ x))
  rw [map_add, ← map_add, ← map_add]
  congr 2
  simp only [map_add, mode_add, LinearMap.add_apply]

/-- **`dualCompMap` is homogeneous in `u`** (at fixed weight). -/
theorem dualCompMap_smul_u (N : OrdVModule W M) (wt : ℤ) (c : ℂ) (u : 𝒱) (n : ℤ) (γ : ℂ) :
    dualCompMap N wt (c • u) n γ = c • dualCompMap N wt u n γ := by
  refine LinearMap.ext (fun g => LinearMap.ext (fun x => ?_))
  simp only [dualCompMap_apply, LinearMap.smul_apply]
  -- pull `c` out of each summand
  have hpull : ∀ j : ℕ,
      g (internalProjTo N.isInternal γ
          (mode (N.YM ((W.L 1 ^ j) (c • u))) (2 * wt - n - 2 - (j : ℤ)) x))
        = c • g (internalProjTo N.isInternal γ
            (mode (N.YM ((W.L 1 ^ j) u)) (2 * wt - n - 2 - (j : ℤ)) x)) := by
    intro j
    rw [map_smul, map_smul, mode_smul, LinearMap.smul_apply, map_smul, map_smul]
  simp only [hpull, smul_comm _ c, ← Finset.smul_sum]

/-- **The dual mode endomorphism is additive in `u`** (at fixed weight). -/
theorem dualModeEndo_add_u (N : OrdVModule W M) (wt : ℤ) (u₁ u₂ : 𝒱) (n : ℤ) :
    dualModeEndo N wt (u₁ + u₂) n
      = dualModeEndo N wt u₁ n + dualModeEndo N wt u₂ n := by
  refine DirectSum.linearMap_ext ℂ (fun γ => ?_)
  refine LinearMap.ext (fun g => ?_)
  simp only [LinearMap.comp_apply, LinearMap.add_comp, LinearMap.add_apply]
  have h1 := dualModeEndo_lof N wt (u₁ + u₂) n γ g
  have h2 := dualModeEndo_lof N wt u₁ n γ g
  have h3 := dualModeEndo_lof N wt u₂ n γ g
  rw [dualCompMap_add_u N wt u₁ u₂ n γ, LinearMap.add_apply, map_add, map_add] at h1
  -- goal LHS = h1.LHS (defeq); h1.RHS = h2.RHS + h3.RHS = (goal RHS via h2,h3)
  exact h1.trans (congr_arg₂ (· + ·) h2.symm h3.symm)

/-- **The dual mode endomorphism is homogeneous in `u`** (at fixed weight). -/
theorem dualModeEndo_smul_u (N : OrdVModule W M) (wt : ℤ) (c : ℂ) (u : 𝒱) (n : ℤ) :
    dualModeEndo N wt (c • u) n = c • dualModeEndo N wt u n := by
  refine DirectSum.linearMap_ext ℂ (fun γ => ?_)
  refine LinearMap.ext (fun g => ?_)
  simp only [LinearMap.comp_apply, LinearMap.smul_comp, LinearMap.smul_apply]
  have h1 := dualModeEndo_lof N wt (c • u) n γ g
  have h2 := dualModeEndo_lof N wt u n γ g
  rw [dualCompMap_smul_u N wt c u n γ, LinearMap.smul_apply, map_smul, map_smul] at h1
  exact h1.trans (congr_arg (c • ·) h2.symm)

/-! ## Target (B), part 1: the contragredient field as a bundled `(End)⟦z^±⟧`.

`Y_{M*}(u, z)`: the formal series whose `n`-th mode is the endomorphism `dualModeEndo`. We
build it for HOMOGENEOUS `u ∈ 𝒱_wt`; the field on a general `u` is the (finite) grade sum.
Here we package the homogeneous field and prove the vacuum normalization `Y_{M*}(𝟙, z) = id`
(Gannon 5.3.1a for `M*`). -/

/-- `dualCompMap` at the **vacuum** (`wt = 0`, `u = 𝟙`) collapses to the single `j = 0` term
`g ∘ proj_γ ∘ 𝟙₍−n−2₎`. -/
theorem dualCompMap_vacuum (N : OrdVModule W M) (n : ℤ) (γ : ℂ)
    (g : Module.Dual ℂ (N.weight γ)) (x : M) :
    dualCompMap N 0 W.vacuum n γ g x
      = g (internalProjTo N.isInternal γ
          (mode (N.YM W.vacuum) (-n - 2) x)) := by
  rw [dualCompMap_apply, show (0:ℤ).toNat + 1 = 1 from rfl, Finset.sum_range_one]
  simp only [pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    show ((-1:ℂ) ^ (0:ℤ)) = 1 from by norm_num]
  rw [show (2 * 0 - n - 2 - ((0:ℕ):ℤ) : ℤ) = -n - 2 from by push_cast; ring]

/-- At the vacuum and `n ≠ −1`, `dualCompMap` vanishes (`𝟙₍−n−2₎ x = 0`). -/
theorem dualCompMap_vacuum_zero (N : OrdVModule W M) {n : ℤ} (hn : n ≠ -1) (γ : ℂ)
    (g : Module.Dual ℂ (N.weight γ)) :
    dualCompMap N 0 W.vacuum n γ g = 0 := by
  refine LinearMap.ext (fun x => ?_)
  rw [dualCompMap_vacuum]
  have hv : mode (N.YM W.vacuum) (-n - 2) x = 0 := by
    have h := N.toWeakModule.act_vacuum (-n-2) x
    rw [WeakModule.act_def] at h
    rw [h, if_neg (by omega : ¬ (-n-2 : ℤ) = -1)]
  rw [hv, map_zero, map_zero, LinearMap.zero_apply]

/-- At the vacuum and `n = −1`, `dualCompMap N 0 𝟙 (-1) γ g x = g (proj_γ x)`. -/
theorem dualCompMap_vacuum_neg_one (N : OrdVModule W M) (γ : ℂ)
    (g : Module.Dual ℂ (N.weight γ)) (x : M) :
    dualCompMap N 0 W.vacuum (-1) γ g x = g (internalProjTo N.isInternal γ x) := by
  rw [dualCompMap_vacuum]
  have hv : mode (N.YM W.vacuum) (-(-1) - 2) x = x := by
    have h := N.toWeakModule.act_vacuum (-(-1)-2) x
    rw [WeakModule.act_def] at h
    rw [h, if_pos (by norm_num : (-(-1)-2 : ℤ) = -1)]
  rw [hv]

/-! ## Target (B): vacuum normalization `Y_{M*}(𝟙, z) = id` (Gannon 5.3.1a for `M*`). -/

/-- **Vacuum vanishing for `n ≠ −1`**: `dualModeEndo N 0 𝟙 n = 0`. -/
theorem dualModeEndo_vacuum_zero (N : OrdVModule W M) {n : ℤ} (hn : n ≠ -1) :
    dualModeEndo N 0 W.vacuum n = 0 := by
  refine DirectSum.linearMap_ext ℂ (fun γ => ?_)
  refine LinearMap.ext (fun g => ?_)
  simp only [LinearMap.comp_apply, LinearMap.zero_comp, LinearMap.zero_apply]
  have h := dualModeEndo_lof N 0 W.vacuum n γ g
  rw [dualCompMap_vacuum_zero N hn γ g, map_zero, map_zero] at h
  exact h

/-- **Vacuum normalization `Y_{M*}(𝟙, z) = id`** (Gannon 5.3.1a, module analogue): the
contragredient field at the vacuum is `𝟙₍ₙ₎^{M*} = δ_{n,−1} · id_{M*}`. The `n = −1` mode is
the identity of the graded dual. -/
theorem dualModeEndo_vacuum_id (N : OrdVModule W M) :
    dualModeEndo N 0 W.vacuum (-1) = LinearMap.id := by
  refine DirectSum.linearMap_ext ℂ (fun γ => ?_)
  refine LinearMap.ext (fun g => ?_)
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  have h := dualModeEndo_lof N 0 W.vacuum (-1) γ g
  have hidx : dualOutIdx 0 (-1) γ = γ := by simp [dualOutIdx]
  rw [hidx] at h
  refine h.trans ?_
  -- show: lof γ (restrict_γ (dualCompMap N 0 𝟙 (-1) γ g)) = lof γ g
  have hfun : restrictToWeight N γ (dualCompMap N 0 W.vacuum (-1) γ g) = g := by
    refine LinearMap.ext (fun y => ?_)
    show (restrictToWeight N γ (dualCompMap N 0 W.vacuum (-1) γ g)) y = g y
    unfold restrictToWeight
    rw [LinearMap.lcomp_apply, Submodule.subtype_apply, dualCompMap_vacuum_neg_one]
    congr 1
    exact internalProjTo_coe N.isInternal γ y
  exact congrArg (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) γ) hfun
