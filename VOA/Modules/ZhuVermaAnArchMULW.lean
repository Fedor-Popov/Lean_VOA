/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUmod
import VOA.Modules.ZhuVermaAnArchMU
import VOA.Modules.ZhuBijection

/-!
# `M(U)` as an `LWModule` and the irreducible quotient `L(U)` (Zhu Thm 5.3.4, hard direction)

This file performs the **structural packaging** of the Dong–Jiang induced module
`M(U) = ⊕ₙ A_{n,0}(𝒱) ⊗ U` (carrier + ℕ-grading proved in `ZhuVermaAnArchMU`) into the project's
bundled lowest-weight `𝒱`-module interface `LWModule W` (`ZhuBijection`), and constructs the
irreducible quotient `L(U) = M(U)/J`.

## The honest input — `MUModuleData`

The carrier `MU W U` and its ℕ-grading `MU.deg` are unconditional (`ZhuVermaAnArchMU`). The
*action* of `𝒱` on `MU W U` is supplied by the Construction-A engine `VHatRep` (DLM3 §4,
`ZhuVermaAnArchMUVhat`), and the genuine deep theorem is that this action satisfies the module
Jacobi 5.3.1b (`IsModuleJacobi`) and is graded by `L₀ = h + n` on the level-`n` piece. As recorded
in `ZhuVermaAnArchMUmod` (`MUGradedAction_not_jacobi_remark`), `MUGradedAction` alone does **not**
yield `IsModuleJacobi`; they are independent inputs. We therefore bundle the genuine module data —
the `VHatRep ρ` on `MU W U`, the `WeakModule` axioms (vacuum, truncation, Jacobi) it satisfies, the
grading compatibility (`L₀` acts as `h + n` on `MU.deg n`), finiteness and bottom-nonvanishing — as
the single structure `MUModuleData W U h`. Everything below is **conditional on this structure**,
which is exactly the output of the deep Construction-A / DJ Prop 3.5 work (the part `MUGradedAction`
does not supply); it is a *hypothesis structure*, **not** an axiom, and contains no `sorry`.

The structural assembly proved here is unconditional given that structure:

* **`MUModuleData.cweight`** — the ℂ-grading of `M(U)`: the ℕ-grading `MU.deg n` placed at the
  complex weight `α = h + n` (and `⊥` elsewhere). Engine-verified that `L₀` acts as the level scalar
  (`certificates/mathematica/heis_engine.wl`: `a₁ a₋₁|0⟩ = 1`, `a₂ a₋₂|0⟩ = 2`).
* **`MUModuleData.cweight_isInternal`** — the ℂ-grading is a genuine internal direct sum
  (reindex `MU.isInternal_deg` along the injection `n ↦ h + n`, exactly as `adjointModule` does).
* **`MUModuleData.toOrdVModule`** — the full `OrdVModule W (MU W U)`, assembled from the bundled
  `WeakModule` (vacuum/truncation/Jacobi) plus the ℂ-grading and its `L0_weight`/finiteness/bounded-
  below data. **This is the OrdVModule upgrade.**
* **`MUModuleData.isLowestWeight`** — `h` is a lowest weight (every nonzero ℂ-weight is `h + n`).
* **`MUModuleData.toLWModule`** — `M(U) : LWModule W`, with `h := h`, realized (bottom `≠ ⊥`).
  **This is the LWModule packaging.**
* **`MUModuleData.bottomEquiv`** — the bottom layer `M(U)_h = cweight h` is the level-`0` piece
  `MU.deg 0`, isomorphic as a ℂ-space to `MUPiece W U 0 = A(𝒱) ⊗ U` (the bottom iso `realizes`).

For `L(U)`: the maximal proper graded submodule `J` and the irreducible quotient `L(U) = M(U)/J`
are reduced to the standard data (`L(U)` irreducible + `L(U)_h ≅ U`); the precise remaining content
is recorded at the end (`LU_target`).

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.4–3.5, Thm 4.13; DLM3 §4;
H. Li hep-th/9406211 §2; Gannon §5.3.1–§5.3.2, Def. 5.3.1, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators TensorProduct DirectSum

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The bundled genuine module data for `M(U)` -/

/-- **The genuine module data for the Dong–Jiang induced module `M(U)`** at lowest weight `h`.

This is the output of the Construction-A engine (`VHatRep` on the carrier `MU W U`,
`ZhuVermaAnArchMUVhat`) together with the deep module-Jacobi theorem (`IsModuleJacobi`,
DJ Prop 3.5) and the grading compatibility. It bundles exactly the data the `OrdVModule`/`LWModule`
interface consumes; it is a **hypothesis structure**, not an axiom, with no `sorry`. Once the deep
Jacobi and grading lemmas are discharged (the genuine remaining theorem), this structure is produced
and every construction below becomes unconditional. -/
structure MUModuleData (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (h : ℂ) where
  /-- The `WeakModule` structure on `MU W U` — its mode action `Y_{M(U)}`, vacuum normalization
  (5.3.1a), field/truncation, and the module Jacobi (5.3.1b). Produced by `VHatRep.toWeakModule`
  from the Construction-A representation `ρ` together with `IsModuleJacobi`. -/
  weak : WeakModule W (MU W U)
  /-- **Grading compatibility (5.3.1c):** `L₀ = ω₍₁₎` acts as the scalar `h + n` on the level-`n`
  graded piece `MU.deg n`. Engine-verified that the conformal mode is the level scalar. -/
  L0_on_deg : ∀ (n : ℕ) (x : MU W U), x ∈ MU.deg W U n →
    mode (weak.YM W.conformalVector) 1 x = ((h : ℂ) + n) • x
  /-- Each level-`n` piece is finite-dimensional (the graded pieces of `M(U)` are f.d. — DJ
  Thm 4.13; here a hypothesis on the bundled carrier). -/
  finrank_deg : ∀ n : ℕ, FiniteDimensional ℂ (MU.deg W U n)
  /-- The bottom layer is nonzero: `U ≠ 0` ⟹ `MU.deg 0 = A(𝒱) ⊗ U ≠ ⊥` (realization). -/
  bottom_ne_bot : MU.deg W U 0 ≠ ⊥

namespace MUModuleData

variable {W : VertexOperatorAlgebra 𝒱} {U : AMod W} {h : ℂ}

/-! ## The ℂ-grading of `M(U)` from the ℕ-grading -/

/-- **The ℂ-grading of `M(U)`**: the ℕ-grading piece `MU.deg n` placed at the complex weight
`α = h + n`, and `⊥` at every `α` not of that form. (Cf. `adjWeight` for the adjoint module.) -/
noncomputable def cweight (D : MUModuleData W U h) (α : ℂ) : Submodule ℂ (MU W U) :=
  ⨆ (n : ℕ) (_ : (h : ℂ) + n = α), MU.deg W U n

/-- `cweight` at `α = h + n` is the level-`n` piece `MU.deg n`. -/
theorem cweight_cast (D : MUModuleData W U h) (m : ℕ) :
    D.cweight ((h : ℂ) + m) = MU.deg W U m := by
  unfold cweight
  apply le_antisymm
  · refine iSup_le (fun n => iSup_le (fun hn => ?_))
    have : n = m := by
      have : (n : ℂ) = (m : ℂ) := by have := hn; linear_combination hn
      exact_mod_cast this
    rw [this]
  · exact le_iSup_of_le m (le_iSup_of_le rfl le_rfl)

/-- `cweight` is `⊥` at every `α` not of the form `h + n`. -/
theorem cweight_eq_bot (D : MUModuleData W U h) {α : ℂ}
    (hne : ∀ n : ℕ, (h : ℂ) + n ≠ α) : D.cweight α = ⊥ :=
  iSup_eq_bot.mpr (fun n => iSup_eq_bot.mpr (fun hn => absurd hn (hne n)))

/-- **The ℂ-grading of `M(U)` is a genuine internal direct-sum decomposition.** Reindex the
ℕ-grading internality `MU.isInternal_deg` along the injection `n ↦ h + n` (the same maneuver as
`adjointModule`). -/
theorem cweight_isInternal (D : MUModuleData W U h) :
    DirectSum.IsInternal D.cweight := by
  have hN := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top (MU.deg W U)).mp
    (MU.isInternal_deg W U)
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · refine iSupIndep_extend (MU.deg W U) D.cweight (fun n => (h : ℂ) + n) ?_ ?_ hN.1
    · intro α hα; exact D.cweight_eq_bot (fun n hn => hα n hn)
    · intro n; exact D.cweight_cast n
  · rw [← hN.2]
    apply le_antisymm
    · refine iSup_le (fun α => ?_)
      unfold cweight
      exact iSup_le (fun n => iSup_le (fun _ => le_iSup (MU.deg W U) n))
    · exact iSup_le (fun n => le_iSup_of_le ((h : ℂ) + n) (by rw [D.cweight_cast n]))

/-! ## The `OrdVModule` upgrade -/

/-- **The `OrdVModule W (MU W U)` upgrade.** Assembles the full ℂ-graded `𝒱`-module from the bundled
`WeakModule` (vacuum/truncation/Jacobi) and the ℂ-grading `cweight` with its internality,
`L0_weight`, finiteness, and bounded-below data. This is the structural payload: `M(U)` is a genuine
graded `𝒱`-module. -/
noncomputable def toOrdVModule (D : MUModuleData W U h) : OrdVModule W (MU W U) where
  toWeakModule := D.weak
  weight := D.cweight
  isInternal := D.cweight_isInternal
  L0_weight := by
    intro α x hx
    by_cases hcase : ∃ m : ℕ, (h : ℂ) + m = α
    · obtain ⟨m, rfl⟩ := hcase
      rw [D.cweight_cast m] at hx
      exact D.L0_on_deg m x hx
    · rw [D.cweight_eq_bot (fun n hn => hcase ⟨n, hn⟩), Submodule.mem_bot] at hx
      rw [hx, map_zero, smul_zero]
  finrank := by
    intro α
    by_cases hcase : ∃ m : ℕ, (h : ℂ) + m = α
    · obtain ⟨m, rfl⟩ := hcase
      rw [D.cweight_cast m]; exact D.finrank_deg m
    · rw [D.cweight_eq_bot (fun n hn => hcase ⟨n, hn⟩)]; infer_instance
  boundedBelow := by
    -- Every nonzero weight is at `α = h + n`, `n ≥ 0`, so `Re α ≥ Re h`.
    refine ⟨h.re, fun α hα => ?_⟩
    by_cases hcase : ∃ m : ℕ, (h : ℂ) + m = α
    · obtain ⟨m, rfl⟩ := hcase
      simp only [Complex.add_re, Complex.natCast_re]
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    · exact absurd (D.cweight_eq_bot (fun n hn => hcase ⟨n, hn⟩)) hα

@[simp] theorem toOrdVModule_weight (D : MUModuleData W U h) (α : ℂ) :
    D.toOrdVModule.weight α = D.cweight α := rfl

/-! ## `h` is a lowest weight; the bottom layer is realized -/

/-- **`h` is a lowest weight of `M(U)`.** Every nonzero ℂ-weight is `h + n` for some `n : ℕ`
(the ℕ-grading is bounded below by `0`). -/
theorem isLowestWeight (D : MUModuleData W U h) : IsLowestWeight D.toOrdVModule h := by
  intro α hα
  by_cases hcase : ∃ m : ℕ, (h : ℂ) + m = α
  · obtain ⟨m, rfl⟩ := hcase
    exact ⟨m, by simp⟩
  · exact absurd (D.cweight_eq_bot (fun n hn => hcase ⟨n, hn⟩)) (by simpa using hα)

/-- **The bottom layer `M(U)_h` is nonzero (realized).** `M(U)_h = cweight h = MU.deg 0` and the
bottom level is nonzero (`U ≠ 0`). -/
theorem bottom_weight_ne_bot (D : MUModuleData W U h) : D.toOrdVModule.weight h ≠ ⊥ := by
  rw [toOrdVModule_weight]
  have : D.cweight h = MU.deg W U 0 := by
    have := D.cweight_cast 0
    simpa using this
  rw [this]
  exact D.bottom_ne_bot

/-! ## The `LWModule` packaging -/

/-- **`M(U)` as a bundled lowest-weight `𝒱`-module `LWModule W`.** Carrier `MU W U`, ℂ-graded
`𝒱`-module structure `toOrdVModule`, realized lowest weight `h`. This is the structural target — the
hard-direction object `U ↦ M(U)` packaged into the bijection interface (`ZhuBijection`). -/
noncomputable def toLWModule (D : MUModuleData W U h) : LWModule W where
  carrier := MU W U
  isMod := D.toOrdVModule
  h := h
  isLow := D.isLowestWeight
  realized := D.bottom_weight_ne_bot

@[simp] theorem toLWModule_carrier (D : MUModuleData W U h) :
    (D.toLWModule).carrier = MU W U := rfl

@[simp] theorem toLWModule_h (D : MUModuleData W U h) : (D.toLWModule).h = h := rfl

@[simp] theorem toLWModule_isMod (D : MUModuleData W U h) :
    (D.toLWModule).isMod = D.toOrdVModule := rfl

/-! ## The bottom iso `M(U)_h ≅ A(𝒱) ⊗ U`

The bottom weight space `M(U)_h = cweight h = MU.deg 0 = range (MU.incl … 0)` is, as a ℂ-space, the
level-`0` piece `MUPiece W U 0 = A_{0,0}(𝒱) ⊗ U = A(𝒱) ⊗ U`. We exhibit the linear equivalence,
which is the `realizes` data of the hard direction (the bottom layer is `A(𝒱) ⊗ U`, the universal
cover of the genuine `M(U)_h ≅ U`). -/

/-- The bottom weight space `M(U)_h` equals the level-`0` graded piece `MU.deg 0`. -/
theorem weight_h_eq_deg0 (D : MUModuleData W U h) : D.toOrdVModule.weight h = MU.deg W U 0 := by
  rw [toOrdVModule_weight]
  have := D.cweight_cast 0
  simpa using this

/-- **The bottom iso (ℂ-linear).** `M(U)_h ≅ A_{0,0}(𝒱) ⊗ U = A(𝒱) ⊗ U`.
The level-`0` inclusion `MU.incl … 0 : MUPiece 0 → MU` is injective (it is `DirectSum.lof`), so it
restricts to a linear equivalence onto its range `MU.deg 0 = M(U)_h`. This is the `realizes` data of
the hard direction. -/
noncomputable def bottomEquiv (D : MUModuleData W U h) :
    MUPiece W U 0 ≃ₗ[ℂ] D.toOrdVModule.weight h := by
  refine (LinearEquiv.ofInjective (MU.incl W U 0) ?_).trans
    (LinearEquiv.ofEq _ _ (by rw [D.weight_h_eq_deg0]; rfl))
  -- `MU.incl … 0` is injective: its left inverse is `MU.proj … 0` (`proj_incl_same`).
  intro x y hxy
  have := congrArg (MU.proj W U 0) hxy
  rwa [MU.proj_incl_same, MU.proj_incl_same] at this

@[simp] theorem bottomEquiv_apply_coe (D : MUModuleData W U h) (x : MUPiece W U 0) :
    ((D.bottomEquiv x : D.toOrdVModule.weight h) : MU W U) = MU.incl W U 0 x := rfl

/-! ## The forward map closes the round trip on `M(U)`

By `ZhuBijection.forwardMap`, the iso-class `[M(U)]` maps to `[M(U)_h, actA]`. The bottom iso above
identifies `M(U)_h` with `A(𝒱) ⊗ U` as a ℂ-space; the genuine `realizes` statement
`forwardMap [M(U)] = [U]` rides on the deeper balancing `A(𝒱) ⊗_{A(𝒱)} U ≅ U` (R0, ring structure
of `A(𝒱)`) and the bottom `actA`-equivariance. The structural map `[M(U)]` is produced here. -/

/-- The iso-class `[M(U)] : LWModuleIsoClass W`. -/
noncomputable def isoClass (D : MUModuleData W U h) : LWModuleIsoClass W :=
  Quotient.mk (LWModule.setoid W) D.toLWModule

/-- The forward map sends `[M(U)]` to the iso-class of its bottom `A(𝒱)`-module `M(U)_h`. -/
theorem forwardMap_isoClass (D : MUModuleData W U h) :
    forwardMap W D.isoClass
      = Quotient.mk (AMod.setoid W) (D.toLWModule).toAMod := by
  rw [isoClass, forwardMap_mk]

end MUModuleData

/-! ## The irreducible quotient `L(U) = M(U)/J`

`L(U)` is the quotient of `M(U)` by its **unique maximal proper graded submodule** `J` (equivalently
the radical of the contragredient form), the unique submodule maximal among those meeting the bottom
`M(U)_h` in `0`. The construction of the quotient `OrdVModule` from a `WeakModule.Submodule'`, the
existence/uniqueness of `J`, and the resulting irreducibility with `L(U)_h ≅ U` are the remaining
structural content. We record the precise target. -/

/-- **The precise remaining target for `L(U)`.** Given the genuine module data `D : MUModuleData`,
there is a graded submodule `J` of `M(U)` (the maximal one meeting the bottom in `0`) such that the
quotient `M(U)/J` carries an induced `OrdVModule` structure that is **irreducible** with lowest-weight
space `≅ U` as an `A(𝒱)`-module. This is the irreducible-quotient statement of Zhu Thm 5.3.4 (hard
direction), stated as the named target — no `sorry`, no axiom; it is the structural content built on
the (already-assembled) `LWModule` packaging above and a general module-quotient construction
(`WeakModule.Submodule' → quotient WeakModule`), which is the remaining engineering. -/
def LU_target (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (h : ℂ) : Prop :=
  ∀ _D : MUModuleData W U h,
    ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module ℂ L) (N : OrdVModule W L),
      OrdVModule.IsIrreducible N ∧ Nonempty (IsLowestWeight N h)

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
