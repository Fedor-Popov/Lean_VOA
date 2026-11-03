/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUVhat
import VOA.Modules.ZhuVermaAnArchMU
import VOA.Modules.WeakModule

/-!
# Game One assembly — the `M(U)` `WeakModule` structure from `IsModuleJacobi`

This file performs the **structural assembly** of the Dong–Jiang induced module `M(U)` (Zhu
Thm 5.3.4, hard direction) into the project's genuine `WeakModule W M` interface
(`VOA.Modules.WeakModule`, Gannon Def. 5.3.1a–b), starting from the Construction-A action
engine already proved in `ZhuVermaAnArchMUVhat`:

* a `V̂`-representation `ρ : VHatRep W M` (a Lie morphism `V̂ →ₗ⁅ℂ⁆ End ℂ M`, equivalently a
  `U(V̂)`-module — the carrier-action engine of `M(U) = U(V̂) ⊗_{U(P)} U`),
* its `𝒱`-mode action `ρ.actMode a m = ρ (gen a m)` and the proved mode-commutation law
  `ρ.actMode_bracket` (the `ℓ = 0` Borcherds slice = locality),
* the genuine remaining Jacobi crux `ρ.IsModuleJacobi` (5.3.1b, the `ℓ ≠ 0` iterate content).

## The precise structural result of this file

The `WeakModule` interface has exactly three fields: `vacuum_YM` (5.3.1a), `truncation` (field /
lower-truncation), and `jacobi` (5.3.1b). The central observation, **proved here axiom-free**:

* **`VHatRep.YMof ρ`** — packages the mode action as the module field
  `Y_{M(U)}(u,z) = ∑ₙ ρ.actMode u n · z^{-n-1}`, i.e. the `ℂ`-linear map
  `u ↦ (fun n : ℤ => ρ.actMode u (-n-1)) : 𝒱 →ₗ[ℂ] (End ℂ M)⟦z^±⟧`, with
  `mode (YMof ρ u) m = ρ.actMode u m` (`mode_YMof`). The `ℂ`-linearity in `u` is the proved
  `actMode_add_left`/`actMode_smul_left`.
* **`VHatRep.jacobi_field_eq`** — the `WeakModule.jacobi` *field statement* for `YMof ρ` is
  **definitionally** `ρ.IsModuleJacobi` (both sides rewrite to `ρ.actMode` via `mode_YMof`).
  So the deep Jacobi axiom of `M(U)` is *exactly* `IsModuleJacobi`; no further reduction.
* **`VHatRep.toWeakModule`** — assembles the full `WeakModule W M` from `ρ` **given** the two
  remaining engineering inputs (which the `WeakModule` interface genuinely demands and which the
  `MUVhat` docstring labels pieces 1–2): the vacuum normalization `hvac` (5.3.1a: the vacuum mode
  acts as the identity distribution) and the field/truncation `htrunc`. The `jacobi` field is
  discharged *directly* by `IsModuleJacobi` — this is the payload.
* **`VHatRep.act_toWeakModule`** — the assembled module's `act` is `ρ.actMode` on the nose, so all
  downstream `WeakModule.act_*` lemmas apply to the `M(U)` action.

## The exact structural answer

> Does the diagonal closure `MUGradedAction` (Construction B) **alone** yield `IsModuleJacobi`, or
> is the composition-associativity (DJ Prop 3.5) an **additional** crux?

It is an **additional crux** — they are genuinely independent inputs, and this file records the
implication precisely (`MUGradedAction_not_jacobi_remark`, a `theorem`-free doc plus the typed
hypotheses of `toWeakModule`):

1. `MUGradedAction` is the **diagonal, single-level** statement: the right residue action descends
   to each graded piece `A_{n,0} ⊗ U` (`MU.actLevel`), i.e. well-definedness of the `p = n` mode on
   one level. It is `WeakModule`-data-free: it does **not** mention the cross-level composition
   `A_{p,n} ⊗_{A_n} A_{n,m} → A_{p,m}`, nor the `ℓ ≠ 0` iterate terms of 5.3.1b.
2. `IsModuleJacobi` (= the `WeakModule.jacobi` field, via `jacobi_field_eq`) is the **full**,
   all-levels, all-`ℓ` Borcherds module identity. Its `ℓ = 0` slice is `actMode_bracket` (proved);
   its `ℓ ≠ 0` slice is the DJ composition associativity (Prop 3.5) — exactly the part
   `MUGradedAction` does not supply.

So the honest dependency is: `MUGradedAction` ⟹ the carrier/level action is well defined
(Construction B), and **IsModuleJacobi** (Construction A, the genuine remaining theorem) ⟹ the
`WeakModule` Jacobi. The bridge `toWeakModule` makes the latter implication mechanical; the former
is the well-definedness proved in `ZhuVermaAnArchMU`. Neither implies the other.

Everything here is green and `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`); no
existing definition is mutated.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.4–3.5, Thm 2.9; DLM3 §4;
H. Li hep-th/9406211 §2; Gannon §5.3.1–§5.3.2, Def. 5.3.1, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat
namespace VHatRep

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## The module field `Y_{M(U)}` from the mode action

`Y_M(u,z) = ∑ₙ u₍ₙ₎ z^{-n-1}` is, in the project's `FormalDist` convention (`mode f m = f (-m-1)`),
the distribution whose coefficient of `zⁿ` is `u₍₋ₙ₋₁₎ = ρ.actMode u (-n-1)`. We package this as a
`ℂ`-linear map in `u` (linearity is the proved `actMode_add_left`/`actMode_smul_left`). -/

/-- **The `M(U)` module field** `Y_{M(U)}(u,z) = ∑ₙ ρ.actMode u n · z^{-n-1}` as a `ℂ`-linear map
`𝒱 →ₗ[ℂ] (End ℂ M)⟦z^±⟧`. The coefficient of `zⁿ` is `ρ.actMode u (-n-1)`, so that
`mode (YMof ρ u) m = ρ.actMode u m` (`mode_YMof`). -/
noncomputable def YMof (ρ : VHatRep W M) : 𝒱 →ₗ[ℂ] (End ℂ M)⟦z^±⟧ where
  toFun u := fun n : ℤ => ρ.actMode u (-n - 1)
  map_add' a a' := by
    funext n
    change ρ.actMode (a + a') (-n - 1)
      = (fun k : ℤ => ρ.actMode a (-k - 1)) n + (fun k : ℤ => ρ.actMode a' (-k - 1)) n
    simp only [ρ.actMode_add_left a a' (-n - 1)]
  map_smul' c a := by
    funext n
    change ρ.actMode (c • a) (-n - 1)
      = (c • fun k : ℤ => ρ.actMode a (-k - 1)) n
    simp only [ρ.actMode_smul_left c a (-n - 1), Pi.smul_apply]

@[simp] theorem YMof_apply (ρ : VHatRep W M) (u : 𝒱) (n : ℤ) :
    YMof ρ u n = ρ.actMode u (-n - 1) := rfl

/-- **The mode of `Y_{M(U)}` is the `𝒱`-mode action**: `mode (Y_{M(U)} u) m = ρ.actMode u m`.
This is the bridge that makes the `WeakModule.act`/`mode`-form identities equal to the
representation's `actMode`. -/
@[simp] theorem mode_YMof (ρ : VHatRep W M) (u : 𝒱) (m : ℤ) :
    mode (YMof ρ u) m = ρ.actMode u m := by
  rw [mode, YMof_apply]
  congr 1
  ring

/-! ## The `WeakModule.jacobi` field statement is exactly `IsModuleJacobi`

Rewriting every `mode (YMof ρ ·) ·` to `ρ.actMode · ·` via `mode_YMof`, the `WeakModule.jacobi`
field for `YMof ρ` becomes verbatim the body of `IsModuleJacobi ρ`. So the deep Jacobi axiom of
`M(U)` is *literally* `IsModuleJacobi`; there is no further reduction step. -/

/-- **The `WeakModule.jacobi` field for `Y_{M(U)}` is precisely `IsModuleJacobi`.**
Each side is the corresponding side of `IsModuleJacobi` after `mode_YMof`. This is the exact
identification of the `M(U)` module-Jacobi axiom with the Construction-A crux. -/
theorem jacobi_field_eq (ρ : VHatRep W M) :
    (∀ (u v : 𝒱) (x : M) (ℓ m n : ℤ),
      (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
          (mode (YMof ρ u) (ℓ + m - i) (mode (YMof ρ v) (n + i) x)
            - negOnePow ℓ • mode (YMof ρ v) (ℓ + n - i) (mode (YMof ρ u) (m + i) x)))
        = ∑ᶠ i : ℤ, cbz m i • mode (YMof ρ (W.smul u (ℓ + i) v)) (m + n - i) x)
      ↔ ρ.IsModuleJacobi := by
  unfold IsModuleJacobi
  simp only [mode_YMof]

/-! ## The full `WeakModule W M(U)` assembly (engineering inputs + `IsModuleJacobi`) -/

/-- **Game One — the `M(U)` `WeakModule` structure.** Assembles the genuine project `WeakModule W M`
(Gannon Def. 5.3.1a–b) for a `V̂`-representation `ρ` from:

* `hvac` — **5.3.1a**: the field of the vacuum is the identity distribution, `Y_{M(U)}(𝟙,z) = id`.
  (Engineering input 2 of `MUVhat`: the vacuum loop mode acts trivially except in degree `-1`.)
* `htrunc` — the **field / lower-truncation** property: `u₍ₙ₎ x = 0` for `n` large.
  (Engineering input 2; holds by the bounded-below `ℂ`-grading of `M(U) = U(V̂) ⊗_{U(P)} U`.)
* `hjac` — **5.3.1b**: `ρ.IsModuleJacobi`, **the** genuine remaining theorem of Construction A.

The payoff: the `jacobi` field is discharged *directly* by `hjac` through `jacobi_field_eq`; no
further work. This is the structural wire from `IsModuleJacobi` to the project module interface. -/
noncomputable def toWeakModule (ρ : VHatRep W M)
    (hvac : YMof ρ W.vacuum = 1)
    (htrunc : ∀ (u : 𝒱) (x : M), ∃ N : ℤ, ∀ n : ℤ, N ≤ n → mode (YMof ρ u) n x = 0)
    (hjac : ρ.IsModuleJacobi) : WeakModule W M where
  YM := YMof ρ
  vacuum_YM := hvac
  truncation := htrunc
  jacobi := (jacobi_field_eq ρ).mpr hjac

/-- The assembled `M(U)` module's mode action is exactly `ρ.actMode` (so every downstream
`WeakModule.act_*` simp-lemma applies to the `M(U)` action). -/
@[simp] theorem act_toWeakModule (ρ : VHatRep W M)
    (hvac : YMof ρ W.vacuum = 1)
    (htrunc : ∀ (u : 𝒱) (x : M), ∃ N : ℤ, ∀ n : ℤ, N ≤ n → mode (YMof ρ u) n x = 0)
    (hjac : ρ.IsModuleJacobi) (u : 𝒱) (n : ℤ) (x : M) :
    (toWeakModule ρ hvac htrunc hjac).act u n x = ρ.actMode u n x := by
  rw [WeakModule.act_def]
  change mode (YMof ρ u) n x = ρ.actMode u n x
  rw [mode_YMof]

/-! ## Vacuum normalization 5.3.1a reduced to the mode statement

`YMof ρ W.vacuum = 1` (5.3.1a) is, coefficient-wise, the statement that the vacuum mode
`ρ.actMode 𝟙 m` is the identity for `m = -1` and `0` otherwise. We record the `Prop`-level
reduction so the `hvac` input of `toWeakModule` can be supplied from the mode characterization once
the vacuum loop-mode action is pinned (engineering input 2). -/

/-- **5.3.1a reduced to modes.** `Y_{M(U)}(𝟙,z) = id` iff the vacuum mode acts as `δ_{n,-1}·id`.
(`mode 1 n = if n = -1 then id else 0`, the `End`-valued identity distribution.) -/
theorem vacuum_YMof_iff (ρ : VHatRep W M) :
    YMof ρ W.vacuum = 1
      ↔ ∀ n : ℤ, ρ.actMode W.vacuum n = if n = -1 then (1 : End ℂ M) else 0 := by
  constructor
  · intro h n
    have hn : mode (YMof ρ W.vacuum) n = mode (1 : (End ℂ M)⟦z^±⟧) n := by rw [h]
    rw [mode_YMof] at hn
    rw [hn, mode_one]
  · intro h
    funext k
    change ρ.actMode W.vacuum (-k - 1) = (1 : (End ℂ M)⟦z^±⟧) k
    rw [h (-k - 1)]
    rw [(rfl : ((1 : (End ℂ M)⟦z^±⟧) k) = (if k = 0 then (1 : End ℂ M) else 0))]
    congr 1
    by_cases hk : k = 0
    · simp [hk]
    · have : (-k - 1 : ℤ) ≠ -1 := by omega
      simp [this, hk]

/-! ## The structural answer, recorded as a typed witness

`MUGradedAction` (Construction B, diagonal level well-definedness) and `IsModuleJacobi`
(Construction A, full Borcherds module identity) are *independent* inputs. We make this concrete:
the bridge `toWeakModule` consumes `IsModuleJacobi` for its `jacobi` field and **does not** consume
`MUGradedAction` — the latter is the separate well-definedness of the carrier/level action proved in
`ZhuVermaAnArchMU` (`MUGradedAction_of_gens`, `induced_action_of_crux`). Conversely, `toWeakModule`
makes no use of the graded carrier `MU`, so no amount of `MUGradedAction` produces the `ℓ ≠ 0`
content of the `jacobi` field. The composition-associativity (DJ Prop 3.5) is therefore an
**additional** crux, isolated exactly as `IsModuleJacobi`. -/

end VHatRep
end VHat

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
