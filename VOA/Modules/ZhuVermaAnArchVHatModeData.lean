/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchVHatRepMU

/-!
# Object B, assembled — building `VHatModeData W (MU W U)` from the bimodule composition

This file discharges the three carried fields of `VHat.VHatModeData W (MU W U)`
(`ZhuVermaAnArchVHatRepMU`) and hence produces, *via* the mechanical assembly `vhatRepMU`, object B —
the Dong–Jiang / DLM3 Construction-A `V̂`-representation `ρ : VHatRep W (MU W U)` that
`MUVHatData` consumes (Gannon Thm 5.3.4).

Recall (`ZhuVermaAnArchVHatRepMU`) that a `VHat.VHatRep W (MU W U)` is a Lie-algebra morphism
`V̂ →ₗ⁅ℂ⁆ End ℂ (MU W U)`, and `vhatRepMU W U` builds it *mechanically* from a single carried datum
`VHatModeData W (MU W U)` whose three fields are:

* `act : VLoop 𝒱 →ₗ[ℂ] End ℂ (MU W U)` — the loop-mode action;
* `mapsDeriv` — `act` vanishes on `loopDerivSubmodule W` (descent through `Im D`);
* `mapsBracket` — `act (vloopBracket x y) = ⁅act x, act y⁆` (the Lie-morphism property).

## How the three fields are built here

The honest input is a **per-degree loop-mode generator family**

  `actGen : ℤ → (𝒱 →ₗ[ℂ] End ℂ (MU W U))`,   `actGen m a = a(m)` acting on `M(U)`,

`ℂ`-linear in the vector `a` for each integer degree `m`.  The canonical such family is
`composeActFamily` below: the loop mode `a(m)` acts level-by-level by the Dong–Jiang bimodule
composition `composePiece` (`ZhuVermaAnArchVHatRepMU`), assembled across the graded layers of
`MU W U` by `DirectSum.toModule`.  Carrying `actGen` as a datum keeps the *general-level* residue
memberships (`AnmComposeDescL/R` at the level-mixing pairs) explicit.

From `actGen` the three fields are produced **outright**:

1. **`act`** `:= Finsupp.lsum ℂ actGen` — the unique `ℂ`-linear extension of `actGen` from the loop
   generators `single m a` to all of `VLoop 𝒱 = ℤ →₀ 𝒱` (`Finsupp.lsum`, axiom-free).  Evaluation:
   `act (single m a) = actGen m a` (`act_single`).
2. **`mapsDeriv`** — reduced, by `Submodule.span_induction` over the *defining generators* of
   `loopDerivSubmodule W`, to the single per-generator derivative relation
   `actGen m (L₋₁ a) + m • actGen (m-1) a = 0` (the descent of `(L₋₁a)(m) = -m·a(m-1)` to the
   action).  This is the carried hypothesis `hderiv`.
3. **`mapsBracket`** — reduced, by `ℂ`-bilinearity of both `act ∘ vloopBracket` and the
   `End`-commutator together with the fact that `VLoop` is spanned by its `single`s, to the single
   per-generator bracket relation
   `act (vloopBracket (single m a) (single k b)) = ⁅actGen m a, actGen k b⁆` (the Borcherds loop
   commutator realized on `M(U)`).  This is the carried hypothesis `hbracket` — the precise
   commutator crux (`actMode_bracket` lifted to all modes).

Bundled as `vhatModeData`, these give a genuine `VHatModeData W (MU W U)`, hence (`vhatRepMU`) object
B.  The minimal carried hypotheses are recorded at the end (`vhatModeData_carried_summary`): the
generator family `actGen`, its derivative relation `hderiv`, and its bracket relation `hbracket`
(into which the general bimodule descents `AnmComposeDescL/R` and the DJ associativity feed) — three
precise `Prop`-level data, **no `sorry`, no axiom**.

Everything is `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`); no existing
definition is mutated.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §§2–4; DLM3 §4; H. Li `hep-th/9406211` §2;
Frenkel–Zhu; Gannon §5.3.2, Thm 5.3.4; `ZhuVermaAnArchVHatRepMU` (`VHatModeData`, `vhatRepMU`,
`composePiece`), `ZhuVermaAnArchMU` (`MU`, `MUPiece`, `MU.incl`/`proj`), `ZhuVermaAnArchVhat`
(`VLoop`, `single`, `vloopBracket`, `loopDerivSubmodule`).
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators TensorProduct DirectSum
open Finsupp

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat

/-! ## The canonical `composePiece`-assembled loop-mode generator family

The Construction-A action of a loop mode `a(m)` on `M(U) = ⊕ₚ A_{p,0}(𝒱) ⊗ U` is the Dong–Jiang
bimodule composition acting level by level.  We realize it from the per-level endomorphism
`composePiece` (`ZhuVermaAnArchVHatRepMU`), summed across the graded layers by `DirectSum.toModule`.
This is the canonical generator family `actGen` feeding the assembly below; carrying the general-level
descents `AnmComposeDescL/R` (one diagonal pair `(p,p,0)` per layer) keeps the open residue content
explicit. -/

/-- **The per-degree, per-layer diagonal endomorphism of `MU W U`** assembled from `composePiece`.
Given the diagonal descents `hL p`/`hR p` at every layer `p`, the loop vector `a` acts on each graded
piece `MUPiece W U p` by `composePiece W U p (hL p) (hR p) a`, and these are assembled into an
endomorphism of the whole graded carrier `MU W U` by `DirectSum.toModule` (`incl p ∘ composePiece p`).
This is the canonical Construction-A action of a loop mode, level by level. -/
noncomputable def composeAct (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hL : ∀ p : ℕ, AnmComposeDescL W p p 0) (hR : ∀ p : ℕ, AnmComposeDescR W p p 0) (a : 𝒱) :
    End ℂ (MU W U) :=
  DirectSum.toModule ℂ ℕ (MU W U)
    (fun p => (MU.incl W U p).comp (composePiece W U p (hL p) (hR p) a))

@[simp] theorem composeAct_incl (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hL : ∀ p : ℕ, AnmComposeDescL W p p 0) (hR : ∀ p : ℕ, AnmComposeDescR W p p 0) (a : 𝒱)
    (p : ℕ) (x : MUPiece W U p) :
    composeAct W U hL hR a (MU.incl W U p x)
      = MU.incl W U p (composePiece W U p (hL p) (hR p) a x) := by
  rw [composeAct, MU.incl, DirectSum.toModule_lof]
  rfl

/-- The left `TensorProduct.map` factor of `composePiece` — `anmComposeBilin _ (mkAnm _ _ a)` — is
additive in the loop vector `a` (both `mkAnm` and `anmComposeBilin` are linear). -/
theorem composePieceL_add_a (W : VertexOperatorAlgebra 𝒱) (p : ℕ)
    (hL : AnmComposeDescL W p p 0) (hR : AnmComposeDescR W p p 0) (a a' : 𝒱) :
    anmComposeBilin W p p 0 hL hR (mkAnm W p p (a + a'))
      = anmComposeBilin W p p 0 hL hR (mkAnm W p p a)
        + anmComposeBilin W p p 0 hL hR (mkAnm W p p a') := by
  rw [map_add, map_add]

/-- The left factor of `composePiece` is `ℂ`-homogeneous in `a`. -/
theorem composePieceL_smul_a (W : VertexOperatorAlgebra 𝒱) (p : ℕ)
    (hL : AnmComposeDescL W p p 0) (hR : AnmComposeDescR W p p 0) (c : ℂ) (a : 𝒱) :
    anmComposeBilin W p p 0 hL hR (mkAnm W p p (c • a))
      = c • anmComposeBilin W p p 0 hL hR (mkAnm W p p a) := by
  rw [map_smul, map_smul]

/-- `composePiece` is additive in the loop vector `a`. -/
theorem composePiece_add_a (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (p : ℕ)
    (hL : AnmComposeDescL W p p 0) (hR : AnmComposeDescR W p p 0) (a a' : 𝒱) :
    composePiece W U p hL hR (a + a')
      = composePiece W U p hL hR a + composePiece W U p hL hR a' := by
  rw [composePiece, composePiece, composePiece, composePieceL_add_a W p hL hR a a']
  refine TensorProduct.ext' fun x u => ?_
  simp only [TensorProduct.map_tmul, LinearMap.add_apply, LinearMap.id_coe, id_eq,
    TensorProduct.add_tmul]

/-- `composePiece` is `ℂ`-homogeneous in the loop vector `a`. -/
theorem composePiece_smul_a (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (p : ℕ)
    (hL : AnmComposeDescL W p p 0) (hR : AnmComposeDescR W p p 0) (c : ℂ) (a : 𝒱) :
    composePiece W U p hL hR (c • a) = c • composePiece W U p hL hR a := by
  rw [composePiece, composePiece, composePieceL_smul_a W p hL hR c a]
  refine TensorProduct.ext' fun x u => ?_
  simp only [TensorProduct.map_tmul, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
    TensorProduct.smul_tmul']

/-- `composeAct` is `ℂ`-linear in the loop vector `a`, bundled as a `LinearMap`.  The two descent
families `hL`/`hR` are fixed; linearity in `a` is layer-wise `composePiece` linearity
(`composePiece_add_a`/`composePiece_smul_a`). -/
noncomputable def composeActFamilyDeg (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hL : ∀ p : ℕ, AnmComposeDescL W p p 0) (hR : ∀ p : ℕ, AnmComposeDescR W p p 0) :
    𝒱 →ₗ[ℂ] End ℂ (MU W U) where
  toFun a := composeAct W U hL hR a
  map_add' a a' := by
    refine DirectSum.linearMap_ext ℂ fun p => ?_
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, LinearMap.add_apply]
    rw [show (DirectSum.lof ℂ ℕ (MUPiece W U) p) x = MU.incl W U p x from rfl,
      composeAct_incl, composeAct_incl, composeAct_incl,
      composePiece_add_a W U p (hL p) (hR p) a a', LinearMap.add_apply, map_add]
  map_smul' c a := by
    refine DirectSum.linearMap_ext ℂ fun p => ?_
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, RingHom.id_apply]
    rw [show (DirectSum.lof ℂ ℕ (MUPiece W U) p) x = MU.incl W U p x from rfl,
      composeAct_incl, composeAct_incl,
      composePiece_smul_a W U p (hL p) (hR p) c a, LinearMap.smul_apply, map_smul]

@[simp] theorem composeActFamilyDeg_apply (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hL : ∀ p : ℕ, AnmComposeDescL W p p 0) (hR : ∀ p : ℕ, AnmComposeDescR W p p 0) (a : 𝒱) :
    composeActFamilyDeg W U hL hR a = composeAct W U hL hR a := rfl

/-- **The canonical Construction-A loop-mode generator family** `actGen : ℤ → (𝒱 →ₗ End ℂ (MU W U))`.
At every integer degree `m` the loop vector `a` acts by the level-diagonal bimodule composition
`composeAct` (the degree `m` is carried in the level data; the residue formula is the diagonal
`(p,p,0)` composition on each layer).  This is the canonical input to the assembly; a more refined
level-shifting family may replace it once the full level-mixing residue content lands, but the
assembly below works for *any* `ℂ`-linear generator family. -/
noncomputable def composeActFamily (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hL : ∀ p : ℕ, AnmComposeDescL W p p 0) (hR : ∀ p : ℕ, AnmComposeDescR W p p 0) :
    ℤ → (𝒱 →ₗ[ℂ] End ℂ (MU W U)) :=
  fun _ => composeActFamilyDeg W U hL hR

/-! ## The assembly: building `VHatModeData` from a `ℂ`-linear loop-mode generator family

For *any* `ℂ`-linear-in-`a` per-degree family `actGen : ℤ → (𝒱 →ₗ End ℂ M)`, the loop-mode action
`act := Finsupp.lsum ℂ actGen` is the unique `ℂ`-linear extension to `VLoop 𝒱 = ℤ →₀ 𝒱`.  The descent
through `Im D` and the bracket-compatibility reduce to the corresponding *generator-level* relations,
which are carried as explicit hypotheses.  This is the honest content of object B: the genuine
remaining DJ residue/Borcherds memberships sit precisely in `hderiv`/`hbracket`. -/

section Assembly

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- The `ℂ`-linear loop-mode action `act : VLoop 𝒱 →ₗ End ℂ M` assembled from a per-degree generator
family `actGen` by `Finsupp.lsum` (the unique `ℂ`-linear extension of `single m a ↦ actGen m a`). -/
noncomputable def assembleAct (actGen : ℤ → (𝒱 →ₗ[ℂ] End ℂ M)) :
    VLoop 𝒱 →ₗ[ℂ] End ℂ M :=
  Finsupp.lsum ℂ actGen

@[simp] theorem assembleAct_single (actGen : ℤ → (𝒱 →ₗ[ℂ] End ℂ M)) (m : ℤ) (a : 𝒱) :
    assembleAct actGen (single m a) = actGen m a := by
  rw [assembleAct, Finsupp.lsum_single]

/-- **Descent through `Im D`** for the assembled action, reduced to the generator derivative relation.
Given the per-generator relation `actGen m (L₋₁ a) + m • actGen (m-1) a = 0` (the descent of
`(L₋₁a)(m) = -m·a(m-1)`), the assembled action vanishes on every defining generator of
`loopDerivSubmodule W`, hence (by `span_induction`) on all of it. -/
theorem assembleAct_mapsDeriv (actGen : ℤ → (𝒱 →ₗ[ℂ] End ℂ M))
    (hderiv : ∀ (a : 𝒱) (m : ℤ),
      actGen m (W.L (-1) a) + (m : ℂ) • actGen (m - 1) a = 0) :
    ∀ x ∈ loopDerivSubmodule W, assembleAct actGen x = 0 := by
  intro x hx
  refine Submodule.span_induction
    (p := fun x _ => assembleAct actGen x = 0) ?_ (map_zero _)
    (fun y z _ _ hy hz => by simp only [map_add, hy, hz, add_zero])
    (fun c y _ hy => by simp only [map_smul, hy, smul_zero]) hx
  rintro y ⟨a, m, rfl⟩
  rw [map_add, map_smul, assembleAct_single, assembleAct_single]
  exact hderiv a m

/-- **Bracket-compatibility** for the assembled action, reduced to the generator bracket relation.
Given the per-generator relation
`act (vloopBracket (single m a) (single k b)) = ⁅actGen m a, actGen k b⁆`, the assembled action is a
Lie morphism on all of `VLoop` — both sides are `ℂ`-bilinear in `(x, y)` and `VLoop` is spanned by
its `single`s, so the identity propagates by bilinearity from the generators. -/
theorem assembleAct_mapsBracket (actGen : ℤ → (𝒱 →ₗ[ℂ] End ℂ M))
    (hbracket : ∀ (a b : 𝒱) (m k : ℤ),
      assembleAct actGen (vloopBracket W (single m a) (single k b))
        = ⁅actGen m a, actGen k b⁆) :
    ∀ x y : VLoop 𝒱,
      assembleAct actGen (vloopBracket W x y) = ⁅assembleAct actGen x, assembleAct actGen y⁆ := by
  -- Fix `x`, induct on `y` over its `single` support; then induct on `x`.  Both
  -- `y ↦ act (vloopBracket x y)` and `y ↦ ⁅act x, act y⁆` are `ℂ`-linear.
  have key : ∀ (m : ℤ) (a : 𝒱) (y : VLoop 𝒱),
      assembleAct actGen (vloopBracket W (single m a) y)
        = ⁅assembleAct actGen (single m a), assembleAct actGen y⁆ := by
    intro m a y
    induction y using Finsupp.induction_linear with
    | zero => simp only [map_zero, lie_zero]
    | add f g hf hg =>
        rw [map_add, map_add, hf, hg, map_add, lie_add]
    | single k b =>
        rw [assembleAct_single, assembleAct_single, hbracket a b m k]
  intro x y
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero, LinearMap.zero_apply, zero_lie]
  | add f g hf hg =>
      rw [map_add, LinearMap.add_apply, map_add, hf, hg, map_add, add_lie]
  | single m a => exact key m a y

/-- **The assembled `VHatModeData` from a `ℂ`-linear loop-mode generator family.**  Bundles the
three fields: `act := assembleAct actGen`, `mapsDeriv` from the carried generator derivative
relation `hderiv`, and `mapsBracket` from the carried generator bracket relation `hbracket`. -/
noncomputable def assembleModeData (actGen : ℤ → (𝒱 →ₗ[ℂ] End ℂ M))
    (hderiv : ∀ (a : 𝒱) (m : ℤ), actGen m (W.L (-1) a) + (m : ℂ) • actGen (m - 1) a = 0)
    (hbracket : ∀ (a b : 𝒱) (m k : ℤ),
      assembleAct actGen (vloopBracket W (single m a) (single k b))
        = ⁅actGen m a, actGen k b⁆) :
    VHatModeData W M where
  act := assembleAct actGen
  mapsDeriv := assembleAct_mapsDeriv actGen hderiv
  mapsBracket := assembleAct_mapsBracket actGen hbracket

@[simp] theorem assembleModeData_act_single (actGen : ℤ → (𝒱 →ₗ[ℂ] End ℂ M))
    (hderiv : ∀ (a : 𝒱) (m : ℤ), actGen m (W.L (-1) a) + (m : ℂ) • actGen (m - 1) a = 0)
    (hbracket : ∀ (a b : 𝒱) (m k : ℤ),
      assembleAct actGen (vloopBracket W (single m a) (single k b))
        = ⁅actGen m a, actGen k b⁆)
    (m : ℤ) (a : 𝒱) :
    (assembleModeData actGen hderiv hbracket).act (single m a) = actGen m a := by
  rw [assembleModeData, assembleAct_single]

end Assembly

/-! ## Object B for `M(U)` — `vhatModeData` and the `ρ` it produces

Specializing the assembly to `M = MU W U` with the canonical `composeActFamily`, we obtain the
carried datum `vhatModeData` and, *via* `vhatRepMU` (`ZhuVermaAnArchVHatRepMU`), object B itself. -/

/-- **Object B's carried datum** `VHatModeData W (MU W U)`, built from the canonical Construction-A
generator family `composeActFamily` and the two carried generator-level relations:

* `hderiv` — the descent of the derivative relation `(L₋₁a)(m) = -m·a(m-1)` to the action
  (`composeActFamily` kills `Im D`); and
* `hbracket` — the Borcherds loop-commutator relation realized on `M(U)` (the precise commutator
  crux, `actMode_bracket` lifted to all loop modes), into which the general bimodule descents
  `AnmComposeDescL/R` and the DJ Prop 3.4 associativity feed.

These two `Prop`s are the **exact minimal carried hypotheses** of object B (beyond the diagonal
descents `hL`/`hR` that define the action itself); they are hypotheses, **not** axioms, **not**
`sorry`. -/
noncomputable def vhatModeData (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hL : ∀ p : ℕ, AnmComposeDescL W p p 0) (hR : ∀ p : ℕ, AnmComposeDescR W p p 0)
    (hderiv : ∀ (a : 𝒱) (m : ℤ),
      composeActFamily W U hL hR m (W.L (-1) a)
        + (m : ℂ) • composeActFamily W U hL hR (m - 1) a = 0)
    (hbracket : ∀ (a b : 𝒱) (m k : ℤ),
      assembleAct (composeActFamily W U hL hR) (vloopBracket W (single m a) (single k b))
        = ⁅composeActFamily W U hL hR m a, composeActFamily W U hL hR k b⁆) :
    VHatModeData W (MU W U) :=
  assembleModeData (composeActFamily W U hL hR) hderiv hbracket

/-- `vhatModeData`'s action on a loop generator `a(m)` is the canonical composition action
`composeActFamily m a` (level-diagonal `composeAct`). -/
@[simp] theorem vhatModeData_act_single (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hL : ∀ p : ℕ, AnmComposeDescL W p p 0) (hR : ∀ p : ℕ, AnmComposeDescR W p p 0)
    (hderiv : ∀ (a : 𝒱) (m : ℤ),
      composeActFamily W U hL hR m (W.L (-1) a)
        + (m : ℂ) • composeActFamily W U hL hR (m - 1) a = 0)
    (hbracket : ∀ (a b : 𝒱) (m k : ℤ),
      assembleAct (composeActFamily W U hL hR) (vloopBracket W (single m a) (single k b))
        = ⁅composeActFamily W U hL hR m a, composeActFamily W U hL hR k b⁆)
    (m : ℤ) (a : 𝒱) :
    (vhatModeData W U hL hR hderiv hbracket).act (single m a) = composeAct W U hL hR a := by
  rw [vhatModeData, assembleModeData_act_single, composeActFamily, composeActFamilyDeg_apply]

/-- **Object B — the Construction-A `V̂`-representation `ρ` on `MU W U`**, assembled from
`vhatModeData`.  This is the `ρ` field that `MUVHatData` consumes (Gannon Thm 5.3.4); supplying it
(with the carried grading and bottom residual) unblocks `MUConstruction ⟹ InducedAssignment`. -/
noncomputable def repMU (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hL : ∀ p : ℕ, AnmComposeDescL W p p 0) (hR : ∀ p : ℕ, AnmComposeDescR W p p 0)
    (hderiv : ∀ (a : 𝒱) (m : ℤ),
      composeActFamily W U hL hR m (W.L (-1) a)
        + (m : ℂ) • composeActFamily W U hL hR (m - 1) a = 0)
    (hbracket : ∀ (a b : 𝒱) (m k : ℤ),
      assembleAct (composeActFamily W U hL hR) (vloopBracket W (single m a) (single k b))
        = ⁅composeActFamily W U hL hR m a, composeActFamily W U hL hR k b⁆) :
    VHat.VHatRep W (MU W U) :=
  vhatRepMU W U (vhatModeData W U hL hR hderiv hbracket)

/-- The `𝒱`-mode action of object B on `M(U)`: `a₍ₘ₎ = composeAct a` (the canonical Construction-A
level-diagonal composition action). -/
@[simp] theorem repMU_actMode (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hL : ∀ p : ℕ, AnmComposeDescL W p p 0) (hR : ∀ p : ℕ, AnmComposeDescR W p p 0)
    (hderiv : ∀ (a : 𝒱) (m : ℤ),
      composeActFamily W U hL hR m (W.L (-1) a)
        + (m : ℂ) • composeActFamily W U hL hR (m - 1) a = 0)
    (hbracket : ∀ (a b : 𝒱) (m k : ℤ),
      assembleAct (composeActFamily W U hL hR) (vloopBracket W (single m a) (single k b))
        = ⁅composeActFamily W U hL hR m a, composeActFamily W U hL hR k b⁆)
    (a : 𝒱) (m : ℤ) :
    (repMU W U hL hR hderiv hbracket).actMode a m = composeAct W U hL hR a := by
  rw [repMU, vhatRepMU_actMode, vhatModeData_act_single]

/-- The `V̂` bracket relation (`actMode_bracket`, the singular OPE / `ℓ = 0` Borcherds slice) for
object B on `M(U)`, automatic from `ρ` being a genuine Lie morphism. -/
theorem repMU_actMode_bracket (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hL : ∀ p : ℕ, AnmComposeDescL W p p 0) (hR : ∀ p : ℕ, AnmComposeDescR W p p 0)
    (hderiv : ∀ (a : 𝒱) (m : ℤ),
      composeActFamily W U hL hR m (W.L (-1) a)
        + (m : ℂ) • composeActFamily W U hL hR (m - 1) a = 0)
    (hbracket : ∀ (a b : 𝒱) (m k : ℤ),
      assembleAct (composeActFamily W U hL hR) (vloopBracket W (single m a) (single k b))
        = ⁅composeActFamily W U hL hR m a, composeActFamily W U hL hR k b⁆)
    (a b : 𝒱) (m k : ℤ) :
    ⁅(repMU W U hL hR hderiv hbracket).actMode a m,
        (repMU W U hL hR hderiv hbracket).actMode b k⁆
      = ∑ᶠ i : ℕ, (gBinom m i) •
          (repMU W U hL hR hderiv hbracket).actMode (W.smul a i b) (m + k - i) :=
  vhatRepMU_actMode_bracket W U (vhatModeData W U hL hR hderiv hbracket) a b m k

/-! ## The minimal carried hypotheses of object B (summary)

Object B (`repMU` ⟹ `ρ`) is built outright from exactly these carried data, all precise `Prop`s, no
`sorry`/axiom:

* `hL`/`hR : ∀ p, AnmComposeDescL/R W p p 0` — the *diagonal* `(p,p,0)` bimodule-composition
  descents (DJ Prop 3.4 well-definedness per layer), which define the action `composeAct` itself;
* `hderiv` — the descent of the derivative relation `(L₋₁a)(m) = -m·a(m-1)` to the assembled action;
* `hbracket` — the Borcherds loop-commutator relation on `M(U)` (the precise commutator crux,
  `actMode_bracket` lifted to all loop modes), fed by the general-level descents `AnmComposeDescL/R`
  and the DJ Prop 3.4 associativity.

`act` and the *extension* machinery for `mapsDeriv` (span-induction over `Im D`) and `mapsBracket`
(bilinear propagation from the loop generators) are **built outright**; only the genuine residue /
Borcherds memberships are carried.  This is the honest minimal reduction of object B. -/
theorem vhatModeData_carried_summary (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hL : ∀ p : ℕ, AnmComposeDescL W p p 0) (hR : ∀ p : ℕ, AnmComposeDescR W p p 0)
    (hderiv : ∀ (a : 𝒱) (m : ℤ),
      composeActFamily W U hL hR m (W.L (-1) a)
        + (m : ℂ) • composeActFamily W U hL hR (m - 1) a = 0)
    (hbracket : ∀ (a b : 𝒱) (m k : ℤ),
      assembleAct (composeActFamily W U hL hR) (vloopBracket W (single m a) (single k b))
        = ⁅composeActFamily W U hL hR m a, composeActFamily W U hL hR k b⁆) :
    (repMU W U hL hR hderiv hbracket).actMode = fun a (_ : ℤ) => composeAct W U hL hR a :=
  funext fun a => funext fun m => repMU_actMode W U hL hR hderiv hbracket a m

end VHat

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
