/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Foundations.Locality
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Pre-vertex algebras — Definition 5.1.3(a)  (Gannon p. 318)

**Lean name.**  Gannon's axioms VA1–VA5 below are formalized as `PreVertexAlgebra`: they contain
no translation covariance, so a `PreVertexAlgebra` is *not* a vertex algebra in the standard sense
(`VOA.TranslationCovariantCounterexample`).  The genuine notion is `VertexAlgebra`
(`VOA/Core/GenuineVertexAlgebra.lean`).

The central definition of the project. A vertex algebra packages infinitely many
bilinear products `u *ₙ v = u₍ₙ₎ v` into a single generating series, the **vertex
operator**
`Y(u, z) := ∑_{n ∈ ℤ} u₍ₙ₎ z^{-n-1} ∈ (End 𝒱)⟦z^±⟧`.

## Definition 5.1.3(a), verbatim

Let `𝒱 = ⊕_{n ∈ ℤ} 𝒱ₙ` be a graded vector space with each `𝒱ₙ` finite-dimensional.
Suppose given a linear map `u ↦ Y(u,z) = ∑_{n} u₍ₙ₎ z^{-n-1}` from `𝒱` into
`(End 𝒱)⟦z^±⟧`, and a distinguished vector `1 ∈ 𝒱₀` (the **vacuum**), obeying, for all
`u, v ∈ 𝒱`:

* **VA1 (grading).** For `u ∈ 𝒱ₖ`, the mode `u₍ₙ₎` is a linear map `𝒱ₗ → 𝒱_{k+ℓ-n-1}`.
* **VA2 (vacuum).** `Y(1, z) = id` (equivalently `1₍ₙ₎ v = δ_{n,-1} v`).
* **VA3 (state–field correspondence).** `Y(u, 0)1` exists and equals `u`
  (equivalently `u₍ₙ₎ 1 = 0` for `n ≥ 0` and `u₍₋₁₎ 1 = u`).
* **VA4 (locality).** `(z₁ - z₂)ᴹ [Y(u,z₁), Y(v,z₂)] = 0` for some `M = M(u,v) ∈ ℕ`.
* **VA5 (regularity).** there is `N = N(u,v)` with `u₍ₙ₎ v = 0` for all `n ≥ N`.

The triple `(𝒱, Y, 1)` is a **vertex algebra**; the `Y(u,z)` are vertex operators.

## Design / target declarations

```lean
/-- A vertex algebra (Gannon Def. 5.1.3(a)). `𝒱` carries an internal `ℤ`-grading with
finite-dimensional pieces; `Y` is the state–field correspondence. -/
structure PreVertexAlgebra (𝒱 : Type*) [AddCommGroup 𝒱] [Module ℂ 𝒱] where
  grading      : ℤ → Submodule ℂ 𝒱
  isInternal   : DirectSum.IsInternal grading
  finrank      : ∀ n, FiniteDimensional ℂ (grading n)
  Y            : 𝒱 →ₗ[ℂ] (End ℂ 𝒱)⟦z^±⟧
  vacuum       : 𝒱
  vacuum_mem   : vacuum ∈ grading 0
  -- VA1
  grading_mode : ∀ {k ℓ : ℤ} (u ∈ grading k) (v ∈ grading ℓ) (n : ℤ),
                   mode (Y u) n v ∈ grading (k + ℓ - n - 1)
  -- VA2
  vacuum_Y     : Y vacuum = (1 : (End ℂ 𝒱)⟦z^±⟧)        -- i.e. `Y(1,z) = id`
  -- VA3
  creation     : ∀ u, mode (Y u) (-1) vacuum = u ∧ ∀ n ≥ 0, mode (Y u) n vacuum = 0
  -- VA4
  locality     : ∀ u v, Local (Y u) (Y v)
  -- VA5
  regularity   : ∀ u v, ∃ N : ℤ, ∀ n ≥ N, mode (Y u) n v = 0

namespace PreVertexAlgebra
/-- The `n`-th product `u₍ₙ₎ v`. -/
def smul (V : PreVertexAlgebra 𝒱) (u : 𝒱) (n : ℤ) (v : 𝒱) : 𝒱 := mode (V.Y u) n v
notation u "⟨" n "⟩" v => ...
end PreVertexAlgebra
```

Modelling note: we keep the grading *internal* (a family of submodules of one space
`𝒱`) rather than an external `⊕`, to match Gannon's `𝒱 = ⊕ 𝒱ₙ` and to ease working
with `1, ω ∈ 𝒱`. See `README.md` for the discussion (internal vs external
grading; VA5 vs the `ℕ`-grading; finite-dimensionality of homogeneous pieces).

The vacuum field `Y(1,z) = id` is the **unit (identity) field** `1 : (End 𝒱)⟦z^±⟧`,
`δ_{n,0}·id` — *not* the constant series; see `FormalDist.one` below (a small
`One` instance for `𝒲⟦z^±⟧`, kept here in `Core` rather than in the
`Foundations` files; it carries **no** multiplication, in keeping with Paradox 5.1).

## Dependencies
* `VOA.Foundations.Locality` (and transitively all of `Foundations`).

## Status
Complete & `sorry`-free / axiom-free. The `structure PreVertexAlgebra`
(VA1–VA5) elaborates; the mode accessor `smul = u₍ₙ₎v` (the realized form of Gannon's
`u₍ₙ₎v`), its linearity, and the VA2/VA3/VA5 consequences are proved and `sorry`-free /
axiom-free (verified by `#print axioms` = `[propext, Classical.choice, Quot.sound]`). The
Borcherds master identity and the derived `T`/`L` calculus live in `Core.BorcherdsIdentity`
and `Core.Identities`.

## References
* Gannon §5.1.3; the historical definition is Borcherds (1986) [68]; the name and the
  `ω`-axioms are FLM [201]. See also Kac, Lepowsky–Li, Frenkel–Ben-Zvi.
-/

namespace VOA

open Module (End)

universe u

variable {𝒲 : Type*}

/-! ## The unit (identity) field on `𝒲⟦z^±⟧`

These are small helpers that morally belong in `Foundations.FormalSeries` /
`Foundations.FormalCalculus`, but are kept here so the `Foundations` files stay
independent of them.  The `One` instance is the vertex-operator unit `Y(𝟙,z) = id` of axiom VA2;
it carries **no** multiplication (Paradox 5.1 still forbids a ring on `FormalDist`). -/

namespace FormalDist

/-- The **identity / unit field** `1 := δ_{n,0}·1`: the formal distribution whose only
nonzero coefficient is `1 ∈ 𝒲`, in degree `0`. Models the vertex-operator unit
`Y(𝟙, z) = id` (Gannon Def. 5.1.3, axiom VA2). It is **not** the pointwise `1` of
`ℤ → 𝒲` (the constant series `δ(z)`); per Paradox 5.1 there is still no multiplication. -/
instance instOne [Zero 𝒲] [One 𝒲] : One (FormalDist 𝒲) := ⟨fun n => if n = 0 then 1 else 0⟩

@[simp] theorem one_apply [Zero 𝒲] [One 𝒲] (n : ℤ) :
    (1 : FormalDist 𝒲) n = if n = 0 then 1 else 0 := rfl

end FormalDist

/-- The mode of the unit field is concentrated at `m = -1`: `𝟙₍ₘ₎ = δ_{m,-1}·1`
(this is the mode form of VA2, `Y(𝟙,z) = id`). -/
@[simp] theorem mode_one [Zero 𝒲] [One 𝒲] (m : ℤ) :
    mode (1 : FormalDist 𝒲) m = if m = -1 then 1 else 0 := by
  rw [mode_apply, FormalDist.one_apply]
  by_cases h : m = -1
  · rw [if_pos h, if_pos (show (-m - 1 : ℤ) = 0 by omega)]
  · rw [if_neg h, if_neg (show ¬ (-m - 1 : ℤ) = 0 by omega)]

/-! ## Linearity of `mode` (helpers, morally in `Foundations.FormalCalculus`) -/

@[simp] theorem mode_add [AddCommGroup 𝒲] (f g : FormalDist 𝒲) (m : ℤ) :
    mode (f + g) m = mode f m + mode g m := rfl

@[simp] theorem mode_zero [AddCommGroup 𝒲] (m : ℤ) :
    mode (0 : FormalDist 𝒲) m = 0 := rfl

@[simp] theorem mode_neg [AddCommGroup 𝒲] (f : FormalDist 𝒲) (m : ℤ) :
    mode (-f) m = - mode f m := rfl

@[simp] theorem mode_sub [AddCommGroup 𝒲] (f g : FormalDist 𝒲) (m : ℤ) :
    mode (f - g) m = mode f m - mode g m := rfl

@[simp] theorem mode_smul [AddCommGroup 𝒲] [Module ℂ 𝒲] (c : ℂ) (f : FormalDist 𝒲) (m : ℤ) :
    mode (c • f) m = c • mode f m := rfl

/-! ## The vertex-algebra structure (Definition 5.1.3(a)) -/

/-- A **pre-vertex algebra**: the data and axioms VA1–VA5 of Gannon's Definition 5.1.3(a)
(p. 318).  `𝒱` carries an internal `ℤ`-grading (a family of submodules with
`DirectSum.IsInternal`) with finite-dimensional homogeneous pieces; `Y` is the state–field
correspondence `u ↦ Y(u,z) = ∑ₙ u₍ₙ₎ z^{-n-1}`, with vacuum `𝟙 ∈ 𝒱₀`, obeying VA1 (grading),
VA2 (vacuum), VA3 (creation), VA4 (locality) and VA5 (regularity).

⚠ **This is not a vertex algebra in the standard sense.**  There is **no translation-covariance
axiom** `Y(Tu,z) = ∂_z Y(u,z)`, and VA1–VA5 imply neither it nor the Borcherds/Jacobi identity:
`VOA.TranslationCovariantCounterexample.VA` is a 3-dimensional `PreVertexAlgebra` on which both
fail (`not_isTranslationCovariant`, `jacobi_fails`).
The genuine notion is `VOA.VertexAlgebra` (`VOA/Core/GenuineVertexAlgebra.lean`), a
`PreVertexAlgebra` together with `PreVertexAlgebra.IsTranslationCovariant`.  Every
`VertexOperatorAlgebra` is one (`VertexOperatorAlgebra.toVertexAlgebra`): covariance enters with
VOA3.  Results that need covariance on a bare `PreVertexAlgebra` take it as an explicit hypothesis. -/
structure PreVertexAlgebra (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] where
  /-- The internal `ℤ`-grading `𝒱 = ⊕ₙ 𝒱ₙ`, as a family of submodules of `𝒱`. -/
  grading : ℤ → Submodule ℂ 𝒱
  /-- The grading is a genuine internal direct-sum decomposition of `𝒱`. -/
  isInternal : DirectSum.IsInternal grading
  /-- Each homogeneous piece `𝒱ₙ` is finite-dimensional (Gannon Def. 5.1.3(a)). -/
  finrank : ∀ n, FiniteDimensional ℂ (grading n)
  /-- The state–field correspondence `Y(u,z) = ∑ₙ u₍ₙ₎ z^{-n-1}`, `ℂ`-linear in `u`. -/
  Y : 𝒱 →ₗ[ℂ] (End ℂ 𝒱)⟦z^±⟧
  /-- The vacuum vector `𝟙`. -/
  vacuum : 𝒱
  /-- The vacuum lies in degree `0`: `𝟙 ∈ 𝒱₀`. -/
  vacuum_mem : vacuum ∈ grading 0
  /-- **VA1 (grading).** For `u ∈ 𝒱ₖ` and `v ∈ 𝒱ₗ`, `u₍ₙ₎ v ∈ 𝒱_{k+ℓ-n-1}`. -/
  grading_mode : ∀ {k ℓ : ℤ} (u : 𝒱), u ∈ grading k → ∀ (v : 𝒱), v ∈ grading ℓ →
    ∀ (n : ℤ), mode (Y u) n v ∈ grading (k + ℓ - n - 1)
  /-- **VA2 (vacuum).** `Y(𝟙, z) = id`, the unit field. -/
  vacuum_Y : Y vacuum = (1 : (End ℂ 𝒱)⟦z^±⟧)
  /-- **VA3 (state–field correspondence).** `u₍₋₁₎ 𝟙 = u` and `u₍ₙ₎ 𝟙 = 0` for `n ≥ 0`. -/
  creation : ∀ u : 𝒱, mode (Y u) (-1) vacuum = u ∧ ∀ n : ℤ, 0 ≤ n → mode (Y u) n vacuum = 0
  /-- **VA4 (locality).** `Y(u,z₁)` and `Y(v,z₂)` are mutually local:
  `(z₁ - z₂)ᴹ [Y(u,z₁), Y(v,z₂)] = 0` for some `M = M(u,v)`. -/
  locality : ∀ u v : 𝒱, Local (Y u) (Y v)
  /-- **VA5 (regularity).** For each `u, v` there is `N` with `u₍ₙ₎ v = 0` for `n ≥ N`. -/
  regularity : ∀ u v : 𝒱, ∃ N : ℤ, ∀ n : ℤ, N ≤ n → mode (Y u) n v = 0

namespace PreVertexAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The `n`-th product `u₍ₙ₎ v` and its basic API -/

/-- The `n`-th product `u₍ₙ₎ v := mode (Y u) n v` (Gannon §5.1.3c): the coefficient of
`z^{-n-1}` in `Y(u,z)`, applied to `v`.  This is the mode accessor written `u₍ₙ₎v` in
Gannon; the ambient vertex algebra `V` is a bundled structure, so it appears explicitly
as `V.smul u n v`. -/
def smul (V : PreVertexAlgebra 𝒱) (u : 𝒱) (n : ℤ) (v : 𝒱) : 𝒱 := mode (V.Y u) n v

/-- Unfolding of the `n`-th product to the underlying mode. -/
theorem smul_def (V : PreVertexAlgebra 𝒱) (u : 𝒱) (n : ℤ) (v : 𝒱) :
    V.smul u n v = mode (V.Y u) n v := rfl

/-- The `n`-th product as the `z^{-n-1}` coefficient of `Y(u,z)` (Gannon §5.1.3c). -/
theorem smul_eq_coeff (V : PreVertexAlgebra 𝒱) (u : 𝒱) (n : ℤ) (v : 𝒱) :
    V.smul u n v = V.Y u (-n - 1) v := rfl

@[simp] theorem smul_add_left (V : PreVertexAlgebra 𝒱) (u₁ u₂ : 𝒱) (n : ℤ) (v : 𝒱) :
    V.smul (u₁ + u₂) n v = V.smul u₁ n v + V.smul u₂ n v := by
  simp only [smul_def, map_add, mode_add, LinearMap.add_apply]

@[simp] theorem smul_smul_left (V : PreVertexAlgebra 𝒱) (c : ℂ) (u : 𝒱) (n : ℤ) (v : 𝒱) :
    V.smul (c • u) n v = c • V.smul u n v := by
  simp only [smul_def, map_smul, mode_smul, LinearMap.smul_apply]

@[simp] theorem smul_zero_left (V : PreVertexAlgebra 𝒱) (n : ℤ) (v : 𝒱) :
    V.smul 0 n v = 0 := by
  simp only [smul_def, map_zero, mode_zero, LinearMap.zero_apply]

@[simp] theorem smul_add_right (V : PreVertexAlgebra 𝒱) (u : 𝒱) (n : ℤ) (v₁ v₂ : 𝒱) :
    V.smul u n (v₁ + v₂) = V.smul u n v₁ + V.smul u n v₂ :=
  map_add (mode (V.Y u) n) v₁ v₂

@[simp] theorem smul_smul_right (V : PreVertexAlgebra 𝒱) (u : 𝒱) (c : ℂ) (n : ℤ) (v : 𝒱) :
    V.smul u n (c • v) = c • V.smul u n v :=
  map_smul (mode (V.Y u) n) c v

@[simp] theorem smul_zero_right (V : PreVertexAlgebra 𝒱) (u : 𝒱) (n : ℤ) :
    V.smul u n 0 = 0 :=
  map_zero (mode (V.Y u) n)

/-! ## VA1: grading of the products -/

/-- **VA1**, in the `smul` API: for `u ∈ 𝒱ₖ`, `v ∈ 𝒱ₗ`, the product `u₍ₙ₎v` lies in
`𝒱_{k+ℓ-n-1}` (Gannon Def. 5.1.3(a)). -/
theorem smul_mem_grading (V : PreVertexAlgebra 𝒱) {k ℓ : ℤ} {u : 𝒱} (hu : u ∈ V.grading k)
    {v : 𝒱} (hv : v ∈ V.grading ℓ) (n : ℤ) :
    V.smul u n v ∈ V.grading (k + ℓ - n - 1) :=
  V.grading_mode u hu v hv n

/-! ## VA2: the vacuum field is the unit -/

/-- **VA2**, in the `smul` API: `𝟙₍ₙ₎ v = δ_{n,-1} v` (Gannon Def. 5.1.3(a)). -/
@[simp] theorem smul_vacuum_left (V : PreVertexAlgebra 𝒱) (n : ℤ) (v : 𝒱) :
    V.smul V.vacuum n v = if n = -1 then v else 0 := by
  rw [smul_def, V.vacuum_Y, mode_one]
  split_ifs <;> simp

/-! ## VA3: creation -/

/-- **VA3**, in the `smul` API (both clauses): `u₍₋₁₎𝟙 = u` and `u₍ₙ₎𝟙 = 0` for `n ≥ 0`
(Gannon Def. 5.1.3(a)). -/
theorem smul_vacuum_right (V : PreVertexAlgebra 𝒱) (u : 𝒱) :
    V.smul u (-1) V.vacuum = u ∧ ∀ n : ℤ, 0 ≤ n → V.smul u n V.vacuum = 0 :=
  V.creation u

/-- **VA3** (creation): `u₍₋₁₎ 𝟙 = u`. -/
@[simp] theorem smul_vacuum_neg_one (V : PreVertexAlgebra 𝒱) (u : 𝒱) :
    V.smul u (-1) V.vacuum = u := (V.creation u).1

/-- **VA3** (regularity on the vacuum): `u₍ₙ₎ 𝟙 = 0` for `n ≥ 0`. -/
theorem smul_vacuum_nonneg (V : PreVertexAlgebra 𝒱) (u : 𝒱) {n : ℤ} (hn : 0 ≤ n) :
    V.smul u n V.vacuum = 0 := (V.creation u).2 n hn

/-- `u₍₀₎ 𝟙 = 0` (the `n = 0` case of VA3). -/
@[simp] theorem smul_vacuum_zero (V : PreVertexAlgebra 𝒱) (u : 𝒱) :
    V.smul u 0 V.vacuum = 0 := (V.creation u).2 0 le_rfl

/-! ## VA5: regularity -/

/-- **VA5**, in the `smul` API: for each `u, v` the products `u₍ₙ₎v` vanish for `n` large
(Gannon Def. 5.1.3(a)).  This finiteness is what makes the doubly-infinite mode sums in
the Borcherds identity algebraically defined. -/
theorem smul_eventually_zero (V : PreVertexAlgebra 𝒱) (u v : 𝒱) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → V.smul u n v = 0 := V.regularity u v

end PreVertexAlgebra

end VOA
