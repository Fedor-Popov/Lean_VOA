/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.VertexAlgebra
import VOA.Foundations.Virasoro

/-!
# Vertex operator algebras — Definition 5.1.3(b),(c)  (Gannon p. 318)

A **vertex operator algebra** is a vertex algebra with a distinguished **conformal
vector** `ω ∈ 𝒱₂` whose modes generate a Virasoro action implementing the grading.

## Definition 5.1.3(b), verbatim

A vertex algebra `(𝒱, Y, 1)` is a **VOA** if there is `ω ∈ 𝒱₂` such that, writing
`Lₙ := ω₍ₙ₊₁₎`:

* **VOA1 (conformal symmetry).** the `Lₙ` form a `𝔙𝔦𝔯`-module whose central term acts
  as `c · id_𝒱` for some `c ∈ ℂ` (the **central charge** / rank). Explicitly
  `[Lₘ, Lₙ] = (m-n)L_{m+n} + (c/12)(m³-m)δ_{m+n,0}`.
* **VOA2 (conformal weight).** `L₀ v = n v` whenever `v ∈ 𝒱ₙ`.
* **VOA3 (translation generator).** `Y(L₋₁ v, z) = ∂_z Y(v, z)`.
* **VOA4 (CFT type).** `𝒱₀ = ℂ1` and `𝒱ₙ = {0}` for all `n < 0`.

`ω` is the conformal vector; `c` the central charge; the grade `n` of `u ∈ 𝒱ₙ` its
**conformal weight**.

## Definition 5.1.3(c)

A quadruple `(𝒱, Y, 1, ω)` is a **near-VOA** if all VOA axioms hold *except VOA4*, and
the `𝒱ₙ` are allowed to be infinite-dimensional. (Needed for indefinite lattices
§5.2.2 and for the Monster Lie algebra §7.2.2.)

## Design / target declarations

```lean
/-- A vertex operator algebra (Gannon Def. 5.1.3(b)): a vertex algebra with a
conformal vector. We expose `L n` as a convenience for `ω₍ₙ₊₁₎`. -/
structure VertexOperatorAlgebra (𝒱 : Type*) [AddCommGroup 𝒱] [Module ℂ 𝒱]
    extends PreVertexAlgebra 𝒱 where
  conformalVector : 𝒱
  conformal_mem   : conformalVector ∈ grading 2
  centralCharge   : ℂ
  -- VOA1: `L n := (conformalVector)₍ₙ₊₁₎` satisfy the Virasoro relations with `c`.
  virasoro        : ∀ m n : ℤ, ⁅L m, L n⁆ =
                      (m - n) • L (m + n)
                        + (if m + n = 0 then ((m^3 - m)/12 * centralCharge) • 1 else 0)
  -- VOA2
  L0_grading      : ∀ {n : ℤ} (v ∈ grading n), L 0 v = (n : ℂ) • v
  -- VOA3
  translation     : ∀ v, Y (L (-1) v) = deriv (Y v)
  -- VOA4 (CFT type)
  vacuum_grade    : grading 0 = ℂ ∙ vacuum
  positivity      : ∀ n < 0, grading n = ⊥
where  -- `L n` is the abbreviation `mode (Y conformalVector) (n+1)`
  L : ℤ → End ℂ 𝒱 := fun n => mode (Y conformalVector) (n + 1)

/-- A near-VOA: VOA1–VOA3 but not necessarily VOA4, with possibly
infinite-dimensional homogeneous pieces (Gannon Def. 5.1.3(c)). -/
structure NearVOA (𝒱 : Type*) [AddCommGroup 𝒱] [Module ℂ 𝒱] where ...
```

Implementation note (the `L`-abbreviation): a Lean `structure` cannot refer, inside its
own field types, to a definition introduced only after the structure.  So the fields
spell out `mode (Y conformalVector) (n+1)` directly, and `L : ℤ → End ℂ 𝒱` together with
its VOA1–VOA3 restatements (`L_virasoro`, `L_zero_grading`, `Y_L_neg_one`) are provided
just after the structure.  This realises the sketched `where L := …` faithfully.

Immediate consequences recorded below (Gannon p. 319): `1 ∈ 𝒱₀` (`vacuum_mem`) and
`ω ∈ 𝒱₂` (`conformal_mem`) hold by construction; `L₋₁, L₀, L₁` span a copy of `𝔰𝔩₂(ℂ)`,
exhibited here by the three structure relations `[L₁,L₋₁] = 2L₀`, `[L₀,L₁] = -L₁`,
`[L₀,L₋₁] = L₋₁` (the central term drops out because `1³-1 = 0³-0 = 0`).

## Dependencies
* `VOA.Core.VertexAlgebra`, `VOA.Foundations.Virasoro`.

## Status
Complete & `sorry`-free / axiom-free. The `structure
VertexOperatorAlgebra extends PreVertexAlgebra` (VOA1–VOA4), the `L n := ω₍ₙ₊₁₎` abbreviation
with its VOA1–VOA3 restatements, the `𝔰𝔩₂`-triple relations, the `NearVOA` of 5.1.3(c) and
the forgetful `toNearVOA` are all proved and `sorry`-free / axiom-free (verified by
`#print axioms` = `[propext, Classical.choice, Quot.sound]`).

## References
* Gannon §5.1.3; FLM [201]; Frenkel–Huang–Lepowsky [197]; Lepowsky–Li.
-/

namespace VOA

open Module (End)

universe u

/-! ## The vertex-operator-algebra structure (Definition 5.1.3(b)) -/

/-- A **graded vertex operator algebra** in the sense of Frenkel–Lepowsky–Meurman and
Lepowsky–Li (FLM §8.10, LL Def. 3.1.22), with the library's conventions: a `PreVertexAlgebra`
(graded VA1–VA5 data with finite-dimensional homogeneous pieces) carrying a conformal vector
`ω ∈ 𝒱₂` and a central charge `c`, whose Virasoro modes `Lₙ := ω₍ₙ₊₁₎ = mode (Y ω) (n+1)`
implement the conformal symmetry (VOA1), the grading (VOA2) and translation (VOA3), and whose
grading is **truncated from below** (`𝒱ₙ = 0` for `n ≪ 0`).  VOA3 makes the underlying
`PreVertexAlgebra` translation covariant.

This is the general notion: it does **not** impose the CFT-type axiom VOA4
(`𝒱₀ = ℂ𝟙`, `𝒱ₙ = 0` for `n < 0`).  The CFT-type notion used throughout the library,
`VertexOperatorAlgebra`, extends this structure by exactly those two fields. -/
structure GradedVertexOperatorAlgebra (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱]
    extends PreVertexAlgebra 𝒱 where
  /-- The conformal vector `ω`. -/
  conformalVector : 𝒱
  /-- The conformal vector lies in degree `2`: `ω ∈ 𝒱₂`. -/
  conformal_mem : conformalVector ∈ grading 2
  /-- The central charge / rank `c ∈ ℂ`. -/
  centralCharge : ℂ
  /-- **VOA1 (conformal symmetry).** Writing `Lₙ = ω₍ₙ₊₁₎ = mode (Y ω) (n+1)`, the modes
  obey the Virasoro relation `[Lₘ,Lₙ] = (m-n)L_{m+n} + (c/12)(m³-m)δ_{m+n,0}`. -/
  virasoro : ∀ m n : ℤ,
      ⁅mode (Y conformalVector) (m + 1), mode (Y conformalVector) (n + 1)⁆
        = ((m : ℂ) - n) • mode (Y conformalVector) (m + n + 1)
          + (if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * centralCharge) • (1 : End ℂ 𝒱)
             else 0)
  /-- **VOA2 (conformal weight).** `L₀ = mode (Y ω) 1` acts on `𝒱ₙ` as multiplication by
  `n`: `L₀ v = n • v` for `v ∈ 𝒱ₙ`. -/
  L0_grading : ∀ {n : ℤ} (v : 𝒱), v ∈ grading n → mode (Y conformalVector) 1 v = (n : ℂ) • v
  /-- **VOA3 (translation generator).** `Y(L₋₁ v, z) = ∂_z Y(v,z)`, where
  `L₋₁ = mode (Y ω) 0`. -/
  translation : ∀ v : 𝒱, Y (mode (Y conformalVector) 0 v) = deriv (Y v)
  /-- **Grading truncation** (FLM/LL): `𝒱ₙ = 0` for all sufficiently negative `n`. -/
  grading_bounded_below : ∃ N : ℤ, ∀ n : ℤ, n < N → grading n = ⊥

/-- A **vertex operator algebra** (Gannon Def. 5.1.3(b), p. 318): a pre-vertex algebra with a
conformal vector `ω ∈ 𝒱₂` and a central charge `c`, whose Virasoro modes
`Lₙ := ω₍ₙ₊₁₎ = mode (Y ω) (n+1)` implement the conformal symmetry (VOA1), the grading
(VOA2) and translation (VOA3), and which is of CFT type (VOA4).  The abbreviation `L n`
is introduced after the structure (see `VertexOperatorAlgebra.L`).

Layering: this is a `GradedVertexOperatorAlgebra` (the general FLM/LL notion) together with
the two CFT-type fields `vacuum_grade` and `positivity`.  The truncation field
`grading_bounded_below` of the parent is filled automatically from `positivity`
(`N = 0`), so constructions need not supply it.  By VOA3 every VOA is a genuine vertex algebra
(`VertexOperatorAlgebra.toVertexAlgebra`). -/
structure VertexOperatorAlgebra (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱]
    extends GradedVertexOperatorAlgebra 𝒱 where
  /-- **VOA4 (CFT type), part 1.** `𝒱₀ = ℂ𝟙`. -/
  vacuum_grade : grading 0 = ℂ ∙ vacuum
  /-- **VOA4 (CFT type), part 2.** `𝒱ₙ = 0` for `n < 0`. -/
  positivity : ∀ n : ℤ, n < 0 → grading n = ⊥
  grading_bounded_below := ⟨0, positivity⟩

namespace GradedVertexOperatorAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- The Virasoro mode `Lₙ := ω₍ₙ₊₁₎` of a graded (not necessarily CFT-type) VOA. -/
def L (W : GradedVertexOperatorAlgebra 𝒱) (n : ℤ) : End ℂ 𝒱 :=
  mode (W.Y W.conformalVector) (n + 1)

theorem L_def (W : GradedVertexOperatorAlgebra 𝒱) (n : ℤ) :
    W.L n = mode (W.Y W.conformalVector) (n + 1) := rfl

/-- **VOA1** in terms of `L`, for a graded VOA. -/
theorem L_virasoro (W : GradedVertexOperatorAlgebra 𝒱) (m n : ℤ) :
    ⁅W.L m, W.L n⁆ = ((m : ℂ) - n) • W.L (m + n)
      + (if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * W.centralCharge) • (1 : End ℂ 𝒱)
         else 0) :=
  W.virasoro m n

/-- **VOA2** in terms of `L`, for a graded VOA. -/
theorem L_zero_grading (W : GradedVertexOperatorAlgebra 𝒱) {n : ℤ} (v : 𝒱)
    (hv : v ∈ W.grading n) : W.L 0 v = (n : ℂ) • v :=
  W.L0_grading v hv

/-- **VOA3** in terms of `L`, for a graded VOA. -/
theorem Y_L_neg_one (W : GradedVertexOperatorAlgebra 𝒱) (v : 𝒱) :
    W.Y (W.L (-1) v) = deriv (W.Y v) :=
  W.translation v

end GradedVertexOperatorAlgebra

namespace VertexOperatorAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- The Virasoro modes of a CFT-type VOA are those of its underlying graded VOA. -/
theorem toGradedVertexOperatorAlgebra_L (W : VertexOperatorAlgebra 𝒱) (n : ℤ) :
    W.toGradedVertexOperatorAlgebra.L n = mode (W.Y W.conformalVector) (n + 1) := rfl

/-- A CFT-type VOA is truncated from below at `0` (the parent truncation field). -/
theorem grading_bounded_below_eq (W : VertexOperatorAlgebra 𝒱) :
    ∃ N : ℤ, ∀ n : ℤ, n < N → W.grading n = ⊥ := ⟨0, W.positivity⟩

end VertexOperatorAlgebra

namespace VertexOperatorAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The Virasoro modes `L n := ω₍ₙ₊₁₎` -/

/-- The Virasoro mode `Lₙ := ω₍ₙ₊₁₎ = mode (Y ω) (n+1)` (Gannon p. 318; note the `+1`
mode shift, `CONVENTIONS` §5). -/
def L (W : VertexOperatorAlgebra 𝒱) (n : ℤ) : End ℂ 𝒱 :=
  mode (W.Y W.conformalVector) (n + 1)

theorem L_def (W : VertexOperatorAlgebra 𝒱) (n : ℤ) :
    W.L n = mode (W.Y W.conformalVector) (n + 1) := rfl

/-- **VOA1** in terms of `L`: the Virasoro relation
`[Lₘ, Lₙ] = (m-n)L_{m+n} + (c/12)(m³-m)δ_{m+n,0}` (Gannon Def. 5.1.3, cf. eq. 3.1.5). -/
theorem L_virasoro (W : VertexOperatorAlgebra 𝒱) (m n : ℤ) :
    ⁅W.L m, W.L n⁆ = ((m : ℂ) - n) • W.L (m + n)
      + (if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * W.centralCharge) • (1 : End ℂ 𝒱)
         else 0) := by
  simp only [L_def]
  exact W.virasoro m n

/-- **VOA2** in terms of `L`: `L₀` acts on `𝒱ₙ` as multiplication by the conformal
weight `n` (Gannon Def. 5.1.3). -/
theorem L_zero_grading (W : VertexOperatorAlgebra 𝒱) {n : ℤ} (v : 𝒱) (hv : v ∈ W.grading n) :
    W.L 0 v = (n : ℂ) • v := by
  rw [L_def]
  exact W.L0_grading v hv

/-- **VOA3** in terms of `L`: `L₋₁` is the translation generator,
`Y(L₋₁ v, z) = ∂_z Y(v,z)` (Gannon Def. 5.1.3, eq. 5.1.8). -/
theorem Y_L_neg_one (W : VertexOperatorAlgebra 𝒱) (v : 𝒱) :
    W.Y (W.L (-1) v) = deriv (W.Y v) := by
  rw [L_def]
  exact W.translation v

/-! ## `1 ∈ 𝒱₀` and `ω ∈ 𝒱₂` (Gannon p. 319) -/

/-- The vacuum lies in degree `0` (a structure field, recorded for the `L`-API). -/
theorem vacuum_mem_grading_zero (W : VertexOperatorAlgebra 𝒱) : W.vacuum ∈ W.grading 0 :=
  W.vacuum_mem

/-- The conformal vector lies in degree `2`: `ω ∈ 𝒱₂`. -/
theorem conformalVector_mem_grading_two (W : VertexOperatorAlgebra 𝒱) :
    W.conformalVector ∈ W.grading 2 := W.conformal_mem

/-! ## The `𝔰𝔩₂`-triple `L₋₁, L₀, L₁` (Gannon Question 5.1.5b) -/

/-- `[L₁, L₋₁] = 2 L₀`: the central term vanishes since `1³ - 1 = 0`.  Together with
`L_zero_L_one` and `L_zero_L_neg_one` this exhibits `L₋₁, L₀, L₁` as an `𝔰𝔩₂(ℂ)`-triple
(`e = L₁, h = -2L₀ … `, Gannon Question 5.1.5b). -/
theorem L_one_L_neg_one (W : VertexOperatorAlgebra 𝒱) :
    ⁅W.L 1, W.L (-1)⁆ = (2 : ℂ) • W.L 0 := by
  have key := W.L_virasoro 1 (-1)
  rw [show (1 : ℤ) + (-1) = 0 by ring] at key
  rw [key]; norm_num

/-- `[L₀, L₁] = - L₁` (the `𝔰𝔩₂` relation `[h/2, e] = e` up to sign convention). -/
theorem L_zero_L_one (W : VertexOperatorAlgebra 𝒱) : ⁅W.L 0, W.L 1⁆ = - W.L 1 := by
  have key := W.L_virasoro 0 1
  rw [show (0 : ℤ) + 1 = 1 by ring] at key
  rw [key]; norm_num [neg_one_smul]

/-- `[L₀, L₋₁] = L₋₁` (the `𝔰𝔩₂` relation `[h/2, f] = -f` up to sign convention). -/
theorem L_zero_L_neg_one (W : VertexOperatorAlgebra 𝒱) : ⁅W.L 0, W.L (-1)⁆ = W.L (-1) := by
  have key := W.L_virasoro 0 (-1)
  rw [show (0 : ℤ) + (-1) = -1 by ring] at key
  rw [key]; norm_num

end VertexOperatorAlgebra

/-! ## Near-VOAs (Definition 5.1.3(c)) -/

/-- A **near-VOA** (Gannon Def. 5.1.3(c), p. 318): the VOA1–VOA3 data — a vacuum, a
conformal vector `ω` with central charge `c`, the Virasoro relations, the `L₀`-grading
and the translation property — but **without VOA4** (CFT type) and **without** the
finite-dimensionality of the homogeneous pieces.  (Needed for indefinite-lattice VOAs
§5.2.2 and the Monster Lie algebra §7.2.2.)  Because it drops the finite-dimensionality
field of `PreVertexAlgebra`, it is spelled out as a standalone structure rather than an
extension; every `VertexOperatorAlgebra` yields one via `toNearVOA`. -/
structure NearVOA (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] where
  /-- The internal `ℤ`-grading (pieces possibly infinite-dimensional). -/
  grading : ℤ → Submodule ℂ 𝒱
  /-- The grading is an internal direct-sum decomposition of `𝒱`. -/
  isInternal : DirectSum.IsInternal grading
  /-- The state–field correspondence. -/
  Y : 𝒱 →ₗ[ℂ] (End ℂ 𝒱)⟦z^±⟧
  /-- The vacuum vector. -/
  vacuum : 𝒱
  /-- `𝟙 ∈ 𝒱₀`. -/
  vacuum_mem : vacuum ∈ grading 0
  /-- **VA1.** -/
  grading_mode : ∀ {k ℓ : ℤ} (u : 𝒱), u ∈ grading k → ∀ (v : 𝒱), v ∈ grading ℓ →
    ∀ (n : ℤ), mode (Y u) n v ∈ grading (k + ℓ - n - 1)
  /-- **VA2.** -/
  vacuum_Y : Y vacuum = (1 : (End ℂ 𝒱)⟦z^±⟧)
  /-- **VA3.** -/
  creation : ∀ u : 𝒱, mode (Y u) (-1) vacuum = u ∧ ∀ n : ℤ, 0 ≤ n → mode (Y u) n vacuum = 0
  /-- **VA4 (locality).** -/
  locality : ∀ u v : 𝒱, Local (Y u) (Y v)
  /-- **VA5 (regularity).** -/
  regularity : ∀ u v : 𝒱, ∃ N : ℤ, ∀ n : ℤ, N ≤ n → mode (Y u) n v = 0
  /-- The conformal vector `ω`. -/
  conformalVector : 𝒱
  /-- `ω ∈ 𝒱₂`. -/
  conformal_mem : conformalVector ∈ grading 2
  /-- The central charge `c`. -/
  centralCharge : ℂ
  /-- **VOA1.** -/
  virasoro : ∀ m n : ℤ,
      ⁅mode (Y conformalVector) (m + 1), mode (Y conformalVector) (n + 1)⁆
        = ((m : ℂ) - n) • mode (Y conformalVector) (m + n + 1)
          + (if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * centralCharge) • (1 : End ℂ 𝒱)
             else 0)
  /-- **VOA2.** -/
  L0_grading : ∀ {n : ℤ} (v : 𝒱), v ∈ grading n → mode (Y conformalVector) 1 v = (n : ℂ) • v
  /-- **VOA3.** -/
  translation : ∀ v : 𝒱, Y (mode (Y conformalVector) 0 v) = deriv (Y v)

/-- Every vertex operator algebra is a near-VOA: forget the finite-dimensionality of the
homogeneous pieces and the CFT-type axiom VOA4 (Gannon Def. 5.1.3(c)). -/
def VertexOperatorAlgebra.toNearVOA {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (W : VertexOperatorAlgebra 𝒱) : NearVOA 𝒱 where
  grading := W.grading
  isInternal := W.isInternal
  Y := W.Y
  vacuum := W.vacuum
  vacuum_mem := W.vacuum_mem
  grading_mode := W.grading_mode
  vacuum_Y := W.vacuum_Y
  creation := W.creation
  locality := W.locality
  regularity := W.regularity
  conformalVector := W.conformalVector
  conformal_mem := W.conformal_mem
  centralCharge := W.centralCharge
  virasoro := W.virasoro
  L0_grading := W.L0_grading
  translation := W.translation

/-- Every graded vertex operator algebra (FLM/LL, not necessarily of CFT type) is a
near-VOA: forget the finite-dimensionality of the homogeneous pieces and the truncation. -/
def GradedVertexOperatorAlgebra.toNearVOA {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (W : GradedVertexOperatorAlgebra 𝒱) : NearVOA 𝒱 where
  grading := W.grading
  isInternal := W.isInternal
  Y := W.Y
  vacuum := W.vacuum
  vacuum_mem := W.vacuum_mem
  grading_mode := W.grading_mode
  vacuum_Y := W.vacuum_Y
  creation := W.creation
  locality := W.locality
  regularity := W.regularity
  conformalVector := W.conformalVector
  conformal_mem := W.conformal_mem
  centralCharge := W.centralCharge
  virasoro := W.virasoro
  L0_grading := W.L0_grading
  translation := W.translation

end VOA
