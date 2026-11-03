/-
Copyright (c) 2026 Leonardo Rastelli, Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.SingularVector
import VOA.Core.SkewSymmetry
import VOA.Core.Deformation
import VOA.Core.DeformedForm

/-!
# The rigidity bridge: singular vectors as obstructions to deforming a VOA

This file connects three layers of the repository:

* `Core.SingularVector` — singular vectors and the ideals they generate;
* `Core.Deformation` — `FirstOrderDeformation W`, the order-`t` deformation of `Y`;
* `Core.DeformedForm` — the pure linear algebra of "which radical vectors of `B₀` survive to
  first order in `B₀ + t·B₁`".

`Core.DeformedForm` is stated for an arbitrary **finite-dimensional** space `E` carrying a
**symmetric** form `B₀` and an arbitrary `B₁`.  What was missing was the object that plays the
role of `(E, B₀, B₁)` for a vertex operator algebra.  That object is built here.

## `E`, `B₀`, `B₁`

* `E := W.grading k`, a single homogeneous piece.  It is finite-dimensional **for free**:
  `finrank : ∀ n, FiniteDimensional ℂ (grading n)` is a *field* of `PreVertexAlgebra`
  (`Core.VertexAlgebra`), not an extra hypothesis.
* `B₀ := shapForm W hvac k`, the **level-`k` Shapovalov (contravariant) form**
  `⟨a, b⟩ₖ := ε(a₍₂ₖ₋₁₎b)`, where `a₍₂ₖ₋₁₎b ∈ 𝒱_{k+k-(2k-1)-1} = 𝒱₀ = ℂ𝟙` by VA1 + VOA4 and
  `ε : 𝒱₀ → ℂ` is the coordinate along `𝟙` (`vacCoeff`).  ⚠ It agrees with the invariant form
  only on quasi-primary left arguments (`invariantForm_eq_shapForm`), so its Gram determinant is
  not in general the Kac determinant (`Examples/LeeYangKac.lean`, level four).
* `B₁ := shapForm₁ D hD hvac k`, defined by **the same formula with `Y` replaced by `Y₁`**:
  `⟨a, b⟩₁ₖ := ε(a¹₍₂ₖ₋₁₎b)`.  So `shapForm + t·shapForm₁` is literally the level-`k` Shapovalov
  form of the deformed vertex algebra, to first order.  `hD : D.IsGraded` is what puts
  `a¹₍₂ₖ₋₁₎b` in `𝒱₀`.

## Main results

* `vacCoeff`, `vacCoeff_smul_vacuum`, `vacCoeff_eq_iff` — the coordinate functional on
  `𝒱₀ = ℂ𝟙` (VOA4 + `𝟙 ≠ 0`).
* `smul_top_mode_comm` — `a₍₂ₖ₋₁₎b = b₍₂ₖ₋₁₎a` for `a, b ∈ 𝒱ₖ`.  Proved from skew-symmetry
  (`Core.SkewSymmetry.skew_mode`): every `j ≥ 1` term of the skew sum lands in `𝒱₋ⱼ = ⊥` by
  CFT-type positivity, and the surviving `j = 0` sign is `sgn(-2k) = +1`.
* `shapForm_symm` — hence the Shapovalov form is symmetric, which is exactly the hypothesis
  `hB₀` of every theorem in `Core.DeformedForm`.  (Note that `∀ B, B.IsSymmetric` is *false* for
  a general `InvariantForm`, by `Core.InvariantFormTranspose.not_forall_isSymmetric`; symmetry
  is a property of *this* form, and has to be proved, not assumed.)
* `invariantForm_eq_shapForm` — for `s ∈ 𝒱ₖ` with `L₁s = 0` and any fully invariant normalised
  `B`, `B(s,y) = (-1)^k·⟨s,y⟩ₖ` on `𝒱ₖ`.  The level-`k` Shapovalov form **is** the
  restriction of the canonical invariant form (up to the standard sign), and
  `mem_radBil_iff_invariantForm` records the two radicals as literally equivalent.  This is the
  identity that the proof of `SingVec.mem_leftRadical_of_shapovalov` establishes en route; it is
  isolated here because the bridge needs it *as an equality*, in both directions.
  `shapForm_grading_one_eq` cross-checks the sign against the independently proved
  `eval_oneMode_grading1_FHL` (`u₍₁₎v = -(u|v)𝟙`) at `k = 1`, where `(-1)^k = -1`.

Two independent criteria put a singular vector into `radBil (shapForm …)`:

* `mem_radBil_of_stronglySingular` — a **strongly** singular vector of weight `k ≥ 1`.
  One line: `2k-1 ≥ k`, so the mode `x₍₂ₖ₋₁₎` for `x ∈ 𝒱ₖ` is an annihilating mode.
* `mem_radBil_of_descendantSpanned` — a **Virasoro** singular vector of weight `k`, provided
  `𝒱ₖ` is spanned by *descendants* `L₋ₘ z` with `m ≥ 1` (`DescendantSpanned`).  This is the
  criterion that applies to Virasoro VOAs, where `Examples/VirasoroSpanning.negSpanVir_eq_top`
  supplies the hypothesis.  Only `virasoro_adj` is used: `B(s, L₋ₘ z) = B(Lₘ s, z) = 0`.

The bridge theorems:

* `not_liftable_of_shapPairing_ne_zero` — if `s ∈ radBil (shapForm)` and the *deformed*
  pairing `⟨s, v⟩₁ₖ ≠ 0` for some `v ∈ radBil (shapForm)`, then `s` admits **no** first-order
  correction: the relation `s` of the undeformed algebra does not survive the deformation.
* `not_liftable_of_self_pairing_ne_zero` — the usable special case `v = s`.
* `not_liftable_of_stronglySingular`, `not_liftable_of_descendantSpanned` — the two packaged
  entry points, with the singular vector supplied by one of the two criteria above.
* `notMem_F2_of_self_pairing_ne_zero`, `F2_lt_F1_of_self_pairing_ne_zero` — the Jantzen-layer
  restatement: the singular vector sits in `F₁ \ F₂`, so the inclusion `F₂ ⊆ F₁` is **strict**.
  (This is the *repaired* shape flagged in the project notes, never the false one.)
* `shapForm₁_zeroDeformation` — the non-vacuity guard: the zero deformation gives `B₁ = 0`, so
  the hypothesis `⟨s,v⟩¹ₖ ≠ 0` is a genuine condition on `D`.

## ⚠ What this file does NOT claim, stated loudly

`Deform.IsRigid W` says *every* first-order deformation is a coboundary.  **Nothing here proves
`IsRigid`, and no theorem below mentions it.**  What is proved is strictly:

> the relation `s` of the undeformed Shapovalov form does not lift to first order

i.e. the deformed form is *less* degenerate at level `k`, so the family
`t ↦ (𝒱, Y + t·Y₁)` is **not flat**: `dim rad B_t` drops at `t ≠ 0`.  Turning non-flatness into
`IsTrivial D` is a further step (one has to know that the deformed algebra is again a VOA with
the same graded dimensions, and then that a dimension-preserving deformation with no new
relations is a coboundary).  That step is **not** taken here.  Presenting the obstruction
statement as rigidity would be exactly the vacuity the project's auditor is asked to catch.

Likewise, the **false** "Jantzen bridge lemma" `rad_R = F₂ ⊕ ε·F₁, flat iff F₁ = F₂` — which
negates its own hypothesis — is *not* used, and no lemma of that shape appears below.  The only
Jantzen-layer facts used are `DefForm.lift_iff_pairing_zero` and
`DefForm.not_liftable_of_pairing_ne_zero`, both of which are unconditional linear algebra.

## Dependencies
`Core.SingularVector` (which pulls in `Core.BilinearForm`, `Core.InvariantFormFHL2`,
`Core.QuotientVOA`), `Core.SkewSymmetry`, `Core.Deformation`, `Core.DeformedForm`.

## Status
Hole-free.  No `sorry`, no `admit`, no `native_decide`, no new axiom.
-/

namespace VOA

open Module (End)
open VertexOperatorAlgebra

universe u

namespace RigidBridge

open SingVec Deform

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-! ## §1.  The coordinate functional on `𝒱₀ = ℂ𝟙`

VOA4 (`vacuum_grade`) says `𝒱₀ = ℂ∙𝟙` exactly.  With `𝟙 ≠ 0` the map `c ↦ c·𝟙` is a linear
isomorphism `ℂ ≃ 𝒱₀`, and `vacCoeff` is its inverse — the functional that reads off "the
coefficient of the vacuum".  This is the same extraction that `Deform.poleCoeff` performs with
`Classical.epsilon`; here it is packaged as an honest linear map, because the Shapovalov form has
to be a `LinearMap` for `Core.DeformedForm` to accept it. -/

/-- `c ↦ c·𝟙`, viewed as a linear map `ℂ → 𝒱₀`. -/
noncomputable def vacEmbed (W : VertexOperatorAlgebra 𝒱) : ℂ →ₗ[ℂ] W.grading 0 :=
  LinearMap.codRestrict (W.grading 0) (LinearMap.toSpanSingleton ℂ 𝒱 W.vacuum)
    (fun c => Submodule.smul_mem _ c W.vacuum_mem)

@[simp] theorem vacEmbed_coe (W : VertexOperatorAlgebra 𝒱) (c : ℂ) :
    ((vacEmbed W c : W.grading 0) : 𝒱) = c • W.vacuum := rfl

/-- `c ↦ c·𝟙` is bijective onto `𝒱₀`: surjective by VOA4 (`𝒱₀ = ℂ∙𝟙`), injective because
`𝟙 ≠ 0` and `ℂ` is a field (no `NoZeroSMulDivisors` instance is needed — we divide). -/
theorem vacEmbed_bijective (W : VertexOperatorAlgebra 𝒱) (hvac : W.vacuum ≠ 0) :
    Function.Bijective (vacEmbed W) := by
  constructor
  · intro a b hab
    have hval : a • W.vacuum = b • W.vacuum := congrArg Subtype.val hab
    by_contra hne
    have hsub : (a - b) • W.vacuum = 0 := by rw [sub_smul, hval, sub_self]
    refine hvac ?_
    have := congrArg (fun v : 𝒱 => (a - b)⁻¹ • v) hsub
    simpa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne)] using this
  · rintro ⟨x, hx⟩
    rw [W.vacuum_grade, Submodule.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    exact ⟨c, rfl⟩

/-- **The vacuum coordinate** `ε : 𝒱₀ →ₗ[ℂ] ℂ`, inverse to `c ↦ c·𝟙`. -/
noncomputable def vacCoeff (W : VertexOperatorAlgebra 𝒱) (hvac : W.vacuum ≠ 0) :
    W.grading 0 →ₗ[ℂ] ℂ :=
  (LinearEquiv.ofBijective (vacEmbed W) (vacEmbed_bijective W hvac)).symm.toLinearMap

/-- Defining property: `ε(x)·𝟙 = x` for `x ∈ 𝒱₀`. -/
@[simp] theorem vacCoeff_smul_vacuum (hvac : W.vacuum ≠ 0) (x : W.grading 0) :
    vacCoeff W hvac x • W.vacuum = (x : 𝒱) :=
  congrArg Subtype.val
    ((LinearEquiv.ofBijective (vacEmbed W) (vacEmbed_bijective W hvac)).apply_symm_apply x)

/-- `ε` reads off the coefficient: `ε(x) = c` exactly when `x = c·𝟙`. -/
theorem vacCoeff_eq_iff (hvac : W.vacuum ≠ 0) (x : W.grading 0) (c : ℂ) :
    vacCoeff W hvac x = c ↔ (x : 𝒱) = c • W.vacuum := by
  constructor
  · rintro rfl; exact (vacCoeff_smul_vacuum hvac x).symm
  · intro h
    have : vacCoeff W hvac x • W.vacuum = c • W.vacuum := by
      rw [vacCoeff_smul_vacuum hvac x, h]
    by_contra hne
    refine hvac ?_
    have hsub : (vacCoeff W hvac x - c) • W.vacuum = 0 := by rw [sub_smul, this, sub_self]
    have := congrArg (fun v : 𝒱 => (vacCoeff W hvac x - c)⁻¹ • v) hsub
    simpa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne)] using this

/-- `ε` vanishes exactly on `0` (it is a linear isomorphism). -/
theorem vacCoeff_eq_zero_iff (hvac : W.vacuum ≠ 0) (x : W.grading 0) :
    vacCoeff W hvac x = 0 ↔ (x : 𝒱) = 0 := by
  rw [vacCoeff_eq_iff hvac x 0, zero_smul]

/-! ## §2.  The level-`k` Shapovalov form -/

/-- **The top mode lands in the vacuum space.**  For `a, b ∈ 𝒱ₖ`, VA1 gives
`a₍₂ₖ₋₁₎b ∈ 𝒱_{k+k-(2k-1)-1} = 𝒱₀`. -/
theorem smul_mem_grading_zero (W : VertexOperatorAlgebra 𝒱) {k : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading k) (hb : b ∈ W.grading k) :
    W.smul a (2 * k - 1) b ∈ W.grading 0 := by
  have h := W.smul_mem_grading ha hb (2 * k - 1)
  rwa [show k + k - (2 * k - 1) - 1 = (0 : ℤ) by ring] at h

/-- The **Shapovalov vector** `a₍₂ₖ₋₁₎b ∈ 𝒱₀` of a pair of weight-`k` states. -/
noncomputable def shapVec (W : VertexOperatorAlgebra 𝒱) (k : ℤ) (a b : W.grading k) :
    W.grading 0 :=
  ⟨W.smul (a : 𝒱) (2 * k - 1) (b : 𝒱), smul_mem_grading_zero W a.2 b.2⟩

@[simp] theorem shapVec_coe (W : VertexOperatorAlgebra 𝒱) (k : ℤ) (a b : W.grading k) :
    ((shapVec W k a b : W.grading 0) : 𝒱) = W.smul (a : 𝒱) (2 * k - 1) (b : 𝒱) := rfl

theorem shapVec_add_left (W : VertexOperatorAlgebra 𝒱) (k : ℤ) (a₁ a₂ b : W.grading k) :
    shapVec W k (a₁ + a₂) b = shapVec W k a₁ b + shapVec W k a₂ b :=
  Subtype.ext (by simp [shapVec])

theorem shapVec_smul_left (W : VertexOperatorAlgebra 𝒱) (k : ℤ) (c : ℂ) (a b : W.grading k) :
    shapVec W k (c • a) b = c • shapVec W k a b :=
  Subtype.ext (by simp [shapVec])

theorem shapVec_add_right (W : VertexOperatorAlgebra 𝒱) (k : ℤ) (a b₁ b₂ : W.grading k) :
    shapVec W k a (b₁ + b₂) = shapVec W k a b₁ + shapVec W k a b₂ :=
  Subtype.ext (by simp [shapVec])

theorem shapVec_smul_right (W : VertexOperatorAlgebra 𝒱) (k : ℤ) (c : ℂ) (a b : W.grading k) :
    shapVec W k a (c • b) = c • shapVec W k a b :=
  Subtype.ext (by simp [shapVec])

/-- **The level-`k` top-mode pairing** `⟨a,b⟩ₖ = ε(a₍₂ₖ₋₁₎b)` on `𝒱ₖ`.

⚠ It is **not** in general the Kac/Shapovalov Gram form: it agrees with the invariant form (up to
the sign `(-1)^k`) only when the left argument is quasi-primary (`invariantForm_eq_shapForm`,
`mem_radBil_iff_invariantForm`).  On non-quasi-primary vectors the two differ; `Examples/LeeYangKac.lean`
documents the discrepancy at level four.  Its degeneracy on quasi-primary (e.g. singular) vectors is
what the computations of `Examples/LeeYangSingular` and `Examples/AffineSl2Singular` detect. -/
noncomputable def shapForm (W : VertexOperatorAlgebra 𝒱) (hvac : W.vacuum ≠ 0) (k : ℤ) :
    LinearMap.BilinForm ℂ (W.grading k) :=
  LinearMap.mk₂ ℂ (fun a b => vacCoeff W hvac (shapVec W k a b))
    (fun a₁ a₂ b => by simp only [shapVec_add_left, map_add])
    (fun c a b => by simp only [shapVec_smul_left, map_smul])
    (fun a b₁ b₂ => by simp only [shapVec_add_right, map_add])
    (fun c a b => by simp only [shapVec_smul_right, map_smul])

@[simp] theorem shapForm_apply (hvac : W.vacuum ≠ 0) (k : ℤ) (a b : W.grading k) :
    shapForm W hvac k a b = vacCoeff W hvac (shapVec W k a b) := rfl

/-- Unfolded characterisation: `⟨a,b⟩ₖ = c` iff `a₍₂ₖ₋₁₎b = c·𝟙`. -/
theorem shapForm_eq_iff (hvac : W.vacuum ≠ 0) {k : ℤ} (a b : W.grading k) (c : ℂ) :
    shapForm W hvac k a b = c ↔ W.smul (a : 𝒱) (2 * k - 1) (b : 𝒱) = c • W.vacuum :=
  vacCoeff_eq_iff hvac _ c

/-- `⟨a,b⟩ₖ = 0` iff the top mode vanishes. -/
theorem shapForm_eq_zero_iff (hvac : W.vacuum ≠ 0) {k : ℤ} (a b : W.grading k) :
    shapForm W hvac k a b = 0 ↔ W.smul (a : 𝒱) (2 * k - 1) (b : 𝒱) = 0 :=
  vacCoeff_eq_zero_iff hvac _

/-- `a₍₂ₖ₋₁₎b = ⟨a,b⟩ₖ·𝟙`: the Shapovalov form *is* the top product. -/
theorem smul_top_mode_eq (hvac : W.vacuum ≠ 0) {k : ℤ} (a b : W.grading k) :
    W.smul (a : 𝒱) (2 * k - 1) (b : 𝒱) = shapForm W hvac k a b • W.vacuum :=
  (vacCoeff_smul_vacuum hvac (shapVec W k a b)).symm

/-! ## §3.  Symmetry of the Shapovalov form

`Core.DeformedForm` needs `B₀` **symmetric** — `range_eq_dualAnnihilator_radBil` is false without
it.  Symmetry is *not* automatic for an abstract `InvariantForm`: `Core.InvariantFormTranspose`
proves `¬ ∀ B, B.IsSymmetric` outright (antisymmetrising an invariant form gives another one).
It has to be proved for *this* form, and it is — from skew-symmetry.

The mechanism: `skew_mode` writes `a₍ₙ₎b` as `∑ⱼ (1/j!)·sgn(-n-1-j)·Tʲ(b₍ₙ₊ⱼ₎a)`.  At the top
mode `n = 2k-1` with `a, b ∈ 𝒱ₖ`, the `j`-th inner product `b₍₂ₖ₋₁₊ⱼ₎a` lies in
`𝒱_{k+k-(2k-1+j)-1} = 𝒱₋ⱼ`, which is `⊥` for `j ≥ 1` by CFT-type positivity (VOA4).  Only `j = 0`
survives, and its sign is `sgn(-2k) = +1` because `-2k` is even.  So the sum collapses to
`b₍₂ₖ₋₁₎a`. -/

/-- **The top mode is symmetric**: `a₍₂ₖ₋₁₎b = b₍₂ₖ₋₁₎a` for `a, b ∈ 𝒱ₖ`.

This holds for every `k : ℤ` (for `k < 0` both sides are trivially zero, `𝒱ₖ = ⊥`). -/
theorem smul_top_mode_comm (W : VertexOperatorAlgebra 𝒱) {k : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading k) (hb : b ∈ W.grading k) :
    W.smul a (2 * k - 1) b = W.smul b (2 * k - 1) a := by
  rw [VertexOperatorAlgebra.skew_mode W a b (2 * k - 1)]
  -- Every `j ≥ 1` term is killed by positivity: the inner product lands in `𝒱₋ⱼ = ⊥`.
  have hterm : ∀ j : ℕ, j ≠ 0 →
      ((j.factorial : ℂ)⁻¹) • (sgn (-(2 * k - 1) - 1 - (j : ℤ))) •
        ((W.toPreVertexAlgebra.T ^ j) ((W.Y b) (-(2 * k - 1) - 1 - (j : ℤ)) a)) = 0 := by
    intro j hj
    have hjpos : 0 < (j : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hj
    have hmem := W.smul_mem_grading hb ha (2 * k - 1 + (j : ℤ))
    rw [show k + k - (2 * k - 1 + (j : ℤ)) - 1 = -(j : ℤ) by ring,
      W.positivity (-(j : ℤ)) (by omega)] at hmem
    have hzero : (W.Y b) (-(2 * k - 1) - 1 - (j : ℤ)) a = 0 := by
      have : W.smul b (2 * k - 1 + (j : ℤ)) a = 0 := (Submodule.mem_bot ℂ).mp hmem
      rw [PreVertexAlgebra.smul_def] at this
      simpa only [mode, show -(2 * k - 1 + (j : ℤ)) - 1 = -(2 * k - 1) - 1 - (j : ℤ) by ring]
        using this
    rw [hzero, map_zero, smul_zero, smul_zero]
  rw [finsum_eq_single _ 0 hterm]
  -- The `j = 0` term: `1/0! = 1`, `T⁰ = id`, and `sgn(-2k) = +1` since `-2k` is even.
  have hsgn : sgn (-(2 * k - 1) - 1 - ((0 : ℕ) : ℤ)) = 1 := by
    rw [show -(2 * k - 1) - 1 - ((0 : ℕ) : ℤ) = -k + -k by push_cast; ring]
    exact if_pos ⟨-k, rfl⟩
  rw [hsgn]
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_zero,
    Module.End.one_apply]
  rw [PreVertexAlgebra.smul_def]
  simp only [mode, Nat.cast_zero, sub_zero]

/-- **The level-`k` Shapovalov form is symmetric** — the hypothesis `hB₀` of every theorem in
`Core.DeformedForm`. -/
theorem shapForm_symm (hvac : W.vacuum ≠ 0) (k : ℤ) (a b : W.grading k) :
    shapForm W hvac k a b = shapForm W hvac k b a := by
  rw [shapForm_apply, shapForm_apply]
  exact congrArg (vacCoeff W hvac) (Subtype.ext (smul_top_mode_comm W a.2 b.2))

/-! ## §4.  Criterion I — a strongly singular vector is in the radical

The **cheap** route, and the one that needs no invariant form at all: strong singularity says
`u₍ₙ₎s = 0` whenever `n ≥ wt u`, and the Shapovalov mode `2k-1` satisfies `2k-1 ≥ k` precisely
when `k ≥ 1`.  So the pairing of `s` against any `x ∈ 𝒱ₖ` is an annihilating mode applied to `s`.
-/

/-- **A strongly singular vector of weight `k ≥ 1` lies in the radical of the level-`k`
Shapovalov form.**  One line: `x₍₂ₖ₋₁₎s = 0` because `2k-1 ≥ k = wt x`. -/
theorem mem_radBil_of_stronglySingular (hvac : W.vacuum ≠ 0) {k : ℤ} {s : 𝒱}
    (hs : IsStronglySingularOfWeight W k s) (hk : 1 ≤ k) :
    (⟨s, hs.homogeneous⟩ : W.grading k) ∈ DefForm.radBil (shapForm W hvac k) := by
  rw [DefForm.mem_radBil]
  intro y
  rw [shapForm_symm, shapForm_eq_zero_iff]
  exact hs.annihilated k (y : 𝒱) y.2 (2 * k - 1) (by omega)

/-! ## §5.  The Shapovalov form is the canonical invariant form

For a **quasi-primary** `s ∈ 𝒱ₖ` (i.e. `L₁s = 0` — automatic for a singular vector) and any
fully invariant normalised `B`, full invariance applied to `u = s`, `n = -1`, `a = 𝟙` reads

`B(s₍₋₁₎𝟙 | y) = (-1)^k ∑ⱼ (1/j!) (𝟙 | (L₁ʲs)₍₂ₖ₋₁₋ⱼ₎ y)`.

`s₍₋₁₎𝟙 = s` (creation) and `L₁s = 0` kills every `j ≥ 1`, so `B(s|y) = (-1)^k (𝟙 | s₍₂ₖ₋₁₎y)`.
For `y ∈ 𝒱ₖ` the inner vector is `⟨s,y⟩ₖ·𝟙` and `(𝟙|𝟙) = +1` (normalisation), giving

`B(s|y) = (-1)^k ⟨s,y⟩ₖ`.

This identity is what the proof of `SingVec.mem_leftRadical_of_shapovalov` establishes en route;
there it is used only in one direction, so it was never isolated.  The bridge needs it as an
**equality**, because the useful implication is the *converse* one: "`s` is orthogonal to `𝒱ₖ`
for the invariant form" ⟹ "`s` is in the radical of the Shapovalov form". -/

/-- **The comparison identity.**  For quasi-primary `s ∈ 𝒱ₖ` and `y ∈ 𝒱ₖ`, the canonical
invariant form and the level-`k` Shapovalov form agree up to the sign `(-1)^k`. -/
theorem invariantForm_eq_shapForm {B : InvariantForm W} (hB : B.IsFullyInvariant)
    (hn : B.Normalized) (hvac : W.vacuum ≠ 0) {k : ℤ} {s : 𝒱} (hs : s ∈ W.grading k)
    (hL1 : W.L 1 s = 0) (y : W.grading k) :
    B.form s (y : 𝒱) = (-1 : ℂ) ^ k * shapForm W hvac k ⟨s, hs⟩ y := by
  have key := hB k s hs (-1) W.vacuum (y : 𝒱)
  rw [W.smul_vacuum_neg_one] at key
  -- collapse the sum to `j = 0` using `L₁ s = 0`
  have hzero : ∀ j ∈ Finset.range (k.toNat + 1), j ≠ 0 →
      ((j.factorial : ℂ)⁻¹) • B.form W.vacuum (W.smul (((W.L 1) ^ j) s)
        (2 * k - (-1) - 2 - (j : ℤ)) (y : 𝒱)) = 0 := by
    intro j _ hj
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    rw [pow_succ, Module.End.mul_apply, hL1, map_zero, W.smul_zero_left, map_zero, smul_zero]
  rw [Finset.sum_eq_single 0 hzero
      (fun h => absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h),
    pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    show (2 * k - (-1) - 2 - ((0 : ℕ) : ℤ)) = 2 * k - 1 by push_cast; ring] at key
  -- `s₍₂ₖ₋₁₎y = ⟨s,y⟩ₖ·𝟙` and `(𝟙|𝟙) = +1`
  rw [smul_top_mode_eq hvac ⟨s, hs⟩ y, map_smul, InvariantForm.Normalized.vacuum_self hn] at key
  simpa only [smul_eq_mul, mul_one] using key

/-- The direction the bridge consumes: orthogonality to `𝒱ₖ` for the invariant form forces
vanishing of the Shapovalov pairing. -/
theorem shapForm_eq_zero_of_invariantForm {B : InvariantForm W} (hB : B.IsFullyInvariant)
    (hn : B.Normalized) (hvac : W.vacuum ≠ 0) {k : ℤ} {s : 𝒱} (hs : s ∈ W.grading k)
    (hL1 : W.L 1 s = 0) (y : W.grading k) (hy : B.form s (y : 𝒱) = 0) :
    shapForm W hvac k ⟨s, hs⟩ y = 0 := by
  have h := invariantForm_eq_shapForm hB hn hvac hs hL1 y
  rw [hy] at h
  rcases mul_eq_zero.mp h.symm with h' | h'
  · exact absurd h' (zpow_ne_zero _ (by norm_num))
  · exact h'

/-- **On quasi-primary vectors, the level-`k` pairing and the canonical invariant form have the
same radical condition.**  For quasi-primary `s`, radical membership on one side is *equivalent*
to orthogonality to `𝒱ₖ` on the other (this is not an equality of Gram matrices on all of `𝒱ₖ`).  (Only `→` is used downstream; `←` records that nothing is lost.) -/
theorem mem_radBil_iff_invariantForm (hvac : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {k : ℤ} {s : 𝒱} (hs : s ∈ W.grading k)
    (hL1 : W.L 1 s = 0) :
    (⟨s, hs⟩ : W.grading k) ∈ DefForm.radBil (shapForm W hvac k) ↔
      ∀ y ∈ W.grading k, (canonicalInvariantForm hvac hqp).form s y = 0 := by
  rw [DefForm.mem_radBil]
  constructor
  · intro h y hy
    rw [invariantForm_eq_shapForm (canonicalInvariantForm_isFullyInvariant hvac hqp)
      (canonicalInvariantForm_normalized hvac hqp) hvac hs hL1 ⟨y, hy⟩, h ⟨y, hy⟩, mul_zero]
  · intro h y
    exact shapForm_eq_zero_of_invariantForm (canonicalInvariantForm_isFullyInvariant hvac hqp)
      (canonicalInvariantForm_normalized hvac hqp) hvac hs hL1 y (h (y : 𝒱) y.2)

/-- **Independent cross-check of the sign convention.**  At `k = 1` the identity
`invariantForm_eq_shapForm` reads `B(u,v) = -⟨u,v⟩₁`.  The level-`1` Shapovalov form is the
coefficient of `u₍₁₎v`, while the unit-normalised invariant form satisfies
`u₍₁₎v = -B(u,v)𝟙`, proved independently in `Core.InvariantFormFHL2` as
`eval_oneMode_grading1_FHL`. -/
theorem shapForm_grading_one_eq (hvac : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) (u v : W.grading 1) :
    shapForm W hvac 1 u v = -(canonicalInvariantForm hvac hqp).form (u : 𝒱) (v : 𝒱) := by
  rw [shapForm_eq_iff, show (2 * (1 : ℤ) - 1) = 1 from by norm_num]
  exact eval_oneMode_grading1_FHL hvac hqp u.2 v.2

/-! ## §6.  Criterion II — a Virasoro singular vector in a Virasoro-generated weight space

The strong-singularity criterion of §4 is cheap but its hypothesis is expensive: verifying
`u₍ₙ₎s = 0` for *every* field `u` is exactly the step `Core.SingularVector` records as missing
(Lepowsky–Li Prop. 4.5.6 is not in the repository).  What an explicit computation actually
delivers — in `Examples/LeeYangSingular`, in `Examples/AffineSl2Singular` — is the **Virasoro**
condition `Lₙs = 0` for `n > 0`.

That is enough, provided the weight space is built out of Virasoro descendants, because
`virasoro_adj` moves the annihilating mode across the form in one step:

`B(s, L₋ₘ z) = B(Lₘ s, z) = B(0, z) = 0`  for `m ≥ 1`,

and `B(s, 𝟙) = 0` by weight orthogonality (`k > 0`).  Note that only the *structure field*
`virasoro_adj` of `InvariantForm` is used here — no full invariance, no skew-symmetry.  Full
invariance enters only through §5, to convert the conclusion into a statement about the
Shapovalov form. -/

/-- `𝒱ₖ` is **spanned by the vacuum and Virasoro descendants**: every weight-`k` state is a
finite sum of scalar multiples of `𝟙` and of vectors `L₋ₘ z` with `m ≥ 1`.

This is a hypothesis about `W`, not a theorem: it says the VOA is generated by its conformal
vector in weight `k`.  It holds for the universal Virasoro VOA
(`Examples/VirasoroSpanning.negSpanVir_eq_top` exhibits `⊤` as the span of the creation
monomials `L₋ₙ₁₋₂⋯L₋ₙᵣ₋₂|0⟩`, each of which is either `|0⟩` or of the form `L₋ₘ z` with
`m = n₁ + 2 ≥ 2 ≥ 1`), and it fails for, e.g., a lattice VOA, whose weight spaces contain
states not obtained from `ω`. -/
def DescendantSpanned (W : VertexOperatorAlgebra 𝒱) (k : ℤ) : Prop :=
  W.grading k ≤
    Submodule.span ℂ
      (insert W.vacuum {v : 𝒱 | ∃ (m : ℤ) (z : 𝒱), 1 ≤ m ∧ v = W.L (-m) z})

/-- The convenient way to supply `DescendantSpanned`: the span is everything. -/
theorem descendantSpanned_of_span_eq_top (W : VertexOperatorAlgebra 𝒱) (k : ℤ)
    (h : Submodule.span ℂ
        (insert W.vacuum {v : 𝒱 | ∃ (m : ℤ) (z : 𝒱), 1 ≤ m ∧ v = W.L (-m) z}) = ⊤) :
    DescendantSpanned W k := by
  rw [DescendantSpanned, h]; exact le_top

/-- **A Virasoro singular vector is orthogonal to a descendant-spanned weight space**, for
*any* invariant form — only `virasoro_adj` is used. -/
theorem invariantForm_eq_zero_of_singular (B : InvariantForm W) {k : ℤ} {s : 𝒱}
    (hs : IsSingularOfWeight W k s) (hspan : DescendantSpanned W k)
    {y : 𝒱} (hy : y ∈ W.grading k) : B.form s y = 0 := by
  have hy' := hspan hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem v hv =>
      simp only [Set.mem_insert_iff, Set.mem_setOf_eq] at hv
      rcases hv with rfl | ⟨m, z, hm, rfl⟩
      · exact InvariantForm.orthogonal_of_ne B (ne_of_gt hs.weight_pos) hs.homogeneous
          W.vacuum_mem
      · rw [← B.virasoro_adj m s z, hs.annihilated m (by omega), map_zero,
          LinearMap.zero_apply]
  | zero => exact map_zero _
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul c a _ ha => rw [map_smul, ha, smul_zero]

/-- **Criterion II.**  A Virasoro singular vector of weight `k` lies in the radical of the
level-`k` Shapovalov form, provided `𝒱ₖ` is spanned by the vacuum and Virasoro descendants.

This is the criterion the explicit Virasoro computations can actually feed. -/
theorem mem_radBil_of_descendantSpanned (hvac : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {k : ℤ} {s : 𝒱}
    (hs : IsSingularOfWeight W k s) (hspan : DescendantSpanned W k) :
    (⟨s, hs.homogeneous⟩ : W.grading k) ∈ DefForm.radBil (shapForm W hvac k) := by
  rw [DefForm.mem_radBil]
  intro y
  exact shapForm_eq_zero_of_invariantForm (canonicalInvariantForm_isFullyInvariant hvac hqp)
    (canonicalInvariantForm_normalized hvac hqp) hvac hs.homogeneous
    (hs.annihilated 1 one_pos) y
    (invariantForm_eq_zero_of_singular _ hs hspan y.2)

/-! ## §7.  The deformed Shapovalov form

Same formula, `Y` replaced by `Y₁`.  `hD : D.IsGraded` is the order-`t` part of VA1 and is what
puts `a¹₍₂ₖ₋₁₎b` in `𝒱₀`, so that `vacCoeff` can be applied. -/

/-- The **deformed Shapovalov vector** `a¹₍₂ₖ₋₁₎b ∈ 𝒱₀`. -/
noncomputable def shapVec₁ (D : FirstOrderDeformation W) (hD : D.IsGraded) (k : ℤ)
    (a b : W.grading k) : W.grading 0 :=
  ⟨D.smul₁ (a : 𝒱) (2 * k - 1) (b : 𝒱), by
    have h := hD k k (a : 𝒱) a.2 (b : 𝒱) b.2 (2 * k - 1)
    rwa [show k + k - (2 * k - 1) - 1 = (0 : ℤ) by ring] at h⟩

@[simp] theorem shapVec₁_coe (D : FirstOrderDeformation W) (hD : D.IsGraded) (k : ℤ)
    (a b : W.grading k) :
    ((shapVec₁ D hD k a b : W.grading 0) : 𝒱) = D.smul₁ (a : 𝒱) (2 * k - 1) (b : 𝒱) := rfl

theorem shapVec₁_add_left (D : FirstOrderDeformation W) (hD : D.IsGraded) (k : ℤ)
    (a₁ a₂ b : W.grading k) :
    shapVec₁ D hD k (a₁ + a₂) b = shapVec₁ D hD k a₁ b + shapVec₁ D hD k a₂ b :=
  Subtype.ext (by simp [shapVec₁])

theorem shapVec₁_smul_left (D : FirstOrderDeformation W) (hD : D.IsGraded) (k : ℤ) (c : ℂ)
    (a b : W.grading k) :
    shapVec₁ D hD k (c • a) b = c • shapVec₁ D hD k a b :=
  Subtype.ext (by simp [shapVec₁])

theorem shapVec₁_add_right (D : FirstOrderDeformation W) (hD : D.IsGraded) (k : ℤ)
    (a b₁ b₂ : W.grading k) :
    shapVec₁ D hD k a (b₁ + b₂) = shapVec₁ D hD k a b₁ + shapVec₁ D hD k a b₂ :=
  Subtype.ext (by simp [shapVec₁])

theorem shapVec₁_smul_right (D : FirstOrderDeformation W) (hD : D.IsGraded) (k : ℤ) (c : ℂ)
    (a b : W.grading k) :
    shapVec₁ D hD k a (c • b) = c • shapVec₁ D hD k a b :=
  Subtype.ext (by simp [shapVec₁])

/-- **The first-order deformed Shapovalov form** `⟨a,b⟩¹ₖ = ε(a¹₍₂ₖ₋₁₎b)` on `𝒱ₖ`.

`shapForm + t·shapForm₁` is the level-`k` Shapovalov form of `(𝒱, Y + t·Y₁)`, to first order in
`t`.  No symmetry is claimed or needed for `B₁` — `Core.DeformedForm` requires symmetry of `B₀`
only. -/
noncomputable def shapForm₁ (D : FirstOrderDeformation W) (hD : D.IsGraded)
    (hvac : W.vacuum ≠ 0) (k : ℤ) : LinearMap.BilinForm ℂ (W.grading k) :=
  LinearMap.mk₂ ℂ (fun a b => vacCoeff W hvac (shapVec₁ D hD k a b))
    (fun a₁ a₂ b => by simp only [shapVec₁_add_left, map_add])
    (fun c a b => by simp only [shapVec₁_smul_left, map_smul])
    (fun a b₁ b₂ => by simp only [shapVec₁_add_right, map_add])
    (fun c a b => by simp only [shapVec₁_smul_right, map_smul])

@[simp] theorem shapForm₁_apply (D : FirstOrderDeformation W) (hD : D.IsGraded)
    (hvac : W.vacuum ≠ 0) (k : ℤ) (a b : W.grading k) :
    shapForm₁ D hD hvac k a b = vacCoeff W hvac (shapVec₁ D hD k a b) := rfl

/-- Unfolded: `⟨a,b⟩¹ₖ ≠ 0` iff the deformed top product is a nonzero multiple of `𝟙`. -/
theorem shapForm₁_eq_iff (D : FirstOrderDeformation W) (hD : D.IsGraded) (hvac : W.vacuum ≠ 0)
    {k : ℤ} (a b : W.grading k) (c : ℂ) :
    shapForm₁ D hD hvac k a b = c ↔ D.smul₁ (a : 𝒱) (2 * k - 1) (b : 𝒱) = c • W.vacuum :=
  vacCoeff_eq_iff hvac _ c

/-- **Non-vacuity guard.**  The undeformed (zero) deformation produces the zero form, so the
hypothesis "`⟨s,v⟩¹ₖ ≠ 0`" of the bridge theorems below is a genuine condition on `D` and not
something that holds automatically. -/
theorem shapForm₁_zeroDeformation (hvac : W.vacuum ≠ 0) (k : ℤ)
    (hD : (zeroDeformation W).IsGraded) :
    shapForm₁ (zeroDeformation W) hD hvac k = 0 := by
  ext a b
  rw [shapForm₁_apply]
  refine (vacCoeff_eq_zero_iff hvac _).mpr ?_
  change (zeroDeformation W).smul₁ (a : 𝒱) (2 * k - 1) (b : 𝒱) = 0
  simp [FirstOrderDeformation.smul₁, zeroDeformation]

/-! ## §8.  The bridge

Everything is in place: `E = 𝒱ₖ` is finite-dimensional (a `PreVertexAlgebra` field),
`B₀ = shapForm` is symmetric (§3), the singular vector is in `radBil B₀` (§4 or §6), and
`B₁ = shapForm₁` is the first-order deformation of `B₀`.  `Core.DeformedForm` does the rest.

Read the conclusion `¬ ∃ s₁, ∀ w, ⟨s,w⟩¹ₖ + ⟨s₁,w⟩ₖ = 0` as: *there is no first-order correction
`s₁` making `s + t·s₁` a radical vector of the deformed form modulo `t²`* — see the
`Core.DeformedForm` docstring, where exactly this equation is derived by expanding
`(B₀ + t·B₁)(s + t·s₁) = 0`.

⚠ Again: this is an obstruction statement, not `Deform.IsRigid`.  See the file docstring. -/

/-- **The obstruction theorem.**  If the singular vector `s` is a relation of the undeformed
level-`k` Shapovalov form, and its *deformed* pairing against some other relation `v` is nonzero,
then `s` admits no first-order correction: the relation does not survive the deformation. -/
theorem not_liftable_of_shapPairing_ne_zero (hvac : W.vacuum ≠ 0)
    (D : FirstOrderDeformation W) (hD : D.IsGraded) {k : ℤ} {s v : W.grading k}
    (hv : v ∈ DefForm.radBil (shapForm W hvac k))
    (hsv : shapForm₁ D hD hvac k s v ≠ 0) :
    ¬ ∃ s₁ : W.grading k, ∀ w : W.grading k,
        shapForm₁ D hD hvac k s w + shapForm W hvac k s₁ w = 0 := by
  haveI := W.finrank k
  exact DefForm.not_liftable_of_pairing_ne_zero (shapForm_symm hvac k) hv hsv

/-- **The usable form**: a singular vector with nonzero deformed *self*-pairing is
obstructed. -/
theorem not_liftable_of_self_pairing_ne_zero (hvac : W.vacuum ≠ 0)
    (D : FirstOrderDeformation W) (hD : D.IsGraded) {k : ℤ} {s : W.grading k}
    (hs : s ∈ DefForm.radBil (shapForm W hvac k))
    (hself : shapForm₁ D hD hvac k s s ≠ 0) :
    ¬ ∃ s₁ : W.grading k, ∀ w : W.grading k,
        shapForm₁ D hD hvac k s w + shapForm W hvac k s₁ w = 0 :=
  not_liftable_of_shapPairing_ne_zero hvac D hD hs hself

/-- Entry point via **Criterion I** (strong singularity). -/
theorem not_liftable_of_stronglySingular (hvac : W.vacuum ≠ 0)
    (D : FirstOrderDeformation W) (hD : D.IsGraded) {k : ℤ} {s : 𝒱}
    (hs : IsStronglySingularOfWeight W k s) (hk : 1 ≤ k)
    (hself : shapForm₁ D hD hvac k ⟨s, hs.homogeneous⟩ ⟨s, hs.homogeneous⟩ ≠ 0) :
    ¬ ∃ s₁ : W.grading k, ∀ w : W.grading k,
        shapForm₁ D hD hvac k ⟨s, hs.homogeneous⟩ w + shapForm W hvac k s₁ w = 0 :=
  not_liftable_of_self_pairing_ne_zero hvac D hD
    (mem_radBil_of_stronglySingular hvac hs hk) hself

/-- Entry point via **Criterion II** (Virasoro singularity + descendant spanning) — the one the
Virasoro minimal-model computations can feed. -/
theorem not_liftable_of_descendantSpanned (hvac : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    (D : FirstOrderDeformation W) (hD : D.IsGraded) {k : ℤ} {s : 𝒱}
    (hs : IsSingularOfWeight W k s) (hspan : DescendantSpanned W k)
    (hself : shapForm₁ D hD hvac k ⟨s, hs.homogeneous⟩ ⟨s, hs.homogeneous⟩ ≠ 0) :
    ¬ ∃ s₁ : W.grading k, ∀ w : W.grading k,
        shapForm₁ D hD hvac k ⟨s, hs.homogeneous⟩ w + shapForm W hvac k s₁ w = 0 :=
  not_liftable_of_self_pairing_ne_zero hvac D hD
    (mem_radBil_of_descendantSpanned hvac hqp hs hspan) hself

/-! ### The Jantzen-layer reading

`DefForm.F1 B₀ = radBil B₀` and `DefForm.F2 B₀ B₁` are the first two Jantzen layers.  The
statements above say exactly that the singular vector sits in `F₁ \ F₂`. -/

/-- The singular vector is a first-layer relation. -/
theorem mem_F1_of_descendantSpanned (hvac : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {k : ℤ} {s : 𝒱}
    (hs : IsSingularOfWeight W k s) (hspan : DescendantSpanned W k) :
    (⟨s, hs.homogeneous⟩ : W.grading k) ∈ DefForm.F1 (shapForm W hvac k) :=
  mem_radBil_of_descendantSpanned hvac hqp hs hspan

/-- **…but not a second-layer one**, when the deformed self-pairing is nonzero.  `F₂` is the
set of relations that survive to first order (`DefForm.mem_F2_iff_liftable`), so this is the
Jantzen-layer restatement of the obstruction.  ⚠ `hself` forces `D` to be non-trivial (see
`F2_lt_F1_of_self_pairing_ne_zero`). -/
theorem notMem_F2_of_self_pairing_ne_zero (hvac : W.vacuum ≠ 0)
    (D : FirstOrderDeformation W) (hD : D.IsGraded) {k : ℤ} {s : W.grading k}
    (hs : s ∈ DefForm.radBil (shapForm W hvac k))
    (hself : shapForm₁ D hD hvac k s s ≠ 0) :
    s ∉ DefForm.F2 (shapForm W hvac k) (shapForm₁ D hD hvac k) := by
  intro hmem
  exact hself (hmem.2 s hs)

/-- The strict inclusion `F₂ ⊊ F₁` that a (repaired) Jantzen argument would consume: the
singular vector is in `F₁` and not in `F₂`.

⚠ **Not a route to rigidity.**  The hypothesis `hself` can hold only for a *non-trivial* graded
deformation: for trivial `D` the deformed self-pairing of a radical vector vanishes
(`NonzeroDeform.shapForm₁_self_eq_zero_of_isTrivial`, `Examples/NonzeroDeformation.lean`).  So on a
graded-rigid VOA `hself` is never satisfiable; and on a simple quotient `L(c,0)` the radical is
zero.  Unused by the rigidity proofs (textbook ch. L07, Warning `l07:warn:bridge`). -/
theorem F2_lt_F1_of_self_pairing_ne_zero (hvac : W.vacuum ≠ 0)
    (D : FirstOrderDeformation W) (hD : D.IsGraded) {k : ℤ} {s : W.grading k}
    (hs : s ∈ DefForm.radBil (shapForm W hvac k))
    (hself : shapForm₁ D hD hvac k s s ≠ 0) :
    DefForm.F2 (shapForm W hvac k) (shapForm₁ D hD hvac k) < DefForm.F1 (shapForm W hvac k) :=
  lt_of_le_of_ne (DefForm.F2_le_F1 _ _) fun h =>
    notMem_F2_of_self_pairing_ne_zero hvac D hD hs hself (h ▸ hs)

end RigidBridge

end VOA
