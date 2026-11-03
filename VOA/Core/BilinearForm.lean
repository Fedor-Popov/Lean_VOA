/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.VertexOperatorAlgebra

/-!
# The invariant bilinear form  (Gannon §5.1.3 end, pp. 321–322)

"Our VOAs all have a nondegenerate invariant bilinear form" — the VOA analogue of the
Killing form, which plays an important role in both CFT and Moonshine.

* **Invariance** (5.1.11a): a bilinear pairing `(·|·) : 𝒱 × 𝒱 → ℂ` is invariant iff
  `(Y(u, z) v | w) = (v | Y(e^{z L₁}(-z⁻²)^{L₀} u, z⁻¹) w)` for all `u, v, w`.
* **Uniqueness** (5.1.11b): if `𝒱` is simple and `L₁ 𝒱₁ = 0`, there is a unique
  invariant form up to scalar, and it is nondegenerate on each `𝒱ₙ`.
* **Normalisation**: the public convention is `(1 | 1) = +1`; then on `𝒱₁`,
  `u₍₁₎v = -(u | v)·1`.  Gannon's `(1 | 1) = -1` convention and its corresponding raw form
  remain available explicitly as `GannonNormalized`.
* Consequences: homogeneous spaces `𝒱ₘ ⟂ 𝒱ₙ` for `m ≠ n`; symmetry `(u|v) = (v|u)`;
  `(Lₙ u | v) = (u | L₋ₙ v)`.

For superalgebras and modules the same notion is used (cf. `Modules.Contragredient`,
which is "closely related to the definition of invariant bilinear form").

## Design decision — encoding invariance (5.1.11a)

The `structure InvariantForm` carries the **Virasoro-adjointness mode content**
`(Lₙ u | v) = (u | L₋ₙ v)` for all `n` — which Gannon lists explicitly as the consequence of
(5.1.11a) (take `u = ω` and extract modes), and which the elementary structure theory
(`orthogonal_of_ne`, the `𝒱₁` symmetry) consumes.  The **full** generating-function invariance
`(Y(u,z)a|b) = (a|Y(e^{zL₁}(-z⁻²)^{L₀}u, z⁻¹)b)`, needed for uniqueness, is added as the predicate
`InvariantForm.IsFullyInvariant` (★) — its explicit mode content, with `(-z⁻²)^{L₀}` giving the
sign `(-1)^{wt}`/index shift and the locally-nilpotent exponential `e^{zL₁}`
(`Core.Automorphism.expEquiv`; `L₁` is locally nilpotent on the bounded-below grading,
`L_one_pow_eq_zero`) giving the finite `L₁ʲ/j!` sum.  It refines `virasoro_adj` (its `u = ω`
slice, since `L₁ω = 0`).  See `README.md`.

## What is proved here (`sorry`-free / axiom-free)

* `structure InvariantForm W` — a `ℂ`-bilinear form with the Virasoro-adjointness
  `virasoro_adj` (the mode content of 5.1.11a), with `L0_adj` recording its `n = 0` case.
* `orthogonal_of_ne` — `𝒱ₘ ⟂ 𝒱ₙ` for `m ≠ n` (from `L0_adj` + `L_zero_grading`:
  `m(u|v) = (L₀u|v) = (u|L₀v) = n(u|v)`, so `(m-n)(u|v) = 0`).

* `IsSimple` / `IsIdeal` — the VOA simplicity predicate (the only ideals are `⊥`, `⊤`),
  needed to state the uniqueness 5.1.11b.

## The 𝒱₁ symmetry (proved, in `Core.InvariantFormSymmetry`) and the open targets

* **`𝒱₁` symmetry.** The `(1)`-pairing symmetry `u₍₁₎v = v₍₁₎u` on `𝒱₁` and the partial form
  symmetry `InvariantForm.isSymmetric_grading1_of_eval` are proved `sorry`/axiom-free in
  `Core.InvariantFormSymmetry`, from skew-symmetry (`skew_mode`).
* **Conditional on `IsFullyInvariant`.** The **uniqueness** `invariantForm_unique` (5.1.11b),
  nondegeneracy, and the
  **full** `𝒱₁`-evaluation `(u|v) = u₍₁₎v` (5.1.12b) are proved (parametric in `IsFullyInvariant`)
  via the full
  generating-function invariance `(Y(u,z)a|b) = (a|Y(e^{zL₁}(-z⁻²)^{L₀}u, z⁻¹)b)`, encoded by its
  explicit mode content `IsFullyInvariant` (★).  From (★) the radical `ker(·|·)` is a VOA ideal
  (`radical_isIdeal`); a normalised difference has `𝟙` in its radical, so the radical is `⊤` and
  the form is determined — uniqueness; simplicity then gives nondegeneracy.  `L₁` is locally
  nilpotent on the bounded-below grading (`L_one_pow_eq_zero`, the engine behind
  `Core.Automorphism.expEquiv`), truncating (★)'s sum to a finite range.

## Dependencies
* `VOA.Core.VertexOperatorAlgebra`.  The `𝒱₁` symmetry consequences live in
  `Core.InvariantFormSymmetry` (which imports this file + the skew gate).

## Status
The infrastructure is `sorry`-free / axiom-free:
`InvariantForm`, `orthogonal_of_ne`, the public `Normalized` convention `(𝟙|𝟙) = 1`, and
`IsSimple`/`IsIdeal` are proved/defined; the `𝒱₁` symmetry is in `Core.InvariantFormSymmetry`.
The main targets `invariantForm_unique` (5.1.11b), nondegeneracy
`invariantForm_nondegenerate`, and the **full** `𝒱₁`-evaluation `eval_oneMode_grading1`
`(u|v) = u₍₁₎v` (5.1.12b) are proved here **parametric in** the full-invariance hypothesis
`IsFullyInvariant` (★) — and that hypothesis is **proved** (the FHL theorem, Li, JPAA 96 (1994)
279-297): the constructed `canonicalInvariantForm` satisfies `IsFullyInvariant` unconditionally
(under `𝟙 ≠ 0` and `L₁𝒱₁ = 0`), so the main 5.1.11b/5.1.12b results hold under those two
hypotheses alone, as
the `…_FHL` corollaries in `Core.InvariantFormFHL2`.  The FHL chain (downstream, so this upstream
file stays import-light): `QPMatch` (`Core.InvariantFormQPMatch`) → general-weight
`canBilin_qp_qp_adj` (`Core.InvariantFormQPMatchGen`) → sl₂ decomposition `qpDecomp`
(`Core.QuasiPrimaryDecomp`) → `canDiagonal_unconditional` → `canonicalInvariantForm`
(`Core.InvariantFormFHL2`).  All `#print axioms = [propext, Classical.choice, Quot.sound]`
(no `sorry`, no project axiom).

## References
* Gannon §5.1.3, eqs. (5.1.11)–(5.1.12); Frenkel–Huang–Lepowsky [199]; Li [380].
-/

namespace VOA

open Module (End)
open scoped BigOperators

universe u

-- Placed under `VertexOperatorAlgebra` so the full name is
-- `VOA.VertexOperatorAlgebra.InvariantForm`, distinct from the Lie-algebra
-- `VOA.InvariantForm` of `Foundations.AffineLie`.
namespace VertexOperatorAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## `L₁` lowers the conformal grading (local nilpotency)

`L₁ = ω₍₂₎` lowers conformal weight by one (`L_one_lower`), so on the bounded-below grading
(VOA4) it is **locally nilpotent**: `L₁ʲu = 0` once `j` exceeds the weight of `u`
(`L_one_pow_eq_zero`).  This is exactly what makes the exponential `e^{zL₁}` — the
locally-nilpotent exponential of `Core.Automorphism` (`expEquiv`/`expFun_smul`) — well defined,
and it is what truncates the full-invariance sum below to a finite range. -/

/-- `L₁` lowers the conformal grading by one: `L₁ 𝒱ₖ ⊆ 𝒱_{k-1}` (since `L₁ = ω₍₂₎` and
`ω ∈ 𝒱₂`, VA1 gives `ω₍₂₎ 𝒱ₖ ⊆ 𝒱_{2+k-2-1}`). -/
theorem L_one_lower (W : VertexOperatorAlgebra 𝒱) {k : ℤ} {x : 𝒱} (hx : x ∈ W.grading k) :
    W.L 1 x ∈ W.grading (k - 1) := by
  have heq : W.L 1 x = W.smul W.conformalVector 2 x := by
    rw [L_def, PreVertexAlgebra.smul_def, show (1 : ℤ) + 1 = 2 by norm_num]
  rw [heq]
  have h := W.smul_mem_grading W.conformal_mem hx 2
  rwa [show (2 + k - 2 - 1 : ℤ) = k - 1 by ring] at h

/-- The iterate `L₁ʲ` lowers the grading by `j`: `L₁ʲ 𝒱ₖ ⊆ 𝒱_{k-j}`. -/
theorem L_one_pow_mem (W : VertexOperatorAlgebra 𝒱) {k : ℤ} {x : 𝒱} (hx : x ∈ W.grading k)
    (j : ℕ) : ((W.L 1) ^ j) x ∈ W.grading (k - j) := by
  induction j with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := L_one_lower W ih
    rwa [show (k - (n : ℤ)) - 1 = k - ((n : ℤ) + 1) by ring, ← Nat.cast_one, ← Nat.cast_add] at h

/-- **Local nilpotency of `L₁`** (the engine behind `e^{zL₁}`): for `x ∈ 𝒱ₖ`, `L₁ʲx = 0` once
`k - j < 0`, i.e. `j > k` (VOA4 positivity: `𝒱_{<0} = 0`). -/
theorem L_one_pow_eq_zero (W : VertexOperatorAlgebra 𝒱) {k : ℤ} {x : 𝒱} (hx : x ∈ W.grading k)
    {j : ℕ} (hj : k - j < 0) : ((W.L 1) ^ j) x = 0 := by
  have hmem := L_one_pow_mem W hx j
  rw [W.positivity (k - j) hj] at hmem
  exact (Submodule.mem_bot ℂ).mp hmem

/-! ## The invariant bilinear form (Gannon 5.1.11a) -/

/-- An **invariant bilinear form** on a VOA (Gannon 5.1.11a).  Encoded by its
Virasoro-adjointness mode content `(Lₙ u | v) = (u | L₋ₙ v)` — the consequence of the
generating-function invariance that the elementary structure theory uses (see the file
docstring on the encoding decision and the deferred full form). -/
structure InvariantForm (W : VertexOperatorAlgebra 𝒱) where
  /-- The underlying `ℂ`-bilinear form `(·|·) : 𝒱 × 𝒱 → ℂ`. -/
  form : LinearMap.BilinForm ℂ 𝒱
  /-- **Invariance (Virasoro-adjointness).** `(Lₙ u | v) = (u | L₋ₙ v)` for every `n`
  (Gannon 5.1.11a, mode content): each `Lₙ` is adjoint to `L₋ₙ`. -/
  virasoro_adj : ∀ (n : ℤ) (a b : 𝒱), form (W.L n a) b = form a (W.L (-n) b)

namespace InvariantForm

variable {W : VertexOperatorAlgebra 𝒱}

/-- The `L₀`-adjointness `(L₀ u | v) = (u | L₀ v)`, the `n = 0` case of invariance. -/
theorem L0_adj (B : InvariantForm W) (a b : 𝒱) : B.form (W.L 0 a) b = B.form a (W.L 0 b) := by
  have h := B.virasoro_adj 0 a b
  rwa [neg_zero] at h

/-- **Orthogonality of distinct homogeneous spaces** (Gannon §5.1.3): `𝒱ₘ ⟂ 𝒱ₙ` for
`m ≠ n`.  Proof: with `a ∈ 𝒱ₘ`, `b ∈ 𝒱ₙ`, `L₀`-adjointness and the `L₀`-grading give
`m·(a|b) = (L₀a|b) = (a|L₀b) = n·(a|b)`, so `(m-n)·(a|b) = 0`; `m ≠ n` forces `(a|b) = 0`. -/
theorem orthogonal_of_ne (B : InvariantForm W) {m n : ℤ} (hmn : m ≠ n) {a b : 𝒱}
    (ha : a ∈ W.grading m) (hb : b ∈ W.grading n) : B.form a b = 0 := by
  have hL := B.L0_adj a b
  rw [W.L_zero_grading a ha, W.L_zero_grading b hb] at hL
  simp only [map_smul, LinearMap.smul_apply] at hL
  -- hL : (m : ℂ) • B.form a b = (n : ℂ) • B.form a b
  have hz : ((m : ℂ) - n) • B.form a b = 0 := by rw [sub_smul, hL, sub_self]
  have hmn' : ((m : ℂ) - n) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hmn)
  rcases smul_eq_zero.mp hz with h | h
  · exact absurd h hmn'
  · exact h

/-! ## Symmetry and uniqueness/normalisation (statements; proofs downstream) -/

/-- `B` is **symmetric**: `(u|v) = (v|u)` (Gannon §5.1.3).  For a VOA-invariant form this is
*not* elementary — it follows from skew-symmetry `Core.Identities.skew` (5.1.8) via
invariance.  Recorded as a predicate; the theorem `∀ B, IsSymmetric B` depends on `skew` and full
invariance (see the file docstring), and is **not** stubbed. -/
def IsSymmetric (B : InvariantForm W) : Prop := ∀ a b : 𝒱, B.form a b = B.form b a

/-- `B` has prescribed vacuum norm `κ`.  Keeping the value as a parameter separates all
scale-invariant structure theory from the two sign conventions used in the literature. -/
def NormalizedAt (B : InvariantForm W) (κ : ℂ) : Prop :=
  B.form W.vacuum W.vacuum = κ

/-- The public unit normalisation `(𝟙|𝟙) = 1`.  With the present FHL adjoint convention this gives
`u₍₁₎v = -(u|v)·𝟙` on `𝒱₁`. -/
def Normalized (B : InvariantForm W) : Prop := B.NormalizedAt 1

/-- Gannon's sign convention `(𝟙|𝟙) = -1` (5.1.12a).  The raw Li/FHL construction in
`Core.InvariantFormCanonical` naturally has this normalisation; the public canonical form is its
negative. -/
def GannonNormalized (B : InvariantForm W) : Prop := B.NormalizedAt (-1)

/-- Unfold a prescribed vacuum norm. -/
theorem NormalizedAt.vacuum_self {B : InvariantForm W} {κ : ℂ} (h : B.NormalizedAt κ) :
    B.form W.vacuum W.vacuum = κ := h

/-- The public normalisation value `(𝟙|𝟙) = 1`. -/
theorem Normalized.vacuum_self {B : InvariantForm W} (h : B.Normalized) :
    B.form W.vacuum W.vacuum = 1 := h

/-- The Gannon normalisation value `(𝟙|𝟙) = -1`. -/
theorem GannonNormalized.vacuum_self {B : InvariantForm W} (h : B.GannonNormalized) :
    B.form W.vacuum W.vacuum = -1 := h

end InvariantForm

/-! ## Simplicity (Gannon §5.1.3 / Def 5.3.2) -/

/-- An **ideal** of a VOA: a subspace closed under every mode `u₍ₙ₎` (`Y(u,z) I ⊆ I((z))`),
i.e. a `𝒱`-submodule for the field action (Gannon §5.1.3). -/
def IsIdeal (W : VertexOperatorAlgebra 𝒱) (I : Submodule ℂ 𝒱) : Prop :=
  ∀ (u v : 𝒱) (n : ℤ), v ∈ I → W.smul u n v ∈ I

/-- A VOA is **simple** if it is nonzero and its only ideals are `⊥` and `⊤`
(Gannon §5.1.3, Def 5.3.2).  Simplicity (with `L₁𝒱₁ = 0`) is what makes the invariant form
unique up to scalar and nondegenerate (5.1.11b). -/
def IsSimple (W : VertexOperatorAlgebra 𝒱) : Prop :=
  (⊤ : Submodule ℂ 𝒱) ≠ ⊥ ∧ ∀ I : Submodule ℂ 𝒱, W.IsIdeal I → I = ⊥ ∨ I = ⊤

/-! ## Full invariance, uniqueness and `𝒱₁`-evaluation (5.1.11b–5.1.12b)

The `𝒱₁` symmetry of the `(1)`-pairing (`u₍₁₎v = v₍₁₎u`) and the partial form symmetry on `𝒱₁`
are proved `sorry`/axiom-free in `Core.InvariantFormSymmetry` (`oneMode_symm_grading1`,
`InvariantForm.isSymmetric_grading1_of_eval`), from skew-symmetry.

We also prove the **uniqueness** `invariantForm_unique` (5.1.11b) and the **full**
`𝒱₁`-evaluation `u₍₁₎v = -(u|v)·𝟙` for the public unit normalisation.  The ingredient is the
**full** generating-function
invariance `(Y(u,z)a|b) = (a|Y(e^{zL₁}(−z⁻²)^{L₀}u, z⁻¹)b)`, encoded by its explicit **mode
content** `IsFullyInvariant` (★): matching `z`-coefficients, for `u` of weight `wt`,
`(u₍ₙ₎a|b) = (−1)^{wt} ∑_{j≤wt} (1/j!) ((L₁ʲu)₍₂wt−n−2−j₎a|b)` — `(−z⁻²)^{L₀}` supplies the sign
`(−1)^{wt}` and the `2wt` index shift, and `e^{zL₁}` (locally nilpotent on the bounded-below
grading, `L_one_pow_eq_zero`, cf. `Core.Automorphism.expEquiv`) supplies the `L₁ʲ/j!` sum, finite
because `L₁ʲu = 0` for `j > wt`.  This is consistent with the Virasoro-adjointness field
`virasoro_adj`, which is exactly the `u = ω` slice (`L₁ω = 0`).

From `IsFullyInvariant`, the radical `ker(·|·)` is a VOA ideal (`radical_isIdeal`); a normalised
difference puts `𝟙` in the radical, so the radical is everything and the form is determined —
giving uniqueness.  Simplicity then forces nondegeneracy (`invariantForm_nondegenerate`). -/

namespace InvariantForm

variable {W : VertexOperatorAlgebra 𝒱}

/-- Scalar multiplication of an invariant form. -/
def scale (c : ℂ) (B : InvariantForm W) : InvariantForm W where
  form := c • B.form
  virasoro_adj := by
    intro n a b
    simp only [LinearMap.smul_apply]
    rw [B.virasoro_adj]

@[simp] theorem scale_form_apply (c : ℂ) (B : InvariantForm W) (a b : 𝒱) :
    (scale c B).form a b = c • B.form a b := rfl

/-- Negation of an invariant form. -/
def neg (B : InvariantForm W) : InvariantForm W := scale (-1) B

@[simp] theorem neg_form_apply (B : InvariantForm W) (a b : 𝒱) :
    (neg B).form a b = -B.form a b := by
  rw [neg, scale_form_apply]
  simp

/-- Scaling transports the prescribed vacuum norm. -/
theorem NormalizedAt.scale {B : InvariantForm W} {κ : ℂ} (h : B.NormalizedAt κ) (c : ℂ) :
    (scale c B).NormalizedAt (c * κ) := by
  rw [NormalizedAt, scale_form_apply, h, smul_eq_mul]

/-- Negating a Gannon-normalised form gives the public unit normalisation. -/
theorem GannonNormalized.neg {B : InvariantForm W} (h : B.GannonNormalized) :
    (neg B).Normalized := by
  rw [Normalized, NormalizedAt, neg_form_apply, h]
  norm_num

/-- Negating a publicly normalised form gives Gannon's normalisation. -/
theorem Normalized.neg {B : InvariantForm W} (h : B.Normalized) :
    (neg B).GannonNormalized := by
  rw [GannonNormalized, NormalizedAt, neg_form_apply, h]

/-- The difference `B₁ - B₂` of two invariant forms is again invariant. -/
def sub (B₁ B₂ : InvariantForm W) : InvariantForm W where
  form := B₁.form - B₂.form
  virasoro_adj := by
    intro n a b
    simp only [LinearMap.sub_apply]
    rw [B₁.virasoro_adj, B₂.virasoro_adj]

/-- **Full invariance** (Gannon 5.1.11a), in explicit mode form — the modal content of
`(Y(u,z)a|b) = (a|Y(e^{zL₁}(−z⁻²)^{L₀}u, z⁻¹)b)`.  For `u` homogeneous of weight `wt`,
`(u₍ₙ₎a|b) = (−1)^{wt} ∑_{j≤wt} (1/j!) ((L₁ʲu)₍₂wt−n−2−j₎a|b)`, with `a` kept in the first slot.
The finite range `j ≤ wt` captures every nonzero term, since `L₁ʲu = 0` for `j > wt`
(`L_one_pow_eq_zero`).  This refines `virasoro_adj` (its `u = ω` slice). -/
abbrev IsFullyInvariant (B : InvariantForm W) : Prop :=
  ∀ (wt : ℤ) (u : 𝒱), u ∈ W.grading wt → ∀ (n : ℤ) (a b : 𝒱),
    B.form (W.smul u n a) b
      = (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) •
          B.form a (W.smul (((W.L 1) ^ j) u) (2 * wt - n - 2 - (j : ℤ)) b)

/-- Full invariance is preserved by differences. -/
theorem IsFullyInvariant.sub {B₁ B₂ : InvariantForm W}
    (h₁ : B₁.IsFullyInvariant) (h₂ : B₂.IsFullyInvariant) :
    (InvariantForm.sub B₁ B₂).IsFullyInvariant := by
  intro wt u hu n a b
  show (B₁.form - B₂.form) (W.smul u n a) b
      = (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) •
          (B₁.form - B₂.form) a (W.smul (((W.L 1) ^ j) u) (2 * wt - n - 2 - (j : ℤ)) b)
  rw [LinearMap.sub_apply, LinearMap.sub_apply, h₁ wt u hu n a b, h₂ wt u hu n a b, ← smul_sub,
    ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [LinearMap.sub_apply, LinearMap.sub_apply, smul_sub]

/-- Full invariance is preserved by scalar multiplication. -/
theorem IsFullyInvariant.scale {B : InvariantForm W} (hB : B.IsFullyInvariant) (c : ℂ) :
    (InvariantForm.scale c B).IsFullyInvariant := by
  intro wt u hu n a b
  simp only [scale_form_apply, smul_eq_mul]
  rw [hB wt u hu n a b]
  simp only [smul_eq_mul]
  have hsum :
      (∑ j ∈ Finset.range (wt.toNat + 1),
          ((j.factorial : ℂ)⁻¹) *
            (c * B.form a (W.smul (((W.L 1) ^ j) u)
              (2 * wt - n - 2 - (j : ℤ)) b)))
        = c * ∑ j ∈ Finset.range (wt.toNat + 1),
            ((j.factorial : ℂ)⁻¹) *
              B.form a (W.smul (((W.L 1) ^ j) u)
                (2 * wt - n - 2 - (j : ℤ)) b) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [hsum]
  ring

/-- Full invariance is preserved by negation. -/
theorem IsFullyInvariant.neg {B : InvariantForm W} (hB : B.IsFullyInvariant) :
    (InvariantForm.neg B).IsFullyInvariant := hB.scale (-1)

/-- The **left radical** of an invariant form: `ker (·|·) = {a | ∀ b, (a|b) = 0}`. -/
def leftRadical (B : InvariantForm W) : Submodule ℂ 𝒱 := LinearMap.ker B.form

theorem mem_leftRadical {B : InvariantForm W} {a : 𝒱} :
    a ∈ leftRadical B ↔ B.form a = 0 := LinearMap.mem_ker

/-- **The radical of a fully-invariant form is an ideal.**  For `v` in the radical and any
`u, n`, full invariance writes `(u₍ₙ₎v|b)` as `(−1)^{wt}∑ⱼ(1/j!)(v|…)`, all of whose terms
vanish because `v` is in the (left) radical.  Decomposing `u` into homogeneous pieces
(`Submodule.iSup_induction`) extends from homogeneous `u`. -/
theorem radical_isIdeal {B : InvariantForm W} (hB : B.IsFullyInvariant) :
    W.IsIdeal (leftRadical B) := by
  intro u v n hv
  rw [mem_leftRadical] at hv
  rw [leftRadical, LinearMap.mem_ker]
  refine LinearMap.ext fun b => ?_
  simp only [LinearMap.zero_apply]
  have hutop : u ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading (motive := fun u =>
    ∀ (n : ℤ) (b : 𝒱), B.form (W.smul u n v) b = 0) hutop ?_ ?_ ?_ n b
  · intro i x hx n b
    rw [hB i x hx n v b]
    have hz : ∀ j ∈ Finset.range (i.toNat + 1),
        ((j.factorial : ℂ)⁻¹) • B.form v (W.smul (((W.L 1) ^ j) x) (2 * i - n - 2 - (j : ℤ)) b)
          = 0 := by
      intro j _
      rw [hv, LinearMap.zero_apply, smul_zero]
    rw [Finset.sum_eq_zero hz, smul_zero]
  · intro n b
    rw [W.smul_zero_left, map_zero, LinearMap.zero_apply]
  · intro x y hx hy n b
    rw [W.smul_add_left, map_add, LinearMap.add_apply, hx n b, hy n b, add_zero]

/-- If `(𝟙|𝟙) = 0` then `𝟙` is in the left radical: `(𝟙|b) = 0` for every `b`, since `𝟙 ⟂ 𝒱ₙ`
for `n ≠ 0` (`orthogonal_of_ne`) and `𝒱₀ = ℂ𝟙`. -/
theorem vacuum_mem_leftRadical {B : InvariantForm W} (h0 : B.form W.vacuum W.vacuum = 0) :
    W.vacuum ∈ leftRadical B := by
  rw [leftRadical, LinearMap.mem_ker]
  refine LinearMap.ext fun b => ?_
  simp only [LinearMap.zero_apply]
  have hbtop : b ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading (motive := fun b => B.form W.vacuum b = 0)
    hbtop ?_ ?_ ?_
  · intro i x hx
    by_cases hi : i = 0
    · subst hi
      rw [W.vacuum_grade, Submodule.mem_span_singleton] at hx
      obtain ⟨c, rfl⟩ := hx
      rw [map_smul, h0, smul_zero]
    · exact orthogonal_of_ne B (Ne.symm hi) W.vacuum_mem hx
  · exact map_zero (B.form W.vacuum)
  · intro x y hx hy; rw [map_add, hx, hy, add_zero]

/-- An ideal containing `𝟙` is all of `𝒱` (every `w = w₍₋₁₎𝟙` lies in it). -/
theorem ideal_eq_top_of_vacuum_mem {I : Submodule ℂ 𝒱} (hI : W.IsIdeal I)
    (h1 : W.vacuum ∈ I) : I = ⊤ := by
  rw [eq_top_iff]
  intro w _
  have h := hI w W.vacuum (-1) h1
  rwa [W.smul_vacuum_neg_one] at h

/-- **Uniqueness of the normalised invariant form** (Gannon 5.1.11b).  Two fully-invariant
forms with the same public normalisation `(𝟙|𝟙) = 1` coincide: their difference `D` is fully invariant
with `(𝟙|𝟙)_D = 0`, so `𝟙 ∈ rad D`; `rad D` is an ideal containing `𝟙` (`radical_isIdeal` +
`ideal_eq_top_of_vacuum_mem`), hence all of `𝒱`, so `D = 0`. -/
theorem invariantForm_unique {B₁ B₂ : InvariantForm W}
    (h₁ : B₁.IsFullyInvariant) (h₂ : B₂.IsFullyInvariant)
    (hn₁ : B₁.Normalized) (hn₂ : B₂.Normalized) : B₁.form = B₂.form := by
  have hD0 : (sub B₁ B₂).form W.vacuum W.vacuum = 0 := by
    show (B₁.form - B₂.form) W.vacuum W.vacuum = 0
    rw [LinearMap.sub_apply, LinearMap.sub_apply, Normalized.vacuum_self hn₁,
      Normalized.vacuum_self hn₂, sub_self]
  have hmem : W.vacuum ∈ leftRadical (sub B₁ B₂) := vacuum_mem_leftRadical hD0
  have htop : leftRadical (sub B₁ B₂) = ⊤ :=
    ideal_eq_top_of_vacuum_mem (radical_isIdeal (IsFullyInvariant.sub h₁ h₂)) hmem
  have hDzero : (sub B₁ B₂).form = 0 := by
    refine LinearMap.ext fun a => ?_
    have ha : a ∈ leftRadical (sub B₁ B₂) := htop ▸ Submodule.mem_top
    rw [mem_leftRadical] at ha
    rw [ha]; rfl
  exact sub_eq_zero.mp hDzero

/-- **Nondegeneracy** (Gannon 5.1.11b): on a simple VOA a normalised fully-invariant form is
nondegenerate — its radical is `⊥`.  (The radical is an ideal; it is not `⊤` since
`(𝟙|𝟙) = 1 ≠ 0`, so simplicity forces `⊥`.) -/
theorem invariantForm_nondegenerate {B : InvariantForm W} (hsimple : W.IsSimple)
    (hB : B.IsFullyInvariant) (hn : B.Normalized) : leftRadical B = ⊥ := by
  rcases hsimple.2 (leftRadical B) (radical_isIdeal hB) with h | h
  · exact h
  · exfalso
    have hmem : W.vacuum ∈ leftRadical B := h ▸ Submodule.mem_top
    rw [mem_leftRadical] at hmem
    have hzero := DFunLike.congr_fun hmem W.vacuum
    rw [LinearMap.zero_apply, Normalized.vacuum_self hn] at hzero
    exact absurd hzero (by norm_num)

/-- **Evaluation on `𝒱₁`**: for `u, v ∈ 𝒱₁` and a publicly normalised fully-invariant
form, `u₍₁₎v = -(u|v)·𝟙` (note `u₍₁₎v ∈ 𝒱₀ = ℂ𝟙`).  Via full invariance applied to
`u = u₍₋₁₎𝟙`: only the `j = 0` term `−(𝟙|u₍₁₎v) = (u|v)` survives (the `j = 1` term has
`L₁u ∈ 𝒱₀` and `𝟙₍₀₎v = 0`; `j ≥ 2` vanish since `L₁ʲu = 0`). -/
theorem eval_oneMode_grading1 {B : InvariantForm W} (hB : B.IsFullyInvariant)
    (hn : B.Normalized) {u v : 𝒱} (hu : u ∈ W.grading 1) (hv : v ∈ W.grading 1) :
    W.smul u 1 v = -B.form u v • W.vacuum := by
  have hmem : W.smul u 1 v ∈ W.grading 0 := by
    have h := W.smul_mem_grading hu hv 1
    rwa [show (1 + 1 - 1 - 1 : ℤ) = 0 by ring] at h
  rw [W.vacuum_grade, Submodule.mem_span_singleton] at hmem
  obtain ⟨μ, hμ⟩ := hmem
  -- hμ : μ • W.vacuum = W.smul u 1 v
  have hu1 : u = W.smul u (-1) W.vacuum := (W.smul_vacuum_neg_one u).symm
  have key := hB 1 u hu (-1) W.vacuum v
  rw [← hu1, show (1 : ℤ).toNat + 1 = 2 by norm_num, Finset.sum_range_succ,
    Finset.sum_range_one] at key
  have hj0 : ((Nat.factorial 0 : ℂ)⁻¹) •
      B.form W.vacuum (W.smul (((W.L 1) ^ 0) u) (2 * 1 - (-1) - 2 - ((0 : ℕ) : ℤ)) v) = μ := by
    rw [pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
      show (2 * 1 - (-1) - 2 - ((0 : ℕ) : ℤ) : ℤ) = 1 by norm_num, ← hμ, map_smul,
      Normalized.vacuum_self hn]
    ring
  have hj1 : ((Nat.factorial 1 : ℂ)⁻¹) •
      B.form W.vacuum (W.smul (((W.L 1) ^ 1) u) (2 * 1 - (-1) - 2 - ((1 : ℕ) : ℤ)) v) = 0 := by
    have hL1mem : ((W.L 1) ^ 1) u ∈ W.grading 0 := by
      have h := L_one_pow_mem W hu 1
      rwa [show (1 - ((1 : ℕ) : ℤ) : ℤ) = 0 by norm_num] at h
    rw [W.vacuum_grade, Submodule.mem_span_singleton] at hL1mem
    obtain ⟨ν, hν⟩ := hL1mem
    rw [← hν, W.smul_smul_left, show (2 * 1 - (-1) - 2 - ((1 : ℕ) : ℤ) : ℤ) = 0 by norm_num,
      W.smul_vacuum_left, if_neg (by norm_num), smul_zero, map_zero, smul_zero]
  rw [hj0, hj1, add_zero] at key
  have hval : B.form u v = -μ := by rw [key, zpow_one, smul_eq_mul]; ring
  rw [← hμ, hval, neg_neg]

end InvariantForm

end VertexOperatorAlgebra

end VOA
