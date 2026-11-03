/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.Reconstruction
import VOA.Core.SkewSymmetry

/-!
# Zero-modes and the Lie algebra `𝒱₁`  (Gannon §5.2.1, pp. 324–325)

The first homogeneous piece `𝒱₁` of a VOA carries a Lie algebra structure; this is
"how Lie algebras arise in VOAs" and the entry point for the affine examples.

* **Zero-mode** `o(u) := u₍ₙ₋₁₎` for `u ∈ 𝒱ₙ` (Gannon §5.2.1). By VA1, `o(u)` preserves
  each grade `𝒱ₘ`. The grade `𝒱ₙ` thus carries the algebra `u × v := o(u) v = u₍₀₎ v`.
* **`𝒱₁` is a Lie algebra.** For `u, v ∈ 𝒱₁`, set `[u, v] := u₍₀₎ v`. Then `[·,·]` is
  antisymmetric (mod `L₋₁𝒱`, but `L₋₁𝒱₀ = 0` so genuinely on `𝒱₁`) and satisfies
  Jacobi, from the commutator formula (5.1.7c) at `ℓ=m=n=0`.
* The form `(u | v) := u₍₁₎ v ∈ 𝒱₀ = ℂ1` is symmetric and invariant on `𝒱₁`
  (eq. 5.2.2), matching the bilinear form of `Core.BilinearForm`. Hence `𝒱₁` is
  **self-dual**, and reductive when `𝒱` is "weakly rational".

## What is proved here (`sorry`-free / axiom-free)

* `zeroMode` — the weight-graded zero-mode operator `o_k(u) = u₍ₖ₋₁₎ = mode (Y u) (k-1)`
  (Gannon §5.2.1), with `zeroMode_apply` and the **grade-preservation** lemma
  `zeroMode_mem_grading` (`o_k(u) : 𝒱ₗ → 𝒱ₗ` for `u ∈ 𝒱ₖ`, directly from VA1).
* `zeroMode_isDerivation` (Gannon 5.2.4 / 5.1.7c at `a=0`): `[u₍₀₎, v₍ₙ₎] = (u₍₀₎v)₍ₙ₎`,
  i.e. `u₍₀₎(v₍ₙ₎w) − v₍ₙ₎(u₍₀₎w) = (u₍₀₎v)₍ₙ₎w` for all `u v w n`. Proved cleanly from the
  field `n`-th-product theorem `nth_product` (read off the `z^{-n-1}`-coefficient of
  `Y(u₍₀₎v,z) = Res_{z₁}[Y(u,z₁),Y(v,z)]`); no use of the existential-`N` commutator form.
* `bracketV1` — the bracket `[u,v] = u₍₀₎v` on `𝒱₁` (VA1: `1+1−0−1 = 1`), and its
  **Jacobi/Leibniz identity** `bracketV1_jacobi` (the `n=0` case of `zeroMode_isDerivation`).

## Antisymmetry, from skew-symmetry

The Lie-algebra **antisymmetry** `[u,v] = −[v,u]` on `𝒱₁` (equivalently `lie_self`,
`u₍₀₎u = 0`) is `u₍₀₎v + v₍₀₎u = T(u₍₁₎v)` (skew-symmetry 5.1.8) together with
`u₍₁₎v ∈ 𝒱₀ = ℂ𝟙` (VA1) and `T𝟙 = 0`. Skew-symmetry `Core.SkewSymmetry.skew` (5.1.8) is
**proved** `sorry`/axiom-free (via `Core.WeakAssoc`), so antisymmetry
(`bracketV1_antisymm`, via the recorded reduction `bracketV1_antisymm_of_skew`) and hence the
`LieRing`/`LieAlgebra ℂ (𝒱₁)` instances are unconditional.

## What this file assembles (`sorry`-free / axiom-free)

* `bracketV1_antisymm` — antisymmetry on `𝒱₁`, unconditional (from `skew_mode` at `n = 0`).
* `instLieRingGradingOne` / `instLieAlgebraGradingOne` — the `LieRing`/`LieAlgebra ℂ`
  structure on `𝒱₁` with bracket `bracketV1`.
* `primaryV` (`𝒫𝒱ₙ`, Gannon 5.2.3) — the **primary subspace** of weight `n`,
  `{v ∈ 𝒱ₙ | Lₖv = 0 ∀ k ≥ 1}`, as a `Submodule ℂ 𝒱`.
* `griessMul` — the **Griess product** `u × v = u₍₁₎v` on `𝒱₂` (Gannon §5.2.1; Griess [263]),
  well-defined into `𝒱₂` by VA1, with the symmetric (`griessMul_comm_of_grading1_eq_bot`,
  commutative once `𝒱₁ = 0`) and unital data recorded.

## Dependencies
* `VOA.Core.Reconstruction` (the field `n`-th-product theorem `nth_product`,
  hence transitively `Identities`, `Goddard`, `Dong`); `Core.SkewSymmetry` (the discharged
  skew gate, for antisymmetry).

## Status
Zero-mode `o(u)` + grade preservation, `zeroMode_isDerivation`, `bracketV1` +
Jacobi, the unconditional antisymmetry, the `LieRing`/`LieAlgebra ℂ (𝒱₁)` instances, the
primary subspaces `𝒫𝒱ₙ` (5.2.3) and the Griess product on `𝒱₂` are all `sorry`-free /
axiom-free (`[propext, Classical.choice, Quot.sound]`).

## References
* Gannon §5.2.1, eqs. (5.2.1)–(5.2.4); Borcherds [68]; Griess [263]; FLM.
-/

namespace VOA

open Module (End)

universe u

namespace VertexOperatorAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The weight-graded zero-mode `o_k(u) = u₍ₖ₋₁₎` (Gannon §5.2.1) -/

/-- The **zero-mode** `o_k(u) := u₍ₖ₋₁₎ = mode (Y u) (k-1)` of a state of conformal weight
`k` (Gannon §5.2.1).  On a homogeneous `u ∈ 𝒱ₖ` this is Gannon's `o(u)` (the weight `k` is
read off from `u`); we carry `k` explicitly since a general `u` need not be homogeneous.
On `𝒱₁` (`k = 1`) it is `u₍₀₎`, the left action of the `𝒱₁` Lie bracket. -/
def zeroMode (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) (k : ℤ) : End ℂ 𝒱 :=
  mode (W.Y u) (k - 1)

/-- Unfolding the zero-mode on a vector: `o_k(u) v = u₍ₖ₋₁₎ v`. -/
@[simp] theorem zeroMode_apply (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) (k : ℤ) (v : 𝒱) :
    W.zeroMode u k v = W.smul u (k - 1) v := rfl

/-- **Grade preservation (VA1).** The zero-mode `o_k(u)` of a weight-`k` state preserves
every homogeneous grade: for `u ∈ 𝒱ₖ` and `v ∈ 𝒱ₗ`, `o_k(u) v ∈ 𝒱ₗ` (Gannon §5.2.1, since
`u₍ₖ₋₁₎ : 𝒱ₗ → 𝒱_{k+ℓ-(k-1)-1} = 𝒱ₗ`). -/
theorem zeroMode_mem_grading (W : VertexOperatorAlgebra 𝒱) {k : ℤ} {u : 𝒱}
    (hu : u ∈ W.grading k) {ℓ : ℤ} {v : 𝒱} (hv : v ∈ W.grading ℓ) :
    W.zeroMode u k v ∈ W.grading ℓ := by
  have h := W.smul_mem_grading hu hv (k - 1)
  rw [show k + ℓ - (k - 1) - 1 = ℓ by ring] at h
  exact h

/-! ## The derivation property `[u₍₀₎, v₍ₙ₎] = (u₍₀₎v)₍ₙ₎` (Gannon 5.2.4) -/

/-- **`u₍₀₎` is a derivation of every product** (Gannon 5.2.4; the `a = 0` case of the
commutator formula 5.1.7c, where `C(0,j) = δ_{j0}`):
`u₍₀₎(v₍ₙ₎w) − v₍ₙ₎(u₍₀₎w) = (u₍₀₎v)₍ₙ₎w` for all `u v w` and `n ∈ ℤ`.

Proved cleanly from the **field `n`-th-product theorem** `nth_product`
(`Y(u₍₀₎v, z) = Res_{z₁}((z₁-z)⁰[Y(u,z₁),Y(v,z)]) = [u₍₀₎, Y(v,z)]`): reading off the
`z^{-n-1}`-coefficient applied to `w` is exactly the claim.  This avoids the
existential-`N` commutator form (`mode_commutator`) entirely. -/
theorem zeroMode_isDerivation (W : VertexOperatorAlgebra 𝒱) (u v w : 𝒱) (n : ℤ) :
    W.smul u 0 (W.smul v n w) - W.smul v n (W.smul u 0 w) = W.smul (W.smul u 0 v) n w := by
  have key := DFunLike.congr_fun (congrFun (nth_product W u v 0) (-n - 1)) w
  rw [show cCoeff 0 (bracketDist (W.Y u) (W.Y v)) (-n - 1)
        = bracketDist (W.Y u) (W.Y v) (-1) (-n - 1) from rfl,
    bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply] at key
  exact key

/-! ## The Lie bracket `[u,v] = u₍₀₎v` on `𝒱₁` (Gannon §5.2.1) -/

/-- The **Lie bracket** `[u,v] := u₍₀₎v` on `𝒱₁` (Gannon §5.2.1).  Well-defined into `𝒱₁`
by VA1: for `u, v ∈ 𝒱₁`, `u₍₀₎v ∈ 𝒱_{1+1-0-1} = 𝒱₁`. -/
def bracketV1 (W : VertexOperatorAlgebra 𝒱) (u v : W.grading 1) : W.grading 1 :=
  ⟨W.smul (u : 𝒱) 0 (v : 𝒱), by
    have h := W.smul_mem_grading u.2 v.2 0
    rwa [show (1 : ℤ) + 1 - 0 - 1 = 1 by ring] at h⟩

/-- Unfolding the bracket to its underlying product. -/
@[simp] theorem bracketV1_coe (W : VertexOperatorAlgebra 𝒱) (u v : W.grading 1) :
    ((W.bracketV1 u v : W.grading 1) : 𝒱) = W.smul (u : 𝒱) 0 (v : 𝒱) := rfl

/-- **Jacobi / Leibniz identity** for the `𝒱₁` bracket (Gannon §5.2.1, from 5.1.7c at
`ℓ=m=n=0`): `[[u,v],w] = [u,[v,w]] − [v,[u,w]]`.  This is the `n=0` case of
`zeroMode_isDerivation` (`(u₍₀₎v)₍₀₎w = u₍₀₎(v₍₀₎w) − v₍₀₎(u₍₀₎w)`); together with
antisymmetry it makes `𝒱₁` a Lie algebra. -/
theorem bracketV1_jacobi (W : VertexOperatorAlgebra 𝒱) (u v w : W.grading 1) :
    W.bracketV1 (W.bracketV1 u v) w
      = W.bracketV1 u (W.bracketV1 v w) - W.bracketV1 v (W.bracketV1 u w) := by
  apply Subtype.ext
  rw [Submodule.coe_sub, bracketV1_coe, bracketV1_coe, bracketV1_coe, bracketV1_coe,
    bracketV1_coe]
  exact (W.zeroMode_isDerivation (u : 𝒱) (v : 𝒱) (w : 𝒱) 0).symm

/-! ## Antisymmetry — the reduction to skew-symmetry

The remaining Lie-algebra axiom, antisymmetry `[u,v] = −[v,u]` on `𝒱₁`, is **not** a
δ-calculus identity.  It is skew-symmetry `Y(u,z)v = e^{zT}Y(v,-z)u` (Gannon 5.1.8) read at
the appropriate coefficient: `u₍₀₎v + v₍₀₎u = T(u₍₁₎v)`, with `u₍₁₎v ∈ 𝒱_{1+1-1-1} = 𝒱₀ =
ℂ𝟙` (VA1, VOA4) and `T𝟙 = 0`.  Skew-symmetry rests on the `n<0`
(normal-ordered) branch of Dong's lemma.

`bracketV1_antisymm_of_skew` records the exact reduction: *given* the coefficient form of
skew-symmetry, antisymmetry on `𝒱₁` follows.  With `skew` (`Core.SkewSymmetry`), this gives the
`LieRing`/`LieAlgebra ℂ (𝒱₁)` instance (Jacobi above is already available). -/

/-- Antisymmetry of the `𝒱₁` bracket, **reduced to skew-symmetry** (Gannon §5.2.1).
Hypothesis `hskew` is the coefficient form of `Core.Identities.skew` (5.1.8) specialised to
`𝒱₁`: `u₍₀₎v + v₍₀₎u = L₋₁(u₍₁₎v)`, where the right side vanishes because `u₍₁₎v ∈ 𝒱₀ = ℂ𝟙`
and `L₋₁𝟙 = T𝟙 = 0`.  Stated as a conditional; the unconditional version is
`bracketV1_antisymm` below. -/
theorem bracketV1_antisymm_of_skew (W : VertexOperatorAlgebra 𝒱) (u v : W.grading 1)
    (hskew : W.smul (u : 𝒱) 0 (v : 𝒱) + W.smul (v : 𝒱) 0 (u : 𝒱) = 0) :
    W.bracketV1 u v = - W.bracketV1 v u := by
  apply Subtype.ext
  rw [Submodule.coe_neg, bracketV1_coe, bracketV1_coe, eq_neg_iff_add_eq_zero]
  exact hskew

/-! ## Antisymmetry, unconditionally, from skew-symmetry -/

/-- `sgn (-1) = -1`. -/
theorem sgn_neg_one : sgn (-1 : ℤ) = -1 := by
  rw [sgn, if_neg (by decide : ¬ Even (-1 : ℤ))]

/-- The skew tower term at `j` for `u v ∈ 𝒱₁`, `n = 0`, vanishes for `j ≥ 1`.
For `j = 1`: `v₍₁₎u ∈ 𝒱₀ = ℂ𝟙` and `T` annihilates `ℂ𝟙` (`T𝟙 = 0`, `T` linear).
For `j ≥ 2`: `(W.Y v)(-1-j) u = v₍ⱼ₎u ∈ 𝒱_{1-j}` with `1-j < 0`, so `= 0`. -/
theorem skew_v1_tower_vanish (W : VertexOperatorAlgebra 𝒱) {u v : 𝒱}
    (hu : u ∈ W.grading 1) (hv : v ∈ W.grading 1) (j : ℕ) (hj : 1 ≤ j) :
    ((j.factorial : ℂ)⁻¹) • (sgn (-(0 : ℤ) - 1 - j)) •
      ((W.toPreVertexAlgebra.T ^ j) ((W.Y v) (-(0 : ℤ) - 1 - j) u)) = 0 := by
  have hmode : (W.Y v) (-(0 : ℤ) - 1 - j) u = W.smul v (j : ℤ) u := by
    rw [PreVertexAlgebra.smul_def, mode_apply, show (-(j : ℤ) - 1) = -(0 : ℤ) - 1 - (j : ℤ) from by ring]
  rw [hmode]
  have hmem : W.smul v (j : ℤ) u ∈ W.grading (1 - (j : ℤ)) := by
    have h := W.smul_mem_grading hv hu (j : ℤ)
    rwa [show (1 : ℤ) + 1 - (j : ℤ) - 1 = 1 - (j : ℤ) by ring] at h
  rcases eq_or_lt_of_le hj with hj1 | hj2
  · have hj1' : (j : ℤ) = 1 := by exact_mod_cast hj1.symm
    rw [hj1', show (1 : ℤ) - 1 = 0 by ring, W.vacuum_grade,
      Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hTvac : (W.toPreVertexAlgebra.T ^ j) W.vacuum = 0 := by
      obtain ⟨k, hk⟩ : ∃ k : ℕ, j = k + 1 := ⟨j - 1, by omega⟩
      rw [hk, pow_succ, Module.End.mul_apply, PreVertexAlgebra.T_vacuum, map_zero]
    have hT0 : (W.toPreVertexAlgebra.T ^ j) (W.smul v (j : ℤ) u) = 0 := by
      rw [hj1', ← hc, map_smul, hTvac, smul_zero]
    rw [hT0, smul_zero, smul_zero]
  · have hjge : 2 ≤ (j : ℤ) := by exact_mod_cast hj2
    rw [W.positivity (1 - (j : ℤ)) (by omega), Submodule.mem_bot] at hmem
    rw [hmem, map_zero, smul_zero, smul_zero]

/-- The coefficient form of skew-symmetry on `𝒱₁`, unconditionally: for `u v ∈ 𝒱₁`,
`u₍₀₎v + v₍₀₎u = 0`.  Read off `skew_mode` at `n = 0`: the `j = 0` term is `sgn(-1)·v₍₀₎u =
-v₍₀₎u`, and all `j ≥ 1` terms vanish (`skew_v1_tower_vanish`). -/
theorem smul_zero_add_swap_eq_zero (W : VertexOperatorAlgebra 𝒱) {u v : 𝒱}
    (hu : u ∈ W.grading 1) (hv : v ∈ W.grading 1) :
    W.smul u 0 v + W.smul v 0 u = 0 := by
  have hsk := W.skew_mode u v 0
  rw [finsum_eq_single _ 0 (fun j hj => skew_v1_tower_vanish W hu hv j
        (Nat.one_le_iff_ne_zero.mpr hj))] at hsk
  have hmode0 : (W.Y v) (-(0 : ℤ) - 1 - ((0 : ℕ) : ℤ)) u = W.smul v (0 : ℤ) u := by
    rw [PreVertexAlgebra.smul_def, mode_apply]; norm_num
  rw [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_zero,
    Module.End.one_apply, hmode0,
    show ((-(0 : ℤ) - 1 - ((0 : ℕ) : ℤ))) = (-1 : ℤ) by norm_num,
    sgn_neg_one, neg_one_smul] at hsk
  rw [hsk, neg_add_cancel]

/-- **Antisymmetry of the `𝒱₁` bracket** (Gannon §5.2.1):
`[u,v] = -[v,u]` on `𝒱₁`.  Discharges the hypothesis of `bracketV1_antisymm_of_skew`
from skew-symmetry. -/
theorem bracketV1_antisymm (W : VertexOperatorAlgebra 𝒱) (u v : W.grading 1) :
    W.bracketV1 u v = - W.bracketV1 v u :=
  W.bracketV1_antisymm_of_skew u v (smul_zero_add_swap_eq_zero W u.2 v.2)

/-! ## Bilinearity of the bracket (δ-calculus; gate-free) -/

/-- `[·,·]` is additive in the first slot. -/
theorem bracketV1_add_left (W : VertexOperatorAlgebra 𝒱) (u₁ u₂ v : W.grading 1) :
    W.bracketV1 (u₁ + u₂) v = W.bracketV1 u₁ v + W.bracketV1 u₂ v := by
  apply Subtype.ext
  rw [Submodule.coe_add, bracketV1_coe, bracketV1_coe, bracketV1_coe, Submodule.coe_add,
    W.smul_add_left]

/-- `[·,·]` is additive in the second slot. -/
theorem bracketV1_add_right (W : VertexOperatorAlgebra 𝒱) (u v₁ v₂ : W.grading 1) :
    W.bracketV1 u (v₁ + v₂) = W.bracketV1 u v₁ + W.bracketV1 u v₂ := by
  apply Subtype.ext
  rw [Submodule.coe_add, bracketV1_coe, bracketV1_coe, bracketV1_coe, Submodule.coe_add,
    W.smul_add_right]

/-- `[·,·]` is `ℂ`-linear in the second slot. -/
theorem bracketV1_smul_right (W : VertexOperatorAlgebra 𝒱) (c : ℂ) (u v : W.grading 1) :
    W.bracketV1 u (c • v) = c • W.bracketV1 u v := by
  apply Subtype.ext
  rw [bracketV1_coe, SetLike.val_smul, SetLike.val_smul, bracketV1_coe, W.smul_smul_right]

/-! ## The Lie-algebra instances on `𝒱₁` -/

/-- **`𝒱₁` is a Lie ring** (Gannon §5.2.1): bracket `[u,v] = u₍₀₎v`, with `add_lie`/`lie_add`
from δ-calculus bilinearity, `lie_self` from the unconditional antisymmetry, and `leibniz_lie`
from the proven Jacobi identity. -/
noncomputable instance instLieRingGradingOne (W : VertexOperatorAlgebra 𝒱) :
    LieRing (W.grading 1) where
  bracket u v := W.bracketV1 u v
  add_lie u₁ u₂ v := W.bracketV1_add_left u₁ u₂ v
  lie_add u v₁ v₂ := W.bracketV1_add_right u v₁ v₂
  lie_self u := by
    have h := W.bracketV1_antisymm u u
    rw [eq_neg_iff_add_eq_zero, ← two_smul ℂ] at h
    show W.bracketV1 u u = 0
    have := smul_eq_zero.mp h
    rcases this with h2 | h0
    · exact absurd h2 (by norm_num)
    · exact h0
  leibniz_lie u v w := by
    show W.bracketV1 u (W.bracketV1 v w)
      = W.bracketV1 (W.bracketV1 u v) w + W.bracketV1 v (W.bracketV1 u w)
    have hj := W.bracketV1_jacobi u v w
    rw [hj]; abel

/-- **`𝒱₁` is a `ℂ`-Lie algebra** (Gannon §5.2.1): the Lie ring above together with
`ℂ`-linearity of the bracket in the second slot. -/
noncomputable instance instLieAlgebraGradingOne (W : VertexOperatorAlgebra 𝒱) :
    LieAlgebra ℂ (W.grading 1) where
  lie_smul c u v := W.bracketV1_smul_right c u v

/-! ## Primary subspaces `𝒫𝒱ₙ` (Gannon 5.2.3) -/

/-- The **primary subspace of weight `n`** `𝒫𝒱ₙ` (Gannon §5.2.1, eq. 5.2.3): the homogeneous
vectors of weight `n` annihilated by every raising mode `Lₖ`, `k ≥ 1`,
`𝒫𝒱ₙ = {v ∈ 𝒱ₙ | Lₖ v = 0 for all k ≥ 1}`.  (For `n = 1` and `L₁𝒱₁ = 0`, `𝒫𝒱₁ = 𝒱₁`; the
weight-`n` primaries are the lowest-weight vectors of the Virasoro action.) -/
def primaryV (W : VertexOperatorAlgebra 𝒱) (n : ℤ) : Submodule ℂ 𝒱 where
  carrier := {v | v ∈ W.grading n ∧ ∀ k : ℤ, 1 ≤ k → W.L k v = 0}
  add_mem' {a b} ha hb := ⟨W.grading n |>.add_mem ha.1 hb.1,
    fun k hk => by rw [map_add, ha.2 k hk, hb.2 k hk, add_zero]⟩
  zero_mem' := ⟨(W.grading n).zero_mem, fun k _ => by rw [map_zero]⟩
  smul_mem' c a ha := ⟨(W.grading n).smul_mem c ha.1,
    fun k hk => by rw [map_smul, ha.2 k hk, smul_zero]⟩

/-- Membership in `𝒫𝒱ₙ` unfolds to: lying in `𝒱ₙ` and being killed by every `Lₖ`, `k ≥ 1`. -/
theorem mem_primaryV (W : VertexOperatorAlgebra 𝒱) (n : ℤ) (v : 𝒱) :
    v ∈ W.primaryV n ↔ v ∈ W.grading n ∧ ∀ k : ℤ, 1 ≤ k → W.L k v = 0 := Iff.rfl

/-- A primary vector lies in its homogeneous grade. -/
theorem primaryV_le_grading (W : VertexOperatorAlgebra 𝒱) (n : ℤ) :
    W.primaryV n ≤ W.grading n := fun _ hv => hv.1

/-! ## The Griess product on `𝒱₂` (Gannon §5.2.1; Griess [263]) -/

/-- The **Griess product** `u × v := u₍₁₎v` on `𝒱₂` (Gannon §5.2.1; Griess [263]).
Well-defined into `𝒱₂` by VA1: for `u, v ∈ 𝒱₂`, `u₍₁₎v ∈ 𝒱_{2+2-1-1} = 𝒱₂`.  On `V♮`
(`𝒱₁ = 0`, `dim 𝒱₂ = 196884`) this is the commutative nonassociative Griess algebra whose
automorphism group is the Monster. -/
def griessMul (W : VertexOperatorAlgebra 𝒱) (u v : W.grading 2) : W.grading 2 :=
  ⟨W.smul (u : 𝒱) 1 (v : 𝒱), by
    have h := W.smul_mem_grading u.2 v.2 1
    rwa [show (2 : ℤ) + 2 - 1 - 1 = 2 by ring] at h⟩

/-- Unfolding the Griess product to its underlying `(1)`-product. -/
@[simp] theorem griessMul_coe (W : VertexOperatorAlgebra 𝒱) (u v : W.grading 2) :
    ((W.griessMul u v : W.grading 2) : 𝒱) = W.smul (u : 𝒱) 1 (v : 𝒱) := rfl

/-- The Griess product is **additive in each slot** (δ-calculus bilinearity, gate-free). -/
theorem griessMul_add_left (W : VertexOperatorAlgebra 𝒱) (u₁ u₂ v : W.grading 2) :
    W.griessMul (u₁ + u₂) v = W.griessMul u₁ v + W.griessMul u₂ v := by
  apply Subtype.ext
  rw [Submodule.coe_add, griessMul_coe, griessMul_coe, griessMul_coe, Submodule.coe_add,
    W.smul_add_left]

theorem griessMul_add_right (W : VertexOperatorAlgebra 𝒱) (u v₁ v₂ : W.grading 2) :
    W.griessMul u (v₁ + v₂) = W.griessMul u v₁ + W.griessMul u v₂ := by
  apply Subtype.ext
  rw [Submodule.coe_add, griessMul_coe, griessMul_coe, griessMul_coe, Submodule.coe_add,
    W.smul_add_right]

/-- **Commutativity of the Griess product when `𝒱₁ = 0`** (Gannon §5.2.1; Griess [263]):
on a VOA with `𝒱₁ = ⊥` (e.g. `V♮`), `u × v = v × u` for `u, v ∈ 𝒱₂`.  Skew (5.1.8) gives
`u₍₁₎v = v₍₁₎u + T(v₍₂₎u)` with `v₍₂₎u ∈ 𝒱_{2+2-2-1} = 𝒱₁ = ⊥`, so the correction `T(v₍₂₎u)`
vanishes.  (For general VOAs the Griess product need not be commutative; the `𝒱₁ = 0`
hypothesis is Griess's setting.) -/
theorem griessMul_comm_of_grading1_eq_bot (W : VertexOperatorAlgebra 𝒱)
    (h1 : W.grading 1 = ⊥) (u v : W.grading 2) :
    W.griessMul u v = W.griessMul v u := by
  apply Subtype.ext
  rw [griessMul_coe, griessMul_coe]
  -- skew at n = 1 on the weight-2 vectors: u₍₁₎v = ∑ⱼ (1/j!) sgn(-2-j) Tʲ((Y v)(-2-j) u)
  have hsk := W.skew_mode (u : 𝒱) (v : 𝒱) 1
  -- every j ≥ 1 term vanishes: (Y v)(-2-j) u = v₍₁₊ⱼ₎u ∈ 𝒱_{2 - j} ⊆ 𝒱₁=⊥ (j=1) or 𝒱_{<0} (j≥2)
  have hsupp : ∀ j : ℕ, j ≠ 0 →
      ((j.factorial : ℂ)⁻¹) • (sgn (-(1 : ℤ) - 1 - j)) •
        ((W.toPreVertexAlgebra.T ^ j) ((W.Y v) (-(1 : ℤ) - 1 - j) u)) = 0 := by
    intro j hj
    have hmode : (W.Y v) (-(1 : ℤ) - 1 - j) (u : 𝒱) = W.smul (v : 𝒱) ((j : ℤ) + 1) (u : 𝒱) := by
      rw [PreVertexAlgebra.smul_def, mode_apply,
        show (-((j : ℤ) + 1) - 1) = -(1 : ℤ) - 1 - (j : ℤ) from by ring]
    rw [hmode]
    have hmem : W.smul (v : 𝒱) ((j : ℤ) + 1) (u : 𝒱) ∈ W.grading (2 - (j : ℤ)) := by
      have h := W.smul_mem_grading v.2 u.2 ((j : ℤ) + 1)
      rwa [show (2 : ℤ) + 2 - ((j : ℤ) + 1) - 1 = 2 - (j : ℤ) by ring] at h
    have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj
    -- `Tʲ` annihilates the produced vector `w ∈ 𝒱_{2-j}` for every `j ≥ 1`: by positivity
    -- when `2-j < 0`; by `T𝟙 = 0` when `2-j = 0` (`w ∈ ℂ𝟙`); by `h1` when `2-j = 1` (`j = 1`).
    have hTw : (W.toPreVertexAlgebra.T ^ j) (W.smul (v : 𝒱) ((j : ℤ) + 1) (u : 𝒱)) = 0 := by
      rcases lt_trichotomy (2 - (j : ℤ)) 0 with hlt | heq | hgt
      · rw [W.positivity _ hlt, Submodule.mem_bot] at hmem
        rw [hmem, map_zero]
      · rw [heq, W.vacuum_grade, Submodule.mem_span_singleton] at hmem
        obtain ⟨c, hc⟩ := hmem
        obtain ⟨k, hk⟩ : ∃ k : ℕ, j = k + 1 := ⟨j - 1, by omega⟩
        rw [← hc, map_smul, hk, pow_succ, Module.End.mul_apply, PreVertexAlgebra.T_vacuum,
          map_zero, smul_zero]
      · have hj1' : (2 : ℤ) - (j : ℤ) = 1 := by omega
        rw [hj1', h1, Submodule.mem_bot] at hmem
        rw [hmem, map_zero]
    rw [hTw, smul_zero, smul_zero]
  rw [finsum_eq_single _ 0 hsupp] at hsk
  -- j = 0 term: sgn(-2) = 1, T⁰ = id, (Y v)(-2) u = v₍₁₎u
  have hmode0 : (W.Y v) (-(1 : ℤ) - 1 - ((0 : ℕ) : ℤ)) (u : 𝒱) = W.smul (v : 𝒱) 1 (u : 𝒱) := by
    rw [PreVertexAlgebra.smul_def, mode_apply]; norm_num
  rw [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_zero, Module.End.one_apply,
    hmode0, show (-(1 : ℤ) - 1 - ((0 : ℕ) : ℤ)) = -2 by norm_num,
    show (sgn (-2 : ℤ)) = 1 by rw [sgn, if_pos (by decide)], one_smul] at hsk
  exact hsk

end VertexOperatorAlgebra

end VOA
