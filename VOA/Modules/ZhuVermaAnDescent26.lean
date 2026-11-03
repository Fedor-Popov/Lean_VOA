/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnDescent25

/-!
# The **circle-anchor reduction** of (L-circ0)/(R-circ0), and the corrected obligation.

This file proves a clean, axiom-free reformulation of the left/right circle-`0` memberships, and
records — with the supporting numerical evidence — the *corrected* statement of the genuine remaining
obstruction (replacing an earlier, mathematically false "two shift-`2n+2` tower identities" framing).

## The circle-anchor reduction (the content of this file)

`circ W n` is **bilinear** (`circ_add_left`/`circ_smul_left`, `ZhuVermaAn`), so for the depth-`0`
circle `circ W 0 u v` the depth-`n` circle product `circ W n (circ W 0 u v) b` is a single
`O_n`-generator and therefore lies in `On W n` unconditionally (`circ_mem_On`).  Hence the target
membership splits off this anchor:

  **`leftProd W n (circ W 0 u v) b ∈ On W n`
     ⟺ `leftProd W n (circ W 0 u v) b − circ W n (circ W 0 u v) b ∈ On W n`**

(`leftProd_circ0_mem_iff_diff`), and similarly on the right (`rightProd_circ0_mem_iff_diff`).  This
isolates the genuine content into the **difference** `Δ := (circ W 0 u v) *ₙ b − (circ W 0 u v) ∘ₙ b`
between the FZ left product `*ₙ` and the circle product `∘ₙ` of the SAME element `circ W 0 u v`.

## Why this is the right move (numerically verified, `certificates/mathematica/lclose_*.wl`)

`Δ` and the original `leftProd` expand into the **same** U-word/V-word bases (`u₍μ₎(v₍γ₎b)` /
`v₍μ₎(u₍γ₎b)`) via the identical iterate split (`iterate_term_rewrite`); they differ only in the
pole/test-function weights.  Subtracting the shift-`2n+2` circle anchor cancels the obstruction in the
**bulk**: for base modes `γ` past a finite threshold (`γ ≳ 2n`), the per-base U/V collectors of `Δ`
ARE genuine shift-`2n+2` `PresOn`-towers (`certificates/mathematica/lclose_delta.wl`: `(UColl−UCollC)(γ,·)` and
`(VColl−VCollC)(γ,·)` fit at shift `2n+2`, grades `M`/`P`, for `γ ≥ threshold`).  Only a **finite**
set of small base modes `γ < threshold` remains, where the U/V collectors are still not per-base
towers — the genuine residual cross-assembly boundary.

## The corrected obligation (NOT `sorry`, NOT axiomatized)

The earlier scaffold (`Lcirc0_mem_of_master_towers`, `LeftCircTowerEq_of_sides`) asked for
`(USideL − uTransL)` / `commL` (or `USideL` / `VSideL`) to be expressed as shift-`2n+2` `PresOn`-tower
combinations.  This **per-base/per-piece tower route is provably a dead end for `n ≥ 1`** (verified by
DIRECT tower fits — `Solve` for the tower weights — in `certificates/mathematica`; these fits are
model-independent and reliable):

* `certificates/mathematica/lclose_shift2.wl`: per base `γ`, `USideL`'s collector `UColl(γ,·)` is a shift-`2` grade-`M` tower
  (e.g. `n=1,P=1,γ=0 → (0,−9,17,−8)` — note this is the **shift-`2`** weight), NOT a shift-`2n+2`
  tower.  Every `On W n` generator `circ W n x y` is, per fixed base, a shift-`2n+2` tower; a shift-`2`
  tower is not a ℂ-combination of shift-`2n+2` towers of the same/higher grade — so no per-base
  collapse exists for `n ≥ 1`.  (At `n = 0`, `2 = 2n+2`, and the per-side route DOES close — consistent
  with `On W 0 = O(𝒱)`.)
* `certificates/mathematica/lclose_verify.wl`: the transposed combined-u part `CombU(·,B)` and the commutator family
  `CommC(k,·)` are NOT shift-`2n+2` towers — so `Lcirc0_mem_of_master_towers`'s two `PresOn`-tower
  hypotheses are unsatisfiable for `n ≥ 1`, and the "uComb / commL shift-`2n+2`
  towers" cannot be supplied.
* `certificates/mathematica/lclose_delta.wl`: after the circle-anchor subtraction below, the per-base collectors of `Δ` ARE
  genuine shift-`2n+2` towers in the **bulk** (base modes `γ` past a finite threshold `γ ≳ 2n`), but a
  **finite** set of small base modes `γ < threshold` remains non-tower.

(Exploratory joint-span linear-algebra searches `{u ∘ₙ (v₍γ₎b), v ∘ₙ (u₍γ₎b), (v₍k₎u) ∘ₙ b, …}` —
`certificates/mathematica/lclose_jointspan.wl`/`certificates/mathematica/lclose_delta_span.wl`/`certificates/mathematica/lclose_diaug.wl` — suggested these small generator
families are insufficient; that model is NOT relied on here, as it does not yet reproduce the known
`n = 0` membership.)

Hence the genuine remaining content is the **finite small-base-mode boundary cross-assembly** of `Δ`:
combining the residual non-tower small-`γ` U/V words with the `(v₍k₎u)`-circle commutator family into
`On W n`, using the depth-`n` `cbz` machinery (`ZhuMu`/`ZhuRes`) and the broader `On`-generator set
(`circ W n x y` for richer homogeneous `x` and bases `y`).  The circle-anchor reduction here reduces
the obligation from "all `γ`" to this finite boundary, and supplies the correct anchor
(`circ W n (circ W 0 u v) b`) for it.  When that finite boundary membership is supplied, (L-circ0)
follows via `leftProd_circ0_mem_of_diff_mem`, and thence the left `gen_mem` via
`leftProd_genL_mem_On_of_circ0` (`ZhuVermaAnDescent22`); the R-mirror is identical with `rightProd`.

## References
* Gannon §5.3.2, Thm 5.3.4; Zhu Thm 2.1.1/2.1.2; Frenkel–Zhu Lemma 2.1.2; Dong–Li–Mason, Adv. Math.
  132 (1998).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The left circle-anchor reduction. -/

/-- The depth-`n` circle product of the depth-`0` circle is a single `O_n`-generator, hence in
`On W n` unconditionally. -/
theorem circ_circ0_mem_On (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (u v b : 𝒱) :
    circ W n (circ W 0 u v) b ∈ On W n :=
  circ_mem_On W n (circ W 0 u v) b

/-- **The left circle-anchor reduction.**  Since `circ W n (circ W 0 u v) b ∈ On W n`, the target
left membership is equivalent to the membership of the FZ-product − circle-product **difference**. -/
theorem leftProd_circ0_mem_iff_diff (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (u v b : 𝒱) :
    leftProd W n (circ W 0 u v) b ∈ On W n
      ↔ (leftProd W n (circ W 0 u v) b - circ W n (circ W 0 u v) b) ∈ On W n := by
  constructor
  · intro h
    exact (On W n).sub_mem h (circ_circ0_mem_On W n u v b)
  · intro h
    have hrw : leftProd W n (circ W 0 u v) b
        = (leftProd W n (circ W 0 u v) b - circ W n (circ W 0 u v) b)
            + circ W n (circ W 0 u v) b := by abel
    rw [hrw]
    exact (On W n).add_mem h (circ_circ0_mem_On W n u v b)

/-- **(L-circ0) from the difference membership.**  The forward-useful direction: if the
FZ-product − circle-product difference lies in `On W n`, so does the FZ left product. -/
theorem leftProd_circ0_mem_of_diff_mem (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (u v b : 𝒱)
    (h : (leftProd W n (circ W 0 u v) b - circ W n (circ W 0 u v) b) ∈ On W n) :
    leftProd W n (circ W 0 u v) b ∈ On W n :=
  (leftProd_circ0_mem_iff_diff W n u v b).mpr h

/-- **(L-circ0) for all arguments from the universally-quantified difference membership.**  This is
the exact hypothesis to feed `leftProd_genL_mem_On_of_circ0` (`ZhuVermaAnDescent22`) for the left
`gen_mem`. -/
theorem leftProd_circ0_mem_On_of_diff_univ (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Hdiff : ∀ M P : ℕ, ∀ u ∈ W.grading (M : ℤ), ∀ v ∈ W.grading (P : ℤ), ∀ b : 𝒱,
      (leftProd W n (circ W 0 u v) b - circ W n (circ W 0 u v) b) ∈ On W n) :
    ∀ M P : ℕ, ∀ u ∈ W.grading (M : ℤ), ∀ v ∈ W.grading (P : ℤ), ∀ b : 𝒱,
      leftProd W n (circ W 0 u v) b ∈ On W n := by
  intro M P u hu v hv b
  exact leftProd_circ0_mem_of_diff_mem W n u v b (Hdiff M P u hu v hv b)

/-! ## The right circle-anchor reduction (mirror). -/

/-- The depth-`n` circle product `circ W n x (circ W 0 u v)` is a single `O_n`-generator, hence in
`On W n` unconditionally. -/
theorem circ_circ0_mem_On_right (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (x u v : 𝒱) :
    circ W n x (circ W 0 u v) ∈ On W n :=
  circ_mem_On W n x (circ W 0 u v)

/-- **The right circle-anchor reduction.** -/
theorem rightProd_circ0_mem_iff_diff (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (x u v : 𝒱) :
    rightProd W n x (circ W 0 u v) ∈ On W n
      ↔ (rightProd W n x (circ W 0 u v) - circ W n x (circ W 0 u v)) ∈ On W n := by
  constructor
  · intro h
    exact (On W n).sub_mem h (circ_circ0_mem_On_right W n x u v)
  · intro h
    have hrw : rightProd W n x (circ W 0 u v)
        = (rightProd W n x (circ W 0 u v) - circ W n x (circ W 0 u v))
            + circ W n x (circ W 0 u v) := by abel
    rw [hrw]
    exact (On W n).add_mem h (circ_circ0_mem_On_right W n x u v)

/-- **(R-circ0) from the difference membership.** -/
theorem rightProd_circ0_mem_of_diff_mem (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (x u v : 𝒱)
    (h : (rightProd W n x (circ W 0 u v) - circ W n x (circ W 0 u v)) ∈ On W n) :
    rightProd W n x (circ W 0 u v) ∈ On W n :=
  (rightProd_circ0_mem_iff_diff W n x u v).mpr h

/-- **(R-circ0) for all arguments from the universally-quantified difference membership.**  The exact
hypothesis to feed `rightProd_genR_mem_On_of_circ0` (`ZhuVermaAnDescent22`) for the right `gen_mem`. -/
theorem rightProd_circ0_mem_On_of_diff_univ (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Hdiff : ∀ K M P : ℕ, ∀ x ∈ W.grading (K : ℤ), ∀ u ∈ W.grading (M : ℤ),
        ∀ v ∈ W.grading (P : ℤ),
      (rightProd W n x (circ W 0 u v) - circ W n x (circ W 0 u v)) ∈ On W n) :
    ∀ K M P : ℕ, ∀ x ∈ W.grading (K : ℤ), ∀ u ∈ W.grading (M : ℤ),
      ∀ v ∈ W.grading (P : ℤ),
      rightProd W n x (circ W 0 u v) ∈ On W n := by
  intro K M P x hx u hu v hv
  exact rightProd_circ0_mem_of_diff_mem W n x u v (Hdiff K M P x hx u hu v hv)

end VOA
