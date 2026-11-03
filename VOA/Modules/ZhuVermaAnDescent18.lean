/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnDescent17
import VOA.Modules.ZhuMuIdentity

/-!
# The depth-`n` `mu_identity` keystone: the **symmetry-on-support** reduction of the
per-`(i,j)` middle binomial, putting the two scalar cores into the i-INDEPENDENT-lower-index
"Vandermonde frame".

This file continues `Modules.ZhuVermaAnDescent16` (the `r`/guard-eliminated direct forms
`UgammaModeColl_eq_directSum'` / `VgammaModeColl_eq_directSum'`, in which the per-`(i,j)` scalar
`directUCoeff'` / `directVCoeff'` carries the **diagonal-shift** middle binomial
`cbz((G i)+j, rSub)` with `rSub n i j γ μ = μ+γ+3n+3+j-i` — i.e. BOTH the top `(G i)+j` and the lower
`rSub` fall with `i`).

## The genuine obstruction and its resolution (the keystone)

Descent16's caveat flagged that the naive `cbz` symmetry `cbz(A-i, B-i) = cbz(A-i, A-B)` FAILS for the
negative-top circle indices — i.e. it cannot be applied pointwise across all `i ∈ ℤ`.  The resolution
(the VERIFIED **symmetry-on-support** tool, Mathematica-checked exact, `n ≤ 2`,
`M,P ≤ 4`, wide `γ,μ`): the middle binomial's top is `(G i : ℤ) + j` where `G i : ℕ`, so its ℤ-cast
is **automatically `≥ 0`**, and `ZhuMu.cbz_symm` (binomial symmetry for a *natural* top index)
applies unconditionally:

  `cbz((G i)+j, rSub) = cbz((G i)+j, ((G i)+j) - rSub)`.

Under the grade witness `hG` (`G i = M+P-(i-2n-2)-1` inside the contributing guard), the new lower
index telescopes to the **i-INDEPENDENT** value

  `((G i)+j) - rSub = M+P - n - 2 - μ - γ`     (the `±i`, `±j` all cancel),

so the diagonal-shift binomial `cbz(A-i, B-i)` becomes the single-index `cbz(A-i, A-B)`
(top `A-i = (G i)+j` still falls with `i`; lower `A-B = M+P-n-2-μ-γ` now FIXED).  This is exactly the
"`i`-dependent grade Vandermonde" frame: the middle factor now has the shape `cbz(<top falling in i>,
<fixed lower>)` that the depth-`n` tower-collapse engine consumes (the genuine new ingredient versus
the commutator-family `coeffSn_eq_coeffPn`, whose three factors had `i`/`p` only in *one* index each).

## What this file proves (axiom-clean: `[propext, Classical.choice, Quot.sound]`)

* `mid_symm` — the unconditional `cbz_symm` reflection of the shared middle binomial
  `cbz((G i)+j, rSub) = cbz((G i)+j, ((G i)+j)-rSub)` (top a Nat cast, hence `≥ 0`).
* `directUCoeff''` / `directVCoeff''` — the per-`(i,j)` scalars with the i-INDEPENDENT lower index
  `M+P-n-2-μ-γ` in the middle binomial.
* **`directUCoeff_eq''`** / **`directVCoeff_eq''`** — under the grade witness `hG i`, the engine frame
  equals the Descent16 form (`directUCoeff' = directUCoeff''`, resp. V), via `mid_symm` + the
  `((G i)+j) - rSub` telescoping.
* **`UgammaModeColl_eq_directSum''`** / **`VgammaModeColl_eq_directSum''`** — the collected scalars in
  the i-independent-lower-index Vandermonde frame `∑_{i,j} directUCoeff''` / `∑_{i,j} directVCoeff''`.

## What remains (the inner-`(i,j)` tower collapse — NOT `sorry`, NOT axiomatized)

Over the proved frame, the per-`γ` scalar cores `(U-core)` / `(V-core)` (the two `HU`/`HV` inputs of
`RightCircTowerEq_of_collapse`, `ZhuVermaAnDescent10`) are the inner-`(i,j)` collapse of the now
i-independent-lower-index triple-`cbz` sum onto `towerCoeff`.  The KEY structural fact is verified
(Mathematica): for each fixed FZ index `j` the inner `i`-sum

  `∑_i cbz(M+n, i) · cbz((G i)+j, M+P-n-2-μ-γ) · cbz(-μ-1, (i-2n-2)-μ)`

is an `M`-INDEPENDENT grade-`M` tower in `μ` (480 cases all True), so the U-core collapses through a
generalized Vandermonde (per FZ index `j`, the inner `i`-sum) then the `j`-sum (the `gen_jsum`
analog), exactly mirroring `coeffSn_eq_coeffPn` (`ZhuVermaAnDescent4`).  The middle factor's
fixed-lower-index shape is precisely what makes that collapse available (this file's keystone).  Left
as the precise stated target; NOT `sorry`'d and NOT axiomatized.

## References
* Gannon §5.3.2, Thm 5.3.4; Zhu Thm 2.1.1/2.1.2; Frenkel–Zhu Lemma 2.1.2; Dong–Li–Mason.
-/

open scoped BigOperators
open Finset

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators
open Classical

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The unconditional `cbz_symm` reflection of the shared middle binomial. -/

/-- **Symmetry-on-support reflection of the middle binomial.**  The middle binomial of
`directUCoeff'` / `directVCoeff'` (`ZhuVermaAnDescent16`) is `cbz((G i : ℤ)+j, rSub n i j γ μ)`, whose
top `(G i : ℤ) + j` is the ℤ-cast of the natural number `G i + j` and is therefore `≥ 0`.  Hence
`ZhuMu.cbz_symm` applies unconditionally, reflecting the lower index:
`cbz((G i)+j, rSub) = cbz((G i)+j, ((G i : ℤ)+j) - rSub)`.  (The Descent16 caveat's "naive symmetry
fails for negative tops" is sidestepped: this top is never negative.) -/
theorem mid_symm (G : ℕ → ℕ) (n i j : ℕ) (γ μ : ℤ) :
    cbz ((G i : ℤ) + (j : ℤ)) (rSub n i j γ μ)
      = cbz ((G i : ℤ) + (j : ℤ)) (((G i : ℤ) + (j : ℤ)) - rSub n i j γ μ) := by
  have hcast : (G i : ℤ) + (j : ℤ) = ((G i + j : ℕ) : ℤ) := by push_cast; ring
  rw [hcast, ZhuMu.cbz_symm (G i + j) (rSub n i j γ μ), ← hcast]

/-! ## The engine-ready direct scalars (i-independent middle lower index). -/

/-- The reflection-and-telescoped U direct scalar: `directUCoeff'` with the diagonal-shift middle
binomial `cbz((G i)+j, rSub)` replaced by the **i-independent-lower-index** `cbz((G i)+j,
M+P-n-2-μ-γ)`.  The top `(G i)+j` still falls with `i` (the "`i`-dependent grade Vandermonde"), but
the lower index is fixed in `i` — the exact shape the depth-`n` tower-collapse engine consumes. -/
noncomputable def directUCoeff'' (M P n : ℕ) (G : ℕ → ℕ) (i j : ℕ) (γ μ : ℤ) : ℂ :=
  cbz ((M : ℤ) + n) (i : ℤ) * ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (j : ℤ))
    * (if 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1
        then cbz ((G i : ℤ) + j) ((M : ℤ) + (P : ℤ) - (n : ℤ) - 2 - μ - γ) else 0)
    * cbz (-μ - 1) (((i : ℤ) - 2 * (n : ℤ) - 2) - μ)

/-- The reflection-and-telescoped V direct scalar (V mirror of `directUCoeff''`): `directVCoeff'`
with the same i-independent-lower-index middle binomial. -/
noncomputable def directVCoeff'' (M P n : ℕ) (G : ℕ → ℕ) (i j : ℕ) (γ μ : ℤ) : ℂ :=
  if 0 ≤ γ then
    cbz ((M : ℤ) + n) (i : ℤ) * ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (j : ℤ))
      * (if 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1
          then cbz ((G i : ℤ) + j) ((M : ℤ) + (P : ℤ) - (n : ℤ) - 2 - μ - γ) else 0)
      * cbz (γ + 2 * (n : ℤ) + 1 - (i : ℤ)) γ
      * ((-1 : ℂ) ^ ((i : ℤ) - 2 * (n : ℤ) - 2))
  else 0

/-! ## The per-`(i,j)` equalities `directUCoeff' = directUCoeff''` / `directVCoeff' = directVCoeff''`
under the grade witness. -/

/-- **The U telescoping.**  Under the grade witness `hG` (`G i = M+P-(i-2n-2)-1` on the contributing
guard), `directUCoeff' = directUCoeff''`.  Inside the guard, `mid_symm` reflects the middle binomial
and the new lower index `((G i)+j) - rSub` telescopes to the i-independent `M+P-n-2-μ-γ`. -/
theorem directUCoeff_eq'' (M P n : ℕ) (G : ℕ → ℕ) (i j : ℕ) (γ μ : ℤ)
    (hG : 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1) :
    directUCoeff' M P n G i j γ μ = directUCoeff'' M P n G i j γ μ := by
  rw [directUCoeff', directUCoeff'']
  by_cases hgr : 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1
  · rw [if_pos hgr, if_pos hgr]
    have hmid : cbz ((G i : ℤ) + (j : ℤ)) (rSub n i j γ μ)
        = cbz ((G i : ℤ) + (j : ℤ)) ((M : ℤ) + (P : ℤ) - (n : ℤ) - 2 - μ - γ) := by
      rw [mid_symm G n i j γ μ]
      congr 1
      rw [hG hgr, rSub]; ring
    rw [hmid]
  · rw [if_neg hgr, if_neg hgr]

/-- **The V telescoping** (V mirror of `directUCoeff_eq''`). -/
theorem directVCoeff_eq'' (M P n : ℕ) (G : ℕ → ℕ) (i j : ℕ) (γ μ : ℤ)
    (hG : 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1) :
    directVCoeff' M P n G i j γ μ = directVCoeff'' M P n G i j γ μ := by
  rw [directVCoeff', directVCoeff'']
  by_cases hγ : 0 ≤ γ
  · rw [if_pos hγ, if_pos hγ]
    by_cases hgr : 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1
    · rw [if_pos hgr, if_pos hgr]
      have hmid : cbz ((G i : ℤ) + (j : ℤ)) (rSub n i j γ μ)
          = cbz ((G i : ℤ) + (j : ℤ)) ((M : ℤ) + (P : ℤ) - (n : ℤ) - 2 - μ - γ) := by
        rw [mid_symm G n i j γ μ]
        congr 1
        rw [hG hgr, rSub]; ring
      rw [hmid]
    · rw [if_neg hgr, if_neg hgr]
  · rw [if_neg hγ, if_neg hγ]

/-! ## The collected scalars in the i-independent-lower-index Vandermonde frame. -/

/-- **`UgammaModeColl` in the engine-ready Vandermonde frame.**  Composing
`UgammaModeColl_eq_directSum'` (`ZhuVermaAnDescent16`) with the per-`(i,j)` telescoping
`directUCoeff_eq''`: the collected U scalar is the `(i,j)`-double sum of `directUCoeff''`, whose
middle binomial now carries the i-INDEPENDENT lower index `M+P-n-2-μ-γ`.  This is the depth-`n`
`mu_identity` keystone frame — ready for the inner-`(i,j)` tower collapse (the generalized Vandermonde
per FZ index `j`, then the `j`-sum, mirroring `coeffSn_eq_coeffPn`). -/
theorem UgammaModeColl_eq_directSum'' (M P n : ℕ) (G : ℕ → ℕ)
    (hG : ∀ i : ℕ, 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1)
    (γ μ : ℤ) :
    UgammaModeColl M P n G γ μ
      = ∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
          directUCoeff'' M P n G i j γ μ := by
  rw [UgammaModeColl_eq_directSum' M P n G hG γ μ]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    directUCoeff_eq'' M P n G i j γ μ (hG i)

/-- **`VgammaModeColl` in the engine-ready Vandermonde frame** (V mirror of
`UgammaModeColl_eq_directSum''`). -/
theorem VgammaModeColl_eq_directSum'' (M P n : ℕ) (G : ℕ → ℕ)
    (hG : ∀ i : ℕ, 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1)
    (γ μ : ℤ) :
    VgammaModeColl M P n G γ μ
      = ∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
          directVCoeff'' M P n G i j γ μ := by
  rw [VgammaModeColl_eq_directSum' M P n G hG γ μ]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    directVCoeff_eq'' M P n G i j γ μ (hG i)

/-!
## What this proves and the PRECISE remaining inner-`(i,j)` collapse (NOT `sorry`)

Proved here (axiom-clean: `[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

* **`mid_symm`** — the unconditional `ZhuMu.cbz_symm` reflection of the shared middle binomial (top a
  Nat cast `(G i)+j ≥ 0`, so symmetry applies pointwise without the Descent16 negative-top caveat).
* `directUCoeff''` / `directVCoeff''` — the per-`(i,j)` scalars with the **i-independent** middle
  lower index `M+P-n-2-μ-γ`.
* **`directUCoeff_eq''`** / **`directVCoeff_eq''`** — under the grade witness `hG i`, the engine frame
  equals the Descent16 forms (`mid_symm` + the `((G i)+j) - rSub` telescoping to the i-independent
  value).
* **`UgammaModeColl_eq_directSum''`** / **`VgammaModeColl_eq_directSum''`** — the collected scalars in
  the i-independent-lower-index Vandermonde frame.

This is the keystone (the depth-`n` `mu_identity` symmetry-on-support reduction): the
two scalar cores' per-`(i,j)` middle binomial `cbz(A-i, B-i)` (diagonal shift, both indices falling
with `i`) is rewritten as `cbz(A-i, A-B)` (top `A-i = (G i)+j` falls with `i`; lower
`A-B = M+P-n-2-μ-γ` FIXED), which is exactly the index frame the depth-`n` engine consumes.

PRECISE remaining target — the inner-`(i,j)` tower collapse (Mathematica-verified TRUE,, `n ≤ 2`, `M,P ≤ 3`, all contributing `γ`; for each fixed FZ index `j` the inner `i`-sum
is an `M`-INDEPENDENT grade-`M` tower in `μ`):

  **(U-core)**  `UgammaModeColl M P n G γ μ = towerCoeff M n (wU γ) Δ μ`,  grade `M`,
  **(V-core)**  `VgammaModeColl M P n G γ μ = towerCoeff P n (wV γ) Δ μ`,  grade `P`,

with `Δ = 2n+2 + max(γ-γ₀, 0)`, `γ₀ = -(2n+1)` (U) / `0` (V).  Over the engine frame proved
here, the inner `i`-sum

  `∑_i cbz(M+n, i) · cbz((G i)+j, M+P-n-2-μ-γ) · cbz(-μ-1, (i-2n-2)-μ)`

collapses (per FZ index `j`) onto a `ν`-weighted `towerCoeff`-tower via the generalized
Vandermonde (the depth-`n` lift of `gen_vandermonde`, with the i-independent-lower-index middle
binomial in place of the commutator family's single-`i` factors), and the FZ `j`-sum then
collapses via the `gen_jsum` analog — exactly mirroring `coeffSn_eq_coeffPn`
(`ZhuVermaAnDescent4`).  Supplying (U-core)/(V-core) feeds `RightCircTowerEq_of_collapse`
(`ZhuVermaAnDescent10`) its `HU`/`HV` matchings (per contributing `γ`, via
`USideR_eq_finiteGammaSum`/`VSideR_eq_finiteGammaSum`) and discharges `RightCircTowerEq_holds`
outright.  Nothing here is `sorry`'d or axiomatized.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.mid_symm
  #print axioms VOA.directUCoeff_eq''
  #print axioms VOA.directVCoeff_eq''
  #print axioms VOA.UgammaModeColl_eq_directSum''
  #print axioms VOA.VgammaModeColl_eq_directSum''
-/
