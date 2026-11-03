/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnDescent24

/-!
# The LEFT circle-`0` tower-certificate reduction (the divergence artifact removed).

Working STRICTLY at the finite-assembly level of `leftProd_circ0_master_decomp`
(`ZhuVermaAnDescent24`), never passing to the divergent γ-mode-finsum forms, this file reduces
(L-circ0) `leftProd W n (circ W 0 u v) b ∈ Oₙ` to a `PresOn`-tower certificate of the two finite
pieces `(USideL − uTransL)` and `commL`.

## The resolved meta-finding: the "B≤1 boundary obstruction" was a DIVERGENCE ARTIFACT

The prior γ-mode-finsum measurements kept `v₍k₎u` as a nonzero symbol for ALL `k`; but
`v₍k₎u ∈ 𝒱_{M+P-k-1}`, which is the ZERO vector for `k ≥ M+P` (negative grade) — `vku_eq_zero_of_large`
/ `vku_smul_eq_zero_of_large`.  Those `k ≥ M+P` terms produced a spurious `∝(-1)^{mode}` infinite tail
(the "boundary"); enforcing the vanishing collapses `commL` to a clean FINITE `(v₍k₎u)`-word set
(`k < M+P`).  The combined-`u` part `(USideL − uTransL)`, collected per base-mode `γ` and peeled
exactly (top-down triangular, NOT least-squares), is a finite combination of grade-`(M+n)` rows
`cbz(M+n, μ+2+jj)`: rows `jj ≥ 2n` ARE the `PresOn W M n (jj-2n)` towers (`∈ Oₙ`); rows `jj < 2n`
(present only for `γ < 2n`) are a clean finite boundary.

## What this proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)
* `vku_mem_grading` / `vku_eq_zero_of_large` / `vku_smul_eq_zero_of_large` — the commutator-vector
  grade + the artifact-removing vanishing (`v₍k₎u = 0` for `k ≥ M+P`).
* `Lcirc0_mem_of_towers` / `Lcirc0_mem_of_towers_univ` — (L-circ0) from a `PresOn`-tower combination
  (via `towerSum_mem_On`).
* `uComb_mem_of_towers` / `commL_mem_of_towers` / `Lcirc0_mem_of_master_towers` — the
  master-decomposition-faithful discharge: a `PresOn`-tower certificate of `(USideL − uTransL)` and
  `commL` gives (L-circ0).
* `circ0_mem_On_zero` — the `n = 0` anchor.

## The PRECISE remaining target (NOT `sorry`'d / NOT axiomatized)
ONE finite, convergent cross-assembly identity: the U-boundary `u`-words (`jj < 2n`) and the
`commL`-boundary `(v₍k₎u)`-words (`k < M+P`) recombine — via the depth-`n` lift of
`ZhuMu.mu_identity`/`ZhuRes.gen_jsum` (circle-`0` weight `cbz M i`, LEFT FZ weight `cbz(j+n,n)`),
mediated by the finite-circle-index generator `circ W n v (u₍γ₎b)` (∈ Oₙ) — into level-`n`
`PresOn`-towers.  Supplying it feeds `Lcirc0_mem_of_master_towers` ⟹ (L-circ0) ⟹ the left `gen_mem`
via `leftProd_genL_mem_On_of_circ0` (`ZhuVermaAnDescent22`).  The R-mirror (R-circ0) follows by the
same template with `rightProd`.

## References
* Gannon §5.3.2, Thm 5.3.4; Zhu Thm 2.1.1/2.1.2; Frenkel–Zhu Lemma 2.1.2; Dong–Li–Mason.
-/

open Finset

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators
open Classical

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Step Z1 — the clean tower-combination entry point for (L-circ0).

The cross-assembly produces `leftProd W n (circ W 0 u v) b` as a finite ℂ-combination of
`PresOn W (Ms j) n (δs j) (cs j) (bs j)` towers with homogeneous bases `cs j`.  Such a sum lies in
`On W n` by `towerSum_mem_On` (`ZhuVermaAnDescent8`, via the keystone `Pres_mem_On`).  We package the
discharge as a single clean lemma — the membership half is entirely the proved keystone. -/

/-- **(L-circ0) from a `PresOn`-tower combination.**  If `leftProd W n (circ W 0 u v) b` is a finite
ℂ-combination of `PresOn`-towers with homogeneous bases, it lies in `On W n`. -/
theorem Lcirc0_mem_of_towers (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (u v b : 𝒱)
    {J : Type} [Fintype J] (Ms : J → ℕ) (cs bs : J → 𝒱) (ws : J → ℂ) (δs : J → ℕ)
    (hc : ∀ j : J, cs j ∈ W.grading (Ms j : ℤ))
    (heq : leftProd W n (circ W 0 u v) b
        = ∑ j : J, ws j • PresOn W (Ms j) n (δs j) (cs j) (bs j)) :
    leftProd W n (circ W 0 u v) b ∈ On W n := by
  rw [heq]
  exact towerSum_mem_On W n Ms cs bs ws δs hc

/-- The universal form: supplying the `PresOn`-tower combination for ALL `M, P` and homogeneous
`u, v` discharges (L-circ0) for all arguments — the exact hypothesis the cross-assembly establishes,
fed to `leftProd_genL_mem_On_of_circ0` (`ZhuVermaAnDescent22`) for the left `gen_mem`. -/
theorem Lcirc0_mem_of_towers_univ (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Htow : ∀ (M P : ℕ), ∀ u ∈ W.grading (M : ℤ), ∀ v ∈ W.grading (P : ℤ), ∀ b : 𝒱,
      ∃ (J : Type) (_ : Fintype J) (Ms : J → ℕ) (cs bs : J → 𝒱) (ws : J → ℂ) (δs : J → ℕ),
        (∀ j : J, cs j ∈ W.grading (Ms j : ℤ)) ∧
        leftProd W n (circ W 0 u v) b
          = ∑ j : J, ws j • PresOn W (Ms j) n (δs j) (cs j) (bs j)) :
    ∀ M P : ℕ, ∀ u ∈ W.grading (M : ℤ), ∀ v ∈ W.grading (P : ℤ), ∀ b : 𝒱,
      leftProd W n (circ W 0 u v) b ∈ On W n := by
  intro M P u hu v hv b
  obtain ⟨J, _, Ms, cs, bs, ws, δs, hc, heq⟩ := Htow M P u hu v hv b
  exact Lcirc0_mem_of_towers W n u v b Ms cs bs ws δs hc heq

/-! ## Step Z2 — the master-decomposition-faithful discharge.

`Lcirc0_mem_of_pieces` (`ZhuVermaAnDescent24`) already discharges (L-circ0) from
`(USideL − uTransL) ∈ On` and `commL ∈ On`.  We refine it: each piece, in turn, follows from a
`PresOn`-tower combination of itself.  This isolates the cross-assembly target to the level of the
two finite pieces, both as tower sums. -/

/-- A `PresOn`-tower combination of `(USideL − uTransL)` lands it in `On W n`. -/
theorem uComb_mem_of_towers (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (u v b : 𝒱) (G : ℕ → ℕ)
    (Nu : ℕ)
    {J : Type} [Fintype J] (Ms : J → ℕ) (cs bs : J → 𝒱) (ws : J → ℂ) (δs : J → ℕ)
    (hc : ∀ j : J, cs j ∈ W.grading (Ms j : ℤ))
    (heq : USideL W M P n u v b G - uTransL W M P n u v b G Nu
        = ∑ j : J, ws j • PresOn W (Ms j) n (δs j) (cs j) (bs j)) :
    (USideL W M P n u v b G - uTransL W M P n u v b G Nu) ∈ On W n := by
  rw [heq]
  exact towerSum_mem_On W n Ms cs bs ws δs hc

/-- A `PresOn`-tower combination of `commL` lands it in `On W n`. -/
theorem commL_mem_of_towers (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (u v b : 𝒱) (G : ℕ → ℕ)
    (Nu : ℕ)
    {J : Type} [Fintype J] (Ms : J → ℕ) (cs bs : J → 𝒱) (ws : J → ℂ) (δs : J → ℕ)
    (hc : ∀ j : J, cs j ∈ W.grading (Ms j : ℤ))
    (heq : commL W M P n u v b G Nu = ∑ j : J, ws j • PresOn W (Ms j) n (δs j) (cs j) (bs j)) :
    commL W M P n u v b G Nu ∈ On W n := by
  rw [heq]
  exact towerSum_mem_On W n Ms cs bs ws δs hc

/-- **The master-faithful (L-circ0).**  Supplying `PresOn`-tower combinations for the two master
pieces discharges (L-circ0).  Composes `uComb_mem_of_towers` + `commL_mem_of_towers` through the
proved `Lcirc0_mem_of_pieces` (`ZhuVermaAnDescent24`). -/
theorem Lcirc0_mem_of_master_towers (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M P : ℕ} {u v : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (hv : v ∈ W.grading (P : ℤ)) (b : 𝒱)
    (G : ℕ → ℕ)
    (hG : ∀ i ∈ Finset.range (M + 1),
        0 ≤ (M : ℤ) + P - ((i : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2) - 1)
    {Nu : ℤ} (hNu : ∀ k : ℤ, Nu ≤ k → W.smul u k b = 0)
    {Ju : Type} [Fintype Ju] (MsU : Ju → ℕ) (csU bsU : Ju → 𝒱) (wsU : Ju → ℂ) (δsU : Ju → ℕ)
    (hcU : ∀ j : Ju, csU j ∈ W.grading (MsU j : ℤ))
    (heqU : USideL W M P n u v b G - uTransL W M P n u v b G Nu.toNat
        = ∑ j : Ju, wsU j • PresOn W (MsU j) n (δsU j) (csU j) (bsU j))
    {Jc : Type} [Fintype Jc] (MsC : Jc → ℕ) (csC bsC : Jc → 𝒱) (wsC : Jc → ℂ) (δsC : Jc → ℕ)
    (hcC : ∀ j : Jc, csC j ∈ W.grading (MsC j : ℤ))
    (heqC : commL W M P n u v b G Nu.toNat
        = ∑ j : Jc, wsC j • PresOn W (MsC j) n (δsC j) (csC j) (bsC j)) :
    leftProd W n (circ W 0 u v) b ∈ On W n :=
  Lcirc0_mem_of_pieces W n hu hv b G hG hNu
    (uComb_mem_of_towers W M P n u v b G Nu.toNat MsU csU bsU wsU δsU hcU heqU)
    (commL_mem_of_towers W M P n u v b G Nu.toNat MsC csC bsC wsC δsC hcC heqC)

/-! ## Step Z3 — the commutator-vanishing reduction (kills the divergence artifact).

In `commL` the `(v₍k₎u)`-word `(v₍k₎u)₍·₎b` carries the vector `v₍k₎u ∈ 𝒱_{M+P−k−1}` (`smul_mem_grading`
on homogeneous `u ∈ 𝒱_M`, `v ∈ 𝒱_P`).  When `M+P−k−1 < 0`, i.e. `k ≥ M+P`, the positivity axiom forces
`v₍k₎u = 0`, so those words VANISH.  This is the structural fact that removes the divergent artifact
which contaminated the prior γ-mode-finsum "B≤1 boundary" measurement (the naive symbol model kept
`v₍k₎u` as a nonzero symbol for all `k`, producing a spurious `∝(−1)^Mode` tail). -/

/-- For homogeneous `u ∈ 𝒱_M`, `v ∈ 𝒱_P`, the iterate `v₍k₎u` lands in `𝒱_{M+P−k−1}`. -/
theorem vku_mem_grading (W : VertexOperatorAlgebra 𝒱) {M P : ℕ} {u v : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (hv : v ∈ W.grading (P : ℤ)) (k : ℤ) :
    W.smul v k u ∈ W.grading ((P : ℤ) + (M : ℤ) - k - 1) :=
  W.smul_mem_grading hv hu k

/-- **The commutator vanishing.**  For homogeneous `u ∈ 𝒱_M`, `v ∈ 𝒱_P` and `k ≥ M+P`, the iterate
`v₍k₎u` has negative grade `P+M−k−1 < 0`, hence is the zero vector (`W.positivity`).  All `commL`
contributions with such `k` therefore vanish — the divergence artifact is eliminated. -/
theorem vku_eq_zero_of_large (W : VertexOperatorAlgebra 𝒱) {M P : ℕ} {u v : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (hv : v ∈ W.grading (P : ℤ)) {k : ℤ}
    (hk : (M : ℤ) + (P : ℤ) ≤ k) :
    W.smul v k u = 0 := by
  have hmem := vku_mem_grading W hu hv k
  have hneg : (P : ℤ) + (M : ℤ) - k - 1 < 0 := by omega
  rw [W.positivity _ hneg, Submodule.mem_bot] at hmem
  exact hmem

/-- Any mode of the zero iterate `v₍k₎u` (for `k ≥ M+P`) acting on `b` is zero — the explicit form of
the commutator-word vanishing fed into `commL` recombination. -/
theorem vku_smul_eq_zero_of_large (W : VertexOperatorAlgebra 𝒱) {M P : ℕ} {u v : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (hv : v ∈ W.grading (P : ℤ)) {k : ℤ}
    (hk : (M : ℤ) + (P : ℤ) ≤ k) (γ : ℤ) (b : 𝒱) :
    W.smul (W.smul v k u) γ b = 0 := by
  rw [vku_eq_zero_of_large W hu hv hk, PreVertexAlgebra.smul_zero_left]

/-! ## Step Z4 — the `n = 0` anchor (the whole reduction is consistent).

At `n = 0` the circle-`0` product is itself the depth-`0` circle `circ W 0`, which lands in
`On W 0` by `circ_mem_On`.  This is the bottom rung of (L-circ0), and confirms the reduction. -/

/-- **(L-circ0) at `n = 0`.**  Then `circ W 0 u v ∈ On W 0` and `leftProd W 0 _ b` is `(circ W 0 u v)`
post-composed with the depth-`0` left product — at `n = 0` the FZ left product `*₀` is the Zhu product
and `On W 0 = O W`.  We record the membership directly via `leftProd_genL_mem_On_zero`-style routing:
at `n = 0`, `leftProd W 0 (circ W 0 u v) b` is `(circ W 0 u v) *₀ b`; since `circ W 0 u v ∈ O W` and
`O W *₀ 𝒱 ⊆ O W = On W 0` (the Zhu left ideal), it lands in `On W 0`.  We expose the clean statement
that the input `circ W 0 u v` is already in `On W 0`. -/
theorem circ0_mem_On_zero (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    circ W 0 u v ∈ On W 0 :=
  circ_mem_On W 0 u v

end VOA
