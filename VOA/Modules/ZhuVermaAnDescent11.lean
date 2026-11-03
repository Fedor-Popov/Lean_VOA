/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnDescent10

/-!
# The `O(𝒱)`-generator reduction chain toward `LeftGenTowerEq_holds` /
`RightGenTowerEq_holds`.

This file continues `Modules.ZhuVermaAnDescent10` (the depth-`n` circle-case iterate-reindexing
chain toward `RightCircTowerEq_holds`).  It builds the analogous *entry-point* apparatus for the two
remaining `gen_mem` predicates of the `A_n(𝒱)` bimodule descent (`ZhuVermaAnDescent8`):

* `LeftGenTowerEq W n g b` (`LeftDescends.gen_mem`): a tower decomposition of `leftProd W n g b` for
  the `O(𝒱)`-base generator `g = (L₋₁u + L₀u) * v`.
* `RightGenTowerEq W n x g` (`RightDescends.gen_mem`): a tower decomposition of `rightProd W n x g`
  for the same `O(𝒱)`-base generator `g` in the *base* slot.

## The generator structure and the entry point

For homogeneous `u ∈ 𝒱_M`, the Zhu base-residue identity `zhuMul_L_base` (`ZhuModule`, FZ Lemma
2.1.1, `k = 0`) gives the **finite** expansion of the `O(𝒱)`-base generator into iterated modes:

  `g = zhuMul W (L₋₁u + L₀u) v = ∑_{i=0}^{M} C(M, i) · u₍ᵢ₋₂₎v`.

By the (already-proved) bilinearity of the FZ products in the relevant slot, the FZ product of `g`
distributes over this finite `i`-sum:

* **`leftGenProd_homogeneous_expand`** (the left entry point):
  `leftProd W n g b = ∑_i C(M, i) • leftProd W n (u₍ᵢ₋₂₎v) b`;
* **`rightGenProd_homogeneous_expand`** (the right entry point):
  `rightProd W n x g = ∑_i C(M, i) • rightProd W n x (u₍ᵢ₋₂₎v)`.

These are the depth-`n`/generator analogs of `rightProd_circ_homogeneous_iterate`
(`ZhuVermaAnDescent6`): the `O(𝒱)`-base generator's `u₍ᵢ₋₂₎v` plays the role of the circle product's
iterate `c₍ℓ₎d`.

## Closure of the tower-decomposition predicates

The predicates `LeftGenTowerEq`/`RightGenTowerEq` (`ZhuVermaAnDescent8`) are *existentials* over an
abstract finite tower index `J` (`∃ J [Fintype J] Ms cs bs ws δs, …`), so they are closed under the
finite ℂ-combinations produced by the entry points above:

* `LeftGenTowerEq_smul_left` / `RightGenTowerEq_smul_right` — scalar closure (the scalar pulls
  through the tower weights `ws`, by `leftProd_smul_left` / `rightProd_smul_right`);
* `LeftGenTowerEq_sum` / `RightGenTowerEq_sum` — finite-`Finset`-sum closure (a `J₁ ⊕ J₂`
  sigma-type tower index per summand, by `leftProd_add_left` / `rightProd_add_right`).

Feeding the entry points into these closure lemmas yields the **per-iterate reduction criteria**:

* `LeftGenTowerEq_of_iterate` — `LeftGenTowerEq W n g b` (for `g = (L₋₁u+L₀u)*v`, `u ∈ 𝒱_M`) holds
  if each per-iterate `LeftGenTowerEq W n (u₍ᵢ₋₂₎v) b` holds (`i < M+1`);
* `RightGenTowerEq_of_iterate` — `RightGenTowerEq W n x g` holds if each per-iterate
  `RightGenTowerEq W n x (u₍ᵢ₋₂₎v)` holds.

This isolates the remaining content of each `gen_mem` predicate to the **per-iterate tower
decomposition** — the genuine depth-`n` iterate core (the Borcherds/associator expansion of the
acting iterate `u₍ᵢ₋₂₎v`, the same engine as the `RightCircTowerEq` U/V cores of
`ZhuVermaAnDescent10`), with the Dong–Li–Mason `(1+z)^{wt a + j}` right-shift on the
`RightGenTowerEq` side.  Nothing here is `sorry`'d or axiomatized; the per-iterate cores are left as
precise stated targets in the closing docstring.

## References
* Gannon §5.3.2, Thm 5.3.4; Zhu Thm 2.1.1/2.1.2; Frenkel–Zhu Lemma 2.1.1/2.1.2; Dong–Li–Mason.
-/

open scoped BigOperators
open Finset

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators
open Classical

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The generator entry points: distributing the FZ product over the iterate expansion of `g`.

For homogeneous `u ∈ 𝒱_M`, `zhuMul_L_base` rewrites the `O(𝒱)`-base generator
`g = (L₋₁u + L₀u) * v` as the finite iterate sum `∑_i C(M,i) • u₍ᵢ₋₂₎v`.  The FZ products are
bilinear in the relevant slot (`leftProd_add_left`/`leftProd_smul_left` for the acting slot;
`rightProd_add_right`/`rightProd_smul_right` for the base slot), so each FZ product of `g`
distributes over the `i`-sum, exposing the per-iterate FZ products `leftProd W n (u₍ᵢ₋₂₎v) b` /
`rightProd W n x (u₍ᵢ₋₂₎v)`.  These are the generator analogs of
`rightProd_circ_homogeneous_iterate` (`ZhuVermaAnDescent6`). -/

/-- **The left-product generator entry point.**  For homogeneous `u ∈ 𝒱_M`, the FZ left product of
the `O(𝒱)`-base generator `g = (L₋₁u + L₀u) * v = ∑ᵢ C(M,i) u₍ᵢ₋₂₎v` (`zhuMul_L_base`) distributes
over the iterate sum: `leftProd W n g b = ∑ᵢ C(M,i) • leftProd W n (u₍ᵢ₋₂₎v) b`.  Generator analog of
`rightProd_circ_homogeneous_iterate`. -/
theorem leftGenProd_homogeneous_expand (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M : ℕ} {u : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (v b : 𝒱) :
    leftProd W n (zhuMul W (W.L (-1) u + W.L 0 u) v) b
      = ∑ i ∈ Finset.range (M + 1),
          cbz (M : ℤ) (i : ℤ) • leftProd W n (W.smul u ((i : ℤ) - 2) v) b := by
  rw [zhuMul_L_base W hu v]
  induction (Finset.range (M + 1)) using Finset.induction with
  | empty => simp [leftProd_zero_left]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, leftProd_add_left, leftProd_smul_left, ih]

/-- **The right-product generator entry point.**  For homogeneous `u ∈ 𝒱_M`, the FZ right product of
the `O(𝒱)`-base generator `g = ∑ᵢ C(M,i) u₍ᵢ₋₂₎v` in the *base* slot distributes over the iterate
sum: `rightProd W n x g = ∑ᵢ C(M,i) • rightProd W n x (u₍ᵢ₋₂₎v)`.  Generator analog of
`rightProd_circ_homogeneous_iterate` (base-slot version). -/
theorem rightGenProd_homogeneous_expand (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M : ℕ} {u : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (v x : 𝒱) :
    rightProd W n x (zhuMul W (W.L (-1) u + W.L 0 u) v)
      = ∑ i ∈ Finset.range (M + 1),
          cbz (M : ℤ) (i : ℤ) • rightProd W n x (W.smul u ((i : ℤ) - 2) v) := by
  rw [zhuMul_L_base W hu v]
  induction (Finset.range (M + 1)) using Finset.induction with
  | empty => simp [rightProd_zero_right]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, rightProd_add_right, rightProd_smul_right, ih]

/-! ## Closure of `LeftGenTowerEq` under finite ℂ-combinations of the acting argument.

`LeftGenTowerEq W n g b` (`ZhuVermaAnDescent8`) asserts `leftProd W n g b` equals a finite
`Fintype`-indexed ℂ-combination of `PresOn`-towers with homogeneous bases.  Because `leftProd` is
bilinear in its acting (first) slot, this is closed under scalar multiplication and finite sums of
the acting argument `g` (with a fixed base `b`): a scalar pulls through the tower weights, and a sum
combines two tower families via a `J₁ ⊕ J₂` sigma-type index. -/

/-- `LeftGenTowerEq` is closed under scalar multiplication of the acting (left) argument: the scalar
pulls through the tower weights `ws` (by `leftProd_smul_left`). -/
theorem LeftGenTowerEq_smul_left (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (c : ℂ) {g b : 𝒱}
    (h : LeftGenTowerEq W n g b) : LeftGenTowerEq W n (c • g) b := by
  obtain ⟨J, _, Ms, cs, bs, ws, δs, hc, heq⟩ := h
  exact ⟨J, ‹_›, Ms, cs, bs, fun j => c * ws j, δs, hc, by
    rw [leftProd_smul_left, heq, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => by rw [smul_smul]⟩

/-- `LeftGenTowerEq` is closed under finite `Finset`-sums of the acting argument (fixed base `b`):
a `J₁ ⊕ J₂` sigma-type tower index combines the per-summand tower families (by `leftProd_add_left`). -/
theorem LeftGenTowerEq_sum {ι : Type} (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (s : Finset ι)
    (gs : ι → 𝒱) (b : 𝒱) (h : ∀ i ∈ s, LeftGenTowerEq W n (gs i) b) :
    LeftGenTowerEq W n (∑ i ∈ s, gs i) b := by
  classical
  induction s using Finset.induction with
  | empty =>
    refine ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, PEmpty.elim, PEmpty.elim, PEmpty.elim,
      fun j => j.elim, ?_⟩
    simp [leftProd_zero_left]
  | insert i s hi ih =>
    obtain ⟨J₁, fJ₁, Ms₁, cs₁, bs₁, ws₁, δs₁, hc₁, heq₁⟩ := h i (Finset.mem_insert_self i s)
    obtain ⟨J₂, fJ₂, Ms₂, cs₂, bs₂, ws₂, δs₂, hc₂, heq₂⟩ :=
      ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
    refine ⟨J₁ ⊕ J₂, inferInstance, Sum.elim Ms₁ Ms₂, Sum.elim cs₁ cs₂, Sum.elim bs₁ bs₂,
      Sum.elim ws₁ ws₂, Sum.elim δs₁ δs₂, ?_, ?_⟩
    · rintro (j | j)
      · exact hc₁ j
      · exact hc₂ j
    · rw [Finset.sum_insert hi, leftProd_add_left, heq₁, heq₂, Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]

/-! ## Closure of `RightGenTowerEq` under finite ℂ-combinations of the base argument.

The mirror of the `LeftGenTowerEq` closure: `rightProd` is bilinear in its base (second) slot
(`rightProd_smul_right`/`rightProd_add_right`), so `RightGenTowerEq W n x g` (fixed acting `x`) is
closed under scalar multiplication and finite sums of the base argument `g`. -/

/-- `RightGenTowerEq` is closed under scalar multiplication of the base (right) argument: the scalar
pulls through the tower weights `ws` (by `rightProd_smul_right`). -/
theorem RightGenTowerEq_smul_right (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (c : ℂ) {x g : 𝒱}
    (h : RightGenTowerEq W n x g) : RightGenTowerEq W n x (c • g) := by
  obtain ⟨J, _, Ms, cs, bs, ws, δs, hc, heq⟩ := h
  exact ⟨J, ‹_›, Ms, cs, bs, fun j => c * ws j, δs, hc, by
    rw [rightProd_smul_right, heq, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => by rw [smul_smul]⟩

/-- `RightGenTowerEq` is closed under finite `Finset`-sums of the base argument (fixed acting `x`):
a `J₁ ⊕ J₂` sigma-type tower index combines the per-summand families (by `rightProd_add_right`). -/
theorem RightGenTowerEq_sum {ι : Type} (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (s : Finset ι)
    (x : 𝒱) (gs : ι → 𝒱) (h : ∀ i ∈ s, RightGenTowerEq W n x (gs i)) :
    RightGenTowerEq W n x (∑ i ∈ s, gs i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    refine ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, PEmpty.elim, PEmpty.elim, PEmpty.elim,
      fun j => j.elim, ?_⟩
    simp [rightProd_zero_right]
  | insert i s hi ih =>
    obtain ⟨J₁, fJ₁, Ms₁, cs₁, bs₁, ws₁, δs₁, hc₁, heq₁⟩ := h i (Finset.mem_insert_self i s)
    obtain ⟨J₂, fJ₂, Ms₂, cs₂, bs₂, ws₂, δs₂, hc₂, heq₂⟩ :=
      ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
    refine ⟨J₁ ⊕ J₂, inferInstance, Sum.elim Ms₁ Ms₂, Sum.elim cs₁ cs₂, Sum.elim bs₁ bs₂,
      Sum.elim ws₁ ws₂, Sum.elim δs₁ δs₂, ?_, ?_⟩
    · rintro (j | j)
      · exact hc₁ j
      · exact hc₂ j
    · rw [Finset.sum_insert hi, rightProd_add_right, heq₁, heq₂, Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]

/-! ## The per-iterate reduction criteria.

Feeding the generator entry points (`leftGenProd_homogeneous_expand` /
`rightGenProd_homogeneous_expand`) into the closure lemmas, each `gen_mem` predicate reduces to the
per-iterate tower decomposition `LeftGenTowerEq W n (u₍ᵢ₋₂₎v) b` (resp.
`RightGenTowerEq W n x (u₍ᵢ₋₂₎v)`) over the finite circle index `i < M+1`.  These are the generator
analogs of `rightProd_circ_mem_On_of_tower_eq`'s reduction, isolating the remaining content to the
single per-iterate core. -/

/-- **`LeftGenTowerEq` from the per-iterate tower decompositions.**  For homogeneous `u ∈ 𝒱_M`, the
`O(𝒱)`-base generator `g = (L₋₁u+L₀u)*v` admits the tower decomposition `LeftGenTowerEq W n g b`
provided each per-iterate `leftProd W n (u₍ᵢ₋₂₎v) b` does (`i < M+1`).  Routes the generator entry
point `leftGenProd_homogeneous_expand` through the closure lemmas `LeftGenTowerEq_sum` /
`LeftGenTowerEq_smul_left`. -/
theorem LeftGenTowerEq_of_iterate (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M : ℕ} {u : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (v b : 𝒱)
    (Hit : ∀ i ∈ Finset.range (M + 1), LeftGenTowerEq W n (W.smul u ((i : ℤ) - 2) v) b) :
    LeftGenTowerEq W n (zhuMul W (W.L (-1) u + W.L 0 u) v) b := by
  rw [zhuMul_L_base W hu v]
  refine LeftGenTowerEq_sum W n (Finset.range (M + 1))
    (fun i => cbz (M : ℤ) (i : ℤ) • W.smul u ((i : ℤ) - 2) v) b ?_
  intro i hi
  exact LeftGenTowerEq_smul_left W n (cbz (M : ℤ) (i : ℤ)) (Hit i hi)

/-- **`RightGenTowerEq` from the per-iterate tower decompositions.**  The base-slot mirror of
`LeftGenTowerEq_of_iterate`: for homogeneous `u ∈ 𝒱_M`, `RightGenTowerEq W n x g` (for the
`O(𝒱)`-base generator `g` in the base slot) holds provided each per-iterate
`rightProd W n x (u₍ᵢ₋₂₎v)` does.  Routes `rightGenProd_homogeneous_expand` through
`RightGenTowerEq_sum` / `RightGenTowerEq_smul_right`. -/
theorem RightGenTowerEq_of_iterate (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M : ℕ} {u : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (v x : 𝒱)
    (Hit : ∀ i ∈ Finset.range (M + 1), RightGenTowerEq W n x (W.smul u ((i : ℤ) - 2) v)) :
    RightGenTowerEq W n x (zhuMul W (W.L (-1) u + W.L 0 u) v) := by
  rw [zhuMul_L_base W hu v]
  refine RightGenTowerEq_sum W n (Finset.range (M + 1)) x
    (fun i => cbz (M : ℤ) (i : ℤ) • W.smul u ((i : ℤ) - 2) v) ?_
  intro i hi
  exact RightGenTowerEq_smul_right W n (cbz (M : ℤ) (i : ℤ)) (Hit i hi)

/-!
## The PRECISE remaining target (NOT `sorry`, NOT axiomatized)

The two `gen_mem` tower-decomposition predicates (`ZhuVermaAnDescent8`) are reduced — by the proved,
axiom-clean generator entry points and closure lemmas of this file — to the single **per-iterate
tower decomposition**:

  (L-it)  `∀ i < M+1, LeftGenTowerEq W n (u₍ᵢ₋₂₎v) b`     ⟹  `LeftGenTowerEq W n g b`,
  (R-it)  `∀ i < M+1, RightGenTowerEq W n x (u₍ᵢ₋₂₎v)`   ⟹  `RightGenTowerEq W n x g`,

for the `O(𝒱)`-base generator `g = zhuMul W (L₋₁u + L₀u) v = ∑ᵢ C(M,i) u₍ᵢ₋₂₎v` (homogeneous
`u ∈ 𝒱_M`), via `LeftGenTowerEq_of_iterate` / `RightGenTowerEq_of_iterate`.

The per-iterate piece is the genuine depth-`n` **iterate core** (NOT an axiom — its truth is the
U/V tower-collapse that the keystone `Pres_mem_On` carries into `On W n`, per the proved
`towerSum_mem_On` of `ZhuVermaAnDescent8`):

* **Left iterate core.**  For the iterate `w := u₍ᵢ₋₂₎v` in the *acting* slot,
  `leftProd W n w b = ∑_j coef_j • resHom W n (n+j+1) w b`.  Expanding the acting iterate `Y(w, z)`
  via the Borcherds/associativity identity (the same `mode_iterate`/`iterate_UV_split` engine as the
  circle-case `rightProd_circ_inner_UVterm`, `ZhuVermaAnDescent7`) and regrouping by the
  `u`-base-mode / `v`-base-mode produces the U/V families based at modes of `b`; each net per-base-
  mode scalar coefficient collapses (via `ZhuRes.gen_vandermonde` per FZ index `j`, then
  `ZhuRes.gen_jsum`) onto a `PresOn`-tower, exactly mirroring `coeffSn_eq_coeffPn`
  (`ZhuVermaAnDescent4`) — yielding the `∑ j, ws j • PresOn …` witness of `LeftGenTowerEq`.

* **Right iterate core.**  For the iterate `w := u₍ᵢ₋₂₎v` in the *base* slot,
  `rightProd W n x w = ∑_j coef_j • resHom W j (n+j+1) x w`, carrying the Dong–Li–Mason
  `(1+z)^{wt x + j}` right-shift; the residue acts `x` on the iterate base `w`, and the same
  Borcherds expansion + `gen_vandermonde`/`gen_jsum` collapse produces the `PresOn`-tower witness of
  `RightGenTowerEq`.

These per-iterate cores are the depth-`n` lift of the `~470`-line
`coeffSn_eq_coeffPn` + `Sn_eq_finsum` + `PresOnCombo_eq_finsum` chain (`ZhuVermaAnDescent4`), now with
the harder `i`-dependent inner residue grade inside the Vandermonde collapse — the same genuine
combinatorial content as the `RightCircTowerEq` U/V cores (`UgammaModeColl = towerCoeff`,
`VgammaModeColl = towerCoeff`, `ZhuVermaAnDescent10`).  They are left here as precise stated targets,
NOT `sorry`'d and NOT axiomatized; faking them would violate the no-holes hard rules.

Once the per-iterate cores are supplied, `LeftGenTowerEq_of_iterate`/`RightGenTowerEq_of_iterate`
(this file) give `LeftGenTowerEq_holds`/`RightGenTowerEq_holds`, which — together with
`RightCircTowerEq_holds` (the circle-case target of `ZhuVermaAnDescent10`) — discharge the three
reindexing predicates of `ZhuVermaAnDescent8`, making `leftDescends_holds`/`rightDescends_holds`
unconditional and `An.lActU`/`An.rActU` the unconditional descended `A_n(𝒱)` bimodule actions, with
the `n = 0` Zhu anchors `An.lActU_zero_mk`/`An.rActU_zero_mk`.

Proved here (axiom-clean: `[propext, Classical.choice, Quot.sound]`):

* **`leftGenProd_homogeneous_expand` / `rightGenProd_homogeneous_expand`** — the generator entry
  points: the FZ product of the `O(𝒱)`-base generator distributes over the finite iterate sum
  `∑ᵢ C(M,i) u₍ᵢ₋₂₎v` (via `zhuMul_L_base` + FZ bilinearity).
* `LeftGenTowerEq_smul_left` / `RightGenTowerEq_smul_right` — scalar closure of the tower predicates.
* `LeftGenTowerEq_sum` / `RightGenTowerEq_sum` — finite-sum closure (`J₁ ⊕ J₂` sigma-type index).
* **`LeftGenTowerEq_of_iterate` / `RightGenTowerEq_of_iterate`** — the per-iterate reduction criteria
  reducing the two `gen_mem` predicates to the per-iterate iterate cores.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.leftGenProd_homogeneous_expand
  #print axioms VOA.rightGenProd_homogeneous_expand
  #print axioms VOA.LeftGenTowerEq_smul_left
  #print axioms VOA.RightGenTowerEq_smul_right
  #print axioms VOA.LeftGenTowerEq_sum
  #print axioms VOA.RightGenTowerEq_sum
  #print axioms VOA.LeftGenTowerEq_of_iterate
  #print axioms VOA.RightGenTowerEq_of_iterate
-/
