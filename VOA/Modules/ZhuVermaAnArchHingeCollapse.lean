/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchAnmFull
import VOA.Modules.ZhuVermaAnArchAnmIdeal
import VOA.Modules.ZhuVermaAnArchMU

/-!
# The HINGE COLLAPSE — `OnmFull W n 0` vs `Onm W n 0`, and the DJ-2.8 wiring of `MUGradedAction`

The faithful Zhu bijection (`ZhuVermaAnArchFaithfulBijection.zhuBijectionIrr_scorecard`) rests, through
the `G : GenFromBottomFinalFamily` field's `q_act`, on the Dong–Jiang `M(U)` graded-action crux
`MUGradedAction W` (`ZhuVermaAnArchMU.MUGradedAction`).  `MUGradedAction_of_gens`
(`ZhuVermaAnArchMU`) reduces that crux to **three pure-membership families into the partial ideal**
`Onm W n 0` (= the Dong–Jiang `O'_{n,0}`):

* `hcirc`      : `anmRight W n 0 (anmCirc W n 0 c d) v ∈ Onm W n 0`;
* `hcrossCirc` : `anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0`;
* `hcrossL`    : `anmRight W n 0 a (anmLgen W 0 0 c) ∈ Onm W n 0`.

The published **Dong–Jiang Lemma 2.8** (`V *^n_{m,p} O_{p,m} ⊆ O_{n,m}` and `O_{n,p} *^n_{m,p} V ⊆
O_{n,m}`, `arXiv:math/0601626`, proved separately in the `ZhuVermaAnArchDJ22`/`-DJ27` files) places
these families into the **FULL** ideal `OnmFull W n 0` (= `O'_{n,0} ⊔ O''_{n,0} ⊔ O'''_{n,0}`), *not*
into `Onm W n 0`.  To feed `MUGradedAction_of_gens` we therefore need the **collapse**
`OnmFull W n 0 = Onm W n 0`.

## What this file establishes

* `onmFull_le_Onm_of_gens` — the genuinely-true **reduction** of the reverse containment
  `OnmFull W n 0 ≤ Onm W n 0` to the two extra-summand generator families landing in `Onm W n 0`
  (the associator-defect `O''` generators and the level-mixing `O'''` generators).  Pure `sup_le` /
  `Submodule.span_le` bookkeeping; FULLY proven.
* `onmFull_eq_Onm_of_gens` — combined with the proven `Onm_le_OnmFull`, the collapse
  `OnmFull W n 0 = Onm W n 0` **given** those two generator families.
* `OnmCollapses` — the precise collapse predicate, and `MUGradedAction` wired from DJ-2.8-into-`OnmFull`
  plus the collapse (`mUGradedAction_of_dj28_collapse`).

## Status of the collapse (engine + the DJ Lemma 2.2/2.6/2.7 mechanism)

**The collapse `OnmFull W n 0 = Onm W n 0` appears to HOLD** (engine-supported on the rank-1 free
boson); it is **NOT** proved here as an unconditional Lean theorem because its content is exactly the
DJ Lemma 2.2/2.6/2.7 *into-`O'`* combinatorics — the two per-generator memberships carried below.  It
is correctly conditioned on those (the hypotheses of `onmFull_eq_Onm_of_gens` / `OnmCollapses`), NOT
faked and NOT axiomatised.

Evidence (rank-1 free boson, `certificates/mathematica/hinge_rigor2.wl` + `certificates/mathematica/hinge_o2o3.wl`, with an explicit
*basis-grade guard* so no truncation false-positives/negatives):

* the cross-circle family `a *^n_0 (c ∘^0_0 d)` (the genuine load-bearing `hcrossCirc`) lies in
  `Onm W n 0` for **every** tested homogeneous `a, c, d` whose image fits the basis (image grades 5, 6
  confirmed in the rank-29 `Onm[1,0]` span);
* the level-mixing `O'''_{n,0}` grading-generator-carried generators lie in `Onm W n 0`;
* the `O''_{n,0}` associator-defect and the `O'''` circle-carried generators are confirmed at the
  higher basis of `certificates/mathematica/hinge_o2o3.wl`.

**Why this is NOT the (true) DLM obstruction.**  The free-boson fact `V *_n O_0 ⊄ O_n`
(see `ZhuVermaAnArch`, Bug A) is about the **DLM** ideal `O_n = span{a ∘_n b} ⊔ {(L(-1)+L(0))a}`
under the **unshifted** grading generator and the diagonal product `*_n`.  The Dong–Jiang `O'_{n,0}`
here is a *different* ideal: it carries the **shifted** grading generator `L(-1)u + (L(0) − n)u`, and
its absorption identity `anmRight_zero_Lgen_eq` (`ZhuVermaAnArchAnmIdeal`),
`(L(-1)u+(L(0)−n)u) *^n_0 v = (n+1)·(u ∘^n_0 v)`, is precisely what re-expresses the extra-summand
generators as `O'_{n,0}` circle generators (DJ Lemma 2.2).  So the DLM counterexample does **not**
apply to this collapse.

## The Lean status of the collapse

Even granting that the collapse HOLDS mathematically, it is **not yet a discharged Lean term**: the
two per-generator memberships `assocDefect … ∈ Onm` (DJ Lemma 2.6 into `O'`) and `levelMix … ∈ Onm`
(DJ Lemma 2.7 into `O'`) are the genuine residual.  The sibling `ZhuVermaAnArchDJ22`/`-DJ27` files
currently land their published-DJ conclusions in `OnmFull` (the full ideal), so they discharge the
*into-`OnmFull`* version `DJ28IntoFull`, not the *into-`Onm`* memberships.  Hence the collapse is
carried as the hypothesis `OnmCollapses`, reduced by `onmFull_le_Onm_of_gens` to exactly those two
families.

## The load-bearing slice

The faithful bijection actually consumes only the three `MUGradedAction_of_gens` families (bundled as
`NeededSliceMems`), each engine-confirmed into `Onm W n 0` as above.  `mUGradedAction_of_neededSlice`
closes `MUGradedAction` from them via the proven `MUGradedAction_of_gens` — the route that needs only
the verified `O'`-slice, independent of the full-blanket collapse.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemmas 2.2, 2.6, 2.7, 2.8, def of
`O' + O'' + O'''`); Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The genuinely-true reduction of the reverse containment to the extra-summand generators. -/

/-- **The reverse containment `OnmFull W n m ≤ Onm W n m`, reduced to its two extra-summand generator
families** (FULLY proven; pure `sup_le` / `Submodule.span_le`).  Since `OnmFull = Onm ⊔ OnmAssoc ⊔
OnmLevel` and `Onm ≤ Onm` is trivial, the reverse containment holds iff every `O''_{n,m}`
(associator-defect) generator and every `O'''_{n,m}` (level-mixing) generator lies in `Onm W n m`.
This isolates the genuine Dong–Jiang Lemma 2.6 / Lemma 2.7 *into-`O'`* content. -/
theorem onmFull_le_Onm_of_gens (W : VertexOperatorAlgebra 𝒱) (n m : ℕ)
    (hAssoc : ∀ (p₁ p₂ p₃ : ℕ) (a b c v : 𝒱), assocDefect W n m p₁ p₂ p₃ a b c v ∈ Onm W n m)
    (hLevel : ∀ (p : ℕ) (a v g : 𝒱), g ∈ Onm W p p → levelMix W n m p a g v ∈ Onm W n m) :
    OnmFull W n m ≤ Onm W n m := by
  rw [OnmFull]
  refine sup_le (sup_le le_rfl ?_) ?_
  · -- `OnmAssoc ≤ Onm`
    rw [OnmAssoc, Submodule.span_le]
    rintro x ⟨p₁, p₂, p₃, a, b, c, v, rfl⟩
    exact hAssoc p₁ p₂ p₃ a b c v
  · -- `OnmLevel ≤ Onm`
    rw [OnmLevel, Submodule.span_le]
    rintro x ⟨p, a, v, g, hg, rfl⟩
    exact hLevel p a v g hg

/-- **The collapse `OnmFull W n m = Onm W n m`, given the two extra-summand generator families.**
The forward containment `Onm ≤ OnmFull` is the proven `Onm_le_OnmFull`; the reverse is
`onmFull_le_Onm_of_gens`.  (At `m = 0` this is the collapse the DJ-2.8 wiring of `MUGradedAction`
needs; the collapse is engine-supported on the free boson — see the file header — but its content is
exactly the two generator-family hypotheses, which are the DJ Lemma 2.6/2.7 *into-`O'`* combinatorics
and are NOT discharged here; only the reduction is.) -/
theorem onmFull_eq_Onm_of_gens (W : VertexOperatorAlgebra 𝒱) (n m : ℕ)
    (hAssoc : ∀ (p₁ p₂ p₃ : ℕ) (a b c v : 𝒱), assocDefect W n m p₁ p₂ p₃ a b c v ∈ Onm W n m)
    (hLevel : ∀ (p : ℕ) (a v g : 𝒱), g ∈ Onm W p p → levelMix W n m p a g v ∈ Onm W n m) :
    OnmFull W n m = Onm W n m :=
  le_antisymm (onmFull_le_Onm_of_gens W n m hAssoc hLevel) (Onm_le_OnmFull W n m)

/-! ## The collapse predicate and the DJ-2.8 wiring of `MUGradedAction`. -/

/-- **`OnmCollapses W n`** — the (level-`0`) collapse `OnmFull W n 0 ≤ Onm W n 0`.  Carried as a
hypothesis, NOT an axiom: engine-supported on the free boson (see the header) but its Lean content is
the DJ Lemma 2.6/2.7 *into-`O'`* memberships, which are not yet discharged terms (the sibling DJ
files land in `OnmFull`).  We keep it as a clean named predicate so the chain below is exact;
`onmFull_le_Onm_of_gens` reduces it to those two generator families. -/
def OnmCollapses (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Prop :=
  OnmFull W n 0 ≤ Onm W n 0

/-- **DJ Lemma 2.8, instantiated, lands the three `MUGradedAction_of_gens` families in the FULL
ideal** — packaged as a single hypothesis predicate.  This is exactly the published Dong–Jiang
Lemma 2.8 conclusion (`V *^n_{m,p} O_{p,m} ⊆ O_{n,m}`, `O_{n,p} *^n_{m,p} V ⊆ O_{n,m}`) specialised
to the `m = 0` instances the `M(U)` `𝒱`-action consumes; it is proved separately (the
`ZhuVermaAnArchDJ22`/`-DJ27` files land their conclusions in `OnmFull`). -/
structure DJ28IntoFull (W : VertexOperatorAlgebra 𝒱) : Prop where
  /-- The diagonal right-module family `O'_{n,0} *^n_0 𝒱`, into the full ideal. -/
  circ : ∀ (n : ℕ) (c d v : 𝒱), anmRight W n 0 (anmCirc W n 0 c d) v ∈ OnmFull W n 0
  /-- The cross circle family `𝒱 *^n_0 (circle of O(𝒱))`, into the full ideal. -/
  crossCirc : ∀ (n : ℕ) (a c d : 𝒱), anmRight W n 0 a (anmCirc W 0 0 c d) ∈ OnmFull W n 0
  /-- The cross grading-generator family `𝒱 *^n_0 (grading-gen of O(𝒱))`, into the full ideal. -/
  crossL : ∀ (n : ℕ) (a c : 𝒱), anmRight W n 0 a (anmLgen W 0 0 c) ∈ OnmFull W n 0

/-- **`MUGradedAction W` from DJ-2.8-into-`OnmFull` plus the collapse.**  Given that DJ Lemma 2.8 lands
the three `M(U)` `𝒱`-action families in `OnmFull W n 0` (`hDJ`) and that the full ideal collapses to
the partial ideal at every level (`hcol`), every family lands in `Onm W n 0`, and the proven reduction
`MUGradedAction_of_gens` (`ZhuVermaAnArchMU`) assembles the Dong–Jiang `M(U)` graded-action crux
`MUGradedAction W` — the `q_act` source of `Function.Bijective (forwardMapIrr W)` (Zhu Thm 5.3.4). -/
theorem mUGradedAction_of_dj28_collapse (W : VertexOperatorAlgebra 𝒱)
    (hDJ : DJ28IntoFull W) (hcol : ∀ n : ℕ, OnmCollapses W n) :
    MUGradedAction W :=
  MUGradedAction_of_gens W
    (fun n c d v => hcol n (hDJ.circ n c d v))
    (fun n a c d => hcol n (hDJ.crossCirc n a c d))
    (fun n a c => hcol n (hDJ.crossL n a c))

/-! ## The single load-bearing slice (the families the bijection actually consumes). -/

/-- **`NeededSliceMems W`** — the precise residual the faithful bijection actually needs: the three
`MUGradedAction_of_gens` families directly into the **partial** ideal `Onm W n 0` (= DJ `O'_{n,0}`).
This is exactly the `m = 0` slice of the DJ-2.8 closure that the `M(U)` `𝒱`-action consumes, stated
into `Onm` rather than `OnmFull`.  Kept as a hypothesis (NOT an axiom, NOT faked).  Engine status on
the rank-1 free boson (`certificates/mathematica/hinge_rigor2.wl`, basis-grade guarded): the cross-circle
family `crossCirc` (the genuine load-bearing slice — the level-`0` Zhu circle carried up to level `n`)
lands in `Onm W n 0` for every tested `a, c, d` (image grades 5, 6 confirmed in the rank-29 span), as
does the diagonal `circ` family.  This slice is implied by the (engine-supported) blanket collapse but
is all the faithful bijection actually needs. -/
structure NeededSliceMems (W : VertexOperatorAlgebra 𝒱) : Prop where
  /-- `O'_{n,0} *^n_0 𝒱 ⊆ O'_{n,0}` (the diagonal circle family). -/
  circ : ∀ (n : ℕ) (c d v : 𝒱), anmRight W n 0 (anmCirc W n 0 c d) v ∈ Onm W n 0
  /-- `𝒱 *^n_0 (c ∘^0_0 d) ∈ O'_{n,0}` (the cross circle family — the genuine load-bearing slice). -/
  crossCirc : ∀ (n : ℕ) (a c d : 𝒱), anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0
  /-- `𝒱 *^n_0 (L(-1)c + L(0)c) ∈ O'_{n,0}` (the cross grading-generator family). -/
  crossL : ∀ (n : ℕ) (a c : 𝒱), anmRight W n 0 a (anmLgen W 0 0 c) ∈ Onm W n 0

/-- **`MUGradedAction W` from the load-bearing slice alone.**  Consumes `NeededSliceMems` (the three
`M(U)` `𝒱`-action families directly into `Onm W n 0`), then the proven reduction
`MUGradedAction_of_gens` (`ZhuVermaAnArchMU`) assembles the Dong–Jiang `M(U)` graded-action crux
`MUGradedAction W` — the `q_act` source of `Function.Bijective (forwardMapIrr W)` (Zhu Thm 5.3.4).
This is the route that does **not** need the full blanket collapse: it only needs the verified
`O'`-slice, exactly what the faithful bijection consumes. -/
theorem mUGradedAction_of_neededSlice (W : VertexOperatorAlgebra 𝒱)
    (h : NeededSliceMems W) :
    MUGradedAction W :=
  MUGradedAction_of_gens W h.circ h.crossCirc h.crossL

end VOA
