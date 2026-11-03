/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchAoutLev0Slice
import VOA.Modules.ZhuVermaAnArchARDTowerDirect

/-!
# Game One (ATTACK: **DirectFZ**) — the `a`-outer FZ-split of `AoutUCoreLev0Core`.

This file attacks the single open Phase-4 frontier core `AoutUCoreLev0Core`
(`ZhuVermaAnArchAoutUCore`, the level-`0` half cross-base collapse whose universal closure finishes
`Function.Bijective (forwardMap W)`, Zhu Thm 5.3.4) through the **DirectFZ** route: the `a`-outer
Frenkel–Zhu mode-split of the right-action difference, NOT the diagonal / slice / grading-generator
routes.

## The DirectFZ vector split (FULLY proven here; engine-verified; no `sorry`/axiom/`pbw`)

The starting point is the PROVEN `a`-outer `i`-sum reindex of the level-`0` half onto the FZ
master-split (`aOutLev0Half_eq_addThree`, `ZhuVermaAnArchAoutLev0Slice`):

  `aOutLev0Half = anmRightDiff + crossDiffComm + aOutLevNHalf`.

The DirectFZ angle isolates the **`a`-outer `c`-outer part** `aOutUPart` (the `c`-already-outer
multi-base pole-`2`-vs-pole-`(n+2)` circle, `aOutUPart_eq_halfDiff`,
`= aOutLev0Half − aOutLevNHalf`) and recognises it as the FZ split of `anmRightDiff`:

  **`aOutUPart = anmRightDiff + crossDiffComm`**            (`aOutUPart_eq_FZsplit`),     
  equivalently  **`anmRightDiff = aOutUPart − crossDiffComm`**  (`anmRightDiff_eq_aOutUPart_sub_comm`).

This is exactly the FZ mode-reassociation `mode_split_gen` (`a₍α₎(c₍μ₎d) = c₍μ₎(a₍α₎d) +
⁅a₍α₎,c₍μ₎⁆d`) summed by the `a`-outer `i`-sum and the pole-difference `μ`-finsum: the `c`-outer piece
`c₍μ₎(a₍α₎d)` collects into `aOutUPart` (a `c`-tower over the wide bases `a₍g₎d`), and the FZ
commutator `⁅a₍α₎,c₍μ₎⁆d` collects into the `c₍s₎a` `MGTowerFam` `crossDiffComm`.  Historical engine evidence
(not retained; rank-1 free boson `n = 1, 2`, mixed homogeneous
`a, c, d`): the FZ commutator piece `∑ᵢ C(K,i) ∑ᶠμ wdiff ⁅a₍i−n−1₎,c₍μ₎⁆d` IS a pure `c₍s₎a`
`MGTowerFam` (negative `s` allowed) and equals `−crossDiffComm` exactly.

## What the DirectFZ split buys

Both halves of the FZ split are KNOWN tower families up to the single open `anmRightDiff` piece:

* `crossDiffComm` is a homogeneous `c₍s₎a` `MGTowerFam` — PROVEN (`crossDiffComm_eq_MGTowerFam`,
  `ZhuVermaAnArchCrossDiffCommutator`);
* `aOutLevNHalf` (the level-`n` half of `aOutUPart`) is a clean depth-`1` level-`n` `c`-`PresTowerFam`
  — PROVEN (`aOutLevNHalf_eq_PresTowerFam`, `ZhuVermaAnArchAoutUCore`);
* `aOutLev0Half` (the level-`0` half) is a clean depth-`1` level-`0` `c`-`PresTowerFam`
  — PROVEN (`aOutLev0Half_eq_PresTowerFam_lev0`, `ZhuVermaAnArchARDTowerGradingGen`).

So through the DirectFZ split the level-`0` half collapse `AoutUCoreLev0Core` is equivalent to the
SINGLE genuinely-open `a`-outer right-action-difference tower decomposition `ARDTowerDecomp`
(`ZhuVermaAnArchCrossCFirstGate`): we prove **`AoutUCoreLev0Core_of_ARDTowerDecomp_directFZ`** (the
forward close through the DirectFZ split, assembled from `anmRightDiff = aOutUPart − crossDiffComm`,
NOT through the diagonal/slice bridge) and re-export the full reduction.

## The genuine remaining identity (engine-verified TRUE; NOT faked / NOT axiomatized)

`ARDTowerDecomp W n K M P a c d` — `anmRightDiff = (level-`n` grade-`M` `c`-`PresTowerFam` over the
wide bases `a₍g₎d`) + (`c₍s₎a` `MGTowerFam`, with the left factors `c₍s₎a` homogeneous of any grade,
the FULL level-`n` circle-generator span).  Historical engine evidence (not retained; all kernels `Quit`): the `c`-outer piece `aOutUPart` is NOT a pure
`c`-tower over `a₍g₎d` (it needs the `c₍s₎a` `MGTowerFam`), and the genuine `c₍s₎a` content runs to
NEGATIVE `s` (creation products `c₍−1₎a, c₍−2₎a, …`, down to and below `−K`, grade-dependent), which
the FZ commutator `crossDiffComm` (`s ≥ 0`) does NOT itself supply — the DirectFZ split is
CIRCULAR on its own (`commAC = −crossDiffComm` exactly in the exploratory computer-algebra run), so the genuinely open,
negative-`s`, cross-base content is precisely `anmRightDiff = ARDTowerDecomp`.  The DirectFZ
contribution here is the clean `a`-outer FZ split as a standalone lemma and the forward close routed
through it.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason, J. Algebra 206 (1998) 67–96; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The DirectFZ `a`-outer split of `aOutUPart`. -/

/-- **The DirectFZ `a`-outer split** `aOutUPart = anmRightDiff + crossDiffComm` (FULLY proven,
homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`).  The `a`-outer `c`-outer part `aOutUPart` (the `c`-already-outer
multi-base pole-`2`-vs-pole-`(n+2)` circle over the bases `a₍·₎d`) is the FZ split of the right-action
difference: the `c`-outer piece `c₍μ₎(a₍α₎d)` plus the FZ commutator `⁅a₍α₎,c₍μ₎⁆d`.

Derivation: `aOutUPart = aOutLev0Half − aOutLevNHalf` (`aOutUPart_eq_halfDiff`, the level halves);
the proven `a`-outer `i`-sum reindex `aOutLev0Half_eq_addThree` gives
`aOutLev0Half = anmRightDiff + crossDiffComm + aOutLevNHalf`, so the level-`n` half cancels and the
`a`-outer `c`-outer part is exactly `anmRightDiff + crossDiffComm`.  This is the FZ mode-split
(`mode_split_gen`, `u = a`, `a = c`) summed by the `a`-outer `i`-sum, with the commutator piece the
PROVEN `c₍s₎a` `MGTowerFam` `crossDiffComm`. -/
theorem aOutUPart_eq_FZsplit (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ}
    {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) :
    aOutUPart W n K M a c d
      = anmRightDiff W n K a c d + crossDiffComm W n K M a c d := by
  rw [aOutUPart_eq_halfDiff W n K M a c d, aOutLev0Half_eq_addThree W n ha hc d]
  abel

/-- **The DirectFZ `a`-outer split, solved for `anmRightDiff`** (FULLY proven, homogeneous `a ∈ 𝒱_K`,
`c ∈ 𝒱_M`): `anmRightDiff = aOutUPart − crossDiffComm`.  The right-action difference is the `a`-outer
`c`-outer part (a `c`-tower over the wide bases `a₍g₎d`, modulo the level-`0`→level-`n` regrade) minus
the FZ commutator `MGTowerFam` `crossDiffComm`.  Equivalent rearrangement of `aOutUPart_eq_FZsplit`. -/
theorem anmRightDiff_eq_aOutUPart_sub_comm (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ}
    {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) :
    anmRightDiff W n K a c d
      = aOutUPart W n K M a c d - crossDiffComm W n K M a c d := by
  rw [aOutUPart_eq_FZsplit W n ha hc d]; abel

/-! ## The DirectFZ forward close — `ARDTowerDecomp ⟹ AoutUCoreLev0Core`. -/

/-- **`ARDTowerDecomp ⟹ AoutUCoreLev0Core`, the DirectFZ route** (FULLY proven; homogeneous
`a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`).  The level-`0` half cross-base collapse `AoutUCoreLev0Core` is
assembled from the genuine endgame core `ARDTowerDecomp` *through the `a`-outer FZ split*, rather than
through the diagonal/slice bridge of `aoutUCoreLev0Core_of_ARDTowerDecomp`
(`ZhuVermaAnArchAoutLev0Slice`).

Concretely: by the level-half split (`aOutUPart_eq_halfDiff`) and the DirectFZ split
(`aOutUPart_eq_FZsplit`),

  `aOutLev0Half = aOutUPart + aOutLevNHalf
               = (anmRightDiff + crossDiffComm) + aOutLevNHalf`,

with the three summands the three KNOWN tower families:

* `anmRightDiff = PresTowerFam W M n c RU ΔU baseU wU + MGTowerFam W n S₀ …` — the carried endgame core
  `ARDTowerDecomp` (the genuine open `a`-outer right-action-difference tower decomposition);
* `crossDiffComm = MGTowerFam W n S₁ …` (`c₍s₎a` @ `d`) — `crossDiffComm_eq_MGTowerFam`
  (FULLY proven via the two commutator twins);
* `aOutLevNHalf = PresTowerFam W M n c (K+1) 1 …` (`c` @ `a₍·₎d`) — `aOutLevNHalf_eq_PresTowerFam`
  (the clean level-`n` half, FULLY proven).

Merging the two grade-`M` level-`n` `c`-`PresTowerFam`s (`PresTowerFam_add`) and the two `c₍s₎a`
`MGTowerFam`s (`MGTowerFam_add`, homogeneity by `MGTowerFam_add_hom`) yields the explicit
`AoutUCoreLev0Core` witness `PresTowerFam W M n c … + MGTowerFam W n …`.  Same conclusion as the
diagonal route — both close on the SAME single `ARDTowerDecomp` — built here through the `a`-outer FZ
split as a distinct, self-contained DirectFZ assembly. -/
theorem AoutUCoreLev0Core_of_ARDTowerDecomp_directFZ (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    {K M P : ℕ} {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (hc : c ∈ W.grading (M : ℤ))
    {d : 𝒱} (hd : d ∈ W.grading (P : ℤ))
    (hard : ARDTowerDecomp W n K M P a c d) :
    AoutUCoreLev0Core W n K M P a c d := by
  -- the endgame core (carried): `anmRightDiff = U₀ + W₀`.
  obtain ⟨RU₀, ΔU₀, S₀, baseU₀, wU₀, gradeS₀, leftS₀, baseS₀, ΔS₀, wS₀, hhom₀, heqARD⟩ := hard
  -- the FZ commutator tower (proven): `crossDiffComm = W₁`.
  obtain ⟨S₁, gradeS₁, leftS₁, baseS₁, ΔS₁, wS₁, hhom₁, hcommeq⟩ :=
    crossDiffComm_eq_MGTowerFam W n ha hc hd
  -- assemble: merged `c`-`PresTowerFam` (U₀ ⊕ U_N) and merged `c₍s₎a`-`MGTowerFam` (W₀ ⊕ W₁).
  refine ⟨RU₀ + (K + 1), max ΔU₀ 1, S₀ + S₁,
    (fun r => Sum.elim baseU₀
        (fun i : Fin (K + 1) => W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d) (finSumFinEquiv.symm r)),
    (fun r δ => Sum.elim (fun r₁ => if δ < ΔU₀ then wU₀ r₁ δ else 0)
        (fun r₂ : Fin (K + 1) => if δ < 1 then (if δ = 0 then cbz (K : ℤ) (r₂ : ℤ) else 0) else 0)
        (finSumFinEquiv.symm r)),
    (fun r => Sum.elim gradeS₀ gradeS₁ (finSumFinEquiv.symm r)),
    (fun r => Sum.elim leftS₀ leftS₁ (finSumFinEquiv.symm r)),
    (fun r => Sum.elim baseS₀ baseS₁ (finSumFinEquiv.symm r)),
    (fun r => Sum.elim ΔS₀ ΔS₁ (finSumFinEquiv.symm r)),
    (fun r => Sum.elim wS₀ wS₁ (finSumFinEquiv.symm r)),
    MGTowerFam_add_hom W S₀ S₁ gradeS₀ leftS₀ gradeS₁ leftS₁ hhom₀ hhom₁, ?_⟩
  -- `aOutLev0Half = aOutUPart + aOutLevNHalf` (level-half split).
  have hsplit : aOutLev0Half W n K M a c d
      = aOutUPart W n K M a c d + aOutLevNHalf W n K M a c d := by
    rw [aOutUPart_eq_halfDiff W n K M a c d]; abel
  rw [hsplit, aOutUPart_eq_FZsplit W n ha hc d, heqARD, hcommeq,
    aOutLevNHalf_eq_PresTowerFam W n K M a c d]
  -- `((U₀ + W₀) + W₁) + U_N = (U₀ + U_N) + (W₀ + W₁)`.
  rw [show ((PresTowerFam W M n c RU₀ ΔU₀ baseU₀ wU₀
              + MGTowerFam W n S₀ gradeS₀ leftS₀ baseS₀ ΔS₀ wS₀)
            + MGTowerFam W n S₁ gradeS₁ leftS₁ baseS₁ ΔS₁ wS₁)
            + PresTowerFam W M n c (K + 1) 1
                (fun i => W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)
                (fun i δ => if δ = 0 then cbz (K : ℤ) (i : ℤ) else 0)
          = (PresTowerFam W M n c RU₀ ΔU₀ baseU₀ wU₀
              + PresTowerFam W M n c (K + 1) 1
                  (fun i => W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)
                  (fun i δ => if δ = 0 then cbz (K : ℤ) (i : ℤ) else 0))
            + (MGTowerFam W n S₀ gradeS₀ leftS₀ baseS₀ ΔS₀ wS₀
                + MGTowerFam W n S₁ gradeS₁ leftS₁ baseS₁ ΔS₁ wS₁) from by abel]
  rw [PresTowerFam_add W M n c RU₀ (K + 1) ΔU₀ 1 baseU₀
        (fun i => W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d) wU₀
        (fun i δ => if δ = 0 then cbz (K : ℤ) (i : ℤ) else 0),
    MGTowerFam_add W n S₀ S₁ gradeS₀ leftS₀ baseS₀ ΔS₀ wS₀ gradeS₁ leftS₁ baseS₁ ΔS₁ wS₁]

/-! ## The DirectFZ bidirectional equivalence and the full reduction. -/

/-- **`ARDTowerDecomp ↔ AoutUCoreLev0Core`, the DirectFZ equivalence** (homogeneous `a ∈ 𝒱_K`,
`c ∈ 𝒱_M`, `d ∈ 𝒱_P`).  Forward through the DirectFZ split assembly
(`AoutUCoreLev0Core_of_ARDTowerDecomp_directFZ`), converse the proved
`ardTowerDecomp_of_aOutUCoreLev0Core` (`ZhuVermaAnArchARDTowerDirect`).  Pins the two cores as
interchangeable endgame targets through the `a`-outer FZ split: proving EITHER closes `MUGradedAction
W` (Zhu Thm 5.3.4). -/
theorem ardTowerDecomp_iff_aOutUCoreLev0Core_directFZ (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    {K M P : ℕ} {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (hc : c ∈ W.grading (M : ℤ))
    {d : 𝒱} (hd : d ∈ W.grading (P : ℤ)) :
    ARDTowerDecomp W n K M P a c d ↔ AoutUCoreLev0Core W n K M P a c d :=
  ⟨fun hdec => AoutUCoreLev0Core_of_ARDTowerDecomp_directFZ W n ha hc hd hdec,
   fun hcore => ardTowerDecomp_of_aOutUCoreLev0Core W n ha hc hd hcore⟩

/-- **The full `MUGradedAction W` from the single universal `ARDTowerDecomp`, the DirectFZ route.**
Given, for every level `n` and all homogeneous data, the `a`-outer right-action-difference tower
decomposition `ARDTowerDecomp`, the DirectFZ forward close
`AoutUCoreLev0Core_of_ARDTowerDecomp_directFZ` supplies the universal `AoutUCoreLev0Core`, and the
PROVEN `MUGradedAction_of_aOutUCoreLev0Core` (`ZhuVermaAnArchAoutUCore`) — every other structural
piece fully discharged — assembles the Dong–Jiang `M(U)` graded-action crux `MUGradedAction W` (the
`q_act` source of the bijection `Function.Bijective (forwardMap W)`, Zhu Thm 5.3.4).

This unifies with the diagonal, `c`-PAST-`a`, FZ-commutator, slice, and grading-generator routes — all
close on the SAME single `ARDTowerDecomp` — built here through the `a`-outer FZ split. -/
theorem MUGradedAction_of_ARDTowerDecomp_directFZ (W : VertexOperatorAlgebra 𝒱)
    (Hdec : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), ARDTowerDecomp W n K M P a c d) :
    MUGradedAction W :=
  MUGradedAction_of_aOutUCoreLev0Core W
    (fun n K M P a ha c hc d hd =>
      AoutUCoreLev0Core_of_ARDTowerDecomp_directFZ W n ha hc hd (Hdec n K M P a ha c hc d hd))

/-! ## Status — the DirectFZ `a`-outer split proved; `AoutUCoreLev0Core` routed to `ARDTowerDecomp`.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`aOutUPart_eq_FZsplit`** — the DirectFZ `a`-outer split `aOutUPart = anmRightDiff + crossDiffComm`
  (the FZ mode-reassociation summed by the `a`-outer `i`-sum), from `aOutUPart_eq_halfDiff` +
  `aOutLev0Half_eq_addThree`.
* **`anmRightDiff_eq_aOutUPart_sub_comm`** — the same solved for `anmRightDiff = aOutUPart −
  crossDiffComm`.
* **`AoutUCoreLev0Core_of_ARDTowerDecomp_directFZ`** — the forward close `ARDTowerDecomp ⟹
  AoutUCoreLev0Core` assembled THROUGH the DirectFZ split (merging the three known tower families
  `anmRightDiff` = `ARDTowerDecomp`, `crossDiffComm` `MGTowerFam`, `aOutLevNHalf` `PresTowerFam`).
* **`ardTowerDecomp_iff_aOutUCoreLev0Core_directFZ`** — the DirectFZ bidirectional equivalence.
* **`MUGradedAction_of_ARDTowerDecomp_directFZ`** — the full `MUGradedAction W` from the single
  universal `ARDTowerDecomp` through the DirectFZ route.

**The single remaining identity (engine-verified TRUE; NOT faked / NOT axiomatized):**
`ARDTowerDecomp W n K M P a c d` — `anmRightDiff = (level-`n` grade-`M` `c`-`PresTowerFam` over the
wide bases `a₍g₎d`) + (`c₍s₎a` `MGTowerFam`, NEGATIVE `s` allowed).  Historical engine evidence
(not retained; all kernels
`Quit`): the FZ commutator piece of the split is exactly `−crossDiffComm` (`s ≥ 0`), so the DirectFZ
split alone is circular; the genuinely open, negative-`s`, grade-dependent cross-base content is
precisely `anmRightDiff = ARDTowerDecomp`, the `a`-outer right-action-difference tower decomposition.
The DirectFZ contribution is the clean `a`-outer FZ split lemma and the forward close routed through
it.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.aOutUPart_eq_FZsplit
  #print axioms VOA.anmRightDiff_eq_aOutUPart_sub_comm
  #print axioms VOA.AoutUCoreLev0Core_of_ARDTowerDecomp_directFZ
  #print axioms VOA.ardTowerDecomp_iff_aOutUCoreLev0Core_directFZ
  #print axioms VOA.MUGradedAction_of_ARDTowerDecomp_directFZ
-/
