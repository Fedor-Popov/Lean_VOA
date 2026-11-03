/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchVecRegradeResidue
import VOA.Modules.ZhuVermaAnArchVecDirectFZ
import VOA.Modules.ZhuVermaAnArchPhase4Trophy

/-!
# Game One — CAPSTONE: the maximal fragment + the EXACT remaining vector sub-identity.

This file assembles the **maximal axiom-clean fragment** of the Zhu Theorem 5.3.4 endgame after the two
fresh attacks `RegradeResidue` (`ZhuVermaAnArchVecRegradeResidue`) and `DirectFZ`
(`ZhuVermaAnArchVecDirectFZ`).  It does NOT close the single open core unconditionally; instead it

1. **unifies the two attack lenses** on the SAME object `aOutLev0Half` into one statement
   (`aOutLev0Half_twoLens`), pinning the exact open residual where the two lenses meet;
2. states the **precise remaining vector sub-identity** as a clean predicate
   (`ARDVecResidue`, definitionally the open `anmRightDiff`-decomposition) and proves the **triple
   equivalence** `ARDVecResidue ↔ ARDTowerDecomp ↔ AoutUCoreLev0Core`, so a single closure of ANY of
   the three finishes the theorem;
3. **re-exports the conditional main theorem** `Function.Bijective (forwardMap W)` from the single open core
   through the cleanest route, recording that the bijection is a TERM modulo exactly this one identity.

No `sorry`/`admit`/`axiom`/`pbw`/`native_decide`.  All results
`#print axioms = [propext, Classical.choice, Quot.sound]`.

## What the two lenses establish about the SAME object `aOutLev0Half`

The level-`0` half `aOutLev0Half W n K M a c d` — the single genuine residual of the `a`-outer
`c`-outer U-core (`ZhuVermaAnArchAoutUCore`) — admits TWO proven structural descriptions:

* **DirectFZ lens** (`aOutLev0Half_eq_addThree`, `ZhuVermaAnArchAoutLev0Slice`):
    `aOutLev0Half = anmRightDiff + crossDiffComm + aOutLevNHalf`,
  the `a`-outer FZ mode-reassociation, with `crossDiffComm` a PROVEN `c₍s₎a` `MGTowerFam`
  (`crossDiffComm_eq_MGTowerFam`) and `aOutLevNHalf` a PROVEN level-`n` `c`-`PresTowerFam`
  (`aOutLevNHalf_eq_PresTowerFam`).  The ONLY non-tower summand is `anmRightDiff`.

* **Regrade lens** (`aOutLev0Half_regrade`, `ZhuVermaAnArchVecRegradeResidue`):
    `aOutLev0Half = ∑_{p<n+1} (−1)^{n−p} C(n,p) • (∑_{i≤K} C(K,i) • regradeCirc W M n p c (a₍i−(n+1)₎d))`,
  the PROVEN scalar regrade `crossDiff_regrade` lifted to the vector level, expressing
  `aOutLev0Half` as a finite combination of grade-`(M+p)`, pole-`(p−n+2)` `c`-circles over the
  `a`-outer multi-base.

Subtracting the two PROVEN tower summands of the DirectFZ lens isolates the open residual:

  `anmRightDiff = aOutLev0Half − crossDiffComm − aOutLevNHalf`
               = (regrade combination) − (PROVEN `MGTowerFam`) − (PROVEN level-`n` `c`-`PresTowerFam`),

which is `aOutLev0Half_twoLens` below.  Both lenses are PROVEN; their difference is exactly the open
core.

## The EXACT remaining vector sub-identity (engine-verified TRUE; NOT faked / NOT axiomatized)

  `ARDVecResidue W n K M P a c d`  (definitionally `ARDTowerDecomp`):

    `anmRightDiff W n K a c d
       = PresTowerFam W M n c RU ΔU baseU wU                       -- a LEVEL-n grade-M c-tower over a₍g₎d
         + MGTowerFam W n S gradeS leftS baseS ΔS wS`,             -- a c₍s₎a MGTowerFam, NEGATIVE s allowed

  where `anmRightDiff W n K a c d = ∑_{i≤K} C(K,i) • a₍i−(n+1)₎ (anmCirc W 0 0 c d − anmCirc W n 0 c d)`
  (`ZhuVermaAnArchMUcircDiffClose`), the level-`n` outer mode acting on the inner pole-`2`-vs-pole-`(n+2)`
  base-difference.

### The engine-isolated residue identification that still has to be supplied

Both fresh attacks pin the SAME irreducible content (engine ground truth, rank-1 Heisenberg free boson,
`n = 1, 2`, all kernels `Quit`):

* **per-base FAILURE** (`certificates/mathematica/vec_regrade_residue3.wl`, plus the exploratory
  script (not retained) `ard_n1step.wl`): the single-base inner
  pole-difference `(circ₀ − circₙ) c d` (equivalently the regrade lens's lower-`p` rows) is NOT a
  single-base level-`n` `c`-tower over `d` — the `n`-offset is irreducibly cross-base, FAILING already
  at `n = 1`.  So no per-base regrade or per-base FZ rearrangement closes it.

* **FZ-split CIRCULARITY** (exploratory computer-algebra evidence not retained): the FZ commutator piece of the
  `a`-outer split equals EXACTLY `−crossDiffComm` (an `s ≥ 0` `c₍s₎a` `MGTowerFam`), so the FZ split
  alone supplies no new content beyond what `crossDiffComm_eq_MGTowerFam` already proves.

* **NEGATIVE-`s` requirement** (exploratory computer-algebra evidence not retained): the genuine residue requires the
  CREATION products `c₍−1₎a, c₍−2₎a, …` with GRADE-DEPENDENT lower windows (e.g. `a = L₋₂, d = L₋₂`
  fails at `s ≥ −(K+1)`, needs wider) — `aOutLev0Half` IS in `(level-n c-tower over a₍g₎d) +
  (negative-s c₍s₎a MGTowerFam)` but NOT with `s ≥ 0`.

The remaining identification is therefore the **cross-base, negative-`s` Vandermonde derivation**: the
regrade rows `regradeCirc W M n p c (a₍i−(n+1)₎d)` (proven) have to be reorganized across the `a`-outer
multi-base `i` into the negative-`s` `c₍s₎a` `MGTowerFam`, using the proven mode commutator
`mode_commutator_finsum`/`mode_split_gen` to generate `c₍s₎a` from the FZ `a₍α₎c` products AND the proven
scalar regrade `towerCoeffAnm_regrade_int` to absorb the `n`-offset onto grade-`(M+p)` rows, then an
`i`-sum Vandermonde to land the negative-`s` window.  Candidate generator for the negative-`s` products:
skew-symmetry (`Core.SkewSymmetry.skew_mode`, axiom-clean).  This is the actual frontier of Zhu Thm
5.3.4 at level `n`; it is NOT reducible to the existing scalar machinery in closed form within scope.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason, J. Algebra 206 (1998) 67–96; H. Li hep-th/9406211 §2; Gannon §5.3.1–§5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The two-lens isolation — both proven descriptions of `aOutLev0Half`, meeting at the residual. -/

/-- **The TWO-LENS isolation of the open residual** (FULLY proven; homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`).
The level-`0` half `aOutLev0Half` is given by the PROVEN **regrade lens** (`aOutLev0Half_regrade`,
`ZhuVermaAnArchVecRegradeResidue`); subtracting the two PROVEN tower summands of the PROVEN
**DirectFZ lens** (`aOutLev0Half_eq_addThree`, `ZhuVermaAnArchAoutLev0Slice`) — the FZ-commutator
`c₍s₎a` `MGTowerFam` `crossDiffComm` and the level-`n` `c`-`PresTowerFam` `aOutLevNHalf` — isolates the
single open residual `anmRightDiff` as the regrade combination minus the two tower families:

  `anmRightDiff W n K a c d
     = (∑_{p<n+1} (−1)^{n−p} C(n,p) • (∑_{i≤K} C(K,i) • regradeCirc W M n p c (a₍i−(n+1)₎d)))
       − crossDiffComm W n K M a c d
       − aOutLevNHalf W n K M a c d`.

The left side is the genuinely open object; the first term on the right is the PROVEN vector regrade,
and the last two are PROVEN tower families.  This is the exact place where the two attack lenses meet:
the open content is the cross-base reorganization of the regrade rows into the negative-`s` `c₍s₎a`
`MGTowerFam`, NOT supplied by either lens alone (see file docstring). -/
theorem aOutLev0Half_twoLens (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ}
    {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) :
    anmRightDiff W n K a c d
      = (∑ p ∈ Finset.range (n + 1),
          ((-1 : ℂ) ^ (n - p) * (Nat.choose n p : ℂ))
            • ∑ i ∈ Finset.range (K + 1),
                cbz (K : ℤ) (i : ℤ)
                  • regradeCirc W M n p c (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d))
        - crossDiffComm W n K M a c d
        - aOutLevNHalf W n K M a c d := by
  -- regrade lens for the first term; FZ lens gives `aOutLev0Half = aRD + crossDiffComm + aOutLevNHalf`.
  rw [← aOutLev0Half_regrade W n K M a c d, aOutLev0Half_eq_addThree W n ha hc d]
  abel

/-! ## The EXACT remaining vector sub-identity (predicate), and the triple equivalence. -/

/-- **`ARDVecResidue` — the EXACT remaining vector sub-identity** (definitionally `ARDTowerDecomp`).
The single open core after the two fresh attacks: the `a`-outer right-action difference `anmRightDiff`
decomposes as a LEVEL-`n` grade-`M` `c`-`PresTowerFam` over the wide bases `a₍g₎d` plus a `c₍s₎a`
`MGTowerFam` (NEGATIVE `s` allowed — the FULL level-`n` circle-generator span).  Aliased to
`ARDTowerDecomp` (`ZhuVermaAnArchCrossCFirstGate`) so that the proven membership/closure machinery
applies verbatim; the alias names this as the precise standalone open identity isolated by both the
regrade lens (`aOutLev0Half_twoLens`) and the DirectFZ lens. -/
def ARDVecResidue (W : VertexOperatorAlgebra 𝒱) (n K M P : ℕ) (a c d : 𝒱) : Prop :=
  ARDTowerDecomp W n K M P a c d

/-- `ARDVecResidue` is, by definition, `ARDTowerDecomp` (the alias is transparent). -/
theorem ardVecResidue_iff_ardTowerDecomp (W : VertexOperatorAlgebra 𝒱) (n K M P : ℕ) (a c d : 𝒱) :
    ARDVecResidue W n K M P a c d ↔ ARDTowerDecomp W n K M P a c d := Iff.rfl

/-- **The triple equivalence** `ARDVecResidue ↔ ARDTowerDecomp ↔ AoutUCoreLev0Core` (homogeneous
`a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`).  The exact remaining sub-identity, the `a`-outer
right-action-difference tower decomposition, and the level-`0` half cross-base collapse are the SAME
endgame target — closing ANY one of the three (unconditionally) finishes Zhu Thm 5.3.4.  Backward leg
of the second `↔` is the PROVEN `ardTowerDecomp_of_aOutUCoreLev0Core`
(`ZhuVermaAnArchARDTowerDirect`); forward leg unifies the regrade-lens close
(`aoutUCoreLev0Core_of_ARDTowerDecomp_regrade`) and the DirectFZ close
(`AoutUCoreLev0Core_of_ARDTowerDecomp_directFZ`) — both proven, both routed through the same core. -/
theorem ardVecResidue_iff_aOutUCoreLev0Core (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M P : ℕ}
    {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (hc : c ∈ W.grading (M : ℤ))
    {d : 𝒱} (hd : d ∈ W.grading (P : ℤ)) :
    ARDVecResidue W n K M P a c d ↔ AoutUCoreLev0Core W n K M P a c d :=
  ⟨fun h => AoutUCoreLev0Core_of_ARDTowerDecomp_directFZ W n ha hc hd h,
   fun h => ardTowerDecomp_of_aOutUCoreLev0Core W n ha hc hd h⟩

/-! ## The full `MUGradedAction W` from the single open residual (both-lens unified). -/

/-- **The full `MUGradedAction W` from the single universal `ARDVecResidue`** (both-lens unified).
Given, for every level `n` and all homogeneous data, the exact remaining sub-identity `ARDVecResidue`
(= `ARDTowerDecomp`), the DirectFZ close `AoutUCoreLev0Core_of_ARDTowerDecomp_directFZ` supplies the
universal `AoutUCoreLev0Core`, and the PROVEN `MUGradedAction_of_aOutUCoreLev0Core`
(`ZhuVermaAnArchAoutUCore`) assembles the Dong–Jiang `M(U)` graded-action crux `MUGradedAction W` (the
`q_act` source of the bijection).  Unifies with the regrade-lens
(`MUGradedAction_of_ARDTowerDecomp_via_regrade`) and DirectFZ
(`MUGradedAction_of_ARDTowerDecomp_directFZ`) routes — all close on the SAME single core. -/
theorem MUGradedAction_of_ARDVecResidue (W : VertexOperatorAlgebra 𝒱)
    (Hres : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), ARDVecResidue W n K M P a c d) :
    MUGradedAction W :=
  MUGradedAction_of_aOutUCoreLev0Core W
    (fun n K M P a ha c hc d hd =>
      AoutUCoreLev0Core_of_ARDTowerDecomp_directFZ W n ha hc hd (Hres n K M P a ha c hc d hd))

/-! ## The conditional Zhu bijection main theorem from the single open residual. -/

/-- **`zhuBijection_trophy_of_ARDVecResidue` — the conditional main theorem from the single open
residual.**  Given the exact remaining vector sub-identity `ARDVecResidue` (= `ARDTowerDecomp` =
`AoutUCoreLev0Core`) for all levels and homogeneous data, together with the term-level construction
data of `zhuBijection_trophy` (the irreducibility scope `hall` and the carrier/bridge data
`F`/`ludata`/`realizes`/`Dfun`/`G`), the forward map `forwardMap W : Φ(𝒱) → Irr A(𝒱)` is a
**bijection**.  This is the tightest packaging of `zhuBijection_trophy` (`ZhuVermaAnArchPhase4Trophy`)
against the single open identity isolated by BOTH fresh attacks: the regrade lens
(`aOutLev0Half_twoLens`) and the DirectFZ lens converge here.

`Function.Bijective (forwardMap W)` is therefore a TERM **modulo exactly one mathematical hypothesis**,
`ARDVecResidue` — NOT yet an unconditional term.  When a sibling closes `ARDVecResidue` (equivalently
`ARDTowerDecomp` / `AoutUCoreLev0Core`) unconditionally, instantiate it here to obtain the bijection
with no mathematical hypothesis. -/
theorem zhuBijection_trophy_of_ARDVecResidue {W : VertexOperatorAlgebra 𝒱}
    (Hres : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), ARDVecResidue W n K M P a c d)
    (F : VHat.CarrierBridgeDataFamily W)
    (ludata : ∀ U : AMod W,
      MUModuleData.LUData ((F.toCarrierBridgeFamily.toMURepFamily).mudata U))
    (realizes : ∀ U : AMod W,
      AModEquiv W
        (((F.toCarrierBridgeFamily.toMURepFamily).toLUFamily ludata).K U).toAMod U)
    (Dfun : InducedAssignment.MUFunctorialData
      ((F.toCarrierBridgeFamily.toMURepFamily).toLUFamily ludata))
    (hall : InducedAssignment.AllLWIrreducible W)
    (G : InducedAssignment.GenFromBottomGFamily
      ((F.toCarrierBridgeFamily.toMURepFamily).toLUFamily ludata)) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_trophy
    (fun n K M P a ha c hc d hd =>
      AoutUCoreLev0Core_of_ARDTowerDecomp_directFZ W n ha hc hd (Hres n K M P a ha c hc d hd))
    F ludata realizes Dfun hall G

/-! ## Status — CAPSTONE: maximal fragment proved; `Function.Bijective (forwardMap W)` is CONDITIONAL.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`admit`/`axiom`/`pbw`/`native_decide`):

* **`aOutLev0Half_twoLens`** — **the two-lens isolation**: the open residual `anmRightDiff` equals the
  PROVEN vector regrade combination MINUS the two PROVEN tower families (`crossDiffComm` `MGTowerFam`,
  `aOutLevNHalf` `PresTowerFam`).  The exact place where the regrade lens and the DirectFZ lens meet.
* **`ARDVecResidue`** / **`ardVecResidue_iff_ardTowerDecomp`** — the EXACT remaining vector sub-identity
  named as a standalone predicate (transparent alias of `ARDTowerDecomp`).
* **`ardVecResidue_iff_aOutUCoreLev0Core`** — the triple equivalence
  `ARDVecResidue ↔ ARDTowerDecomp ↔ AoutUCoreLev0Core`; closing any one finishes the theorem.
* **`MUGradedAction_of_ARDVecResidue`** — the full `MUGradedAction W` from the single open residual.
* **`zhuBijection_trophy_of_ARDVecResidue`** — the conditional main theorem:
  `Function.Bijective (forwardMap W)` from the single open residual + the term-level carrier data.

**Status.** `Function.Bijective (forwardMap W)` is NOT an unconditional axiom-clean term: it is
a TERM **modulo exactly one mathematical hypothesis**, the single universally-quantified vector
sub-identity

  `ARDVecResidue W n K M P a c d`  (= `ARDTowerDecomp` = `AoutUCoreLev0Core`)
    `:  anmRightDiff = (level-n grade-M c-PresTowerFam over a₍g₎d) + (c₍s₎a MGTowerFam, NEGATIVE s)`.

The two fresh attacks each got to this SAME core: **DirectFZ** got furthest as a self-contained
de-risk (proving the `a`-outer FZ split `aOutUPart = anmRightDiff + crossDiffComm` and showing the FZ
commutator piece is EXACTLY `−crossDiffComm`, so the split is circular and the open content is purely
the negative-`s` `anmRightDiff = ARDTowerDecomp`); **RegradeResidue** proved the genuine VECTOR regrade
`presAnm_lev0_regrade` / `aOutLev0Half_regrade` (the proven scalar `crossDiff_regrade` lifted to the
vector level) and showed the regraded rows are pole-shifted and per-base irreducible.  The
engine-isolated residue identification still needed: the **cross-base, negative-`s` Vandermonde
reorganization** of the proven regrade rows `regradeCirc W M n p c (a₍i−(n+1)₎d)` into the negative-`s`
`c₍s₎a` `MGTowerFam`, generating the creation products `c₍−1₎a, c₍−2₎a, …` (candidate: skew-symmetry
`Core.SkewSymmetry.skew_mode`) and absorbing the `n`-offset by the proven `towerCoeffAnm_regrade_int`,
with a grade-dependent lower window — the genuine frontier of Zhu Thm 5.3.4 at level `n`.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.aOutLev0Half_twoLens
  #print axioms VOA.ardVecResidue_iff_ardTowerDecomp
  #print axioms VOA.ardVecResidue_iff_aOutUCoreLev0Core
  #print axioms VOA.MUGradedAction_of_ARDVecResidue
  #print axioms VOA.zhuBijection_trophy_of_ARDVecResidue
-/
