/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchSkewHardMem
import VOA.Modules.ZhuVermaAnArchCFirstDiffMaster

/-!
# MemCFirst — `HARDmem` through the master-split `crossCFirstDiff`, reduced to the **lone**
level-`0` cross-circle membership.

This file attacks the `HARDmem` main theorem along the cleanest available target, `crossCFirstDiff`
(via `hardmem_iff_crossCFirstDiff_mem`).  The decisive simplification is the PROVEN master bridge
`crossCFirstDiff_eq_anmCircAnmRightDiff` (`ZhuVermaAnArchCFirstDiffMaster`):

  `crossCFirstDiff W n K M a c d
     = anmCirc W 0 0 c (anmRight W n 0 a d) − anmCirc W n 0 c (anmRight W n 0 a d)`,

a clean **two-term circle difference** with NO residual commutator (the `crossDiffComm` cancels —
engine `certificates/mathematica/ccfd_clean.wl`).  Of the two terms:

* the **level-`n`** circle `anmCirc W n 0 c (anmRight W n 0 a d)` is a level-`n` circle GENERATOR,
  hence in `Onm W n 0` for free (`anmCirc_mem_Onm`, here `anmCircN_anmRight_mem`); and
* the **level-`0`** circle `anmCirc W 0 0 c (anmRight W n 0 a d)` is the lone genuinely-open piece
  (the predicate `CircAnmRightOnm` / the report's `crossCirc0_mem_Onm`).

Consequently the ENTIRE `HARDmem` endgame collapses, by **two existing proven lemmas plus
`anmCirc_mem_Onm`**, to exactly ONE membership: the level-`0` cross circle

  `(crossCirc0)   anmCirc W 0 0 c (anmRight W n 0 a d) ∈ Onm W n 0`     (homogeneous `a ∈ 𝒱_K`,
  `c ∈ 𝒱_M`, `d ∈ 𝒱_P`).

This is the cleanest possible exposure of the `HARDmem` content: `crossCFirstDiff ∈ Onm` ⇔
`crossCirc0` (`crossCFirstDiff_mem_iff_crossCirc0`), so `HARDmem` ⇔ `crossCirc0`
(`hardmem_iff_crossCirc0`).  Proving the conditional closure of the main theorem against `crossCirc0`
alone (`hardmem_holds_of_crossCirc0`, `MUGradedAction_of_crossCirc0`,
`zhuBijection_trophy_of_crossCirc0`)
makes `Function.Bijective (forwardMap W)` a TERM modulo this single membership.

## What `crossCirc0` actually is, and why it is NOT a `Submodule.sum_mem`

Engine-verified TRUE (rank-1 Heisenberg free boson, `certificates/mathematica/ard_term1.wl` `SMAX = 12`): the level-`0` cross
circle lies in the span of three PROVEN `Onm`-generator families — F1 (`c`-tower at `a₍g₎d`,
`Pres_mem_Onm`), F2 (the `c₍s₎a`-creation tower at `d`, `csaBlock_mem_Onm`), F3 (the additional lever:
`a`-tower at `c₍g₎d`, `Pres_mem_Onm`).  **However** the realizing coefficients are NON-CONSTRUCTIVE:
a direct exact `LinearSolve` (`certificates/mathematica/memcfirst_solve2.wl`, `n = 1`, `a = L₋₂`, `c = d = J`) produces a
witness with NO recognizable closed form (e.g. denominators `13, 26` — minimum-norm artifacts, not a
binomial/Vandermonde pattern).  So a pure `Submodule.sum_mem` is NOT available: closing `crossCirc0`
genuinely requires the explicit Dong–Jiang Lemma 2.8 cross-base/skew coefficient assignment (the
`coeffSn_eq_coeffPn`-type Vandermonde collapse, `ZhuVermaAnDescent4`, extended with the F3 `a`-tower
column) — the irreducible combinatorial residue.  This file does NOT fake that; it proves the exact
reduction and states `crossCirc0` as the precise residual.

## Proved here (axiom-clean)

* `anmCircN_anmRight_mem` — the level-`n` term `anmCirc W n 0 c (anmRight W n 0 a d) ∈ Onm W n 0`
  (a level-`n` circle generator; `anmCirc_mem_Onm`).
* `crossCFirstDiff_mem_iff_crossCirc0` — `crossCFirstDiff ∈ Onm W n 0 ↔
  anmCirc W 0 0 c (anmRight W n 0 a d) ∈ Onm W n 0`, via the master bridge + the level-`n` term.
* `hardmem_iff_crossCirc0` — `HARDmem W n K M P a c d ↔ anmCirc W 0 0 c (anmRight W n 0 a d) ∈
  Onm W n 0` (chaining `hardmem_iff_crossCFirstDiff_mem`).
* `hardmem_holds_of_crossCirc0` — the universal `crossCirc0` membership ⟹ the universal `HARDmem`.
* `MUGradedAction_of_crossCirc0` — `MUGradedAction W` from the universal `crossCirc0`.
* `zhuBijection_trophy_of_crossCirc0` — the main theorem `Function.Bijective (forwardMap W)` from the
  universal `crossCirc0` plus the term-level carrier/bridge data.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The level-`n` term of the master-split difference is a free circle generator. -/

/-- **The level-`n` circle term lies in `Onm W n 0`** (for free).  `anmCirc W n 0 c w` is a
level-`n` circle generator of `Onm W n 0`, so `anmCirc_mem_Onm` lands it in the ideal — here on
the right action `w := anmRight W n 0 a d`.  No combinatorial content. -/
theorem anmCircN_anmRight_mem (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a c d : 𝒱) :
    anmCirc W n 0 c (anmRight W n 0 a d) ∈ Onm W n 0 :=
  anmCirc_mem_Onm W n 0 c (anmRight W n 0 a d)

/-! ## `crossCFirstDiff ∈ Onm` ⇔ the lone level-`0` cross circle ∈ `Onm`. -/

/-- **`crossCFirstDiff ∈ Onm W n 0 ↔ anmCirc W 0 0 c (anmRight W n 0 a d) ∈ Onm W n 0`**
(homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`).  By the PROVEN master bridge
`crossCFirstDiff_eq_anmCircAnmRightDiff`, `crossCFirstDiff` is the two-term difference
`anmCirc W 0 0 c (a*d) − anmCirc W n 0 c (a*d)`; the level-`n` term is in `Onm W n 0` for free
(`anmCircN_anmRight_mem`), so adding/subtracting it transfers the membership to/from the level-`0`
term.  This isolates the lone open piece. -/
theorem crossCFirstDiff_mem_iff_crossCirc0 (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ}
    {a c : 𝒱} (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) :
    crossCFirstDiff W n K M a c d ∈ Onm W n 0 ↔
      anmCirc W 0 0 c (anmRight W n 0 a d) ∈ Onm W n 0 := by
  rw [crossCFirstDiff_eq_anmCircAnmRightDiff W n ha hc d]
  constructor
  · intro h
    -- `Term1 = (Term1 − TermN) + TermN`; both summands in `Onm`.
    have hsum := Submodule.add_mem _ h (anmCircN_anmRight_mem W n a c d)
    rwa [sub_add_cancel] at hsum
  · intro h
    exact Submodule.sub_mem _ h (anmCircN_anmRight_mem W n a c d)

/-! ## `HARDmem` ⇔ the lone level-`0` cross circle ∈ `Onm`. -/

/-- **`HARDmem W n K M P a c d ↔ anmCirc W 0 0 c (anmRight W n 0 a d) ∈ Onm W n 0`** (homogeneous
`a ∈ 𝒱_K`, `c ∈ 𝒱_M`).  Chains the proven master-split membership equivalence
`hardmem_iff_crossCFirstDiff_mem` (`HARDmem ↔ crossCFirstDiff ∈ Onm`) with the bridge
`crossCFirstDiff_mem_iff_crossCirc0` (`crossCFirstDiff ∈ Onm ↔ crossCirc0 ∈ Onm`).  This is the
TIGHTEST statement of the `HARDmem` content: the whole endgame is exactly the single level-`0` cross
circle membership. -/
theorem hardmem_iff_crossCirc0 (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M P : ℕ}
    {a c d : 𝒱} (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) :
    HARDmem W n K M P a c d ↔ anmCirc W 0 0 c (anmRight W n 0 a d) ∈ Onm W n 0 := by
  rw [hardmem_iff_crossCFirstDiff_mem W n ha hc (P := P) (d := d),
    crossCFirstDiff_mem_iff_crossCirc0 W n ha hc d]

/-! ## The conditional closure of the main theorem against `crossCirc0` alone. -/

/-- **The universal level-`0` cross-circle membership ⟹ the universal `HARDmem`.**  For every level
`n` and homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, the level-`0` cross circle membership
`anmCirc W 0 0 c (anmRight W n 0 a d) ∈ Onm W n 0` is, by `hardmem_iff_crossCirc0`, EXACTLY
`HARDmem W n K M P a c d`.  Re-packaging the universal hypothesis. -/
theorem hardmem_holds_of_crossCirc0 (W : VertexOperatorAlgebra 𝒱)
    (Hcirc : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ),
      anmCirc W 0 0 c (anmRight W n 0 a d) ∈ Onm W n 0) :
    ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), HARDmem W n K M P a c d := by
  intro n K M P a ha c hc d hd
  exact (hardmem_iff_crossCirc0 W n ha hc (P := P) (d := d)).mpr (Hcirc n K M P a ha c hc d hd)

/-- **`MUGradedAction W` from the universal `crossCirc0`.**  The universal level-`0` cross circle
membership supplies the universal `HARDmem` (`hardmem_holds_of_crossCirc0`), which the proven
membership endgame `MUGradedAction_of_HARDmem` (`ZhuVermaAnArchSkewHardMem`) assembles into the
Dong–Jiang `M(U)` graded-action crux `MUGradedAction W`. -/
theorem MUGradedAction_of_crossCirc0 (W : VertexOperatorAlgebra 𝒱)
    (Hcirc : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ),
      anmCirc W 0 0 c (anmRight W n 0 a d) ∈ Onm W n 0) :
    MUGradedAction W :=
  MUGradedAction_of_HARDmem W (hardmem_holds_of_crossCirc0 W Hcirc)

/-- **`zhuBijection_trophy_of_crossCirc0` — the main theorem from the lone level-`0` cross-circle
membership.**  Given the universal `crossCirc0` (the model-TRUE single membership, engine-verified
at `SMAX = 12`) together with the term-level carrier/bridge data of `zhuBijection_phase4`, the
forward map `forwardMap W : Φ(𝒱) → Irr A(𝒱)` is a **bijection**.  Route:
`crossCirc0 → HARDmem → MUGradedAction W` (`MUGradedAction_of_crossCirc0`), then end-to-end through
the proven `genFromBottomFinalFamily_of_G` and the clean headline `clean_route_zhuBijection` — the
identical tail used by `zhuBijection_trophy_of_HARDmem`.  This exposes the main theorem modulo exactly ONE
membership, the level-`0` cross circle. -/
theorem zhuBijection_trophy_of_crossCirc0 {W : VertexOperatorAlgebra 𝒱}
    (Hcirc : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ),
      anmCirc W 0 0 c (anmRight W n 0 a d) ∈ Onm W n 0)
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
  let hgraded : MUGradedAction W := MUGradedAction_of_crossCirc0 W Hcirc
  Stage7Audit.clean_route_zhuBijection F ludata realizes Dfun hall
    (InducedAssignment.genFromBottomFinalFamily_of_G _ hgraded G)

/-! ## Status — `HARDmem` reduced (by two PROVEN lemmas + `anmCirc_mem_Onm`) to ONE membership.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`admit`/`axiom`/`pbw`/`native_decide`):

* **`anmCircN_anmRight_mem`** — the level-`n` term is a free circle generator in `Onm W n 0`.
* **`crossCFirstDiff_mem_iff_crossCirc0`** — `crossCFirstDiff ∈ Onm ↔ crossCirc0 ∈ Onm`, via the
  master bridge `crossCFirstDiff_eq_anmCircAnmRightDiff` + the level-`n` term.
* **`hardmem_iff_crossCirc0`** — `HARDmem ↔ crossCirc0 ∈ Onm`, chaining
  `hardmem_iff_crossCFirstDiff_mem`.
* **`hardmem_holds_of_crossCirc0`** / **`MUGradedAction_of_crossCirc0`** /
  **`zhuBijection_trophy_of_crossCirc0`** — the conditional closure of the full endgame (universal
  `HARDmem`, `MUGradedAction W`, and `Function.Bijective (forwardMap W)`) against the universal
  `crossCirc0` alone.

**Status.** `hardmem_holds` is NOT an unconditional axiom-clean term.  It is a TERM modulo
exactly ONE membership — the level-`0` cross circle

  `(crossCirc0)   anmCirc W 0 0 c (anmRight W n 0 a d) ∈ Onm W n 0`

for all `n` and homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P` (the in-repo predicate
`CircAnmRightOnm`, the report's `crossCirc0_mem_Onm`).  The `MemCFirst` route discharges everything
ELSE: the master bridge kills the residual commutator and the level-`n` term, leaving this single
level-`0` circle.  The membership is engine-TRUE (`certificates/mathematica/ard_term1.wl`, `SMAX = 12`, in span of the
PROVEN F1/F2/F3 generator families) but is NOT a pure `Submodule.sum_mem`: the realizing
coefficients are non-constructive (`certificates/mathematica/memcfirst_solve2.wl` — no closed form), so closing it genuinely
needs the explicit Dong–Jiang Lemma 2.8 cross-base/skew Vandermonde coefficient assignment (the
`coeffSn_eq_coeffPn`-type collapse extended by the F3 `a`-tower column), the irreducible
combinatorial residue.  NOT faked.

Precise residual Lean signature (the genuine open content):

  `theorem crossCirc0_mem_Onm (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M P : ℕ} {a c d : 𝒱}`
  `    (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) (hd : d ∈ W.grading (P : ℤ)) :`
  `    anmCirc W 0 0 c (anmRight W n 0 a d) ∈ Onm W n 0`
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.anmCircN_anmRight_mem
  #print axioms VOA.crossCFirstDiff_mem_iff_crossCirc0
  #print axioms VOA.hardmem_iff_crossCirc0
  #print axioms VOA.hardmem_holds_of_crossCirc0
  #print axioms VOA.MUGradedAction_of_crossCirc0
  #print axioms VOA.zhuBijection_trophy_of_crossCirc0
-/
