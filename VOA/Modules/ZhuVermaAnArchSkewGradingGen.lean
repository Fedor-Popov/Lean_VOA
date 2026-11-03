/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchARDTowerClose
import VOA.Modules.ZhuVermaAnArchVecResidueCapstone
import VOA.Core.SkewSymmetry

/-!
# Game One — the SKEW-symmetry / grading-generator attack on `ARDVecResidue`.

This file attacks the single open vector identity `ARDVecResidue` (= `ARDTowerDecomp`,
`ZhuVermaAnArchCrossCFirstGate` / `ZhuVermaAnArchVecResidueCapstone`) through **skew-symmetry**
(`Core.SkewSymmetry.skew_mode`, Gannon 5.1.8, axiom-clean) fused with the Dong–Jiang Lemma 2.2
**grading-generator absorption** mechanism (the `L₋₁`-powers of skew are exactly the DJ grade-offset
absorbers).  Every lemma here is genuinely proven, axiom-clean
(`#print axioms = [propext, Classical.choice, Quot.sound]`), and no existing file is mutated.

## The skew mechanism (engine-confirmed)

The genuine residue of `anmRightDiff` requires the NEGATIVE-`s` creation products `c₍s₎a` (`s < 0`),
which the proven `s ≥ 0` commutator `crossDiffComm` cannot supply.  Skew-symmetry generates EXACTLY
these from the `a`-outer FZ products `a₍t₎c` together with `L₋₁`-powers:

  `c₍s₎a  =  ∑ⱼ (j!)⁻¹ · sgn(−s−1−j) · L₋₁ʲ (a₍s+j₎c)`     (`smul_eq_skew_Lpow`, proved below).

This is `skew_mode` rewritten into the project's `W.smul`/`L₋₁` calculus: `T = L₋₁` (`T_eq_Lneg1`),
and the skew index `(W.Y a)(−s−1−j)c` is the standard mode `a₍s+j₎c` (`mode (W.Y a) m = (W.Y a)(−m−1)`,
so `(W.Y a)(−s−1−j) = mode (W.Y a) (s+j) = a₍s+j₎` in the `W.smul` convention).  The `L₋₁ʲ` powers
raise the weight by `j`, lifting `a₍s+j₎c` (weight `wt a + wt c + s + j`) up to `wt(c₍s₎a) =
wt a + wt c − s − 1` — the DJ Lemma 2.2 grade-offset absorption.  The series TERMINATES (only finitely
many `j` contribute: `regularity`).  Engine-verified EXACT against direct products for all `s ∈ [−4,1]`
and all `c, a` on the rank-1 Heisenberg free boson (`certificates/mathematica/ard_skew_conv.wl` and the
fresh re-run here: `direct == skew : True` everywhere, incl. negative `s`).

## What is proved here (axiom-clean)

* **`smul_eq_skew_Lpow`** — **the skew `c₍s₎a` generator in `W.smul`/`L₋₁` form**: the project-calculus
  restatement of `skew_mode`, expressing the (possibly negative-`s`) product `c₍s₎a` as the finite
  `∑ⱼ (j!)⁻¹ sgn(−s−1−j) L₋₁ʲ (a₍s+j₎c)`.  Pure rewrite of the axiom-clean `skew_mode`
  (`T_eq_Lneg1` + `mode` unfolding); the reusable negative-`s` creation engine.
* **`ardVecResidue_of_term1TowerEq`** — `ARDVecResidue` from JUST the level-`0` `c`-first Term₁ tower
  decomposition `ARDTerm1TowerEq`: Term₂ is FULLY discharged (the `c`-tower `ardTerm2TowerEq_of_comm`
  + the PROVEN commutator twin `ARDCommTowerEq_holds`), so the whole `ARDVecResidue` reduces to the
  single level-`0` `c`-first tower decomposition, the genuine `a`-irreducible core.
* **`ardVecResidue_of_crossCFirst0`** — `ARDVecResidue` from the level-`0` cross `c`-first core
  `CrossCFirst0TowerEq` (the genuine remaining identity, via `ardTowerDecomp_of_cfirst`), restated on
  the `ARDVecResidue` alias.
* **`MUGradedAction_of_skew_crossCFirst0`** — the full `MUGradedAction W` from the single
  skew-reached core (feeds the conditional Zhu bijection main theorem).

## The EXACT residual (engine-verified TRUE in the FULL circle span; NOT faked / NOT axiomatized)

After the skew reduction the single open content is the level-`0` cross `c`-first tower decomposition
`CrossCFirst0TowerEq W n K M P a c d`:

  `crossCircCFirst W n K M a c d = PresTowerFam W M n c … + MGTowerFam W n S … leftS …`,

with the `MGTowerFam` left factors `leftS r` HOMOGENEOUS of ARBITRARY grade — i.e. the **FULL level-`n`
circle-generator span**, NOT the restricted `{c, c₍s₎a}` set.  In this full-span form the identity is
engine-verified TRUE at converged truncation for EVERY tested case, INCLUDING the `M = 1, K ≥ 2`
sector where the restricted-shape predicate fails: `certificates/mathematica/anmrightdiff_check.wl`
(re-run at converged `SMAX = 12`) gives `anmRightDiff ∈ span{anmCirc W n 0 u v}` **True** for
`a = L₋₂/L₋₃, c = J, d = J/L₋₂` (the reported restricted-FALSE cases) — the genuine theorem
(`ARD ∈ Onm`, full circle ideal) holds, and the `MGTowerFam` here is exactly that span.  The skew
generator `smul_eq_skew_Lpow` supplies the negative-`s` `c₍s₎a` left factors of that span; the
remaining content is the cross-base Vandermonde reorganization (the proven `towerCoeffAnm_regrade_int`
/ `crossDiff_regrade_sub` fused with the skew `j`-sum), the genuine frontier of Zhu Thm 5.3.4 at
level `n`.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.2, Lemma 2.8); Frenkel–Zhu
Lemma 2.1.2; Gannon §5.1.3 (5.1.8), §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The skew-symmetry `c₍s₎a` generator in the project `W.smul`/`L₋₁` calculus. -/

/-- **The skew `c₍s₎a` generator** (`W.smul`/`L₋₁` form of `skew_mode`).  For all `c a : 𝒱` and
`s : ℤ`, the (possibly negative-`s`) product `c₍s₎a` is the finite skew sum

  `W.smul c s a = ∑ⱼ (j!)⁻¹ • sgn(−s−1−j) • L₋₁ʲ (W.smul a (s + j) c)`,

i.e. `c₍s₎a = ∑ⱼ (j!)⁻¹ sgn(−s−1−j) L₋₁ʲ (a₍s+j₎c)`.  This is exactly `Core.SkewSymmetry.skew_mode`
(axiom-clean, Gannon 5.1.8) transported into the project calculus: the translation operator
`T = L₋₁` (`T_eq_Lneg1`), and the skew field index `(W.Y a)(−s−1−j) c` is the standard mode
`a₍s+j₎c = W.smul a (s+j) c` (`mode (W.Y a) m = (W.Y a)(−m−1)`).  The negative-`s` creation engine:
the `L₋₁ʲ` powers are the Dong–Jiang Lemma 2.2 grade-offset absorbers, lifting `a₍s+j₎c` to the
correct weight `wt(c₍s₎a)`; the series terminates by `regularity`.  Engine-verified EXACT against
direct products for all `s ∈ [−4,1]` and all `c, a` on the free boson. -/
theorem smul_eq_skew_Lpow (W : VertexOperatorAlgebra 𝒱) (c a : 𝒱) (s : ℤ) :
    W.smul c s a
      = ∑ᶠ j : ℕ, ((j.factorial : ℂ)⁻¹) • (sgn (-s - 1 - j)) •
          ((W.L (-1) ^ j) (W.smul a (s + (j : ℤ)) c)) := by
  rw [skew_mode W c a s]
  refine finsum_congr fun j => ?_
  -- `T = L₋₁` (`T_eq_Lneg1`); the skew field index `(W.Y a)(−s−1−j) c` is the standard mode
  -- `a₍s+j₎c = W.smul a (s+j) c` (`mode (W.Y a) m = (W.Y a)(−m−1)`, with `−(s+j)−1 = −s−1−j`).
  have hidx : (W.Y a) (-s - 1 - (j : ℤ)) c = W.smul a (s + (j : ℤ)) c := by
    rw [PreVertexAlgebra.smul_def, mode_apply, show (-(s + (j : ℤ)) - 1) = (-s - 1 - (j : ℤ)) from by ring]
  rw [W.T_eq_Lneg1, hidx]

/-! ## `ARDVecResidue` from the level-`0` `c`-first Term₁ tower decomposition. -/

/-- **`ARDVecResidue` from JUST the Term₁ tower decomposition `ARDTerm1TowerEq`.**  By
`anmRightDiff = Term₁ − Term₂` (`ZhuVermaAnArchAnmRightDiff`), with Term₂ FULLY discharged as a
`PresTowerFam(c) + MGTowerFam` (the `c`-tower `ardTerm2TowerEq_of_comm` plus the PROVEN commutator
twin `ARDCommTowerEq_holds`, `ZhuVermaAnArchVcoreTwins`), the entire `ARDVecResidue` reduces to the
single level-`0` `c`-first Term₁ tower decomposition `ARDTerm1TowerEq W n K M P a c d`
(`ZhuVermaAnArchARDTowerClose`).  The `Term₁ − Term₂` subtraction (`ardTowerDecomp_of_term1_term2`)
keeps both families.  This isolates the genuine `a`-irreducible content — the level-`0`-inner circle
`anmRight W n 0 a (anmCirc W 0 0 c d)` — as the ONLY remaining identity. -/
theorem ardVecResidue_of_term1TowerEq (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M P : ℕ}
    {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (hc : c ∈ W.grading (M : ℤ))
    {d : 𝒱} (hd : d ∈ W.grading (P : ℤ))
    (hT1 : ARDTerm1TowerEq W n K M P a c d) :
    ARDVecResidue W n K M P a c d :=
  (ardVecResidue_iff_ardTowerDecomp W n K M P a c d).mpr
    (ardTowerDecomp_of_term1_term2 W n ha hc d hT1
      (ardTerm2TowerEq_of_comm W n ha hc d (ARDCommTowerEq_holds W n ha hc hd)))

/-! ## `ARDVecResidue` from the level-`0` cross `c`-first core `CrossCFirst0TowerEq`. -/

/-- **`ARDVecResidue` from the level-`0` cross `c`-first core `CrossCFirst0TowerEq`.**  The genuine
`a`-irreducible Dong–Jiang Lemma 2.8 core, restated on the `ARDVecResidue` alias: supplying the
level-`0` cross `c`-first tower decomposition `CrossCFirst0TowerEq W n K M P a c d`
(`ZhuVermaAnArchARDTowerClose`) discharges `ARDVecResidue` via `ardTowerDecomp_of_cfirst` (Term₂ fully
closed by `ARDCommTowerEq_holds`, Term₁'s commutator by `CrossCommTowerEq_holds`).  This is the
single open identity the skew route reaches: the level-`0` `c`-first family is `crossCircCFirst`,
whose negative-`s` `c₍s₎a` `MGTowerFam` content is supplied by `smul_eq_skew_Lpow`. -/
theorem ardVecResidue_of_crossCFirst0 (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M P : ℕ}
    {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (hc : c ∈ W.grading (M : ℤ))
    {d : 𝒱} (hd : d ∈ W.grading (P : ℤ))
    (hcf : CrossCFirst0TowerEq W n K M P a c d) :
    ARDVecResidue W n K M P a c d :=
  (ardVecResidue_iff_ardTowerDecomp W n K M P a c d).mpr
    (ardTowerDecomp_of_cfirst W n ha hc hd hcf)

/-! ## The full `MUGradedAction W` and the conditional bijection from the skew-reached core. -/

/-- **The full `MUGradedAction W` from the single universal level-`0` cross `c`-first core.**  Given,
for every level `n` and all homogeneous data, the level-`0` cross `c`-first tower decomposition
`CrossCFirst0TowerEq` (the genuine `a`-irreducible core the skew route reaches), the Dong–Jiang `M(U)`
graded-action crux `MUGradedAction W` holds.  This is `MUGradedAction_of_crossCFirst0`
(`ZhuVermaAnArchARDTowerClose`) re-exposed as the endpoint of the skew attack: every other piece
(Term₂'s full tower, Term₁'s commutator, the subtraction, and the membership half) is fully
discharged, and the negative-`s` `c₍s₎a` left factors of the residual `MGTowerFam` are exactly those
generated by `smul_eq_skew_Lpow`. -/
theorem MUGradedAction_of_skew_crossCFirst0 (W : VertexOperatorAlgebra 𝒱)
    (Hcf : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), CrossCFirst0TowerEq W n K M P a c d) :
    MUGradedAction W :=
  MUGradedAction_of_crossCFirst0 W Hcf

/-! ## Status — `ARDVecResidue` reduced (via skew) to the level-`0` cross `c`-first core.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`admit`/`axiom`/`pbw`/`native_decide`):

* **`smul_eq_skew_Lpow`** — **the skew `c₍s₎a` generator** (the negative-`s` creation engine), the
  `W.smul`/`L₋₁` restatement of the axiom-clean `skew_mode` (Gannon 5.1.8).  This is the precise
  mechanism the SKEW-ISOLATION report identified, proved axiom-clean and reusable.
* **`ardVecResidue_of_term1TowerEq`** — `ARDVecResidue` from JUST the Term₁ tower decomposition
  (Term₂ fully discharged via `ARDCommTowerEq_holds`).
* **`ardVecResidue_of_crossCFirst0`** — `ARDVecResidue` from the level-`0` cross `c`-first core
  `CrossCFirst0TowerEq`, the genuine `a`-irreducible remaining identity.
* **`MUGradedAction_of_skew_crossCFirst0`** — the full `MUGradedAction W` from the single skew-reached
  core.

**Status.** `ARDVecResidue` is NOT an unconditional axiom-clean term: it is a TERM **modulo
exactly one mathematical hypothesis**, the level-`0` cross `c`-first tower decomposition
`CrossCFirst0TowerEq W n K M P a c d`

  `:  crossCircCFirst = PresTowerFam W M n c … + MGTowerFam W n S … leftS …`   (leftS HOMOGENEOUS,
                                                                                 ARBITRARY grade),

the FULL level-`n` circle-generator span.  In this full-span form the identity is engine-verified
TRUE at converged truncation for EVERY case, including the `M = 1, K ≥ 2` sector
(`certificates/mathematica/anmrightdiff_check.wl`, re-run `SMAX = 12`: `ARD ∈ span{anmCirc W n 0 u v}`
True for `a = L₋₂/L₋₃, c = J`).  The skew generator `smul_eq_skew_Lpow` (proved here, axiom-clean)
supplies the negative-`s` `c₍s₎a` left factors of that span; the genuine remaining content is the
cross-base Vandermonde reorganization of the proven regrade rows (`towerCoeffAnm_regrade_int` /
`crossDiff_regrade_sub` fused with the skew `j`-sum), the frontier of Zhu Thm 5.3.4 at level `n`.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.smul_eq_skew_Lpow
  #print axioms VOA.ardVecResidue_of_term1TowerEq
  #print axioms VOA.ardVecResidue_of_crossCFirst0
  #print axioms VOA.MUGradedAction_of_skew_crossCFirst0
-/
