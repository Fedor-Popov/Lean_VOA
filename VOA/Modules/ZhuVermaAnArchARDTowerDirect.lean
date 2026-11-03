/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchAoutLev0Slice
import VOA.Modules.ZhuVermaAnArchAoutLev0Ugamma

/-!
# Game One — the **bidirectional reduction** `ARDTowerDecomp ↔ AoutUCoreLev0Core`.

This file establishes that the single open frontier core `ARDTowerDecomp`
(`ZhuVermaAnArchCrossCFirstGate`) — the `a`-outer right-action-difference tower decomposition — is
**exactly equivalent** to the level-`0` half cross-base collapse `AoutUCoreLev0Core`
(`ZhuVermaAnArchAoutUCore`).  The forward direction `ARDTowerDecomp ⟹ AoutUCoreLev0Core` is already
proved (`aoutUCoreLev0Core_of_ARDTowerDecomp`, `ZhuVermaAnArchAoutLev0Slice`); here we prove the
**converse** `AoutUCoreLev0Core ⟹ ARDTowerDecomp`, pinning the two cores as genuinely interchangeable
endgame targets (proving EITHER closes `MUGradedAction W`, Zhu Thm 5.3.4).

## The converse (FULLY proven here; no `sorry`/axiom/`pbw`)

The `a`-outer `i`-sum reindex (`aOutLev0Half_eq_addThree`, `ZhuVermaAnArchAoutLev0Slice`) gives, for
homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`,

  `aOutLev0Half W n K M a c d = anmRightDiff W n K a c d + crossDiffComm W n K M a c d
                                  + aOutLevNHalf W n K M a c d`,

equivalently

  `anmRightDiff = aOutLev0Half − crossDiffComm − aOutLevNHalf`.

Supplying `aOutLev0Half = PresTowerFam(c) + MGTowerFam` from the carried `AoutUCoreLev0Core`, with the
two PROVEN towers

  `crossDiffComm = MGTowerFam` (`c₍s₎a` @ `d`)     (`crossDiffComm_eq_MGTowerFam`),
  `aOutLevNHalf  = PresTowerFam(c) @ a₍·₎d`         (`aOutLevNHalf_eq_PresTowerFam`),

subtracted off, leaves `anmRightDiff` as `(PresTowerFam(c) − PresTowerFam(c)) +
(MGTowerFam − MGTowerFam)`.  Both differences are again of their own kind
(`smul_PresTowerFam`/`PresTowerFam_add`; `smul_MGTowerFam`/`MGTowerFam_add`, homogeneity by
`MGTowerFam_add_hom`), yielding the explicit `ARDTowerDecomp` witness.

Combined with the proved forward direction this gives the explicit equivalence
`ardTowerDecomp_iff_aOutUCoreLev0Core`, and the full `MUGradedAction W` from the SINGLE universal
`AoutUCoreLev0Core` is re-exported (already available through `MUGradedAction_of_aOutUCoreLev0Core`,
`ZhuVermaAnArchAoutUCore`; restated here against the converse so the two cores are visibly
interchangeable).

## Engine status (rank-1 free boson; NOT faked)

* `certificates/mathematica/ardtower_direct_check.wl`: `aOutLev0Half ∈
  (c-tow@a₍g₎d) + ((c₍s₎a)-tow@d)` is **True** (`n = 1, 2`, mixed homogeneous `a, c, d`, span bounds
  `8`); the `c`-towers ALONE do NOT suffice (**False**) — both families load-bearing.  The proven
  `aOutLev0Half_eq_addThree` reindex makes `aOutLev0Half` and `anmRightDiff` differ only by the two
  proven towers, so the two cores are genuinely interchangeable.
* `certificates/mathematica/ardtower_scalar_id.wl`: the per-base level-`0` weight
  `cbz(M, μ+2)` is **NOT** a per-base grade-`M` level-`n` `c`-tower (residual `1`, `√2`, `1`, `√5`,
  …) while the level-`n` half `cbz(M, μ+(n+2))` IS (residual `0`, coefficient `1`).  This pins the
  genuine cross-base content as the single irreducible scalar residual.

## The single remaining identity (engine-verified TRUE; NOT faked)

Either of the two interchangeable cores `ARDTowerDecomp` / `AoutUCoreLev0Core` — the nested-mode
level-`0`-vs-level-`n` `c`-tower-over-`a₍g₎d` plus `c₍s₎a`-`MGTowerFam` decomposition.  Its scalar
heart is the **cross-base regrade** of the level-`0` per-base weight `cbz(M, μ+2)` onto a level-`n`
grade-`M` `c`-tower plus a `c₍s₎a` spill, the nested (`a`-outer) analogue of the FULLY-proven
diagonal U/V core `UgammaModeCollAnm_eq_towerCoeff` / `VgammaModeCollAnm_eq_towerCoeff`
(`ZhuVermaAnArchMUcircV`/`ZhuVermaAnArchMUcircClose`), with the extra pole-`2`-vs-pole-`(n+2)` offset
absorbed by the proven regrade `towerCoeffAnm_regrade_int`/`regradeWt` (`ZhuVermaAnArchHPoleN`).

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason, J. Algebra 206 (1998) 67–96; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The converse reduction — `AoutUCoreLev0Core ⟹ ARDTowerDecomp`. -/

/-- **`AoutUCoreLev0Core ⟹ ARDTowerDecomp`** (the converse reduction, homogeneous `a ∈ 𝒱_K`,
`c ∈ 𝒱_M`, `d ∈ 𝒱_P`).  By the `a`-outer `i`-sum reindex `aOutLev0Half_eq_addThree`,

  `anmRightDiff = aOutLev0Half − crossDiffComm − aOutLevNHalf`,

with each subtracted summand a known tower family:

* `aOutLev0Half = PresTowerFam W M n c RU₀ ΔU₀ baseU₀ wU₀ + MGTowerFam W n S₀ …` — the carried
  level-`0` half cross-base collapse `AoutUCoreLev0Core`;
* `crossDiffComm = MGTowerFam W n S₁ …` (in the products `c₍s₎a` @ `d`) — `crossDiffComm_eq_MGTowerFam`
  (PART (II), FULLY proven via the two commutator twins);
* `aOutLevNHalf = PresTowerFam W M n c (K+1) 1 …` (in `c` @ `a₍·₎d`) — `aOutLevNHalf_eq_PresTowerFam`
  (the clean level-`n` half collapse, FULLY proven).

The grade-`M` level-`n` `c`-`PresTowerFam` difference `U₀ − U_N` is again a `PresTowerFam`
(`smul_PresTowerFam` by `−1` + `PresTowerFam_add`); the `c₍s₎a`-`MGTowerFam` difference `W₀ − W₁` is
again an `MGTowerFam` (`smul_MGTowerFam` by `−1` + `MGTowerFam_add`, homogeneity by
`MGTowerFam_add_hom`).  This yields the explicit `ARDTowerDecomp` witness — the converse of the proved
`aoutUCoreLev0Core_of_ARDTowerDecomp` (`ZhuVermaAnArchAoutLev0Slice`). -/
theorem ardTowerDecomp_of_aOutUCoreLev0Core (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M P : ℕ}
    {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (hc : c ∈ W.grading (M : ℤ))
    {d : 𝒱} (hd : d ∈ W.grading (P : ℤ))
    (hcore : AoutUCoreLev0Core W n K M P a c d) :
    ARDTowerDecomp W n K M P a c d := by
  -- the level-`0` half collapse (carried): `aOutLev0Half = U₀ + W₀`.
  obtain ⟨RU₀, ΔU₀, S₀, baseU₀, wU₀, gradeS₀, leftS₀, baseS₀, ΔS₀, wS₀, hhom₀, hlev0⟩ := hcore
  -- the commutator tower (proven): `crossDiffComm = W₁`.
  obtain ⟨S₁, gradeS₁, leftS₁, baseS₁, ΔS₁, wS₁, hhom₁, hcommeq⟩ :=
    crossDiffComm_eq_MGTowerFam W n ha hc hd
  -- assemble the witness: merged `c`-`PresTowerFam` (U₀ ⊕ (−1)•U_N) and merged `c₍s₎a`-`MGTowerFam`
  -- (W₀ ⊕ (−1)•W₁).
  refine ⟨RU₀ + (K + 1), max ΔU₀ 1, S₀ + S₁,
    (fun r => Sum.elim baseU₀
        (fun i : Fin (K + 1) => W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d) (finSumFinEquiv.symm r)),
    (fun r δ => Sum.elim (fun r₁ => if δ < ΔU₀ then wU₀ r₁ δ else 0)
        (fun r₂ : Fin (K + 1) => if δ < 1 then (-1 : ℂ) * (if δ = 0 then cbz (K : ℤ) (r₂ : ℤ) else 0)
          else 0) (finSumFinEquiv.symm r)),
    (fun r => Sum.elim gradeS₀ gradeS₁ (finSumFinEquiv.symm r)),
    (fun r => Sum.elim leftS₀ leftS₁ (finSumFinEquiv.symm r)),
    (fun r => Sum.elim baseS₀ baseS₁ (finSumFinEquiv.symm r)),
    (fun r => Sum.elim ΔS₀ ΔS₁ (finSumFinEquiv.symm r)),
    (fun r => Sum.elim wS₀ (fun r₁ δ => (-1 : ℂ) * wS₁ r₁ δ) (finSumFinEquiv.symm r)),
    MGTowerFam_add_hom W S₀ S₁ gradeS₀ leftS₀ gradeS₁ leftS₁ hhom₀ hhom₁, ?_⟩
  -- `anmRightDiff = aOutLev0Half − crossDiffComm − aOutLevNHalf`.
  have hard : anmRightDiff W n K a c d
      = aOutLev0Half W n K M a c d
        - crossDiffComm W n K M a c d - aOutLevNHalf W n K M a c d := by
    rw [aOutLev0Half_eq_addThree W n ha hc d]; abel
  rw [hard, hlev0, hcommeq, aOutLevNHalf_eq_PresTowerFam W n K M a c d]
  -- `(U₀ + W₀) − W₁ − U_N = (U₀ + (−1)•U_N) + (W₀ + (−1)•W₁)`.
  rw [show (PresTowerFam W M n c RU₀ ΔU₀ baseU₀ wU₀
              + MGTowerFam W n S₀ gradeS₀ leftS₀ baseS₀ ΔS₀ wS₀)
            - MGTowerFam W n S₁ gradeS₁ leftS₁ baseS₁ ΔS₁ wS₁
            - PresTowerFam W M n c (K + 1) 1
                (fun i => W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)
                (fun i δ => if δ = 0 then cbz (K : ℤ) (i : ℤ) else 0)
          = (PresTowerFam W M n c RU₀ ΔU₀ baseU₀ wU₀
              + (-1 : ℂ) • PresTowerFam W M n c (K + 1) 1
                  (fun i => W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)
                  (fun i δ => if δ = 0 then cbz (K : ℤ) (i : ℤ) else 0))
            + (MGTowerFam W n S₀ gradeS₀ leftS₀ baseS₀ ΔS₀ wS₀
                + (-1 : ℂ) • MGTowerFam W n S₁ gradeS₁ leftS₁ baseS₁ ΔS₁ wS₁) from by
      simp only [neg_one_smul]; abel]
  rw [smul_PresTowerFam W M n c (K + 1) 1
        (fun i => W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)
        (fun i δ => if δ = 0 then cbz (K : ℤ) (i : ℤ) else 0) (-1 : ℂ),
    PresTowerFam_add W M n c RU₀ (K + 1) ΔU₀ 1 baseU₀
      (fun i => W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d) wU₀
      (fun i δ => (-1 : ℂ) * if δ = 0 then cbz (K : ℤ) (i : ℤ) else 0),
    smul_MGTowerFam W n S₁ gradeS₁ leftS₁ baseS₁ ΔS₁ wS₁ (-1 : ℂ),
    MGTowerFam_add W n S₀ S₁ gradeS₀ leftS₀ baseS₀ ΔS₀ wS₀
      gradeS₁ leftS₁ baseS₁ ΔS₁ (fun r₁ δ => (-1 : ℂ) * wS₁ r₁ δ)]

/-! ## The explicit bidirectional equivalence of the two endgame cores. -/

/-- **`ARDTowerDecomp ↔ AoutUCoreLev0Core`** (the explicit bidirectional equivalence, homogeneous
`a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`).  The forward direction is the proved
`aoutUCoreLev0Core_of_ARDTowerDecomp` (`ZhuVermaAnArchAoutLev0Slice`); the converse is
`ardTowerDecomp_of_aOutUCoreLev0Core` (above).  Both directions differ only by the two PROVEN towers
`crossDiffComm` (`MGTowerFam`) and `aOutLevNHalf` (`PresTowerFam`), so the `a`-outer
right-action-difference tower decomposition and the level-`0` half cross-base collapse are genuinely
interchangeable endgame targets: proving EITHER closes `MUGradedAction W` (Zhu Thm 5.3.4). -/
theorem ardTowerDecomp_iff_aOutUCoreLev0Core (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M P : ℕ}
    {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (hc : c ∈ W.grading (M : ℤ))
    {d : 𝒱} (hd : d ∈ W.grading (P : ℤ)) :
    ARDTowerDecomp W n K M P a c d ↔ AoutUCoreLev0Core W n K M P a c d :=
  ⟨fun hdec => aoutUCoreLev0Core_of_ARDTowerDecomp W n ha hc hd hdec,
   fun hcore => ardTowerDecomp_of_aOutUCoreLev0Core W n ha hc hd hcore⟩

/-! ## The full `MUGradedAction W` from the single universal `AoutUCoreLev0Core` (converse route). -/

/-- **The full `MUGradedAction W` from the single universal `AoutUCoreLev0Core`** (re-exported through
the converse reduction).  Given, for every level `n` and all homogeneous data, the level-`0` half
cross-base collapse `AoutUCoreLev0Core`, the converse reduction `ardTowerDecomp_of_aOutUCoreLev0Core`
supplies the universal `ARDTowerDecomp`, and `MUGradedAction_of_ARDTowerDecomp_via_aOutLev0`
(`ZhuVermaAnArchAoutLev0Slice`) assembles the Dong–Jiang `M(U)` graded-action crux `MUGradedAction W`.

This is the converse-direction re-export: it visibly closes `MUGradedAction W` from `AoutUCoreLev0Core`
through `ARDTowerDecomp`, confirming the two cores are interchangeable (the direct route
`MUGradedAction_of_aOutUCoreLev0Core`, `ZhuVermaAnArchAoutUCore`, closes it from `AoutUCoreLev0Core`
directly). -/
theorem MUGradedAction_of_aOutUCoreLev0Core_via_ARD (W : VertexOperatorAlgebra 𝒱)
    (Hcore : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), AoutUCoreLev0Core W n K M P a c d) :
    MUGradedAction W :=
  MUGradedAction_of_ARDTowerDecomp_via_aOutLev0 W
    (fun n K M P a ha c hc d hd =>
      ardTowerDecomp_of_aOutUCoreLev0Core W n ha hc hd (Hcore n K M P a ha c hc d hd))

/-! ## Status — the two endgame cores `ARDTowerDecomp` / `AoutUCoreLev0Core` PINNED as equivalent.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`ardTowerDecomp_of_aOutUCoreLev0Core`** — **the converse reduction** `AoutUCoreLev0Core ⟹
  ARDTowerDecomp`, via the `a`-outer `i`-sum reindex `aOutLev0Half_eq_addThree`
  (`anmRightDiff = aOutLev0Half − crossDiffComm − aOutLevNHalf`), subtracting the two PROVEN towers
  `crossDiffComm` (`MGTowerFam`, `crossDiffComm_eq_MGTowerFam`) and `aOutLevNHalf` (`PresTowerFam`,
  `aOutLevNHalf_eq_PresTowerFam`), and merging the resulting `PresTowerFam`/`MGTowerFam` differences
  via `smul_PresTowerFam`/`PresTowerFam_add` and `smul_MGTowerFam`/`MGTowerFam_add` (`MGTowerFam_add_hom`).
* **`ardTowerDecomp_iff_aOutUCoreLev0Core`** — the explicit bidirectional equivalence (forward:
  proved `aoutUCoreLev0Core_of_ARDTowerDecomp`; converse: above).
* **`MUGradedAction_of_aOutUCoreLev0Core_via_ARD`** — the full `MUGradedAction W` from the single
  universal `AoutUCoreLev0Core` through the converse reduction.

**The single remaining identity (engine-verified TRUE; NOT faked):** either interchangeable core
`ARDTowerDecomp W n K M P a c d` / `AoutUCoreLev0Core W n K M P a c d`.  Its scalar heart, isolated
in `certificates/mathematica/ardtower_scalar_id.wl`, is the cross-base regrade of the level-`0`
per-base weight `cbz(M, μ+2)` (which is provably **NOT** a per-base grade-`M` level-`n` `c`-tower,
residual `1`/`√2`/…) onto a level-`n` grade-`M` `c`-tower-over-`a₍g₎d` plus a `c₍s₎a` `MGTowerFam`
spill — the nested (`a`-outer) analogue of the FULLY-proven diagonal U/V core
`UgammaModeCollAnm_eq_towerCoeff`/`VgammaModeCollAnm_eq_towerCoeff` (`ZhuVermaAnArchMUcircV`/
`ZhuVermaAnArchMUcircClose`), the pole-`2`-vs-pole-`(n+2)` offset absorbed by the proven regrade
`towerCoeffAnm_regrade_int`/`regradeWt` (`ZhuVermaAnArchHPoleN`).  Engine values:
`certificates/mathematica/ardtower_direct_check.wl` (`aOutLev0Half ∈ (c-tow@a₍g₎d)+((c₍s₎a)-tow@d)` **True**,
`n = 1, 2`; `c`-towers ALONE **False**).
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.ardTowerDecomp_of_aOutUCoreLev0Core
  #print axioms VOA.ardTowerDecomp_iff_aOutUCoreLev0Core
  #print axioms VOA.MUGradedAction_of_aOutUCoreLev0Core_via_ARD
-/
