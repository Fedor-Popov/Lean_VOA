/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.LogTensorArCoefficientFormula
import VOA.Modules.LogTensorArCoordinates
import VOA.Modules.LogTensorPzPointTransport
import VOA.Modules.LogTensorBalancing
import VOA.Modules.LogTensorArBranchEquiv
import VOA.Modules.LogTensorArDualPairing
import VOA.Modules.LogTensorPzPointEvaluation
import VOA.Modules.LogTensorArEquiv
import VOA.Modules.LogModuleCategory
import VOA.Modules.LogModuleC1Dual
import VOA.Modules.LogModuleC1Parts
import VOA.Modules.LogTensorUniformLog
import VOA.Modules.LogTensorTwist
import VOA.Modules.LogModuleC1Graded
import VOA.Modules.WeakModule
import VOA.Modules.AdmissibleModule
import VOA.Modules.LogVModule
import VOA.Modules.SuperWeakModule
import VOA.Modules.SuperAdjointModule
import VOA.Modules.ModuleRestrict
import VOA.Modules.ModuleRestrictOrd
import VOA.Modules.Translation
import VOA.Modules.Character
import VOA.Modules.OrdinaryExact
import VOA.Modules.OrdinaryComplex
import VOA.Modules.Rationality
import VOA.Modules.AdmissibleRationality
import VOA.Modules.AdmissibleGradedComplement
import VOA.Modules.AdmissibleSemisimpleDecomp
import VOA.Modules.C2Cofinite
import VOA.Modules.RationalityLattice
import VOA.Modules.StronglyRational
import VOA.Modules.PoissonDescent
import VOA.Modules.PoissonQuotient
import VOA.Modules.FiniteGeneration
import VOA.Modules.FiniteGenerationProof
import VOA.Modules.PairClosure
import VOA.Modules.ZhuAlgebra
import VOA.Modules.ZeroModeMult
import VOA.Modules.ZhuModule
import VOA.Modules.ZhuRing
import VOA.Modules.ZhuRingResidue
import VOA.Modules.ZhuMuIdentity
import VOA.Modules.ZhuUCore
import VOA.Modules.ZhuVCore
import VOA.Modules.ZhuRightIdeal
import VOA.Modules.ZhuAssociator
import VOA.Modules.ZhuRingInstance
import VOA.Modules.ZhuPolynomialSimplicity
import VOA.Modules.ZhuBijection
import VOA.Modules.ZhuVermaAn
import VOA.Modules.ZhuVermaAnBimodule
import VOA.Modules.ZhuVermaAnDescent
import VOA.Modules.ZhuVermaAnDescent2
import VOA.Modules.ZhuVermaAnDescent3
import VOA.Modules.ZhuVermaAnDescent4
import VOA.Modules.ZhuVermaAnDescent5
import VOA.Modules.ZhuVermaAnDescent6
import VOA.Modules.ZhuVermaAnDescent7
import VOA.Modules.ZhuVermaAnDescent8
import VOA.Modules.ZhuVermaAnDescent9
import VOA.Modules.ZhuVermaAnDescent10
import VOA.Modules.ZhuVermaAnDescent11
import VOA.Modules.ZhuVermaAnDescent12
import VOA.Modules.ZhuVermaAnDescent13
import VOA.Modules.ZhuVermaAnDescent14
import VOA.Modules.ZhuVermaAnDescent15
import VOA.Modules.ZhuVermaAnDescent16
import VOA.Modules.ZhuVermaAnDescent17
import VOA.Modules.ZhuVermaAnDescent18
import VOA.Modules.ZhuVermaAnDescent19
import VOA.Modules.ZhuVermaAnDescent20
import VOA.Modules.ZhuVermaAnDescent21
import VOA.Modules.ZhuVermaAnDescent22
import VOA.Modules.ZhuVermaAnDescent23
import VOA.Modules.ZhuVermaAnDescent24
import VOA.Modules.ZhuVermaAnDescent25
import VOA.Modules.ZhuVermaAnDescent26
import VOA.Modules.ZhuInduced
import VOA.Modules.ZhuInducedPointwise
import VOA.Modules.Fusion
import VOA.Modules.Contragredient
import VOA.Modules.ContragredientAction
import VOA.Modules.ContragredientJacobi
import VOA.Modules.ContragredientTransport
import VOA.Modules.ContragredientFromResidual
import VOA.Modules.ContragredientFHL
import VOA.Modules.ContragredientFHLBase
import VOA.Modules.ContragredientFHLComul
import VOA.Modules.ContragredientFHLGen
import VOA.Modules.ContragredientClose
import VOA.Modules.ContragredientCharacter
import VOA.Modules.ContragredientCharacterClose

/- The Zhu bijection, **conditional on the explicit projection parameter `Pr`.**
   `zhuBijective Pr` is the `sorry`-free, `pbw`-free faithful Zhu bijection. The canonical wrapper
   `zhuBijective_of_voaPBW` supplies `Pr` from `PBWPrinciple.inducedBottom`; the bundle's separate
   `affineVacuum` field is not used by this wrapper. The `ZhuVermaAnArch*` imports below provide
   intermediate constructions, alternative conditional routes and reusable APIs. Where a comment
   there describes the bijection as open, it refers to that file's own route; the bijection itself
   is given by the `ZhuVermaAnArchLUBijection{,PBW}` main theorems imported near the end of this
   file. -/
import VOA.Modules.ZhuVermaAnArchPhase4Bijection
/- `CrossCircReduce` reduces the A-direction keystone `hslice`/`MUGradedAction` to the SINGLE
   cross-circle membership family (the diagonal `circ` field is the proven `hcirc_closed`; `crossL`
   derives from `crossCirc`). -/
import VOA.Modules.ZhuVermaAnArchCrossCircReduce
/- `CrossCircCollapse` reduces the whole A-direction (`MUGradedAction`) to the SINGLE ideal
   inclusion `OnmFull W n 0 ≤ Onm W n 0` (the collapse `O'', O''' ⊆ O'`): crossCirc-into-`OnmFull`
   is the proven `circCross_mem`, transported across the collapse. -/
import VOA.Modules.ZhuVermaAnArchCrossCircCollapse
/- DJ Lemma 2.8 (Half A sole open core `anmRightDiff ∈ Onm`), the induction-on-`n` scaffold and the
   corrected direct DLM route.  `DJ28Base`: the `n = 0` base cases (Zhu two-sided ideal).
   `DJ28Induction`: `MUGradedAction ⟸ (∀ n, Term1Level ∧ Term2Level)`, tower-free via `Submodule.sub_mem`.
   `DJ28PoleShift`: the off-diagonal pole-shift `resHom W s (n+2+t) ∈ Onm` for `t ≥ s` (m=0 DLM Lemma
   2.1(i)), the black box behind DLM's direct Jacobi/iterate ideal proof (off the diagonal `Pres_mem_Onm`). -/
import VOA.Modules.ZhuVermaAnArchDJ28Base
import VOA.Modules.ZhuVermaAnArchDJ28Induction
import VOA.Modules.ZhuVermaAnArchDJ28PoleShift
/- `DJ28Term2`: the membership side of the DLM Part-3 commutator expansion of `Term₂`
   (`anmRight W n 0 a (anmCirc W n 0 c d) ∈ Onm`), packaged via `resHom_offdiag_mem_Onm` +
   `anmCirc_mem_Onm`; reduces `Term2Level` to the single commutator identity `Term2Level_of_commIdentity`. -/
import VOA.Modules.ZhuVermaAnArchDJ28Term2
/- `DJ28Term2Identity`: the scalar heart of the `Term₂` DLM commutator identity — `coeffST2_collapse`,
   the `(a₍ₛ₎c)`-mode coefficient collapse `∑_p cbz(K,p)cbz(M,X-p)cbz(p-(n+1),s) = ∑_{t≤s}
   cbz(-(n+1),s-t)cbz(K,t)cbz(K+M-t,X-t)` (three FZ Vandermondes: `vandermonde_range`+`stepB`+`stepC`),
   engine-verified exact (`certificates/mathematica/term2_coeff.wl`). The scalar core of `Term2Level_of_commIdentity` (matched-
   level, the closable half of the DJ 2.8 keystone; `Term₁` cross-level stays the wall). -/
import VOA.Modules.ZhuVermaAnArchDJ28Term2Identity
/- `DJ28Term1Reduce`: with `Term2Level_holds` proved, the level-0-inner `Term₁` (DJ Lemma 2.8) is
   reduced — via the DJ Prop 5.2 uniform pole-shift `resHom_poleShift` + outer ℂ-linearity — to the
   pole-deficient `r ≥ 1` alternating tail `Term1TailResidual` (the `r = 0` level-`n` circle main term
   is absorbed by `Term2Level`). `MUGradedAction_of_Term1Tail`: the whole Half-A keystone from that tail. -/
import VOA.Modules.ZhuVermaAnArchDJ28Term1Reduce
/- `DJ28Term1Capstone`: with `Term2Level_holds` proved, `mUGradedAction_of_crossCircCore` — the whole
   Half-A crux `MUGradedAction W` from the SINGLE residual `CrossCircCore` (= `Term₁`, the level-0-inner
   cross circle); `Term₂` is discharged. DJ's degree argument (iterate + `resHom_offdiag_mem_Onm` = DJ
   Lemma 2.4) reduces it to the c-first `crossCirc0` core (engine-TRUE, circular under a↔c — the genuine
   remaining cross-level core; `Onm` = DJ's O', the correct target). -/
import VOA.Modules.ZhuVermaAnArchDJ28Term1Capstone
/- `LiDuality`/`LiReduce`: the Haisheng Li (arXiv 2205.05481) module-theoretic route to `CrossCircCore`.
   `LiDuality` proves the abstract annihilator-stability duality (Li Lemma 2.16, `mapsTo_of_dualMap_
   annihilator`): a primal closure `ψ q ⊆ p` from a dual containment `ψ*(Ann p) ⊆ Ann q` + weak-*
   closedness of `p`. `LiReduce` ports it to the repo: `crossCircCore_of_liDual` reduces `CrossCircCore`
   to (a) `OnmWeakClosed` (graded finite-dim closedness) + (b) `LiDualStable` (the regular-representation
   dual-module condition, Li Thm 3.17). `mUGradedAction_of_liDual`: the whole Half-A crux from those two
   Li obligations. -/
import VOA.Modules.ZhuVermaAnArchLiDuality
import VOA.Modules.ZhuVermaAnArchLiReduce
/- `ZhuVermaAnArchLiRegRep`: Li's regular representation `D^{(-1)}(𝒱) ⊂ 𝒱^*` — brick 1, the full-dual
   FHL adjoint `Yadj`/`adjOp` on `Module.Dual ℂ 𝒱` (Li arXiv 2205.05481 §3), the foundation for
   discharging `LiDualStable`. -/
import VOA.Modules.ZhuVermaAnArchLiRegRep
/- `ZhuVermaAnArchLiVacuum`: brick 2 — the DAGGER level-`(0,n)` vacuum space `VacuumSpace` via the
   FHL-adjoint pole condition (Li Def 3.4 / Prop 3.5, `m=0`), and the SOUND proven inclusion
   `adjPoleSpace_le_Onm : AdjPoleSpace W n ⊆ Onm W n 0` (FHL `x↔z⁻¹` re-summation). ⚠ The dagger vacuum
   space annihilates `O†ₙ₀ ⊊ Onm=O'ₙ₀` for `n≥1`; the P1/vacuum-route main theorems were unsound and removed
   (sound route = `mUGradedAction_of_liDualStable`). -/
import VOA.Modules.ZhuVermaAnArchLiVacuum
/- `MUBalancedBottom`: the `A(𝒱)`-balanced generalized-Verma bottom `M(U)(0) = A₀₀ ⊗_{A(𝒱)} U` as a
   standalone object — `MUBalBottom`, the DJ iso `muBalBottomEquiv : MUBalBottom ≅ U`, and the
   balancing quotient bridge `muBalQuot : MUPiece 0 ↠ MUBalBottom` (through which `layerAction 0`
   factors).  The (R0) foundation for the bimodule-balancing re-grading of `MUModuleData`'s bottom. -/
import VOA.Modules.ZhuVermaAnArchMUBalancedBottom
/- `MUBalancedBottomA`: the balanced bottom `M(U)(0) ≅ U` **as `A(𝒱)`-modules** (the genuine DJ
   statement) — the `A(𝒱)`-linear R0 map `bottomActA`, the `A(𝒱)`-module `MUBalBottomA`, and the iso
   `muBalBottomEquivA : MUBalBottomA ≃ₗ[A(𝒱)] P_h`, over the proved `instRingA`/`moduleMh`. The
   `A(𝒱)`-equivariant `n = 0` target for the bimodule-balancing re-grading. -/
import VOA.Modules.ZhuVermaAnArchMUBalancedBottomA
/- `MUBalancedPiece`: the `A(𝒱)`-balanced level-`n` piece `MUPieceBal W U n = A_{n,0}(𝒱) ⊗_{A(𝒱)} U`
   for every `n` (generalizing the `n = 0` `MUBalBottom`) — the ℂ-tensor cover `MUPiece W U n` modulo
   the representative-level balancing span `balancing W U n`; the defining relation `mkPieceBal_balance`,
   and the `n = 0` match `muPieceBal0Equiv : MUPieceBal W U 0 ≃ MUBalBottom` (`balancing_zero_eq_ker`). -/
import VOA.Modules.ZhuVermaAnArchMUBalancedPiece
/- `MUBal`: the `A(𝒱)`-balanced generalized-Verma carrier `MUBal W U = ⨁ₙ MUPieceBal W U n`
   (bimodule-balanced replacement of the ℂ-tensor `MU`), with the level-`n` inclusion/projection and the internal
   direct-sum grading `MUBal.isInternal_deg` (mirroring `MU.isInternal_deg`). -/
import VOA.Modules.ZhuVermaAnArchMUBal
/- `MUGradedActionFull`: the DJ Theorem 2.9 `M(U)` `𝒱`-action closure into DJ's ACTUAL ideal `OnmFull`
   (= `O'+O''+O'''`), unconditional — `mUGradedActionFull_holds : MUGradedActionFull W`, right-module via
   `anmRight_OnmFull_unconditional`, cross via the span-closure `anmCrossClosureFull` of
   `dj28IntoFull_unconditional`. The `Onm`(O') `MUGradedAction` cross half is the DJ Rmk 2.10 OPEN problem
   (`O_{n,m}=O'_{n,m}`, m≠n, "we cannot find a proof"); the `OnmFull` keystone here is complete. -/
import VOA.Modules.ZhuVermaAnArchMUGradedActionFull
/- `MUFull`: DJ's induced-module pieces on the GENUINE full ideal — `MUPieceFull W U n = AnmFull W n 0 ⊗ U`,
   `MUFull`, and the unconditional graded (diagonal) action layer `MUFull.actLevel = actLevelFull` (no
   `AnmRightModule`/`CrossCircCore` hypothesis; DJ Thm 2.9 into DJ's ideal). Half-A action layer closed. -/
import VOA.Modules.ZhuVermaAnArchMUFull
/- `MUFullAction`: DJ's GENUINE `M(U)` 𝒱-action on the full ideal via the BIMODULE COMPOSITION (DJ §4 /
   Lemma 4.1, NOT a levelShift) — `oFull W U n m v : MUPieceFull W U m →ₗ MUPieceFull W U n`, the
   level-(m→n) mode `o_{n,m}(v)`, modulo the named `LeftGradingResidual`. NON-DEGENERATE (level-dependent
   Borcherds derivative escapes the levelShift `derivObstruction`); the levelShift degeneracy was a
   wrong-carrier artifact. Module Jacobi (DJ Thm 4.13) = the remaining Half-B core. -/
import VOA.Modules.ZhuVermaAnArchMUFullAction
/- `LeftGradingResidualFull`: discharged — the general-`p` right-slot grading absorption
   `leftGradingResidual_zero_gen : ∀ n p, LeftGradingResidual W n 0 p` (`V ∗ⁿ_{0,p} O'_{p,0} ⊆ O_{n,0}`,
   DJ Lemma 2.5 right-factor half). Axiom-clean, pbw-free. Closed identity
   `a ∗ⁿ_{0,p}(anmLgen W p 0 c) = anmLgen W n 0 (a ∗ⁿ_{0,p} c) + σ_p·(a ∘ⁿ_0 c)`,
   `σ_p = (−1)^{p+1}(n+1)C(n,p)`, via the per-mode telescope `lgrfull_abs_scalar`. Unblocks
   `oFull`/`oFull_comp` (M(U) 𝒱-action well-definedness) and the whole `MUFull → Zhu 5.3.4` bijection. -/
import VOA.Modules.ZhuVermaAnArchLeftGradingResidualFull
/- `MUFullActionU`: the unconditional M(U) 𝒱-action. `oFullU W U n m v : MUPieceFull W U m →ₗ
   MUPieceFull W U n` (DJ's genuine `o_{n,m}(v)`, no carried hypothesis) and `oFullU_comp` (DJ Lemma 4.1
   `o_{n,p}(a)∘o_{p,m}(b) = o_{n,m}(a ∗ⁿ_{m,p} b)`, unconditional) — the LeftGradingResidual residuals in
   `oFull`/`oFull_comp` discharged by `leftGradingResidual_zero_gen`. Multiplicative core of the M(U)
   module Jacobi (Gannon 5.3.1b / DJ Thm 4.13), axiom-clean. -/
import VOA.Modules.ZhuVermaAnArchMUFullActionU
/- `MUFullGrading`: the ℕ-grading API of DJ's full-ideal `M(U) = ⊕ₙ A_{n,0}(𝒱)⊗U` — `MUFull.deg`,
   `MUFull.isInternal_deg` (`M(U) = ⊕ₙ M(U)(n)` is a genuine internal direct sum), the orthogonal
   level projections, and the bottom layer `MUFull.bottomIncl`/`proj0`. The full-ideal mirror of
   `MU.deg`/`MU.isInternal_deg`; the graded input of the `OrdVModule` upgrade. -/
import VOA.Modules.ZhuVermaAnArchMUFullGrading
/- `MUFullMode`: DJ §4's `𝒱`-modes `u_p` of `M(U)` and the field `Y_{M(U)}(u,z)` — `muFullMode`
   (`oFullU` assembled level-by-level with DJ's case split `wt u − p − 1 + n ≥ 0`), `muFullYM`, and
   **DJ Lemma 4.6 discharged at `m = 0`**: `muFullMode_truncation` (4.6(1), each `Y_{M(U)}(u,z)` is a
   field) and `muFullMode_vacuum` (4.6(2), `Y_{M(U)}(𝟙,z) = id`, via `anmGen_vacuum_offdiag`). -/
import VOA.Modules.ZhuVermaAnArchMUFullMode
/- `MUFullRho`: `M(U)` as a `V̂`-representation. **`muFullActGen_hderiv` (the mode translation
   relation `(L₋₁a)_m + m·a_{m−1} = 0`) is unconditional** — it collapses to DJ's grading generator
   `anmLgen` in the acting slot, killed by the proved `anmGen_OnmFull_right_unconditional` (DJ Lemma
   2.8 right). `muFullRho` is then a `VHatRep W (MUFull W U)` modulo the single named leaf
   `MUFullBracket` (DJ Lemma 4.7, the commutator formula). -/
import VOA.Modules.ZhuVermaAnArchMUFullRho
/- `MUFullLW`: the DJ Thm 4.10 pipeline completed on the full-ideal carrier — `muFullWeak`
   (`WeakModule W (MUFull W U)`, modulo the two DJ leaves `MUFullBracket` + `ModuleIterate`), the
   graded packaging `MUFullModuleData` → `toOrdVModule` → `toLWModule`, and `buildMUFullModuleData`.
   Truncation/vacuum/translation are all discharged; `U ↦ M(U)` is an `LWModule W` term as soon as
   the two DJ leaves are supplied. -/
import VOA.Modules.ZhuVermaAnArchMUFullLW
/- `DJ23`: the two pure-𝒱 leaves under DJ Lemma 4.7 named (`DJ23Comm` = DJ Lemma 2.3, `DJ48Bdry` =
   DJ's `la4.8` boundary companion), plus **the mathematical core**:
   `anmGen_commutator_interior` — the representative-level commutator
   `a ∗^N_{0,n₁}(b ∗^{n₁}_{0,n} g) − b ∗^N_{0,n₂}(a ∗^{n₂}_{0,n} g) ≡ ∑ᵢ C(p,i)(a₍ᵢ₎b) ∗^N_{0,n} g`
   from `DJ23Comm` + the proved `mUFullCompAssoc_holds` (Thm 2.9) and
   `anmGen_OnmFull_right_unconditional` (Lemma 2.8 right). Index bookkeeping engine-verified. -/
import VOA.Modules.ZhuVermaAnArchDJ23
/- `SkewModOnm`: **SKEW SYMMETRY MODULO THE DONG–JIANG IDEAL** — the relation the repo had at NO
   level (not even Zhu's level-0 ancestor). `skew_mod_Onm`:
   `v₍t₎u ≡ sgn(t+1)·∑ⱼ C(E,j)·u₍t+j₎v (mod O'_{N,m})`, `E = wt u+wt v−2+m−N−t`. Proved from the
   proved VOA skew (`smul_eq_skew_Lpow`) plus the new `Lneg1_pow_mod_Onm` (the `L₋₁`-tower collapses
   mod `O'` — peel the INNERMOST `L₋₁`, so only scalars multiply a congruence; no `O'`-stability
   under `L₋₁` is needed, and none holds). **No Möbius substitution `z ↦ −z/(1+z)` is built.** -/
import VOA.Modules.ZhuVermaAnArchSkewModOnm
/- `AltVandermonde`: the scalar engine `cbz_alt_vandermonde`:
   `∑ₛ (−1)ˢ C(A,s) C(B−s, L−s) = C(B−A, L)` (`A : ℕ`, `B L : ℤ`), by Pascal induction on `A`. -/
import VOA.Modules.ZhuVermaAnArchAltVandermonde
/- `ResSkew`: the **residue form** of skew mod the ideal — `resHom_skew_mod_Onm`:
   `Res_z (1+z)^{wt v+m}/z^P Y(v,z)u ≡ (−1)^{P+1}·Res_z (1+z)^{wt u+P−N−2}/z^P Y(u,z)v (mod O'_{N,m})`.
   Swapping a residue's arguments costs only a sign and an exponent shift — the whole content of DJ's
   `−z/(1+z)` contour move. Also `resFull` (the honest residue, valid at negative exponent, where the
   repo's `resHom` truncation is wrong) and `resHom_eq_resFull`. -/
import VOA.Modules.ZhuVermaAnArchResSkew
/- `DJ23Close`: **DJ LEMMA 2.3** modulo one pure binomial identity. `dj23_homog` (homogeneous
   args) and `dj23Comm_of_dj51 : DJ51CoeffD → DJ23Comm W` (full, via ℂ-linearity in `b` + VOA
   positivity). The residue skew relation `resHom_skew_mod_Onm` turns all three terms into `resFull`s,
   so DJ 2.3 collapses to comparing coefficients of `a₍ℓ₎b` — leaving exactly `DJ51CoeffD`, the
   convolved coefficient form of DJ Appendix Prop 5.1 (`A_{p₁,p₂}(z) = 1`). Engine-verified. -/
import VOA.Modules.ZhuVermaAnArchDJ23Close
/- `DJ51`: DJ Appendix **Prop 5.1 in Laurent-coefficient form** — `dj51_coeff`: the coefficient of
   `z^r` in `A_{p₁,p₂}(z)` is `δ_{r,0}`. Proved by a single induction on `p₁` after applying binomial
   symmetry (`ZhuMu.cbz_symm`), via a hockey-stick with a `k = −1` defect (`cbz_range_hockey` — the
   defect IS the Kronecker delta) and a Pascal convolution (`cbz_pascalConvol`). -/
import VOA.Modules.ZhuVermaAnArchDJ51
/- `DJ23Final`: **DONG–JIANG LEMMA 2.3, unconditional** (`dj23Comm_holds`). The shifted Vandermonde
   `cbz_shift_convol` (`C(D+A, ℓ+σ) = ∑_r C(A,r+σ)C(D,ℓ−r)`) convolves `dj51_coeff` up to
   `dj51CoeffD_holds : DJ51CoeffD`, discharging the last hypothesis of `dj23Comm_of_dj51`. Downstream:
   `anmGen_commutator_interior_uncond` and `oFullU_commutator_interior_tmul_uncond` — the
   representative- and operator-level `M(U)` commutator (DJ Lemma 4.7, interior regime), free of
   every carried hypothesis. NO Möbius substitution `z ↦ −z/(1+z)` was ever built. -/
import VOA.Modules.ZhuVermaAnArchDJ23Final
/- `DJ48`: DJ Lemma `la4.8`, the boundary companion of Lemma 2.3 — `dj48_case1` (an EXACT equality in
   𝒱) and `dj48_case2` (mod O′, via `resHom_skew_mod_Onm`). Both phrased with ℕ indices only, the
   negativity recorded as `N + m < p`. Key: `cbz_neg_upper` (`C(n,k) = (−1)^k C(k−n−1,k)`) turns the
   alternating binomial into an ordinary one that is already complete, so DJ's detour through Lemma 2.4
   at general `m` is NOT needed; both regimes collapse to Vandermonde. -/
import VOA.Modules.ZhuVermaAnArchDJ48
/- `DJ47`: DJ Lemma 4.7 at representative AND operator level in EVERY regime —
   `anmGen_commutator_bdryA/bdryB` plus the reusable descent helper `oFullU_eq_of_repr_mem`
   (representative congruence ⟹ operator identity on ALL of `M(U)(n)`, not just generators), and the
   three operator-level regimes `oFullU_comm_interior_gen`/`bdryA_gen`/`bdryB_gen`. -/
import VOA.Modules.ZhuVermaAnArchDJ47
/- `MUFullBracketClose`: **`mUFullBracket_holds : MUFullBracket W U` — DJ LEMMA 4.7,
   unconditional.** The level bookkeeping (`muFullMode_commutator_incl`, four regimes) plus the
   `vloopBracket` assembly (`assembleAct_bracket_apply`). Hence `muFullRhoU W U : VHatRep W (MUFull W U)`
   — DJ's `M(U)` as a `V̂`-representation with NO carried hypothesis. -/
import VOA.Modules.ZhuVermaAnArchMUFullBracketClose
/- `DJ24Gen`: **DJ LEMMA 2.4 AT GENERAL BASE LEVEL `m`** — `resHom_offdiag_mem_Onm_gen`:
   `Res_z (1+z)^{M+m+s}/z^{q+m+2+t} Y(u,z)v ∈ O'_{q,m}` for `t ≥ s ≥ 0` (not only at
   `m = 0`). `PresAnm`/`PresAnmOff` are parameter-generic and `presAnm_recursion`/`presAnmOff_pascal`
   carry no hypothesis on `u`, so the whole `m=0` argument transports under `M ↦ M+m`, `n ↦ q+m`;
   only the base case (`anmCirc W q m` instead of `anmCirc W q 0`) and the target ideal change. -/
import VOA.Modules.ZhuVermaAnArchDJ24Gen
/- `IterateNonneg`: **the `ℓ ≥ 0` half of the module Borcherds identity is free** —
   `module_borcherds_nonneg` (no `ModuleIterate` hypothesis) and `moduleIterate_nonneg`. Inverting
   `MBL_rec`/`MBR_rec` gives `D (ℓ+1) m n = D ℓ (m+1) n − D ℓ m (n+1)`, so the `ℓ = 0` locality column
   (`MBL_zero_ell`, free for a `VHatRep`) propagates upward in `ℓ` for every `m, n` at once.
   ⟹ the ENTIRE genuine content of `ModuleIterate` is the regime `ℓ < 0` = DJ Lemma 4.9. -/
import VOA.Modules.ZhuVermaAnArchIterateNonneg
/- `MUFullWeakU`: scaffold — the whole `M(U)` module structure wired to the SINGLE remaining
   hypothesis `hit : ModuleIterate (muFullRhoU W U)` (whose `ℓ ≥ 0` half is free by
   `moduleIterate_nonneg`): `muFullActModeTruncatedU`/`muFullVacuumCreationU` (unconditional),
   `muFullWeakU hit : WeakModule W (MUFull W U)`, `buildMUFullModuleDataU`, and
   `muFullLWModuleU : LWModule W` — DJ's `M(U)` as a bundled lowest-weight module. -/
import VOA.Modules.ZhuVermaAnArchMUFullWeakU
/- `DWeightPoleShift`: the Dong–Jiang Prop 5.2 D-weight mechanism for the level-0 circle pole-shift
   (the DJ-2.8 keystone), formalized: `cbz_absorb` (absorption binomial) and `resHom_Lneg1_ibp`
   (the `L(-1)` IBP recursion — the telescoping tool that raises the residue pole while emitting
   `anmLgen` L-generators). Pole-shift (a) reduces to `cbz_fd`; the cancellation (c) remains. -/
import VOA.Modules.ZhuVermaAnArchDWeightPoleShift
/- `CrossCircConditional`: the cleanest CONDITIONAL Zhu-5.3.4 bijection — `Function.Bijective
   (forwardMapIrr W)` from the SINGLE Half-A residual `CrossCircCore` (`∀ n`) plus the minimal Half-B
   fields.  `zhu534_of_crossCircCore` carries Half B whole (`StructuralData`); `zhu534_of_crossCircCore_fields`
   names its fields individually; `zhu534_of_crossCircCore_peelGraded` additionally DISCHARGES the
   construction bundle's `graded : MUGradedAction W` field from `CrossCircCore` (via
   `mUGradedAction_of_crossCircCore`), carrying only the `graded`-free bundle `GAUniformNoGraded`. -/
import VOA.Modules.ZhuVermaAnArchCrossCircConditional
/- `ZhuVermaAnArchCrossCircSdAssemble`: combines `_peelGraded` with `bijection_of_sdAssemble` —
   `zhu534_of_crossCircCore_sdAssemble` discharges `hslice`, `graded`, `A`, `hirr` all from `CrossCircCore`,
   carrying only the genuine leaves `G0`/`bregen`/`realizes`/`Dfun`/`G'`. -/
import VOA.Modules.ZhuVermaAnArchCrossCircSdAssemble
/- `DJ49Master`: the PURE SCALAR core of DJ Lemma 4.9 — `dj49_master`:
   `∑_{r=0}^{k*} (−1)^r C(K+n−1+r, r) C(K+n, j−ℓ−r) = δ_{j,ℓ}` for `j − ℓ ≤ k*`.  No vertex-algebra
   content: upper-index negation (`cbz_negA_eq`, from `alt_cbz_eq`) turns the alternating binomial
   into `C(−A, r)`, the tail beyond `k*` vanishes because `C(A, m−r) = 0` for `m < r`, and the full
   convolution Vandermondes (`cbz_vandermonde`) to `C(0, m)` = the Kronecker delta
   (`cbz_zero_upper`). -/
import VOA.Modules.ZhuVermaAnArchDJ49Master
/- `OnmCollapseZero`: the BOTTOM hinge `(n,m) = (0,0)`.  Proves the pole-`0` reduction of the
   Dong–Jiang three-index product — `anmGen_zero_zero_succ`: `u *^0_{0,p+1} v = resHom W p 0 u v`
   (and `*^0_{0,0} = zhuMul`) — off the new `resHom_shift_pascal` /`resHom_shift_expand`.  Discharges
   the `p = 0` level-mixing family and the all-zero associator-defect family into `Onm W 0 0` from
   the unconditional `zhuRingData_holds`, and assembles `OnmFull W 0 0 = O W` from the two generator
   families (`onmFull_zero_zero_eq_O_of_gens`).  The families themselves are NOT discharged: this is
   DJ Prop. 4.5 at `n = 0`, whose only known proof is representation-theoretic (DLM3 Thm 4.1), and
   `resHom_zeroPole_zhuLgen` shows the pole-`0` residue absorbs `O(𝒱)` in neither slot. -/
import VOA.Modules.ZhuVermaAnArchOnmCollapseZero
/- `AModScope`: the additive repair of the `AMod` scope bug.  `AMod W` carries no nontriviality and
   no irreducibility, so `∀ U : AMod W` statements of `hbot`/`bottom_A0_irred`/`hL0` shape are FALSE
   — refuted here by `zeroAMod` (`not_forall_nontrivial`, `not_forall_muFull_bottom_ne_bot`,
   `MUFull.deg_zero_eq_bot_zeroAMod`) and by `AMod.prod` (`not_forall_amodDichotomy`,
   `not_scopedNontrivial_amodDichotomy`, `not_forall_exists_omegaScalar`).  Supplies the scoped
   predicates (`AModDichotomy`, `AMod.OmegaScalar`, reusing `IsSimpleAMod`), their `AModEquiv`
   transport, the scoped quantifiers `ScopedNontrivial`/`ScopedSimple`/`ScopedIrr`, the `IrrAMod`
   coercions (`IrrAMod.nontrivial`/`IrrAMod.omegaScalar` unconditional; simplicity on the named gate
   `AllIrrBottomRecovers`), and the corrected scoped `hbot`/`hL0`.  Scopes only — no keystone. -/
import VOA.Modules.ZhuVermaAnArchAModScope
/- `DJCarrier`: Dong–Jiang's carrier ported VERBATIM (`math/0601626` §4) — the level piece
   `DJPiece W U n = A_{n,m}(𝒱) ⊗_{A_m(𝒱)} U` over the FULL ideal (`AnmFull = 𝒱 ⧸ OnmFull`) and
   BALANCED at the GENERAL base level `m` (no `⊗_ℂ`, no `m = 0` restriction).  Proves the right
   `A_m(𝒱)`-action on `A_{n,m}(𝒱)` (`AnmFull.rightRep`/`rightHom` unconditional off
   `anmRight_OnmFull_unconditional`; `AnmFull.rightAct` modulo the acting-slot descent
   `DJRightSlot`, itself proved from `LeftGradingResidual W n m m` and unconditional at `m = 0`
   via `leftGradingResidual_zero_gen` → `AnmFull.rightActZero`), the bundled level-`m` module
   `AmMod W m`, and — modulo the single named hypothesis `DJAnnEqAn W m` (= DJ Prop. 4.6
   `A_{m,m} = A_m`, which DJ prove only representation-theoretically via DLM3 Thm 4.1) — the payoff
   `djPieceMEquiv : DJPiece W U m ≃ₗ U.carrier` (DJ's `M(U)(m) = U`). -/
import VOA.Modules.ZhuVermaAnArchDJCarrier
/- `DJCarrierGraded`: the graded Dong–Jiang carrier `DJCarrier W U = ⨁ₙ DJPiece W U n`
   (`M(U) = ⨁_{n∈ℤ₊} A_{n,m}(𝒱) ⊗_{A_m(𝒱)} U`), with `incl`/`proj`, the grading `deg`, the internal
   direct-sum decomposition `DJCarrier.isInternal_deg`, `degEquivPiece`, and the graded payoff
   `DJCarrier.degMEquiv : M(U)(m) ≃ₗ U` (modulo `DJAnnEqAn W m`). -/
import VOA.Modules.ZhuVermaAnArchDJCarrierGraded
/- `DJAction`: Dong–Jiang's `𝒱`-action on the BALANCED carrier (`math/0601626` §4, the display just
   before Lemma 4.6) — `u_p(v ⊗ w) = (u ∗^{wt u−p−1+n}_{m,n} v) ⊗ w` for `wt u−1−p+n ≥ 0`, else `0`
   — with BOTH of DJ's well-definedness obligations discharged.  (i) Ideal descent = DJ Lemma 2.8's
   left inclusion, carried as `DJLeftSlot`/`DJActionDescent` and unconditional at `m = 0`
   (`djActionDescent_zero`, off `leftGradingResidual_zero_gen`).  (ii) Balancing = DJ's
   `(u ∗^N_{m,n} v) ∗^N_m a = u ∗^N_{m,n} (v ∗ⁿ_m a)`, unconditional: the defect is the
   `(p₁,p₂,p₃) = (m,n,N)` outer-`𝟙` generator of `O''_{N,m} ⊆ OnmFull` (`djAssocDefect_mem` off
   `bareAssoc_mem_OnmFull`) — the exact payoff of DJ's full ideal.  Proves `djPieceAct`, the mode
   `djMode`, the field `djYM`, and DJ **Lemma 4.6** in full at GENERAL base level `m`:
   `djMode_truncation` (4.6(1)) and `djMode_vacuum`/`djYM_vacuum` (4.6(2)), the latter via the new
   general-`m` vacuum evaluation `anmGen_vacuum_scalar` (`𝟙 ∗^N_{m,n} x = C(n−N−1, n−N)·x`, by
   `cbz_neg_upper` + `ZhuMu.cbz_symm` + `ZhuRes.vandermonde_range`).  Also proves DJ **Lemma 4.7's
   INTERIOR regime** at general base level `m`, unconditional (`anmGen_commutator_interior_gen` on
   representatives, `djPieceAct_commutator_interior` on the balanced piece): two `O''`
   reassociations + DJ 2.8-right transport + the proved unconditional DJ Lemma 2.3
   (`dj23Comm_holds`, whose base level is the middle index, hence `m`-agnostic).  NOT here: DJ 4.7's
   BOUNDARY regimes (they need the undischarged `DJ48Bdry`) and DJ Lemma 4.8 (associativity), so
   `DJCarrier` is NOT shown to be a `WeakModule`. -/
import VOA.Modules.ZhuVermaAnArchDJAction
/- `DJGeneration`: Dong–Jiang **Theorem 4.10's generation clause** on the balanced, full-ideal,
   general-`m` carrier — DJ's one-line argument, ported as one line (NO level induction).  Engine:
   the vacuum in the RIGHT slot of `∗^N_{m,p}` at general base level `m`,
   `mkAnmFull_anmGen_vacuum_right` (`[u ∗^N_{m,p} 𝟙] = C(p−m−1, p−m)·[u]`, every `u`, scalar
   independent of `N`) — the exact mirror of `anmGen_vacuum_scalar`, off the shifted coset calculus
   `mkAnmFull_smul_vacuum_homog` plus `cbz_vandermonde_top` and `cbz_neg_upper`/`ZhuMu.cbz_symm`.
   Specializes to the **unit law** `mkAnmFull_anmRight_vacuum_right` (`[u ∗^N_m 𝟙] = [u]`), which is
   the identity DJ's sentence uses.  ⚠ Certificate `mkAnmFull_anmGenBar_vacuum_offdiag`
   (`[u ∗̄^N_m 𝟙] = 0` for `N ≠ m`) shows DJ's printed `∗̄ⁿ_m` in that sentence is a typo for `∗ⁿ_m`.
   Generation: `djCarrier_generated_by_degM` (a mode-stable `S ⊇ M(U)(m)` is `⊤`), sharpened by
   `djCarrier_generated_by_vacTensor`/`djCarrier_degM_le_span` (`M(U)(m)` is spanned by `𝟙 ⊗ w`,
   unconditionally — Prop. `pa4.5` is NOT needed for generation, only for DJ's `U`-phrasing
   `djCarrier_generated_by_U`).  Hypothesis-free at `m = 0` (`djCarrier_generated_by_degZero`). -/
import VOA.Modules.ZhuVermaAnArchDJGeneration
/- `DJ49Star`: the PURE-`𝒱` statement `(★)` (`DJ49Star`) carrying all of Dong–Jiang Lemma 4.9 (the
   `ℓ < 0` regime of `ModuleIterate`), plus its coefficient machinery: `anmGenZ` (`anmGen` at an
   integer intermediate level), the leftover killer `resFull_offdiag_mem_Onm` /
   `coeffFinsum_offdiag_mem_Onm` (DJ 2.4 at general base level, read coefficientwise), the A-part
   expansion `anmGen_eq_coeff` (`(−1)^s C(a+s,s) = C(−a−1,s)`), the B-part expansion
   `anmGen_swap_coeff_mem` (via `resHom_skew_mod_Onm`), and `dj49_generator_form` — the proved
   `dj49_master` reindexed into the generator basis `j ↦ C(K+n, j+q+n+2+k)`.  `(★)` itself is NOT
   proved: what remains is the closed evaluation of the two coefficient sums. -/
import VOA.Modules.ZhuVermaAnArchDJ49Star
/- `DJ49Iterate`: the OPERATOR transport of Dong–Jiang Lemma 4.9 — `moduleIterate_of_dj49Star`:
   `DJ49Star W → ModuleIterate (muFullRhoU W U)` for EVERY `U : AMod W`.  The `ℓ ≥ 0` half is the
   free `moduleIterate_nonneg`; the `ℓ < 0` half is `(★)` pushed through the linear evaluation map
   `oFullUAt` (`D ↦ o_{q,n}(D)x`), which kills `O_{q,n}(𝒱)` by DJ 2.8 right
   (`oFullU_eq_zero_of_mem`), after `oFullU_comp` (DJ 4.1) has collapsed every mode composition to a
   single mode at the common level `q`.  Four level regimes, as in `muFullMode_commutator_incl`.
   Yields `muFullWeakOfStar : WeakModule W (MUFull W U)` and `muFullLWModuleOfStar`. -/
import VOA.Modules.ZhuVermaAnArchDJ49Iterate
/- `MUBalFullPiece`: the balanced-bottom surgery over Dong–Jiang's GENUINE ideal.  `balancingFull`/`MUPieceBalFull`
   are the `A(𝒱)`-balanced level-`n` pieces `A_{n,0}(𝒱) ⊗_{A(𝒱)} U` on `OnmFull`, and
   `anmGen_anmRight_assoc_mem_OnmFull` (the `(p₁,p₂) = (0,n)` instance of the proved bare DJ
   associator `bareAssoc_mem_OnmFull`) makes `oFullU` preserve the balancing — so the DJ mode
   operators DESCEND, `oBalFullU`, unconditionally, with `oBalFullU_comp` = DJ Lemma 4.1.  Over the
   prime ideal `Onm` this descent is out of reach (DJ Remark 2.10). -/
import VOA.Modules.ZhuVermaAnArchMUBalFullPiece
/- `MUBalFull`: the balanced graded carrier `⨁ₙ A_{n,0}(𝒱) ⊗_{A(𝒱)} U` with `.deg`/`isInternal_deg`
   and the modes `muBalFullMode`/`muBalFullYM` (DJ Lemma 4.6(1)(2)).  STEP 3 (the bottom) carries the
   EXPLICIT Gate hypothesis `hcol : OnmFull W 0 0 ≤ O W` (= `OnmCollapses W 0`, NOT proved here):
   under it `balancingFull_zero_eq_ker` gives `muPieceBalFull0EquivU : M(U)(0) ≃ₗ[ℂ] U` and
   `muBalFullBottomEquivA : M(U)(0) ≃ₗ[A(𝒱)] U` — the `A(𝒱)`-LINEAR bottom that makes `r0` true. -/
import VOA.Modules.ZhuVermaAnArchMUBalFull
/- `DLM3Deg`: the DLM3 §3 degree calculus of `V̂` — `degSpan`, the graded
   bracket `⁅V̂(d), V̂(e)⁆ ⊆ V̂(d+e)` (`deg_bracket_deg`), the deep part `⨁_{p>n} V̂(−p)` and the
   parabolic `P_n` as a `LieSubalgebra` (`Pn`), the lower-truncation engine `gen_eventually_deep`,
   and the vacuum package (`𝟙(m) = 0` for `m ≠ −1`, `𝟙(−1) ∈ P_n`, `𝟙(−1)` central). -/
import VOA.Modules.ZhuVermaAnArchDLM3Deg
/- `DLM3Induced`: DLM3 (4.1)–(4.2) — the induced module `M_n(U) = U(V̂) ⊗_{U(P_n)} U` (`IndMod`, a
   balancing quotient of `U(V̂) ⊗_ℂ U`), its `V̂`-representation by left multiplication (`indRho`),
   the PBW-free generation principle (`ind_generation`, from `uenv_induction`), and the two module
   field properties `ActModeTruncated` (`ind_actModeTruncated`) and `VacuumCreation`
   (`ind_vacuumCreation`).  Corollary: the defect quotient `M̄_n(U)` is a genuine `WeakModule`
   (`indBarWeakModule`).  The level-`n` identification `M̄_n(U)(n) = U` is NOT claimed. -/
import VOA.Modules.ZhuVermaAnArchDLM3Induced
/- `GateB1`: the ANNIHILATION half (B1) of the `(0,0)` gate.  Builds the cross-level zero mode
   `oLev N d` (= Dong–Jiang `o_{n,m}`, `d = m−n`; `oLev N 0 = oMod`, `oLev N (−n) = gMode N n`) and
   proves unconditionally: the level truncation `mode_vanish_of_level` (`M(m) ⊆ Ω_m(M)`), the
   `u`-outside expansion `oLev_resHom_uOutside` (the whole `v`-outside Jacobi family cancels, off
   `resHom_vOutside_coeff_vanish`), the high-pole law `oLev_resHom_vanish`, and hence
   `Onm_annihilates_level` — `O'_{n,m}(𝒱)` kills `M(m)`, whose diagonal case `Onm_annihilates_diag`
   is DJ Thm 4.3 on the graded pieces (= the plan's B0).  B1 itself is REDUCED to the single named
   hypothesis `DJComposition W` (DJ Lemma 4.1) by `gateAnnihilation_of_djComposition`; the anchor
   `djComposition_at_zero` proves its `(0,0,0)` case (= Gannon 5.3.9a). -/
import VOA.Modules.ZhuVermaAnArchGateB1
/- `DLM3Zero`: **DLM3 Proposition 3.1 at `n = 0`** and the level-0 `ParabolicRep`.  Proves Zhu's
   Lemma 2.1.3 `zhu_comm_mod_O` (`u*v − v*u ≡ Res_z (1+z)^{wt u−1} Y(u,z)v mod O(𝒱)`, off the
   proved `resHom_skew_mod_Onm` at `(N,m,P) = (0,0,1)` plus one Pascal step), builds the grade
   projections `gradeComp` and the map `VHat.zhuDeg0 : V̂ →ₗ[ℂ] A(𝒱)` (`a(m) ↦ [π_{m+1}a]`), and
   shows it is a Lie morphism on the parabolic `P₀` (`zhuDeg0_bracket_parabolic`).  Deliverable:
   `VHat.DLM3.parabolicRepOfAMod : AMod W → ParabolicRep W 0 U.carrier` — DLM3 (4.1)'s input datum,
   unconditional at `n = 0`; hence `indBarWeakModule` attaches a weak `𝒱`-module to ANY
   `A(𝒱)`-module, with an `A(𝒱)`-equivariant bottom map (`indBarBottom_zhu_equivariant`).
   Injectivity of that bottom map (DLM3 Thm 4.1) is NOT claimed, nor is `DirectSum.IsInternal` for
   the level grading (DLM3's PBW step).  Pulls `DLM3Admissible`/`DLM3Level` into the build. -/
import VOA.Modules.ZhuVermaAnArchDLM3Zero
/- `DLM3Survival`: **DLM3's radical `J` and the survival of `U` in `M̄_0(U)`** (DLM3 Thm 4.1/4.2's
   closing argument).  Builds `BottomProjection` (DLM3's PBW step, carried as DATA), the radical
   `radical Pr = {v | ⟨u′, x v⟩ = 0 ∀ u′ ∈ U*, x ∈ U(V̂)}` — with `U* = Hom_ℂ(U,ℂ)` separating
   points (`eq_zero_of_forall_dual`), so `J` is `V̂`-invariant (= DLM3 Prop 4.7) and `J ∩ U = 0` is
   free — and the main theorem `survival` / `survival_zero`: modulo `BottomProjection` and
   `DefectPairsToZero` (= DLM3's `U(V̂)W ⊆ J`, their Props 4.3/4.6) the bottom map `U → M̄_0(U)` is
   INJECTIVE, `A(𝒱)`-equivariant, and lands in level 0 ∩ `Ω_0`.  No finiteness on `U` anywhere.
   Unconditional content: `indDefectVec_nonneg` (only `ℓ < 0` matters), `indDefectVec_mem_levCover`
   (the defect is homogeneous ⟹ one mode index survives), `defectPairsToZero_of_bottom_of_stable`
   (generation reduction), and the PBW-free straightening `levCover_eq_posLevel` ⟹
   `levCover_eq_bot_of_neg` (`M_0(U)(d) = 0`, `d < 0`) and `levCover_zero_eq_range`
   (`M_0(U)(0) = 1 ⊗ U`). The later Euler-operator theorem proves level directness
   unconditionally, reducing the `BottomProjection` boundary to bottom injectivity alone. -/
import VOA.Modules.ZhuVermaAnArchDLM3Survival
/- `Gate`: **B3 and the assembly of the `(0,0)` gate** (DJ Prop. 4.6 at `(n,m) = (0,0)`).
   Introduces `AdmLev` — a weak module plus a level family vanishing in negative degrees, strictly
   weaker than `OrdVModule` (no internality, no finiteness, no `L₀` condition) — and RE-PROVES the
   whole unconditional part of B1 over it (`oLevW`, `modeW_vanish_of_lev`,
   `oLevW_resHom_uOutside`, `oLevW_resHom_vanish`, `OnmW_annihilates_lev/_diag`).  This is not
   cosmetic: B1's `OrdVModule` carries `finrank`, so it cannot be instantiated at the
   (infinite-dimensional) regular module `U = A(𝒱)` that B3 needs, and B2's `M̄_0(U)` is a weak
   module anyway.  Unconditional bonuses: `admLevOfLowestWeight` (so `DJCompositionLev` IMPLIES
   B1's `DJComposition`), `oLevW_zhuMul_lev_zero` / `djCompositionLev_at_zero` (the `(0,0,0)`
   anchor, `OrdVModule`-free), `levBar_eq_bot_of_neg` (`M̄_0(U)(d) = 0` for `d < 0`).
   `gate_of_realization` = B3, and `gateRealizationOfSurvival` = the B2 → B3 bridge, giving
   `gate_of_dj_and_dlm3 : OnmFull W 0 0 = O W` from EXACTLY three named inputs —
   `DJCompositionLev` (DJ Lemma 4.1), `BottomProjection` (DLM3's PBW step, data) and
   `DefectPairsToZero` (DLM3's `U(V̂)W ⊆ J`).  The gate itself is NOT proved; every downstream
   consumer (`DJAnnEqAn W 0`, `anmFullDiagEquivZero`, `djPieceMEquivZero`,
   `djCarrierDegZeroEquiv`) takes it as an explicit hypothesis. -/
import VOA.Modules.ZhuVermaAnArchGate

/- `ZhuVermaAnArchZeroModeLaw`: **THE ZERO-MODE LAW** on the bottom `Ω(M)` of a **weak**
   module (no grading, no level family, no `finrank`):
   `o(u *ⁿ_{m,p} v) w = u₍wt u−1+e₎ v₍wt v−1−e₎ w`, `e = p − n`, INDEPENDENT of `m`
   (`oOmega_anmGen_law`; bundled grade-free form `oOmega_anmGen_law'`).  The single binomial
   cancellation is `alt_cbz_shift_vanish` (`∑_j (−1)^j C(N,j) C(j−q,i) = 0`, `i < N`); the
   `u`-outside family then Vandermonde-collapses (`zeroModeCoeff_collapse`) and the outer
   Dong–Jiang weights give a Kronecker delta at `d = e` (`zeroModeOuter_collapse`).
   Corollaries: `e < 0 ⟹ 0` (`oOmega_anmGen_vanish_of_lt`); `e = 0 ⟹ o(u)o(v)`
   (`oOmega_anmGenBar_mult`, Zhu multiplicativity for the WHOLE DJ family); **B0**
   `Onm_diag_annihilates_Omega` — `O_p(𝒱)` annihilates the bottom for every `p` (DJ Thm 4.3 at the
   bottom, a COROLLARY of the law via `anmCirc_eq_anmGen`), and `O_annihilates_Omega` at `p = 0`;
   `djCompositionLev_base` = DJ Lemma 4.1 at `(n,m) = (0,0)` for every `p`.
   NOT proved: `DJCompositionLev` at general `(n,m)` (a different, `D = m−n` statement), hence NOT
   the gate. -/
import VOA.Modules.ZhuVermaAnArchZeroModeLaw

/- `ZhuVermaAnArchGateB1Ann`: **B1, unconditional** — the annihilation half of the `(0,0)` gate.
   Closes the gap left by `ZhuVermaAnArchZeroModeLaw` (whose `D = 0` law on `Ω(M)` is NOT
   Dong–Jiang Lemma 4.1, which is a `D = m−n` statement on `M(m)`).  The `u`-outside expansion
   `oLevW_resHom_uOutside` was already proved at general `(D,s,m)`; the only obstruction was the
   hypothesis `0 ≤ d` on the two scalar collapses, whereas on `M(m)` the surviving `u`-mode offsets
   are `d ≥ D − m = −n`.  Both collapses are re-proved on exactly that range
   (`zeroModeCoeff_collapse_range`, `zeroModeOuter_collapse_low` — the latter's bound is SHARP:
   at `m = e = p = 0`, `d = −1` the identity fails).  Deliverables:
   `oLevW_resHom_law_lev` (the level-`m` residue law), `oLevW_anmGen_law_lev` = **DJ Lemma
   4.1** `o_{n,m}(a *ⁿ_{m,p} b) w = o_{n,p}(a) o_{p,m}(b) w`, hence
   `djCompositionLev_holds : DJCompositionLev W` and `djComposition_holds : DJComposition W` — the
   named hypotheses of `ZhuVermaAnArchGate` / `ZhuVermaAnArchGateB1` are THEOREMS.
   The two sharp statements reducing B1 are proved as `B1AssocInner`/`B1Level` with proofs
   `b1AssocInner_holds` / `b1Level_holds` (every depth `p₃`, not just `p₃ = 0`), and B1 itself is
   `gateAnnihilationLev_holds : GateAnnihilationLev W` (plus `gateAnnihilation_holds`).
   Consequently `gate_of_dlm3` reduces the `(0,0)` gate to just TWO named inputs —
   `BottomProjection` and `DefectPairsToZero`, both Dong–Li–Mason §4 at `n = 0` (B2).
   The gate itself is NOT proved;
   no PBW, no `finrank`, no `L₀`, no module grading beyond the bare `AdmLev` level family. -/
import VOA.Modules.ZhuVermaAnArchGateB1Ann

/- `ZhuVermaAnArchDefectDerivation`: the representation-independent engine of DLM3 Lemma 4.5 —
   `defectVec_Lneg1_left : δ(L₋₁a, b, x, ℓ, N) = −ℓ · δ(a, b, x, ℓ−1, N)`, valid in every
   `V̂`-representation — together with `defectVec_vacuum_left` (the `a = 𝟙` defect vanishes),
   the two binomial absorption identities `cbz_mul_sub` / `cbz_mul_index`, the `resFull` Pascal
   recursion and the resulting Zhu-product splitting `zhuMul_eq_resFull_sum`, and the
   degree-complementary bracket class `zhuDeg0_bracket_gen_complement`. Unconditional. -/
import VOA.Modules.ZhuVermaAnArchDefectDerivation

/- `ZhuVermaAnArchDLM3PBWSplit`: DLM3 §4's PBW input as an EXPLICIT NAMED HYPOTHESIS
   `PBWFreeness` (freeness of `U(V̂)` over `U(P_n)` / the Harish–Chandra split), never an axiom.
   Level independence is unconditional (`levCover_iSupIndep`), so only bottom injectivity
   remains in general. Concrete adjoint and Heisenberg instances are axiom-free; the general
   project wrapper specializes the relative-induction field of
   the theorem `VOA.pbw : PBWPrinciple`, including at
   `regularAMod`. The historical two-field package yields
   `DirectSum.IsInternal (levCover P)` and, at `n = 0`, the degree-`0` projection
   `BottomProjection` are THEOREMS. The spanning half is already PBW-free
   (`levCover_zero_eq_range`), so this is the irreducible PBW residue. -/
import VOA.Modules.ZhuVermaAnArchDLM3PBWSplit
import VOA.Modules.ZhuVermaAnArchDLM3PBWIndependence
import VOA.Modules.ZhuVermaAnArchDLM3BottomProjectionBoundary
import VOA.Modules.ZhuVermaAnArchDLM3PBWAxiom
import VOA.Modules.ZhuVermaAnArchDLM3AdjointBottom

/- `ZhuVermaAnArchDLM3Prop43`: **DLM3 Proposition 4.3 at `n = 0`** — the bottom of `M_0(U)`
   pairs to zero. Unconditionally, the bottom iterate defect VANISHES in every level `≤ 0`
   (`indDefectVec_bottom_level_le`); the `ℓ = −1` core `indDefectVec_bottom_neg_one` is exactly the
   `A(𝒱)`-module axiom `o(a)o(b)u = o(a∗b)u` on `U`, and `indDefectVec_bottom_negPole` (DLM3
   Lemma 4.5) propagates it to every negative pole. With the PBW-supplied projection this gives
   `proj_indDefectVec_bottom` for all `a, b ∈ 𝒱`. The residual to `DefectPairsToZero` is exactly
   DLM3 Props 4.6/4.7, carried as the named `BottomPropagates` / `OrbitPropagates`. -/
import VOA.Modules.ZhuVermaAnArchDLM3Prop43

/- `ZhuVermaAnArchGateB3`: **B3 and the closed `(0,0)` gate**. The regular-module
   instantiation `o(x)·[𝟙] = [x ∗ 𝟙] = [x]` (`regularAMod_rho_one_chain`) turns B1's annihilation
   into `x ∈ O(𝒱)` (`mem_O_of_oLevW_vanish_at_one`); with B1 unconditional the gate needs only a
   realization of `U = A(𝒱)` (`gate_of_realization_uncond`). `gate_of_pbw` closes
   `OnmFull W 0 0 = O W` on exactly TWO named inputs — `PBWFreeness` and DLM3's
   `DefectPairsToZero` (equivalently `gate_of_pbw_props` with DLM3 Props 4.6/4.7 displayed).
   The gate re-assembles through the combinatorial generator families
   (`onmFull_zero_zero_eq_O_via_gens`) and discharges every downstream consumer:
   `DJAnnEqAn W 0`, `OnmFull W 0 0 = OnFull W 0`, `AnmFull W 0 0 ≃ A_0(𝒱) ≃ A(𝒱)`,
   `djPieceMEquiv`, `DJCarrier.degMEquiv` (the bottom of `M(U)` is `U`). The gate is NOT claimed, only
   reduced. -/
import VOA.Modules.ZhuVermaAnArchGateB3

/- `ZhuVermaAnArchDLM3Pairing`: the **S0 / S1 / S2** audit of DLM3 §4 at `n = 0`, plus the
   consolidation of what remains. S0 is discharged (`ParabolicRep.act` is a bundled `LieHom`;
   `parabolicRepOfAMod_act_lie`, on Zhu 2.1(iii) via `mk_resFull_eq_zhuMul_sub`); S1/S2 are the
   proved `indDefectVec_bottom_neg_one` / `_negPole` of `DLM3Prop43`. New:
   `defectPairsToZero_iff_proj_defectSubmodule` turns DLM3's `U(V̂)W ⊆ J` into the submodule
   inclusion `defectSubmodule ≤ ker π₀` (so DLM3 Prop 4.7 is NOT an independent input), and
   `projKills_iff_bottomPropagates_and_orbitPropagates` shows the single `Prop`
   `ProjKillsDefectSubmodule` is equivalent to the PAIR (DLM3 Prop 4.6, DLM3 Prop 4.7).
   Also: the bottom base case has content only at STRICTLY POSITIVE level
   (`indDefectVec_bottom_mem_radical_of_homog`, `defectPairsToZero_of_bottom_pos_of_stable`).
   `gate_of_pbw_projKills` restates the gate on the consolidated residual. `ProjKillsDefectSubmodule` is
   carried, never assumed. -/
import VOA.Modules.ZhuVermaAnArchDLM3Pairing

/- `ZhuVermaAnArchDLM3Propagate`: the **S3 + S4** slice — DLM3 Props 4.6 and 4.7 at `n = 0`.
   Both are proved (`bottomPropagates_of_modeShift`, `orbitPropagates_of_modeShift`) from ONE
   representation-level, PBW-free, `U`-free input `VHatRep.DefectModeShift` (DLM2 Prop 6.1 at the
   canonical pole `ℓ = −1`). `defectSubmodule_eq_dOneSpan`: the plain span of the `ℓ = −1`
   defects is already `V̂`-invariant, so DLM3 Prop 4.7 costs nothing extra;
   `proj_defect_neg_one_top`: DLM3 Prop 4.6 by a LEVEL argument that is cheap at `n = 0` (below
   level `0` the defect vanishes, at level `0` it lies in `1 ⊗ U` where `π₀` is injective, above
   level `0` a non-negative mode keeps it there) — the DLM2 induction's troublesome `π₀(x·δ)` term
   has no content. Also proved: the `ℓ`-reduction `defectVec_mem_dOneSpanAt` and the
   normal-ordered toolkit (`defectVec_neg_one_eq`, `gsum_succ`, `actMode_comm_vec`, the hockey
   stick `gsum_sub_gsum_zero` and the `a`-slot shift law `sumR_sub_gsum_shift`). `DefectModeShift`
   is CARRIED, never assumed silently; no axiom is declared. `gate_of_pbw_modeShift` states the
   `(0,0)` gate on exactly two named inputs (independent `regularAMod` bottom injectivity via
   `PBWFreeness`, plus `DefectModeShift`). -/
import VOA.Modules.ZhuVermaAnArchDLM3Propagate

/- `ZhuVermaAnArchDLM3Survive`: **B2 ASSEMBLED — the gate conditional on `BottomProjection`**.
   `defectModeShift_of_truncated` **PROVES** `VHatRep.DefectModeShift` (DLM2 Prop 6.1 at the
   canonical pole `ℓ = −1`) for every truncated `V̂`-representation, from `gsum_actMode_shift`
   (pushing `c₍ₖ₎` through the normal-ordered sum, `pterm`/`qterm_actMode_shift`), the proved
   `a`-slot shift law `sumR_sub_gsum_shift`, and `vlevel_cancel` (the `𝒱`-level commutator
   `[c₍ₜ₎, a₍₋₁₎]`, whose content is `cbz_subsetOfSubset` plus the triangle reindex
   `finsum_triangle_reindex`, `t = q + r`). Hence `defectPairsToZero_of_bottomProjection`:
   DLM3's `U(V̂)W ⊆ J` at `n = 0`, for a GENERAL `U : AMod W`, with no hypothesis beyond the
   projection; `indBarBottom_injective_of_bottomProjection` (`U` survives, DLM3 Thm 4.1 at
   `n = 0`); and `gate_of_pbwDatum` : `OnmFull W 0 0 = O W` whose ONLY hypothesis is the
   explicit datum `BottomProjection (parabolicRepOfAMod W (regularAMod W))`. The project-level
   witness `voaPBWBottomProjection` derives this instance from the generic relative-induction field
   of the theorem `VOA.pbw : PBWPrinciple`. The
   downstream consumers (`DJAnnEqAn W 0`, `OnmFull W 0 0 = OnFull W 0`, `OnmCollapses W 0`,
   `AnmFull W 0 0 ≃ A_0(𝒱)`, `djPieceMEquiv`, `DJCarrier.degMEquiv` = the bottom of `M(U)` is `U`,
   DJ Thm 4.10's generation sentence) are restated on that one hypothesis. NO new axiom and NO
   `sorry`; the declarations remain conditional on the explicit hypothesis (which `#print axioms`
   does not report). -/
import VOA.Modules.ZhuVermaAnArchDLM3Survive

/- `ZhuVermaAnArchDefectModeShift`: an **INDEPENDENT second proof** of `VHatRep.DefectModeShift`
   (DLM2 Prop 6.1 at the canonical pole `ℓ = −1`), written concurrently with — and unaware of —
   `ZhuVermaAnArchDLM3Survive`'s `defectModeShift_of_truncated`.  Every declaration carries a
   `_dms` suffix where it would otherwise clash; nothing in the earlier file was touched.
   ⚠ THIS FILE IS A DUPLICATE RESULT — Fedor's call whether to keep it (as a cross-check of the
   gate's keystone) or drop it.  Different proof route: the `𝒱`-level double sum is collapsed by
   `vandermonde_column` — a single `ℤ`-shift `t = j + r` (`finsum_comp_equiv (Equiv.addLeft j)`)
   feeding `cbz_subsetOfSubset`, with the `r < 0` terms killed on BOTH sides — rather than by a
   triangle reindex over `ℕ × ℕ`; and the two halves of `G` are handled once through the combined
   summand `gterm` (`gsum_eq_finsum_gterm`) instead of twice.  Proved: `pterm_modeShift`,
   `qterm_modeShift`, `gterm_modeShift`, `gsum_modeShift` (the `G`-shift law, Step B),
   `vandermonde_column`, `stepA_dms` (Step A), `defectModeShift_of_truncated_dms`,
   `defectModeShift_indRho`, and the gate `gate_of_pbw_only` conditional on the independent
   `BottomProjection` datum.
   THE IDENTITY WAS ENGINE-VERIFIED BEFORE FORMALIZATION:
   0 mismatches in 25 920 (free boson, symbolic `λ`) + 3 969 (Virasoro, symbolic `c`, `h`)
   instances at `ℓ = −1`, in NON-module `V̂`-representations (the DLM3 induced modules — on an
   honest VOA module every defect is identically `0` and the test would be vacuous), with the `V̂`
   derivative relation imposed, exact termination bounds, and all five sharpness controls failing
   loudly.  ⚠ ENGINE FINDING: the same identity is FALSE at a general pole `ℓ ≠ −1`; only the
   canonical pole is claimed.  NO axiom, NO `sorry`. -/
import VOA.Modules.ZhuVermaAnArchDefectModeShift

/- `DJ48BdryHolds`: **`dj48Bdry_holds : DJ48Bdry W`** — the last undischarged pure-`𝒱` leaf under
   DJ Lemma 4.7 (DJ's `la4.8`, printed Lemma 4.9), from the proved `dj48_case1`; plus its mirror
   `DJ48BdryB`/`dj48BdryB_holds` (from `dj48_case2`).  On top of them, DJ **Lemma 4.7 on the
   balanced carrier `DJCarrier` in ALL FOUR REGIMES**, at general base level `m`:
   `anmGen_commutator_bdry{A,B}_gen` (representatives), `djPieceAct_eq_of_repr_mem` (descent onto
   all of `M(U)(n)`), `djPieceAct_commutator_{interior,bdryA,bdryB}_all`, and the operator identity
   `djMode_commutator` / `djMode_commutator_gen` (arbitrary, non-homogeneous `a, b`) :
   `[a_p, b_q] = ∑ᵢ C(p,i)(a₍ᵢ₎b)_{p+q−i}` on `M(U)`, hypothesis-free at `m = 0`
   (`djModeZero_commutator`, `djModeZero_commutator_gen`).  Only carried input:
   `DJActionDescent W m` (a theorem at `m = 0`).  ⚠ The repo's `DJ48Bdry` encodes only DJ's FIRST
   mixed regime; the second is the new `DJ48BdryB`.  NOT here: DJ Lemma 4.8
   (associativity/iterate), so `DJCarrier` is still not a `WeakModule`.  No axiom, no `sorry`. -/
import VOA.Modules.ZhuVermaAnArchDJ48BdryHolds

/- `DJCarrierIterate` (C2): **`(★)` IS A THEOREM** — `dj49StarPrime_holds` / `dj49Star_holds`
   discharge the pure-`𝒱` membership that `ZhuVermaAnArchDJ49Star` / `…DJ49Iterate` carried as a
   hypothesis, so Dong–Jiang Lemma 4.9 (`ModuleIterate`, `ℓ < 0`) is unconditional.  Route:
   the alternating Dong–Jiang sums collapse to a single residue family (`dj49c2_collapse`, via the
   triangular reindex `dj49c2_triangle` + the Vandermonde `dj49c2_inner_vand`), skew symmetry
   (`resHom_skew_mod_Onm`) converts the `v`-first family into `u`-modes at the uniform sign
   `(−1)^P`, and one scalar identity (`dj49c2_scalar`, from `dj49c2_S1`/`dj49c2_S2`) exhibits the
   leftover as a combination of the high-pole generators killed by `resFull_offdiag_mem_Onm`.
   Downstream, unconditionally: `moduleIterate_muFullRhoU`, `muFullWeakU_uncond` (⚠ the `⊗_ℂ`
   cover `MUFull`, not the balanced carrier), and — on the **balanced** `DJCarrier` at base level
   `0` — `djPieceAct_comp_zero` (DJ Lemma 4.1 on `M(U)(n)`, from `bareAssoc_mem_OnmFull`),
   `djPieceAct_eq_zero_of_mem`, `djModeZero_iterate_incl` and `djModeZero_iterate_neg`
   (`(u₍ℓ₎v)₍N₎ = ∑ᵢ (−1)ⁱC(ℓ,i)(u₍ℓ₋ᵢ₎v₍N₊ᵢ₎ − (−1)^ℓ v₍ℓ₊N₋ᵢ₎u₍ᵢ₎)` for all `u, v` and all
   `x ∈ M(U)`).  ⚠ NOT here: the `ℓ ≥ 0` half on `DJCarrier` — `moduleIterate_nonneg` needs a
   `VHat.VHatRep`, and none is built on `DJCarrier`; so `DJCarrier` is still not a `WeakModule`.
   Axiom-clean, pbw-free, no `sorry`. -/
import VOA.Modules.ZhuVermaAnArchDJCarrierIterate

/- `DJCarrierWeak`: **`DJCarrier` IS a `WeakModule`.**  The `ℓ ≥ 0` half of `ModuleIterate` on
   the balanced carrier needs a `VHat.VHatRep`; this file builds one.  `djActGen_hderiv` is the `L₋₁` translation relation
   `(L₋₁a)₍ₘ₎ + m·a₍ₘ₋₁₎ = 0` on `DJCarrier` (from the proved `anmGen_Lgen_acting_mem`, DJ Lemma
   2.8's right inclusion at the grading generator); `djActGen_bracket` is the proved
   `djModeZero_commutator_gen` in `assembleModeData` form; together they give
   `djRhoZero : VHatRep W (DJCarrier W U)` with `actMode a m = djModeZero W U m a`.  Hence
   `moduleIterate_nonneg` applies and, with `djModeZero_iterate_neg`, yields the full
   `moduleIterate_djRhoZero`; `isModuleJacobi_of_iterate` + `weakModuleOfRep` then give
   `djCarrierWeak W U : WeakModule W (DJCarrier W U)` with **zero carried hypotheses** (no PBW
   datum, no `DJAnnEqAn`, no `DJ48Bdry`, no `LeftGradingResidual`).  Graded packaging:
   `djCWeight`/`djCWeight_isInternal`/`djCWeight_isLow`/`djCWeight_boundedBelow` are unconditional;
   `GradedLWWeakModule` is `OrdVModule` + lowest weight MINUS the `finrank` field — deliberately, since
   `OrdVModule.finrank` is FALSE for the infinite-dimensional bottoms (e.g. `U = A(𝒱)`) the bijection
   ranges over — and `djGradedLW` carries only the grading scalar `hL0` and the bottom `hbot`.
   Bottom: `djCarrierWeak_bottom_equiv` / `djCarrier_deg_zero_ne_bot` / `djGradedLW_of_pbwDatum`
   thread the explicit assumption `BottomProjection (parabolicRepOfAMod W (regularAMod W))`
   and the `AModScope` scoped `Nontrivial U.carrier` explicitly. The project-level witness
   `voaPBWBottomProjection` derives this instance from the generic relative-induction field of
   `VOA.pbw`. The proof terms are `#print axioms`-clean and do not use `pbw`, but are
   conditional on that explicit datum;
   no `sorry`. -/
import VOA.Modules.ZhuVermaAnArchDJCarrierWeak

/- `LUGraded` (C5 layer 1): the whole graded-submodule / maximal-`J` / irreducible-quotient layer,
   rebuilt over the **finrank-free** `GradedLWWeakModule` (the `OrdVModule`-typed ancestors —
   `ZhuVermaAnArchL0Semisimple`, `ZhuVermaAnArchVModQuotGraded`, `ZhuVermaAnArchLumax`,
   `ZhuVermaAnArchGameTwo` — cannot be used, since `OrdVModule.finrank` is false at the scope the
   bijection needs).  unconditional: `submodule_isGraded` (`L₀`-semisimplicity: *every* weak
   submodule of a graded weak module is graded, no finiteness), `maxJ` (the supremum of all
   bottom-trivial graded submodules), `maxJ_isGraded`, `maxJ_bottom_disjoint` — a **THEOREM**
   here, whereas the `OrdVModule` track carried it as the hypothesis `MaxJData.sup_bottom_disjoint` —
   the graded quotient `GradedLWWeakModule.quotient`, `comapQuot`/`comapQuot_isGraded`, `LU = M/J`,
   `LU_bottom_equiv` (`L_h ≅ M_h`), `le_maxJ_of_bottom_disjoint`, `maxJ_ne_top` and
   `eq_maxJ_of_maximal` (uniqueness of the irreducible quotient).  Carried, and *only* here:
   the two named `Prop`s `GeneratedByBottom` and `BottomIrreducible`, out of which
   `LU_isIrreducible` is proved.  ⚠ DLM3 Lemma 4.8 / DJ Thm 4.16 prove simplicity of `L(U)`
   from complete reducibility of `M(U)` and are valid only for RATIONAL `V`; that argument is
   deliberately NOT imported — the route here is the maximal-graded-proper-submodule quotient and
   uses no rationality, no complete reducibility and no finite-dimensionality.
   Axiom-clean, pbw-free, no `sorry`. -/
import VOA.Modules.ZhuVermaAnArchLUGraded

/- `LU` (C5 layer 2): `J(U)`, `L(U) = M(U)/J(U)` and its irreducibility for Dong–Jiang's balanced
   `M(U) = ⨁ₙ A_{n,0}(𝒱) ⊗_{A(𝒱)} U`, with **both** inputs of layer 1 discharged.
   `djGeneratedByBottom` is DJ Thm 4.13's generation sentence off the proved
   `djCarrierWeak_generated_by_bottom`; `djBottomIrreducible` comes from simplicity of `U` through
   `djCarrierWeak_bottom_equiv_rho` — the new statement that the bottom identification
   `M(U)(0) ≅ U` is `A₀(𝒱)`-EQUIVARIANT (DJ's "isomorphic `A_m(V)`-modules"; not only the
   `ℂ`-linear half).  Also `AMod.toAmModZero` / `anFullZeroEquiv` — the
   bridge `AMod W → AmMod W 0` (`OnFull W 0 = O(𝒱)`, `leftProd W 0 = zhuMul`) — and
   `IsSimpleAmMod` / `isSimpleAmMod_toAmModZero`.  Main results: `djJ`, `djLU`,
   `djLU_isIrreducible`, `djLU_bottom_U` with `djLU_bottom_U_rho` (`L(U)(0) ≅ U` as
   `A₀(𝒱)`-modules = the round trip), and `djJ_unique`. Carried, all displayed: the explicit
   `BottomProjection` datum `Pr`, the `AModScope` scope (`Nontrivial U.carrier`,
   `IsSimpleAmMod U`) and the grading scalar
   `hL0`.  ⚠ The OTHER bijection direction (`P ≅ L(P_h)` for irreducible `P`) is reduced by
   `eq_maxJ_of_maximal` to the universal property of `M(U)` (DJ Thm 4.13's second half), which is
   NOT built and NOT asserted; its two ingredients DJ Lemma 4.1 / Corollary 4.2 at general indices
   ARE already theorems (`djCompositionLev_holds`, `oLevW_anmGen_law_lev`,
   `oLevW_anmRight_law_lev`), and what is missing is the off-diagonal `(n,0)` descent of `o_{n,0}`
   through `OnmAssoc`/`OnmLevel` (proved only at `(0,0)`, `gateAnnihilationLev_holds`). The
   project-level `regularAMod` witness is `voaPBWBottomProjection`, derived from the generic
   relative-induction field of the theorem `VOA.pbw : PBWPrinciple`. Proof-term `#print axioms`-clean and `pbw`-free, but conditional on `Pr`; no `sorry`. -/
import VOA.Modules.ZhuVermaAnArchLU
/- `GateAnnN0`: the OFF-DIAGONAL `(n,0)` ideal-descent `oLevW_OnmFull_n0_vanish_uncond` — the zero mode
   `o_{n,0}(x)` of every `x ∈ O_{n,0}(𝒱)` annihilates the bottom level of any non-negatively levelled
   weak `𝒱`-module (`O'` via `OnmW_annihilates_lev`, `O''`/`O'''` via DJ Lemma 4.1 + the proved
   `n`-independent `oLevW_assocInner_vanish`/`OnmW_annihilates_diag`). unconditional (`djCompositionLev_holds`).
   This is the analytic core of the M(U) universal property (DJ Thm 4.13 second half): well-definedness of
   `φ̄([v]⊗w) = o_{n,0}(v)·φ(w)` against `O_{n,0}(𝒱)`. Axiom-clean, pbw-free. -/
import VOA.Modules.ZhuVermaAnArchGateAnnN0
/- `OffDiagDescent`: the GENERAL off-diagonal `(n,m)` ideal-descent `oLevW_OnmFull_vanish_nm` (o_{n,m}(x)
   kills level m for x ∈ OnmFull W n m), and its `(n,0)` instance `oLevW_OnmFull_n_zero_vanish` (the
   universal-property input). Index-generalizes the (0,0) proofs via the proved general DJ Lemma 4.1
   (`djCompositionLev_holds`) + `OnmW_annihilates_lev`/`_diag`. Subsumes GateAnnN0's (n,0) form.
   Axiom-clean, pbw-free. -/
import VOA.Modules.ZhuVermaAnArchOffDiagDescent
/- `UnivMap`: the descended zero-mode maps built ON the (n,0) ideal-descent — scaffolds for the M(U)
   universal property (DJ Thm 4.13 second half). `oLevAnmFullDescend A L n hw : A_{n,0}(𝒱) →ₗ M`
   ([v] ↦ o_{n,0}(v)·w, well-defined by the (n,0) descent, lands in L.lev n), and the ⊗_ℂ-cover map
   `oLevCoverMap A L n φ hφ : A_{n,0}(𝒱) ⊗ X →ₗ M` ([v]⊗x ↦ o_{n,0}(v)·(φ x)) for a bottom embedding
   φ : X →ₗ M. The A_{n,0}(𝒱)-linear building blocks of φ̄; the remaining ⊗_{A(𝒱)}-balancing (DJ Cor
   4.2) descends the cover to DJ's balanced piece. Axiom-clean, pbw-free. -/
import VOA.Modules.ZhuVermaAnArchUnivMap
/- `LUUniversal`: DJ Thm 4.13 SECOND HALF — the induced map `φ̄ = oLevUnivMap A L U φ` is a WEAK-MODULE
   MAP. `oLevUnivMap_intertwine` : φ̄(aₚ·x) = aₚ·φ̄(x) ∀ a p x, ported line-by-line from DJ's proof
   (djMode_apply_tmul + DJ Lemma 4.1 `oLevW_anmGen_law_lev` + the mode identity o_{N,n}(u)=uₚ), extended
   over levels (DirectSum + djPiece_ext) and over a (reduce_homogeneous). The deep content of the M(U)
   universal property. Axiom-clean, pbw-free. -/
import VOA.Modules.ZhuVermaAnArchLUUniversal
/- `LUUniversalIrr`: DJ Thm 4.13 second half SPECIALIZED to an irreducible target P. `pPhiBar P :
   M(Ω(P)) → P` — DJ's induced map φ̄ for P (A=P.isMod.toWeakModule, L=admLevOfLowestWeight,
   U=Ω(P).toAmModZero, φ=bottom inclusion; hφact = the bottom action actA IS the zero mode oLevW A 0,
   via actA_mk_apply_coe + oLevW_zero_eq_oMod). `pPhiBar_intertwine` = it's a weak-module map. Toward
   `realizesIrr` (P ≅ L(Ω(P)) via surjectivity + ker=J). The base map is unconditional; the later
   bottom-triviality/kernel declarations carry the explicit `regularAMod` `BottomProjection`
   hypothesis `Pr`. Proof-term clean and `pbw`-free, but conditional where `Pr` appears. -/
import VOA.Modules.ZhuVermaAnArchLUUniversalIrr
/- `LURealizesIrr`: `realizesIrr` — every irreducible `P` is `L(Ω(P))` (DJ Thm 4.13).  `φ̄` is
   surjective (`pPhiBar_surjective`) with `ker φ̄ = J(Ω(P))` (`pPhiBarKer_eq_djJ` via `djJ_unique` +
   bottom-triviality + maximality), so the first-isomorphism theorem gives `pRealizesLWIso :
   LWModule.Iso W ((djLU …).toLWModule hfin) P`. Carries the explicit `BottomProjection` datum
   `Pr`, whose project-level witness is `voaPBWBottomProjection`, plus `hU`, `hL0`, `hfin`.
   Proof-term `#print axioms`-clean and `pbw`-free, but conditional on `Pr`; no
   existing file mutated. -/
import VOA.Modules.ZhuVermaAnArchLURealizesIrr
/- `LUFiniteWeights`: TASK A — `hfin` is DERIVABLE, not an additional carried hypothesis. `pFiniteWeights` proves
   `(djLU …).FiniteWeights` for irreducible `P` by transporting `P.isMod.finrank` across the LINEAR
   equivalence `pRealizesLinEquiv` (which does NOT take `hfin`) — it intertwines `L₀`
   (`pRealizesLinEquiv_act`), so maps `L(Ω(P))_α` into the finite-dim `P_α`; `mem_weight_of_L0op_eq`
   (`L₀`-eigenvector ⟹ weight vector, general `GradedLWWeakModule`) supplies the containment.
   `pFiniteWeights` still carries the explicit `regularAMod` `BottomProjection` hypothesis `Pr`;
   proof-term clean and `pbw`-free does not make it unconditional. -/
import VOA.Modules.ZhuVermaAnArchLUFiniteWeights
/- `LUFunctorial`: TASK B core (`hfin`-free) — functoriality of `M(·)` in its bottom.  `djFunctorEquiv
   U₁ U₂ e : M(U₁) ≅ M(U₂)` (`= ⨁ₙ id ⊗ e`, well-def against the DJ balancing via `e`'s `ρ`-intertwine,
   `djFunctorCover_maps_balancing`); `djFunctorEquiv_natural` — it intertwines `djModeZero` (the
   action touches factor 1, `e` factor 2).  `amModHomOfBottomEquiv` bridges an `AModEquiv` of bottoms to
   the `AmModHom` data.  Mirrors the MU-track `MU.functorEquiv`.  Axiom-clean, pbw-free. -/
import VOA.Modules.ZhuVermaAnArchLUFunctorial
/- `LUIsoInvariant`: TASK B `J`-naturality + descent.  `djFunctorEquiv_maps_djJ` — `M(e)` carries
   `J(U₁)` onto `J(U₂)` (`J = maxJ` canonical: transported submodule is bottom-trivial + `≤ maxJ` both
   ways, `transported_le_djJ`).  `djLUFunctorLinEquiv` descends `M(e)` to `L(U₁) ≅ L(U₂)` (linear).
   Carries `(Pr, hU, h, hL0)`; the project-level `regularAMod` witness is
   `voaPBWBottomProjection`, derived from the generic relative-induction field of
   `VOA.pbw`. Proof-term `#print axioms`-clean and `pbw`-free, but conditional on `Pr`. -/
import VOA.Modules.ZhuVermaAnArchLUIsoInvariant
/- `Zhu534`: the FINAL ASSEMBLY of `Function.Bijective (forwardMapIrr W)` at the irreducible scope.
   `forwardMapIrr_surjective_uncond` — surjectivity of the faithful forward map carries **no**
   hypothesis (the codomain `IrrAMod W` is the image predicate `IsBottomOfIrr`, so this is a
   tautology of the statement, NOT Zhu's surjectivity; it does show the `InducedAssignment`/`hirr`
   arguments of `InducedAssignment.forwardMapIrr_surjective` are unnecessary).
   `forwardMapIrr_bijective_iff_rigidity : Function.Bijective (forwardMapIrr W) ↔
   IrredBottomRigidity W` — the bijection is EQUIVALENT to Zhu's irreducible uniqueness, so
   `forwardMapIrr_bijective_of_rigidity` consumes the provably minimal hypothesis (the repo's
   `FaithfulScorecard`/`GeneratedFromBottom` route factors through it).  Also the scoped universal
   property `GeneratedFromBottomIrr` (indexed by `IrrAMod W` only, weaker than
   `InducedAssignment.GeneratedFromBottom`) with `irredBottomRigidity_of_universalIrr` and the
   converse `generatedFromBottomIrr_of_rigidity`.
   The C5 bridge: `GradedLWWeakModule.FiniteWeights` / `toOrdVModule` / `toLWModule` /
   `toLWModule_isIrreducibleLW` — the finrank-free C5 layer enters the `LWModule` chain through
   exactly one named datum, the `OrdVModule.finrank` field; plus `bottom_equivariance_of_homog`
   (homogeneous-mode equivariance ⟹ full `o(u)`/`rhoLW` equivariance), the packaged
   `IrrRealization W U`, `SimpleAModsRealized`, and the codomain-fidelity
   `isBottomOfIrr_iff_isSimpleAMod` (`IrrAMod W` really is `Irr A(𝒱)`).
   Dong–Jiang's `L(U)` wired in: `djLU_bottom_U_oMod`, `djLU_bottomAModEquiv`,
   `djIrrRealization`, `djLU_isBottomOfIrr` (carrying only `Pr`, `hU`, `hL0`, `hfin`, `hsimple`).
   ⚠⚠ REFUTATION `not_nonempty_inducedAssignment` / `not_nonempty_faithfulScorecard` /
   `not_forall_hasInducedModule`: `InducedAssignment W` is UNINHABITED (`realize` is total on
   `AMod W`, but `zeroAMod W` has a subsingleton carrier while every `LWModule` bottom is
   nontrivial), so every bijection theorem consuming one — `InducedAssignment.forwardMapIrr_
   bijective`, `FaithfulScorecard.bijectiveIrr`, `zhuBijectionIrr_scorecard`, `zhuBijection_*` —
   is VACUOUS as typed, and `ZhuInducedPointwise`'s `∀ U, HasInducedModule W U` is false.
   ⚠ `Function.Bijective (forwardMapIrr W)` is NOT unconditional: the exact abstract residual is
   `IrredBottomRigidity W` = `GeneratedFromBottomIrr W`, i.e. the universal property of `M(U)`,
   which C5 did NOT build. Section 6's DJ realizations additionally carry the explicit
   `regularAMod` `BottomProjection` hypothesis `Pr`. Proof-term clean and `pbw`-free, but
   conditional where those parameters appear; no `sorry`. -/
import VOA.Modules.ZhuVermaAnArchZhu534
/- `HL0`: TASK C — the `L₀`-grading of `M(U)` for a bottom `Ω(P)`.  `pHL0 P : ∀ n x ∈ deg n,
   djModeZero W (pBotAmMod P) 1 ω x = (P.h + n) • x` — via DJ Lemma 2.3 (`dj23Comm_holds`) + the grading
   generator `anmLgen` (`resExp 1 ω v = L₋₁v + L₀v`) + the bottom `ω`-scalar `lowestAMod_omegaScalar`.
   No `BottomProjection` parameter (an unused `Pr` was removed, register entry 60); the same core for
   an arbitrary `U` is `Modularity.HL0Scoped.genHL0`. -/
import VOA.Modules.ZhuVermaAnArchHL0
/- `LUBijection`: CONDITIONAL CAPSTONE — `zhuBijective Pr : Function.Bijective (forwardMapIrr W)` (Zhu 5.3.4
   faithful form).  Assembles `DJRealizationFamily W` = ⟨`djK = L(Ω(·))`, `realizes` (`pRealizesLWIso`),
   `isoInvariant` (`djLUFunctorLWIso'` + `pH_eq`)⟩; `hfin` derived (`pFiniteWeights`), `hL0` discharged
   (`pHL0`). Sole remaining input = the explicit `BottomProjection` assumption `Pr`; its
   project-level witness is `voaPBWBottomProjection`, derived from the generic relative-induction
   field of the theorem `VOA.pbw : PBWPrinciple`. Its proof term
   is `#print axioms`-clean [propext, Classical.choice, Quot.sound], sorry-free, and does not use
   `pbw`; the theorem is nevertheless conditional on `Pr`. -/
import VOA.Modules.ZhuVermaAnArchLUBijection
import VOA.Modules.ZhuVermaAnArchLUBijectionPBW
import VOA.Modules.C2ImpliesZhuFinite
import VOA.Modules.NilpotentGenerators
import VOA.Modules.PoissonTrace
import VOA.Modules.QuasiLisseFinite
import VOA.Modules.SuperZhuRing
import VOA.Modules.SuperZhuResidue
import VOA.Modules.SuperZhuRightIdeal
import VOA.Modules.SuperZhuAssociator
import VOA.Modules.SuperZhuRingDischarge

import VOA.Modules.LogTensorContraNilModes
import VOA.Modules.LogTensorContraL0Exp

import VOA.Modules.LogTensorPzEvaluation

import VOA.Modules.LogTensorPzReconstruction

import VOA.Modules.LogTensorPzMaximal
import VOA.Modules.LogTensorPzHomFinite
import VOA.Modules.LogTensorUniformNil
import VOA.Modules.LogModuleC1Cofinite
import VOA.Modules.LogTensorPzPointPostcompose
import VOA.Modules.LogTensorPzPointPrecompose
import VOA.Modules.LogTensorUnitCreation
import VOA.Modules.SelfDualContragredient

/-!
# Representation theory

"The raison d'être of VOAs are their modules" (Gannon §5.3). This is the algebraic
meaning of Moonshine.

* `WeakModule`     — the ungraded weak module (Li / Dong–Li–Mason) and the `ℂ`-graded
  `OrdVModule` (Gannon Def. 5.3.1c).  ⚠ Gannon's Def. 5.3.1 defines **two** notions, not three,
  and his "weak" module is already the `ℕ`-graded one — see `AdmissibleModule`.
* `AdmissibleModule` — the `ℕ`-gradable weak module (Zhu §1.4; Dong–Li–Mason Def. 2.2; **and**
  Gannon Def. 5.3.1 "weak"), and `AdmissiblyRational`: every admissible module is completely
  reducible.  A leaf file, so `Rationality` can state Gannon Def. 5.3.2 over it.
* `Character`      — the graded dimension `χ_M(τ)` (5.3.2) and the one-point function
  `χ_M(τ, v)` (5.3.13).
* `Rationality`    — `V`-modules, `GannonRational` (Def 5.3.2) and holomorphic VOAs,
  Lemma 5.3.3, and the module-level map of the whole rationality lattice with every
  implication tagged PROVED-HERE or CITED.  ⚠ No predicate is named `WeaklyRational`: that name
  inverts its meaning, and Gannon's third clause must be transcribed over his `ℕ`-graded weak
  modules, not over the ungraded `WeakModule`.
* `AdmissibleRationality` — the Zhu-algebra-facing half of the standard notion:
  `ZhuAdmissibleSemisimple` (DLM Math. Ann. 310 Thm 8.1(a); J. Algebra 206 Thm 4.10(a)), the
  `OrdVModule → AdmissibleModule` comparison, and the positive witness generator
  `admissiblyRational_of_span_vacuum`.
* `C2Cofinite`     — `O₂(𝒱)`, the Poisson algebra `A₂(𝒱)`, and `C₂`-cofiniteness
  (Def 5.3.5).
* `RationalityLattice` — the implication lattice between `AdmissiblyRational`, `Regular`
  (Dong–Li–Mason, Adv. Math. **132** (1997), Def. 3.1) and `GannonRational`.  Defines
  `Regular` — *every **weak** module completely reducible*, the honest referent of the phrase
  "weakly rational" and the **strongest** notion here.  Proves `ordinary ⟹ admissible` in full
  generality, hence Gannon clause (1); proves `Φ(𝒱) ↪ Φadm(𝒱)`; carries the Dong–Li–Mason,
  Abe–Buhl–Dong and H. Li theorems as **named, cited hypotheses** (one `def` each, never
  axioms) and chains them to `AdmissiblyRational ⟹ GannonRational` — with **no**
  `C₂`-cofiniteness, once clause (3) is stated over the category Gannon Def. 5.3.1 actually
  uses.
* `StronglyRational` — the two literature bundles that sit on top of the lattice:
  `StronglyFinite` (Creutzig–Gannon, arXiv:1605.04630v1, §2.2: *simple `C₂`-cofinite VOA of
  CFT-type with `V ≅ V∨`*) and `StronglyRational` (Dong–Mason, arXiv:math/0201318v1, §3;
  McRae, arXiv:2108.01898v3, §2.2: that plus `AdmissiblyRational`).  ⚠ Its self-duality
  conjunct is `VertexOperatorAlgebra.SelfDual` — *a nondegenerate fully invariant bilinear
  form*, McRae §2.2 clause (2)'s own "equivalently" — **not** `Contragredient.SelfContragredient`,
  which this file **proves vacuous** (`selfContragredient_of_ordVModule`: every `OrdVModule` is
  linearly isomorphic to its graded dual).  Proves Dong–Mason's equivalence
  *self-dual ⟺ strong CFT type* (`selfDual_iff`), documents that CFT type is discharged by the
  ambient VOA4 fields, resolves the duplicate `IsSimple`, and supplies the witness generator
  `stronglyRational_of_span_vacuum`.
* `ZhuAlgebra`     — Zhu's associative algebra `A(𝒱)` (5.3.8) and Theorem 5.3.4: a
  bijection between irreducible `A(𝒱)`-modules and irreducible `𝒱`-modules.
* `Fusion`         — the fusion product `M ⊠ N`, fusion coefficients, the fusion ring
  (5.3.3), and the quantum dimension (5.3.12).
* `Contragredient` — the restricted dual `M*` (5.3.4a) and unitary modules (5.3.5).
-/

