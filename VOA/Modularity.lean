/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.OnePointFunctions
import VOA.Modularity.SquareBracketWitt
import VOA.Modularity.SquareBracketVirasoro
import VOA.Modularity.GelfandFuks
import VOA.Modularity.SquareBracketGrading
import VOA.Modularity.Schwarzian
import VOA.Modularity.ChiralBlock
import VOA.Modularity.ZhuRecursion
import VOA.Modularity.ChangeCoord
import VOA.Modularity.EisensteinFormal
import VOA.Modularity.SqWeightSpanning
import VOA.Modularity.ZhuRecursionProof
import VOA.Modularity.LambertSeries
import VOA.Modularity.ZhuNormalization
import VOA.Modularity.GradedTrace
import VOA.Modularity.ZhuAssembly
import VOA.Modularity.SquareBracketSubst
import VOA.Modularity.ZhuTheorem
import VOA.Modularity.ConvergenceBridge
import VOA.Modularity.ExpLogBinomial
import VOA.Modularity.ZhuCoefficientIdentity
import VOA.Modularity.ZhuRecursionClose
import VOA.Modularity.GrowthBound
import VOA.Modularity.BlockSpanning
import VOA.Modularity.ZhuBlockConditions
import VOA.Modularity.MoonshineCorollary
import VOA.Modularity.JFunction
import VOA.Modularity.JacobiCharacter
import VOA.Modularity.Twisted
import VOA.Modularity.LiFiltration
import VOA.Modularity.OrderedSpan
import VOA.Modularity.BuhlSpanningProof
import VOA.Modularity.OrderedMonomialBridge
import VOA.Modularity.BuhlSpanningData
import VOA.Modularity.C2Extraction
import VOA.Modularity.BuhlSpanningC2
import VOA.Modularity.TraceIndependence
import VOA.Modularity.TraceNonvanish
import VOA.Modularity.C2GradedVanishing
import VOA.Modularity.TraceSpanningS
import VOA.Modularity.SquareBracketC2
import VOA.Modularity.BlockFiniteness
import VOA.Modularity.JInvariantAnalytic
import VOA.Modularity.TEigenInjective
import VOA.Modularity.EisensteinBridge
import VOA.Modularity.QEvalHolomorphic
import VOA.Modularity.SerreDerivative
import VOA.Modularity.QEvalConv
import VOA.Modularity.EisensteinAnalytic
import VOA.Modularity.QEvalLinear
import VOA.Modularity.AnalyticBlock
import VOA.Modularity.BlockSlash
import VOA.Modularity.GradedBlock
import VOA.Modularity.RhoS
import VOA.Modularity.BlockDeterminacy
import VOA.Modularity.JacobiZhu
import VOA.Modularity.MoonshineFromBlocks
import VOA.Modularity.OnePointGrowth
import VOA.Modularity.OnePointDescent
import VOA.Modularity.BlockSpace
import VOA.Modularity.BlockRank
import VOA.Modularity.BlockFiniteDim
import VOA.Modularity.SlashAmbientObstruction
import VOA.Modularity.SemisimpleTrace
import VOA.Modularity.SymmetricFunctionals
import VOA.Modularity.BlockZeroMode
import VOA.Modularity.SqAmbientAssembly
import VOA.Modularity.CuspFunctionalCount
import VOA.Modularity.CuspDegeneration
import VOA.Modularity.CuspLimit
import VOA.Modularity.FormalSpecialization
import VOA.Modularity.MinimalClosure
import VOA.Modularity.BlockTranslation
import VOA.Modularity.WedderburnSimples
import VOA.Modularity.EisensteinCuspLimit
import VOA.Modularity.GrowthClosure
import VOA.Modularity.LevelOneStructure
import VOA.Modularity.CuspPoint
import VOA.Modularity.BlockRelSpanning
import VOA.Modularity.AModBridge
import VOA.Modularity.WedderburnAMod
import VOA.Modularity.SimpleAModFinite
import VOA.Modularity.LowestWeightExistence
import VOA.Modularity.TraceGrowthReduction
import VOA.Modularity.ZhuAlgebraFinite
import VOA.Modularity.ZhuCount
import VOA.Modularity.ZhuCountC2
import VOA.Modularity.ConformalWeightChoice
import VOA.Modularity.E46Point
import VOA.Modularity.FamilyIndexing
import VOA.Modularity.BlockRelSpanE
import VOA.Modularity.BlockRelSpanTransport
import VOA.Modularity.ZhuBlockCount
import VOA.Modularity.BlockBoundC2
import VOA.Modularity.SqAmbientRank
import VOA.Modularity.CharIndependence
import VOA.Modularity.LeadingCoeff
import VOA.Modularity.BottomCharacter
import VOA.Modularity.QEvalShift
import VOA.Modularity.SqWeightNat
import VOA.Modularity.CharIndependenceAMod
import VOA.Modularity.Majorant
import VOA.Modularity.SubexpClosure
import VOA.Modularity.QEvalLinearity
import VOA.Modularity.FibreIndependence
import VOA.Modularity.ZhuModularityFibre
import VOA.Modularity.IndicialRecursion
import VOA.Modularity.IndicialGrowth
import VOA.Modularity.OnePointODE
import VOA.Modularity.ZhuModularityODE
import VOA.Modularity.FormalODE
import VOA.Modularity.QConvModule
import VOA.Modularity.QExpansionBridge
import VOA.Modularity.SubexpSeriesRing
import VOA.Modularity.BlockRelSpanG
import VOA.Modularity.FormalBlockFinite
import VOA.Modularity.QDerivProductRule
import VOA.Modularity.ZhuODEAssembly
import VOA.Modularity.UniCollapse
import VOA.Modularity.BlockSystem
import VOA.Modularity.SystemGrowth
import VOA.Modularity.BlockGrowth
import VOA.Modularity.BlockFiniteEtingof
import VOA.Modularity.AKModularODE
import VOA.Modularity.AKUniformODE
import VOA.Modularity.EisensteinRamanujan
import VOA.Modularity.AKMLDE
import VOA.Modularity.AKSl2Payoff
import VOA.Modularity.ZhuModularityC2
import VOA.Modularity.C2Corollaries
import VOA.Modularity.AKZhuModularity
import VOA.Modularity.AKSl2Instance
import VOA.Modularity.HL0Scoped
import VOA.Modularity.OmegaCentral
import VOA.Modularity.RealizationAssembly
import VOA.Modularity.AnFiniteDim
import VOA.Modularity.Anm0FiniteDim
import VOA.Modularity.RealizationCofinite
import VOA.Modularity.ZhuModularitySurface
import VOA.Modularity.StrictSpanning
import VOA.Modularity.ZhuModularityGN
import VOA.Modularity.GNLemma7
import VOA.Modularity.ZhuModularityPinned
import VOA.Modularity.GNWords
import VOA.Modularity.GNInduction
import VOA.Modularity.GNReach
import VOA.Modularity.GNBlock
import VOA.Modularity.GNStep
import VOA.Modularity.GNSwap
import VOA.Modularity.GNGradeZero
import VOA.Modularity.GNHighHead
import VOA.Modularity.GNSortingLink1
import VOA.Modularity.GNLink0Closure
import VOA.Modularity.GNLink2Representatives
import VOA.Modularity.GNLink3Migration
import VOA.Modularity.GNLink4RepeatedHead
import VOA.Modularity.GNLevelOne
import VOA.Modularity.GNBoundedReach
import VOA.Modularity.GNProp8Closure
import VOA.Modularity.GNProp8PBW
import VOA.Modularity.ZhuStronglyRational
import VOA.Modularity.ZhuModularityRational
import VOA.Modularity.EisensteinSerreClosure
import VOA.Modularity.MoonshineHauptmodul
import VOA.Modularity.SqModeLinear
import VOA.Modularity.SqGradedBlock
import VOA.Modularity.SqModeWeight
import VOA.Modularity.SqGradedBlockSlash
import VOA.Modularity.SqSlashBridge
import VOA.Modularity.GammaThetaStatement
import VOA.Modularity.SlashSubgroup
import VOA.Modularity.ThetaGroup
import VOA.Modularity.PseudoTrace
import VOA.Modularity.LogarithmicQSeries
import VOA.Modularity.LogarithmicPseudoTraceRealization
import VOA.Modularity.LogarithmicPseudoTraceBlock
import VOA.Modularity.LogarithmicPseudoTraceRecursion
import VOA.Modularity.TraceSpace
import VOA.Modularity.SuperIntegral
import VOA.Modularity.HalfIntegralGridFoundations
import VOA.Modularity.SuperSpinQuasiLisseAlgebra
import VOA.Modularity.ZhuModularityCanonical
import VOA.Modularity.AKGradingInstance
import VOA.Modularity.AKGradingTotal
import VOA.Modularity.AKMLDEUnconditional

/-!
# Modularity

"The next four subsections mark a climax for the book" (Gannon §5.3.3). The graded
dimensions of the irreducible modules of a nice VOA carry a representation of
`SL₂(ℤ)`.

* `OnePointFunctions` — change-of-coordinate operators `T_f` and the Schwarzian
  (5.3.15), the squared modes `L[n]` (5.3.16), the torus partition function, and the
  `n`-point chiral blocks (5.3.17).
* `ZhuTheorem`        — **Zhu's modularity theorem 5.3.8**: a `C₂`-cofinite weakly
  rational VOA yields an `SL₂(ℤ)`-representation `ρ` on the span of one-point
  functions. The abstract `V♮`-type/hauptmodul implication is available; the concrete
  `χ_{V♮} = J` is proved in `VOA/Moonshine/` by a direct character computation, not through
  this theorem.
* `JacobiCharacter`   — Jacobi characters `χ^J_M(τ, v, w)` (Def 5.3.7) and their
  transformation law, Theorem 5.3.9 (5.3.20)–(5.3.21).
* `Twisted`           — `g`-twisted modules (5.3.22), the trace functions
  `𝒵(M, h; τ)` (5.3.23), orbifolds `𝒱^G` (proved to be VOAs), and Conjecture 5.3.10.
* `EisensteinAnalytic`/`QEvalLinear`/`AnalyticBlock`/`BlockSlash`/`GradedBlock`/`RhoS`/
  `BlockDeterminacy` — **the analytic half of Zhu's `S`-law**: `zhuGC j = (−B_{2j}/(2j)!)·E_{2j}`
  is Mathlib's modular form for `j ≥ 2` (`slashC_zhuGC`) and `(2πi)⁻²·G₂` for `j = 1`
  (`zhuGC_one`); the trace functions are honest holomorphic genus-one blocks
  (`torusOnePoint_isAnalyticBlock`); condition (ii) loses its `G₂` and condition (iii) becomes a
  **Serre-derivative equation** (`omega_serre`); hence the block space is `SL₂(ℤ)`-stable
  (`isGradedBlock_blockSlash`) and `TraceSpanning`/`zhu_modularity` follow from the single spanning
  statement `BlockSpannedByTraces` — or, on the cheaper route, from `SlashSpannedAtS`, the same
  statement for the `S`-slashes only (`Modularity/RhoS`).  `BlockDeterminacy` ports Zhu's finiteness
  to the analytic side, adds finite generation over the Eisenstein ring, `∂`-stability, and the
  identity theorem on the connected `imGT 0`; `OnePointGrowth`/`OnePointDescent` reduce the
  general-`v` growth datum to the `g + 1` `C₂`-generators (convolution preserves subexponential
  growth, so Zhu's `[−2]`-identity propagates it up the filtration); `BlockSpace`/`BlockRank` make
  the blocks a `ℂ`-space and show that, the trace blocks being independent,
  `BlockSpannedByTraces` **is** the numerical bound `dim_ℂ 𝔅 ≤ #Φ(𝒱)`
  (`blockSpannedByTraces_of_rank_le`, `zhu_modularity_of_finrank_le`);
  `MoonshineFromBlocks` reaches Gannon's Question 5.3.4 — for a holomorphic `c = 24` VOA the
  character is `SL₂(ℤ)`-invariant as soon as `dim 𝔅 ≤ 1`.
* `JacobiZhu` — the `A = T` slice of Theorem 5.3.9 (unconditional) and its `v = 0` slice (from
  Zhu's law), which pin the convention of `JacobiTransformation` from both sides.
* `ZhuRecursionClose` — Zhu's recursion `zhuRecursionPinned_holds` (with
  `ExpLogBinomial`, `ZhuCoefficientIdentity`); `ZhuBlockConditions` — the trace functions are
  genus-one conformal blocks (`torusOnePointHom_isFormalBlock`).
* `GrowthBound`       — the convergence wall reduced to Buhl's ordered spanning set;
  `LiFiltration`/`OrderedSpan`/`BuhlSpanningProof`/`OrderedMonomialBridge`/`BuhlSpanningData`/
  `C2Extraction`/`BuhlSpanningC2` — Li's `C₂`-filtration, the straightening (bubble-sort)
  theorem and the graded descent, delivering `orderedSpanningData_adjoint_of_C2Cofinite`
  (Gaberdiel–Neitzke for `𝒱` itself, **unconditional**) and `buhlSpanningOn_of_C2Cofinite`
  (the module case, modulo the finite lowest-weight bottom family of Buhl §3–4);
  `C2GradedVanishing` — `exists_grading_le_O₂`, Buhl's Remark 3.5 (`⊕_{i≥N}𝒱ᵢ ⊆ C₂(𝒱)`),
  stated without proof in his paper, proved here from the gradedness of `O₂`.
* `BlockSpanning`     — `zhu_modularity_of_spanning` for every `A ∈ SL₂(ℤ)` from the two named
  spanning data; `TraceIndependence` — `traceIndependent_of_tEigen_injective` discharges the
  *second* datum from the `T`-eigenvalues `e^{2πi(hᵢ−c/24)}` being distinct (Lagrange isolation
  applied to the moment equations `Σⱼ λⱼᵏ cⱼSⱼ = 0`), leaving `TraceSpanning` alone; `TraceNonvanish` — `traceIndependent_of_orderedSpanning`, the
  same with the nonvanishing hypothesis discharged from the growth bound (the character is
  nonzero at `τ = it` because its coefficients are dimensions with a positive leading one); `MoonshineCorollary` — Question 5.3.4 and `χ` `SL₂(ℤ)`-invariant for `V♮`-type VOAs.
-/
