/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LeechLatticeVOA
import VOA.Moonshine.LatticeInvolution
import VOA.Moonshine.PlusWeightOne
import VOA.Moonshine.TwistedHeisenberg
import VOA.Moonshine.PlusWeightTwo
import VOA.Moonshine.ExtraspecialModule
import VOA.Moonshine.LatticeGradedDim
import VOA.Moonshine.HeisenbergTwistedModuleL0
import VOA.Moonshine.TwistedSectorDim
import VOA.Moonshine.HeisenbergTwistedModuleInstance
import VOA.Moonshine.Character
import VOA.Moonshine.LatticeTwistedVertex
import VOA.Moonshine.FrameCount
import VOA.Moonshine.FrameTwisted
import VOA.Moonshine.CyclicFrameSectors
import VOA.Moonshine.TForm
import VOA.Moonshine.TrialityTheta
import VOA.Moonshine.FrameBridgeGolay
import VOA.Moonshine.LatticeTwistedModule
import VOA.Moonshine.LatticeTwistedAssoc
import VOA.Moonshine.TwistedPlus
import VOA.Moonshine.SkewLeech
import VOA.Moonshine.InvFormTP
import VOA.Moonshine.VnatFields
import VOA.Moonshine.VnatCarrier
import VOA.Moonshine.Generation
import VOA.Moonshine.WbarLeech
import VOA.Moonshine.NondegLeech
import VOA.Moonshine.CyclicTwisted
import VOA.Moonshine.VnatGenuine
import VOA.Moonshine.TTBlock
import VOA.Moonshine.VnatAxioms
import VOA.Moonshine.M8h0Gap
import VOA.Moonshine.M8h0VPBlock
import VOA.Moonshine.SimpleVnat
import VOA.Moonshine.Main
import VOA.Moonshine.TrialityTwSigma
import VOA.Moonshine.SigmaExistZhu
import VOA.Moonshine.SigmaExistLeech
import VOA.Moonshine.ZhuGenGround
import VOA.Moonshine.ZhuGenV0
import VOA.Moonshine.SigmaTopOffdiag
import VOA.Moonshine.GroundLattice
import VOA.Moonshine.ZhuGenerated
import VOA.Moonshine.M8hKey
import VOA.Moonshine.SigmaKeyTop
import VOA.Moonshine.SigmaTop2TTOct
import VOA.Moonshine.SigmaTop2Bridge
import VOA.Moonshine.KeySkewBlock
import VOA.Moonshine.SigmaAssemble
import VOA.Moonshine.FZGenV3
import VOA.Moonshine.MainTopPairs
import VOA.Moonshine.TopPairs
import VOA.Moonshine.JAnalyticQExpansion

/-!
# The Moonshine module construction

Umbrella for the construction of `V♮ = V_Λ^+ ⊕ (V_Λ^T)^+`.  The Leech lattice is imported from
the vendored `VOA/LatticesAndCodes` files (from *Lattices and Codes*).

## Construction steps

Module docstrings under `VOA/Moonshine/` refer to the steps of the construction by the labels
below.

* **M1** — the Leech lattice VOA `V_Λ` (`LeechLatticeVOA`).
* **M2** — the lattice involution `θ` and the fixed-point VOA `V_Λ^+` (`LatticeInvolution`).
* **M3** — `(V_Λ^+)₁ = 0` (`PlusWeightOne`).
* **M4** — the `θ`-twisted Heisenberg algebra and its Fock module `S[θ]` (`TwistedHeisenberg`).
* **M5** — the extraspecial module `T` (`ExtraspecialModule`).
* **M6** — the `θ`-twisted module `V_Λ^T = S[θ] ⊗ T` (twisted vertex operators and the twisted
  Jacobi identity); **M6a** is its Heisenberg part (`HeisenbergTwistedModule*`), **M6c** the
  twisted vertex operators `Y^T(e^α, z)` and their locality
  (`LatticeTwisted{Exp,EOps,TwoPoint,Vertex}`; the other `LatticeTwisted*` files belong to M6).
* **M7** — graded dimensions: **M7a** weight two, **M7b** the lattice VOA and its `θ`-fixed part,
  **M7c** the twisted sector, **M7d** the character identity: graded dimensions equal the
  coefficients of the formal series `JShift` (`q·J`, `J = j − 744`); the analytic link to `j` is
  `hasSum_JShift`.
* **M8** — the vertex operator of `V♮ = V_Λ^+ ⊕ (V_Λ^T)^+`: **M8a** `(V_Λ^T)^+` as a
  `V_Λ^+`-module; **M8b** the skew intertwiner `W`; **M8c** its adjoint `W̄` and the invariant
  forms; **M8d** the carrier and block fields; **M8e** the Golay frame decomposition;
  **M8f** cyclicity of the frame sectors; **M8g** the triality `σ` (**M8g-0**: the sublattice
  bridge `V_{N(A₁²⁴)} ⊇ V_{Λ₀} ⊆ V_Λ`, giving `golayV0 ≅ V₀⁺`); **M8h** twisted × twisted
  locality (`htt`), whose open half is DGM (4.23) (**M8h-0**: the proved half (4.22), skew-symmetry
  of `W̄`, and the reduction of (4.23) to four frame pairs); **M8i** the VOA axioms of `V♮`.
* **M9** — the assembled theorem `Moonshine.moonshine` (`TopPairs`), which has no hypotheses: a
  VOA structure on `Vnat` with the block map `Ynat wbarL`, `c = 24`, `V₁ = 0`, `dim V₂ = 196884`,
  graded dimensions equal to the coefficients of the formal series `JShift`, and simple.  It
  obtains M8h through the triality route: `moonshine_of_topPairs` → `moonshine_of_keySkew` →
  `moonshine_of_top` → `M8hKey.moonshine_of_sigma`, with the last input `topPairs_one`.
  `Main` (`moonshine_of_frameLocality`) and `MainTopPairs` keep conditional forms of M9.  Not
  claimed: a Monster action, holomorphy or rationality, uniqueness, or an isomorphism with FLM's
  explicit `V♮` (the twisted × twisted block here is the form-adjoint `W̄`).
* **R-gen** — Zhu generation of `V₀⁺` by its weight-two part (`zhuGenerated_weightTwo`); it feeds
  the twisted half of M8g.

Files that describe M8h as open, or take `htt` or `TPBlockLocal` as a hypothesis, refer to the
direct route to DGM (4.23).  On the triality route `M8hKey` derives (4.23) from the triality data
and the residual `SigmaKey`; these are discharged by `SigmaAssemble`, `SigmaKeyTop`, the
Frenkel–Zhu reduction `FZKey.keySkew_of_FZ` and `topPairs_one`.  The "conditional" status line of
`M8hKey` describes that file in isolation.
-/
