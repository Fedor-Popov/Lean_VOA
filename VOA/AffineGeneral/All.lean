/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.VARec
import VOA.AffineGeneral.LieData
import VOA.AffineGeneral.Currents
import VOA.AffineGeneral.Grading
import VOA.AffineGeneral.SugawaraField
import VOA.AffineGeneral.WordFields
import VOA.AffineGeneral.SugawaraCurrentCov
import VOA.AffineGeneral.SugawaraResidue
import VOA.AffineGeneral.Reconstruction
import VOA.AffineGeneral.Assembly
import VOA.AffineGeneral.GradedFields
import VOA.AffineGeneral.SugawaraEnergy
import VOA.AffineGeneral.Virasoro
import VOA.AffineGeneral.Sl3Instance
import VOA.AffineGeneral.Casimir
import VOA.AffineGeneral.Simple
import VOA.AffineGeneral.WeightOne
import VOA.AffineGeneral.SimpleQuotient
import VOA.AffineGeneral.SimpleAffineQuotient
import VOA.AffineGeneral.DeligneInstance
import VOA.AffineGeneral.A2General
import VOA.AffineGeneral.SlnSimple
import VOA.AffineGeneral.CartanLatticeSimple
import VOA.AffineGeneral.E8Dimension
import VOA.AffineGeneral.E8Deligne
import VOA.AffineGeneral.RootEnum
import VOA.AffineGeneral.RootCounts
import VOA.AffineGeneral.LatticeDeligne
import VOA.AffineGeneral.LatticeKilling
import VOA.AffineGeneral.LatticeNormalization
import VOA.AffineGeneral.SCLie
import VOA.AffineGeneral.SCSimple
import VOA.AffineGeneral.G2Lie
import VOA.AffineGeneral.F4Lie
import VOA.AffineGeneral.E6Lie
import VOA.AffineGeneral.SCLieData
import VOA.AffineGeneral.E6LieData
import VOA.AffineGeneral.Singular
import VOA.AffineGeneral.SingularQuad
import VOA.AffineGeneral.SCSingular
import VOA.AffineGeneral.LiPresentation

/-!
# The universal affine VOA `V^k(𝔤)` for general `𝔤`

Umbrella for `VOA/AffineGeneral/`.  Main results: `VOA.AffineGeneral.affineVOA` (any Lie data),
`universalAffineVOA` / `killingAffineVOA` (every simple `𝔤`, no further hypotheses); concrete simple
`𝔤` = `sl_n` (`SlnSimple`) and the lattice algebras `a2Lie d4Lie e6Lie e7Lie e8Lie` (`CartanLatticeSimple`);
`dim 𝔢₈ = 248` (`E8Dimension`) and the Deligne case `E₈` on `L_{-6}(𝔢₈)` (`E8Deligne`);
root counts / dimensions of `D₄ E₆ E₇` (`RootCounts`) and their Deligne cases (`LatticeDeligne`);
the standard normalization `Killing/(2h∨)` (roots of length 2) for each (`LatticeNormalization`);
`𝔤₂` from checked structure constants (`SCLie`, `SCSimple`, `G2Lie`) and `𝔣₄` (`F4Lie`) with their
Deligne cases.
-/
