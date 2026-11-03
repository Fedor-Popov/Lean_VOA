/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.DeformationCentralModes
import VOA.Core.DeformationIteration
import VOA.Core.DeformationLiftedModes
import VOA.Core.DeformationPoleForm
import VOA.Core.DeformationReconstruction
import VOA.Core.DeformationCurrentModes

import VOA.Core.VertexAlgebra
import VOA.Core.VertexOperatorAlgebra
import VOA.Core.SuperVertexAlgebra
import VOA.Core.SuperVertexOperatorAlgebra
import VOA.Core.SuperGoddard
import VOA.Core.OPE
import VOA.Core.Identities
import VOA.Core.Fields
import VOA.Core.Goddard
import VOA.Core.BareVA
import VOA.Core.Dong
import VOA.Core.FieldOps
import VOA.Core.LocalSystem
import VOA.Core.FieldCombinatorics
import VOA.Core.LocalSystemBare
import VOA.Core.LocalSystemAction
import VOA.Core.FieldProductIterate
import VOA.Core.LocalSystemJacobi
import VOA.Core.LocalSystemRegular
import VOA.Core.DongSuper
import VOA.Core.DongSuperNeg
import VOA.Core.Reconstruction
import VOA.Core.ReconstructionExistence
import VOA.Core.SuperCovariant
import VOA.Core.SuperVOASubalgebra
import VOA.Core.SuperEvenPart
import VOA.Core.VOASubalgebraGenerated
import VOA.Core.SuperNearVOA
import VOA.Core.SuperReconstruction
import VOA.Core.Skew
import VOA.Core.FLM
import VOA.Core.WeakAssoc
import VOA.Core.SkewSymmetry
import VOA.Core.SuperSkew
import VOA.Core.SuperWeakAssoc
import VOA.Core.Commutativity
import VOA.Core.CommutativeRing
import VOA.Core.BilinearForm
import VOA.Core.InvariantFormSymmetry
import VOA.Core.InvariantFormFHL
import VOA.Core.LieAlgebraV1
import VOA.Core.V1LieAlgebra
import VOA.Core.Automorphism
import VOA.Core.GriessAutomorphism
import VOA.Core.AutFromGenerators
import VOA.Core.InnerAutomorphism
import VOA.Core.BorcherdsIdentity
import VOA.Core.Borcherds
import VOA.Core.SuperTranslationCovariance
import VOA.Core.SuperNthProduct
import VOA.Core.SuperBorcherdsIdentity
import VOA.Core.SuperBorcherds
import VOA.Core.InvariantFormDiagonal
import VOA.Core.InvariantFormPStep
import VOA.Core.InvariantFormFHLClosure
import VOA.Core.InvariantFormTranspose
import VOA.Core.InvariantFormCanonical
import VOA.Core.InvariantFormAdjoint
import VOA.Core.InvariantFormCanonicalFHL
import VOA.Core.InvariantFormCanonicalVir
import VOA.Core.InvariantFormCanonicalPStep
import VOA.Core.InvariantFormQPMatch
import VOA.Core.QuasiPrimaryDecomp
import VOA.Core.InvariantFormQPMatchGen
import VOA.Core.InvariantFormFHL2
import VOA.Core.InvariantFormDelimitation
import VOA.Core.Deformation
import VOA.Core.DeformedForm
import VOA.Core.QuotientVOA
import VOA.Core.BRSTCohomology
import VOA.Core.ScreeningKernel
import VOA.Core.SingularVector
import VOA.Core.TensorVOA
import VOA.Core.TensorFieldLift
import VOA.Core.InternalGradingOperator
import VOA.Core.WeightCommutatorField
import VOA.Core.DeformationGraded
import VOA.Core.WeightOneCohomology
import VOA.Core.InvariantFormRadical
import VOA.Core.GradedFormMatrix
import VOA.Core.JacobiLocal
import VOA.Core.RigidityBridge
import VOA.Core.SimpleImage
import VOA.Core.NonlinearConformal
import VOA.Core.NonlinearVirasoro
import VOA.Core.NonlinearZeta
import VOA.Core.NPExtension
import VOA.Core.NonlinearMR
import VOA.Core.VAPresentation
import VOA.Core.PresentationDoctrine
import VOA.Core.RealStructure
import VOA.Core.GoodFiltration
import VOA.Core.GoodFiltrationQuotient
import VOA.Core.GradedUnitarity
import VOA.Core.FlagMinors
import VOA.Core.MinorPivots
import VOA.Core.GlobalConformalTowers
import VOA.Core.HermitianSchur
import VOA.Core.RealSymmetricTwo
import VOA.Core.LinearFiltration
import VOA.Core.TranslationCovariant
import VOA.Core.GenuineVertexAlgebra

/-!
# Core theory (Phases 1–2)

The definitions and the easy consequences of the axioms (Gannon §5.1.3, §5.2.1).

* `PreVertexAlgebra`            — Definition 5.1.3(a): axioms VA1–VA5.
* `VertexOperatorAlgebra`    — Definition 5.1.3(b): conformal vector `ω`, axioms
  VOA1–VOA4; and the near-VOA of 5.1.3(c).
* `BorcherdsIdentity`        — the Jacobi identity (5.1.7a), the Borcherds identity
  (5.1.7b) and its specialisations: the commutator (5.1.7c) and iterate (5.1.7d)
  formulae.
* `Identities`               — the translation operator `T = L₋₁` (5.1.8),
  skew-symmetry `Y(u,z)v = e^{zT} Y(v,-z)u`, and the associativity/duality formulae
  (5.1.9).
* `Commutativity`            — Theorem 5.1.4: a commutative vertex algebra is the
  same as a commutative associative unital algebra with a derivation.
* `BilinearForm`             — the invariant bilinear form (5.1.11)–(5.1.12).
* `LieAlgebraV1`             — zero-modes `o(u)` and the Lie algebra structure on
  `𝒱₁` (§5.2.1).
* `Automorphism`             — `Aut(𝒱)`, inner automorphisms `exp(u₍₀₎)` (5.2.4).
* `WeightOneCohomology`      — Whitehead's second lemma `H²(𝔰𝔩₂,𝔰𝔩₂) = 0` as a finite
  computation, the weight-one Lie 2-cocycle of a graded first-order deformation
  (`Deform.weightOneCochain_mem_twoCocycle`), and the normalisation predicate
  `VertexOperatorAlgebra.WeightOneH2Vanishes` ([KQ] §6.2 / Linshaw–Qi eq. (3)).
-/
