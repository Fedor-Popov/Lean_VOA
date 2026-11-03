/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.SuperSpinRelationsSq
import VOA.Modularity.SuperSpinSectorAutomorphisms
import VOA.Modularity.GammaThetaStatement

/-!
# Square-weight compatibility for fixed-pair state eigenspaces

This is a foundation for a square-weight spin-sector descent.  It avoids
the false premise that `L[-1] = L(-1) + L(0)` preserves original `L(0)`-homogeneity:
the relations use the official global half-weight square modes, and automorphisms commute with
the square Virasoro operators.

For one fixed outer ordered pair `(g,h)` of commuting involutions, the `SpinPair` values remain
inner simultaneous state-eigencharacter labels.  This file proves that square-weight projections
preserve those inner eigenspaces.  It does **not** construct outer trace sectors, a finite cusp
quotient, a descent/spanning theorem, trace realization, or `Gamma_theta` modularity.
-/

namespace VOA

open GammaThetaStmt

set_option autoImplicit false

universe u

variable {VType : Type u} [AddCommGroup VType] [Module Complex VType]
variable {W : SuperVertexOperatorAlgebra VType}

namespace SuperNearVOA

/-- The official internal decomposition by square-bracket `L[0]` eigenvalue. -/
@[reducible] noncomputable def superSqWeightDecomposition
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W) :
    DirectSum.Decomposition W.toSuperNearVOA.superSqWeightSpace :=
  (superSqWeightSpace_isInternal W hhalf).chooseDecomposition _

end SuperNearVOA

namespace SuperAut

/-- Automorphisms commute with every integral-weight square mode. -/
theorem map_superVSqZ (g : SuperAut W) (a : VType) (k : Nat) (m : Int) (v : VType) :
    g (W.toSuperNearVOA.superVSqZ a k m v) =
      W.toSuperNearVOA.superVSqZ (g a) k m (g v) := by
  rw [W.toSuperNearVOA.superVSqZ_apply, W.toSuperNearVOA.superVSqZ_apply]
  calc
    g (∑ᶠ i : Int, sqBracketCoeffZ k m i • W.toSuperNearVOA.smul a i v) =
        ∑ᶠ i : Int, g (sqBracketCoeffZ k m i • W.toSuperNearVOA.smul a i v) :=
      map_finsum g.toLinearEquiv.toLinearMap
        (W.toSuperNearVOA.superSqModeZ_support_finite a k m v)
    _ = _ := finsum_congr fun i => by
      rw [g.toLinearEquiv.map_smul]
      congr 1
      change g (W.smul a i v) = W.smul (g a) i (g v)
      exact g.map_smul a i v

/-- Automorphisms commute with the square Virasoro operators. -/
theorem map_superLsq (g : SuperAut W) (n : Int) (v : VType) :
    g (W.toSuperNearVOA.superLsq n v) = W.toSuperNearVOA.superLsq n (g v) := by
  rw [SuperNearVOA.superLsq, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.smul_apply]
  rw [map_sub, g.toLinearEquiv.map_smul]
  have hω := g.map_superVSqZ W.conformalVector 2 (n + 1) v
  change
    g (W.toSuperNearVOA.superVSqZ W.toSuperNearVOA.conformalVector 2 (n + 1) v) =
      W.toSuperNearVOA.superVSqZ (g W.toSuperNearVOA.conformalVector) 2 (n + 1) (g v)
    at hω
  have hOne := g.map_superVSqZ W.vacuum 0 (n + 1) v
  change
    g (W.toSuperNearVOA.superVSqZ W.toSuperNearVOA.vacuum 0 (n + 1) v) =
      W.toSuperNearVOA.superVSqZ (g W.toSuperNearVOA.vacuum) 0 (n + 1) (g v)
    at hOne
  have hgω : g W.toSuperNearVOA.conformalVector = W.toSuperNearVOA.conformalVector :=
    g.map_omega
  have hgOne : g W.toSuperNearVOA.vacuum = W.toSuperNearVOA.vacuum := g.map_vacuum
  rw [hω, hOne, hgω, hgOne]

/-- Every automorphism preserves every square-weight eigenspace. -/
theorem map_mem_superSqWeightSpace (g : SuperAut W) {K : Complex} {x : VType}
    (hx : x ∈ W.toSuperNearVOA.superSqWeightSpace K) :
    g x ∈ W.toSuperNearVOA.superSqWeightSpace K := by
  rw [W.toSuperNearVOA.mem_superSqWeightSpace_iff] at hx ⊢
  rw [← g.map_superLsq 0 x, hx, g.toLinearEquiv.map_smul]

/-- Each involution projector preserves every square-weight eigenspace. -/
theorem spinProjector_mem_superSqWeightSpace (g : SuperAut W) (mu : SpinPhase)
    {K : Complex} {x : VType} (hx : x ∈ W.toSuperNearVOA.superSqWeightSpace K) :
    g.spinProjector mu x ∈ W.toSuperNearVOA.superSqWeightSpace K := by
  rw [spinProjector_apply]
  exact (W.toSuperNearVOA.superSqWeightSpace K).smul_mem _
    ((W.toSuperNearVOA.superSqWeightSpace K).add_mem
      hx ((W.toSuperNearVOA.superSqWeightSpace K).smul_mem _
        (g.map_mem_superSqWeightSpace hx)))

/-- The simultaneous quarter-projectors preserve every square-weight eigenspace. -/
theorem spinPairProjector_mem_superSqWeightSpace (g h : SuperAut W) (p : SpinPair)
    {K : Complex} {x : VType} (hx : x ∈ W.toSuperNearVOA.superSqWeightSpace K) :
    spinPairProjector g h p x ∈ W.toSuperNearVOA.superSqWeightSpace K := by
  exact g.spinProjector_mem_superSqWeightSpace p.mu
    (h.spinProjector_mem_superSqWeightSpace p.lambda hx)

/-- Under the square-weight decomposition, each square projection preserves an inner state
eigenspace for the fixed outer pair `(g,h)`. -/
theorem homogProj_superSqWeightSpace_mem_spinSectors
    (g h : SuperAut W) (hg : g ^ 2 = 1) (hh : h ^ 2 = 1)
    (hcomm : g * h = h * g) (hhalf : IsHalfIntegerGraded W)
    {p : SpinPair} {x : VType} (hx : x ∈ spinSectors g h p) (K : Complex) :
    letI := SuperNearVOA.superSqWeightDecomposition W hhalf
    homogProj W.toSuperNearVOA.superSqWeightSpace K x ∈ spinSectors g h p := by
  letI := SuperNearVOA.superSqWeightDecomposition W hhalf
  rw [mem_spinSectors_iff g h hg hh hcomm] at hx ⊢
  constructor
  · have hc := homogProj_comm W.toSuperNearVOA.superSqWeightSpace g.toEnd
      (fun _ _ hy => g.map_mem_superSqWeightSpace hy) K x
    calc
      g.toEnd (homogProj W.toSuperNearVOA.superSqWeightSpace K x) =
          homogProj W.toSuperNearVOA.superSqWeightSpace K (g.toEnd x) := hc.symm
      _ = homogProj W.toSuperNearVOA.superSqWeightSpace K
          (SpinPhase.value p.mu • x) := by rw [show g.toEnd x = _ from hx.1]
      _ = _ := (homogProj W.toSuperNearVOA.superSqWeightSpace K).map_smul _ _
  · have hc := homogProj_comm W.toSuperNearVOA.superSqWeightSpace h.toEnd
      (fun _ _ hy => h.map_mem_superSqWeightSpace hy) K x
    calc
      h.toEnd (homogProj W.toSuperNearVOA.superSqWeightSpace K x) =
          homogProj W.toSuperNearVOA.superSqWeightSpace K (h.toEnd x) := hc.symm
      _ = homogProj W.toSuperNearVOA.superSqWeightSpace K
          (SpinPhase.value p.lambda • x) := by rw [show h.toEnd x = _ from hx.2]
      _ = _ := (homogProj W.toSuperNearVOA.superSqWeightSpace K).map_smul _ _

end SuperAut

end VOA
