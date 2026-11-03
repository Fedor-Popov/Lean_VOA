/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.SuperRelativeEtingofFinite
import VOA.Modules.SuperTwistedZhu

/-!
# Sign-adjusted twisted-Zhu comparison for relative super Poisson homology

The relative Etingof quotient for a spatial twist `g` uses the literal fixed locus `(R_V)^g`.
Some twisted-super Zhu comparisons instead use the sign-adjusted automorphism `sigma * g`, where
`sigma` is parity.  This file gives that convention its own names and its own actual carriers:
the fixed C2 locus, Reynolds average, twisted-Zhu relation space, and twisted-Zhu quotient.

Nothing here replaces `g` by `sigma * g` in `SuperRelativePoissonData`, and no equality of the two
fixed loci is asserted without a hypothesis.  In particular, weight and parity remain independent
and no spin--statistics assumption is made.  The integer `N` in the twisted-Zhu carriers is only a
parameter; users must separately supply the finite-order theorem required by applications.
-/

namespace VOA

open Module (End)

set_option autoImplicit false

universe u

variable {VType : Type u} [AddCommGroup VType] [Module ℂ VType]
variable {W : SuperVertexOperatorAlgebra VType}

/-- The separately named sign-adjusted automorphism used only for twisted-Zhu comparison. -/
noncomputable def SuperAut.twistedZhuSignAdjusted (g : SuperAut W) : SuperAut W :=
  W.parityAut * g

@[simp] theorem SuperAut.twistedZhuSignAdjusted_one :
    (1 : SuperAut W).twistedZhuSignAdjusted = W.parityAut := by
  simp [SuperAut.twistedZhuSignAdjusted]

/-- The C2 fixed locus for the sign-adjusted twisted-Zhu convention.  This is not the relative
fixed locus `(R_V)^g`. -/
noncomputable def SuperAut.twistedZhuSignAdjustedFixedC2 (g : SuperAut W) :
    Submodule ℂ (SuperC2Symbol W) :=
  g.twistedZhuSignAdjusted.superC2Fixed

/-- The Reynolds projector used by the sign-adjusted twisted-Zhu presentation. -/
noncomputable def SuperAut.twistedZhuSignAdjustedAverage (g : SuperAut W) (N : ℕ) :
    End ℂ VType :=
  g.twistedZhuSignAdjusted.fixedAverage N

/-- The actual Dong--Zhao relation subspace after making the `sigma * g` comparison convention
explicit in the name. -/
noncomputable def SuperVertexOperatorAlgebra.twistedZhuSignAdjustedO
    (W : SuperVertexOperatorAlgebra VType) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) (N : ℕ) : Submodule ℂ VType :=
  W.twistedO hW g.twistedZhuSignAdjusted N

/-- The corresponding sign-adjusted twisted-Zhu quotient carrier. -/
noncomputable abbrev SuperVertexOperatorAlgebra.twistedZhuSignAdjustedA
    (W : SuperVertexOperatorAlgebra VType) (hW : W.toSuperNearVOA.IntegralWeights)
    (g : SuperAut W) (N : ℕ) : Type u :=
  VType ⧸ W.twistedZhuSignAdjustedO hW g N

/-- When parity acts trivially on the state C2 quotient, the sign-adjusted and literal
spatial fixed loci coincide.  The hypothesis is explicit and is not a spin--statistics axiom. -/
theorem SuperAut.twistedZhuSignAdjustedFixedC2_eq_superC2Fixed
    (g : SuperAut W) (hparity : W.parityAut.superC2Map = LinearMap.id) :
    g.twistedZhuSignAdjustedFixedC2 = g.superC2Fixed := by
  ext x
  rw [SuperAut.twistedZhuSignAdjustedFixedC2]
  rw [SuperAut.mem_superC2Fixed_iff, SuperAut.mem_superC2Fixed_iff]
  rw [SuperAut.twistedZhuSignAdjusted]
  rw [SuperAut.superC2Map_mul_apply, hparity, LinearMap.id_apply]

end VOA
