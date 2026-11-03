/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.GNProp8PBW
import VOA.Modularity.StronglyRationalFamily
import VOA.Modules.StronglyRational

/-!
# Zhu modularity for a strongly rational VOA

This is the integral, non-super packaging of the pinned Zhu theorem.  The module family is the
canonical family indexed by `Φ W`; its weights, cardinality and bottom-separation data are derived,
not hypotheses.  The two literature inputs are named exactly as in the rationality lattice:
Dong--Li--Mason finiteness and Zhu/Dong--Li--Mason semisimplicity.
-/

namespace VOA

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱}

/-- **Pinned Zhu modularity for the canonical irreducible family of a strongly rational VOA.**

Compared with `zhuModularity_pinned_of_C2Cofinite_voaPBW`, this discharges the explicit family,
conformal weights, family cardinality, simple-bottom and bottom-separation inputs. -/
theorem zhuModularity_stronglyRational_voaPBW
    (hSR : StronglyRational W)
    (hFin : DLMFinitelyManyIrredAdmissible W)
    (hZhu : ZhuAdmissibleSemisimple W) :
    letI : Finite (Φ W) := finite_Φ_of_finite_Φadm W (hFin hSR.rational)
    letI : Fintype (Φ W) := Fintype.ofFinite (Φ W)
    letI : DecidableEq (Φ W) := Classical.decEq (Φ W)
    ∃ D : ModularData W (Φ W),
      D.Mfam = canonicalIrrModule ∧
      D.h = (fun c => conformalWeightOf (canonicalIrrModule c)) ∧
      ZhuModularityAnalytic D := by
  classical
  letI : Finite (Φ W) := finite_Φ_of_finite_Φadm W (hFin hSR.rational)
  letI : Fintype (Φ W) := Fintype.ofFinite (Φ W)
  letI : DecidableEq (Φ W) := Classical.decEq (Φ W)
  exact zhuModularity_pinned_of_C2Cofinite_voaPBW
    (canonicalIrrModule (W := W))
    (fun c => conformalWeightOf (canonicalIrrModule c))
    hSR.c2Cofinite
    (hZhu hSR.rational)
    canonicalIrrFamily_card
    canonicalIrrFamily_hasConformalWeight
    (fun j k hjk hw => canonicalIrrFamily_bottomSeparated hjk hw)

end VOA
