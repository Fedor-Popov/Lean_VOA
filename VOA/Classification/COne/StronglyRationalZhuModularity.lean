/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Classification.COne.AdmissibleOrdinaryFinite
import VOA.Modularity.ZhuModularityRational
import VOA.Modularity.ZhuModularityCanonical

/-!
# Zhu modularity for strongly rational VOAs, with Dong–Li–Mason finiteness discharged

`zhuModularity_stronglyRational_of_finite` (`Modularity/ZhuModularityRational.lean`) still took
`DLMFinitelyManyIrredAdmissible W` as a hypothesis. For a strongly rational VOA it holds:

* `C₂`-cofiniteness makes `A(W)` finite-dimensional, and rationality makes it semisimple
  (`isSemisimpleRing_A_of_rational`), so `Φ W` is finite (`Huang.ZhuFiniteIrr.finite_Φ_of_C2Cofinite`);
* under `C₂`, every irreducible admissible module is ordinary, so `Φ W → Φadm W` is onto
  (`AdmissibleOrdinary.ΦtoΦadm_surjective`).

The bottom projection these use is `voaPBWBottomProjection`, which rests on the theorem `VOA.pbw`.

* `dlmFinitelyManyIrredAdmissible_of_C2Cofinite`: DLM finiteness for every `C₂`-cofinite VOA.
* `finite_Φadm_of_stronglyRational`, `finite_Φ_of_stronglyRational`.
* `zhuModularity_stronglyRational`: Zhu modularity for the canonical family of irreducible modules of a strongly
  rational VOA, with no further hypothesis.  Alias of `zhuModularity_canonical_of_stronglyRational`
  (`Modularity/ZhuModularityCanonical.lean`); kept for compatibility.
-/

namespace VOA

open VHat VHat.DLM3

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **Dong–Li–Mason finiteness** for every `C₂`-cofinite VOA: a rational `C₂`-cofinite VOA
has finitely many irreducible admissible modules up to isomorphism. This is a `C₂`-cofinite
analogue of Dong–Li–Mason, *Twisted representations of vertex operator algebras*, Math. Ann.
**310** (1998) 571–600, Thm 8.1(b) (at `g = 1`), which assumes rationality only. -/
theorem dlmFinitelyManyIrredAdmissible_of_C2Cofinite {W : VertexOperatorAlgebra 𝒱} (hC2 : C2Cofinite W) :
    DLMFinitelyManyIrredAdmissible W := fun hrat =>
  Classification.COne.AdmissibleOrdinary.c2SemisimpleAdmissibleFiniteness_of_bottomProjection
    (voaPBWBottomProjection (parabolicRepOfAMod W (regularAMod W))) hC2 (isSemisimpleRing_A_of_rational hrat)

/-- A strongly rational VOA has finitely many irreducible admissible modules. -/
theorem finite_Φadm_of_stronglyRational {W : VertexOperatorAlgebra 𝒱} (hSR : StronglyRational W) :
    Finite (Φadm W) :=
  dlmFinitelyManyIrredAdmissible_of_C2Cofinite hSR.c2Cofinite hSR.rational

/-- A strongly rational VOA has finitely many irreducible (ordinary) modules. -/
theorem finite_Φ_of_stronglyRational {W : VertexOperatorAlgebra 𝒱} (hSR : StronglyRational W) :
    Finite (Φ W) :=
  finite_Φ_of_finite_Φadm W (finite_Φadm_of_stronglyRational hSR)

/-- Alias of `VOA.zhuModularity_canonical_of_stronglyRational`; kept for compatibility.

**Zhu's modularity theorem for a strongly rational VOA**: the torus one-point functions of the
canonical family of irreducible modules span an `SL₂(ℤ)`-representation with diagonal `ρ(T)`.
The statement is that of `VOA.zhuModularity_canonical_of_stronglyRational` (the `Finite (Φ W)`
instance is supplied by a different proof term, which is irrelevant since `Finite` is a `Prop`).
The general form (no simplicity or self-duality) is
`VOA.zhuModularity_canonical_of_C2Cofinite_admissiblyRational`; cite that name as the main
theorem. -/
theorem zhuModularity_stronglyRational {W : VertexOperatorAlgebra 𝒱} (hSR : StronglyRational W) :
    letI : Finite (Φ W) := finite_Φ_of_finite_Φadm W (dlmFinitelyManyIrredAdmissible_of_C2Cofinite
      hSR.c2Cofinite hSR.rational)
    letI : Fintype (Φ W) := Fintype.ofFinite (Φ W)
    letI : DecidableEq (Φ W) := Classical.decEq (Φ W)
    ∃ D : ModularData W (Φ W),
      D.Mfam = canonicalIrrModule ∧
      D.h = (fun c => conformalWeightOf (canonicalIrrModule c)) ∧
      ZhuModularityAnalytic D :=
  zhuModularity_canonical_of_stronglyRational W hSR

end VOA

section AxiomAudit
#print axioms VOA.dlmFinitelyManyIrredAdmissible_of_C2Cofinite
#print axioms VOA.finite_Φ_of_stronglyRational
#print axioms VOA.zhuModularity_stronglyRational
end AxiomAudit
