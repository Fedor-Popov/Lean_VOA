/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Huang.ZhuSemisimple
import VOA.Modularity.ZhuStronglyRational

/-!
# Zhu modularity from rationality

The pinned Zhu modularity theorem (`zhuModularity_pinned_of_C2Cofinite`) takes `IsSemisimpleRing (A W)` as a
hypothesis, and `ZhuAdmissibleSemisimple W` (`Modules/AdmissibleRationality.lean`) was carried as a named
literature input. Both are discharged here.

* `zhuAdmissibleSemisimple_holds W : ZhuAdmissibleSemisimple W`. Rationality (`AdmissiblyRational`) implies
  that Zhu's algebra is semisimple, for **every** VOA, with no `C₂` hypothesis. The proof is
  `Huang.ZhuSemisimple.isSemisimpleRing_A_of_admissiblyRational` (the Dong–Jiang module `M(A(V))`, bottom
  recovery and a weak complement), applied with the bottom projection `voaPBWBottomProjection`. That projection
  comes from the project's PBW theorem `VOA.pbw`, which is a theorem, not an axiom.
* `zhuModularity_pinned_of_rational`: Zhu's modularity theorem with **rational** in place of "semisimple Zhu
  algebra".
* `zhuModularity_stronglyRational_of_finite`: the canonical-family form for a strongly rational VOA. Its only
  remaining literature input is `DLMFinitelyManyIrredAdmissible` (Dong–Li–Mason finiteness).
-/

namespace VOA

open VHat VHat.DLM3

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **Rational ⇒ Zhu's algebra is semisimple**, for every VOA (Dong–Li–Mason, *Twisted
representations of vertex operator algebras*, Math. Ann. **310** (1998) 571–600, Thm 8.1(a) at
`g = 1`; the `A_n(V)` generalisation is Dong–Li–Mason, J. Algebra **206** (1998) 67–96,
Thm 4.10(a)). No `C₂`-cofiniteness is needed. -/
theorem zhuAdmissibleSemisimple_holds (W : VertexOperatorAlgebra 𝒱) : ZhuAdmissibleSemisimple W :=
  Huang.ZhuSemisimple.zhuAdmissibleSemisimple_of_Pr
    (voaPBWBottomProjection (parabolicRepOfAMod W (regularAMod W)))

/-- `IsSemisimpleRing (A W)` from rationality.
A specialisation of the general form
`VOA.Huang.ZhuSemisimple.isSemisimpleRing_A_of_admissiblyRational` (at the bottom projection
`voaPBWBottomProjection …`); cite that name as the main theorem. -/
theorem isSemisimpleRing_A_of_rational {W : VertexOperatorAlgebra 𝒱} (hrat : AdmissiblyRational W) :
    letI := instRingA W; IsSemisimpleRing (A W) :=
  zhuAdmissibleSemisimple_holds W hrat

section Pinned

variable {W : VertexOperatorAlgebra 𝒱} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Zhu's modularity theorem for a rational `C₂`-cofinite VOA** (pinned form): the torus one-point functions of
the given family of irreducible modules span an `SL₂(ℤ)`-representation with diagonal `ρ(T)`. -/
theorem zhuModularity_pinned_of_rational [Finite (Φ W)]
    (Mfam : ι → IrrModule W) (h : ι → ℂ)
    (hC2 : C2Cofinite W) (hrat : AdmissiblyRational W)
    (hcard : Fintype.card ι = Nat.card (Φ W))
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hsep : ∀ j k : ι, j ≠ k → h j = h k →
      IsEmpty (AModEquiv W (lowestAMod (hcw j).2) (lowestAMod (hcw k).2))) :
    ∃ D : ModularData W ι, D.Mfam = Mfam ∧ D.h = h ∧ ZhuModularityAnalytic D :=
  zhuModularity_pinned_of_C2Cofinite_voaPBW Mfam h hC2 (isSemisimpleRing_A_of_rational hrat) hcard hcw hsep

end Pinned

/-- **Zhu modularity for the canonical family of a strongly rational VOA**, with Zhu semisimplicity proved; the
only remaining literature input is Dong–Li–Mason finiteness `DLMFinitelyManyIrredAdmissible`. -/
theorem zhuModularity_stronglyRational_of_finite {W : VertexOperatorAlgebra 𝒱}
    (hSR : StronglyRational W) (hFin : DLMFinitelyManyIrredAdmissible W) :
    letI : Finite (Φ W) := finite_Φ_of_finite_Φadm W (hFin hSR.rational)
    letI : Fintype (Φ W) := Fintype.ofFinite (Φ W)
    letI : DecidableEq (Φ W) := Classical.decEq (Φ W)
    ∃ D : ModularData W (Φ W),
      D.Mfam = canonicalIrrModule ∧
      D.h = (fun c => conformalWeightOf (canonicalIrrModule c)) ∧
      ZhuModularityAnalytic D :=
  zhuModularity_stronglyRational_voaPBW hSR hFin (zhuAdmissibleSemisimple_holds W)

end VOA

section AxiomAudit
#print axioms VOA.zhuAdmissibleSemisimple_holds
#print axioms VOA.zhuModularity_pinned_of_rational
#print axioms VOA.zhuModularity_stronglyRational_of_finite
end AxiomAudit
