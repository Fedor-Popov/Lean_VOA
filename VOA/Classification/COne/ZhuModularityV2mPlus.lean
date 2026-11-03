/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.ZhuModularityCanonical
import VOA.Classification.COne.PlusC2Final
import VOA.Classification.COne.PlusTwistCharacters
import VOA.Classification.COne.OrbTopZhu
import VOA.Classification.COne.LatticeStronglyRational
import VOA.Classification.COne.Statement

/-!
# Zhu modularity for `V_{2m}⁺` (and the tetrahedral orbifold), with every hypothesis discharged

Nontrivial instances of `zhuModularity_canonical_of_C2Cofinite_semisimple`:

* `zhuModularity_V2mPlus`: for every `m ≥ 2`, the one-point functions of the canonical
  irreducible modules of the rank-one lattice orbifold `V_{√(2m)ℤ}⁺` (central charge `1`)
  span an `SL₂(ℤ)`-representation in the sense of `ZhuModularityAnalytic`.  Inputs:
  `V2mPlus_c2Cofinite` (Yamskulna; Abe–Buhl–Dong) and `V2mPlus_zhuSemisimple` (Abe Thm 7.1(1);
  the Zhu algebra has dimension `m + 7`, `V2mPlus_zhu_finrank`).
* `zhuModularity_cubicModel`: the same for the tetrahedral `c = 1` orbifold `cubicModel`
  (`OrbA4.cubicModel_c2Cofinite_holds`, `OrbTop.cubicModel_zhuSemisimple`).

* `zhuModularity_V2m`: the same for the lattice VOA `V_{2m}` itself, `m ≥ 1`, from
  `V2m_stronglyRational` via `zhuModularity_canonical_of_stronglyRational` (Zhu semisimplicity
  comes from `isSemisimpleRing_A_of_admissiblyRational`).
* `zhuModularity_of_nice`: the same for every `Nice` VOA (Gannon–Rayhaun Def. 2.6).

Note on `zhuModularity_V2mPlus`: the hypothesis `hm : 1 ≤ m` is implied by `hm2 : 2 ≤ m`; it is
kept because `V2mPlus m hm` takes it as an argument.

No hypotheses remain; the only project-level trust is the PBW theorem `VOA.pbw`.
-/

namespace VOA.Classification.COne

open VOA

/-- **Zhu modularity for `V_{2m}⁺`, `m ≥ 2`, unconditionally.**  The canonical family
of irreducible `V_{2m}⁺`-modules, with their conformal weights, has one-point functions
transforming under `SL₂(ℤ)` by a genuine matrix representation (`ZhuModularityAnalytic`). -/
theorem zhuModularity_V2mPlus (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) :
    letI : Finite (Φ (V2mPlus m hm)) :=
      VOA.Huang.ZhuFiniteIrr.finite_Φ_of_C2Cofinite_pbw (V2mPlus_c2Cofinite m hm)
    letI : Fintype (Φ (V2mPlus m hm)) := Fintype.ofFinite _
    letI : DecidableEq (Φ (V2mPlus m hm)) := Classical.decEq _
    ∃ D : VOA.ModularData (V2mPlus m hm) (Φ (V2mPlus m hm)), D.Mfam = canonicalIrrModule ∧
      D.h = (fun c => conformalWeightOf (canonicalIrrModule c)) ∧ VOA.ZhuModularityAnalytic D :=
  zhuModularity_canonical_of_C2Cofinite_semisimple (V2mPlus m hm) (V2mPlus_c2Cofinite m hm)
    (V2mPlus_zhuSemisimple m hm hm2)

/-- **Zhu modularity for the lattice VOA `V_{2m}`, `m ≥ 1`, unconditionally.** -/
theorem zhuModularity_V2m (m : ℕ) (hm : 1 ≤ m) :
    letI : Finite (Φ (V2m m hm)) :=
      VOA.Huang.ZhuFiniteIrr.finite_Φ_of_C2Cofinite_pbw (V2m_stronglyRational m hm).c2Cofinite
    letI : Fintype (Φ (V2m m hm)) := Fintype.ofFinite _
    letI : DecidableEq (Φ (V2m m hm)) := Classical.decEq _
    ∃ D : VOA.ModularData (V2m m hm) (Φ (V2m m hm)), D.Mfam = canonicalIrrModule ∧
      D.h = (fun c => conformalWeightOf (canonicalIrrModule c)) ∧ VOA.ZhuModularityAnalytic D :=
  zhuModularity_canonical_of_stronglyRational (V2m m hm) (V2m_stronglyRational m hm)

/-- **Zhu modularity for every `Nice` VOA** (strongly rational and pseudo-unitary; only the
strongly rational half is used). -/
theorem zhuModularity_of_nice {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (V : VertexOperatorAlgebra 𝒱) (hV : Nice V) :
    letI : Finite (Φ V) := VOA.Huang.ZhuFiniteIrr.finite_Φ_of_C2Cofinite_pbw hV.1.c2Cofinite
    letI : Fintype (Φ V) := Fintype.ofFinite _
    letI : DecidableEq (Φ V) := Classical.decEq _
    ∃ D : VOA.ModularData V (Φ V), D.Mfam = canonicalIrrModule ∧
      D.h = (fun c => conformalWeightOf (canonicalIrrModule c)) ∧ VOA.ZhuModularityAnalytic D :=
  zhuModularity_canonical_of_stronglyRational V hV.1

/-- **Zhu modularity for the tetrahedral `c = 1` orbifold `cubicModel`, unconditionally.** -/
theorem zhuModularity_cubicModel :
    letI : Finite (Φ OrbRat2.cubicModel) :=
      VOA.Huang.ZhuFiniteIrr.finite_Φ_of_C2Cofinite_pbw OrbA4.cubicModel_c2Cofinite_holds
    letI : Fintype (Φ OrbRat2.cubicModel) := Fintype.ofFinite _
    letI : DecidableEq (Φ OrbRat2.cubicModel) := Classical.decEq _
    ∃ D : VOA.ModularData OrbRat2.cubicModel (Φ OrbRat2.cubicModel),
      D.Mfam = canonicalIrrModule ∧
      D.h = (fun c => conformalWeightOf (canonicalIrrModule c)) ∧ VOA.ZhuModularityAnalytic D :=
  zhuModularity_canonical_of_C2Cofinite_semisimple OrbRat2.cubicModel
    OrbA4.cubicModel_c2Cofinite_holds OrbTop.cubicModel_zhuSemisimple

end VOA.Classification.COne
