/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.PlusNice

/-!
# The `V_{2m}⁺` clause of the converse, from the cited facts at `m ≥ 2` only

`PlusNice.lean` reduced `Nice (V2mPlus m hm)` to three cited facts quantified over **every**
`m ≥ 1`.  The case `m = 1` is a theorem (`V2mPlus_one_nice`, via `V₂⁺ ≅ V₈`), and the `.plus`
label of the list only ever occurs with `m ≥ 2` (`HasCOneLabel`, GR Thm 3.1).  This file removes
the redundant case from the cited residue.

## Proved here
* `V2mPlus_one_c2Cofinite`, `V2mPlus_one_admissiblyRational`, `V2mPlus_one_pseudoUnitary`:
  the three facts at `m = 1` (projections of `V2mPlus_one_nice`).
* `v2mPlusC2CofiniteFact_iff`, `v2mPlusRationalFact_iff`, `v2mPlusPseudoUnitaryFact_iff`:
  each fact of `PlusNice.lean` is **equivalent** to its `m ≥ 2` restriction, so nothing is
  weakened and nothing is lost.
* `nice_V2mPlus_of_factsGe2` (all `m ≥ 1`) and `nice_of_hasCOneLabel_plus_of_factsGe2`
  (the `.plus` clause of GR Prop. 3.2), conditional only on the `m ≥ 2` facts.

## Sources of the three residual facts (checked against the arXiv text and Crossref)
* `V2mPlusC2CofiniteFactGe2`: G. Yamskulna, Comm. Algebra **32** (2004) 927–954,
  doi:10.1081/AGB-120027959, arXiv:math/0202056.  Writing `⟨α,α⟩ = 2k` (`k = m` here): her
  Theorem 5.1(2) proves `k ≥ 3`; her Lemma 3.8 covers `k = 2` by `V_L⁺ ≅ L(½,0) ⊗ L(½,0)`
  (Dong–Griess–Höhn, CMP 193 (1998), Lemma 3.1) and `C₂` of that tensor product (DLM).  Also
  Abe–Buhl–Dong, Trans. AMS **356** (2004) 3391–3402, Thm 5.3 (all positive-definite even `L`,
  reducing to Yamskulna).
* `V2mPlusRationalFactGe2`: T. Abe, Math. Z. **249** (2005) 455–484,
  doi:10.1007/s00209-004-0709-1, arXiv:math/0311210 — "any `ℤ_{≥0}`-graded weak module is
  completely reducible", which is `AdmissiblyRational`.
* `V2mPlusPseudoUnitaryFactGe2`: C. Dong, K. Nagatomo, Comm. Math. Phys. **202** (1999) 169–195,
  doi:10.1007/s002200050578, arXiv:math/9807168, Theorem 5.13 (the complete list of irreducible
  admissible `V_L⁺`-modules), with the lowest weights of the listed modules
  (`0, 1, k/4, r²/4k, 1/16, 9/16`).  Every irreducible ordinary module is irreducible admissible.
-/

set_option linter.style.longLine false

namespace VOA.Classification.COne

open VOA

/-! ## The case `m = 1` -/

theorem V2mPlus_one_c2Cofinite (hm : 1 ≤ 1) : C2Cofinite (V2mPlus 1 hm) :=
  V2mPlus_one_nice.1.toStronglyFinite.c2Cofinite

theorem V2mPlus_one_admissiblyRational (hm : 1 ≤ 1) : AdmissiblyRational (V2mPlus 1 hm) :=
  V2mPlus_one_nice.1.rational

theorem V2mPlus_one_pseudoUnitary (hm : 1 ≤ 1) : PseudoUnitary (V2mPlus 1 hm) :=
  V2mPlus_one_nice.2

/-! ## The cited facts, restricted to `m ≥ 2` -/

/-- **Cited (Yamskulna 2004, Thm 5.1(2) for `m ≥ 3`, Lemma 3.8 for `m = 2`)**: `V_{2m}⁺` is
`C₂`-cofinite for `m ≥ 2`.  See the module docstring for the full references. -/
def V2mPlusC2CofiniteFactGe2 : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m → C2Cofinite (V2mPlus m hm)

/-- **Cited (Abe, Math. Z. 249 (2005))**: `V_{2m}⁺` is rational (every admissible module is
completely reducible) for `m ≥ 2`. -/
def V2mPlusRationalFactGe2 : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m → AdmissiblyRational (V2mPlus m hm)

/-- **Cited (Dong–Nagatomo, CMP 202 (1999), Thm 5.13, with the listed lowest weights)**:
`V_{2m}⁺` is pseudo-unitary for `m ≥ 2`. -/
def V2mPlusPseudoUnitaryFactGe2 : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m → PseudoUnitary (V2mPlus m hm)

theorem v2mPlusC2CofiniteFact_iff : V2mPlusC2CofiniteFact ↔ V2mPlusC2CofiniteFactGe2 := by
  refine ⟨fun h m hm _ => h m hm, fun h m hm => ?_⟩
  rcases Nat.lt_or_ge m 2 with h1 | h2
  · obtain rfl : m = 1 := by omega
    exact V2mPlus_one_c2Cofinite hm
  · exact h m hm h2

theorem v2mPlusRationalFact_iff : V2mPlusRationalFact ↔ V2mPlusRationalFactGe2 := by
  refine ⟨fun h m hm _ => h m hm, fun h m hm => ?_⟩
  rcases Nat.lt_or_ge m 2 with h1 | h2
  · obtain rfl : m = 1 := by omega
    exact V2mPlus_one_admissiblyRational hm
  · exact h m hm h2

theorem v2mPlusPseudoUnitaryFact_iff :
    V2mPlusPseudoUnitaryFact ↔ V2mPlusPseudoUnitaryFactGe2 := by
  refine ⟨fun h m hm _ => h m hm, fun h m hm => ?_⟩
  rcases Nat.lt_or_ge m 2 with h1 | h2
  · obtain rfl : m = 1 := by omega
    exact V2mPlus_one_pseudoUnitary hm
  · exact h m hm h2

/-! ## Assembly -/

/-- **`V_{2m}⁺` is nice for every `m ≥ 1`**, `#print axioms`-clean, conditional only on the
three cited facts at `m ≥ 2`. -/
theorem nice_V2mPlus_of_factsGe2 (hC2 : V2mPlusC2CofiniteFactGe2)
    (hRat : V2mPlusRationalFactGe2) (hPU : V2mPlusPseudoUnitaryFactGe2) (m : ℕ) (hm : 1 ≤ m) :
    Nice (V2mPlus m hm) :=
  nice_V2mPlus_of_facts (v2mPlusC2CofiniteFact_iff.mpr hC2) (v2mPlusRationalFact_iff.mpr hRat)
    (v2mPlusPseudoUnitaryFact_iff.mpr hPU) m hm

/-- **The `.plus` clause of Gannon–Rayhaun Prop. 3.2**, conditional only on the three cited facts
at `m ≥ 2`: a VOA (carrier in `Type`) isomorphic to `V_{2m}⁺` is nice and has `c = 1`. -/
theorem nice_of_hasCOneLabel_plus_of_factsGe2 (hC2 : V2mPlusC2CofiniteFactGe2)
    (hRat : V2mPlusRationalFactGe2) (hPU : V2mPlusPseudoUnitaryFactGe2)
    {𝒱 : Type} [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱) (m : ℕ)
    (h : HasCOneLabel V (.plus m)) : Nice V ∧ V.centralCharge = 1 :=
  nice_of_hasCOneLabel_plus_of_facts (v2mPlusC2CofiniteFact_iff.mpr hC2)
    (v2mPlusRationalFact_iff.mpr hRat) (v2mPlusPseudoUnitaryFact_iff.mpr hPU) V m h

end VOA.Classification.COne

section AxiomAudit
#print axioms VOA.Classification.COne.v2mPlusC2CofiniteFact_iff
#print axioms VOA.Classification.COne.v2mPlusRationalFact_iff
#print axioms VOA.Classification.COne.v2mPlusPseudoUnitaryFact_iff
#print axioms VOA.Classification.COne.nice_V2mPlus_of_factsGe2
#print axioms VOA.Classification.COne.nice_of_hasCOneLabel_plus_of_factsGe2
end AxiomAudit
