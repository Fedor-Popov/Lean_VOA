import VOA.Classification.COne.OrbRat2Reduction
import VOA.Classification.COne.OrbRat2Table

/-!
# The tetrahedral model `W = (V₈⁺)^{ℤ/3} ≅ V₂^{A₄}`: rationality reduced to four pair splittings

Literature (Dong–Jiang, "Representations of the vertex operator algebra `V_{L₂}^{A₄}`",
J. Algebra 377 (2013), arXiv:1209.1168): `W` has exactly 21 irreducible modules, all with
one-dimensional tops, so `A(W) ≅ ℂ²¹`.  Their lowest weights (`tetraWeightQ`) are

* untwisted: `0, 1, 4, 4` (the `A₄`-irreps `1, 3, 1', 1''` in `V₂`) and `1/4, 9/4, 9/4`
  (the genuine `2T`-irreps `2, 2', 2''` in `V_{L+α/2}`);
* order-two sector: `1/16, 9/16`;
* the two order-three sectors: `1/36, 25/36, 49/36, 1/9, 4/9, 16/9`, each twice.

This list was re-derived independently and checked by an exact `S`-closure
test of the 21 characters (a computer-algebra check outside Lean); that is numerical evidence,
not a Lean proof.

Consequence proved here (`cubicModel_admissiblyRational_of_inputs`): given `C₂`, the Zhu
dimension bound `≤ 21` and the 21-character table, rationality of `W` needs ONLY the splitting
of four resonant pairs, all in the UNTWISTED sector, one orientation each:
`(1 ↘ 0)`, `(4 ↘ 0)`, `(4 ↘ 1)`, `(9/4 ↘ 1/4)` (kernel bottom first, quotient bottom second).
No twisted sector is involved in any resonance.
-/

set_option maxSynthPendingDepth 3

noncomputable section

namespace VOA.Classification.COne.OrbRat2

open VOA VertexOperatorAlgebra

/-- The 21 lowest weights of the irreducible `V₂^{A₄}`-modules (Dong–Jiang). -/
def tetraWeightQ : Fin 21 → ℚ :=
  ![0, 1, 4, 4, 1/4, 9/4, 9/4, 1/16, 9/16,
    1/36, 25/36, 49/36, 1/9, 4/9, 16/9,
    1/36, 25/36, 49/36, 1/9, 4/9, 16/9]

def tetraWeight (i : Fin 21) : ℂ := (tetraWeightQ i : ℂ)

/-- OPEN (true: Dong–Jiang arXiv:1209.1168; by `C₂` this is a statement about a
finite-dimensional algebra): the Zhu algebra of the tetrahedral model has dimension at most 21. -/
def CubicZhuDimensionBound : Prop :=
  Module.finrank ℂ (VOA.A cubicModel) ≤ 21

/-- OPEN (true: Dong–Jiang arXiv:1209.1168 — the tops of the 21 irreducible modules): 21
distinct characters of `A(W)` with `[ω] ↦` the lowest weights `tetraWeight`. -/
def CubicZhuCharacterTable : Prop :=
  CharTable cubicModel 21 tetraWeight

/-- OPEN (true, as a consequence of rationality: Dong–Jiang arXiv:1209.1168): the four untwisted
resonant splittings, kernel bottom first.  These are TRUE restrictions of resonant whole
splitting: they quantify over every weak module with the indicated factor bottoms. -/
def CubicResonantPairs : Prop :=
  PlusRat2Dual.PairSplit cubicModel 1 0 ∧ PlusRat2Dual.PairSplit cubicModel 4 0 ∧
    PlusRat2Dual.PairSplit cubicModel 4 1 ∧ PlusRat2Dual.PairSplit cubicModel (9/4) (1/4)

/-- The resonant table pairs (nonzero integral gap), certified by kernel computation. -/
theorem tetra_resonant_table :
    ∀ i j : Fin 21, (tetraWeightQ j - tetraWeightQ i).den = 1 →
      tetraWeightQ j ≠ tetraWeightQ i →
      (tetraWeightQ i = 1 ∧ tetraWeightQ j = 0) ∨ (tetraWeightQ i = 0 ∧ tetraWeightQ j = 1) ∨
      (tetraWeightQ i = 4 ∧ tetraWeightQ j = 0) ∨ (tetraWeightQ i = 0 ∧ tetraWeightQ j = 4) ∨
      (tetraWeightQ i = 4 ∧ tetraWeightQ j = 1) ∨ (tetraWeightQ i = 1 ∧ tetraWeightQ j = 4) ∨
      (tetraWeightQ i = 9/4 ∧ tetraWeightQ j = 1/4) ∨
      (tetraWeightQ i = 1/4 ∧ tetraWeightQ j = 9/4) := by
  decide +kernel

/-- Rationality of the tetrahedral model from `C₂`, the Zhu dimension bound, the character
table, and the four untwisted resonant splittings. -/
theorem cubicModel_admissiblyRational_of_inputs (hC2 : C2Cofinite cubicModel)
    (hdim : CubicZhuDimensionBound) (htab : CubicZhuCharacterTable)
    (hres : CubicResonantPairs) : AdmissiblyRational cubicModel := by
  apply admissiblyRational_of_charTable_pairs hC2 hdim htab
  intro i j z hz hij
  have hq : tetraWeightQ j = tetraWeightQ i + z := by
    have : ((tetraWeightQ j : ℚ) : ℂ) = ((tetraWeightQ i + z : ℚ) : ℂ) := by
      push_cast; exact hij
    exact_mod_cast this
  have hden : (tetraWeightQ j - tetraWeightQ i).den = 1 := by
    rw [hq, add_sub_cancel_left]; rfl
  have hne : tetraWeightQ j ≠ tetraWeightQ i := by
    rw [hq]; intro h; apply hz; exact_mod_cast (add_eq_left.mp h)
  obtain ⟨h10, h40, h41, h94⟩ := hres
  have ec : ∀ k : Fin 21, ∀ r : ℚ, tetraWeightQ k = r → tetraWeight k = (r : ℂ) := by
    intro k r hk; simp [tetraWeight, hk]
  rcases tetra_resonant_table i j hden hne with
    ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ <;>
    rw [ec i _ hi, ec j _ hj] <;> push_cast
  · exact Or.inl h10
  · exact Or.inr h10
  · exact Or.inl h40
  · exact Or.inr h40
  · exact Or.inl h41
  · exact Or.inr h41
  · exact Or.inl h94
  · exact Or.inr h94

/-- The tetrahedral model Prop from the three Zhu/splitting inputs. -/
theorem cubicModelRationalOfC2_of_inputs (hdim : CubicZhuDimensionBound)
    (htab : CubicZhuCharacterTable) (hres : CubicResonantPairs) : CubicModelRationalOfC2 :=
  fun hC2 => cubicModel_admissiblyRational_of_inputs hC2 hdim htab hres

/-- Conversely the four pair splittings are NECESSARY (given `C₂`): they are consequences of
rationality, so `CubicResonantPairs` is no stronger than the target. -/
theorem cubicResonantPairs_of_rational (hC2 : C2Cofinite cubicModel)
    (hR : AdmissiblyRational cubicModel) : CubicResonantPairs := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · intro M _ _ B P _ _ hb ht
    exact OrbRat.wholeSplitting_of_admissiblyRational hC2 hR B P _ _ hb ht

end VOA.Classification.COne.OrbRat2
