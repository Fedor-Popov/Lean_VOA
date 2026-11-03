import VOA.DeligneAudit.D4CharBoxGaussian
import VOA.DeligneAudit.LeviTypeA2CertSl2Bound

/-! The sharp graded local Weyl bound for the sl2 lowering-current orbit. -/

namespace VOA.DeligneAudit.D4Char

open Sl2Weyl A3Sector

noncomputable section

def sl2DegreeBoxes (m d : ℕ) : Finset (ℕ →₀ ℕ) :=
  (Finset.range (m + 1)).biUnion fun a =>
    (a2BoxModeSet m a).filter fun f => (Finsupp.weight om f).2 = d

theorem boxP_length_le (m : ℕ) (f : ℕ →₀ ℕ) (h : BoxP m f) :
    Finsupp.degree f ≤ m := by
  by_cases hf : f = 0
  · simp [hf]
  · obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hf
    have hh := h i hi
    omega

theorem sl2DegreeBoxes_mem (m d : ℕ) (f : ℕ →₀ ℕ) :
    f ∈ sl2DegreeBoxes m d ↔ BoxP m f ∧ (Finsupp.weight om f).2 = d := by
  classical
  simp only [sl2DegreeBoxes, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨a, ha, hf, hd⟩
    exact ⟨((mem_a2BoxModeSet m a (by omega) f).mp hf).2, hd⟩
  · rintro ⟨hf, hd⟩
    have ha := boxP_length_le m f hf
    exact ⟨Finsupp.degree f, by omega,
      (mem_a2BoxModeSet m _ ha f).mpr ⟨rfl, hf⟩, hd⟩

theorem sl2DegreeBoxes_card_le (m d : ℕ) :
    (sl2DegreeBoxes m d).card ≤ A2.gl2Hilb m 0 d := by
  classical
  calc
    _ ≤ ∑ a ∈ Finset.range (m + 1),
        ((a2BoxModeSet m a).filter fun f => (Finsupp.weight om f).2 = d).card :=
      Finset.card_biUnion_le
    _ = ∑ a ∈ Finset.range (m + 1), A2.qbinomCoeff m a d := by
      apply Finset.sum_congr rfl
      intro a ha
      exact modeBox_card_degree m a d (by simpa using ha)
    _ = A2.gl2Hilb m 0 d := by
      unfold A2.gl2Hilb
      rw [Nat.sub_zero, ← Nat.range_succ_eq_Icc_zero]
      simpa only [Nat.add_sub_cancel] using
        (Finset.sum_range_reflect (fun a => A2.qbinomCoeff m a d) (m + 1)).symm

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Exact sum of current modes; no direct-grading assumption on the module is needed. -/
def sl2LowerDegree (F : ℕ → Module.End ℂ V) (y : V) (d : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ l : List ℕ, l.sum = d ∧ v = (l.map F).prod y}

theorem sl2_word_bihomogeneous (l : List ℕ) :
    MvPolynomial.IsWeightedHomogeneous om (CLAssembly.mono l) (l.length, l.sum) := by
  induction l with
  | nil =>
      simpa [CLAssembly.mono] using MvPolynomial.isWeightedHomogeneous_one ℂ om
  | cons r l ih =>
      have hh := (MvPolynomial.isWeightedHomogeneous_X ℂ om r).mul ih
      simpa [CLAssembly.mono, om, Nat.add_comm] using hh

/-- Garland's homogeneous box spanning gives a finite spanning family in each degree. -/
theorem sl2LowerDegree_le_boxes (F : ℕ → Module.End ℂ V)
    (hFF : ∀ i j, F i * F j = F j * F i) (y : V) (m d : ℕ)
    (hk : ∀ r s, 1 ≤ r → m + 1 ≤ r + s →
      (PowerSeries.coeff s (Garland.Fs F ^ r)) y = 0) :
    sl2LowerDegree F y d ≤ Submodule.span ℂ
      ((fun f => Sl2Weyl.evAlg F hFF (MvPolynomial.monomial f 1) y) ''
        (sl2DegreeBoxes m d : Set (ℕ →₀ ℕ))) := by
  apply Submodule.span_le.mpr
  rintro v ⟨l, hd, rfl⟩
  have hs := span_box_graded F hFF y m hk (sl2_word_bihomogeneous l)
  rw [CLAssembly.evAlg_mono F hFF] at hs
  apply (Submodule.span_mono ?_) hs
  rintro v ⟨f, hf, hw, rfl⟩
  refine ⟨f, (sl2DegreeBoxes_mem m d f).mpr ⟨hf, ?_⟩, rfl⟩
  exact (congrArg Prod.snd hw).trans hd

theorem sl2LowerDegree_finite_and_rank (F : ℕ → Module.End ℂ V)
    (hFF : ∀ i j, F i * F j = F j * F i) (y : V) (m d : ℕ)
    (hk : ∀ r s, 1 ≤ r → m + 1 ≤ r + s →
      (PowerSeries.coeff s (Garland.Fs F ^ r)) y = 0) :
    FiniteDimensional ℂ (sl2LowerDegree F y d) ∧
      Module.finrank ℂ (sl2LowerDegree F y d) ≤ A2.gl2Hilb m 0 d := by
  classical
  let E : Finset V := (sl2DegreeBoxes m d).image
    (fun f => Sl2Weyl.evAlg F hFF (MvPolynomial.monomial f 1) y)
  have hs : sl2LowerDegree F y d ≤ Submodule.span ℂ (E : Set V) := by
    simpa only [E, Finset.coe_image] using sl2LowerDegree_le_boxes F hFF y m d hk
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (E : Set V)) :=
    FiniteDimensional.span_of_finite _ E.finite_toSet
  refine ⟨Submodule.finiteDimensional_of_le hs, ?_⟩
  exact (Submodule.finrank_mono hs).trans
    ((finrank_span_finset_le_card (R := ℂ) (s := E)).trans
      (Finset.card_image_le.trans (sl2DegreeBoxes_card_le m d)))

/-- The sharp sl2 local Weyl estimate, for every highest weight and every degree. -/
theorem sl2_local_weyl_graded_bound {E H F : ℕ → Module.End ℂ V}
    (hS : CVsl2.SL2 E H F) {y : V} (hE : ∀ s, E s y = 0)
    (hH : ∀ s, 0 < s → H s y = 0) (m : ℕ)
    (hF : (F 0 ^ (m + 1)) y = 0) (d : ℕ) :
    FiniteDimensional ℂ (sl2LowerDegree F y d) ∧
      Module.finrank ℂ (sl2LowerDegree F y d) ≤ A2.gl2Hilb m 0 d := by
  apply sl2LowerDegree_finite_and_rank F hS.hFF y m d
  intro r s hr hrs
  exact Garland.garland
    (fun k => by simpa only [add_comm] using hS.hEF 1 k)
    (fun j k => hS.hHF (j + 1) k) hS.hFF
    (hE 1) (fun j => hH (j + 1) (by omega)) r hr hF s hrs

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.boxP_length_le
#print axioms VOA.DeligneAudit.D4Char.sl2DegreeBoxes_mem
#print axioms VOA.DeligneAudit.D4Char.sl2DegreeBoxes_card_le
#print axioms VOA.DeligneAudit.D4Char.sl2_word_bihomogeneous
#print axioms VOA.DeligneAudit.D4Char.sl2LowerDegree_le_boxes
#print axioms VOA.DeligneAudit.D4Char.sl2LowerDegree_finite_and_rank
#print axioms VOA.DeligneAudit.D4Char.sl2_local_weyl_graded_bound
