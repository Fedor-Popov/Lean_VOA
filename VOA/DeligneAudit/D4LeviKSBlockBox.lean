import VOA.DeligneAudit.D4LeviKSBlockGarlandSpan

/-! The graded one-alphabet box theorem in symmetric-polynomial coordinates. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.Sl2Weyl
open VOA.DeligneAudit.A3Sector

/-- The symmetric images of the occupation box, with the mode degree fixed. -/
noncomputable def ksBlockBoxPolys (q n d : ℕ) :
    Finset (MvPolynomial (Fin n) ℂ) := by
  classical
  exact (ksOneBoxPolys q n d).image (ksBlockTheta n)

theorem ksOneBoxPolys_homogeneous (q n d : ℕ) (P : R)
    (hP : P ∈ ksOneBoxPolys q n d) :
    IsWeightedHomogeneous om P (n, d) := by
  classical
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hP
  exact isWeightedHomogeneous_monomial om f 1 (Finset.mem_filter.mp hf).2

theorem ksBlockBoxPolys_card_le (q n d : ℕ) (hn : n ≤ q) :
    (ksBlockBoxPolys q n d).card ≤ q.choose n :=
  Finset.card_image_le.trans (ksOneBoxPolys_card_le q n d hn)

/-- Every box image is the orbit sum of a mode tuple in the rectangle
    `n × (q - n)`, with exactly degree `d`. -/
theorem ksBlockBoxPolys_spec (q n d : ℕ) (hn : n ≤ q)
    (P : MvPolynomial (Fin n) ℂ) (hP : P ∈ ksBlockBoxPolys q n d) :
    ∃ v : Fin n → ℕ, (∀ i, v i ≤ q - n) ∧ (∑ i, v i) = d ∧
      P = rzOrbitSum (Fin n) (∏ i, X i ^ v i) := by
  classical
  obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hQ
  obtain ⟨hf, hw⟩ := Finset.mem_filter.mp hf
  obtain ⟨hlen, hbox⟩ := (mem_a2BoxModeSet q n hn f).mp hf
  let v := ksOccupationModes n f hlen
  refine ⟨v, ?_, ?_, ksBlockTheta_monomial n f hlen⟩
  · intro i
    have hmem : v i ∈ VOA.DeligneAudit.CLAssembly.lst f := List.get_mem _ _
    have hb := VOA.DeligneAudit.CLAssembly.boxP_lst hbox (v i) hmem
    rw [VOA.DeligneAudit.CLAssembly.length_lst, hlen] at hb
    omega
  · rw [← rz_sum_ofFn, ksOccupationModes_ofFn, a2_lst_sum, hw]

/-- The one-alphabet box spanning theorem, entirely in the block's
    symmetric polynomial ring and homogeneous in the mode degree. -/
theorem ksBlockSymmetric_span_graded (q n d : ℕ) (hn : n ≤ q)
    (P : MvPolynomial (Fin n) ℂ)
    (hP : P ∈ symmetricSubalgebra (Fin n) ℂ) (hd : P.IsHomogeneous d) :
    P ∈ Submodule.span ℂ (ksBlockBoxPolys q n d : Set _) ⊔
      ksBlockGarlandSpan q n d := by
  classical
  obtain ⟨Q, hQ, hQP⟩ := ksBlockTheta_surjective_graded n d P hP hd
  obtain ⟨B, hB, C, hC, hBC⟩ :=
    Submodule.mem_sup.mp (ksOneBox_span_graded q n d hn Q hQ)
  rw [← hQP, ← hQ.weightedHomogeneousComponent_same, ← hBC, map_add, map_add]
  apply Submodule.add_mem_sup
  · clear hBC
    induction hB using Submodule.span_induction with
    | mem B hB =>
        rw [(ksOneBoxPolys_homogeneous q n d B hB).weightedHomogeneousComponent_same]
        exact Submodule.subset_span (Finset.mem_image.mpr ⟨B, hB, rfl⟩)
    | zero => simp
    | add A B hA hB ihA ihB =>
        rw [map_add, map_add]
        exact Submodule.add_mem _ ihA ihB
    | smul t B hB ihB =>
        rw [map_smul, map_smul]
        exact Submodule.smul_mem _ t ihB
  · exact ksBlockTheta_component_J_mem q n d C hC

/-- When the block is longer than the Garland weight, the entire homogeneous
    symmetric component consists of subset Garland relations. -/
theorem ksBlockSymmetric_mem_Garland_of_length_gt (q n d : ℕ) (hn : q < n)
    (P : MvPolynomial (Fin n) ℂ)
    (hP : P ∈ symmetricSubalgebra (Fin n) ℂ) (hd : P.IsHomogeneous d) :
    P ∈ ksBlockGarlandSpan q n d := by
  obtain ⟨Q, hQ, rfl⟩ := ksBlockTheta_surjective_graded n d P hP hd
  exact ksBlockTheta_J_mem q n d Q (ksOneBox_J_of_length_gt q n d hn Q hQ) hQ

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksOneBoxPolys_homogeneous
#print axioms VOA.DeligneAudit.D4Levi.ksBlockBoxPolys_card_le
#print axioms VOA.DeligneAudit.D4Levi.ksBlockBoxPolys_spec
#print axioms VOA.DeligneAudit.D4Levi.ksBlockSymmetric_span_graded
#print axioms VOA.DeligneAudit.D4Levi.ksBlockSymmetric_mem_Garland_of_length_gt
