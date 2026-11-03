import VOA.DeligneAudit.D4LeviKSFlagBoxSpan
import VOA.DeligneAudit.D4LeviKSCorrectedCount

/-! The finite three-block box family and its corrected graded cardinality. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.Sl2Weyl

noncomputable def ksFlagBoxPolynomial (a b c : ℕ)
    (t : ((ℕ →₀ ℕ) × (ℕ →₀ ℕ)) × (ℕ →₀ ℕ)) :
    pairTargetSymmetric a b c :=
  ⟨ksTargetXMap a b c (ksBlockTheta a (monomial t.1.1 1)) *
      ksTargetYMap a b c (ksBlockTheta b (monomial t.1.2 1)) *
        ksTargetZMap a b c (ksBlockTheta c (monomial t.2 1)),
    (pairTargetSymmetric a b c).mul_mem
      ((pairTargetSymmetric a b c).mul_mem
        (ksTargetXMap_symmetric a b c _ (ksBlockTheta_symmetric a _))
        (ksTargetYMap_symmetric a b c _ (ksBlockTheta_symmetric b _)))
      (ksTargetZMap_symmetric a b c _ (ksBlockTheta_symmetric c _))⟩

noncomputable def ksFlagFiniteBox (m a b c d : ℕ) :
    Finset (pairTargetSymmetric a b c) := by
  classical
  exact ((ksBoxTriples m a b c).filter (fun t => ksBoxDegree t = d)).image
    (ksFlagBoxPolynomial a b c)

theorem ksFlagFiniteBox_card_le (m a b c d : ℕ) :
    (ksFlagFiniteBox m a b c d).card ≤ ksGradedBoxCount m a b c d := by
  exact Finset.card_image_le

/-- The polynomial boxes use exactly the occupation triples counted by the
    corrected count; coincidences of polynomial images can only decrease the count. -/
theorem ksFlagBoxSpan_le_finite (m a b c d : ℕ) :
    ksFlagBoxSpan m a b c d ≤
      (Submodule.span ℂ (ksFlagFiniteBox m a b c d : Set _)).map
        (Subalgebra.val (pairTargetSymmetric a b c)).toLinearMap := by
  classical
  apply Submodule.span_le.mpr
  rintro T ⟨dx, dy, dz, hd, P, hP, Q, hQ, R, hR, rfl⟩
  obtain ⟨P', hP', rfl⟩ := Finset.mem_image.mp hP
  obtain ⟨fx, hfx, rfl⟩ := Finset.mem_image.mp hP'
  obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.mp hQ
  obtain ⟨fy, hfy, rfl⟩ := Finset.mem_image.mp hQ'
  obtain ⟨R', hR', rfl⟩ := Finset.mem_image.mp hR
  obtain ⟨fz, hfz, rfl⟩ := Finset.mem_image.mp hR'
  obtain ⟨hfx, hdx⟩ := Finset.mem_filter.mp hfx
  obtain ⟨hfy, hdy⟩ := Finset.mem_filter.mp hfy
  obtain ⟨hfz, hdz⟩ := Finset.mem_filter.mp hfz
  refine ⟨ksFlagBoxPolynomial a b c ((fx, fy), fz), Submodule.subset_span ?_, rfl⟩
  apply Finset.mem_image.mpr
  refine ⟨((fx, fy), fz), Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
  · exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hfx, hfy⟩, hfz⟩
  · simpa only [ksBoxDegree, hdx, hdy, hdz] using hd

set_option maxHeartbeats 800000 in
-- Comparing the mapped submodules unfolds several nested finite box images.
/-- The full graded target component is spanned by a finite family of at most
    `ksGradedBoxCount` elements, modulo the established flag relations. -/
theorem ksFlag_homogeneous_finite_span (m a b c d : ℕ)
    (P : pairTargetSymmetric a b c)
    (hd : (P : MvPolynomial (PairTarget a b c) ℂ).IsHomogeneous d) :
    P ∈ Submodule.span ℂ (ksFlagFiniteBox m a b c d : Set _) ⊔
      ksFlagMaximalRelationSpan m a b c d := by
  by_cases hsize : a + b + c ≤ m
  · have hh := (sup_le_sup_right (ksFlagBoxSpan_le_finite m a b c d) _)
      (ksFlag_three_block_span m a b c d hsize P P.property hd)
    rw [ksFlagRelationImage, ← Submodule.map_sup] at hh
    obtain ⟨Q, hQ, heq⟩ := hh
    have he : Q = P := Subtype.ext heq
    simpa only [he] using hQ
  · rw [ksFlagMaximalRelationSpan_eq_top_of_overfull m a b c d (by omega)]
    simp

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksFlagFiniteBox_card_le
#print axioms VOA.DeligneAudit.D4Levi.ksFlagBoxSpan_le_finite
#print axioms VOA.DeligneAudit.D4Levi.ksFlag_homogeneous_finite_span
