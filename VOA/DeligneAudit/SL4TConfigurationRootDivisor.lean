import VOA.DeligneAudit.SL4TDeformedRemainderVanishing

/-! The distinct selected sites give a large common divisor of the deformed remainders. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- The size of a selected alphabet is its occupied sites plus its fully selected doubles. -/
theorem fullFlag_selected_card (B k : ℕ) (Y : Finset (Fin B))
    (f : FullFlagConfiguration B k) :
    Y.card = (Y.image f.val).card + fullFlagDoublesIn Y f := by
  classical
  have hcount (a : Fin (B - k)) :
      (Y.filter fun i => f.val i = a).card =
        (if a ∈ Y.image f.val then 1 else 0) +
          (if a.val < k ∧ ∀ i, f.val i = a → i ∈ Y then 1 else 0) := by
    let S := Y.filter fun i => f.val i = a
    let T := Finset.univ.filter fun i => f.val i = a
    have hST : S ⊆ T := by intro i hi; simpa [S, T] using (Finset.mem_filter.mp hi).2
    have hT : T.card = if a.val < k then 2 else 1 := f.property a
    have hle : S.card ≤ T.card := Finset.card_le_card hST
    by_cases ha : a ∈ Y.image f.val
    · obtain ⟨i, hiY, hia⟩ := Finset.mem_image.mp ha
      have hpos : 0 < S.card := Finset.card_pos.mpr ⟨i, by simp [S, hiY, hia]⟩
      rw [if_pos ha]
      by_cases hd : a.val < k ∧ ∀ i, f.val i = a → i ∈ Y
      · rw [if_pos hd]
        have he : S = T := by
          apply Finset.Subset.antisymm hST
          intro i hi
          have hi' := (Finset.mem_filter.mp hi).2
          exact Finset.mem_filter.mpr ⟨hd.2 i hi', hi'⟩
        change S.card = _
        rw [he, hT, if_pos hd.1]
      · rw [if_neg hd, add_zero]
        change S.card = 1
        by_cases hak : a.val < k
        · rw [if_pos hak] at hT
          have hne : S.card ≠ 2 := by
            intro htwo
            have he : S = T := Finset.eq_of_subset_of_card_le hST (by omega)
            apply hd
            refine ⟨hak, ?_⟩
            intro u hu
            have huT : u ∈ T := by simp [T, hu]
            rw [← he] at huT
            exact (Finset.mem_filter.mp huT).1
          omega
        · rw [if_neg hak] at hT
          omega
    · have hzero : S = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        obtain ⟨hiY, hia⟩ := Finset.mem_filter.mp hi
        exact ha (Finset.mem_image.mpr ⟨i, hiY, hia⟩)
      have hnot : ¬ (a.val < k ∧ ∀ i, f.val i = a → i ∈ Y) := by
        rintro ⟨hak, hall⟩
        rw [if_pos hak] at hT
        obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
        have hia := (Finset.mem_filter.mp hi).2
        exact ha (Finset.mem_image.mpr ⟨i, hall i hia, hia⟩)
      change S.card = _
      rw [hzero, Finset.card_empty, if_neg ha, if_neg hnot, zero_add]
  have hs := Finset.sum_card_fiberwise_eq_card_filter Y Finset.univ f.val
  simp only [Finset.mem_univ, Finset.filter_true] at hs
  rw [← hs]
  simp only [hcount, Finset.sum_add_distrib, Finset.sum_boole, fullFlagDoublesIn]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id]

/-- One factor for each occupied image divides the product over all original positions. -/
theorem product_image_dvd_product {ι κ A : Type*} [DecidableEq κ] [CommMonoid A]
    (Y : Finset ι) (f : ι → κ) (g : κ → A) :
    (∏ a ∈ Y.image f, g a) ∣ ∏ i ∈ Y, g (f i) := by
  classical
  rw [← Finset.prod_fiberwise_of_maps_to' (fun i hi => Finset.mem_image_of_mem f hi) g]
  apply Finset.prod_dvd_prod_of_dvd
  intro a ha
  obtain ⟨i, hiY, hia⟩ := Finset.mem_image.mp ha
  exact Finset.dvd_prod_of_mem (fun _ => g a) (Finset.mem_filter.mpr ⟨hiY, hia⟩)

/-- The polynomial with one factor at each occupied selected site. -/
def selectedSitePolynomial (B k : ℕ) (Y : Finset (Fin B))
    (f : FullFlagConfiguration B k) (ζ : Fin (B - k) → ℂ) : Polynomial ℂ :=
  ∏ a ∈ Y.image f.val, (Polynomial.X - Polynomial.C (ζ a))

/-- The selected-site polynomial is monic. -/
theorem selectedSitePolynomial_monic (B k : ℕ) (Y : Finset (Fin B))
    (f : FullFlagConfiguration B k) (ζ : Fin (B - k) → ℂ) :
    (selectedSitePolynomial B k Y f ζ).Monic := by
  classical
  exact Polynomial.monic_prod_of_monic _ _ (fun a ha => Polynomial.monic_X_sub_C _)

/-- Its degree is the number of occupied selected sites. -/
theorem selectedSitePolynomial_natDegree (B k : ℕ) (Y : Finset (Fin B))
    (f : FullFlagConfiguration B k) (ζ : Fin (B - k) → ℂ) :
    (selectedSitePolynomial B k Y f ζ).natDegree = (Y.image f.val).card := by
  classical
  unfold selectedSitePolynomial
  have h := Polynomial.natDegree_prod_of_monic
    (s := Y.image f.val) (f := fun a => Polynomial.X - Polynomial.C (ζ a))
    (fun a ha => Polynomial.monic_X_sub_C _)
  simpa using h

/-- Evaluation turns the selected alphabet characteristic into its product of site factors. -/
theorem selectedAlphabetCharacteristic_evaluate (B k : ℕ) (Y : Finset (Fin B))
    (f : FullFlagConfiguration B k) (ζ : Fin (B - k) → ℂ) :
    alphabetCharacteristic ((fullFlagSubalphabet Y).map
      (MvPolynomial.aeval (fun i => ζ (f.val i)))) =
        ∏ i ∈ Y, (Polynomial.X - Polynomial.C (ζ (f.val i))) := by
  classical
  simp only [fullFlagSubalphabet, List.map_map, Function.comp_def, MvPolynomial.aeval_X,
    alphabetCharacteristic_product, List.map_map]
  simpa only [Finset.toList_toFinset] using
    (List.prod_toFinset (fun i => Polynomial.X - Polynomial.C (ζ (f.val i)))
      (Finset.nodup_toList Y)).symm

/-- The common divisor is contained in the evaluated selected characteristic. -/
theorem selectedSitePolynomial_dvd_characteristic (B k : ℕ) (Y : Finset (Fin B))
    (f : FullFlagConfiguration B k) (ζ : Fin (B - k) → ℂ) :
    selectedSitePolynomial B k Y f ζ ∣
      alphabetCharacteristic ((fullFlagSubalphabet Y).map
        (MvPolynomial.aeval (fun i => ζ (f.val i)))) := by
  rw [selectedAlphabetCharacteristic_evaluate]
  exact product_image_dvd_product Y f.val (fun a => Polynomial.X - Polynomial.C (ζ a))

/-- The same common divisor is contained in the scalar site polynomial. -/
theorem selectedSitePolynomial_dvd_sites (B k : ℕ) (Y : Finset (Fin B))
    (f : FullFlagConfiguration B k) (ζ : Fin (B - k) → ℂ) :
    selectedSitePolynomial B k Y f ζ ∣ alphabetCharacteristic (List.ofFn ζ) := by
  classical
  rw [alphabetCharacteristic_product, List.map_ofFn, List.prod_ofFn]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)

/-- Every deformed minor vanishes at a configuration below its stratum threshold. -/
theorem deformedRemainderMinor_configuration_zero (B k j : ℕ) (Y : Finset (Fin B))
    (ζ : Fin (B - k) → ℂ) (rows cols : Fin j → ℕ)
    (f : FullFlagStratumConfiguration B k j Y) :
    MvPolynomial.aeval (fullFlagStratumPoint B k j Y ζ f)
      (deformedRemainderMinor (fullFlagSubalphabet Y) (B - k) j
        (alphabetCharacteristic (List.ofFn ζ)) rows cols) = 0 := by
  rw [deformedRemainderMinor_evaluate _ _ _ _ (by
    rw [alphabetCharacteristic_natDegree, List.length_ofFn])]
  apply scalarRemainderMinor_eq_zero _ _ (selectedSitePolynomial B k Y f.val ζ) j
    (alphabetCharacteristic_monic _) (selectedSitePolynomial_monic B k Y f.val ζ)
    (selectedSitePolynomial_dvd_characteristic B k Y f.val ζ)
    (selectedSitePolynomial_dvd_sites B k Y f.val ζ)
  rw [alphabetCharacteristic_natDegree, List.length_map, fullFlagSubalphabet,
    List.length_map, Finset.length_toList, selectedSitePolynomial_natDegree]
  have hcard := fullFlag_selected_card B k Y f.val
  have hf := f.property
  omega

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.fullFlag_selected_card
#print axioms VOA.DeligneAudit.SL4T.product_image_dvd_product
#print axioms VOA.DeligneAudit.SL4T.selectedSitePolynomial_monic
#print axioms VOA.DeligneAudit.SL4T.selectedSitePolynomial_natDegree
#print axioms VOA.DeligneAudit.SL4T.selectedAlphabetCharacteristic_evaluate
#print axioms VOA.DeligneAudit.SL4T.selectedSitePolynomial_dvd_characteristic
#print axioms VOA.DeligneAudit.SL4T.selectedSitePolynomial_dvd_sites
#print axioms VOA.DeligneAudit.SL4T.deformedRemainderMinor_configuration_zero
