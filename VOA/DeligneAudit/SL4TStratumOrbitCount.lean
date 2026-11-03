import VOA.DeligneAudit.SL4TMiddleFlagStratumTransport

/-!
# The weighted stratum count as a sum over attained site colour multiplicities

A configuration places the positions on sites. Its site colour multiplicities record how many
positions of each colour sit at each site; these are the Young-subgroup orbits. A doubled site
is selected when all its positions have selected colours, and this count agrees with the
number of selected doubles of any configuration in the orbit. The stratum counts are therefore
the numbers of attained multiplicities with fewer than `j` selected doubled sites, and the
weighted stratum count is bounded by the sum, over attained multiplicities, of the cost of the
level `r` minus the number of selected doubled sites.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {C : Type*} [DecidableEq C] {B : ℕ} (colour : Fin B → C)

/-- The number of doubled sites all of whose positions have selected colours. -/
def selectedDoubleSiteCount (k : ℕ) (selected : Finset C) {S : ℕ} (m : Fin S → C → ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun a : Fin S => a.val < k ∧ ∀ c ∉ selected, m a c = 0).card

/-- The selected doubled sites of an orbit are the selected doubles of its configurations. -/
theorem selectedDoubleSiteCount_multiplicity (k : ℕ) (selected : Finset C)
    (f : FullFlagConfiguration B k) :
    selectedDoubleSiteCount k selected (configurationColourMultiplicity colour f) =
      fullFlagDoublesIn (selectedColourPositions colour selected) f := by
  unfold selectedDoubleSiteCount fullFlagDoublesIn
  apply congrArg Finset.card
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  apply and_congr_right
  intro _
  constructor
  · intro h i hi
    simp only [selectedColourPositions, Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hc
    have h0 := h (colour i) hc
    rw [configurationColourMultiplicity, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff] at h0
    exact h0 (Finset.mem_univ i) ⟨hi, rfl⟩
  · intro h c hc
    rw [configurationColourMultiplicity, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro i _ ⟨hi, rfl⟩
    have hY := h i hi
    simp only [selectedColourPositions, Finset.mem_filter, Finset.mem_univ, true_and] at hY
    exact hc hY

/-- The attained site colour multiplicities of all configurations. -/
def attainedColourMultiplicities (k : ℕ) : Finset (Fin (B - k) → C → ℕ) := by
  classical
  exact Finset.univ.image (fun f : FullFlagConfiguration B k =>
    configurationColourMultiplicity colour f)

theorem mem_attainedColourMultiplicities (k : ℕ) (m : Fin (B - k) → C → ℕ) :
    m ∈ attainedColourMultiplicities colour k ↔
      ∃ f : FullFlagConfiguration B k, configurationColourMultiplicity colour f = m := by
  classical
  unfold attainedColourMultiplicities
  simp

/-- The stratum counts are the numbers of attained multiplicities below the threshold. -/
theorem colourStratumCount_eq_card (k j : ℕ) (selected : Finset C) :
    colourStratumCount colour k j selected = ((attainedColourMultiplicities colour k).filter
      fun m => selectedDoubleSiteCount k selected m < j).card := by
  classical
  unfold colourStratumCount
  have he : Set.range (fun f : FullFlagStratumConfiguration B k j
      (selectedColourPositions colour selected) =>
        configurationColourMultiplicity colour f.val) =
      ↑((attainedColourMultiplicities colour k).filter
        fun m => selectedDoubleSiteCount k selected m < j) := by
    ext m
    simp only [Set.mem_range, Finset.coe_filter, Set.mem_setOf_eq,
      mem_attainedColourMultiplicities]
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨⟨f.val, rfl⟩, by
        rw [selectedDoubleSiteCount_multiplicity]
        exact f.property⟩
    · rintro ⟨⟨f, rfl⟩, hj⟩
      rw [selectedDoubleSiteCount_multiplicity] at hj
      exact ⟨⟨f, hj⟩, rfl⟩
  rw [he, Nat.card_coe_set_eq, Set.ncard_coe_finset]

/-- The weighted stratum count is at most the sum of level costs over attained
multiplicities. -/
theorem colourStratumCost_le_attained (k : ℕ) (selected : Finset C) :
    colourStratumCost colour k selected ≤
      ∑ m ∈ attainedColourMultiplicities colour k,
        lineLevelCost (selectedColourPositions colour selected).card
          ((selectedColourPositions colour selected).card -
            selectedDoubleSiteCount k selected m) := by
  classical
  set r := (selectedColourPositions colour selected).card
  set M := attainedColourMultiplicities colour k
  let s : (Fin (B - k) → C → ℕ) → ℕ := fun m => selectedDoubleSiteCount k selected m
  let g : ℕ → ℕ := fun j => lineLevelCost r (r - j)
  have hdiff (j : ℕ) : (M.filter fun m => s m < j + 1).card - (M.filter fun m => s m < j).card =
      (M.filter fun m => s m = j).card := by
    have hu : (M.filter fun m => s m < j + 1) =
        (M.filter fun m => s m < j) ∪ (M.filter fun m => s m = j) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hm, hj⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
        · exact Or.inl ⟨hm, h⟩
        · exact Or.inr ⟨hm, h⟩
      · rintro (⟨hm, h⟩ | ⟨hm, h⟩)
        · exact ⟨hm, by omega⟩
        · exact ⟨hm, by omega⟩
    have hd : Disjoint (M.filter fun m => s m < j) (M.filter fun m => s m = j) := by
      rw [Finset.disjoint_filter]
      intro m _ h1 h2
      omega
    rw [hu, Finset.card_union_of_disjoint hd]
    omega
  have hcost : colourStratumCost colour k selected =
      ∑ j ∈ Finset.range (r + 1), (M.filter fun m => s m = j).card * g j := by
    unfold colourStratumCost
    apply Finset.sum_congr rfl
    intro j _
    rw [colourStratumCount_eq_card, colourStratumCount_eq_card]
    exact congrArg (· * g j) (hdiff j)
  rw [hcost]
  calc ∑ j ∈ Finset.range (r + 1), (M.filter fun m => s m = j).card * g j
      = ∑ j ∈ Finset.range (r + 1),
          ∑ m ∈ (M.filter fun m => s m < r + 1).filter (fun m => s m = j), g (s m) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hf : (M.filter fun m => s m < r + 1).filter (fun m => s m = j) =
            M.filter fun m => s m = j := by
          rw [Finset.filter_filter]
          apply Finset.filter_congr
          intro m _
          constructor
          · exact fun h => h.2
          · intro h
            exact ⟨by have := Finset.mem_range.mp hj; omega, h⟩
        rw [hf, Finset.sum_congr rfl (fun m hm => by rw [(Finset.mem_filter.mp hm).2]),
          Finset.sum_const, smul_eq_mul]
    _ = ∑ m ∈ M.filter (fun m => s m < r + 1), g (s m) :=
        Finset.sum_fiberwise_of_maps_to (fun m hm =>
          Finset.mem_range.mpr (Finset.mem_filter.mp hm).2) _
    _ ≤ ∑ m ∈ M, g (s m) := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

end

end VOA.DeligneAudit.SL4T
