import VOA.DeligneAudit.SL4TSiteWordCatalog
import VOA.DeligneAudit.SL4TMultiDoubledAssembly

/-!
# The multi-doubled-site rank bound for the truncated sl4 Weyl module

An attained site colour multiplicity function has two positions at each doubled site, one at
each simple site, and the block lengths as colour totals. It is therefore the multiplicity
function of a word of the catalog with the same colour content, whose triples are its
selected doubled sites. Distinct multiplicity functions give distinct words, so the sum of
level costs over attained multiplicities is at most the sum over the words of the block.
For the canonical colouring of a valid middle tuple the block of a word is determined by its
colour content, and the level cost of a catalog word is its contribution, so this sum is the
word count of the block.

Together with the transport of the stratum line flags, this constructs the coefficient flag
of every valid block for every positive number of doubled sites, and discharges the flag
hypothesis of the Levi assembly:

    dim W^{sl4}(B ω₂, B - k) ≤ 20 ^ k * 6 ^ (B - 2 * k)   for all 2 * k ≤ B.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

section Words

variable {B : ℕ} (colour : Fin B → Fin 4)

/-- An attained multiplicity function has two positions at each doubled site and one at each
simple site. -/
theorem attainedColourMultiplicities_site_total (k : ℕ) (m : Fin (B - k) → Fin 4 → ℕ)
    (hm : m ∈ attainedColourMultiplicities colour k) (a : Fin (B - k)) :
    ∑ c, m a c = if a.val < k then 2 else 1 := by
  classical
  obtain ⟨f, rfl⟩ := (mem_attainedColourMultiplicities colour k m).mp hm
  rw [← f.property a, Finset.card_eq_sum_card_fiberwise (f := colour) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro c _
  unfold configurationColourMultiplicity
  rw [Finset.filter_filter]

/-- The colour totals of an attained multiplicity function are the colour class sizes. -/
theorem attainedColourMultiplicities_colour_total (k : ℕ) (m : Fin (B - k) → Fin 4 → ℕ)
    (hm : m ∈ attainedColourMultiplicities colour k) (c : Fin 4) :
    ∑ a, m a c = (Finset.univ.filter fun i => colour i = c).card := by
  classical
  obtain ⟨f, rfl⟩ := (mem_attainedColourMultiplicities colour k m).mp hm
  rw [Finset.card_eq_sum_card_fiberwise (f := f.val) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro a _
  unfold configurationColourMultiplicity
  rw [Finset.filter_filter]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i _
  exact and_comm

theorem not_mem_characteristic_iff (v : Fin 4 → ℕ) :
    (∀ c ∉ ({1, 3} : Finset (Fin 4)), v c = 0) ↔ (v 0 = 0 ∧ v 2 = 0) := by
  constructor
  · intro h
    exact ⟨h 0 (by decide), h 2 (by decide)⟩
  · rintro ⟨h0, h2⟩ c hc
    fin_cases c
    · exact h0
    · exact absurd (by decide) hc
    · exact h2
    · exact absurd (by decide) hc

/-- The decoded doubled sites of an attained multiplicity function. -/
theorem siteWordOf_doubled (k n : ℕ) (hS : B - k = k + n) (m : Fin (B - k) → Fin 4 → ℕ)
    (hm : m ∈ attainedColourMultiplicities colour k) (a : Fin k) :
    doubledSiteColourCount ((siteWordOf k n hS m).1 a) = m ⟨a.val, by omega⟩ := by
  apply doubledSiteIndexOf_spec
  rw [attainedColourMultiplicities_site_total colour k m hm, if_pos a.isLt]

/-- The decoded simple sites of an attained multiplicity function. -/
theorem siteWordOf_simple (k n : ℕ) (hS : B - k = k + n) (m : Fin (B - k) → Fin 4 → ℕ)
    (hm : m ∈ attainedColourMultiplicities colour k) (b : Fin n) :
    simpleSiteColourCount ((siteWordOf k n hS m).2 b) = m ⟨k + b.val, by omega⟩ := by
  apply simpleSiteIndexOf_spec
  rw [attainedColourMultiplicities_site_total colour k m hm]
  have hb : ¬ (k + b.val < k) := by omega
  exact if_neg hb

/-- Distinct attained multiplicity functions have distinct words. -/
theorem siteWordOf_injOn (k n : ℕ) (hS : B - k = k + n) :
    Set.InjOn (siteWordOf k n hS) (attainedColourMultiplicities colour k) := by
  intro m hm m' hm' h
  funext a
  by_cases ha : a.val < k
  · have h₁ := siteWordOf_doubled colour k n hS m hm ⟨a.val, ha⟩
    have h₂ := siteWordOf_doubled colour k n hS m' hm' ⟨a.val, ha⟩
    rw [h] at h₁
    exact h₁.symm.trans h₂
  · have hb : a.val - k < n := by omega
    have h₁ := siteWordOf_simple colour k n hS m hm ⟨a.val - k, hb⟩
    have h₂ := siteWordOf_simple colour k n hS m' hm' ⟨a.val - k, hb⟩
    rw [h] at h₁
    have ha' : (⟨k + (a.val - k), by omega⟩ : Fin (B - k)) = a := Fin.ext (by simp; omega)
    rw [ha'] at h₁ h₂
    exact h₁.symm.trans h₂

/-- The word of an attained multiplicity function has the colour class sizes as content. -/
theorem siteWordOf_content (k n : ℕ) (hS : B - k = k + n) (m : Fin (B - k) → Fin 4 → ℕ)
    (hm : m ∈ attainedColourMultiplicities colour k) :
    siteWordContent (siteWordOf k n hS m) =
      fun c => (Finset.univ.filter fun i => colour i = c).card := by
  funext c
  unfold siteWordContent
  rw [← attainedColourMultiplicities_colour_total colour k m hm c, sum_sites_split k n hS]
  congr 1
  · exact Finset.sum_congr rfl fun a _ => congrFun (siteWordOf_doubled colour k n hS m hm a) c
  · exact Finset.sum_congr rfl fun b _ => congrFun (siteWordOf_simple colour k n hS m hm b) c

/-- The triples of the word of an attained multiplicity function are its selected doubled
sites. -/
theorem siteWordOf_triples (k n : ℕ) (hS : B - k = k + n) (m : Fin (B - k) → Fin 4 → ℕ)
    (hm : m ∈ attainedColourMultiplicities colour k) :
    siteWordTriples (siteWordOf k n hS m) = selectedDoubleSiteCount k {1, 3} m := by
  classical
  unfold siteWordTriples selectedDoubleSiteCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, sum_sites_split k n hS]
  have hz (b : ℕ) : ¬ (k + b < k) := by omega
  simp only [hz, false_and, if_false, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr rfl
  intro a _
  rw [doubledSiteTripleCount_eq, siteWordOf_doubled colour k n hS m hm a,
    not_mem_characteristic_iff]
  simp [a.isLt]

/-- The level costs of attained multiplicities are bounded by those of the words with the
same colour content. -/
theorem attained_sum_le_wordSum (k n : ℕ) (hS : B - k = k + n) (g : ℕ → ℕ) :
    ∑ m ∈ attainedColourMultiplicities colour k, g (selectedDoubleSiteCount k {1, 3} m) ≤
      ∑ w : SiteWord k n, if siteWordContent w =
        (fun c => (Finset.univ.filter fun i => colour i = c).card) then
          g (siteWordTriples w) else 0 := by
  classical
  rw [← Finset.sum_filter]
  calc ∑ m ∈ attainedColourMultiplicities colour k, g (selectedDoubleSiteCount k {1, 3} m)
      = ∑ m ∈ attainedColourMultiplicities colour k,
          g (siteWordTriples (siteWordOf k n hS m)) :=
        Finset.sum_congr rfl fun m hm => by rw [siteWordOf_triples colour k n hS m hm]
    _ = ∑ w ∈ (attainedColourMultiplicities colour k).image (siteWordOf k n hS),
          g (siteWordTriples w) := by
        rw [Finset.sum_image (siteWordOf_injOn colour k n hS)]
    _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset
        intro w hw
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hw
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, siteWordOf_content colour k n hS m hm⟩

end Words

section Middle

variable (q : MixedParams) (hq : MixedValid q) (hA : q.A = 0)

include hq hA

/-- The colour classes of the canonical colouring have the block lengths. -/
theorem middleFlagPosition_colourCount (c : Fin 4) :
    (Finset.univ.filter fun i => middleFlagPositionColour q hq hA i = c).card =
      middleFlagLength q c := by
  classical
  rw [← Fintype.card_subtype, ← Fintype.card_congr (middleFlagPositionFibre q hq hA c),
    Fintype.card_fin]

/-- A valid middle tuple is recovered from its block lengths. -/
theorem mixedParamsOfContent_middleFlagLength :
    mixedParamsOfContent (middleFlagLength q) = q := by
  obtain ⟨hd1, hd3⟩ := middleFlag_outer_lengths q hq hA
  obtain ⟨A, B, d1, d2, d3, e1, e2⟩ := q
  simp only at hA hd1 hd3
  simp only [MixedValid, mixedP, mixedQ] at hq
  simp only [mixedParamsOfContent, middleFlagLength, mixedP, mixedQ, MixedParams.mk.injEq]
  simp
  omega

/-- The weighted stratum count of a valid block is at most its word count. -/
theorem middleFlag_stratumCost_le_blockBound (k : ℕ) (hkB : 2 * k ≤ q.B.toNat) :
    colourStratumCost (middleFlagPositionColour q hq hA) k {1, 3} ≤
      multiDoubledSiteBlockBound q.B.toNat k q := by
  classical
  have hr : (selectedColourPositions (middleFlagPositionColour q hq hA) {1, 3}).card =
      (mixedWeight q).toNat := middleFlagSelected_card q hq hA
  have hL : (fun c => (Finset.univ.filter
      fun i => middleFlagPositionColour q hq hA i = c).card) = middleFlagLength q :=
    funext (middleFlagPosition_colourCount q hq hA)
  have hS : q.B.toNat - k = k + (q.B.toNat - 2 * k) := by omega
  refine (colourStratumCost_le_attained (middleFlagPositionColour q hq hA) k {1, 3}).trans ?_
  rw [hr]
  refine (attained_sum_le_wordSum (middleFlagPositionColour q hq hA) k (q.B.toNat - 2 * k) hS
    (fun j => lineLevelCost (mixedWeight q).toNat ((mixedWeight q).toNat - j))).trans
    (le_of_eq ?_)
  rw [hL]
  unfold multiDoubledSiteBlockBound
  rw [mixedCatalogFiber_map_sum]
  have hcat : ((multiDoubledSiteCellCatalog k (q.B.toNat - 2 * k)).map
      (fun c => if c.1 = q then mixedCellContribution c.2 else 0)).sum =
      ((multiDoubledSiteCellCatalog k (q.B.toNat - 2 * k)).map
        (fun c => if c.1 = q then lineLevelCost (mixedWeight q).toNat
          ((mixedWeight q).toNat - c.2.2) else 0)).sum := by
    congr 1
    apply List.map_congr_left
    intro c hc
    by_cases hcq : c.1 = q
    · rw [if_pos hcq, if_pos hcq]
      have hw := multiDoubledSiteCellCatalog_weight k (q.B.toNat - 2 * k) c hc
      have hb := multiDoubledSiteCellCatalog_balanced k (q.B.toNat - 2 * k) c hc
      rw [hcq] at hw hb
      have hlev : (mixedWeight q).toNat - c.2.2 = mixedCellLevel c.2 := by
        have h₁ : (mixedWeight q).toNat = c.2.1 + 2 * c.2.2 := by rw [hw]; omega
        simp only [mixedCellLevel]
        omega
      rw [← hb, lineLevelCost, hlev]
    · rw [if_neg hcq, if_neg hcq]
  rw [hcat, multiDoubledSiteCellCatalog_map_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [siteWordData_params, siteWordData_triples]
  have hiff : mixedParamsOfContent (siteWordContent w) = q ↔
      siteWordContent w = middleFlagLength q := by
    constructor
    · intro h
      apply mixedParamsOfContent_injective
      rw [h, mixedParamsOfContent_middleFlagLength q hq hA]
    · intro h
      rw [h, mixedParamsOfContent_middleFlagLength q hq hA]
  by_cases hw : siteWordContent w = middleFlagLength q
  · rw [if_pos hw, if_pos (hiff.mpr hw)]
  · rw [if_neg hw, if_neg (fun h => hw (hiff.mp h))]

end Middle

/-- Every valid block carries the concrete coefficient flag, for every positive number of
doubled sites. -/
theorem multiDoubledSiteCoefficientFlag_valid (B k : ℕ) (hk : 1 ≤ k) (hkB : 2 * k ≤ B)
    (q : MixedParams) (hq : q ∈ mixedValidBlocks 0 B) :
    MultiDoubledSiteCoefficientFlag B k q := by
  obtain ⟨hv, hA, hB⟩ := (mem_mixedValidBlocks 0 B q).mp hq
  have hA0 : q.A = 0 := by simpa using hA
  have hBn : q.B.toNat = B := by omega
  have h := multiDoubledSiteCoefficientFlag_of_stratumCost q hv hA0 k hk (by omega)
    (middleFlag_stratumCost_le_blockBound q hv hA0 k (by omega))
  rw [hBn] at h
  exact h

/-- The truncated sl4 Weyl module with highest weight `B ω₂` and current truncation `B - k`
is finite-dimensional of dimension at most `20 ^ k * 6 ^ (B - 2 k)`, for every `2 k ≤ B`:
each doubled site contributes twenty and each simple site six. -/
theorem truncatedWeyl_sl4_multiDoubledSite_rank_le (B k : ℕ) (hk : 2 * k ≤ B) :
    FiniteDimensional ℂ (TruncatedLabelModule 0 B 0 (B - k)) ∧
      Module.finrank ℂ (TruncatedLabelModule 0 B 0 (B - k)) ≤ 20 ^ k * 6 ^ (B - 2 * k) := by
  by_cases hk0 : k = 0
  · subst k
    simpa using truncatedLabelModule_finite_and_local_bound 0 B 0 B
  · exact truncatedWeyl_sl4_multiDoubledSite_rank_le_of_flags B k hk
      (fun q hq => multiDoubledSiteCoefficientFlag_valid B k (by omega) hk q hq)

end

end VOA.DeligneAudit.SL4T
