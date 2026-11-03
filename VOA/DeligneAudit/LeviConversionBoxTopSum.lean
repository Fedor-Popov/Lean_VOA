import VOA.DeligneAudit.LeviConversionBoxTopPositions

/-! Rewrite the top Wick sum with explicit positional subsets. -/

namespace VOA.DeligneAudit.LeviConversion

noncomputable section

private theorem choices_map {ι κ : Type*} (g : ι → κ) (xs : List ι) :
    choices (xs.map g) =
      (choices xs).map (fun p => (p.1.map g, p.2.map g)) := by
  induction xs with
  | nil => simp [choices]
  | cons x xs ih =>
    simp only [List.map_cons, choices, ih, List.map_append, List.map_map]
    rfl

private theorem topSum_indexed {A : Type*} [Ring A] (a b : ℕ → A)
    (k s : ℕ) (xs : List ℕ) :
    topSum a b k s xs =
      ∑ T ∈ (Finset.univ : Finset (Fin xs.length)).powerset,
        let p := splitAt (List.finRange xs.length) T
        if p.2.length = k then
          aWord a (p.1.map xs.get) *
            PowerSeries.coeff s (bWord b (p.2.map xs.get))
        else 0 := by
  let g : List (Fin xs.length) × List (Fin xs.length) → A := fun p =>
    if p.2.length = k then
      aWord a (p.1.map xs.get) *
        PowerSeries.coeff s (bWord b (p.2.map xs.get))
    else 0
  have h := choices_sum_powerset (List.finRange xs.length)
    (List.nodup_finRange xs.length) g
  have hmap : (List.finRange xs.length).map xs.get = xs :=
    List.map_get_finRange xs
  calc
    topSum a b k s xs =
        ((choices ((List.finRange xs.length).map xs.get)).map
          (fun p => if p.2.length = k then
            aWord a p.1 * PowerSeries.coeff s (bWord b p.2) else 0)).sum := by
              simp only [hmap, topSum]
    _ = ((choices (List.finRange xs.length)).map g).sum := by
      rw [choices_map, List.map_map]
      simp only [g, Function.comp_def, List.length_map]
    _ = _ := by simpa only [List.toFinset_finRange, g] using h

/-- The top Wick sum is indexed by `powersetCard k` on the positions.
Repeated modes remain distinct because the subset consists of positions. -/
theorem topSum_powersetCard {A : Type*} [Ring A] (a b : ℕ → A)
    (k s : ℕ) (xs : List ℕ) :
    topSum a b k s xs =
      ∑ T ∈ (Finset.univ : Finset (Fin xs.length)).powersetCard k,
        let p := splitAt (List.finRange xs.length) T
        aWord a (p.1.map xs.get) *
          PowerSeries.coeff s (bWord b (p.2.map xs.get)) := by
  rw [topSum_indexed]
  simp only [Finset.powersetCard_eq_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T hT
  have hlen := splitAt_selected_length (List.finRange xs.length)
    (List.nodup_finRange xs.length) T
    (by simpa only [List.toFinset_finRange] using Finset.mem_powerset.mp hT)
  simp [hlen]

/-- The two terms in the requested partition of the top Wick sum. -/
def positionalTopTerm {A : Type*} [Ring A] (a b : ℕ → A)
    (s : ℕ) (xs : List ℕ) (T : Finset (Fin xs.length)) : A :=
  let p := splitAt (List.finRange xs.length) T
  aWord a (p.1.map xs.get) *
    PowerSeries.coeff s (bWord b (p.2.map xs.get))

theorem topSum_zero_nonzero_split {A : Type*} [Ring A] (a b : ℕ → A)
    (k s : ℕ) (xs : List ℕ) :
    topSum a b k s xs =
      ∑ T ∈ ((Finset.univ : Finset (Fin xs.length)).powersetCard k).filter
        (fun T => T ⊆ zeroPositions xs.get),
        positionalTopTerm a b s xs T +
      ∑ T ∈ ((Finset.univ : Finset (Fin xs.length)).powersetCard k).filter
        (fun T => ¬ T ⊆ zeroPositions xs.get),
        positionalTopTerm a b s xs T := by
  rw [topSum_powersetCard]
  simp only [positionalTopTerm]
  symm
  exact Finset.sum_filter_add_sum_filter_not _ _ _

/-- A subset of zero positions contributes exactly `k` zero tails. -/
theorem selected_modes_zero (xs : List ℕ) (k : ℕ)
    (T : Finset (Fin xs.length))
    (hT : T ∈ (Finset.univ : Finset (Fin xs.length)).powersetCard k)
    (hzero : T ⊆ zeroPositions xs.get) :
    (splitAt (List.finRange xs.length) T).2.map xs.get =
      List.replicate k 0 := by
  have hlen := splitAt_selected_length (List.finRange xs.length)
    (List.nodup_finRange xs.length) T
    (by simp)
  have hcard : T.card = k := (Finset.mem_powersetCard.mp hT).2
  apply List.eq_replicate_iff.mpr
  constructor
  · simpa [hcard] using hlen
  · intro z hz
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
    have hiT : i ∈ T := by simpa using (List.mem_filter.mp hi).2
    exact (Finset.mem_filter.mp (hzero hiT)).2

/-- The contracted power-series product for an all-zero positional choice. -/
theorem selected_bWord_zero {A : Type*} [Ring A] (b : ℕ → A)
    (xs : List ℕ) (k : ℕ) (T : Finset (Fin xs.length))
    (hT : T ∈ (Finset.univ : Finset (Fin xs.length)).powersetCard k)
    (hzero : T ⊆ zeroPositions xs.get) :
    bWord b ((splitAt (List.finRange xs.length) T).2.map xs.get) =
      fCurrent b ^ k := by
  rw [selected_modes_zero xs k T hT hzero]
  simp [bWord, bTail, fCurrent]

end
end VOA.DeligneAudit.LeviConversion

#print axioms VOA.DeligneAudit.LeviConversion.topSum_powersetCard
#print axioms VOA.DeligneAudit.LeviConversion.topSum_zero_nonzero_split
#print axioms VOA.DeligneAudit.LeviConversion.selected_modes_zero
#print axioms VOA.DeligneAudit.LeviConversion.selected_bWord_zero
