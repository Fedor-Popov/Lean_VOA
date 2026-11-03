import VOA.DeligneAudit.LeviConversionCore

/-! Positional Wick choices as subsets of a finite set of distinct labels. -/

namespace VOA.DeligneAudit.LeviConversion

noncomputable section

variable {ι : Type*} [DecidableEq ι]

def splitAt (xs : List ι) (T : Finset ι) : List ι × List ι :=
  (xs.filter fun x => x ∉ T, xs.filter fun x => x ∈ T)

private theorem splitAt_insert_of_not_mem (xs : List ι) (T : Finset ι) (x : ι)
    (hx : x ∉ xs.toFinset) : splitAt xs (insert x T) = splitAt xs T := by
  apply Prod.ext
  · change xs.filter (fun z => z ∉ insert x T) = xs.filter (fun z => z ∉ T)
    apply List.filter_congr
    intro z hz
    have hzx : z ≠ x := by
      intro h
      apply hx
      simpa using (h ▸ hz)
    simp [Finset.mem_insert, hzx]
  · change xs.filter (fun z => z ∈ insert x T) = xs.filter (fun z => z ∈ T)
    apply List.filter_congr
    intro z hz
    have hzx : z ≠ x := by
      intro h
      apply hx
      simpa using (h ▸ hz)
    simp [Finset.mem_insert, hzx]

private theorem splitAt_cons_not_mem (xs : List ι) (T : Finset ι) (x : ι)
    (hx : x ∉ T) :
    splitAt (x :: xs) T = (x :: (splitAt xs T).1, (splitAt xs T).2) := by
  simp [splitAt, hx]

private theorem splitAt_cons_insert (xs : List ι) (T : Finset ι) (x : ι)
    (hx : x ∉ xs.toFinset) :
    splitAt (x :: xs) (insert x T) =
      ((splitAt xs T).1, x :: (splitAt xs T).2) := by
  rw [show splitAt (x :: xs) (insert x T) =
    ((splitAt xs (insert x T)).1, x :: (splitAt xs (insert x T)).2) by
      simp [splitAt]]
  rw [splitAt_insert_of_not_mem xs T x hx]

theorem choices_sum_powerset {B : Type*} [AddCommMonoid B] (xs : List ι)
    (hnd : xs.Nodup) (g : List ι × List ι → B) :
    ((choices xs).map g).sum =
      ∑ T ∈ xs.toFinset.powerset, g (splitAt xs T) := by
  induction xs generalizing g with
  | nil => simp [choices, splitAt]
  | cons x xs ih =>
      have hx : x ∉ xs.toFinset := by simpa using (List.nodup_cons.mp hnd).1
      have hnd' : xs.Nodup := (List.nodup_cons.mp hnd).2
      simp only [choices, List.map_append, List.sum_append,
        List.map_map, Function.comp_def, List.toFinset_cons]
      rw [Finset.sum_powerset_insert hx]
      rw [ih hnd' (fun p => g (x :: p.1, p.2)),
        ih hnd' (fun p => g (p.1, x :: p.2))]
      congr 1
      · apply Finset.sum_congr rfl
        intro T hT
        rw [splitAt_cons_not_mem xs T x
          (Finset.notMem_of_mem_powerset_of_notMem hT hx)]
      · apply Finset.sum_congr rfl
        intro T hT
        rw [splitAt_cons_insert xs T x hx]

theorem splitAt_selected_length (xs : List ι) (hnd : xs.Nodup)
    (T : Finset ι) (hT : T ⊆ xs.toFinset) :
    (splitAt xs T).2.length = T.card := by
  have hnd' : (xs.filter fun x => x ∈ T).Nodup := hnd.filter _
  have hset : (xs.filter fun x => x ∈ T).toFinset = T := by
    ext x
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.mp (hT h), h⟩⟩
  change (xs.filter fun x => x ∈ T).length = T.card
  rw [← List.toFinset_card_of_nodup hnd', hset]

variable {R : Type*} [Ring R]

/-- The Wick expansion indexed by actual finite subsets of distinct labels. -/
theorem wick_identity_powerset (F : R) (a b : ι → R)
    (hFA : ∀ i, F * a i - a i * F = b i)
    (hFB : ∀ i, F * b i = b i * F)
    (hAB : ∀ i j, a i * b j = b j * a i)
    (k : ℕ) (xs : List ι) (hnd : xs.Nodup) :
    (xs.map a).prod * F ^ k =
      ∑ T ∈ xs.toFinset.powerset,
        wickTerm F a b k (splitAt xs T) := by
  rw [wick_identity F a b hFA hFB hAB k xs]
  exact choices_sum_powerset xs hnd _

/-- The same identity grouped by contraction count using `powersetCard`. -/
theorem wick_identity_powersetCard (F : R) (a b : ι → R)
    (hFA : ∀ i, F * a i - a i * F = b i)
    (hFB : ∀ i, F * b i = b i * F)
    (hAB : ∀ i j, a i * b j = b j * a i)
    (k : ℕ) (xs : List ι) (hnd : xs.Nodup) :
    (xs.map a).prod * F ^ k =
      ∑ t ∈ Finset.range (xs.length + 1),
        ∑ T ∈ xs.toFinset.powersetCard t,
          wickTerm F a b k (splitAt xs T) := by
  rw [wick_identity_powerset F a b hFA hFB hAB k xs hnd]
  calc
    (∑ T ∈ xs.toFinset.powerset, wickTerm F a b k (splitAt xs T)) =
        ∑ t ∈ Finset.range (xs.length + 1),
          ∑ T ∈ xs.toFinset.powerset with T.card = t,
            wickTerm F a b k (splitAt xs T) := by
              symm
              apply Finset.sum_fiberwise_of_maps_to
              intro T hT
              have hc := Finset.card_le_card (Finset.mem_powerset.mp hT)
              simpa only [List.toFinset_card_of_nodup hnd, Finset.mem_range,
                Nat.lt_succ_iff] using hc
    _ = _ := by simp only [Finset.powersetCard_eq_filter]

end
end VOA.DeligneAudit.LeviConversion

#print axioms VOA.DeligneAudit.LeviConversion.wick_identity_powerset
#print axioms VOA.DeligneAudit.LeviConversion.wick_identity_powersetCard
