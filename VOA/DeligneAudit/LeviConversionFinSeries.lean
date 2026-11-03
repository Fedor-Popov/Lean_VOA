import VOA.DeligneAudit.LeviConversionFinset
import VOA.DeligneAudit.LeviConversionSeries

/-! Wick's identity indexed by subsets of `Fin n`. -/

namespace VOA.DeligneAudit.LeviConversion

noncomputable section

variable {A : Type*} [Ring A]

/-- The power-series Wick identity, with repeated modes represented by distinct
positions in `Fin n` and subsets grouped by their cardinality. -/
theorem wick_series_powersetCard (f a b : ℕ → A)
    (hfa : ∀ i j, f i * a j - a j * f i = b (i + j))
    (hfb : ∀ i j, f i * b j = b j * f i)
    (hab : ∀ i j, a i * b j = b j * a i)
    (n k : ℕ) (x : Fin n → ℕ) :
    ((List.finRange n).map fun i => aConst a (x i)).prod * fCurrent f ^ k =
      ∑ t ∈ Finset.range (n + 1),
        ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard t,
          wickTerm (fCurrent f) (fun i => aConst a (x i))
            (fun i => bTail b (x i)) k (splitAt (List.finRange n) T) := by
  have h := wick_identity_powersetCard (fCurrent f)
    (fun i : Fin n => aConst a (x i)) (fun i : Fin n => bTail b (x i))
    (fun i => current_comm_a f a b hfa (x i))
    (fun i => current_comm_b f b hfb (x i))
    (fun i j => const_comm_tail a b hab (x i) (x j))
    k (List.finRange n) (List.nodup_finRange n)
  simpa only [List.length_finRange, List.toFinset_finRange] using h

end
end VOA.DeligneAudit.LeviConversion

#print axioms VOA.DeligneAudit.LeviConversion.wick_series_powersetCard
