import VOA.DeligneAudit.LeviTypeA2CertCurrentCount

/-! Lower Wick terms lie in the Levi closure of higher radical keys. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.LeviConversion
open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

private theorem lower_choice_height (q k : ℕ) (xs ys : List ℕ)
    (t : List ℕ × List ℕ)
    (ht : t ∈ choices (xs ++ List.replicate k 0))
    (hlt : t.2.length < k) (d : ℕ) :
    a2KeyHeight q ⟨xs.length, ys.length + k, d⟩ <
      (q : ℤ) + (t.1.length : ℤ) - (ys.length + t.2.length : ℕ) := by
  have hc := choices_length (xs ++ List.replicate k 0) t ht
  simp only [List.length_append, List.length_replicate] at hc
  dsimp [a2KeyHeight]
  omega

/-- Each summand after expanding the two current coefficients lies in the
Levi closure of keys above the original radical count pair. -/
theorem a2_f2_lower_wick_summand (q k : ℕ) (xs ys : List ℕ)
    (t : List ℕ × List ℕ)
    (ht : t ∈ choices (xs ++ List.replicate k 0))
    (hlt : t.2.length < k) (d : ℕ)
    (z : ℕ × ℕ) :
    ((PowerSeries.coeff z.1
          (fCurrent (fun i => ρ.op 4 i) ^ (k - t.2.length)) *
        aWord (fun i => ρ.op 3 i) t.1) *
        PowerSeries.coeff z.2 (bWord (fun i => ρ.op 5 i) t.2)) •
      ((ys.map fun i => ρ.op 5 i).prod • w) ∈
        a2LeviClosure ρ
          (a2HigherKeySpan ρ w q ⟨xs.length, ys.length + k, d⟩) := by
  let K : A2RadicalKey := ⟨xs.length, ys.length + k, d⟩
  let N := a2LeviClosure ρ (a2HigherKeySpan ρ w q K)
  have hys : (ys.map fun i => ρ.op 5 i).prod w ∈
      a2CountSpan ρ w 0 ys.length := by
    simpa using a2CountSpan_second_word ρ w ys 0 0 (a2CountSpan_zero ρ w)
  have hb := a2_bWord_coeff_count ρ w t.2 z.2 0 ys.length hys
  have ha := a2CountSpan_first_word ρ w t.1 0
    (ys.length + t.2.length) hb
  have hbase : (aWord (fun i => ρ.op 3 i) t.1 *
      PowerSeries.coeff z.2 (bWord (fun i => ρ.op 5 i) t.2)) •
        ((ys.map fun i => ρ.op 5 i).prod • w) ∈ N := by
    have hmem : (aWord (fun i => ρ.op 3 i) t.1 *
        PowerSeries.coeff z.2 (bWord (fun i => ρ.op 5 i) t.2)) •
          ((ys.map fun i => ρ.op 5 i).prod • w) ∈
        a2CountSpan ρ w t.1.length (ys.length + t.2.length) := by
      simpa [aWord, mul_smul] using ha
    exact a2LeviClosure_contains ρ _
      (a2CountSpan_le_higher ρ w q K _ _
        (lower_choice_height q k xs ys t ht hlt d) hmem)
  have hf := a2_fCurrent_pow_preserves ρ
    (a2HigherKeySpan ρ w q K) (k - t.2.length) z.1 hbase
  simpa [N, K, mul_assoc, mul_smul] using hf

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_f2_lower_wick_summand
