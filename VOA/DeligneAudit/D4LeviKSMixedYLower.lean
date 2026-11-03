import VOA.DeligneAudit.D4LeviKSMixedXLower

/-! Partial YZG contractions have strictly higher D4 Levi key. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

private def yMixedKey (rs xs : List ℕ) (c d : ℕ) : RadicalKey :=
  rzKey xs (List.replicate rs.length 0) [] c d

theorem y_mixed_lower_term (rs xs : List ℕ) (c d : ℕ)
    (p : List ℕ × List ℕ)
    (hp : p ∈ choices (xs ++ List.replicate c 0))
    (hshort : p.2.length < c) (q : ℕ × ℕ) :
    (conversionTerm (fTopOp ρ) (xOp ρ) (zOp ρ) c q.1 p *
      PowerSeries.coeff q.2
        (rs.map (transportCurrent (yOp ρ))).prod) w ∈
      higherOrbit ρ w m (yMixedKey rs xs c d) := by
  let N := higherOrbit ρ w m (yMixedKey rs xs c d)
  let B := (rs.map (transportCurrent (yOp ρ))).prod
  have hB : PowerSeries.coeff q.2 B w ∈
      xyzCountSpan ρ w 0 rs.length 0 := by
    simpa [B] using y_transport_coeff_count ρ w rs q.2 0 0 0
      (xyzCountSpan_zero ρ w)
  have hlen := choices_length (xs ++ List.replicate c 0) p hp
  simp only [List.length_append, List.length_replicate] at hlen
  have hheight : keyHeight m (yMixedKey rs xs c d) <
      4 * (m : ℤ) + 2 * p.1.length - 2 * rs.length - 4 * p.2.length := by
    dsimp [yMixedKey, rzKey, keyHeight]
    simp only [List.length_replicate, add_zero]
    omega
  have hterm (t : ℕ × ℕ) :
      ((PowerSeries.coeff t.1 (fCurrent (fTopOp ρ) ^ (c - p.2.length)) *
          aWord (xOp ρ) p.1) *
          PowerSeries.coeff t.2 (bWord (zOp ρ) p.2)) •
        (PowerSeries.coeff q.2 B w) ∈ N := by
    have hz : PowerSeries.coeff t.2 (bWord (zOp ρ) p.2)
        (PowerSeries.coeff q.2 B w) ∈
        xyzCountSpan ρ w 0 rs.length p.2.length := by
      simpa using xyzCountSpan_z_coeff ρ w p.2 t.2 0 rs.length 0 hB
    have hx := xyzCountSpan_x_word ρ w p.1 0 rs.length p.2.length hz
    have hbase :
        (aWord (xOp ρ) p.1 *
          PowerSeries.coeff t.2 (bWord (zOp ρ) p.2)) •
          (PowerSeries.coeff q.2 B w) ∈ N := by
      apply xyzCountSpan_le_higher ρ w m p.1.length rs.length p.2.length
        (yMixedKey rs xs c d) hheight
      simpa [aWord, mul_smul] using hx
    have hf := fTop_coeff_preserves_higher ρ w m
      (yMixedKey rs xs c d) (c - p.2.length) t.1 hbase
    simpa [N, mul_assoc, mul_smul] using hf
  have hsum :
      (∑ t ∈ Finset.antidiagonal q.1,
        (PowerSeries.coeff t.1 (fCurrent (fTopOp ρ) ^ (c - p.2.length)) *
          aWord (xOp ρ) p.1) *
          PowerSeries.coeff t.2 (bWord (zOp ρ) p.2)) •
        (PowerSeries.coeff q.2 B w) ∈ N := by
    rw [Finset.sum_smul]
    exact N.sum_mem (fun t ht => hterm t)
  have hscalar (z : ℂ) :
      (algebraMap ℂ (Module.End ℂ V) z) •
        ((∑ t ∈ Finset.antidiagonal q.1,
          (PowerSeries.coeff t.1
            (fCurrent (fTopOp ρ) ^ (c - p.2.length)) *
              aWord (xOp ρ) p.1) *
            PowerSeries.coeff t.2 (bWord (zOp ρ) p.2)) •
          (PowerSeries.coeff q.2 B w)) ∈ N := by
    simpa using N.smul_mem z hsum
  have hcast : ((-1 : Module.End ℂ V) ^ p.2.length *
      (c.descFactorial p.2.length : Module.End ℂ V)) =
      algebraMap ℂ (Module.End ℂ V)
        ((-1 : ℂ) ^ p.2.length * (c.descFactorial p.2.length : ℂ)) := by
    simp
  unfold conversionTerm
  rw [hcast]
  simpa only [mul_smul] using
    hscalar ((-1 : ℂ) ^ p.2.length * (c.descFactorial p.2.length : ℂ))

theorem y_mixed_lower_mem (rs xs : List ℕ) (c s d : ℕ) :
    mixedLower (fTopOp ρ) (xOp ρ) (zOp ρ) c s
      (xs ++ List.replicate c 0)
      (rs.map (transportCurrent (yOp ρ))).prod w ∈
        higherOrbit ρ w m (yMixedKey rs xs c d) := by
  let N := higherOrbit ρ w m (yMixedKey rs xs c d)
  change (∑ q ∈ Finset.antidiagonal s,
    lowerSum (fTopOp ρ) (xOp ρ) (zOp ρ) c q.1
      (xs ++ List.replicate c 0) *
      PowerSeries.coeff q.2
        (rs.map (transportCurrent (yOp ρ))).prod) • w ∈ N
  rw [Finset.sum_smul]
  apply N.sum_mem
  intro q hq
  have hl := lowerSum_mem_of_higher_terms (fTopOp ρ) (xOp ρ) (zOp ρ)
    c q.1 (xs ++ List.replicate c 0)
    (PowerSeries.coeff q.2
      (rs.map (transportCurrent (yOp ρ))).prod) w N
    (fun p hp hshort => by
      simpa [mul_smul] using
        y_mixed_lower_term ρ w m rs xs c d p hp hshort q)
  simpa [mul_smul] using hl

/-- Graded YZG(b) in its full positional-contraction form. -/
theorem yz_full_contractions_higher
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (rs xs : List ℕ) (c s : ℕ)
    (hK : 1 ≤ rs.length) (hks : m + 1 ≤ c + rs.length + s) :
    mixedTop (xOp ρ) (zOp ρ) c s (xs ++ List.replicate c 0)
      (rs.map (transportCurrent (yOp ρ))).prod w ∈
      higherOrbit ρ w m
        (rzKey xs (List.replicate rs.length 0) [] c
          (rs.sum + xs.sum + s)) := by
  apply mixed_top_mem_of_lower w (fTopOp ρ) (xOp ρ) (zOp ρ)
    (fTop_x_comm ρ) (fTop_z_comm ρ)
    (fun i j => by
      ext v
      simpa [xOp, zOp] using radical_ops_comm ρ 1 5 i j v)
  · exact y_partial_garland_zero ρ w m h rs c s (by omega) hks
  · exact y_mixed_lower_mem ρ w m rs xs c s
      (rs.sum + xs.sum + s)

/-- The indexed YZG(b) relation in the descending D4 key prefix. -/
theorem yz_full_contractions_prefix
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (rs xs : List ℕ) (c s i : ℕ)
    (hK : 1 ≤ rs.length) (hks : m + 1 ≤ c + rs.length + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ =
      rzKey xs (List.replicate rs.length 0) [] c
        (rs.sum + xs.sum + s)) :
    mixedTop (xOp ρ) (zOp ρ) c s (xs ++ List.replicate c 0)
      (rs.map (transportCurrent (yOp ρ))).prod w ∈
        keyPrefix ρ w m i := by
  rw [keyPrefix_eq_higher ρ w m h i hi, hkey]
  exact yz_full_contractions_higher ρ w m h rs xs c s hK hks

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.y_mixed_lower_term
#print axioms VOA.DeligneAudit.D4Levi.y_mixed_lower_mem
#print axioms VOA.DeligneAudit.D4Levi.yz_full_contractions_higher
#print axioms VOA.DeligneAudit.D4Levi.yz_full_contractions_prefix
