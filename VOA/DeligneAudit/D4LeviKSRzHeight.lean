import VOA.DeligneAudit.D4LeviKSDegreeShiftHeight

/-! The graded Rz relation has a strict Levi-height error. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

private theorem rz_lower_base_height
    (xs ys zs : List ℕ) (k : ℕ)
    (p : List ℕ × List ℕ)
    (hp : p ∈ choices (ys ++ List.replicate k 0))
    (hshort : p.2.length < k) (q : ℕ × ℕ) (d : ℕ) :
    ((PowerSeries.coeff q.1 (fCurrent (fOp ρ) ^ (k - p.2.length)) *
        aWord (yOp ρ) p.1) *
        PowerSeries.coeff q.2 (bWord (zOp ρ) p.2)) •
      (((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) • w) ∈
        heightHigherOrbit ρ w m (rzKey xs ys zs k d) := by
  let N := heightHigherOrbit ρ w m (rzKey xs ys zs k d)
  have hz : (zs.map (zOp ρ)).prod w ∈
      xyzCountSpan ρ w 0 0 zs.length := by
    simpa using xyzCountSpan_z_word ρ w zs 0 0 0
      (xyzCountSpan_zero ρ w)
  have hx : (xs.map (xOp ρ)).prod ((zs.map (zOp ρ)).prod w) ∈
      xyzCountSpan ρ w xs.length 0 zs.length := by
    simpa using xyzCountSpan_x_word ρ w xs 0 0 zs.length hz
  have hb := xyzCountSpan_z_coeff ρ w p.2 q.2 xs.length 0
    zs.length hx
  have ha := xyzCountSpan_y_word ρ w p.1 xs.length 0
    (zs.length + p.2.length) hb
  have hlen := choices_length (ys ++ List.replicate k 0) p hp
  simp only [List.length_append, List.length_replicate] at hlen
  have hheight : keyHeight m (rzKey xs ys zs k d) <
      4 * (m : ℤ) + 2 * xs.length - 2 * p.1.length -
        4 * (zs.length + p.2.length) := by
    dsimp [rzKey, keyHeight]
    omega
  have hbase : (aWord (yOp ρ) p.1 *
      PowerSeries.coeff q.2 (bWord (zOp ρ) p.2)) •
      (((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) • w) ∈ N := by
    apply xyzCountSpan_le_heightHigher ρ w m xs.length p.1.length
      (zs.length + p.2.length) (rzKey xs ys zs k d) hheight
    simpa [aWord, mul_smul] using ha
  have hf := fOp_coeff_preserves_heightHigher ρ w m
    (rzKey xs ys zs k d) (k - p.2.length) q.1 hbase
  simpa [N, mul_assoc, mul_smul] using hf

private theorem rz_lower_term_height
    (xs ys zs : List ℕ) (k s d : ℕ)
    (p : List ℕ × List ℕ)
    (hp : p ∈ choices (ys ++ List.replicate k 0))
    (hshort : p.2.length < k) :
    conversionTerm (fOp ρ) (yOp ρ) (zOp ρ) k s p •
      (((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) • w) ∈
        heightHigherOrbit ρ w m (rzKey xs ys zs k d) := by
  let N := heightHigherOrbit ρ w m (rzKey xs ys zs k d)
  have hsum :
      (∑ q ∈ Finset.antidiagonal s,
        (PowerSeries.coeff q.1 (fCurrent (fOp ρ) ^ (k - p.2.length)) *
          aWord (yOp ρ) p.1) *
          PowerSeries.coeff q.2 (bWord (zOp ρ) p.2)) •
        (((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) • w) ∈ N := by
    rw [Finset.sum_smul]
    exact N.sum_mem (fun q _ =>
      rz_lower_base_height ρ w m xs ys zs k p hp hshort q d)
  have hscalar (t : ℂ) :
      (algebraMap ℂ (Module.End ℂ V) t) •
        ((∑ q ∈ Finset.antidiagonal s,
          (PowerSeries.coeff q.1
            (fCurrent (fOp ρ) ^ (k - p.2.length)) *
              aWord (yOp ρ) p.1) *
            PowerSeries.coeff q.2 (bWord (zOp ρ) p.2)) •
          (((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) • w)) ∈ N := by
    simpa using N.smul_mem t hsum
  have hcast : ((-1 : Module.End ℂ V) ^ p.2.length *
      (k.descFactorial p.2.length : Module.End ℂ V)) =
      algebraMap ℂ (Module.End ℂ V)
        ((-1 : ℂ) ^ p.2.length * (k.descFactorial p.2.length : ℂ)) := by
    simp
  unfold conversionTerm
  rw [hcast]
  simpa only [mul_smul] using
    hscalar ((-1 : ℂ) ^ p.2.length * (k.descFactorial p.2.length : ℂ))

private theorem rz_lower_sum_height
    (xs ys zs : List ℕ) (k s d : ℕ) :
    lowerSum (fOp ρ) (yOp ρ) (zOp ρ) k s
        (ys ++ List.replicate k 0) •
      (((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) • w) ∈
        heightHigherOrbit ρ w m (rzKey xs ys zs k d) := by
  apply lowerSum_mem_of_higher_terms (fOp ρ) (yOp ρ) (zOp ρ)
    k s (ys ++ List.replicate k 0)
    ((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) w
    (heightHigherOrbit ρ w m (rzKey xs ys zs k d))
  intro p hp hshort
  exact rz_lower_term_height ρ w m xs ys zs k s d p hp hshort

/-- The Rz top contraction vanishes modulo strictly greater Levi height,
    a condition stable when positive Cartan modes raise its degree. -/
theorem rz_top_height
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (xs ys zs : List ℕ) (k s : ℕ)
    (hk : 1 ≤ k) (hks : m + 1 ≤ k + s) :
    topSum (yOp ρ) (zOp ρ) k s (ys ++ List.replicate k 0) •
      (((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) • w) ∈
        heightHigherOrbit ρ w m
          (rzKey xs ys zs k (xs.sum + ys.sum + zs.sum + s)) := by
  have hfa : ∀ i j, fOp ρ i * yOp ρ j - yOp ρ j * fOp ρ i =
      zOp ρ (i + j) := by
    intro i j
    exact fTwo_y_comm ρ i j
  have hfb : ∀ i j, fOp ρ i * zOp ρ j = zOp ρ j * fOp ρ i := by
    intro i j
    exact fTwo_z_comm ρ i j
  have hab : ∀ i j, yOp ρ i * zOp ρ j = zOp ρ j * yOp ρ i := by
    intro i j
    ext v
    simpa [yOp, zOp] using radical_ops_comm ρ 4 5 i j v
  have hkill : PowerSeries.coeff s (fCurrent (fOp ρ) ^ k) w = 0 :=
    fTwo_garland_zero ρ w m h k s hk hks
  exact topSum_mem_higher_linear (fOp ρ) (yOp ρ) (zOp ρ)
    hfa hfb hab k s (ys ++ List.replicate k 0)
    ((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) w
    (rz_xz_spectator_comm ρ xs zs) hkill
    (by intro t v; simp) _
    (rz_lower_sum_height ρ w m xs ys zs k s
      (xs.sum + ys.sum + zs.sum + s))

/-- Rz remains a relation in the prefix at its shifted degree, rather than
    merely in the prefix at the original degree. -/
theorem rz_top_shifted_prefix
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (xs ys zs : List ℕ) (k s i : ℕ)
    (ps : List (Fin 3 × ℕ))
    (hk : 1 ≤ k) (hks : m + 1 ≤ k + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ =
      keyShift (ps.map Prod.snd).sum
        (rzKey xs ys zs k (xs.sum + ys.sum + zs.sum + s))) :
    selectiveCartanWord ρ ps
      (topSum (yOp ρ) (zOp ρ) k s (ys ++ List.replicate k 0) •
        (((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) • w)) ∈
      keyPrefix ρ w m i := by
  exact heightHigherOrbit_shifted_prefix ρ w m h _ _ i hi hkey ps
    (rz_top_height ρ w m h xs ys zs k s hk hks)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rz_top_height
#print axioms VOA.DeligneAudit.D4Levi.rz_top_shifted_prefix
