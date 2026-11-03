import VOA.DeligneAudit.D4LeviKSRyWick

/-! Lower highest-Levi-root Wick terms are strictly higher in the D4 key order. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

theorem fTop_coeff_preserves_higher (key : RadicalKey) (n s : ℕ)
    {v : V} (hv : v ∈ higherOrbit ρ w m key) :
    PowerSeries.coeff s (fCurrent (fTopOp ρ) ^ n) v ∈
      higherOrbit ρ w m key := by
  induction n generalizing s v with
  | zero =>
      by_cases hs : s = 0
      · subst s
        simpa [fCurrent] using hv
      · simp [hs]
  | succ n ih =>
      rw [pow_succ, PowerSeries.coeff_mul]
      change (∑ q ∈ Finset.antidiagonal s,
        PowerSeries.coeff q.1 (fCurrent (fTopOp ρ) ^ n) *
          PowerSeries.coeff q.2 (fCurrent (fTopOp ρ))) • v ∈ _
      rw [Finset.sum_smul]
      apply (higherOrbit ρ w m key).sum_mem
      intro q hq
      have hf : fTopOp ρ q.2 v ∈ higherOrbit ρ w m key := by
        have hh := higherOrbit_full_levi_inv ρ w m key (23 : Fin 28)
          ⟨9, rfl⟩ q.2 hv
        simpa [fTopOp] using (higherOrbit ρ w m key).neg_mem hh
      simpa [fCurrent, fTopOp, mul_smul] using ih q.1 hf

theorem ry_lower_base (xs ys zs : List ℕ) (k : ℕ)
    (p : List ℕ × List ℕ)
    (hp : p ∈ choices (xs ++ List.replicate k 0))
    (hshort : p.2.length < k) (q : ℕ × ℕ) (d : ℕ) :
    ((PowerSeries.coeff q.1 (fCurrent (fTopOp ρ) ^ (k - p.2.length)) *
        aWord (xOp ρ) p.1) *
        PowerSeries.coeff q.2 (bWord (zOp ρ) p.2)) •
      (((ys.map (yOp ρ)).prod * (zs.map (zOp ρ)).prod) • w) ∈
        higherOrbit ρ w m (rzKey xs ys zs k d) := by
  let N := higherOrbit ρ w m (rzKey xs ys zs k d)
  have hz : (zs.map (zOp ρ)).prod w ∈
      xyzCountSpan ρ w 0 0 zs.length := by
    simpa using xyzCountSpan_z_word ρ w zs 0 0 0
      (xyzCountSpan_zero ρ w)
  have hy : (ys.map (yOp ρ)).prod ((zs.map (zOp ρ)).prod w) ∈
      xyzCountSpan ρ w 0 ys.length zs.length := by
    simpa using xyzCountSpan_y_word ρ w ys 0 0 zs.length hz
  have hb := xyzCountSpan_z_coeff ρ w p.2 q.2 0 ys.length
    zs.length hy
  have ha := xyzCountSpan_x_word ρ w p.1 0 ys.length
    (zs.length + p.2.length) hb
  have hlen := choices_length (xs ++ List.replicate k 0) p hp
  simp only [List.length_append, List.length_replicate] at hlen
  have hheight : keyHeight m (rzKey xs ys zs k d) <
      4 * (m : ℤ) + 2 * p.1.length - 2 * ys.length -
        4 * (zs.length + p.2.length) := by
    dsimp [rzKey, keyHeight]
    omega
  have hbase : (aWord (xOp ρ) p.1 *
      PowerSeries.coeff q.2 (bWord (zOp ρ) p.2)) •
      (((ys.map (yOp ρ)).prod * (zs.map (zOp ρ)).prod) • w) ∈ N := by
    apply xyzCountSpan_le_higher ρ w m p.1.length ys.length
      (zs.length + p.2.length) (rzKey xs ys zs k d) hheight
    simpa [aWord, mul_smul] using ha
  have hf := fTop_coeff_preserves_higher ρ w m
    (rzKey xs ys zs k d) (k - p.2.length) q.1 hbase
  simpa [N, mul_assoc, mul_smul] using hf

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.fTop_coeff_preserves_higher
#print axioms VOA.DeligneAudit.D4Levi.ry_lower_base
