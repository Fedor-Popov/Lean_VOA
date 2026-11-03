import VOA.DeligneAudit.D4LeviKSRzAbsorb

/-! Every lower Rz Wick term lies in a strictly higher radical key orbit. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

def rzKey (xs ys zs : List ℕ) (k d : ℕ) : RadicalKey :=
  ⟨0, xs.length, 0, 0, ys.length, zs.length + k, d⟩

theorem rz_lower_base (xs ys zs : List ℕ) (k : ℕ)
    (p : List ℕ × List ℕ)
    (hp : p ∈ choices (ys ++ List.replicate k 0))
    (hshort : p.2.length < k) (q : ℕ × ℕ) (d : ℕ) :
    ((PowerSeries.coeff q.1 (fCurrent (fOp ρ) ^ (k - p.2.length)) *
        aWord (yOp ρ) p.1) *
        PowerSeries.coeff q.2 (bWord (zOp ρ) p.2)) •
      (((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) • w) ∈
        higherOrbit ρ w m (rzKey xs ys zs k d) := by
  let N := higherOrbit ρ w m (rzKey xs ys zs k d)
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
    apply xyzCountSpan_le_higher ρ w m xs.length p.1.length
      (zs.length + p.2.length) (rzKey xs ys zs k d) hheight
    simpa [aWord, mul_smul] using ha
  have hf := fOp_coeff_preserves_higher ρ w m
    (rzKey xs ys zs k d) (k - p.2.length) q.1 hbase
  simpa [N, mul_assoc, mul_smul] using hf

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rz_lower_base
