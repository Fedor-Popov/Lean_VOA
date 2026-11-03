import VOA.DeligneAudit.D4LeviKSRzGeneralCollapse
import VOA.DeligneAudit.D4LeviKSWordCoeff
import VOA.DeligneAudit.D4LeviKSPairHeight

/-! The general Rz source relation as an explicit finite Z-mode sum. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.LeviConversion
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem rz_zero_coeff_words (ρ : CurrentModule D4sector.f V)
    (k s : ℕ) :
    PowerSeries.coeff s (fCurrent (zOp ρ) ^ k) =
      ((modeAllocations (List.replicate k 0) s).map fun modes =>
        (modes.map (zOp ρ)).prod).sum := by
  have hb : bWord (zOp ρ) (List.replicate k 0) =
      fCurrent (zOp ρ) ^ k := by
    simp [bWord, bTail, fCurrent]
  rw [← hb, ← shiftedWordCoeff_eq_coeff]
  exact shiftedWordCoeff_eq_allocations (zOp ρ) (List.replicate k 0) s

theorem rzKey_zero_pairFinalKey (a b c d k : ℕ)
    (xs zs : List ℕ) (hx : xs.length = a + b)
    (hz : zs.length + k = c) :
    rzKey xs (List.replicate b 0) zs k d = pairFinalKey a b c d := by
  simp [rzKey, pairFinalKey, hx, hz]

/-- The Rz generator at every supported key, with its complete
    homogeneous Z factor displayed as a finite sum of words. -/
theorem rz_zero_pair_words_prefix
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c k s : ℕ) (xs zs : List ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hk : 1 ≤ k) (hks : m + 1 ≤ k + s)
    (hx : xs.length = a + b) (hz : zs.length + k = c)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ =
      pairFinalKey a b c (xs.sum + zs.sum + s)) :
    ((yOp ρ 0) ^ b *
      ((modeAllocations (List.replicate k 0) s).map fun modes =>
        (modes.map (zOp ρ)).prod).sum) •
        (((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) • w) ∈
      keyPrefix ρ w m i := by
  rw [← rz_zero_coeff_words ρ k s]
  apply rz_zero_dressed_prefix ρ w m i b k s h xs zs hk hks hi
  rw [rzKey_zero_pairFinalKey a b c _ k xs zs hx hz]
  exact hkey

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rz_zero_coeff_words
#print axioms VOA.DeligneAudit.D4Levi.rzKey_zero_pairFinalKey
#print axioms VOA.DeligneAudit.D4Levi.rz_zero_pair_words_prefix
