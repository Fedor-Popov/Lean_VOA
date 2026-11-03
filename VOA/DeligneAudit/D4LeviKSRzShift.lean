import VOA.DeligneAudit.D4LeviKSPairOne

/-! Selective Cartan shift closure of the graded Rz relation. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

/-- Every ordered choice of X, Y, and Z power-sum Cartan shifts preserves
    the graded Rz relation at its key prefix. -/
theorem rz_cartan_shifted_prefix
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (xs ys zs : List ℕ) (k s i : ℕ) (ps : List (Fin 3 × ℕ))
    (hk : 1 ≤ k) (hks : m + 1 ≤ k + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ =
      rzKey xs ys zs k (xs.sum + ys.sum + zs.sum + s)) :
    selectiveCartanWord ρ ps
      (topSum (yOp ρ) (zOp ρ) k s (ys ++ List.replicate k 0) •
        (((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) • w)) ∈
      keyPrefix ρ w m i := by
  rw [keyPrefix_eq_higher ρ w m h i hi, hkey]
  exact selectiveCartanWord_higher ρ w m ps _
    (rz_top_higher ρ w m h xs ys zs k s hk hks)

/-- The span of all finite Cartan power-sum shifts of Rz lies in the prefix. -/
theorem rz_cartanShiftSpan_le_prefix
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (xs ys zs : List ℕ) (k s i : ℕ)
    (hk : 1 ≤ k) (hks : m + 1 ≤ k + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ =
      rzKey xs ys zs k (xs.sum + ys.sum + zs.sum + s)) :
    cartanShiftSpan ρ
      (topSum (yOp ρ) (zOp ρ) k s (ys ++ List.replicate k 0) •
        (((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) • w)) ≤
      keyPrefix ρ w m i := by
  rw [keyPrefix_eq_higher ρ w m h i hi, hkey]
  exact cartanShiftSpan_le_higher ρ w m _
    (rz_top_higher ρ w m h xs ys zs k s hk hks)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rz_cartan_shifted_prefix
#print axioms VOA.DeligneAudit.D4Levi.rz_cartanShiftSpan_le_prefix
