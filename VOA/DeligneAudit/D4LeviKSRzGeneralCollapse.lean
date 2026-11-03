import VOA.DeligneAudit.D4LeviKSRzGraded
import VOA.DeligneAudit.LeviConversionBoxTopZero

/-! Collapse the all-zero positional Rz contraction at arbitrary XYZ shape. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.LeviConversion
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

/-- Every positional choice in an all-zero top contraction has the same term. -/
theorem rz_zero_topSum {A : Type*} [Ring A] (y z : ℕ → A)
    (hy : ∀ r t, y r * y t = y t * y r) (b k s : ℕ) :
    topSum y z k s (List.replicate b 0 ++ List.replicate k 0) =
      (Nat.choose (b + k) k : A) *
        (aWord y (List.replicate b 0) *
          PowerSeries.coeff s (fCurrent z ^ k)) := by
  classical
  let L := List.replicate b 0 ++ List.replicate k 0
  have hterm (T : Finset (Fin L.length))
      (hT : T ∈ (Finset.univ : Finset (Fin L.length)).powersetCard k) :
      (let p := splitAt (List.finRange L.length) T
       aWord y (p.1.map L.get) *
         PowerSeries.coeff s (bWord z (p.2.map L.get))) =
        aWord y (List.replicate b 0) *
          PowerSeries.coeff s (fCurrent z ^ k) := by
    have hz : T ⊆ zeroPositions L.get := by
      intro t ht
      simp [zeroPositions, L]
    have ha := selected_aWord_zero y hy (List.replicate b 0) k T
      (by simpa only [L] using hT) (by simpa only [L] using hz)
    have hb := selected_bWord_zero z L k T hT hz
    have ha' : aWord y ((splitAt (List.finRange L.length) T).1.map L.get) =
        aWord y (List.replicate b 0) := by
      simpa only [L] using ha
    dsimp only
    rw [ha', hb]
  rw [topSum_powersetCard]
  have hsum :
      (∑ T ∈ (Finset.univ : Finset (Fin L.length)).powersetCard k,
        let p := splitAt (List.finRange L.length) T
        aWord y (p.1.map L.get) *
          PowerSeries.coeff s (bWord z (p.2.map L.get))) =
      ∑ _T ∈ (Finset.univ : Finset (Fin L.length)).powersetCard k,
        aWord y (List.replicate b 0) *
          PowerSeries.coeff s (fCurrent z ^ k) := by
    apply Finset.sum_congr rfl
    intro T hT
    exact hterm T hT
  rw [show List.replicate b 0 ++ List.replicate k 0 = L from rfl]
  rw [hsum, Finset.sum_const, Finset.card_powersetCard]
  simp [L]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem yOp_pairwise_comm (ρ : CurrentModule D4sector.f V)
    (r t : ℕ) : yOp ρ r * yOp ρ t = yOp ρ t * yOp ρ r := by
  ext v
  simpa [yOp] using radical_ops_comm ρ 4 4 r t v

/-- The Rz relation for every XYZ shape after all contracted Y modes
    are specialized to zero. The complete Z-current coefficient is the
    homogeneous symmetric sum in the `k` new Z modes. -/
theorem rz_zero_dressed_prefix
    (ρ : CurrentModule D4sector.f V) (w : V) (m i b k s : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (xs zs : List ℕ) (hk : 1 ≤ k) (hks : m + 1 ≤ k + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ =
      rzKey xs (List.replicate b 0) zs k
        (xs.sum + zs.sum + s)) :
    ((yOp ρ 0) ^ b * PowerSeries.coeff s (fCurrent (zOp ρ) ^ k)) •
        (((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) • w) ∈
      keyPrefix ρ w m i := by
  have hr := rz_top_prefix ρ w m h xs (List.replicate b 0) zs k s i
    hk hks hi (by simpa using hkey)
  rw [rz_zero_topSum (yOp ρ) (zOp ρ) (yOp_pairwise_comm ρ) b k s] at hr
  have hprod : aWord (yOp ρ) (List.replicate b 0) = (yOp ρ 0) ^ b := by
    simp [aWord]
  rw [hprod] at hr
  have hn : Nat.choose (b + k) k ≠ 0 := by
    exact Nat.ne_of_gt (Nat.choose_pos (by omega))
  have hc : (Nat.choose (b + k) k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hsmul :
      (Nat.choose (b + k) k : ℂ) •
        (((yOp ρ 0) ^ b * PowerSeries.coeff s (fCurrent (zOp ρ) ^ k)) •
          (((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) • w)) ∈
        keyPrefix ρ w m i := by
    simpa only [mul_smul, Nat.cast_smul_eq_nsmul] using hr
  exact (Submodule.smul_mem_iff (keyPrefix ρ w m i) hc).mp hsmul

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rz_zero_topSum
#print axioms VOA.DeligneAudit.D4Levi.rz_zero_dressed_prefix
