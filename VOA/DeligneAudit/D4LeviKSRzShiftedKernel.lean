import VOA.DeligneAudit.D4LeviKSRzHeight
import VOA.DeligneAudit.D4LeviKSDegreeShiftKernel
import VOA.DeligneAudit.D4LeviKSRzGeneralKernel

/-! General Rz orbit generators remain target relations after degree shifts. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.LeviConversion
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem yOp_comm_height
    (ρ : CurrentModule D4sector.f V) (r t : ℕ) :
    yOp ρ r * yOp ρ t = yOp ρ t * yOp ρ r := by
  ext v
  simpa [yOp] using radical_ops_comm ρ 4 4 r t v

theorem rz_zero_pair_words_height
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m a b c k s : ℕ) (xs zs : List ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hk : 1 ≤ k) (hks : m + 1 ≤ k + s)
    (hx : xs.length = a + b) (hz : zs.length + k = c) :
    ((yOp ρ 0) ^ b *
      ((modeAllocations (List.replicate k 0) s).map fun modes =>
        (modes.map (zOp ρ)).prod).sum) •
      (((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) • w) ∈
        heightHigherOrbit ρ w m
          (pairFinalKey a b c (xs.sum + zs.sum + s)) := by
  rw [← rz_zero_coeff_words ρ k s]
  have hr := rz_top_height ρ w m h xs (List.replicate b 0) zs k s hk hks
  have hr' : topSum (yOp ρ) (zOp ρ) k s
      (List.replicate b 0 ++ List.replicate k 0) •
        (((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) • w) ∈
      heightHigherOrbit ρ w m
        (pairFinalKey a b c (xs.sum + zs.sum + s)) := by
    simpa [rzKey, pairFinalKey, hx, hz] using hr
  rw [rz_zero_topSum (yOp ρ) (zOp ρ)
    (yOp_comm_height ρ) b k s] at hr'
  have hprod : aWord (yOp ρ) (List.replicate b 0) = (yOp ρ 0) ^ b := by
    simp [aWord]
  rw [hprod] at hr'
  have hc : (Nat.choose (b + k) k : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos (by omega)))
  have hsmul : (Nat.choose (b + k) k : ℂ) •
      (((yOp ρ 0) ^ b * PowerSeries.coeff s (fCurrent (zOp ρ) ^ k)) •
        (((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) • w)) ∈
      heightHigherOrbit ρ w m
        (pairFinalKey a b c (xs.sum + zs.sum + s)) := by
    simpa only [mul_smul, Nat.cast_smul_eq_nsmul] using hr'
  exact (Submodule.smul_mem_iff _ hc).mp hsmul

theorem rzSourceGenerator_height
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m a b k l s : ℕ) (α : Fin b ⊕ Fin a → ℕ)
    (β : Fin l → ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hk : 1 ≤ k) (hks : m + 1 ≤ k + s) :
    xyzEvaluation ρ w (pairSourceShape a b (k + l))
        (rzSourceGenerator a b k l s α β) ∈
      heightHigherOrbit ρ w m
        (pairFinalKey a b (k + l)
          (((Finset.univ.toList : List (Fin b ⊕ Fin a)).map α).sum +
            ((Finset.univ.toList : List (Fin l)).map β).sum + s)) := by
  let xs := (Finset.univ.toList : List (Fin b ⊕ Fin a)).map α
  let zs := (Finset.univ.toList : List (Fin l)).map β
  have hx : xs.length = a + b := by
    simp [xs, Fintype.card_sum, Nat.add_comm]
  have hz : zs.length + k = k + l := by simp [zs, Nat.add_comm]
  have hraw : xyzEvaluation ρ w (pairSourceShape a b (k + l))
      (rzRawSourceGenerator a b k l s α β) ∈
      heightHigherOrbit ρ w m
        (pairFinalKey a b (k + l) (xs.sum + zs.sum + s)) := by
    rw [rzRawSourceGenerator_word_bridge]
    simpa only [xs, zs, List.map_map, Function.comp_def] using
      rz_zero_pair_words_height ρ w m a b (k + l) k s xs zs
        h hk hks hx hz
  rw [rzSourceGenerator_evaluation]
  simpa only [xs, zs] using
    (heightHigherOrbit ρ w m
      (pairFinalKey a b (k + l) (xs.sum + zs.sum + s))).nsmul_mem
      hraw _

theorem rzTargetGenerator_mul_shifted_mem_ker
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b k l s r : ℕ) (α : Fin b ⊕ Fin a → ℕ)
    (β : Fin l → ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hk : 1 ≤ k) (hks : m + 1 ≤ k + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ =
      pairFinalKey a b (k + l)
        (((Finset.univ.toList : List (Fin b ⊕ Fin a)).map α).sum +
          ((Finset.univ.toList : List (Fin l)).map β).sum + s + r))
    (U : pairTargetSymmetric a b (k + l)) :
    U * rzTargetGenerator a b k l s α β ∈
      (pairTargetQuotientEvaluation ρ w m i a b (k + l)
        (pairKernelPrefix_of_sat ρ w m i a b (k + l)
          (((Finset.univ.toList : List (Fin b ⊕ Fin a)).map α).sum +
            ((Finset.univ.toList : List (Fin l)).map β).sum + s + r)
          h hi hkey)).ker := by
  exact pairTarget_mul_height_mem_shifted_ker ρ w m i a b (k + l)
    (((Finset.univ.toList : List (Fin b ⊕ Fin a)).map α).sum +
      ((Finset.univ.toList : List (Fin l)).map β).sum + s) r
    h hi hkey (rzTargetGenerator a b k l s α β) U
    ⟨rzSourceGenerator a b k l s α β,
      rzSourceGenerator_mem a b k l s α β⟩ rfl
    (rzSourceGenerator_height ρ w m a b k l s α β h hk hks)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rz_zero_pair_words_height
#print axioms VOA.DeligneAudit.D4Levi.rzSourceGenerator_height
#print axioms VOA.DeligneAudit.D4Levi.rzTargetGenerator_mul_shifted_mem_ker
