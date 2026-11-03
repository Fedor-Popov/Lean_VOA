import VOA.DeligneAudit.D4LeviKSMixedZeroBase
import VOA.DeligneAudit.D4LeviKSMixedXLower
import VOA.DeligneAudit.D4LeviKSMixedYLower

/-! All-zero maximal-active mixed Garland relations at supported keys. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.LeviConversion
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem xOp_comm (ρ : CurrentModule D4sector.f V) (r t : ℕ) :
    xOp ρ r * xOp ρ t = xOp ρ t * xOp ρ r := by
  ext v
  simpa [xOp] using radical_ops_comm ρ 1 1 r t v

private theorem yOp_comm (ρ : CurrentModule D4sector.f V) (r t : ℕ) :
    yOp ρ r * yOp ρ t = yOp ρ t * yOp ρ r := by
  ext v
  simpa [yOp] using radical_ops_comm ρ 4 4 r t v

theorem rx_zero_current_prefix
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c s : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hK : 1 ≤ a + b) (hks : m + 1 ≤ c + a + b + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c s) :
    ((yOp ρ 0) ^ b * PowerSeries.coeff s
      (fCurrent (zOp ρ) ^ c *
        (List.replicate (a + b) (transportCurrent (xOp ρ) 0)).prod)) w ∈
      keyPrefix ρ w m i := by
  have hr := xz_full_contractions_prefix ρ w m h
    (List.replicate (a + b) 0) (List.replicate b 0) c s i
    (by simpa using hK) (by simpa [Nat.add_assoc] using hks) hi (by
      simpa [rzKey, pairFinalKey] using hkey)
  rw [mixedTop_zero_base (yOp ρ) (zOp ρ) (yOp_comm ρ) b c s] at hr
  simp only [aWord, List.map_replicate, List.prod_replicate,
    List.sum_replicate, zero_mul, zero_add] at hr
  have hc : (Nat.choose (b + c) c : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos (by omega)))
  have hsmul : (Nat.choose (b + c) c : ℂ) •
      (((yOp ρ 0) ^ b * PowerSeries.coeff s
        (fCurrent (zOp ρ) ^ c *
          (List.replicate (a + b) (transportCurrent (xOp ρ) 0)).prod)) w) ∈
      keyPrefix ρ w m i := by
    simpa [List.prod_replicate, Module.End.mul_apply, Algebra.smul_def,
      Nat.cast_smul_eq_nsmul] using hr
  exact (Submodule.smul_mem_iff (keyPrefix ρ w m i) hc).mp hsmul

theorem ry_zero_current_prefix
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c s : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hK : 1 ≤ b) (hks : m + 1 ≤ c + b + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c s) :
    ((xOp ρ 0) ^ (a + b) * PowerSeries.coeff s
      (fCurrent (zOp ρ) ^ c *
        (List.replicate b (transportCurrent (yOp ρ) 0)).prod)) w ∈
      keyPrefix ρ w m i := by
  have hr := yz_full_contractions_prefix ρ w m h
    (List.replicate b 0) (List.replicate (a + b) 0) c s i
    (by simpa using hK) (by simpa using hks) hi (by
      simpa [rzKey, pairFinalKey] using hkey)
  rw [mixedTop_zero_base (xOp ρ) (zOp ρ) (xOp_comm ρ) (a + b) c s] at hr
  simp only [aWord, List.map_replicate, List.prod_replicate,
    List.sum_replicate, zero_mul, zero_add] at hr
  have hc : (Nat.choose (a + b + c) c : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos (by omega)))
  have hsmul : (Nat.choose (a + b + c) c : ℂ) •
      (((xOp ρ 0) ^ (a + b) * PowerSeries.coeff s
        (fCurrent (zOp ρ) ^ c *
          (List.replicate b (transportCurrent (yOp ρ) 0)).prod)) w) ∈
      keyPrefix ρ w m i := by
    simpa [List.prod_replicate, Module.End.mul_apply, Algebra.smul_def,
      Nat.cast_smul_eq_nsmul] using hr
  exact (Submodule.smul_mem_iff (keyPrefix ρ w m i) hc).mp hsmul

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rx_zero_current_prefix
#print axioms VOA.DeligneAudit.D4Levi.ry_zero_current_prefix
