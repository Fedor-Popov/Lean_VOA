import VOA.DeligneAudit.D4LeviKSXzHeight
import VOA.DeligneAudit.D4LeviKSYzHeight
import VOA.DeligneAudit.D4LeviKSMixedMaximalKernel

/-! Maximal mixed symmetric generators have strict-height source errors. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.LeviConversion
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem xOp_comm_height
    (ρ : CurrentModule D4sector.f V) (r t : ℕ) :
    xOp ρ r * xOp ρ t = xOp ρ t * xOp ρ r := by
  ext v
  simpa [xOp] using radical_ops_comm ρ 1 1 r t v

private theorem yOp_comm_height
    (ρ : CurrentModule D4sector.f V) (r t : ℕ) :
    yOp ρ r * yOp ρ t = yOp ρ t * yOp ρ r := by
  ext v
  simpa [yOp] using radical_ops_comm ρ 4 4 r t v

private theorem rx_zero_current_height
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m a b c s : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hK : 1 ≤ a + b) (hks : m + 1 ≤ c + a + b + s) :
    ((yOp ρ 0) ^ b * PowerSeries.coeff s
      (fCurrent (zOp ρ) ^ c *
        (List.replicate (a + b) (transportCurrent (xOp ρ) 0)).prod)) w ∈
      heightHigherOrbit ρ w m (pairFinalKey a b c s) := by
  have hr := xz_full_contractions_height ρ w m h
    (List.replicate (a + b) 0) (List.replicate b 0) c s
    (by simpa using hK) (by simpa [Nat.add_assoc] using hks)
  have hr' : mixedTop (yOp ρ) (zOp ρ) c s
      (List.replicate b 0 ++ List.replicate c 0)
      ((List.replicate (a + b) 0).map
        (transportCurrent (xOp ρ))).prod w ∈
      heightHigherOrbit ρ w m (pairFinalKey a b c s) := by
    simpa [rzKey, pairFinalKey] using hr
  rw [mixedTop_zero_base (yOp ρ) (zOp ρ)
    (yOp_comm_height ρ) b c s] at hr'
  simp only [aWord, List.map_replicate, List.prod_replicate,
    List.sum_replicate, zero_mul, zero_add] at hr'
  have hc : (Nat.choose (b + c) c : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos (by omega)))
  have hsmul : (Nat.choose (b + c) c : ℂ) •
      (((yOp ρ 0) ^ b * PowerSeries.coeff s
        (fCurrent (zOp ρ) ^ c *
          (List.replicate (a + b) (transportCurrent (xOp ρ) 0)).prod)) w) ∈
      heightHigherOrbit ρ w m (pairFinalKey a b c s) := by
    simpa [List.prod_replicate, Module.End.mul_apply, Algebra.smul_def,
      Nat.cast_smul_eq_nsmul] using hr'
  exact (Submodule.smul_mem_iff _ hc).mp hsmul

private theorem ry_zero_current_height
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m a b c s : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hK : 1 ≤ b) (hks : m + 1 ≤ c + b + s) :
    ((xOp ρ 0) ^ (a + b) * PowerSeries.coeff s
      (fCurrent (zOp ρ) ^ c *
        (List.replicate b (transportCurrent (yOp ρ) 0)).prod)) w ∈
      heightHigherOrbit ρ w m (pairFinalKey a b c s) := by
  have hr := yz_full_contractions_height ρ w m h
    (List.replicate b 0) (List.replicate (a + b) 0) c s
    (by simpa using hK) (by simpa using hks)
  have hr' : mixedTop (xOp ρ) (zOp ρ) c s
      (List.replicate (a + b) 0 ++ List.replicate c 0)
      ((List.replicate b 0).map
        (transportCurrent (yOp ρ))).prod w ∈
      heightHigherOrbit ρ w m (pairFinalKey a b c s) := by
    simpa [rzKey, pairFinalKey] using hr
  rw [mixedTop_zero_base (xOp ρ) (zOp ρ)
    (xOp_comm_height ρ) (a + b) c s] at hr'
  simp only [aWord, List.map_replicate, List.prod_replicate,
    List.sum_replicate, zero_mul, zero_add] at hr'
  have hc : (Nat.choose (a + b + c) c : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos (by omega)))
  have hsmul : (Nat.choose (a + b + c) c : ℂ) •
      (((xOp ρ 0) ^ (a + b) * PowerSeries.coeff s
        (fCurrent (zOp ρ) ^ c *
          (List.replicate b (transportCurrent (yOp ρ) 0)).prod)) w) ∈
      heightHigherOrbit ρ w m (pairFinalKey a b c s) := by
    simpa [List.prod_replicate, Module.End.mul_apply, Algebra.smul_def,
      Nat.cast_smul_eq_nsmul] using hr'
  exact (Submodule.smul_mem_iff _ hc).mp hsmul

theorem rxMixedSeed_height
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m a b c s : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hK : 1 ≤ a + b) (hks : m + 1 ≤ c + a + b + s) :
    xyzEvaluation ρ w (pairSourceShape a b c) (rxMixedSeed a b c s) ∈
      heightHigherOrbit ρ w m (pairFinalKey a b c s) := by
  rw [rxMixedSeed_evaluation_list]
  have he := xyz_hsymm_evaluation_colourList ρ w
    (List.replicate c (5 : Fin 6) ++
      List.replicate (a + b) (1 : Fin 6)) s
  simp only [List.length_append, List.length_replicate,
    List.map_append, List.map_replicate, List.prod_append,
    List.prod_replicate] at he
  simp [xOp, zOp, radicalColour] at he
  rw [he]
  simpa [transportCurrent, fCurrent] using
    rx_zero_current_height ρ w m a b c s h hK hks

theorem ryMixedSeed_height
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m a b c s : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hK : 1 ≤ b) (hks : m + 1 ≤ c + b + s) :
    xyzEvaluation ρ w (pairSourceShape a b c) (ryMixedSeed a b c s) ∈
      heightHigherOrbit ρ w m (pairFinalKey a b c s) := by
  rw [ryMixedSeed_evaluation_list]
  have he := xyz_hsymm_evaluation_colourList ρ w
    (List.replicate c (5 : Fin 6) ++ List.replicate b (4 : Fin 6)) s
  simp only [List.length_append, List.length_replicate,
    List.map_append, List.map_replicate, List.prod_append,
    List.prod_replicate] at he
  simp [yOp, zOp, radicalColour] at he
  rw [he]
  simpa [transportCurrent, fCurrent] using
    ry_zero_current_height ρ w m a b c s h hK hks

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rxMixedSeed_height
#print axioms VOA.DeligneAudit.D4Levi.ryMixedSeed_height
