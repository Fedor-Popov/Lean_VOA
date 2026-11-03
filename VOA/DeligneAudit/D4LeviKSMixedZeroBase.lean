import VOA.DeligneAudit.D4LeviKSRzGeneralFamily

/-! A common all-zero mixed-contraction formula for Rx and Ry. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.LeviConversion
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem mixedTop_zero_base (a z : ℕ → Module.End ℂ V)
    (ha : ∀ r t, a r * a t = a t * a r)
    (n c s : ℕ) (B : PowerSeries (Module.End ℂ V)) :
    mixedTop a z c s (List.replicate n 0 ++ List.replicate c 0) B =
      (Nat.choose (n + c) c : Module.End ℂ V) *
        ((a 0) ^ n *
          PowerSeries.coeff s (fCurrent z ^ c * B)) := by
  classical
  unfold mixedTop
  simp_rw [rz_zero_topSum a z ha n c]
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  have hsum :
      (∑ q ∈ Finset.antidiagonal s,
        (aWord a (List.replicate n 0) *
          PowerSeries.coeff q.1 (fCurrent z ^ c)) *
          PowerSeries.coeff q.2 B) =
        aWord a (List.replicate n 0) *
          PowerSeries.coeff s (fCurrent z ^ c * B) := by
    rw [PowerSeries.coeff_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    simp only [mul_assoc]
  simp only [mul_assoc] at hsum
  rw [hsum]
  simp [aWord]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.mixedTop_zero_base
