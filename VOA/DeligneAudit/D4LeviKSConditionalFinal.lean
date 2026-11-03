import VOA.DeligneAudit.D4LeviKSOneBoxQuot
import VOA.DeligneAudit.D4LeviKSUnsupported
import VOA.DeligneAudit.D4LeviTerminal

/-! The final D4 rank inequality, isolated from its remaining per-key box bound. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- The key filtration and the multinomial count turn the per-key KS bound
into the rank bound for every saturated cyclic D4 module. -/
theorem d4_rank_of_key_box_bounds
    (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hkey : ∀ i : Fin (globalKeyBox m).card,
      Module.finrank ℂ
        (keyLayer ρ w (keyEnum m i) ⧸
          (keyPrefix ρ w m i.val).comap
            (keyLayer ρ w (keyEnum m i)).subtype) ≤
        ksBoxCount m (keyEnum m i)) :
    FiniteDimensional ℂ (cycSubG ρ w) ∧
      Module.finrank ℂ (cycSubG ρ w) ≤ 29 ^ m := by
  obtain ⟨hfd, hrank⟩ := d4_all_weight_finite_and_raw_sum ρ w m h
  refine ⟨hfd, hrank.trans ?_⟩
  calc
    (∑ i : Fin (globalKeyBox m).card,
      keyOrbitLength m (keyEnum m i) *
        Module.finrank ℂ
          (keyLayer ρ w (keyEnum m i) ⧸
            (keyPrefix ρ w m i.val).comap
              (keyLayer ρ w (keyEnum m i)).subtype)) ≤
      ∑ i : Fin (globalKeyBox m).card,
        keyOrbitLength m (keyEnum m i) * ksBoxCount m (keyEnum m i) := by
          exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (hkey i)
    _ ≤ 29 ^ m := ksBoxCount_enum_sum m

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.d4_rank_of_key_box_bounds
