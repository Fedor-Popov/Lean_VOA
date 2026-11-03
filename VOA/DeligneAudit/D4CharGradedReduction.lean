import VOA.DeligneAudit.D4CharHilbertIdentity
import VOA.DeligneAudit.D4LeviKSDemazureRank

/-! First L1 reduction: finite graded pieces and sufficiency of the universal module. -/

namespace VOA.DeligneAudit.D4Char

open SectorWeyl UnivG DeligneSector.D4

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem d4_cycDeg_le_cyclic (ρ : CurrentModule D4sector.f V) (w : V) (N : ℕ) :
    cycDeg ρ w N ≤ cycSubG ρ w := by
  apply Submodule.span_le.mpr
  rintro v ⟨l, _, rfl⟩
  exact wordOp_mem_cycSubG ρ w l

/-- The finished total-rank proof supplies finiteness in every exact current degree. -/
theorem d4_cycDeg_finite (n : ℕ) (ρ : CurrentModule D4sector.f V) (w : V)
    (h : Sat D4sector.f ρ w (ravFam D4sector n 0)) (N : ℕ) :
    FiniteDimensional ℂ (cycDeg ρ w N) := by
  haveI := (D4Levi.d4_all_weight_rank ρ w n h).1
  exact FiniteDimensional.of_injective
    (Submodule.inclusion (d4_cycDeg_le_cyclic ρ w N))
    (Submodule.inclusion_injective (d4_cycDeg_le_cyclic ρ w N))

/-- This is only the inherited coarse bound, not the desired sharp graded estimate. -/
theorem d4_cycDeg_le_total (n : ℕ) (ρ : CurrentModule D4sector.f V) (w : V)
    (h : Sat D4sector.f ρ w (ravFam D4sector n 0)) (N : ℕ) :
    Module.finrank ℂ (cycDeg ρ w N) ≤ 29 ^ n := by
  have hh := D4Levi.d4_all_weight_rank ρ w n h
  haveI := hh.1
  exact (Submodule.finrank_mono (d4_cycDeg_le_cyclic ρ w N)).trans hh.2

/-- L1 needs a sharp bound only on the presented universal module, in each degree. -/
def UniversalGradedLeviBound : Prop :=
  ∀ n N : ℕ, Module.finrank ℂ
    (cycDeg (univRepG D4sector.f (ravFam D4sector n 0))
      (wUG D4sector.f (ravFam D4sector n 0)) N) ≤ d4LeviHilb n N

theorem gradedLeviBound_iff_universal : GradedLeviBound ↔ UniversalGradedLeviBound := by
  constructor
  · intro h n N
    exact h n _ (univRepG D4sector.f (ravFam D4sector n 0))
      (wUG D4sector.f (ravFam D4sector n 0))
      (univG_sat D4sector.f (ravFam D4sector n 0)) N
  · intro hu n V _ _ ρ w h N
    haveI := d4_cycDeg_finite n (univRepG D4sector.f (ravFam D4sector n 0))
      (wUG D4sector.f (ravFam D4sector n 0))
      (univG_sat D4sector.f (ravFam D4sector n 0)) N
    exact (finrank_cycDeg_le_univG h N).trans (hu n N)

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.d4_cycDeg_le_cyclic
#print axioms VOA.DeligneAudit.D4Char.d4_cycDeg_finite
#print axioms VOA.DeligneAudit.D4Char.d4_cycDeg_le_total
#print axioms VOA.DeligneAudit.D4Char.gradedLeviBound_iff_universal
