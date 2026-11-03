import VOA.DeligneAudit.DeligneFusionCVRectIntegrationIdeal

/-!
# Functoriality of the actual mixed coefficient ideal

Coefficient ideals commute with coefficient-ring homomorphisms. This
identifies actual ideals under the canonical variable split and under
highest-mode variable elimination, rather than assuming presentation
compatibility for those maps.
-/

namespace VOA.DeligneAudit.A2.CVRectIdealMap

open VOA.DeligneAudit.A2.CVRectIntegrationIdeal

variable {R Q : Type*} [CommRing R] [CommRing Q]

theorem coefficientIdeal_map (φ : R →+* Q) (S T : PowerSeries R) (μ : ℕ → ℕ → ℕ) :
    Ideal.map φ (coefficientIdeal S T μ) =
      coefficientIdeal (PowerSeries.map φ S) (PowerSeries.map φ T) μ := by
  unfold coefficientIdeal
  rw [Ideal.map_span]
  congr 1
  ext P
  constructor
  · rintro ⟨Q, ⟨a, b, j, hj, rfl⟩, rfl⟩
    refine ⟨a, b, j, hj, ?_⟩
    rw [← map_pow, ← map_pow, ← map_mul, PowerSeries.coeff_map]
  · rintro ⟨a, b, j, hj, rfl⟩
    refine ⟨PowerSeries.coeff j (S ^ a * T ^ b), ⟨a, b, j, hj, rfl⟩, ?_⟩
    rw [← map_pow, ← map_pow, ← map_mul, PowerSeries.coeff_map]

end VOA.DeligneAudit.A2.CVRectIdealMap

#print axioms VOA.DeligneAudit.A2.CVRectIdealMap.coefficientIdeal_map
