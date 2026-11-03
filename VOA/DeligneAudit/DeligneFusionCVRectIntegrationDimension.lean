import VOA.DeligneAudit.DeligneFusionCVRectShift

/-!
# The actual two-piece polynomial quotient dimension step

The shift map and normalized-integration map give the two quotient
pieces. Rank--nullity then proves finiteness and the sum upper bound
from finiteness of the two smaller polynomial quotients. Neither the
dimension recurrence nor a fusion presentation is assumed.
-/

namespace VOA.DeligneAudit.A2.CVRectIntegrationDimension

open VOA.DeligneAudit.A2.CVRectIntegrationIdeal
open VOA.DeligneAudit.A2.CVRectIntegrationSeries
open VOA.DeligneAudit.A2.CVRectIntegrationPrimitive
open VOA.DeligneAudit.A2.CVRectShift

noncomputable section

section Linear

variable {K A R : Type*} [Field K] [AddCommGroup A] [Module K A]
  [AddCommGroup R] [Module K R]

/-- Quotienting by a source relation space and then by a linear image
gives the actual two-piece rank--nullity bound. -/
theorem quotient_two_term (I : Submodule K A) (J : Submodule K R)
    (C : A →ₗ[K] R) (hI : I ≤ J.comap C)
    [FiniteDimensional K (A ⧸ I)] [FiniteDimensional K (R ⧸ (J ⊔ C.range))] :
    FiniteDimensional K (R ⧸ J) ∧
      Module.finrank K (R ⧸ J) ≤
        Module.finrank K (R ⧸ (J ⊔ C.range)) + Module.finrank K (A ⧸ I) := by
  let π : (R ⧸ J) →ₗ[K] (R ⧸ (J ⊔ C.range)) :=
    J.mapQ (J ⊔ C.range) (LinearMap.id : R →ₗ[K] R)
      (by simp)
  let f : (A ⧸ I) →ₗ[K] (R ⧸ J) := I.mapQ J C hI
  have hπ : Function.Surjective π := by
    intro q
    obtain ⟨p, rfl⟩ := (J ⊔ C.range).mkQ_surjective q
    exact ⟨J.mkQ p, rfl⟩
  have hf : f.range = π.ker := by
    dsimp only [f, π]
    rw [Submodule.range_mapQ, Submodule.ker_mapQ, Submodule.comap_id,
      Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]
  exact VOA.DeligneAudit.CVRectSeparation.finite_dimensional_two_term π f hπ hf

end Linear

section Polynomial

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- The actual generalized-site two-color dimension step, with the two
smaller quotient modules as the only finiteness inputs. -/
theorem polynomial_dimension_step (f g : PowerSeries A)
    (ks inactive : List ℕ) (K : ℕ) (hK : 1 ≤ K) (hmax : ∀ k ∈ ks, k ≤ K)
    [FiniteDimensional ℂ (A ⧸
      (coefficientIdeal f g (shiftedOrder ks inactive K)).restrictScalars ℂ)]
    [FiniteDimensional ℂ (Polynomial A ⧸
      (coefficientIdeal (chosenCurrent ks.length f) (constantCurrent g)
        (mixedOrder ks inactive (K - 1))).restrictScalars ℂ)] :
    FiniteDimensional ℂ (Polynomial A ⧸
      (coefficientIdeal (chosenCurrent ks.length f) (constantCurrent g)
        (mixedOrder ks inactive K)).restrictScalars ℂ) ∧
      Module.finrank ℂ (Polynomial A ⧸
        (coefficientIdeal (chosenCurrent ks.length f) (constantCurrent g)
          (mixedOrder ks inactive K)).restrictScalars ℂ) ≤
        Module.finrank ℂ (Polynomial A ⧸
          (coefficientIdeal (chosenCurrent ks.length f) (constantCurrent g)
            (mixedOrder ks inactive (K - 1))).restrictScalars ℂ) +
        Module.finrank ℂ (A ⧸
          (coefficientIdeal f g (shiftedOrder ks inactive K)).restrictScalars ℂ) := by
  let S := chosenCurrent ks.length f
  let T := constantCurrent g
  let I := (coefficientIdeal f g (shiftedOrder ks inactive K)).restrictScalars ℂ
  let J := (coefficientIdeal S T (mixedOrder ks inactive K)).restrictScalars ℂ
  let C := (Polynomial.CAlgHom : A →ₐ[ℂ] Polynomial A).toLinearMap
  have hI : I ≤ J.comap C := by
    intro P hP
    exact (Ideal.map_le_iff_le_comap.mp (shift_ideal_map f g ks inactive K)) hP
  have hb := primitiveQuotient_bound S T ks inactive K hK hmax
    (derivative_chosenCurrent _ _) (derivative_constantCurrent _)
  haveI : FiniteDimensional ℂ (Polynomial A ⧸ (J ⊔ C.range)) := hb.1
  have hq := quotient_two_term I J C hI
  refine ⟨hq.1, hq.2.trans ?_⟩
  exact Nat.add_le_add_right hb.2 _

end Polynomial

end

end VOA.DeligneAudit.A2.CVRectIntegrationDimension

#print axioms VOA.DeligneAudit.A2.CVRectIntegrationDimension.quotient_two_term
#print axioms VOA.DeligneAudit.A2.CVRectIntegrationDimension.polynomial_dimension_step
