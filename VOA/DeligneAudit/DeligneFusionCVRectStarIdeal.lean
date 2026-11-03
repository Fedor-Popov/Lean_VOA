import VOA.DeligneAudit.DeligneFusionCVRectIntegrationIdeal

/-!
# The three-color star coefficient ideal

The capacities in `left` act on `(x,y)`, those in `right` act on
`(y,z)`, and those in `center` act only on `y`. These are definitions
of an actual commutative polynomial quotient. No mixed CV presentation
or ordinary current action is assumed.
-/

namespace VOA.DeligneAudit.A2.CVRectStarIdeal

open VOA.DeligneAudit.A2.CVRectIntegrationOrder

noncomputable section

/-- The exact excess order of the three-color star configuration. -/
def starOrder (left right center : List ℕ) (p q r : ℕ) : ℕ :=
  excess left (p + q) + excess right (q + r) + excess center q

/-- The ideal includes every polynomial consequence of its mixed
three-current coefficient generators. -/
def coefficientIdeal3 {R : Type*} [CommRing R]
    (X Y Z : PowerSeries R) (μ : ℕ → ℕ → ℕ → ℕ) : Ideal R :=
  Ideal.span {P | ∃ p q r j, j < μ p q r ∧
    P = PowerSeries.coeff j (X ^ p * Y ^ q * Z ^ r)}

theorem active_site_order (left right center : List ℕ) (K p q r : ℕ) :
    starOrder (K :: left) right center p q r =
      siteOrder left (excess right (q + r) + excess center q) K q p := by
  simp only [starOrder, siteOrder, excess, List.map_cons, List.sum_cons]
  omega

theorem coefficientIdeal3_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (X Y Z : PowerSeries R) (μ : ℕ → ℕ → ℕ → ℕ) :
    Ideal.map φ (coefficientIdeal3 X Y Z μ) =
      coefficientIdeal3 (PowerSeries.map φ X) (PowerSeries.map φ Y)
        (PowerSeries.map φ Z) μ := by
  unfold coefficientIdeal3
  rw [Ideal.map_span]
  congr 1
  ext P
  constructor
  · rintro ⟨Q, ⟨p, q, r, j, hj, rfl⟩, rfl⟩
    refine ⟨p, q, r, j, hj, ?_⟩
    rw [← map_pow, ← map_pow, ← map_pow, ← map_mul, ← map_mul, PowerSeries.coeff_map]
  · rintro ⟨p, q, r, j, hj, rfl⟩
    refine ⟨PowerSeries.coeff j (X ^ p * Y ^ q * Z ^ r), ⟨p, q, r, j, hj, rfl⟩, ?_⟩
    rw [← map_pow, ← map_pow, ← map_pow, ← map_mul, ← map_mul, PowerSeries.coeff_map]

end

end VOA.DeligneAudit.A2.CVRectStarIdeal

#print axioms VOA.DeligneAudit.A2.CVRectStarIdeal.active_site_order
#print axioms VOA.DeligneAudit.A2.CVRectStarIdeal.coefficientIdeal3_map
