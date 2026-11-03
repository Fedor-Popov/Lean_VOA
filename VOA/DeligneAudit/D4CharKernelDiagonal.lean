import VOA.DeligneAudit.D4CharMixedTheta

/-! Euler numerators under the homogeneous diagonal substitution. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open PowerSeries

noncomputable section

variable {R : Type*} [CommRing R]

theorem gtEulerPos_map {S : Type*} [CommRing S] (φ : R →+* S)
    (q : R) (h : PochhammerUnits q) (a : R) :
    (gtEulerPos q h a).map φ =
      gtEulerPos (φ q) (gtPochhammerUnits_map φ q h) (φ a) := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_map, gtEulerPos, coeff_mk, map_mul, map_pow, map_neg, map_one]
  rw [gtInvPoch_map]

theorem gtEulerPos_rescale (q : R) (h : PochhammerUnits q) (a b : R) :
    rescale a (gtEulerPos q h b) = gtEulerPos q h (a * b) := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_rescale, gtEulerPos, coeff_mk, mul_pow]
  ring

/-- A diagonal coefficient of degree k becomes degree 2k, with no scalar lost. -/
theorem gtBiCollapse_diagonal (a b : R) (F : PowerSeries R) :
    gtBiCollapseHom a b (PowerSeries.mk fun n => monomial n (coeff n F)) =
      expand 2 two_ne_zero (rescale (a * b) F) := by
  apply PowerSeries.ext
  intro n
  change coeff n (gtBiCollapse a b _) = _
  simp only [gtBiCollapse, coeff_mk, gtBiCoeff, AddMonoidHom.comp_apply,
    LinearMap.toAddMonoidHom_coe, coeff_monomial]
  by_cases hn : 2 ∣ n
  · obtain ⟨k, rfl⟩ := hn
    rw [coeff_expand_mul, coeff_rescale, Finset.sum_eq_single (k, k)]
    · simp [mul_pow, mul_assoc]
    · intro p hp hne
      have hp := Finset.mem_antidiagonal.mp hp
      have he : p.2 ≠ p.1 := by
        intro he
        apply hne
        apply Prod.ext <;> dsimp <;> omega
      simp [Ne.symm he]
    · simp [Finset.mem_antidiagonal, two_mul]
  · rw [coeff_expand_of_not_dvd _ _ _ hn]
    apply Finset.sum_eq_zero
    intro p hp
    have hp := Finset.mem_antidiagonal.mp hp
    have he : p.2 ≠ p.1 := by
      intro he
      apply hn
      exact ⟨p.1, by omega⟩
    simp [Ne.symm he]

/-- The numerator (a*s*b*s;q) is the ordinary Euler factor expanded by two. -/
theorem gtBiCollapse_eulerPos (q : R) (h : PochhammerUnits q) (a b c : R) :
    gtBiCollapseHom a b
      (gtEulerPos (R := PowerSeries R) (PowerSeries.C q)
        (gtPochhammerUnits_map (S := PowerSeries R) PowerSeries.C q h)
        (PowerSeries.C c * X)) =
      expand 2 two_ne_zero (gtEulerPos q h (a * b * c)) := by
  have he : gtEulerPos (R := PowerSeries R) (PowerSeries.C q)
      (gtPochhammerUnits_map (S := PowerSeries R) PowerSeries.C q h) (PowerSeries.C c * X) =
        PowerSeries.mk (fun n => monomial n (coeff n (gtEulerPos q h c))) := by
    apply PowerSeries.ext
    intro n
    have hm (r : R) : monomial n r = PowerSeries.C r * X ^ n := by
      rw [X_pow_eq, ← monomial_zero_eq_C_apply, monomial_mul_monomial]
      simp
    simp only [gtEulerPos, coeff_mk, mul_pow]
    rw [← gtInvPoch_map (S := PowerSeries R) PowerSeries.C q h n,
      hm]
    simp only [map_mul, map_pow, map_neg, map_one]
    ring
  rw [he, gtBiCollapse_diagonal, gtEulerPos_rescale]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtEulerPos_map
#print axioms VOA.DeligneAudit.D4Char.gtEulerPos_rescale
#print axioms VOA.DeligneAudit.D4Char.gtBiCollapse_diagonal
#print axioms VOA.DeligneAudit.D4Char.gtBiCollapse_eulerPos
