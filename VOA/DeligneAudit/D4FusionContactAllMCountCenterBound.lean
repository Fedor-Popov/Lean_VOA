import VOA.DeligneAudit.D4FusionContactAllMCountCenter
import VOA.DeligneAudit.DeligneFusionCVRectBound
import VOA.DeligneAudit.DeligneFusionCVRectPolynomialCurrent
import VOA.DeligneAudit.DeligneFusionCVRectReflection

/-! A genuine enlarged-family base: the actual center-only quotient has rank at most3^m.
The checked one-color coefficient ideal maps into the actual image ideal. -/

namespace VOA.DeligneAudit.D4FusionContact.Polynomial.AllMCount

open VOA.DeligneAudit.A2

noncomputable section

def fromOneColor (m : ℕ) : CVRectFamily.Ring 0 m →ₐ[ℂ] CenterRing m :=
  MvPolynomial.aeval (Sum.elim Fin.elim0 MvPolynomial.X)

theorem fromOneColor_surjective (m : ℕ) : Function.Surjective (fromOneColor m) := by
  let sectionMap : CenterRing m →ₐ[ℂ] CVRectFamily.Ring 0 m := MvPolynomial.rename Sum.inr
  have he : (fromOneColor m).comp sectionMap = AlgHom.id ℂ (CenterRing m) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [sectionMap, fromOneColor]
  intro p
  exact ⟨sectionMap p, congrArg (fun f : CenterRing m →ₐ[ℂ] CenterRing m => f p) he⟩

theorem fromOneColor_reverse (m : ℕ) :
    PowerSeries.map (fromOneColor m).toRingHom (CVRectSplit.reverseRight 0 m) =
      (Polynomial.reflect (m - 1) (CVRectPolynomial.finiteCurrent m (centerMode m)) :
        PowerSeries (CenterRing m)) := by
  rw [CVRectPolynomial.reflect_finiteCurrent_series]
  unfold CVRectSplit.reverseRight
  simp only [map_sum, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X]
  apply Finset.sum_congr rfl
  intro i _
  simp [fromOneColor, centerMode, i.isLt]

theorem oneColor_ideal_le (m : ℕ) :
    CVRectFamily.ideal 0 m [] (List.replicate m 2) ≤
      (centerIdeal m).comap (fromOneColor m).toRingHom := by
  unfold CVRectFamily.ideal CVRectIntegrationIdeal.coefficientIdeal
  apply Ideal.span_le.mpr
  rintro _ ⟨a, b, j, hj, rfl⟩
  change fromOneColor m (PowerSeries.coeff j
    (CVRectSplit.reverseLeft 0 m ^ a * CVRectSplit.reverseRight 0 m ^ b)) ∈ centerIdeal m
  cases a with
  | succ a =>
      simp only [CVRectSplit.reverseLeft_zero, zero_pow (Nat.succ_ne_zero _),
        zero_mul, map_zero]
      exact (centerIdeal m).zero_mem
  | zero =>
      simp only [pow_zero, one_mul]
      have horder : j < m * (b - 2) := by
        simpa [CVRectZero.familyOrder, CVRectIntegrationOrder.excess, nsmul_eq_mul] using hj
      have hm : 1 ≤ m := by
        by_contra hh
        have he : m = 0 := by omega
        subst m
        simp only [Nat.zero_mul] at horder
        omega
      have hb : 3 ≤ b := by
        by_contra hh
        have he : b - 2 = 0 := by omega
        rw [he, Nat.mul_zero] at horder
        omega
      let f := CVRectPolynomial.finiteCurrent m (centerMode m)
      have hf : f.natDegree ≤ m - 1 := CVRectPolynomial.finiteCurrent_natDegree_le _ _
      change (fromOneColor m).toRingHom
        (PowerSeries.coeff j (CVRectSplit.reverseRight 0 m ^ b)) ∈ centerIdeal m
      rw [← PowerSeries.coeff_map, map_pow, fromOneColor_reverse,
        ← Polynomial.coe_pow, Polynomial.coeff_coe]
      change (Polynomial.reflect (m - 1) f ^ b).coeff j ∈ centerIdeal m
      by_cases hdegree : j ≤ (m - 1) * b
      · have he := CVRectReflection.coeff_reflect_pow_mul_pow f 1 (m - 1) 0 b 0 j hf
          (by simp) (by simpa only [Nat.mul_zero, Nat.add_zero] using hdegree)
        simp only [pow_zero, mul_one] at he
        rw [he]
        have hD : (m - 1) * b + b = m * b := by
          calc
            _ = (m - 1 + 1) * b := by ring
            _ = _ := by rw [Nat.sub_add_cancel hm]
        have hM : m * b = m * (b - 2) + 2 * m := by
          calc
            _ = m * (b - 2 + 2) := by rw [Nat.sub_add_cancel (show 2 ≤ b by omega)]
            _ = _ := by ring
        have hs : 2 * m < b + ((m - 1) * b - j) := by
          have heq := Nat.sub_add_cancel hdegree
          omega
        have hh := center_coefficient_mem m b ((m - 1) * b - j) (by omega) hs
        have hseries : (f : PowerSeries (CenterRing m)) = centerCurrent m :=
          CVRectPolynomial.finiteCurrent_series m (centerMode m) (centerMode_high m)
        rw [← hseries, ← Polynomial.coe_pow, Polynomial.coeff_coe] at hh
        exact hh
      · have he := CVRectReflection.coeff_reflect_pow_mul_pow_high f 1 (m - 1) 0 b 0 j hf
          (by simp) (by simpa only [Nat.mul_zero, Nat.add_zero] using (by omega : (m - 1) * b < j))
        simp only [pow_zero, mul_one] at he
        rw [he]
        exact (centerIdeal m).zero_mem

def centerModelMap (m : ℕ) :
    CVRectFamily.Model 0 m [] (List.replicate m 2) →ₐ[ℂ] CenterModel m :=
  Ideal.quotientMapₐ (centerIdeal m) (fromOneColor m) (oneColor_ideal_le m)

theorem centerModelMap_surjective (m : ℕ) : Function.Surjective (centerModelMap m) :=
  Ideal.quotientMap_surjective (H := oneColor_ideal_le m) (fromOneColor_surjective m)

theorem oneColor_model_bound (m : ℕ) :
    FiniteDimensional ℂ (CVRectFamily.Model 0 m [] (List.replicate m 2)) ∧
      Module.finrank ℂ (CVRectFamily.Model 0 m [] (List.replicate m 2)) ≤ 3 ^ m := by
  let one := List.replicate m 2
  let P : ℕ → Prop := fun n => FiniteDimensional ℂ (CVRectFamily.Model 0 n [] one) ∧
    Module.finrank ℂ (CVRectFamily.Model 0 n [] one) ≤ CVRectCount.familyWeight [] one
  have hb : P (0 + one.length) := CVRectBound.family_bound [] one
  have he : P (0 + one.length) = P m := congrArg P (by simp only [one, List.length_replicate,
    Nat.zero_add])
  have ht := he.mp hb
  exact ⟨ht.1, ht.2.trans_eq (by simp [CVRectCount.familyWeight, one])⟩

/-- Unconditional count of the actual all-A-deleted quotient. It is one
base of a possible enlarged recurrence, not the full28^m theorem. -/
theorem center_model_bound (m : ℕ) :
    FiniteDimensional ℂ (CenterModel m) ∧ Module.finrank ℂ (CenterModel m) ≤ 3 ^ m := by
  have hb := oneColor_model_bound m
  haveI := hb.1
  let f := (centerModelMap m).toLinearMap
  have hf : Function.Surjective f := centerModelMap_surjective m
  haveI := Module.Finite.of_surjective f hf
  exact ⟨inferInstance, (LinearMap.finrank_le_finrank_of_surjective hf).trans hb.2⟩

end
end VOA.DeligneAudit.D4FusionContact.Polynomial.AllMCount

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllMCount.oneColor_ideal_le
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllMCount.center_model_bound
