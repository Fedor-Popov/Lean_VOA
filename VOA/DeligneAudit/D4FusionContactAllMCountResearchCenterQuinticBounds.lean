import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleComponentBounds

/-! Exact original C-source budgets in the degree-five/current-(2m-3)
pure-A component. The small natural-subtraction exceptions are excluded
explicitly; no C-source ideal membership or count is asserted. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

theorem matching_center_quintic_power_cases (m : ℕ) (hm : 2 ≤ m)
    (i : OrbitSourceIndex m) (e : (Fin 9 × Fin m) →₀ ℕ)
    (hb : i.seed.val.1 = true)
    (hmatch : Finsupp.weight (componentWeight m) e + orbitSourceDegree m i =
      pureATargetDegree 5 (2 * m - 3)) :
    i.seed.val.2.1 = 4 ∨ i.seed.val.2.1 = 5 := by
  have hp := matching_source_power_le m 5 (2 * m - 3) i e hmatch
  have hc := matching_source_current_sum_le m 5 (2 * m - 3) i e hmatch
  have hs : 2 * m < i.seed.val.2.1 + i.seed.val.2.2 := by
    simpa only [AllM.seedThreshold,hb,if_true] using i.seed.property.2
  omega

theorem matching_center_quintic_mode_budget (m : ℕ) (hm : 2 ≤ m)
    (i : OrbitSourceIndex m) (e : (Fin 9 × Fin m) →₀ ℕ)
    (hb : i.seed.val.1 = true)
    (hmatch : Finsupp.weight (componentWeight m) e + orbitSourceDegree m i =
      pureATargetDegree 5 (2 * m - 3)) :
    i.shifts.sum + (i.outer.map Prod.snd).sum ≤ i.seed.val.2.1 - 4 := by
  have hp := matching_source_power_le m 5 (2 * m - 3) i e hmatch
  have hc := matching_source_current_sum_le m 5 (2 * m - 3) i e hmatch
  have hs : 2 * m < i.seed.val.2.1 + i.seed.val.2.2 := by
    simpa only [AllM.seedThreshold,hb,if_true] using i.seed.property.2
  omega

theorem matching_center_quartic_static_budget (m : ℕ) (hm : 2 ≤ m)
    (i : OrbitSourceIndex m) (e : (Fin 9 × Fin m) →₀ ℕ)
    (hb : i.seed.val.1 = true) (hr : i.seed.val.2.1 = 4)
    (hmatch : Finsupp.weight (componentWeight m) e + orbitSourceDegree m i =
      pureATargetDegree 5 (2 * m - 3)) :
    i.seed.val.2.2 = 2 * m - 3 ∧ i.shifts.sum = 0 ∧ (i.outer.map Prod.snd).sum = 0 := by
  have hc := matching_source_current_sum_le m 5 (2 * m - 3) i e hmatch
  have hs : 2 * m < i.seed.val.2.1 + i.seed.val.2.2 := by
    simpa only [AllM.seedThreshold,hb,if_true] using i.seed.property.2
  omega

/-- A fifth-power source already exhausts the PBW budget, so its matching
multiplier is the literal constant monomial. -/
theorem matching_fifth_source_multiplier_zero (m T : ℕ)
    (i : OrbitSourceIndex m) (e : (Fin 9 × Fin m) →₀ ℕ)
    (hr : i.seed.val.2.1 = 5)
    (hmatch : Finsupp.weight (componentWeight m) e + orbitSourceDegree m i =
      pureATargetDegree 5 T) : e = 0 := by
  have he := congrFun hmatch 0
  change Finsupp.weight (componentWeight m) e 0 + (i.seed.val.2.1 : ℤ) = 5 at he
  have hz : Finsupp.weight (componentWeight m) e 0 = 0 := by rw [hr] at he; omega
  apply Finsupp.ext
  intro x
  have hx := component_term_le_weight m e 0 x
  have hw : componentWeight m x 0 = 1 := by simp [componentWeight,modeWeight]
  rw [hw,mul_one,hz] at hx
  have hez : (e x : ℤ) = 0 := by omega
  exact_mod_cast hez

end
#print axioms matching_center_quintic_power_cases
#print axioms matching_center_quintic_mode_budget
#print axioms matching_center_quartic_static_budget
#print axioms matching_fifth_source_multiplier_zero
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
