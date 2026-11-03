import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleComponentActual

/-! Concrete source budgets extracted from the original matching-component
formula. No bounded-list exhaustion or numerical rank is assumed. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

def pureATargetDegree (D T : ℕ) : Fin 3 → ℤ := ![(D : ℤ),(T : ℤ),0]

theorem componentWeight_nonneg (m : ℕ) (x : Fin 9 × Fin m) (j : Fin 3) :
    0 ≤ componentWeight m x j := by
  fin_cases j
  · change 0 ≤ (1 : ℤ) + 0 * x.2.val
    simp only [zero_mul,add_zero]
    omega
  · change 0 ≤ (0 : ℤ) + 1 * x.2.val
    simp only [zero_add,one_mul]
    exact Nat.cast_nonneg _
  · change 0 ≤ cWeight x.1 + 0 * x.2.val
    simpa only [zero_mul,add_zero] using cWeight_nonneg x.1

theorem component_monomial_weight_eq (m : ℕ) (e : (Fin 9 × Fin m) →₀ ℕ) (j : Fin 3) :
    Finsupp.weight (componentWeight m) e j =
      e.sum (fun x k => (k : ℤ) * componentWeight m x j) := by
  simp only [Finsupp.weight_apply,Finsupp.sum,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro x _
  change e x • componentWeight m x j = (e x : ℤ) * componentWeight m x j
  simp only [nsmul_eq_mul]

theorem component_monomial_weight_nonneg (m : ℕ) (e : (Fin 9 × Fin m) →₀ ℕ) (j : Fin 3) :
    0 ≤ Finsupp.weight (componentWeight m) e j := by
  rw [component_monomial_weight_eq,Finsupp.sum]
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (Nat.cast_nonneg _) (componentWeight_nonneg m x j))

theorem component_term_le_weight (m : ℕ) (e : (Fin 9 × Fin m) →₀ ℕ)
    (j : Fin 3) (x : Fin 9 × Fin m) :
    (e x : ℤ) * componentWeight m x j ≤ Finsupp.weight (componentWeight m) e j := by
  classical
  by_cases hx : e x = 0
  · rw [hx,Nat.cast_zero,zero_mul]
    exact component_monomial_weight_nonneg m e j
  · rw [component_monomial_weight_eq,Finsupp.sum]
    exact Finset.single_le_sum
      (fun y _ => mul_nonneg (Nat.cast_nonneg _) (componentWeight_nonneg m y j))
      (Finsupp.mem_support_iff.mpr hx)

/-- A zero-C-degree monomial contains no C variable at any current mode. -/
theorem component_c_zero_exponent (m : ℕ) (e : (Fin 9 × Fin m) →₀ ℕ)
    (hz : Finsupp.weight (componentWeight m) e 2 = 0) (k : Fin m) : e (8,k) = 0 := by
  have ht := component_term_le_weight m e 2 (8,k)
  have hc : componentWeight m (8,k) 2 = 1 := by simp [componentWeight,modeWeight,cWeight]
  rw [hc,mul_one,hz] at ht
  have he : (e (8,k) : ℤ) = 0 := by omega
  exact_mod_cast he

/-- PBW budget comes directly from the matching grade equality. -/
theorem matching_source_power_le (m D T : ℕ) (i : OrbitSourceIndex m)
    (e : (Fin 9 × Fin m) →₀ ℕ)
    (hmatch : Finsupp.weight (componentWeight m) e + orbitSourceDegree m i =
      pureATargetDegree D T) :
    i.seed.val.2.1 ≤ D := by
  have he := congrFun hmatch 0
  change Finsupp.weight (componentWeight m) e 0 + (i.seed.val.2.1 : ℤ) = (D : ℤ) at he
  have hw := component_monomial_weight_nonneg m e 0
  have hh : (i.seed.val.2.1 : ℤ) ≤ D := by omega
  exact_mod_cast hh

/-- Seed coefficient plus all nonnegative shift/outer modes fit the current budget. -/
theorem matching_source_current_sum_le (m D T : ℕ) (i : OrbitSourceIndex m)
    (e : (Fin 9 × Fin m) →₀ ℕ)
    (hmatch : Finsupp.weight (componentWeight m) e + orbitSourceDegree m i =
      pureATargetDegree D T) :
    i.seed.val.2.2 + i.shifts.sum + (i.outer.map Prod.snd).sum ≤ T := by
  have he := congrFun hmatch 1
  change Finsupp.weight (componentWeight m) e 1 +
    ((i.seed.val.2.2 + i.shifts.sum + (i.outer.map Prod.snd).sum : ℕ) : ℤ) = (T : ℤ) at he
  have hw := component_monomial_weight_nonneg m e 1
  have hh : ((i.seed.val.2.2 + i.shifts.sum + (i.outer.map Prod.snd).sum : ℕ) : ℤ) ≤ T := by omega
  exact_mod_cast hh

theorem matching_source_current_bounds (m D T : ℕ) (i : OrbitSourceIndex m)
    (e : (Fin 9 × Fin m) →₀ ℕ)
    (hmatch : Finsupp.weight (componentWeight m) e + orbitSourceDegree m i =
      pureATargetDegree D T) :
    i.seed.val.2.2 ≤ T ∧ i.shifts.sum ≤ T ∧ (i.outer.map Prod.snd).sum ≤ T := by
  have h := matching_source_current_sum_le m D T i e hmatch
  omega

/-- A NONZERO matching C product converts every original C factor exactly once. -/
theorem matching_c_contacts_exact (m D T : ℕ) (i : OrbitSourceIndex m)
    (e : (Fin 9 × Fin m) →₀ ℕ) (hb : i.seed.val.1 = true)
    (hmatch : Finsupp.weight (componentWeight m) e + orbitSourceDegree m i =
      pureATargetDegree D T)
    (hne : MvPolynomial.monomial e (1 : ℂ) * orbitSourcePoly m i ≠ 0) :
    i.outer.length = i.seed.val.2.1 ∧ Finsupp.weight (componentWeight m) e 2 = 0 := by
  have hs : orbitSourcePoly m i ≠ 0 := right_ne_zero_of_mul hne
  have hl : ∀ x ∈ i.outer, category x.1 = 0 := by
    intro x hx
    simpa only [branchCategory,hb,if_true] using i.branch x hx
  have hlen : i.outer.length ≤ i.seed.val.2.1 := by
    by_contra h
    apply hs
    exact c_sourceWord_too_many_contacts m i.seed hb i.shifts i.outer hl (by omega)
  have hlenZ : (i.outer.length : ℤ) ≤ i.seed.val.2.1 := by exact_mod_cast hlen
  have he := congrFun hmatch 2
  change Finsupp.weight (componentWeight m) e 2 +
    (if i.seed.val.1 then (i.seed.val.2.1 : ℤ) - i.outer.length else 0) = 0 at he
  rw [hb,if_pos rfl] at he
  have hw := component_monomial_weight_nonneg m e 2
  have hsame : (i.outer.length : ℤ) = (i.seed.val.2.1 : ℤ) := by omega
  constructor
  · exact_mod_cast hsame
  · omega

/-- Every nonzero matching pure-A product has a pure-A multiplier. -/
theorem matching_multiplier_c_zero (m D T : ℕ) (i : OrbitSourceIndex m)
    (e : (Fin 9 × Fin m) →₀ ℕ)
    (hmatch : Finsupp.weight (componentWeight m) e + orbitSourceDegree m i =
      pureATargetDegree D T)
    (hne : MvPolynomial.monomial e (1 : ℂ) * orbitSourcePoly m i ≠ 0) :
    Finsupp.weight (componentWeight m) e 2 = 0 := by
  cases hb : i.seed.val.1 with
  | true => exact (matching_c_contacts_exact m D T i e hb hmatch hne).2
  | false =>
      have he := congrFun hmatch 2
      change Finsupp.weight (componentWeight m) e 2 +
        (if i.seed.val.1 then (i.seed.val.2.1 : ℤ) - i.outer.length else 0) = 0 at he
      simpa only [hb,Bool.false_eq_true,if_false,add_zero] using he

theorem matching_multiplier_no_c (m D T : ℕ) (i : OrbitSourceIndex m)
    (e : (Fin 9 × Fin m) →₀ ℕ)
    (hmatch : Finsupp.weight (componentWeight m) e + orbitSourceDegree m i =
      pureATargetDegree D T)
    (hne : MvPolynomial.monomial e (1 : ℂ) * orbitSourcePoly m i ≠ 0) :
    ∀ k : Fin m, e (8,k) = 0 :=
  component_c_zero_exponent m e (matching_multiplier_c_zero m D T i e hmatch hne)

end
#print axioms matching_source_power_le
#print axioms matching_source_current_bounds
#print axioms matching_c_contacts_exact
#print axioms matching_multiplier_no_c
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
