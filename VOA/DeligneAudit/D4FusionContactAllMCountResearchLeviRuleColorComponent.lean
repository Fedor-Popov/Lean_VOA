import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleComponentActual

/-! The original ideal's exact PBW/current/C/three-bit component, with every
source's color degree proved from its actual sparse current arrows. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

/-- A contact letter replaces C by its actual output color. -/
def contactBitIncrement (d : Fin 3) (a : Fin 18) : ℤ := bitWeight d (target a 8)

theorem contact_bit_rule : ∀ (a : Fin 18) (d : Fin 3) (i : Fin 9), 10 ≤ a.val →
    coeff a i = 0 ∨ bitWeight d (target a i) = bitWeight d i + contactBitIncrement d a := by
  decide +kernel

/-- Exact color degree of a whole original C source, before any projection. -/
theorem c_sourceWord_bit_degree (m : ℕ) (j : AllM.SeedIndex m) (hj : j.val.1 = true)
    (modes : List ℕ) (l : List (Fin 18 × ℕ)) (hl : ∀ x ∈ l, category x.1 = 0)
    (d : Fin 3) :
    (sourceWord m j modes l).IsWeightedHomogeneous (modeWeight m (bitWeight d) 0)
      (wordGrade (contactBitIncrement d) 0 l) := by
  have hp := shifted_seed_graded m j modes (bitWeight d) 0
  have hcolor : bitWeight d (sourceColor j.val.1) = 0 := by
    rw [hj]; fin_cases d <;> rfl
  simp only [hcolor,mul_zero,zero_mul,add_zero] at hp
  have hh := word_graded ℂ m (bitWeight d) 0 (contactBitIncrement d) l
    (fun x hx i => contact_bit_rule x.1 d i ((category_zero_iff x.1).mp (hl x hx))) hp
  simpa only [zero_add] using hh

def orbitSourceBitDegree (m : ℕ) (i : OrbitSourceIndex m) (d : Fin 3) : ℤ :=
  if i.seed.val.1 then wordGrade (contactBitIncrement d) 0 i.outer
  else wordGrade (axisIncrement d) 0 i.outer

theorem orbitSourcePoly_bit_graded (m : ℕ) (i : OrbitSourceIndex m) (d : Fin 3) :
    (orbitSourcePoly m i).IsWeightedHomogeneous (modeWeight m (bitWeight d) 0)
      (orbitSourceBitDegree m i d) := by
  cases hb : i.seed.val.1 with
  | false =>
      have hl : ∀ x ∈ i.outer, category x.1 = 1 := by
        intro x hx
        simpa only [branchCategory,hb,Bool.false_eq_true,if_false] using i.branch x hx
      simpa only [orbitSourceBitDegree,hb,Bool.false_eq_true,if_false] using
        u_sourceWord_axis_degree m i.seed hb i.shifts i.outer hl d
  | true =>
      have hl : ∀ x ∈ i.outer, category x.1 = 0 := by
        intro x hx
        simpa only [branchCategory,hb,if_true] using i.branch x hx
      simpa only [orbitSourceBitDegree,hb,if_true] using
        c_sourceWord_bit_degree m i.seed hb i.shifts i.outer hl d

/-- PBW, current, C, then the three actual Boolean-color bit weights. -/
def colorComponentWeight (m : ℕ) : Fin 9 × Fin m → Fin 6 → ℤ := fun x =>
  ![componentWeight m x 0,componentWeight m x 1,componentWeight m x 2,
    modeWeight m (bitWeight 0) 0 x,modeWeight m (bitWeight 1) 0 x,
    modeWeight m (bitWeight 2) 0 x]

def orbitSourceColorDegree (m : ℕ) (i : OrbitSourceIndex m) : Fin 6 → ℤ :=
  ![orbitSourceDegree m i 0,orbitSourceDegree m i 1,orbitSourceDegree m i 2,
    orbitSourceBitDegree m i 0,orbitSourceBitDegree m i 1,orbitSourceBitDegree m i 2]

/-- Every original row has its full six-coordinate degree, including zero rows. -/
theorem orbitSourcePoly_color_graded (m : ℕ) (i : OrbitSourceIndex m) :
    (orbitSourcePoly m i).IsWeightedHomogeneous (colorComponentWeight m)
      (orbitSourceColorDegree m i) := by
  apply (weighted_pi_iff _ _ _).mpr
  intro j
  fin_cases j
  · exact (weighted_pi_iff _ _ _).mp (orbitSourcePoly_graded m i) 0
  · exact (weighted_pi_iff _ _ _).mp (orbitSourcePoly_graded m i) 1
  · exact (weighted_pi_iff _ _ _).mp (orbitSourcePoly_graded m i) 2
  · exact orbitSourcePoly_bit_graded m i 0
  · exact orbitSourcePoly_bit_graded m i 1
  · exact orbitSourcePoly_bit_graded m i 2

/-- Exact extraction of the original ideal's six-coordinate homogeneous slice. -/
theorem candidate_color_component_eq_matching_span (m : ℕ) (n : Fin 6 → ℤ) :
    (AllM.candidateIdeal m).restrictScalars ℂ ⊓
      MvPolynomial.weightedHomogeneousSubmodule ℂ (colorComponentWeight m) n =
        Submodule.span ℂ (matchingGradeProducts (colorComponentWeight m)
          (orbitSourcePoly m) (orbitSourceColorDegree m) n) := by
  rw [candidateIdeal_eq_orbitIdeal,orbitIdeal,← orbitSourcePoly_range]
  exact (matching_span_eq_ideal_component (colorComponentWeight m) (orbitSourcePoly m)
    (orbitSourceColorDegree m) (orbitSourcePoly_color_graded m) n).symm

/-- Forgetting the last three coordinates recovers the original component weights. -/
theorem colorComponentWeight_base (m : ℕ) (x : Fin 9 × Fin m) (j : Fin 3) :
    colorComponentWeight m x (Fin.castAdd 3 j) = componentWeight m x j := by
  fin_cases j <;> rfl

theorem orbitSourceColorDegree_base (m : ℕ) (i : OrbitSourceIndex m) (j : Fin 3) :
    orbitSourceColorDegree m i (Fin.castAdd 3 j) = orbitSourceDegree m i j := by
  fin_cases j <;> rfl

theorem color_monomial_weight_base (m : ℕ) (e : Fin 9 × Fin m →₀ ℕ) (j : Fin 3) :
    Finsupp.weight (colorComponentWeight m) e (Fin.castAdd 3 j) =
      Finsupp.weight (componentWeight m) e j := by
  simp only [Finsupp.weight_apply,Finsupp.sum,Finset.sum_apply,Pi.smul_apply,
    colorComponentWeight_base]

/-- Existing actual PBW/current/C budgets apply directly to every color match. -/
theorem color_matching_base (m : ℕ) (i : OrbitSourceIndex m) (e : Fin 9 × Fin m →₀ ℕ)
    (n : Fin 6 → ℤ)
    (hm : Finsupp.weight (colorComponentWeight m) e + orbitSourceColorDegree m i = n) :
    Finsupp.weight (componentWeight m) e + orbitSourceDegree m i =
      fun j => n (Fin.castAdd 3 j) := by
  funext j
  have hh := congrFun hm (Fin.castAdd 3 j)
  simpa only [Pi.add_apply,color_monomial_weight_base,orbitSourceColorDegree_base] using hh

/-- The stored quintic Cartan-weight block, expressed in actual bit coordinates. -/
def quinticColorDegree (m : ℕ) : Fin 6 → ℤ := ![5,((2*m-3 : ℕ) : ℤ),0,2,2,2]

theorem candidate_quintic_color_component_eq_matching_span (m : ℕ) :
    (AllM.candidateIdeal m).restrictScalars ℂ ⊓
      MvPolynomial.weightedHomogeneousSubmodule ℂ (colorComponentWeight m) (quinticColorDegree m) =
        Submodule.span ℂ (matchingGradeProducts (colorComponentWeight m)
          (orbitSourcePoly m) (orbitSourceColorDegree m) (quinticColorDegree m)) :=
  candidate_color_component_eq_matching_span m _

end
#print axioms color_matching_base
#print axioms contact_bit_rule
#print axioms c_sourceWord_bit_degree
#print axioms orbitSourcePoly_color_graded
#print axioms candidate_quintic_color_component_eq_matching_span
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
