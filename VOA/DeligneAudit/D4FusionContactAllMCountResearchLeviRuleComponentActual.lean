import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleCutoffs
import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleGradeProjectionComponents

/-! Exact simultaneous PBW/current/C component spans for the original
candidate differential ideal. No finite enumeration or rank is assumed. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

/-- Negative currents preserve the number of C factors, including killed arrows. -/
theorem negative_c_rule : ∀ (a : Fin 18) (i : Fin 9), (7 ≤ a.val ∧ a.val<10) →
    coeff a i = 0 ∨ cWeight (target a i) = cWeight i := by decide +kernel

theorem u_sourceWord_c_degree (m : ℕ) (j : AllM.SeedIndex m) (hj : j.val.1 = false)
    (modes : List ℕ) (l : List (Fin 18 × ℕ)) (hl : ∀ x ∈ l, category x.1 = 1) :
    (sourceWord m j modes l).IsWeightedHomogeneous (modeWeight m cWeight 0) 0 := by
  have hp := shifted_seed_graded m j modes cWeight 0
  have hcolor : cWeight (sourceColor j.val.1) = 0 := by rw [hj]; rfl
  simp only [hcolor,mul_zero,zero_mul,add_zero] at hp
  have hh := word_graded ℂ m cWeight 0 (fun _ => 0) l (fun x hx i => ?_) hp
  · simpa only [wordGrade,zero_mul,add_zero,List.map_const',List.sum_replicate,nsmul_zero] using hh
  · rcases negative_c_rule x.1 i ((category_one_iff x.1).mp (hl x hx)) with hz | hw
    · exact Or.inl hz
    · exact Or.inr (by simpa only [add_zero] using hw)

/-- Syntactic sources retain their proved grade even when the polynomial is zero. -/
structure OrbitSourceIndex (m : ℕ) where
  seed : AllM.SeedIndex m
  shifts : List ℕ
  outer : List (Fin 18 × ℕ)
  branch : ∀ x ∈ outer, category x.1 = branchCategory seed.val.1

def orbitSourcePoly (m : ℕ) (i : OrbitSourceIndex m) : Ring ℂ m :=
  sourceWord m i.seed i.shifts i.outer

theorem orbitSourcePoly_range (m : ℕ) : Set.range (orbitSourcePoly m) = orbitSeeds m := by
  ext p
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨i.seed,i.shifts,i.outer,i.branch,rfl⟩
  · rintro ⟨j,modes,outer,hc,rfl⟩
    exact ⟨⟨j,modes,outer,hc⟩,rfl⟩

def componentWeight (m : ℕ) : Fin 9 × Fin m → Fin 3 → ℤ := fun x =>
  ![modeWeight m (fun _ => 1) 0 x,modeWeight m (fun _ => 0) 1 x,modeWeight m cWeight 0 x]

def orbitSourceDegree (m : ℕ) (i : OrbitSourceIndex m) : Fin 3 → ℤ :=
  ![(i.seed.val.2.1:ℤ),
    ((i.seed.val.2.2+i.shifts.sum+(i.outer.map Prod.snd).sum:ℕ):ℤ),
    if i.seed.val.1 then (i.seed.val.2.1:ℤ)-i.outer.length else 0]

theorem orbitSourcePoly_c_degree (m : ℕ) (i : OrbitSourceIndex m) :
    (orbitSourcePoly m i).IsWeightedHomogeneous (modeWeight m cWeight 0)
      (if i.seed.val.1 then (i.seed.val.2.1:ℤ)-i.outer.length else 0) := by
  cases hb : i.seed.val.1 with
  | false =>
      have hl : ∀ x ∈ i.outer, category x.1 = 1 := by
        intro x hx
        simpa only [branchCategory,hb,Bool.false_eq_true,if_false] using i.branch x hx
      simpa only [hb,Bool.false_eq_true,if_false] using
        u_sourceWord_c_degree m i.seed hb i.shifts i.outer hl
  | true =>
      have hl : ∀ x ∈ i.outer, category x.1 = 0 := by
        intro x hx
        simpa only [branchCategory,hb,if_true] using i.branch x hx
      simpa only [hb,if_true] using c_sourceWord_degree m i.seed hb i.shifts i.outer hl

/-- Every original syntactic orbit source has its exact simultaneous grade. -/
theorem orbitSourcePoly_graded (m : ℕ) (i : OrbitSourceIndex m) :
    (orbitSourcePoly m i).IsWeightedHomogeneous (componentWeight m) (orbitSourceDegree m i) := by
  apply (weighted_pi_iff _ _ _).mpr
  intro j
  fin_cases j
  · exact sourceWord_pbw m i.seed i.shifts i.outer
  · exact sourceWord_current m i.seed i.shifts i.outer
  · exact orbitSourcePoly_c_degree m i

/-- Exact component extraction from the original candidate ideal, with no
presentation, enumeration, finiteness or dimension premise. -/
theorem candidate_component_eq_matching_span (m : ℕ) (n : Fin 3 → ℤ) :
    (AllM.candidateIdeal m).restrictScalars ℂ ⊓
      MvPolynomial.weightedHomogeneousSubmodule ℂ (componentWeight m) n =
        Submodule.span ℂ (matchingGradeProducts (componentWeight m)
          (orbitSourcePoly m) (orbitSourceDegree m) n) := by
  rw [candidateIdeal_eq_orbitIdeal,orbitIdeal,← orbitSourcePoly_range]
  exact (matching_span_eq_ideal_component (componentWeight m) (orbitSourcePoly m)
    (orbitSourceDegree m) (orbitSourcePoly_graded m) n).symm

end
#print axioms orbitSourcePoly_range
#print axioms u_sourceWord_c_degree
#print axioms orbitSourcePoly_graded
#print axioms candidate_component_eq_matching_span
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
