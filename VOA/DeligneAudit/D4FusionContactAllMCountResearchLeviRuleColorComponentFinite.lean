import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleColorComponentCartan
import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleComponentFinite

/-! Exact finite six-color components of the original candidate ideal.
Every projected finite source product is zero or its unchanged original row. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

/-- Pure-A target with three additional, arbitrary integral bit degrees. -/
def pureAColorTargetDegree (D T : ℕ) (b : Fin 3 → ℤ) : Fin 6 → ℤ :=
  ![(D : ℤ),(T : ℤ),0,b 0,b 1,b 2]

theorem pureAColorTargetDegree_base (D T : ℕ) (b : Fin 3 → ℤ) (j : Fin 3) :
    pureAColorTargetDegree D T b (Fin.castAdd 3 j) = pureATargetDegree D T j := by
  fin_cases j <;> rfl

theorem color_component_forget (m D T : ℕ) (b : Fin 3 → ℤ) (p : Ring ℂ m)
    (hp : p.IsWeightedHomogeneous (colorComponentWeight m) (pureAColorTargetDegree D T b)) :
    p.IsWeightedHomogeneous (componentWeight m) (pureATargetDegree D T) := by
  intro e he
  funext j
  have hh := congrFun (hp he) (Fin.castAdd 3 j)
  simpa only [color_monomial_weight_base,pureAColorTargetDegree_base] using hh

/-- Restrict the existing explicit finite source-product indices by exact bit grade. -/
def boundedColorComponentPairs (m D T : ℕ) (b : Fin 3 → ℤ) :
    Set (OrbitSourceIndex m × ((Fin 9 × Fin m) →₀ ℕ)) :=
  {q | q ∈ boundedComponentPairs m D T ∧
    Finsupp.weight (colorComponentWeight m) q.2 + orbitSourceColorDegree m q.1 =
      pureAColorTargetDegree D T b}

theorem boundedColorComponentPairs_finite (m D T : ℕ) (b : Fin 3 → ℤ) :
    (boundedColorComponentPairs m D T b).Finite :=
  (boundedComponentPairs_finite m D T).subset (fun _ h => h.1)

/-- Literal unchanged monomial multiples of bounded original whole source words. -/
def finiteColorComponentRows (m D T : ℕ) (b : Fin 3 → ℤ) : Set (Ring ℂ m) :=
  (fun q => MvPolynomial.monomial q.2 (1 : ℂ) * orbitSourcePoly m q.1) ''
    boundedColorComponentPairs m D T b

theorem finiteColorComponentRows_finite (m D T : ℕ) (b : Fin 3 → ℤ) :
    (finiteColorComponentRows m D T b).Finite :=
  (boundedColorComponentPairs_finite m D T b).image _

theorem actual_product_color_graded (m : ℕ)
    (q : OrbitSourceIndex m × ((Fin 9 × Fin m) →₀ ℕ)) :
    (MvPolynomial.monomial q.2 (1 : ℂ) * orbitSourcePoly m q.1).IsWeightedHomogeneous
      (colorComponentWeight m)
      (Finsupp.weight (colorComponentWeight m) q.2 + orbitSourceColorDegree m q.1) :=
  (MvPolynomial.isWeightedHomogeneous_monomial (colorComponentWeight m) q.2 (1 : ℂ) rfl).mul
    (orbitSourcePoly_color_graded m q.1)

/-- Projection creates no artificial source rows: every output is zero or the original. -/
theorem actual_product_color_projection (m : ℕ)
    (q : OrbitSourceIndex m × ((Fin 9 × Fin m) →₀ ℕ)) (n : Fin 6 → ℤ) :
    MvPolynomial.weightedHomogeneousComponent (colorComponentWeight m) n
      (MvPolynomial.monomial q.2 (1 : ℂ) * orbitSourcePoly m q.1) = 0 ∨
    MvPolynomial.weightedHomogeneousComponent (colorComponentWeight m) n
      (MvPolynomial.monomial q.2 (1 : ℂ) * orbitSourcePoly m q.1) =
        MvPolynomial.monomial q.2 (1 : ℂ) * orbitSourcePoly m q.1 := by
  classical
  have hg := actual_product_color_graded m q
  by_cases hn : Finsupp.weight (colorComponentWeight m) q.2 + orbitSourceColorDegree m q.1 = n
  · exact Or.inr (by rw [hn] at hg; exact hg.weightedHomogeneousComponent_same)
  · exact Or.inl (hg.weightedHomogeneousComponent_ne n (Ne.symm hn))

/-- Every projected original base row lies in the literal finite color-row span. -/
theorem finite_base_row_color_projection_mem (m D T : ℕ) (b : Fin 3 → ℤ)
    (p : Ring ℂ m) (hp : p ∈ finiteComponentRows m D T) :
    MvPolynomial.weightedHomogeneousComponent (colorComponentWeight m)
      (pureAColorTargetDegree D T b) p ∈ Submodule.span ℂ (finiteColorComponentRows m D T b) := by
  classical
  obtain ⟨q,hq,rfl⟩ := hp
  have hg := actual_product_color_graded m q
  by_cases hn : Finsupp.weight (colorComponentWeight m) q.2 + orbitSourceColorDegree m q.1 =
      pureAColorTargetDegree D T b
  · rw [hn] at hg
    rw [hg.weightedHomogeneousComponent_same]
    exact Submodule.subset_span ⟨q,⟨hq,hn⟩,rfl⟩
  · rw [hg.weightedHomogeneousComponent_ne _ (Ne.symm hn)]
    exact Submodule.zero_mem _

/-- Exact FINITE six-color source spanning for the original candidate ideal. -/
theorem candidate_color_component_eq_finite_span (m D T : ℕ) (b : Fin 3 → ℤ) :
    (AllM.candidateIdeal m).restrictScalars ℂ ⊓
      MvPolynomial.weightedHomogeneousSubmodule ℂ (colorComponentWeight m)
        (pureAColorTargetDegree D T b) =
      Submodule.span ℂ (finiteColorComponentRows m D T b) := by
  apply le_antisymm
  · intro p hp
    have hhom : p.IsWeightedHomogeneous (colorComponentWeight m)
        (pureAColorTargetDegree D T b) := hp.2
    have hbase : p ∈ Submodule.span ℂ (finiteComponentRows m D T) := by
      rw [← candidate_component_eq_finite_span]
      exact ⟨hp.1,color_component_forget m D T b p hhom⟩
    have himage := (Submodule.image_span_subset
      (MvPolynomial.weightedHomogeneousComponent (colorComponentWeight m)
        (pureAColorTargetDegree D T b))
      (finiteComponentRows m D T) (Submodule.span ℂ (finiteColorComponentRows m D T b))).mpr
        (fun q hq => finite_base_row_color_projection_mem m D T b q hq)
    have hh := himage ⟨p,hbase,rfl⟩
    rw [hhom.weightedHomogeneousComponent_same] at hh
    exact hh
  · apply Submodule.span_le.mpr
    rintro p ⟨q,hq,rfl⟩
    constructor
    · have hb : MvPolynomial.monomial q.2 (1 : ℂ) * orbitSourcePoly m q.1 ∈
          (AllM.candidateIdeal m).restrictScalars ℂ ⊓
            MvPolynomial.weightedHomogeneousSubmodule ℂ (componentWeight m)
              (pureATargetDegree D T) := by
        rw [candidate_component_eq_finite_span]
        exact Submodule.subset_span ⟨q,hq.1,rfl⟩
      exact hb.1
    · have hg := actual_product_color_graded m q
      rw [hq.2] at hg
      exact hg

/-- The stored quintic physical-weight slice has an actual finite original-row span. -/
theorem candidate_quintic_color_component_eq_finite_span (m : ℕ) :
    (AllM.candidateIdeal m).restrictScalars ℂ ⊓
      MvPolynomial.weightedHomogeneousSubmodule ℂ (colorComponentWeight m) (quinticColorDegree m) =
      Submodule.span ℂ (finiteColorComponentRows m 5 (2*m-3) (fun _ => 2)) :=
  candidate_color_component_eq_finite_span m 5 (2*m-3) (fun _ => 2)

theorem candidate_quintic_physical_mem_iff_finite_span (m : ℕ) (p : Ring ℂ m) :
    (p ∈ AllM.candidateIdeal m ∧
      p.IsWeightedHomogeneous (modeWeight m (fun _ => 1) 0) 5 ∧
      p.IsWeightedHomogeneous (modeWeight m (fun _ => 0) 1) ((2*m-3 : ℕ) : ℤ) ∧
      p.IsWeightedHomogeneous (modeWeight m cWeight 0) 0 ∧
      ∀ d : Fin 3, p.IsWeightedHomogeneous (modeWeight m (physicalColorWeight d) 0) 1) ↔
        p ∈ Submodule.span ℂ (finiteColorComponentRows m 5 (2*m-3) (fun _ => 2)) := by
  rw [← candidate_quintic_color_component_eq_finite_span]
  change (_ ∧ _) ↔ _ ∧ _
  exact and_congr_right (fun _ => (quintic_color_component_iff m p).symm)

end
#print axioms finiteColorComponentRows_finite
#print axioms actual_product_color_projection
#print axioms candidate_color_component_eq_finite_span
#print axioms candidate_quintic_physical_mem_iff_finite_span
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
