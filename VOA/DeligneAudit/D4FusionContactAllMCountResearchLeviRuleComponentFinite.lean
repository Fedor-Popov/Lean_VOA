import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleComponentFiniteIndices

/-! Exact finite source-product spanning for every pure-A homogeneous
component of the original candidate ideal. No rank or count premise. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

def sourceWithShifts (m : ℕ) (i : OrbitSourceIndex m) (v : List ℕ) : OrbitSourceIndex m :=
  ⟨i.seed,v,i.outer,i.branch⟩

theorem sourceWithShifts_degree (m : ℕ) (i : OrbitSourceIndex m) (v : List ℕ)
    (hv : v.sum = i.shifts.sum) :
    orbitSourceDegree m (sourceWithShifts m i v) = orbitSourceDegree m i := by
  simp only [orbitSourceDegree,sourceWithShifts,hv]

theorem orbitSource_shift_seed_nonzero (m : ℕ) (i : OrbitSourceIndex m)
    (hne : orbitSourcePoly m i ≠ 0) : shiftWord m i.shifts (monoSeed m i.seed) ≠ 0 := by
  intro hz
  apply hne
  change wordOp (representation ℂ m) i.outer
    (monoMap ℂ m (sourceColor i.seed.val.1) (shiftWord m i.shifts (monoSeed m i.seed))) = 0
  rw [hz,map_zero,wordOp_zero]

theorem orbitSource_shift_scalar (m : ℕ) (i : OrbitSourceIndex m) (v : List ℕ) (z : ℂ)
    (hz : shiftWord m i.shifts (monoSeed m i.seed) = z • shiftWord m v (monoSeed m i.seed)) :
    orbitSourcePoly m i = z • orbitSourcePoly m (sourceWithShifts m i v) := by
  change wordOp (representation ℂ m) i.outer
    (monoMap ℂ m (sourceColor i.seed.val.1) (shiftWord m i.shifts (monoSeed m i.seed))) = _
  rw [hz,map_smul,wordOp_smul]
  rfl

/-- Every nonzero matching source product is a scalar multiple of a row
from the explicitly bounded seed/shift/outer/multiplier index set. -/
theorem matching_product_finite_coverage (m D T : ℕ) (i : OrbitSourceIndex m)
    (e : (Fin 9 × Fin m) →₀ ℕ)
    (hmatch : Finsupp.weight (componentWeight m) e + orbitSourceDegree m i =
      pureATargetDegree D T)
    (hne : MvPolynomial.monomial e (1 : ℂ) * orbitSourcePoly m i ≠ 0) :
    ∃ (z : ℂ) (q : OrbitSourceIndex m × ((Fin 9 × Fin m) →₀ ℕ)),
      q ∈ boundedComponentPairs m D T ∧
      MvPolynomial.monomial e (1 : ℂ) * orbitSourcePoly m i =
        z • (MvPolynomial.monomial q.2 (1 : ℂ) * orbitSourcePoly m q.1) := by
  have hs : orbitSourcePoly m i ≠ 0 := right_ne_zero_of_mul hne
  have hcur := matching_source_current_bounds m D T i e hmatch
  obtain ⟨z,v,hv,hvsum,hscalar⟩ := shift_seed_bounded_coverage m T i.seed i.shifts hcur.2.1
    (orbitSource_shift_seed_nonzero m i hs)
  have hseed : i.seed ∈ boundedSeedIndices m D T :=
    ⟨matching_source_power_le m D T i e hmatch,hcur.1⟩
  have houter := sourceWord_outer_mem_bounded m i.seed i.shifts i.outer i.branch hs
  have hindex : sourceWithShifts m i v ∈ boundedOrbitSourceIndices m D T :=
    ⟨hseed,hv,houter⟩
  have hmono : e ∈ boundedComponentMonomials m D := by
    have hh := congrFun hmatch 0
    change Finsupp.weight (componentWeight m) e 0 + (i.seed.val.2.1 : ℤ) = (D : ℤ) at hh
    change Finsupp.weight (componentWeight m) e 0 ≤ (D : ℤ)
    omega
  have hmatch' : Finsupp.weight (componentWeight m) e +
      orbitSourceDegree m (sourceWithShifts m i v) = pureATargetDegree D T := by
    rw [sourceWithShifts_degree m i v hvsum]
    exact hmatch
  refine ⟨z,(sourceWithShifts m i v,e),⟨hindex,hmono,hmatch'⟩,?_⟩
  rw [orbitSource_shift_scalar m i v z hscalar,mul_smul_comm]

/-- Exact finite spanning of the original ideal component, at every cutoff
and every PBW/current budget. The row set's finiteness is separately proved. -/
theorem candidate_component_eq_finite_span (m D T : ℕ) :
    (AllM.candidateIdeal m).restrictScalars ℂ ⊓
      MvPolynomial.weightedHomogeneousSubmodule ℂ (componentWeight m) (pureATargetDegree D T) =
        Submodule.span ℂ (finiteComponentRows m D T) := by
  rw [candidate_component_eq_matching_span]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro p ⟨i,e,hmatch,rfl⟩
    by_cases hz : MvPolynomial.monomial e (1 : ℂ) * orbitSourcePoly m i = 0
    · rw [hz]
      exact Submodule.zero_mem _
    · obtain ⟨z,q,hq,he⟩ := matching_product_finite_coverage m D T i e hmatch hz
      rw [he]
      apply Submodule.smul_mem
      exact Submodule.subset_span ⟨q,hq,rfl⟩
  · apply Submodule.span_le.mpr
    rintro p ⟨⟨i,e⟩,hp,rfl⟩
    exact Submodule.subset_span ⟨i,e,hp.2.2,rfl⟩

end
#print axioms matching_product_finite_coverage
#print axioms finiteComponentRows_finite
#print axioms candidate_component_eq_finite_span
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
