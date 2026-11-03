import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleComponentBounds
import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleShiftFinite
import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleOuterFinite
import Mathlib.Data.Finite.Prod

/-! Explicit finite indices for actual component rows. Every bound is a
concrete inequality/list cutoff, not a source-finiteness hypothesis. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

def boundedSeedIndices (m D T : ℕ) : Set (AllM.SeedIndex m) :=
  {j | j.val.2.1 ≤ D ∧ j.val.2.2 ≤ T}

theorem boundedSeedIndices_finite (m D T : ℕ) : (boundedSeedIndices m D T).Finite := by
  have hf : (Set.univ ×ˢ ({r : ℕ | r ≤ D} ×ˢ {s : ℕ | s ≤ T}) :
      Set (Bool × ℕ × ℕ)).Finite :=
    (Set.toFinite (Set.univ : Set Bool)).prod
      ((Set.finite_le_nat D).prod (Set.finite_le_nat T))
  have hp : ((fun j : AllM.SeedIndex m => j.val) ⁻¹'
      (Set.univ ×ˢ ({r : ℕ | r ≤ D} ×ˢ {s : ℕ | s ≤ T}))).Finite :=
    hf.preimage (by intro a _ b _ h; exact Subtype.ext h)
  apply hp.subset
  intro j hj
  exact ⟨Set.mem_univ _,hj⟩

/-- PBW degree at most D, using the proved constant-one first variable weight. -/
def boundedComponentMonomials (m D : ℕ) : Set ((Fin 9 × Fin m) →₀ ℕ) :=
  {e | Finsupp.weight (componentWeight m) e 0 ≤ (D : ℤ)}

theorem boundedComponentMonomials_finite (m D : ℕ) :
    (boundedComponentMonomials m D).Finite := by
  have hf : ({f : Fin 9 × Fin m → ℕ | ∀ x, f x ≤ D} :
      Set (Fin 9 × Fin m → ℕ)).Finite :=
    Set.Finite.pi' (fun _ => Set.finite_le_nat D)
  have hp : ((fun e : (Fin 9 × Fin m) →₀ ℕ => (e : Fin 9 × Fin m → ℕ)) ⁻¹'
      {f : Fin 9 × Fin m → ℕ | ∀ x, f x ≤ D}).Finite :=
    hf.preimage (by intro a _ b _ h; exact Finsupp.ext (congrFun h))
  apply hp.subset
  intro e he x
  have ht := component_term_le_weight m e 0 x
  have hx : componentWeight m x 0 = 1 := by simp [componentWeight,modeWeight]
  rw [hx,mul_one] at ht
  have hh : (e x : ℤ) ≤ D := le_trans ht he
  exact_mod_cast hh

def boundedOrbitSourceIndices (m D T : ℕ) : Set (OrbitSourceIndex m) :=
  {i | i.seed ∈ boundedSeedIndices m D T ∧
    i.shifts ∈ boundedShiftLists m T ∧
    i.outer ∈ boundedOuterLists m i.seed.val.2.1 i.seed.val.1}

theorem orbitSourceIndex_tuple_injective (m : ℕ) :
    Function.Injective (fun i : OrbitSourceIndex m => (i.seed,i.shifts,i.outer)) := by
  rintro ⟨j,s,o,h⟩ ⟨j',s',o',h'⟩ he
  simp only [Prod.mk.injEq] at he
  rcases he with ⟨rfl,rfl,rfl⟩
  rfl

theorem boundedOrbitSourceIndices_finite (m D T : ℕ) :
    (boundedOrbitSourceIndices m D T).Finite := by
  let u : Set (AllM.SeedIndex m × List ℕ × List (Fin 18 × ℕ)) :=
    ⋃ j ∈ boundedSeedIndices m D T,
      {j} ×ˢ (boundedShiftLists m T ×ˢ boundedOuterLists m j.val.2.1 j.val.1)
  have hu : u.Finite := (boundedSeedIndices_finite m D T).biUnion (fun j _ =>
    (Set.finite_singleton j).prod ((boundedShiftLists_finite m T).prod
      (boundedOuterLists_finite m j.val.2.1 j.val.1)))
  have hp : ((fun i : OrbitSourceIndex m => (i.seed,i.shifts,i.outer)) ⁻¹' u).Finite :=
    hu.preimage (by intro a _ b _ h; exact orbitSourceIndex_tuple_injective m h)
  apply hp.subset
  intro i hi
  exact Set.mem_iUnion.mpr ⟨i.seed,Set.mem_iUnion.mpr
    ⟨hi.1,⟨Set.mem_singleton _,hi.2.1,hi.2.2⟩⟩⟩

def boundedComponentPairs (m D T : ℕ) :
    Set (OrbitSourceIndex m × ((Fin 9 × Fin m) →₀ ℕ)) :=
  {p | p.1 ∈ boundedOrbitSourceIndices m D T ∧
    p.2 ∈ boundedComponentMonomials m D ∧
    Finsupp.weight (componentWeight m) p.2 + orbitSourceDegree m p.1 = pureATargetDegree D T}

theorem boundedComponentPairs_finite (m D T : ℕ) : (boundedComponentPairs m D T).Finite :=
  ((boundedOrbitSourceIndices_finite m D T).prod
    (boundedComponentMonomials_finite m D)).subset (fun _ hp => ⟨hp.1,hp.2.1⟩)

/-- Literal monomial multiples of bounded original source words, with exact grade. -/
def finiteComponentRows (m D T : ℕ) : Set (Ring ℂ m) :=
  (fun p => MvPolynomial.monomial p.2 (1 : ℂ) * orbitSourcePoly m p.1) ''
    boundedComponentPairs m D T

theorem finiteComponentRows_finite (m D T : ℕ) : (finiteComponentRows m D T).Finite :=
  (boundedComponentPairs_finite m D T).image _

end
#print axioms boundedSeedIndices_finite
#print axioms boundedComponentMonomials_finite
#print axioms boundedOrbitSourceIndices_finite
#print axioms finiteComponentRows_finite
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
