import VOA.Classification.COne.OrbOctaZCSeed16

/-! The proved conformal relation, one proved positive seed relation, and the
exact three remaining seed relations for octahedral vacuum uniqueness. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbOctaZC
open VOA OrbOctaZ OrbZhu OrbOcta Polynomial

/-- Q24 annihilates the weight-sixteen seed in the original spanning family. -/
theorem q24_seed_one :
    aeval (omegaL W) positivePolynomial (mk W (octaSeeds 1)) = 0 := q24_seed16

/-- Only the weight-36, weight-81, and weight-144 seed identities remain. -/
theorem vacuumFiber_iff_three_Q24 :
    OctahedralVacuumFiber ↔ ∀ i : Fin 3,
      aeval (omegaL W) positivePolynomial (mk W (octaSeeds i.succ.succ)) = 0 := by
  rw [vacuumFiber_iff_Q24]
  constructor
  · intro h i; exact h i.succ
  · intro h i
    exact Fin.cases q24_seed_one (fun j => h j) i

/-- The proved seed relation improves the unconditional dimension bound to 124. -/
theorem octa_zhu_finrank_le_124 : Module.finrank ℂ (A W) ≤ 124 := by
  let heights : Fin 5 → ℕ := fun i => if i = 1 then 24 else 25
  have hm : ∀ i, ∀ a < 25,
      (omegaL W ^ a) (mk W (octaSeeds i)) ∈ towerSub W (mk W (octaSeeds i)) (heights i) := by
    intro i a ha
    by_cases hi : i = 1
    · subst i
      have h := pow_mem_towerSub_of_monic W (mk W (octaSeeds 1))
        positivePolynomial_monic q24_seed_one a
      simpa only [heights, if_pos rfl, positivePolynomial_natDegree] using h
    · simpa only [heights, if_neg hi] using pow_mem_towerSub W (mk W (octaSeeds i)) ha
  have hd := (finrank_A_le_of_towers W octaSeeds (fun i => (seedWeight i : ℤ))
    seeds_homogeneous (fun _ => 25) heights towers25 hm).2
  simpa [heights, Fin.sum_univ_succ] using hd

/-- The remaining three explicit certificates suffice without rationality. -/
theorem octa_pseudoUnitary_of_three_Q24
    (h : ∀ i : Fin 3,
      aeval (omegaL W) positivePolynomial (mk W (octaSeeds i.succ.succ)) = 0) :
    PseudoUnitary (orbifoldVOA OrbC2b.octa) :=
  octa_pseudoUnitary_of_vacuumFiber (vacuumFiber_iff_three_Q24.mpr h)

end VOA.Classification.COne.OrbOctaZC
