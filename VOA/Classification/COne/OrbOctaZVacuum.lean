import VOA.Classification.COne.OrbOctaZCandidate
import VOA.Classification.COne.OrbB5Vacuum

/-! # The four remaining octahedral vacuum-fiber identities

The exact additional sufficient input is that each of the four nonvacuum
seed classes is divisible by the conformal class in Zhu's algebra. This
forces the entire weight-zero bottom action to be the vacuum character.
The reduction needs neither rationality nor a classification of modules.
The four divisibilities and the degree-25 conformal identity remain open.
-/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbOctaZ
open VOA Polynomial OrbC2b OrbOcta OrbZhu OrbB5 OrbPos PlusUnitary

private theorem octa_simple : W.IsSimple :=
  @exceptionalOrbifold_isSimple octa
    (Finite.of_equiv (Equiv.Perm (Fin 4)) octa_group.some.symm.toEquiv)

/-- OPEN: four concrete divisibilities in the intrinsic octahedral Zhu algebra. -/
def OctahedralVacuumFiber : Prop :=
  ∀ i : Fin 4, ∃ z : A W, omegaL W z = mk W (octaSeeds i.succ)

/-- The explicit finite Zhu spanning family. -/
theorem zhu_towers25 :
    Submodule.span ℂ (Set.range fun p : (Σ _ : Fin 5, Fin 25) =>
      (omegaL W ^ (p.2 : ℕ)) (mk W (octaSeeds p.1))) = ⊤ :=
  span_towers_A_eq_top W octaSeeds (fun i => (seedWeight i : ℤ)) seeds_homogeneous
    (fun _ => 25) (fun _ => 25) towers25
    (fun i _ ha => pow_mem_towerSub W (mk W (octaSeeds i)) ha)

theorem seed_zeroBottom (hF : OctahedralVacuumFiber)
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule W M) (hl : IsLowestWeight N 0) (i : Fin 4) :
    actA N hl (mk W (octaSeeds i.succ)) = 0 := by
  obtain ⟨z, hz⟩ := hF i
  rw [← hz]
  have h := actA_omegaL_pow N hl 1 z
  simpa using h

private abbrev adj := adjointModule W
private theorem adj_low : IsLowestWeight adj 0 := isLowestWeight_adjoint W

/-- Every Zhu class acts by the same scalar on any zero bottom and the vacuum bottom. -/
theorem zeroBottom_scalar (hF : OctahedralVacuumFiber)
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule W M) (hl : IsLowestWeight N 0) (z : A W) :
    ∃ c : ℂ, actA N hl z = c • 1 ∧ actA adj (h := 0) adj_low z = c • 1 := by
  let S := pairedScalars (actA N hl) (actA adj (h := 0) adj_low)
    (1 : Module.End ℂ (N.weight 0)) (1 : Module.End ℂ (adj.weight 0))
  have hs (i : Fin 5) : mk W (octaSeeds i) ∈ S := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨1, by simpa only [one_smul] using actA_one N hl,
        by simpa only [one_smul] using actA_one adj adj_low⟩
    · exact ⟨0, by rw [seed_zeroBottom hF N hl j, zero_smul],
        by rw [seed_zeroBottom hF adj adj_low j, zero_smul]⟩
  have hp (n : ℕ) {a : A W} (ha : a ∈ S) : (omegaL W ^ n) a ∈ S := by
    obtain ⟨c, hc, hc'⟩ := ha
    exact ⟨(0 : ℂ) ^ n * c, by rw [actA_omegaL_pow, hc, smul_smul],
      by rw [actA_omegaL_pow, hc', smul_smul]⟩
  have htop : (⊤ : Submodule ℂ (A W)) ≤ S := by
    rw [← zhu_towers25]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, a⟩, rfl⟩
    exact hp a (hs i)
  exact htop (Submodule.mem_top : z ∈ ⊤)

set_option synthInstance.maxHeartbeats 100000 in
-- Nested orbifold carriers make the scalar-zero instance expensive.
/-- Vacuum uniqueness from four explicit seed identities, without rationality. -/
theorem vacuum_of_lowest_zero (hF : OctahedralVacuumFiber)
    {M : Type} [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M)
    (hi : N.IsIrreducible) (hl : IsLowestWeight N 0) (hne : N.weight 0 ≠ ⊥) :
    Nonempty (ModuleEquiv W N (adjointModule W)) := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  apply nonempty_moduleEquiv_adjoint_of_vacuumTop octa_simple N hi
    hl hx hx0
  intro k hk a ha
  obtain ⟨c, hc, hc'⟩ := zeroBottom_scalar hF N hl (mk W a)
  have hc0 : c = 0 := by
    have hh := congrArg (fun f : Module.End ℂ (adj.weight 0) =>
      (f ⟨W.vacuum, vacuum_mem_adjoint_weight W⟩).val) hc'
    change ((actA adj (h := 0) adj_low (mk W a)
      ⟨W.vacuum, vacuum_mem_adjoint_weight W⟩ : adj.weight 0) : _) = c • W.vacuum at hh
    rw [actA_mk_apply_coe, oMod_adjoint_vacuum W hk ha] at hh
    exact (smul_eq_zero.mp hh.symm).resolve_right
      octa_simple.vacuum_ne_zero
  have hh := congrArg (fun f : Module.End ℂ (N.weight 0) => (f ⟨x, hx⟩).val) hc
  change ((actA N hl (mk W a) ⟨x, hx⟩ : N.weight 0) : M) = c • x at hh
  rwa [actA_mk_apply_coe, hc0, zero_smul] at hh

/-- Four explicit degree-24 identities imply the vacuum-fiber condition. -/
theorem vacuumFiber_of_positive_annihilators
    (h : ∀ i : Fin 4,
      (aeval (omegaL W) positivePolynomial) (mk W (octaSeeds i.succ)) = 0) :
    OctahedralVacuumFiber := by
  have hc : IsCoprime (X - Polynomial.C (0 : ℂ)) positivePolynomial := by
    rw [(irreducible_X_sub_C _).coprime_iff_not_dvd, dvd_iff_isRoot]
    exact positivePolynomial_eval_zero_ne
  simp only [map_zero, sub_zero] at hc
  obtain ⟨a, b, hab⟩ := hc
  rw [mul_comm a X] at hab
  intro i
  refine ⟨(aeval (omegaL W) a) (mk W (octaSeeds i.succ)), ?_⟩
  have he := congrArg (fun P : ℂ[X] =>
    (aeval (omegaL W) P) (mk W (octaSeeds i.succ))) hab
  simpa only [map_add, map_mul, aeval_X, LinearMap.add_apply, Module.End.mul_apply,
    h i, map_zero, add_zero, map_one, Module.End.one_apply] using he

/-- Given the conformal identity, the four degree-24 identities are equivalent
    to the four divisibilities, so this is a finite certificate target. -/
theorem vacuumFiber_iff_positive_annihilators (hP : OctahedralConformalZhuRelation) :
    OctahedralVacuumFiber ↔ ∀ i : Fin 4,
      (aeval (omegaL W) positivePolynomial) (mk W (octaSeeds i.succ)) = 0 := by
  refine ⟨?_, vacuumFiber_of_positive_annihilators⟩
  intro hF i
  obtain ⟨z, hz⟩ := hF i
  rw [← hz]
  have he := congrArg (fun f : Module.End ℂ (A W) => f z) (candidate_annihilates hP)
  rw [candidatePolynomial, mul_comm X positivePolynomial] at he
  simpa only [map_mul, aeval_X, Module.End.mul_apply, LinearMap.zero_apply] using he

/-- The same finite certificate improves the dimension bound to 121. -/
theorem finrank_le_121_of_zhu_fiber
    (hP : OctahedralConformalZhuRelation) (hF : OctahedralVacuumFiber) :
    Module.finrank ℂ (A W) ≤ 121 := by
  have hs := (vacuumFiber_iff_positive_annihilators hP).mp hF
  let heights : Fin 5 → ℕ := Fin.cases 25 (fun _ => 24)
  have hm : ∀ i, ∀ a < 25,
      (omegaL W ^ a) (mk W (octaSeeds i)) ∈ towerSub W (mk W (octaSeeds i)) (heights i) := by
    intro i a _
    refine Fin.cases ?_ (fun j => ?_) i
    · have h := pow_mem_towerSub_of_monic W (mk W W.vacuum) candidatePolynomial_monic hP a
      simpa only [candidatePolynomial_natDegree] using h
    · have h := pow_mem_towerSub_of_monic W (mk W (octaSeeds j.succ))
        positivePolynomial_monic (hs j) a
      simpa only [positivePolynomial_natDegree] using h
  have hd := (finrank_A_le_of_towers W octaSeeds (fun i => (seedWeight i : ℤ))
    seeds_homogeneous (fun _ => 25) heights towers25 hm).2
  simpa [heights, Fin.sum_univ_succ] using hd

/-- The complete direct Zhu route, with its two unproved inputs visible. -/
theorem octa_pseudoUnitary_of_zhu_fiber
    (hP : OctahedralConformalZhuRelation) (hF : OctahedralVacuumFiber) :
    PseudoUnitary (orbifoldVOA octa) := by
  apply (pseudoUnitary_iff_positiveLowestWeights W).mpr
  intro M _ _ N hi hn h hl hne
  rcases lowestWeight_zero_or_gap hP N hl hne with rfl | hh
  · obtain ⟨e⟩ := vacuum_of_lowest_zero hF N hi hl hne
    exact (hn.false e).elim
  · linarith

end VOA.Classification.COne.OrbOctaZ
