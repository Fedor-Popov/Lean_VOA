import VOA.Moonshine.MoonshineCNChargedFields
import VOA.Examples.LatticeGenGrading
import Mathlib.Order.CompactlyGenerated.Basic

/-!
# Internal weight grading without a positivity assumption

The Fock-weight/charge decomposition is already internal. Coarsening along
`(w, α) ↦ w + (α,α)/2` preserves independence even when the fibers are infinite.
The weight-zero space of the hyperbolic lattice is infinite-dimensional.
-/

namespace VOA.Moonshine.ConwayNorton

open scoped BigOperators TensorProduct Classical
open IntegralLattice HeisenbergN LatGen

/-- The existing lattice weight spaces are independent without positivity. -/
theorem latticeWeightGrading_independent (L : IntegralLattice) :
    iSupIndep (gradingLatGen L) := by
  rw [iSupIndep_def]
  intro k
  rw [gradingLatGen_eq_biSup L k, iSup_ne_gradingLatGen_eq_biSup L k]
  apply (bigradα_iSupIndep L).disjoint_biSup_biSup
  rw [Set.disjoint_left]
  exact fun _ hp hn => hn hp

/-- Internal integer grading, including indefinite lattices and infinite fibers. -/
theorem latticeWeightGrading_isInternal (L : IntegralLattice) :
    DirectSum.IsInternal (gradingLatGen L) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (latticeWeightGrading_independent L) (gradingLatGen_iSup_eq_top L)

/-- Negative oscillator weights vanish, with no restriction on lattice energy. -/
theorem latticeWeightGrading_eq_positiveFiber (L : IntegralLattice) (k : ℤ) :
    gradingLatGen L k = ⨆ p ∈ fiberPosGen L k, bigradα L p := by
  rw [gradingLatGen_eq_biSup L k]
  apply le_antisymm
  · refine iSup_le (fun p => iSup_le (fun hp => ?_))
    by_cases hpw : 0 ≤ p.1
    · exact le_biSup (bigradα L) ⟨hp, hpw⟩
    · rw [show bigradα L p = ⊥ from bigradα_eq_bot_of_neg L p.2 (by omega)]
      exact bot_le
  · exact iSup_le (fun p => iSup_le (fun hp => le_biSup (bigradα L) hp.1))

noncomputable def lorentzianWeightGrading : ℤ → Submodule ℂ LorentzianFockSpace :=
  gradingLatGen lorentzianLattice

theorem lorentzianWeightGrading_isInternal : DirectSum.IsInternal lorentzianWeightGrading :=
  latticeWeightGrading_isInternal lorentzianLattice

theorem lorentzian_halfNorm (α : lorentzianLattice.carrier) :
    halfNorm lorentzianLattice α = lorentzianEnergy α := by
  have h := two_halfNorm lorentzianLattice lorentzian_even α
  have he := lorentzianEnergy_half_norm α
  omega

theorem lorentzianChargeState_mem_weight (α : lorentzianLattice.carrier) :
    lorentzianChargeState α ∈ lorentzianWeightGrading (lorentzianEnergy α) := by
  have h := bigradα_le_gradingLatGen lorentzianLattice 0 α
    (show lorentzianChargeState α ∈ bigradα lorentzianLattice (0, α) from
      ⟨vacuumN _, by simpa only [HeisenbergN.gradingZN_of_nonneg (le_refl 0)] using
        vacuumN_mem_gradingWN (rank lorentzianLattice), rfl⟩)
  simpa only [zero_add, lorentzian_halfNorm] using h

theorem lorentzianWeightGrading_not_bounded_below :
    ¬ ∃ N : ℤ, ∀ n : ℤ, n < N → lorentzianWeightGrading n = ⊥ :=
  lorentzian_grading_not_bounded_below _ lorentzianChargeState_mem_weight

theorem lorentzianChargeCoefficient_charge_eq (α β : lorentzianLattice.carrier) :
    lorentzianChargeCoefficient α (lorentzianChargeState β) = if β = α then 1 else 0 := by
  classical
  simp [lorentzianChargeCoefficient, lorentzianChargeState, latChargeGen,
    latStateGen, eGen, vacuumN, Finsupp.single_apply]

/-- Infinitely many linearly independent isotropic charged ground states. -/
theorem lorentzianIsotropicChargeStates_independent :
    LinearIndependent ℂ (fun i : ℤ => lorentzianChargeState ![i, 0]) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  have hval : ∀ j : ℤ, lorentzianChargeCoefficient ![i, 0]
      (lorentzianChargeState ![j, 0]) = if j = i then 1 else 0 := by
    intro j
    rw [lorentzianChargeCoefficient_charge_eq]
    split_ifs with hvec hji hji
    · rfl
    · exact (hji (congrFun hvec 0)).elim
    · subst j
      exact (hvec rfl).elim
    · rfl
  have hc := congrArg (lorentzianChargeCoefficient ![i, 0]) hg
  simp only [map_sum, map_smul, map_zero, hval] at hc
  simpa [hi] using hc

/-- This is an actual obstruction to the finite-weight-space `VertexAlgebra`. -/
theorem lorentzianWeightZero_not_finiteDimensional :
    ¬ FiniteDimensional ℂ (lorentzianWeightGrading 0) := by
  intro hfinite
  letI := hfinite
  let v : ℤ → lorentzianWeightGrading 0 := fun i =>
    ⟨lorentzianChargeState ![i, 0], by
      simpa [lorentzianEnergy] using lorentzianChargeState_mem_weight ![i, 0]⟩
  have hv : LinearIndependent ℂ v :=
    LinearIndependent.of_comp (lorentzianWeightGrading 0).subtype
      lorentzianIsotropicChargeStates_independent
  exact Module.Finite.not_linearIndependent_of_infinite v hv

end VOA.Moonshine.ConwayNorton
