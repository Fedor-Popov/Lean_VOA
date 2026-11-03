import VOA.Classification.COne.OrbPos2Sectors

/-!
# The shifted energy operator on the actual rank-one lattice-module carrier

This file constructs an endomorphism, not a twisted vertex operator map.
Its unshifted term is the conformal mode of `LatMod.latticeModule`.
The charge operator is defined explicitly on the tensor-product momentum factor.
All eigenvalues, rather than only distinguished eigenvectors, are controlled.
-/

namespace VOA.Classification.COne.OrbPos3
open VOA VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet VOA.HeisenbergN OrbPos2 LatMod
open scoped TensorProduct

/-- Inversion of the energy shift requires shifting the Cartan zero mode too.
This is an operator identity, not an inverse-twist theorem for vertex fields. -/
theorem shiftedL0_inverse {M : Type*} [AddCommGroup M] [Module ℂ M]
    (L H : Module.End ℂ M) (t : ℂ) :
    shiftedL0 (shiftedL0 L H t) (H - (2 * t) • LinearMap.id) (-t) = L := by
  unfold shiftedL0
  module

noncomputable abbrev Space := LatModuleGen (latP 1)

/-- Root charge on the momentum factor of the coset labelled by `j`. -/
noncomputable def chargeMomentum (j : ℤ) : Module.End ℂ ((latP 1).carrier →₀ ℂ) :=
  Finsupp.linearCombination ℂ (fun k : ℤ => (2 * (k : ℂ) + j) • eGen (latP 1) k)

/-- The diagonal root-charge operator on the actual lattice carrier. -/
noncomputable def charge (j : ℤ) : Module.End ℂ Space :=
  TensorProduct.map LinearMap.id (chargeMomentum j)

theorem charge_latState (j k : ℤ) (p : FockN (rank (latP 1))) :
    charge j (latStateGen (latP 1) p k) =
      (2 * (k : ℂ) + j) • latStateGen (latP 1) p k := by
  simp only [charge, latStateGen, TensorProduct.map_tmul, LinearMap.id_apply,
    chargeMomentum, eGen, Finsupp.linearCombination_single, one_smul,
    TensorProduct.tmul_smul]

/-- The diagonal charge is the actual root Heisenberg zero mode, with the
root normalized to have squared length two. -/
theorem charge_eq_root_zeroMode (j : ℤ) :
    charge j = chargeCoord (latP 1) (1 : ℤ) (a0 1) •
      mode ((latticeModule 1 le_rfl j).YM (hVec (latP 1) (a0 1))) 0 := by
  refine LinearMap.ext_on_range (latStateGen_span (latP 1)) fun ⟨p, k⟩ => ?_
  rw [charge_latState, LinearMap.smul_apply, latticeModule_zeroMode, smul_smul,
    mul_comm _ (chi 1 j k), chi_mul 1 le_rfl j k]
  norm_num

/-- The actual ordinary-module conformal mode, with the proposed Li energy shift. -/
noncomputable def energyOperator (n : ℕ) (a j : ℤ) : Module.End ℂ Space :=
  shiftedL0 (mode ((latticeModule 1 le_rfl j).YM (V2m 1 le_rfl).conformalVector) 1)
    (charge j) ((a : ℂ) / (2 * n))

theorem energyOperator_latState (n : ℕ) (a j k : ℤ) {r : ℕ}
    {p : FockN (rank (latP 1))} (hp : p ∈ gradingWN (rank (latP 1)) r) :
    energyOperator n a j (latStateGen (latP 1) p k) =
      (innerEnergy n a j k r : ℂ) • latStateGen (latP 1) p k := by
  have hL := latticeModule_L0 1 le_rfl j hp k
  have hL' : mode ((latticeModule 1 le_rfl j).YM (V2m 1 le_rfl).conformalVector) 1
      (latStateGen (latP 1) p k) =
      (((k : ℂ) + j / 2) ^ 2 + r) • latStateGen (latP 1) p k := by
    rw [hL]
    congr 1
    push_cast
    ring
  have hH : charge j (latStateGen (latP 1) p k) =
      (2 * ((k : ℂ) + j / 2)) • latStateGen (latP 1) p k := by
    rw [charge_latState]
    congr 1
    ring
  rw [energyOperator, shiftedL0_eigen _ _ _ _ _ _ hL' hH]
  congr 1
  simp only [innerEnergy]
  push_cast
  rfl

/-- Every nonzero eigenspace of the shifted operator has the predicted energy.
This uses the spanning bigrading, so it also controls arbitrary linear combinations. -/
theorem energyOperator_spectrum (n : ℕ) (a j : ℤ) {α : ℂ}
    (hα : Module.End.eigenspace (energyOperator n a j) α ≠ ⊥) :
    ∃ (k : ℤ) (r : ℕ), α = (innerEnergy n a j k r : ℂ) := by
  classical
  let S : Set ℂ := {α | ∃ (k : ℤ) (r : ℕ), α = (innerEnergy n a j k r : ℂ)}
  have hs : (⨆ β ∈ S, Module.End.eigenspace (energyOperator n a j) β) = ⊤ := by
    rw [eq_top_iff, ← bigradα_iSup_eq_top (latP 1)]
    refine iSup_le fun ⟨w, k⟩ => ?_
    by_cases hw : 0 ≤ w
    · apply le_trans ?_ (le_iSup_of_le (innerEnergy n a j k w.toNat : ℂ)
        (le_iSup_of_le (show (innerEnergy n a j k w.toNat : ℂ) ∈ S from
          ⟨k, w.toNat, rfl⟩) le_rfl))
      rintro x ⟨p, hp, rfl⟩
      rw [gradingZN_of_nonneg hw] at hp
      rw [Module.End.mem_eigenspace_iff]
      exact energyOperator_latState n a j k hp
    · rw [bigradα_eq_bot_of_neg (latP 1) k (lt_of_not_ge hw)]
      exact bot_le
  by_contra hn
  have hn' : α ∉ S := hn
  have hd := (Module.End.eigenspaces_iSupIndep (energyOperator n a j)).disjoint_biSup hn'
  rw [hs, disjoint_top] at hd
  exact hα hd

/-- The zero-translate, zero-oscillator state realizes the proposed lowest energy. -/
theorem energyOperator_ground (n : ℕ) (a j : ℤ) :
    Module.End.eigenspace (energyOperator n a j) (innerEnergy n a j 0 0 : ℂ) ≠ ⊥ := by
  intro he
  have hm : latVacuumGen (latP 1) ∈
      Module.End.eigenspace (energyOperator n a j) (innerEnergy n a j 0 0 : ℂ) := by
    rw [Module.End.mem_eigenspace_iff]
    exact energyOperator_latState n a j 0 (vacuumN_mem_gradingWN _)
  rw [he, Submodule.mem_bot] at hm
  exact (V2m_isSimple 1 le_rfl).vacuum_ne_zero hm

/-- Exact attained minimum for the two normalized charge cosets. -/
theorem energyOperator_lowest {n : ℕ} (hn : 0 < n) {a ε : ℤ}
    (ha : 0 ≤ a) (han : a ≤ n) (hε : ε = 0 ∨ ε = 1) :
    Module.End.eigenspace (energyOperator n a ε) (innerEnergy n a ε 0 0 : ℂ) ≠ ⊥ ∧
      ∀ α : ℂ, Module.End.eigenspace (energyOperator n a ε) α ≠ ⊥ →
        (innerEnergy n a ε 0 0 : ℝ) ≤ α.re := by
  refine ⟨energyOperator_ground n a ε, ?_⟩
  intro α hα
  obtain ⟨k, r, rfl⟩ := energyOperator_spectrum n a ε hα
  simp only [Complex.ratCast_re]
  exact_mod_cast innerEnergy_minimum hn ha han hε k r

/-- Normalize any integral coset label, not just labels chosen in advance as zero or one. -/
theorem innerEnergy_normalize (n : ℕ) (a j k : ℤ) (r : ℕ) :
    innerEnergy n a j k r = innerEnergy n a (j % 2) (k + j / 2) r := by
  have hj : j = j % 2 + 2 * (j / 2) := (Int.emod_add_mul_ediv j 2).symm
  have hjQ : (j : ℚ) = (j % 2 : ℤ) + 2 * (j / 2 : ℤ) := by exact_mod_cast hj
  unfold innerEnergy
  push_cast
  rw [hjQ]
  ring

end VOA.Classification.COne.OrbPos3
