import VOA.Moonshine.MoonshineCNMatterNilpotence
import VOA.Moonshine.MoonshineCNNearAdjointClosure
import VOA.Moonshine.MoonshineCNTensorGeneratorAdjoint
import VOA.Moonshine.MoonshineCNMonsterPairing

/-! Concrete matter opposite modes, their exact cutoff, and tensor generation.
Lie invariance is asserted only under the displayed opposite-adjoint hypothesis. -/

noncomputable section
namespace VOA.Moonshine.ConwayNorton

open AutMonster IntegralLattice LatGen
open scoped TensorProduct BigOperators

def moonshineMatterOppositeModes (n : ℤ) :
    moonshineMatterSpace →ₗ[ℂ] Module.End ℂ moonshineMatterSpace :=
  moonshineMatterNearVOA.oppositeModes moonshineMatterVirasoroOne_locallyNilpotent n

/-- The actual FHL transform uses matter/oscillator level, not total weight. -/
theorem moonshineMatterOppositeModes_charge_cutoff (α : lorentzianLattice.carrier)
    {N : ℤ} {u : moonshineMatterSpace} (hu : u ∈ moonshineMatterNearVOA.grading N)
    (hα : u ∈ moonshineMatterMomentum α) (n : ℤ) :
    moonshineMatterOppositeModes n u = (-1 : ℂ) ^ N •
      ∑ j ∈ Finset.range ((N - LatGen.halfNorm lorentzianLattice α).toNat + 1),
        ((j.factorial : ℂ)⁻¹) • mode (moonshineMatterNearVOA.Y
          ((moonshineMatterNearVOA.L 1 ^ j) u)) (2 * N - n - 2 - (j : ℤ)) := by
  rw [moonshineMatterOppositeModes,
    moonshineMatterNearVOA.oppositeModes_homogeneous _ hu]
  exact moonshineMatterNearVOA.oppositeModeAtWeight_eq_sum N n _
    (moonshineMatterVirasoroOne_cutoff α hu hα)

theorem moonshineMatterOppositeModes_primary
    (u : moonshineMatterNearVOA.primaryWeightOne) :
    moonshineMatterOppositeModes 0 u = -mode (moonshineMatterNearVOA.Y u) 0 := by
  apply moonshineMatterNearVOA.oppositeModes_primary
  · rw [moonshineMatterNearVOA.grading_eq_virasoroZero_eigenspace,
      Module.End.mem_eigenspace_iff, Int.cast_one, one_smul]
    exact u.property.1
  · exact u.property.2 1 (by norm_num)

/-- Charges, currents and the embedded Vnat factor generate the actual tensor algebra. -/
theorem moonshineMatter_generated_by_tensor_generators (S : Submodule ℂ moonshineMatterSpace)
    (hVnat : ∀ a : Vnat, a ⊗ₜ[ℂ] lorentzianNearVOA.vacuum ∈ S)
    (hCharge : ∀ α, VnatVOA.vacuum ⊗ₜ[ℂ] latChargeGen lorentzianLattice α ∈ S)
    (hCurrent : ∀ a, VnatVOA.vacuum ⊗ₜ[ℂ]
      frameWordState lorentzianLattice [(0, a)] 0 ∈ S)
    (hClosed : ∀ u ∈ S, ∀ v ∈ S, ∀ n : ℤ,
      mode (moonshineMatterNearVOA.Y u) n v ∈ S) : S = ⊤ := by
  let T := S.comap (TensorProduct.mk ℂ Vnat LorentzianFockSpace VnatVOA.vacuum)
  have hT : T = ⊤ := frameStateField_generated_by_charges_currents
    lorentzianComplexFrame lorentzian_even T hCharge hCurrent (by
      intro u hu v hv n
      have h := hClosed _ hu _ hv n
      change mode (moonshineMatterNearVOA.Y (VnatVOA.vacuum ⊗ₜ[ℂ] u)) n
        (VnatVOA.vacuum ⊗ₜ[ℂ] v) ∈ S at h
      rw [moonshineMatter_latticeGenerator_mode, LinearMap.lTensor_tmul] at h
      exact h)
  have hL (b : LorentzianFockSpace) : VnatVOA.vacuum ⊗ₜ[ℂ] b ∈ S := by
    change b ∈ T
    rw [hT]
    trivial
  apply top_unique
  intro t ht
  clear ht
  induction t using TensorProduct.induction_on with
  | zero => exact S.zero_mem
  | add t t' ht ht' => exact S.add_mem ht ht'
  | tmul a b =>
      have h := hClosed _ (hVnat a) _ (hL b) (-1)
      rw [moonshineMatter_vnatGenerator_mode, LinearMap.rTensor_tmul,
        (VnatVOA.creation a).1] at h
      exact h

/-- Specialization to primaries and the descended form. The FHL hypothesis is explicit. -/
theorem monsterLieBilinearForm_invariant_of_oppositeAdjoint
    (hAdj : ∀ (a : moonshineMatterNearVOA.primaryWeightOne) (b c : moonshineMatterSpace),
      moonshineMatterForm (mode (moonshineMatterNearVOA.Y a) 0 b) c =
        moonshineMatterForm b (moonshineMatterOppositeModes 0 a c))
    (u v w : monsterLieAlgebra) :
    monsterLieBilinearForm ⁅u, v⁆ w = monsterLieBilinearForm u ⁅v, w⁆ := by
  apply monsterLieBilinearForm_invariant_of_primaryAdjoint _ u v w
  intro a b c
  have h := hAdj a b c
  rw [moonshineMatterOppositeModes_primary, LinearMap.neg_apply, map_neg] at h
  exact h

end VOA.Moonshine.ConwayNorton
