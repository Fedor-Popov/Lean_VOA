import VOA.Moonshine.MoonshineCNReconstruction

/-!
# Complex-frame lattice construction: StateFields

Structural adaptation of `LatticeGenVOAInstance` using a complex bilinear
frame. The carrier, formal-distribution conventions and finite-support proofs
are preserved. No positive-definiteness hypothesis is introduced.
-/

set_option maxHeartbeats 1600000
set_option linter.style.longLine false

namespace VOA.Moonshine.ConwayNorton

open scoped BigOperators TensorProduct
open Module (End)
open IntegralLattice HeisenbergN LatGen Reconstruction

variable {L : IntegralLattice} (F : ComplexLatticeFrame L)

noncomputable def frameStateField (hEven : L.Even)  :
    LatModuleGen L →ₗ[ℂ] FormalDist (End ℂ (LatModuleGen L)) :=
  (frameStateField_exists F hEven).choose


theorem frameStateField_word (hEven : L.Even)  (l : List (ℕ × Fin (rank L)))
    (α : L.carrier) :
    frameStateField F hEven (frameWordState L l α) = frameWordField F l α :=
  (frameStateField_exists F hEven).choose_spec.1 (l, α)


theorem frameStateField_isField (hEven : L.Even)  (u : LatModuleGen L) :
    IsField (frameStateField F hEven u) :=
  (frameStateField_exists F hEven).choose_spec.2.1 u


theorem frameStateField_local (hEven : L.Even)  (u v : LatModuleGen L) :
    Local (frameStateField F hEven u) (frameStateField F hEven v) :=
  (frameStateField_exists F hEven).choose_spec.2.2.1 u v


theorem frameStateField_cre0 (hEven : L.Even)  (u : LatModuleGen L) :
    (frameStateField F hEven u) 0 (latVacuumGen L) = u :=
  (frameStateField_exists F hEven).choose_spec.2.2.2.1 u


theorem frameStateField_creneg (hEven : L.Even)  (u : LatModuleGen L) {q : ℤ} (hq : q < 0) :
    (frameStateField F hEven u) q (latVacuumGen L) = 0 :=
  (frameStateField_exists F hEven).choose_spec.2.2.2.2.1 u q hq


theorem frameStateField_DCov (hEven : L.Even)  (u : LatModuleGen L) :
    Reconstruction.DCovariant (frameTranslation F) (frameStateField F hEven u) :=
  (frameStateField_exists F hEven).choose_spec.2.2.2.2.2 u


theorem creationVariable_zero_charge (m : ℕ) : creationVariable F 0 m = 0 := by
  simp [creationVariable]


theorem creationCoefficient_zero_charge (N : ℕ) : creationCoefficient F 0 (N + 1) = 0 := by
  have h := creationCoefficient_recursion_sum F 0 (N + 1)
  rw [Finset.sum_eq_zero (fun m _ => by rw [creationVariable_zero_charge, zero_mul])] at h
  have h2 : ((N + 1 : ℕ) : ℂ) • creationCoefficient F 0 (N + 1) = 0 := h.symm
  rw [smul_eq_zero] at h2
  rcases h2 with h0 | h0
  · exact absurd h0 (by exact_mod_cast Nat.succ_ne_zero N)
  · exact h0


theorem creationField_zero_charge (t : ℤ) :
    creationField F 0 t = if t = 0 then (LinearMap.id : End ℂ (FockN (rank L))) else 0 := by
  rw [creationField_apply]
  by_cases ht : t = 0
  · rw [if_pos ht, if_pos (by omega : (0 : ℤ) ≤ t), ht, show (0 : ℤ).toNat = 0 from rfl,
      creationOperator, creationCoefficient_zero, LinearMap.mulLeft_one]
  · by_cases ht0 : 0 ≤ t
    · rw [if_pos ht0, if_neg ht,
        show t.toNat = (t.toNat - 1) + 1 from by omega,
        creationOperator, creationCoefficient_zero_charge,
        show LinearMap.mulLeft ℂ (0 : FockN (rank L)) = 0 from by
          refine LinearMap.ext fun p => ?_
          rw [LinearMap.mulLeft_apply, zero_mul, LinearMap.zero_apply]]
    · rw [if_neg ht0, if_neg ht]


theorem annihilationField_zero_charge (t : ℤ) :
    annihilationField F 0 t = if t = 0 then (LinearMap.id : End ℂ (FockN (rank L))) else 0 := by
  rw [annihilationField_eq_annihilationCoefficientZ, annihilationCoefficientZ]
  by_cases ht : t = 0
  · rw [ht, show -(0 : ℤ) = 0 from rfl, if_pos (le_refl 0), show (0 : ℤ).toNat = 0 from rfl,
      annihilationCoefficient, if_pos rfl]
  · by_cases ht0 : 0 ≤ -t
    · rw [if_pos ht0, if_neg ht, show (-t).toNat = ((-t).toNat - 1) + 1 from by omega, annihilationCoefficient_succ,
        Finset.sum_eq_zero (fun m _ => by
          rw [show frameOscillator F 0 ((m : ℤ) + 1) = 0 from by
            rw [frameOscillator_eq_sum]; exact Finset.sum_eq_zero fun a _ => by rw [frameCoordinate_zero, zero_smul],
            neg_zero, LinearMap.zero_comp]), smul_zero]
    · rw [if_neg ht0, if_neg ht]


theorem dressingField_zero_charge (t : ℤ) (x : FockN (rank L)) :
    dressingField F 0 t x = if t = 0 then x else 0 := by
  rw [dressingField_apply_conv]
  by_cases ht : t = 0
  · rw [if_pos ht, ht, finsum_eq_single _ 0 (fun m hm => by
      rw [creationField_zero_charge, if_neg hm, LinearMap.zero_apply])]
    rw [creationField_zero_charge, if_pos rfl, annihilationField_zero_charge,
      show (0 : ℤ) - 0 = 0 from rfl, if_pos rfl]; rfl
  · rw [if_neg ht, finsum_eq_zero_of_forall_eq_zero fun m => ?_]
    by_cases hm : m = 0
    · rw [hm, annihilationField_zero_charge, show t - 0 = t from by ring, if_neg ht,
        LinearMap.zero_apply, map_zero]
    · rw [creationField_zero_charge, if_neg hm, LinearMap.zero_apply]


theorem canonicalChargedField_zero_apply (t : ℤ) (y : LatModuleGen L) :
    canonicalChargedField F 0 t y = if t = 0 then y else 0 := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; split_ifs <;> rfl
  | add y1 y2 h1 h2 =>
      rw [map_add, h1, h2]; split_ifs <;> simp
  | tmul p g =>
      induction g using Finsupp.induction_linear with
      | zero => erw [TensorProduct.tmul_zero, map_zero]; split_ifs <;> rfl
      | add g1 g2 h1 h2 => erw [TensorProduct.tmul_add, map_add, h1, h2]; split_ifs <;> simp
      | single β a =>
          rw [(Finsupp.smul_single_one β a).symm,
            show (Finsupp.single β (1 : ℂ) : L.carrier →₀ ℂ) = eGen L β from rfl]
          erw [TensorProduct.tmul_smul, map_smul,
            show p ⊗ₜ[ℂ] eGen L β = latStateGen L p β from rfl, canonicalChargedField_tmul,
            latticeCocycle_zero_left, one_smul, show L.form 0 β = 0 from by simp, sub_zero,
            latStateGen, dressingField_zero_charge, zero_add]
          split_ifs with ht
          · rfl
          · rw [TensorProduct.zero_tmul, smul_zero]


theorem canonicalChargedField_zero_eq_one :
    (canonicalChargedField F 0 : FormalDist (End ℂ (LatModuleGen L))) = (1 : (End ℂ (LatModuleGen L))⟦z^±⟧) := by
  funext t
  refine LinearMap.ext fun y => ?_
  rw [canonicalChargedField_zero_apply]
  rw [FormalDist.one_apply]
  split_ifs with ht
  · rw [Module.End.one_apply]
  · rw [LinearMap.zero_apply]


theorem frameStateField_vacuum (hEven : L.Even)  :
    frameStateField F hEven (latVacuumGen L) = (1 : (End ℂ (LatModuleGen L))⟦z^±⟧) := by
  rw [show latVacuumGen L = frameWordState L [] 0 from by
      rw [frameWordState_nil, latChargeGen, latVacuumGen, latStateGen],
    frameStateField_word, frameWordField_nil, canonicalChargedField_zero_eq_one]


theorem frameStateField_creation (hEven : L.Even)  (u : LatModuleGen L) :
    mode (frameStateField F hEven u) (-1) (latVacuumGen L) = u
      ∧ ∀ n : ℤ, 0 ≤ n → mode (frameStateField F hEven u) n (latVacuumGen L) = 0 := by
  refine ⟨?_, fun n hn => ?_⟩
  · rw [mode_apply, show (-(-1 : ℤ) - 1) = 0 from by ring]; exact frameStateField_cre0 F hEven u
  · rw [mode_apply]; exact frameStateField_creneg F hEven u (by omega : -n - 1 < 0)


theorem frameStateField_regularity (hEven : L.Even)  (u v : LatModuleGen L) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → mode (frameStateField F hEven u) n v = 0 := by
  obtain ⟨Bnd, hB⟩ := frameStateField_isField F hEven u v
  refine ⟨-Bnd + 1, fun n hn => ?_⟩
  rw [mode_apply]; exact hB (-n - 1) (by omega)


end VOA.Moonshine.ConwayNorton
