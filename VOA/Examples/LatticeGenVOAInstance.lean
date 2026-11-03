/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenWordFields
import VOA.Core.VertexOperatorAlgebra

/-!
# The general even-lattice VOA instance — reconstruction-derived VA axioms

The all-states vertex map `YfullGen` and its accessors from `latYfullGen_of_locality`, plus the
reconstruction-derived VA axioms: VA2 (`YfullGen_vacuum`: `Y(|0⟩) = 1` via `Yeαvec 0 = 1`), VA3
(`YfullGen_creation`), VA5 (`YfullGen_regularity`).  Cross-charge lift of A₁'s `LatticeVOAInstance`.

All `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN Reconstruction

variable (L : IntegralLattice)

/-! ## §A  `YfullGen` and its accessors. -/

/-- The reconstructed lattice vertex map `YfullGen`. -/
noncomputable def YfullGen (hEven : L.Even) (hPos : L.PosDef) :
    LatModuleGen L →ₗ[ℂ] FormalDist (End ℂ (LatModuleGen L)) :=
  (latYfullGen_of_locality L hEven hPos).choose

theorem YfullGen_word (hEven : L.Even) (hPos : L.PosDef) (l : List (ℕ × Fin (rank L)))
    (α : L.carrier) :
    YfullGen L hEven hPos (wordStateLatGen L l α) = YwordLatGen L l α :=
  (latYfullGen_of_locality L hEven hPos).choose_spec.1 (l, α)

theorem YfullGen_isField (hEven : L.Even) (hPos : L.PosDef) (u : LatModuleGen L) :
    IsField (YfullGen L hEven hPos u) :=
  (latYfullGen_of_locality L hEven hPos).choose_spec.2.1 u

theorem YfullGen_local (hEven : L.Even) (hPos : L.PosDef) (u v : LatModuleGen L) :
    Local (YfullGen L hEven hPos u) (YfullGen L hEven hPos v) :=
  (latYfullGen_of_locality L hEven hPos).choose_spec.2.2.1 u v

theorem YfullGen_cre0 (hEven : L.Even) (hPos : L.PosDef) (u : LatModuleGen L) :
    (YfullGen L hEven hPos u) 0 (latVacuumGen L) = u :=
  (latYfullGen_of_locality L hEven hPos).choose_spec.2.2.2.1 u

theorem YfullGen_creneg (hEven : L.Even) (hPos : L.PosDef) (u : LatModuleGen L) {q : ℤ} (hq : q < 0) :
    (YfullGen L hEven hPos u) q (latVacuumGen L) = 0 :=
  (latYfullGen_of_locality L hEven hPos).choose_spec.2.2.2.2.1 u q hq

theorem YfullGen_DCov (hEven : L.Even) (hPos : L.PosDef) (u : LatModuleGen L) :
    Reconstruction.DCovariant (TrecGen L) (YfullGen L hEven hPos u) :=
  (latYfullGen_of_locality L hEven hPos).choose_spec.2.2.2.2.2 u

/-! ## §B  VA2 — the vacuum field is the unit (`Yeαvec 0 = 1`). -/

/-- The charge-`0` variable vanishes. -/
theorem vVar_zero_charge (m : ℕ) : vVar L 0 m = 0 := by
  rw [vVar]; refine Finset.sum_eq_zero fun a _ => ?_; rw [chargeCoord_zero, zero_smul]

/-- `vSchur 0 (N+1) = 0`. -/
theorem vSchur_zero_charge (N : ℕ) : vSchur L 0 (N + 1) = 0 := by
  have h := vSchur_recursion_sum L 0 (N + 1)
  rw [Finset.sum_eq_zero (fun m _ => by rw [vVar_zero_charge, zero_mul])] at h
  have h2 : ((N + 1 : ℕ) : ℂ) • vSchur L 0 (N + 1) = 0 := h.symm
  rw [smul_eq_zero] at h2
  rcases h2 with h0 | h0
  · exact absurd h0 (by exact_mod_cast Nat.succ_ne_zero N)
  · exact h0

/-- `E⁻(0)_t = if t = 0 then id else 0`. -/
theorem EminusVecField_zero_charge (t : ℤ) :
    EminusVecField L 0 t = if t = 0 then (LinearMap.id : End ℂ (FockN (rank L))) else 0 := by
  rw [EminusVecField_apply]
  by_cases ht : t = 0
  · rw [if_pos ht, if_pos (by omega : (0 : ℤ) ≤ t), ht, show (0 : ℤ).toNat = 0 from rfl,
      EminusVec, vSchur_zero, LinearMap.mulLeft_one]
  · by_cases ht0 : 0 ≤ t
    · rw [if_pos ht0, if_neg ht,
        show t.toNat = (t.toNat - 1) + 1 from by omega,
        EminusVec, vSchur_zero_charge,
        show LinearMap.mulLeft ℂ (0 : FockN (rank L)) = 0 from by
          refine LinearMap.ext fun p => ?_
          rw [LinearMap.mulLeft_apply, zero_mul, LinearMap.zero_apply]]
    · rw [if_neg ht0, if_neg ht]

/-- `E⁺(0)_t = if t = 0 then id else 0`. -/
theorem EplusVecField_zero_charge (t : ℤ) :
    EplusVecField L 0 t = if t = 0 then (LinearMap.id : End ℂ (FockN (rank L))) else 0 := by
  rw [EplusVecField_eq_aExpVecZ, aExpVecZ]
  by_cases ht : t = 0
  · rw [ht, show -(0 : ℤ) = 0 from rfl, if_pos (le_refl 0), show (0 : ℤ).toNat = 0 from rfl,
      aExpVec, if_pos rfl]
  · by_cases ht0 : 0 ≤ -t
    · rw [if_pos ht0, if_neg ht, show (-t).toNat = ((-t).toNat - 1) + 1 from by omega, aExpVec_succ,
        Finset.sum_eq_zero (fun m _ => by
          rw [show chargeOsc L 0 ((m : ℤ) + 1) = 0 from by
            rw [chargeOsc_eq_sum]; exact Finset.sum_eq_zero fun a _ => by rw [chargeCoord_zero, zero_smul],
            neg_zero, LinearMap.zero_comp]), smul_zero]
    · rw [if_neg ht0, if_neg ht]

/-- `EE(0)_t = if t = 0 then id else 0` (the neutral dressing). -/
theorem EEVec_zero_charge (t : ℤ) (x : FockN (rank L)) :
    EEVec L 0 t x = if t = 0 then x else 0 := by
  rw [EEVec_apply_conv]
  by_cases ht : t = 0
  · rw [if_pos ht, ht, finsum_eq_single _ 0 (fun m hm => by
      rw [EminusVecField_zero_charge, if_neg hm, LinearMap.zero_apply])]
    rw [EminusVecField_zero_charge, if_pos rfl, EplusVecField_zero_charge,
      show (0 : ℤ) - 0 = 0 from rfl, if_pos rfl]; rfl
  · rw [if_neg ht, finsum_eq_zero_of_forall_eq_zero fun m => ?_]
    by_cases hm : m = 0
    · rw [hm, EplusVecField_zero_charge, show t - 0 = t from by ring, if_neg ht,
        LinearMap.zero_apply, map_zero]
    · rw [EminusVecField_zero_charge, if_neg hm, LinearMap.zero_apply]

/-- The charge-`0` vertex operator acts as the mode indicator. -/
theorem Yeαvec_zero_apply (t : ℤ) (y : LatModuleGen L) :
    Yeαvec L 0 t y = if t = 0 then y else 0 := by
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
            show p ⊗ₜ[ℂ] eGen L β = latStateGen L p β from rfl, Yeαvec_tmul,
            latticeCocycle_zero_left, one_smul, show L.form 0 β = 0 from by simp, sub_zero,
            latStateGen, EEVec_zero_charge, zero_add]
          split_ifs with ht
          · rfl
          · rw [TensorProduct.zero_tmul, smul_zero]

/-- **VA2 ingredient**: `Yeαvec 0 = 1` (the neutral vertex operator is the identity distribution). -/
theorem Yeαvec_zero_eq_one :
    (Yeαvec L 0 : FormalDist (End ℂ (LatModuleGen L))) = (1 : (End ℂ (LatModuleGen L))⟦z^±⟧) := by
  funext t
  refine LinearMap.ext fun y => ?_
  rw [Yeαvec_zero_apply]
  rw [FormalDist.one_apply]
  split_ifs with ht
  · rw [Module.End.one_apply]
  · rw [LinearMap.zero_apply]

/-- **VA2**: `YfullGen |0⟩ = 1`. -/
theorem YfullGen_vacuum (hEven : L.Even) (hPos : L.PosDef) :
    YfullGen L hEven hPos (latVacuumGen L) = (1 : (End ℂ (LatModuleGen L))⟦z^±⟧) := by
  rw [show latVacuumGen L = wordStateLatGen L [] 0 from by
      rw [wordStateLatGen_nil, latChargeGen, latVacuumGen, latStateGen],
    YfullGen_word, YwordLatGen_nil, Yeαvec_zero_eq_one]

/-! ## §C  VA3 (creation) and VA5 (regularity). -/

/-- **VA3 (creation)**: `mode (YfullGen u) (-1) |0⟩ = u` and `mode (YfullGen u) n |0⟩ = 0` for `n ≥ 0`. -/
theorem YfullGen_creation (hEven : L.Even) (hPos : L.PosDef) (u : LatModuleGen L) :
    mode (YfullGen L hEven hPos u) (-1) (latVacuumGen L) = u
      ∧ ∀ n : ℤ, 0 ≤ n → mode (YfullGen L hEven hPos u) n (latVacuumGen L) = 0 := by
  refine ⟨?_, fun n hn => ?_⟩
  · rw [mode_apply, show (-(-1 : ℤ) - 1) = 0 from by ring]; exact YfullGen_cre0 L hEven hPos u
  · rw [mode_apply]; exact YfullGen_creneg L hEven hPos u (by omega : -n - 1 < 0)

/-- **VA5 (regularity)**: each `YfullGen u` is a field. -/
theorem YfullGen_regularity (hEven : L.Even) (hPos : L.PosDef) (u v : LatModuleGen L) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → mode (YfullGen L hEven hPos u) n v = 0 := by
  obtain ⟨Bnd, hB⟩ := YfullGen_isField L hEven hPos u v
  refine ⟨-Bnd + 1, fun n hn => ?_⟩
  rw [mode_apply]; exact hB (-n - 1) (by omega)

end VOA.LatGen
