import VOA.Moonshine.MoonshineCNNearGoddard

/-! Translation covariance and creation for every near-VOA.
Port of `SuperTranslationCovariance` with ordinary locality. -/

namespace VOA

open Module (End)

universe u

namespace NearVOA

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

theorem Y_Tr (V : NearVOA 𝒱) (u : 𝒱) : V.Y (V.L (-1) u) = deriv (V.Y u) := by
  rw [L_def, show (-1 : ℤ) + 1 = 0 by ring]
  exact V.translation u

theorem mode_Y_Tr (V : NearVOA 𝒱) (u : 𝒱) (n : ℤ) :
    mode (V.Y (V.L (-1) u)) n = (-n) • mode (V.Y u) (n - 1) := by
  rw [Y_Tr, mode_deriv]

theorem L_neg_one_vacuum (V : NearVOA 𝒱) : V.L (-1) V.vacuum = 0 := by
  have h : V.L (-1) V.vacuum = V.smul V.conformalVector 0 V.vacuum := by
    rw [L_def, show (-1 : ℤ) + 1 = 0 by ring]; rfl
  rw [h]
  exact V.smul_vacuum_eq_zero V.conformalVector le_rfl

theorem creation_pow (V : NearVOA 𝒱) (a : 𝒱) (k : ℕ) :
    V.smul a (-(k : ℤ) - 1) V.vacuum = ((k.factorial : ℂ)⁻¹) • ((V.L (-1) ^ k) a) := by
  induction k generalizing a with
  | zero =>
      rw [show (-(↑(0 : ℕ) : ℤ) - 1) = -1 by norm_num,
        smul_neg_one_vacuum]
      simp
  | succ k ih =>
      have key : V.smul (V.L (-1) a) (-(k : ℤ) - 1) V.vacuum
          = ((k : ℤ) + 1) • V.smul a (-(k : ℤ) - 2) V.vacuum := by
        rw [smul_def, smul_def, mode_Y_Tr,
          show (-(-(k : ℤ) - 1)) = (k : ℤ) + 1 by ring,
          show ((-(k : ℤ) - 1) - 1) = -(k : ℤ) - 2 by ring, LinearMap.smul_apply]
      have hih := ih (V.L (-1) a)
      have hTk : (V.L (-1) ^ k) (V.L (-1) a) = (V.L (-1) ^ (k + 1)) a := by
        rw [pow_succ]; rfl
      rw [key, hTk] at hih
      rw [show (-(↑(k + 1) : ℤ) - 1) = -(k : ℤ) - 2 by push_cast; ring]
      have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      rw [← Int.cast_smul_eq_zsmul ℂ ((k : ℤ) + 1)] at hih
      push_cast at hih
      have hX : V.smul a (-(k : ℤ) - 2) V.vacuum
          = ((k : ℂ) + 1)⁻¹ • ((k.factorial : ℂ)⁻¹ • (V.L (-1) ^ (k + 1)) a) := by
        rw [← hih, inv_smul_smul₀ hk1]
      rw [hX, smul_smul]
      congr 1
      rw [← mul_inv, Nat.factorial_succ]
      push_cast
      ring

theorem L_neg_one_smul_vacuum (V : NearVOA 𝒱) (u : 𝒱) (s : ℤ) :
    V.L (-1) (V.smul u s V.vacuum) = V.smul (V.L (-1) u) s V.vacuum := by
  rcases lt_or_ge s 0 with hs | hs
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, s = -(j : ℤ) - 1 := ⟨(-s - 1).toNat, by omega⟩
    rw [creation_pow, creation_pow, map_smul]
    congr 1
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← pow_succ', ← pow_succ]
  · rw [V.smul_vacuum_eq_zero u hs, V.smul_vacuum_eq_zero _ hs, map_zero]

theorem isField_Y (V : NearVOA 𝒱) (u : 𝒱) : IsField (V.Y u) := by
  intro x
  obtain ⟨N, hN⟩ := V.regularity u x
  refine ⟨-N, fun n hn => ?_⟩
  have h := hN (-n - 1) (by omega)
  rwa [mode_apply, show (-(-n - 1) - 1 : ℤ) = n by ring] at h

theorem Y_omega_neg_one (V : NearVOA 𝒱) : (V.Y V.conformalVector) (-1) = V.L (-1) := by
  rw [L_def, show (-1 : ℤ) + 1 = 0 by ring, mode_apply]
  norm_num

theorem cCoeff_zero_omega (V : NearVOA 𝒱) (u : 𝒱) (m : ℤ) :
    cCoeff 0 (bracketDist (V.Y V.conformalVector) (V.Y u)) m
      = V.L (-1) * (V.Y u) m - (V.Y u) m * V.L (-1) := by
  show mulBySubPow 0 (bracketDist (V.Y V.conformalVector) (V.Y u)) (-1) m = _
  rw [mulBySubPow_zero]
  show bracketDist (V.Y V.conformalVector) (V.Y u) (-1) m = _
  rw [bracketDist_apply, Y_omega_neg_one]

/-- Translation covariance follows from Goddard uniqueness and Dong locality. -/
theorem translation_covariance (V : NearVOA 𝒱) (u : 𝒱) :
    cCoeff 0 (bracketDist (V.Y V.conformalVector) (V.Y u)) = V.Y (V.L (-1) u) := by
  refine V.goddard_uniqueness _ (V.L (-1) u)
    (fun b => V.dong_fields V.conformalVector u b 0) (fun m => ?_)
  rw [cCoeff_zero_omega]
  show V.L (-1) ((V.Y u) m V.vacuum) - (V.Y u) m (V.L (-1) V.vacuum)
    = (V.Y (V.L (-1) u)) m V.vacuum
  have e1 : (V.Y u) m V.vacuum = V.smul u (-m - 1) V.vacuum := by
    rw [smul_def, mode_apply]; norm_num
  have e2 : (V.Y (V.L (-1) u)) m V.vacuum = V.smul (V.L (-1) u) (-m - 1) V.vacuum := by
    rw [smul_def, mode_apply]; norm_num
  rw [L_neg_one_vacuum, map_zero, sub_zero, e1, e2, L_neg_one_smul_vacuum]

theorem L_comm_Ycoeff (V : NearVOA 𝒱) (u : 𝒱) (s : ℤ) :
    ⁅V.L (-1), (V.Y u) s⁆ = (s + 1) • (V.Y u) (s + 1) := by
  have h := congrFun (translation_covariance V u) s
  rw [cCoeff_zero_omega, Y_Tr, deriv_apply] at h
  rw [LieRing.of_associative_ring_bracket]
  exact h

theorem L_comm_mode (V : NearVOA 𝒱) (u : 𝒱) (n : ℤ) :
    ⁅V.L (-1), mode (V.Y u) n⁆ = (-n) • mode (V.Y u) (n - 1) := by
  have h := L_comm_Ycoeff V u (-n - 1)
  rw [show (-n - 1 : ℤ) + 1 = -n from by ring] at h
  rw [mode_apply, h, mode_apply, show (-(n - 1) - 1 : ℤ) = -n from by ring]

theorem L_neg_one_deriv (V : NearVOA 𝒱) (u w : 𝒱) (n : ℤ) :
    V.L (-1) (V.smul u n w) - V.smul u n (V.L (-1) w) = V.smul (V.L (-1) u) n w := by
  have h := DFunLike.congr_fun (L_comm_mode V u n) w
  rw [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply, LinearMap.smul_apply] at h
  simp only [smul_def]
  rw [mode_Y_Tr, LinearMap.smul_apply]
  exact h

theorem Y_Tpow (V : NearVOA 𝒱) (u : 𝒱) (j : ℕ) :
    V.Y ((V.L (-1) ^ j) u) = (deriv^[j]) (V.Y u) := by
  induction j with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, Y_Tr, ih, Function.iterate_succ',
        Function.comp_apply]

theorem smul_T_apply (V : NearVOA 𝒱) (w v : 𝒱) (n : ℤ) :
    V.smul (V.L (-1) w) n v = (-n) • V.smul w (n - 1) v := by
  rw [smul_def, mode_Y_Tr, LinearMap.smul_apply]
  rfl

theorem smul_Tpow (V : NearVOA 𝒱) (u v : 𝒱) (k : ℕ) (n : ℤ) :
    V.smul ((V.L (-1) ^ k) u) n v
      = (∏ i ∈ Finset.range k, (-(n - (i : ℤ)))) • V.smul u (n - (k : ℤ)) v := by
  induction k generalizing n with
  | zero => simp
  | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, smul_T_apply, ih, smul_smul,
        Finset.prod_range_succ' (fun i => -(n - (i : ℤ))) j]
      have hidx : n - 1 - (j : ℤ) = n - ((j + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hidx]
      congr 1
      rw [show (-(n - ((0 : ℕ) : ℤ))) = -n by push_cast; ring, mul_comm]
      congr 1
      exact Finset.prod_congr rfl (fun i _ => by push_cast; ring)

theorem smul_Tpow_neg_one (V : NearVOA 𝒱) (u v : 𝒱) (k : ℕ) :
    V.smul ((V.L (-1) ^ k) u) (-1) v = (k.factorial : ℤ) • V.smul u (-(k : ℤ) - 1) v := by
  rw [smul_Tpow]
  congr 1
  · rw [← VertexOperatorAlgebra.prod_one_add_factorial]; exact Finset.prod_congr rfl (fun i _ => by ring)
  · congr 1; ring

end NearVOA

end VOA
