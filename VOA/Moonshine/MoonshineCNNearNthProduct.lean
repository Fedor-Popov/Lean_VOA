import VOA.Moonshine.MoonshineCNNearTranslation
import VOA.Core.SuperNthProduct

/-! Nonnegative products and the commutator formula for every near-VOA.
The sign-generic field helpers are retained; all vertex algebra results use sign one. -/

namespace VOA
open Module (End)
open scoped BigOperators
universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace NearVOA

theorem commT_bracketDistε (V : NearVOA 𝒱) (ε : ℂ) (u v : 𝒱) :
    commT (V.L (-1)) (bracketDistε ε (V.Y u) (V.Y v))
      = deriv2 (bracketDistε ε (V.Y u) (V.Y v)) := by
  have leib : ∀ (a b c : End ℂ 𝒱), ⁅a, b * c⁆ = ⁅a, b⁆ * c + b * ⁅a, c⁆ := fun a b c => by
    simp only [LieRing.of_associative_ring_bracket]; noncomm_ring
  apply FormalDist₂.ext; intro s t
  simp only [commT_apply, deriv2_apply, bracketDistε_apply, lie_sub, lie_smul, leib,
    L_comm_Ycoeff, smul_mul_assoc, mul_smul_comm, smul_sub, smul_add, smul_comm ε]
  abel

theorem L_comm_cCoeffε (V : NearVOA 𝒱) (ε : ℂ) (u v : 𝒱) (k : ℕ) (m : ℤ) :
    ⁅V.L (-1), cCoeff k (bracketDistε ε (V.Y u) (V.Y v)) m⁆
      = (m + 1) • cCoeff k (bracketDistε ε (V.Y u) (V.Y v)) (m + 1) := by
  show commT (V.L (-1)) (mulBySubPow k (bracketDistε ε (V.Y u) (V.Y v))) (-1) m = _
  rw [commT_mulBySubPow, commT_bracketDistε, resByParts]
  rfl

theorem applyVec_bracketDistε_quadrant (V : NearVOA 𝒱) (ε : ℂ) (u v : 𝒱) (s t : ℤ)
    (hs : s ≤ -1) (ht : t ≤ -1) :
    applyVec V.vacuum (bracketDistε ε (V.Y u) (V.Y v)) s t = 0 := by
  rw [applyVec_apply, bracketDistε_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.mul_apply, Module.End.mul_apply,
    V.Y_apply_vacuum_eq_zero v (by omega),
    V.Y_apply_vacuum_eq_zero u (by omega), map_zero, map_zero, smul_zero,
    sub_zero]

theorem cCoeff_apply_vacuumε (V : NearVOA 𝒱) (ε : ℂ) (u v : 𝒱) (k : ℕ) (m : ℤ) :
    cCoeff k (bracketDistε ε (V.Y u) (V.Y v)) m V.vacuum
      = mulBySubPow k (applyVec V.vacuum (bracketDistε ε (V.Y u) (V.Y v))) (-1) m := by
  show mulBySubPow k (bracketDistε ε (V.Y u) (V.Y v)) (-1) m V.vacuum = _
  rw [← applyVec_apply, applyVec_mulBySubPow]

theorem cCoeff_vacuum_negε (V : NearVOA 𝒱) (ε : ℂ) (u v : 𝒱) (k : ℕ) {m : ℤ} (hm : m < 0) :
    cCoeff k (bracketDistε ε (V.Y u) (V.Y v)) m V.vacuum = 0 := by
  rw [cCoeff_apply_vacuumε]
  exact mulBySubPow_zero_of_quadrant (applyVec_bracketDistε_quadrant V ε u v) k (-1) m
    (by omega) (by omega)

theorem cCoeff_vacuum_baseε (V : NearVOA 𝒱) (ε : ℂ) (u v : 𝒱) (k : ℕ) :
    cCoeff k (bracketDistε ε (V.Y u) (V.Y v)) 0 V.vacuum = V.smul u k v := by
  rw [cCoeff_apply_vacuumε,
    mulBySubPow_diag_of_quadrant (applyVec_bracketDistε_quadrant V ε u v) k (-1) (by omega),
    applyVec_apply, bracketDistε_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.mul_apply, Module.End.mul_apply,
    V.Y_apply_vacuum_zero,
    V.Y_apply_vacuum_eq_zero u (by omega), map_zero, smul_zero, sub_zero]
  rw [smul_def, mode_apply, show (-1 - (k : ℤ)) = -(k : ℤ) - 1 from by ring]

theorem cCoeff_vacuum_eqε (V : NearVOA 𝒱) (ε : ℂ) (u v : 𝒱) (k : ℕ) (m : ℤ) :
    cCoeff k (bracketDistε ε (V.Y u) (V.Y v)) m V.vacuum
      = (V.Y (V.smul u k v)) m V.vacuum := by
  by_cases hm : m < 0
  · rw [cCoeff_vacuum_negε V ε u v k hm,
      V.Y_apply_vacuum_eq_zero (V.smul u k v) hm]
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = (j : ℤ) := ⟨m.toNat, by omega⟩
    clear hm
    induction j with
    | zero =>
        rw [Nat.cast_zero, cCoeff_vacuum_baseε]
        exact (V.Y_apply_vacuum_zero _).symm
    | succ i ih =>
        have expand : ∀ (X : End ℂ 𝒱), ⁅V.L (-1), X⁆ V.vacuum = V.L (-1) (X V.vacuum) := by
          intro X
          rw [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
            Module.End.mul_apply, L_neg_one_vacuum, map_zero, sub_zero]
        have hA := DFunLike.congr_fun (L_comm_cCoeffε V ε u v k (i : ℤ)) V.vacuum
        have hB := DFunLike.congr_fun (L_comm_Ycoeff V (V.smul u k v) (i : ℤ)) V.vacuum
        rw [expand, LinearMap.smul_apply] at hA hB
        have key : ((i : ℤ) + 1) • cCoeff k (bracketDistε ε (V.Y u) (V.Y v)) ((i : ℤ) + 1)
              V.vacuum
            = ((i : ℤ) + 1) • (V.Y (V.smul u k v)) ((i : ℤ) + 1) V.vacuum := by
          rw [← hA, ih, hB]
        have hc : (((i : ℤ) + 1 : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
        rw [← Int.cast_smul_eq_zsmul ℂ ((i : ℤ) + 1),
          ← Int.cast_smul_eq_zsmul ℂ ((i : ℤ) + 1)] at key
        rw [Nat.cast_succ]
        exact smul_right_injective 𝒱 hc key

/-- The nonnegative field product is the vertex operator of the state product. -/
theorem nth_product (V : NearVOA 𝒱) (u v : 𝒱) (k : ℕ) :
    cCoeff k (bracketDistε 1 (V.Y u) (V.Y v)) = V.Y (V.smul u k v) := by
  refine V.goddard_uniqueness _ (V.smul u k v) (fun b => ?_)
    (cCoeff_vacuum_eqε V 1 u v k)
  simpa only [bracketDistε_one] using V.dong_fields u v b k

def modeBracketε (ε : ℂ) (a b : FormalDist (End ℂ 𝒱)) (m n : ℤ) : End ℂ 𝒱 :=
  mode a m * mode b n - ε • (mode b n * mode a m)

@[simp] theorem modeBracketε_apply (ε : ℂ) (a b : FormalDist (End ℂ 𝒱)) (m n : ℤ) :
    modeBracketε ε a b m n = mode a m * mode b n - ε • (mode b n * mode a m) := rfl

theorem modeBracketε_eq (ε : ℂ) (a b : FormalDist (End ℂ 𝒱)) (m n : ℤ) :
    modeBracketε ε a b m n = bracketDistε ε a b (-m - 1) (-n - 1) := rfl

theorem bracket_deltaSum (V : NearVOA 𝒱) (u v : 𝒱) :
    ∃ (N : ℕ) (c : Fin N → FormalDist (End ℂ 𝒱)),
      bracketDistε ((1 : ℂ)) (V.Y u) (V.Y v) = ∑ j : Fin N, deltaDeriv (j : ℕ) (c j) := by
  obtain ⟨N, hN⟩ := V.localε_one u v
  exact ⟨N, (local_iff_deltaSum _ N).mp hN⟩

theorem mode_bracket_opeε (V : NearVOA 𝒱) (ε : ℂ) (u v : 𝒱) {N : ℕ}
    {c : Fin N → FormalDist (End ℂ 𝒱)}
    (h : bracketDistε ε (V.Y u) (V.Y v) = ∑ j : Fin N, deltaDeriv (j : ℕ) (c j)) (a b : ℤ) :
    modeBracketε ε (V.Y u) (V.Y v) a b = ∑ j : Fin N,
      (∏ i ∈ Finset.range (j : ℕ), (a - (i : ℤ))) • mode (c j) (a + b - ((j : ℕ) : ℤ)) := by
  rw [modeBracketε_eq, h, formalDist₂_sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [deltaDeriv_apply,
    show (∏ i ∈ Finset.range (j : ℕ), (-(-a - 1) - 1 - (i : ℤ)))
        = ∏ i ∈ Finset.range (j : ℕ), (a - (i : ℤ)) from
      Finset.prod_congr rfl (fun i _ => by ring)]
  congr 1
  rw [mode_apply]
  congr 1
  ring

theorem commutator_bound (V : NearVOA 𝒱) (u v : 𝒱) (m n : ℤ) :
    ∃ N : ℕ, (∀ k : ℕ, N ≤ k → V.smul u k v = 0)
      ∧ modeBracketε ((1 : ℂ)) (V.Y u) (V.Y v) m n
        = ∑ j : Fin N, gBinom m (j : ℕ) • mode (V.Y (V.smul u (j : ℕ) v)) (m + n - (j : ℕ)) := by
  obtain ⟨N, c, hdecomp⟩ := bracket_deltaSum V u v
  refine ⟨N, ?_, ?_⟩
  · intro k hk
    have h1 : V.Y (V.smul u k v) = cCoeff k (bracketDistε ((1 : ℂ)) (V.Y u) (V.Y v)) :=
      (nth_product V u v k).symm
    rw [hdecomp, cCoeff_sum, Finset.sum_eq_zero (fun j _ => by
        rw [cCoeff_deltaDeriv, if_neg (by have h := j.2; omega)])] at h1
    have h2 : V.smul u k v = mode (V.Y (V.smul u k v)) (-1) V.vacuum :=
      (V.smul_neg_one_vacuum (V.smul u k v)).symm
    rw [h2, h1, mode_apply]; rfl
  · rw [mode_bracket_opeε V ((1 : ℂ)) u v hdecomp m n]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hne : ((j : ℕ).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hcj : c j = (((j : ℕ).factorial : ℂ)⁻¹) • V.Y (V.smul u (j : ℕ) v) := by
      have hrec := cCoeff_deltaSum c j
      rw [← hdecomp, nth_product V u v] at hrec
      rw [hrec, ← Int.cast_smul_eq_zsmul ℂ ((j : ℕ).factorial : ℤ), Int.cast_natCast, smul_smul,
        inv_mul_cancel₀ hne, one_smul]
    rw [hcj, mode_smul,
      ← Int.cast_smul_eq_zsmul ℂ (∏ i ∈ Finset.range (j : ℕ), (m - (i : ℤ))), smul_smul]
    congr 1
    rw [gBinom, div_eq_mul_inv]
    congr 1
    push_cast
    rfl

theorem mode_commutator (V : NearVOA 𝒱) (u v : 𝒱) (a b : ℤ) :
    ∃ N : ℕ, modeBracketε ((1 : ℂ)) (V.Y u) (V.Y v) a b
      = ∑ j : Fin N, gBinom a (j : ℕ) • mode (V.Y (V.smul u (j : ℕ) v)) (a + b - (j : ℕ)) := by
  obtain ⟨N, _, h⟩ := commutator_bound V u v a b
  exact ⟨N, h⟩

theorem mode_iterate_nonneg_choose (V : NearVOA 𝒱) (u v : 𝒱) (k : ℕ) (n : ℤ) :
    mode (V.Y (V.smul u (k : ℤ) v)) n =
      ∑ r ∈ Finset.range (k + 1), (((-1 : ℤ) ^ (k - r)) * (k.choose r : ℤ)) •
        (mode (V.Y u) (r : ℤ) * mode (V.Y v) (n + ((k - r : ℕ) : ℤ))
          - (1 : ℂ) • (mode (V.Y v) (n + ((k - r : ℕ) : ℤ)) * mode (V.Y u) (r : ℤ))) := by
  rw [← nth_product V u v k, mode_apply, cCoeff_apply, mulBySubPow_apply_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [bracketDistε_apply, show (-1 : ℤ) - (r : ℤ) = -(r : ℤ) - 1 from by ring,
    show (-n - 1) - ((k - r : ℕ) : ℤ) = -(n + ((k - r : ℕ) : ℤ)) - 1 from by ring]
  simp only [mode_apply]

theorem mode_iterate_nonneg (V : NearVOA 𝒱) (u v : 𝒱) (k : ℕ) (n : ℤ) :
    mode (V.Y (V.smul u (k : ℤ) v)) n =
      ∑ r ∈ Finset.range (k + 1), (((-1 : ℂ) ^ (k - r)) * gBinom (k : ℤ) r) •
        (mode (V.Y u) (r : ℤ) * mode (V.Y v) (n + ((k - r : ℕ) : ℤ))
          - (1 : ℂ) • (mode (V.Y v) (n + ((k - r : ℕ) : ℤ)) * mode (V.Y u) (r : ℤ))) := by
  rw [mode_iterate_nonneg_choose V u v]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  have hrle : r ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  rw [gBinom_natCast_eq_choose hrle,
    ← Int.cast_smul_eq_zsmul ℂ (((-1 : ℤ) ^ (k - r)) * (k.choose r : ℤ))]
  congr 1
  push_cast
  rfl

theorem mode_iterate_borcherds_nonneg (V : NearVOA 𝒱) (u v : 𝒱) (k : ℕ) (n : ℤ) :
    mode (V.Y (V.smul u (k : ℤ) v)) n =
      ∑ i ∈ Finset.range (k + 1), ((-1 : ℂ) ^ i * gBinom (k : ℤ) i) •
        (mode (V.Y u) ((k : ℤ) - i) * mode (V.Y v) (n + i)
          - ((1 : ℂ) * (-1 : ℂ) ^ k) • (mode (V.Y v) ((k : ℤ) + n - i) * mode (V.Y u) i)) := by
  rw [mode_iterate_nonneg V u v]
  simp only [smul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  congr 1
  · -- A-part (`u·v`): reflect `r ↦ k - r`
    rw [← Finset.sum_range_reflect
      (fun r => (((-1 : ℂ) ^ (k - r)) * gBinom (k : ℤ) r) •
        (mode (V.Y u) (r : ℤ) * mode (V.Y v) (n + ((k - r : ℕ) : ℤ)))) (k + 1)]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [show k + 1 - 1 - i = k - i from by omega, Nat.sub_sub_self hik, gBinom_symm_nat hik,
      Nat.cast_sub hik]
  · -- B-part (`v·u`): index `r = i`, sign/symmetry identity, `ε` a spectator scalar
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [Nat.cast_sub hik, smul_smul, smul_smul,
      show n + ((k : ℤ) - i) = (k : ℤ) + n - i from by ring]
    congr 1
    rw [show ((-1 : ℂ) ^ (k - i) * gBinom (k : ℤ) i) * (1 : ℂ)
          = (1 : ℂ) * ((-1 : ℂ) ^ (k - i) * gBinom (k : ℤ) i) from by ring,
      show ((-1 : ℂ) ^ i * gBinom (k : ℤ) i) * ((1 : ℂ) * (-1 : ℂ) ^ k)
          = (1 : ℂ) * ((-1 : ℂ) ^ i * (-1 : ℂ) ^ k * gBinom (k : ℤ) i) from by ring]
    congr 2
    rw [← pow_add, show i + k = (k - i) + 2 * i from by omega, pow_add, pow_mul]
    simp

end NearVOA

end VOA
