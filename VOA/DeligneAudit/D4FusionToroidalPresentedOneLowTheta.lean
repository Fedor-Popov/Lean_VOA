import VOA.DeligneAudit.D4FusionToroidalPresentedOneLowSl2

/-! The squared highest-root current kills the multiplicity-one generator. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.DeligneSector.Sparse

noncomputable section

private abbrev ρ := univRepG D4sector.f OneR
private abbrev w := wUG D4sector.f OneR

private def thetaH (r : ℕ) : OneU →ₗ[ℂ] OneU :=
  -(∑ c : Fin 28, D4sector.f (15 : Fin 28) (27 : Fin 28) c • ρ.op c r)

private theorem theta_doubleZ : ∀ d : Fin 28,
    (∑ c : Fin 28, fZ br 15 27 c * fZ br c 27 d) =
      if d = 27 then 2 else 0 := by
  decide +kernel

private theorem theta_double (d : Fin 28) :
    (∑ c : Fin 28, D4sector.f (15 : Fin 28) (27 : Fin 28) c * D4sector.f c (27 : Fin 28) d) =
      if d = 27 then (2 : ℂ) else 0 := by
  change (∑ c : Fin 28, (fZ br 15 27 c : ℂ) * (fZ br c 27 d : ℂ)) = _
  have h := theta_doubleZ d
  split_ifs at h ⊢ <;> exact_mod_cast h

private theorem thetaH_comm (r s : ℕ) (x : OneU) :
    thetaH r (ρ.op (27 : Fin 28) s x) - ρ.op (27 : Fin 28) s (thetaH r x) =
      (-2 : ℂ) • ρ.op (27 : Fin 28) (r + s) x := by
  have hin : ∀ c y,
      ρ.op c r (ρ.op (27 : Fin 28) s y) - ρ.op (27 : Fin 28) s (ρ.op c r y) =
      ∑ d : Fin 28, D4sector.f c (27 : Fin 28) d • ρ.op d (r + s) y :=
    fun c y => ρ.comm c (27 : Fin 28) r s y
  calc
    thetaH r (ρ.op (27 : Fin 28) s x) - ρ.op (27 : Fin 28) s (thetaH r x) =
        -∑ c : Fin 28, D4sector.f (15 : Fin 28) (27 : Fin 28) c •
          (ρ.op c r (ρ.op (27 : Fin 28) s x) - ρ.op (27 : Fin 28) s (ρ.op c r x)) := by
          simp only [thetaH, LinearMap.neg_apply, LinearMap.coe_sum, Finset.sum_apply,
            LinearMap.smul_apply, map_neg, map_sum, map_smul, smul_sub,
            Finset.sum_sub_distrib]
          abel
    _ = -∑ d : Fin 28,
        (∑ c : Fin 28, D4sector.f (15 : Fin 28) (27 : Fin 28) c *
          D4sector.f c (27 : Fin 28) d) •
          ρ.op d (r + s) x := by
          simp only [hin, Finset.smul_sum, smul_smul]
          rw [Finset.sum_comm]
          simp only [Finset.sum_smul]
    _ = (-2 : ℂ) • ρ.op (27 : Fin 28) (r + s) x := by
          simp only [theta_double, ite_smul, zero_smul, Finset.sum_ite_eq',
            Finset.mem_univ, if_true]
          rw [neg_smul]

private theorem thetaEF_comm (r s : ℕ) (x : OneU) :
    (-ρ.op (15 : Fin 28) r) (ρ.op (27 : Fin 28) s x) -
      ρ.op (27 : Fin 28) s ((-ρ.op (15 : Fin 28) r) x) =
      thetaH (r + s) x := by
  have h := ρ.comm (15 : Fin 28) (27 : Fin 28) r s x
  simp only [LinearMap.neg_apply, map_neg, thetaH, LinearMap.coe_sum,
    Finset.sum_apply, LinearMap.smul_apply]
  calc
    _ = -(ρ.op (15 : Fin 28) r (ρ.op (27 : Fin 28) s x) -
        ρ.op (27 : Fin 28) s (ρ.op (15 : Fin 28) r x)) := by abel
    _ = _ := congrArg Neg.neg h

private theorem theta_support : ∀ c : Fin 28,
    fZ br 15 27 c ≠ 0 → c.val < 4 := by
  decide +kernel

private theorem thetaH_generator_one : thetaH 1 w = 0 := by
  have hs : (∑ c : Fin 28, D4sector.f (15 : Fin 28) (27 : Fin 28) c • ρ.op c 1 w) = 0 := by
    apply Finset.sum_eq_zero
    intro c _
    by_cases hfc : fZ br 15 27 c = 0
    · change (fZ br 15 27 c : ℂ) • ρ.op c 1 w = 0
      rw [hfc, Int.cast_zero, zero_smul]
    · have hc := theta_support c hfc
      have hs := rs_cartan_pos
        (show Sat D4sector.f ρ w (ravSpec D4sector 1 2) by
          simpa [OneR, ravFam_zero_right] using univG_sat D4sector.f OneR)
        (show D4sector.cartan c by exact hc) 1 (by omega)
      rw [hs]
      simp
  simp only [thetaH, LinearMap.neg_apply, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply, hs, neg_zero]

private theorem thetaH_generator_zero : thetaH 0 w = (2 : ℂ) • w := by
  have hterm : ∀ c : Fin 28,
      D4sector.f (15 : Fin 28) (27 : Fin 28) c • ρ.op c 0 w =
        (D4sector.f (15 : Fin 28) (27 : Fin 28) c * (thetaD4 c : ℂ)) • w := by
    intro c
    by_cases hc : c.val < 4
    · have hs := rs_cartan_zero
        (show Sat D4sector.f ρ w (ravSpec D4sector 1 2) by
          simpa [OneR, ravFam_zero_right] using univG_sat D4sector.f OneR)
        (show D4sector.cartan c by exact hc)
      change ρ.op c 0 w = (((1 * thetaD4 c : ℕ) : ℂ)) • w at hs
      simp only [one_mul] at hs
      rw [hs, smul_smul]
    · have hfc : fZ br 15 27 c = 0 := by
        by_contra h0
        exact hc (theta_support c h0)
      have hf : D4sector.f (15 : Fin 28) (27 : Fin 28) c = 0 := by
        change (fZ br 15 27 c : ℂ) = 0
        rw [hfc, Int.cast_zero]
      rw [hf, zero_smul, zero_mul, zero_smul]
  simp only [thetaH, LinearMap.neg_apply, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply]
  rw [Finset.sum_congr rfl (fun c _ => hterm c), ← Finset.sum_smul,
    Finset.sum_eq_single (1 : Fin 28)]
  · change -((((fZ br 15 27 1 : ℤ) : ℂ) * (thetaD4 1 : ℂ)) • w) =
        (2 : ℂ) • w
    norm_num [thetaD4, fZ, br, brT, sget]
  · intro c _ hc
    have hc1 : c.val ≠ 1 := fun h => hc (Fin.ext h)
    simp [thetaD4, hc1]
  · simp

theorem one_top_mode_one_theta : ρ.op D4sector.c₀ 1 oneTop = 0 := by
  letI : FiniteDimensional ℂ OneU := rav_finiteDimensional 1 (by omega)
  let T := ρ.op (27 : Fin 28) 1
  let E := -ρ.op (15 : Fin 28) 0
  let F := ρ.op (27 : Fin 28) 0
  let H := thetaH 0
  have hEw : E w = 0 := by
    change -ρ.op (15 : Fin 28) 0 w = 0
    have hs := rs_raising
      (show Sat D4sector.f ρ w (ravSpec D4sector 1 2) by
        simpa [OneR, ravFam_zero_right] using univG_sat D4sector.f OneR)
      (show D4sector.raising (15 : Fin 28) by
        change 4 ≤ (15 : Fin 28).val ∧ (15 : Fin 28).val < 16
        decide) 0
    rw [hs, neg_zero]
  have hET : ∀ x, E (T x) - T (E x) = thetaH 1 x := by
    intro x
    simpa only [E, T, Nat.zero_add] using thetaEF_comm 0 1 x
  have hHT : ∀ x, H (T x) - T (H x) = (-2 : ℂ) • T x := by
    intro x
    simpa only [H, T, Nat.zero_add] using thetaH_comm 0 1 x
  have hH1T : thetaH 1 (T w) = 0 := by
    have h := thetaH_comm 1 1 w
    rw [thetaH_generator_one, map_zero, sub_zero] at h
    change thetaH 1 (T w) = (-2 : ℂ) • ρ.op (27 : Fin 28) 2 w at h
    rw [one_generator_mode_two 27, smul_zero] at h
    exact h
  have hETw : E (T w) = 0 := by
    have h := hET w
    rw [hEw, map_zero, sub_zero, thetaH_generator_one] at h
    exact h
  have hETTw : E (T (T w)) = 0 := by
    have h := hET (T w)
    rw [hETw, map_zero, sub_zero, hH1T] at h
    exact h
  have hHTw : H (T w) = 0 := by
    have h := hHT w
    rw [thetaH_generator_zero, map_smul] at h
    have h' := sub_eq_iff_eq_add.mp h
    rw [h']
    module
  have hHTTw : H (T (T w)) = (-2 : ℂ) • T (T w) := by
    have h := hHT (T w)
    rw [hHTw, map_zero, sub_zero] at h
    exact h
  have hEF : ∀ x, E (F x) - F (E x) = H x := by
    intro x
    simpa only [E, F, H, Nat.zero_add] using thetaEF_comm 0 0 x
  have hHF : ∀ x, H (F x) - F (H x) = (-2 : ℂ) • F x := by
    intro x
    simpa only [H, F, Nat.zero_add] using thetaH_comm 0 0 x
  have hz := sl2_negative_two_of_finite E F H hEF hHF (T (T w)) hETTw hHTTw
  simpa only [oneTop, T, ρ, w, D4sector] using hz

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.one_top_mode_one_theta
