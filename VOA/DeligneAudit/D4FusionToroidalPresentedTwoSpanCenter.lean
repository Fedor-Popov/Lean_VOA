import VOA.DeligneAudit.D4FusionToroidalPresentedTwoSpanLoweringOuter

/-! The central simple root triple on the two degree-one generators. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.D4FusionContact
open VOA.DeligneAudit.SectorWeyl

noncomputable section

private theorem center_root_bracket : ∀ c : Fin 28,
    fZ br (twoSeedRootE 2) (negativeIndex 2) c =
      if c = 1 then 1 else 0 := by
  decide +kernel

theorem two_center_rootH_eq :
    twoSeedRootH 2 = (ρPTE 2).op (1 : Fin 28) 0 0 := by
  apply LinearMap.ext
  intro x
  have hsign : twoSeedRootSign 2 = 1 := by decide
  simp only [twoSeedRootH, hsign, Int.cast_one, one_smul,
    LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
  have hf (c : Fin 28) :
      D4sector.f (twoSeedRootE 2) (negativeIndex 2) c =
        if c = 1 then (1 : ℂ) else 0 := by
    change (fZ br (twoSeedRootE 2) (negativeIndex 2) c : ℂ) = _
    rw [center_root_bracket]
    split_ifs <;> simp
  simp only [hf, ite_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, one_smul]

theorem two_sl2_negative_three_of_nilpotent {V : Type*}
    [AddCommGroup V] [Module ℂ V] (E F H : V →ₗ[ℂ] V)
    (hEF : ∀ x, E (F x) - F (E x) = H x)
    (hHF : ∀ x, H (F x) - F (H x) = (-2 : ℂ) • F x)
    (u : V) (hE : E u = 0) (hH : H u = (-3 : ℂ) • u)
    (hN : ∃ N : ℕ, F^[N] u = 0) : u = 0 := by
  obtain ⟨N, hN⟩ := hN
  induction N with
  | zero => simpa using hN
  | succ n ih =>
      by_cases hp : F^[n] u = 0
      · exact ih hp
      · have h := sl2_E_Fpow E F H hEF hHF u (-3) hE hH n
        rw [hN, map_zero] at h
        have hcoef : ((n : ℂ) + 1) * ((-3 : ℂ) - n) ≠ 0 := by
          apply mul_ne_zero
          · exact_mod_cast Nat.succ_ne_zero n
          · intro hz
            have hre := congrArg Complex.re hz
            have hnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
            norm_num at hre
            linarith
        exact (hp ((smul_eq_zero.mp h.symm).resolve_left hcoef)).elim

private theorem center_commute_iter (s n : ℕ) (x : PTE 2) :
    ((ρPTE 2).op (negativeIndex 2) 0 0)^[n]
      ((ρPTE 2).op D4sector.c₀ 1 s x) =
    (ρPTE 2).op D4sector.c₀ 1 s
      (((ρPTE 2).op (negativeIndex 2) 0 0)^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, twoGen_negative_comm,
        Function.iterate_succ_apply']

theorem twoGen_center_lowering (s : ℕ) :
    (twoCurrent.op (negativeIndex 2) 0)^[2] (twoGen s) = 0 := by
  let E := (twoSeedRootSign 2 : ℂ) •
    (ρPTE 2).op (twoSeedRootE 2) 0 0
  let F := (ρPTE 2).op (negativeIndex 2) 0 0
  let H := twoSeedRootH 2
  let u := twoGen s
  have hsign : twoSeedRootSign 2 = 1 := by decide
  have hEF : ∀ x, E (F x) - F (E x) = H x := by
    intro x
    exact two_seed_rootEF 2 x
  have hHF : ∀ x, H (F x) - F (H x) = (-2 : ℂ) • F x := by
    intro x
    exact two_seed_rootHF 2 0 (by omega) x
  have hraise : D4sector.raising (twoSeedRootE 2) := by
    change 4 ≤ (twoSeedRootE 2).val ∧ (twoSeedRootE 2).val < 16
    decide
  have hE : E u = 0 := by
    simpa [E, u, hsign, twoCurrent] using
      twoGen_raising s (twoSeedRootE 2) hraise 0
  have hcartan : D4sector.cartan (1 : Fin 28) := by
    change (1 : Fin 28).val < 4
    decide
  have hH : H u = (1 : ℂ) • u := by
    change twoSeedRootH 2 (twoGen s) = (1 : ℂ) • twoGen s
    rw [two_center_rootH_eq]
    simpa [twoCurrent, D4sector, thetaD4] using
      twoGen_cartan_zero s (1 : Fin 28) hcartan
  have hv : F^[3] (pTE 2) = 0 := by
    simpa [F, D4sector, lowExpD4, negativeIndex] using
      two_seed_lowering_v_nil 2 (by decide)
  have hu : F^[3] u = 0 := by
    change F^[3] ((ρPTE 2).op D4sector.c₀ 1 s (pTE 2)) = 0
    rw [show F = (ρPTE 2).op (negativeIndex 2) 0 0 from rfl,
      center_commute_iter, hv, map_zero]
  have he : E (F^[2] u) = 0 := by
    have ht := sl2_E_Fpow E F H hEF hHF u 1 hE hH 1
    simpa using ht
  have hh : H (F^[2] u) = (-3 : ℂ) • F^[2] u := by
    have ht := sl2_H_Fpow F H hHF u 1 hH 2
    convert ht using 1
    norm_num
  have hn : ∃ N : ℕ, F^[N] (F^[2] u) = 0 := by
    refine ⟨1, ?_⟩
    simpa [Function.iterate_succ_apply'] using hu
  have hz := two_sl2_negative_three_of_nilpotent E F H
    hEF hHF (F^[2] u) he hh hn
  simpa [twoCurrent, F, u] using hz

theorem twoOne_center_lowering :
    (twoOneCurrent.op (negativeIndex 2) 0)^[2] twoOneGen = 0 := by
  have hz : (twoCurrent.op (negativeIndex 2) 0)
      ((twoCurrent.op (negativeIndex 2) 0) (twoGen 0)) = 0 := by
    simpa [Function.iterate_succ_apply'] using twoGen_center_lowering 0
  change (twoM 1).mkQ
    ((twoCurrent.op (negativeIndex 2) 0)
      ((twoCurrent.op (negativeIndex 2) 0) (twoGen 0))) = 0
  rw [hz, map_zero]

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.two_center_rootH_eq
#print axioms VOA.DeligneAudit.Toroidal.two_sl2_negative_three_of_nilpotent
#print axioms VOA.DeligneAudit.Toroidal.twoGen_center_lowering
#print axioms VOA.DeligneAudit.Toroidal.twoOne_center_lowering
