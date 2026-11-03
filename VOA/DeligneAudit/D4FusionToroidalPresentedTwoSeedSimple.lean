import VOA.DeligneAudit.D4FusionToroidalPresentedTwoSeedLowering

/-! The four simple negative-root letters kill the quadratic seed. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4FusionContact

noncomputable section

theorem two_seed_lowering_zero (i : Fin 12) (hi : i.val < 4)
    (s : ℕ) (hs : s ≤ 1) :
    (ρPTE 2).op (negativeIndex i) 0 s twoQuadraticSeed = 0 := by
  let E := (twoSeedRootSign i : ℂ) • (ρPTE 2).op (twoSeedRootE i) 0 0
  let F := (ρPTE 2).op (negativeIndex i) 0 0
  let H := twoSeedRootH i
  let Y := (ρPTE 2).op (negativeIndex i) 0 s
  let u := Y twoQuadraticSeed
  have hraise : D4sector.raising (twoSeedRootE i) := by
    change 4 ≤ (twoSeedRootE i).val ∧ (twoSeedRootE i).val < 16
    simp only [twoSeedRootE, Fin.val_mk]
    omega
  have hES : E twoQuadraticSeed = 0 := by
    change (twoSeedRootSign i : ℂ) •
      (ρPTE 2).op (twoSeedRootE i) 0 0 twoQuadraticSeed = 0
    rw [two_seed_raising_zero (twoSeedRootE i) hraise 0 (by omega), smul_zero]
  have hHS : H twoQuadraticSeed = 0 := by
    exact two_seed_rootH_zero i 0 (by omega)
  have hE : E u = 0 := by
    have hc := (ρPTE 2).comm (twoSeedRootE i) (negativeIndex i)
      0 0 0 s twoQuadraticSeed
    rw [if_pos (by omega)] at hc
    have hscaled := congrArg ((twoSeedRootSign i : ℂ) • ·) hc
    have hz := two_seed_rootH_zero i s hs
    change (twoSeedRootSign i : ℂ) •
      (∑ c : Fin 28, D4sector.f (twoSeedRootE i) (negativeIndex i) c •
        (ρPTE 2).op c 0 s twoQuadraticSeed) = 0 at hz
    simp only [Nat.zero_add] at hscaled
    have hscaled' : (twoSeedRootSign i : ℂ) •
        ((ρPTE 2).op (twoSeedRootE i) 0 0
          (Y twoQuadraticSeed) -
          Y ((ρPTE 2).op (twoSeedRootE i) 0 0 twoQuadraticSeed)) = 0 := by
      exact hscaled.trans hz
    rw [smul_sub] at hscaled'
    have hmap : (twoSeedRootSign i : ℂ) •
        Y ((ρPTE 2).op (twoSeedRootE i) 0 0 twoQuadraticSeed) =
        Y ((twoSeedRootSign i : ℂ) •
          (ρPTE 2).op (twoSeedRootE i) 0 0 twoQuadraticSeed) := by
      rw [map_smul]
    rw [hmap] at hscaled'
    change E u - Y (E twoQuadraticSeed) = 0 at hscaled'
    rw [hES, map_zero, sub_zero] at hscaled'
    exact hscaled'
  have hH : H u = (-2 : ℂ) • u := by
    have hc := two_seed_rootHF i s hs twoQuadraticSeed
    change H u - Y (H twoQuadraticSeed) = (-2 : ℂ) • u at hc
    rw [hHS, map_zero, sub_zero] at hc
    exact hc
  have hEF : ∀ x, E (F x) - F (E x) = H x := by
    intro x
    exact two_seed_rootEF i x
  have hHF : ∀ x, H (F x) - F (H x) = (-2 : ℂ) • F x := by
    intro x
    exact two_seed_rootHF i 0 (by omega) x
  have hN : ∃ N : ℕ, F^[N] u = 0 := two_seed_lowering_nil i hi s hs
  exact two_sl2_negative_two_of_nilpotent E F H hEF hHF u hE hH hN

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.two_seed_lowering_zero
