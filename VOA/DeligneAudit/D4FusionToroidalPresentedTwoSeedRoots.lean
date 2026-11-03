import VOA.DeligneAudit.D4FusionToroidalPresentedTwoSeedSl2

/-! Root-triple commutators on the multiplicity-two toroidal presentation. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.D4FusionContact

noncomputable section

def twoSeedRootE (i : Fin 12) : Fin 28 := ⟨i.val + 4, by omega⟩
def twoSeedRootSign (i : Fin 12) : ℤ := if i.val < 4 then 1 else -1

def twoSeedRootH (i : Fin 12) : PTE 2 →ₗ[ℂ] PTE 2 :=
  (twoSeedRootSign i : ℂ) •
    ∑ c : Fin 28, D4sector.f (twoSeedRootE i) (negativeIndex i) c •
      (ρPTE 2).op c 0 0

private theorem root_support : ∀ i : Fin 12, ∀ c : Fin 28,
    fZ br (twoSeedRootE i) (negativeIndex i) c ≠ 0 → c.val < 4 := by
  decide +kernel

private theorem root_doubleZ : ∀ i : Fin 12, ∀ d : Fin 28,
    twoSeedRootSign i *
      (∑ c : Fin 28, fZ br (twoSeedRootE i) (negativeIndex i) c *
        fZ br c (negativeIndex i) d) =
      if d = negativeIndex i then -2 else 0 := by
  decide +kernel

private theorem root_double (i : Fin 12) (d : Fin 28) :
    (twoSeedRootSign i : ℂ) *
      (∑ c : Fin 28, D4sector.f (twoSeedRootE i) (negativeIndex i) c *
        D4sector.f c (negativeIndex i) d) =
      if d = negativeIndex i then (-2 : ℂ) else 0 := by
  change (twoSeedRootSign i : ℂ) *
    (∑ c : Fin 28, (fZ br (twoSeedRootE i) (negativeIndex i) c : ℂ) *
      (fZ br c (negativeIndex i) d : ℂ)) = _
  have h := root_doubleZ i d
  split_ifs at h ⊢ <;> exact_mod_cast h

theorem two_seed_rootEF (i : Fin 12) (x : PTE 2) :
    ((twoSeedRootSign i : ℂ) • (ρPTE 2).op (twoSeedRootE i) 0 0)
      ((ρPTE 2).op (negativeIndex i) 0 0 x) -
    (ρPTE 2).op (negativeIndex i) 0 0
      (((twoSeedRootSign i : ℂ) • (ρPTE 2).op (twoSeedRootE i) 0 0) x) =
      twoSeedRootH i x := by
  have h := (ρPTE 2).comm (twoSeedRootE i) (negativeIndex i) 0 0 0 0 x
  have h' :
      (ρPTE 2).op (twoSeedRootE i) 0 0
        ((ρPTE 2).op (negativeIndex i) 0 0 x) -
      (ρPTE 2).op (negativeIndex i) 0 0
        ((ρPTE 2).op (twoSeedRootE i) 0 0 x) =
        ∑ c : Fin 28, D4sector.f (twoSeedRootE i) (negativeIndex i) c •
          (ρPTE 2).op c 0 0 x := by
    simpa only [Nat.zero_add, if_pos (by omega)] using h
  simp only [twoSeedRootH, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply,
    map_smul, Finset.smul_sum, smul_smul]
  rw [← smul_sub, h', Finset.smul_sum]
  simp only [smul_smul]

theorem two_seed_rootHF (i : Fin 12) (s : ℕ) (hs : s ≤ 1) (x : PTE 2) :
    twoSeedRootH i ((ρPTE 2).op (negativeIndex i) 0 s x) -
      (ρPTE 2).op (negativeIndex i) 0 s (twoSeedRootH i x) =
        (-2 : ℂ) • (ρPTE 2).op (negativeIndex i) 0 s x := by
  have hin : ∀ c y,
      (ρPTE 2).op c 0 0 ((ρPTE 2).op (negativeIndex i) 0 s y) -
      (ρPTE 2).op (negativeIndex i) 0 s ((ρPTE 2).op c 0 0 y) =
        ∑ d : Fin 28, D4sector.f c (negativeIndex i) d •
          (ρPTE 2).op d 0 s y := by
    intro c y
    have h := (ρPTE 2).comm c (negativeIndex i) 0 0 0 s y
    rw [if_pos (by omega)] at h
    simpa only [Nat.zero_add] using h
  calc
    twoSeedRootH i ((ρPTE 2).op (negativeIndex i) 0 s x) -
        (ρPTE 2).op (negativeIndex i) 0 s (twoSeedRootH i x) =
        (twoSeedRootSign i : ℂ) •
          ∑ c : Fin 28, D4sector.f (twoSeedRootE i) (negativeIndex i) c •
            ((ρPTE 2).op c 0 0 ((ρPTE 2).op (negativeIndex i) 0 s x) -
              (ρPTE 2).op (negativeIndex i) 0 s ((ρPTE 2).op c 0 0 x)) := by
          simp only [twoSeedRootH, LinearMap.smul_apply, LinearMap.coe_sum,
            Finset.sum_apply, map_smul, map_sum, smul_sub, Finset.sum_sub_distrib]
    _ = (twoSeedRootSign i : ℂ) •
        ∑ d : Fin 28,
          (∑ c : Fin 28, D4sector.f (twoSeedRootE i) (negativeIndex i) c *
            D4sector.f c (negativeIndex i) d) • (ρPTE 2).op d 0 s x := by
          simp only [hin, Finset.smul_sum, smul_smul]
          rw [Finset.sum_comm]
          simp only [Finset.sum_smul, Finset.mul_sum]
    _ = (-2 : ℂ) • (ρPTE 2).op (negativeIndex i) 0 s x := by
          simp only [Finset.smul_sum, smul_smul, root_double, ite_smul, zero_smul,
            Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem two_seed_rootH_zero (i : Fin 12) (s : ℕ) (hs : s ≤ 1) :
    ((twoSeedRootSign i : ℂ) •
      ∑ c : Fin 28, D4sector.f (twoSeedRootE i) (negativeIndex i) c •
        (ρPTE 2).op c 0 s) twoQuadraticSeed = 0 := by
  have hz : (∑ c : Fin 28, D4sector.f (twoSeedRootE i) (negativeIndex i) c •
      (ρPTE 2).op c 0 s twoQuadraticSeed) = 0 := by
    apply Finset.sum_eq_zero
    intro c _
    by_cases hc : fZ br (twoSeedRootE i) (negativeIndex i) c = 0
    · change (fZ br (twoSeedRootE i) (negativeIndex i) c : ℂ) • _ = 0
      rw [hc, Int.cast_zero, zero_smul]
    · rw [two_seed_cartan_zero c (root_support i c hc) s hs]
      simp
  simp only [LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply, hz, smul_zero]

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.two_seed_rootEF
#print axioms VOA.DeligneAudit.Toroidal.two_seed_rootHF
#print axioms VOA.DeligneAudit.Toroidal.two_seed_rootH_zero
