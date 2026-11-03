import VOA.DeligneAudit.D4FusionToroidalPresentedOneLowSl2

/-! Every zero-mode lowering colour kills the one-top vector. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.D4FusionContact

noncomputable section

private abbrev ρ := univRepG D4sector.f OneR

private def rootE (i : Fin 12) : Fin 28 := ⟨i.val + 4, by omega⟩
private def rootSign (i : Fin 12) : ℤ := if i.val < 4 then 1 else -1

private def rootH (i : Fin 12) : OneU →ₗ[ℂ] OneU :=
  (rootSign i : ℂ) •
    (∑ c : Fin 28, D4sector.f (rootE i) (negativeIndex i) c • ρ.op c 0)

private theorem root_support : ∀ i : Fin 12, ∀ c : Fin 28,
    fZ br (rootE i) (negativeIndex i) c ≠ 0 → c.val < 4 := by
  decide +kernel

private theorem root_doubleZ : ∀ i : Fin 12, ∀ d : Fin 28,
    rootSign i *
      (∑ c : Fin 28, fZ br (rootE i) (negativeIndex i) c *
        fZ br c (negativeIndex i) d) =
      if d = negativeIndex i then -2 else 0 := by
  decide +kernel

private theorem root_double (i : Fin 12) (d : Fin 28) :
    (rootSign i : ℂ) *
      (∑ c : Fin 28, D4sector.f (rootE i) (negativeIndex i) c *
        D4sector.f c (negativeIndex i) d) =
      if d = negativeIndex i then (-2 : ℂ) else 0 := by
  change (rootSign i : ℂ) *
    (∑ c : Fin 28, (fZ br (rootE i) (negativeIndex i) c : ℂ) *
      (fZ br c (negativeIndex i) d : ℂ)) = _
  have h := root_doubleZ i d
  split_ifs at h ⊢ <;> exact_mod_cast h

private theorem rootEF (i : Fin 12) (x : OneU) :
    ((rootSign i : ℂ) • ρ.op (rootE i) 0)
      (ρ.op (negativeIndex i) 0 x) -
      ρ.op (negativeIndex i) 0
        (((rootSign i : ℂ) • ρ.op (rootE i) 0) x) = rootH i x := by
  have h := ρ.comm (rootE i) (negativeIndex i) 0 0 x
  have h' : ρ.op (rootE i) 0 (ρ.op (negativeIndex i) 0 x) -
      ρ.op (negativeIndex i) 0 (ρ.op (rootE i) 0 x) =
        ∑ c : Fin 28, D4sector.f (rootE i) (negativeIndex i) c • ρ.op c 0 x := by
    simpa only [Nat.zero_add] using h
  simp only [rootH, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply,
    map_smul, LinearMap.smul_apply, Finset.smul_sum, smul_smul]
  rw [← smul_sub, h', Finset.smul_sum]
  simp only [smul_smul]

private theorem rootHF (i : Fin 12) (x : OneU) :
    rootH i (ρ.op (negativeIndex i) 0 x) -
      ρ.op (negativeIndex i) 0 (rootH i x) =
        (-2 : ℂ) • ρ.op (negativeIndex i) 0 x := by
  have hin : ∀ c y,
      ρ.op c 0 (ρ.op (negativeIndex i) 0 y) -
        ρ.op (negativeIndex i) 0 (ρ.op c 0 y) =
          ∑ d : Fin 28, D4sector.f c (negativeIndex i) d • ρ.op d 0 y :=
    fun c y => by simpa using ρ.comm c (negativeIndex i) 0 0 y
  calc
    rootH i (ρ.op (negativeIndex i) 0 x) -
        ρ.op (negativeIndex i) 0 (rootH i x) =
        (rootSign i : ℂ) •
          ∑ c : Fin 28, D4sector.f (rootE i) (negativeIndex i) c •
            (ρ.op c 0 (ρ.op (negativeIndex i) 0 x) -
              ρ.op (negativeIndex i) 0 (ρ.op c 0 x)) := by
          simp only [rootH, LinearMap.smul_apply, LinearMap.coe_sum,
            Finset.sum_apply, map_smul, map_sum, smul_sub, Finset.sum_sub_distrib]
    _ = (rootSign i : ℂ) •
        ∑ d : Fin 28,
          (∑ c : Fin 28, D4sector.f (rootE i) (negativeIndex i) c *
            D4sector.f c (negativeIndex i) d) • ρ.op d 0 x := by
          simp only [hin, Finset.smul_sum, smul_smul]
          rw [Finset.sum_comm]
          simp only [Finset.sum_smul, Finset.mul_sum]
    _ = (-2 : ℂ) • ρ.op (negativeIndex i) 0 x := by
          simp only [Finset.smul_sum, smul_smul, root_double, ite_smul, zero_smul,
            Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem rootH_top (i : Fin 12) : rootH i oneTop = 0 := by
  have hs : (∑ c : Fin 28,
      D4sector.f (rootE i) (negativeIndex i) c • ρ.op c 0 oneTop) = 0 := by
    apply Finset.sum_eq_zero
    intro c _
    by_cases hfc : fZ br (rootE i) (negativeIndex i) c = 0
    · change (fZ br (rootE i) (negativeIndex i) c : ℂ) • ρ.op c 0 oneTop = 0
      rw [hfc, Int.cast_zero, zero_smul]
    · rw [one_top_mode_zero_cartan c (root_support i c hfc)]
      simp
  simp only [rootH, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply, hs, smul_zero]

theorem one_top_mode_zero_lowering (i : Fin 12) :
    ρ.op (negativeIndex i) 0 oneTop = 0 := by
  letI : FiniteDimensional ℂ OneU := rav_finiteDimensional 1 (by omega)
  let E := (rootSign i : ℂ) • ρ.op (rootE i) 0
  let F := ρ.op (negativeIndex i) 0
  let H := rootH i
  have he : 4 ≤ (rootE i).val ∧ (rootE i).val < 16 := by
    simp only [rootE, Fin.val_mk]
    omega
  have hEtop : E oneTop = 0 := by
    change (rootSign i : ℂ) • ρ.op (rootE i) 0 oneTop = 0
    rw [one_top_mode_zero_raising (rootE i) he, smul_zero]
  have hHtop : H oneTop = 0 := rootH_top i
  have hEF : ∀ x, E (F x) - F (E x) = H x := rootEF i
  have hHF : ∀ x, H (F x) - F (H x) = (-2 : ℂ) • F x := rootHF i
  have hEv : E (F oneTop) = 0 := by
    have h := hEF oneTop
    rw [hEtop, map_zero, sub_zero, hHtop] at h
    exact h
  have hHv : H (F oneTop) = (-2 : ℂ) • F oneTop := by
    have h := hHF oneTop
    rw [hHtop, map_zero, sub_zero] at h
    exact h
  exact sl2_negative_two_of_finite E F H hEF hHF (F oneTop) hEv hHv

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.one_top_mode_zero_lowering
