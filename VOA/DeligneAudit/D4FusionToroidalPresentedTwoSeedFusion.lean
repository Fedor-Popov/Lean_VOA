import VOA.DeligneAudit.D4FusionToroidalPresentedTwoSeedSimple

/-! The eight composite negative roots follow from the four simple ones by brackets. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.D4FusionContact

noncomputable section

private def fusionA (c : Fin 28) : Fin 28 :=
  if c = 20 then 18 else if c = 21 then 18 else if c = 22 then 18 else
  if c = 23 then 20 else if c = 24 then 20 else if c = 25 then 21 else
  if c = 26 then 23 else 26

private def fusionB (c : Fin 28) : Fin 28 :=
  if c = 20 then 16 else if c = 21 then 17 else if c = 22 then 19 else
  if c = 23 then 17 else if c = 24 then 19 else if c = 25 then 19 else
  if c = 26 then 19 else 18

private def fusionCoeff (c : Fin 28) : ℤ := if c = 22 ∨ c = 23 then 1 else -1

private theorem fusion_bracketZ : ∀ c e : Fin 28, 20 ≤ c.val →
    fZ br (fusionA c) (fusionB c) e =
      if e = c then fusionCoeff c else 0 := by
  decide +kernel

private theorem fusion_bracket (c e : Fin 28) (hc : 20 ≤ c.val) :
    D4sector.f (fusionA c) (fusionB c) e =
      if e = c then (fusionCoeff c : ℂ) else 0 := by
  change (fZ br (fusionA c) (fusionB c) e : ℂ) = _
  rw [fusion_bracketZ c e hc]
  split_ifs <;> simp

private theorem fusion_parents : ∀ c : Fin 28, 20 ≤ c.val →
    16 ≤ (fusionA c).val ∧ (fusionA c).val < c.val ∧
    16 ≤ (fusionB c).val ∧ (fusionB c).val < c.val := by
  decide +kernel

private theorem fusion_coeff_ne_zero : ∀ c : Fin 28, 20 ≤ c.val →
    (fusionCoeff c : ℂ) ≠ 0 := by
  intro c _
  unfold fusionCoeff
  split_ifs <;> norm_num

theorem two_seed_all_negative_zero (s : ℕ) (hs : s ≤ 1) :
    ∀ c : Fin 28, 16 ≤ c.val →
      (ρPTE 2).op c 0 s twoQuadraticSeed = 0 := by
  have hall : ∀ n : ℕ, ∀ c : Fin 28, c.val = n → 16 ≤ c.val →
      ∀ t : ℕ, t ≤ 1 → (ρPTE 2).op c 0 t twoQuadraticSeed = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
        intro c hcn hc16 t ht
        by_cases hc20 : c.val < 20
        · obtain ⟨i, hi⟩ := negativeIndex_covers c hc16
          subst c
          have hsimple : i.val < 4 := by
            have ht : ∀ j : Fin 12, (negativeIndex j).val < 20 → j.val < 4 := by
              decide +kernel
            exact ht i hc20
          exact two_seed_lowering_zero i hsimple t ht
        · have hc20' : 20 ≤ c.val := by omega
          obtain ⟨ha16, ha, hb16, hb⟩ := fusion_parents c hc20'
          have hA := ih (fusionA c).val (by omega) (fusionA c) rfl ha16 0
            (by omega)
          have hB := ih (fusionB c).val (by omega) (fusionB c) rfl hb16 t ht
          have hcomm := (ρPTE 2).comm (fusionA c) (fusionB c)
            0 0 0 t twoQuadraticSeed
          rw [if_pos (by omega)] at hcomm
          have hsum : (∑ e : Fin 28,
              D4sector.f (fusionA c) (fusionB c) e •
                (ρPTE 2).op e 0 t twoQuadraticSeed) =
              (fusionCoeff c : ℂ) • (ρPTE 2).op c 0 t twoQuadraticSeed := by
            simp only [fusion_bracket c _ hc20', ite_smul, zero_smul,
              Finset.sum_ite_eq', Finset.mem_univ, if_true]
          have hcomm' : (0 : PTE 2) =
              (∑ e : Fin 28, D4sector.f (fusionA c) (fusionB c) e •
                (ρPTE 2).op e 0 t twoQuadraticSeed) := by
            simpa only [Nat.zero_add, hA, hB, map_zero, sub_zero] using hcomm
          have hz : (fusionCoeff c : ℂ) •
              (ρPTE 2).op c 0 t twoQuadraticSeed = 0 :=
            (hcomm'.trans hsum).symm
          exact (smul_eq_zero.mp hz).resolve_left
            (fusion_coeff_ne_zero c hc20')
  intro c hc
  exact hall c.val c rfl hc s hs

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.two_seed_all_negative_zero
