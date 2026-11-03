import VOA.DeligneAudit.D4FusionToroidalPresentedTwoZero

/-! Cyclicity and the sharp rank bound for the zero-u-degree quotient. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector

noncomputable section

def twoZeroLetters (l : List (TLtr 28)) : List (Ltr 28) :=
  l.map fun x => (x.1, x.2.2)

theorem two_pure_word (l : List (TLtr 28)) (hl : twoUDeg l = 0) :
    (twoN 1).mkQ (wordOpT (ρPTE 2) l (pTE 2)) =
      wordOp twoZeroCurrent (twoZeroLetters l) twoZeroGen := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      have hi : x.2.1 = 0 := by
        simp only [twoUDeg] at hl
        omega
      have hrest : twoUDeg l = 0 := by
        simp only [twoUDeg] at hl
        omega
      simp only [twoZeroLetters, List.map_cons, wordOpT, wordOp]
      simp only [twoZeroLetters] at ih
      rw [← ih hrest]
      change (twoN 1).mkQ _ =
        (quotRepG twoCurrent (twoN 1) twoCurrent_inv).op x.1 x.2.2
          ((twoN 1).mkQ (wordOpT (ρPTE 2) l (pTE 2)))
      rw [quotRepG_op]
      by_cases hs : x.2.2 < 2
      · have hs' : x.2.2 ≤ 1 := by omega
        simp [twoCurrent, hi, hs']
      · have hz := (ρPTE 2).high_zero x.1 x.2.1 x.2.2 (by omega)
        have hn : ¬ x.2.2 ≤ 1 := by omega
        simp [twoCurrent, hn, hz]

theorem two_zero_cyclic : cycSubG twoZeroCurrent twoZeroGen = ⊤ := by
  have hall : ∀ y : PTE 2,
      (twoN 1).mkQ y ∈ cycSubG twoZeroCurrent twoZeroGen := by
    intro y
    have hy : y ∈ Submodule.span ℂ
        (Set.range fun l : List (TLtr 28) => wordOpT (ρPTE 2) l (pTE 2)) := by
      rw [PTE_cyclic 2]
      exact Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨l, rfl⟩ := hy
        by_cases hd : 1 ≤ twoUDeg l
        · have hz : (twoN 1).mkQ (wordOpT (ρPTE 2) l (pTE 2)) = 0 :=
            (Submodule.Quotient.mk_eq_zero _).mpr (twoN_word 1 l hd)
          rw [hz]
          exact Submodule.zero_mem _
        · have hzero : twoUDeg l = 0 := by omega
          rw [two_pure_word l hzero]
          exact wordOp_mem_cycSubG twoZeroCurrent twoZeroGen _
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | smul a x _ hx => simpa only [map_smul] using Submodule.smul_mem _ a hx
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (twoN 1) x
  exact hall y

theorem two_zero_rank_bound :
    FiniteDimensional ℂ twoZeroQuot ∧ Module.finrank ℂ twoZeroQuot ≤ 784 := by
  let spec := lwSpec D4sector 2
  have hU := univ_localWeylRelG D4sector 2
  letI : FiniteDimensional ℂ D4FusionContact.Polynomial.M2Model :=
    D4FusionContact.Polynomial.m2Model_finite
  letI : FiniteDimensional ℂ
      (D4FusionContact.Polynomial.universalPBWGr spec) :=
    Module.Finite.of_surjective (D4FusionContact.Polynomial.m2ModelMap hU)
      (D4FusionContact.Polynomial.m2ModelMap_surjective hU)
  have hsource := D4FusionContact.Polynomial.universal_source_bound spec
    D4FusionContact.Polynomial.m2_universal_highest
  letI : FiniteDimensional ℂ (UModG D4sector.f spec) := hsource.1
  have hs : Sat D4sector.f twoZeroCurrent twoZeroGen spec :=
    (localWeylRelG_iff D4sector twoZeroCurrent twoZeroGen 2).mp two_zero_localWeyl
  have hsurj : Function.Surjective (univMapG hs) := by
    apply LinearMap.range_eq_top.mp
    apply top_unique
    rw [← two_zero_cyclic, cycSubG, Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    exact ⟨wordOp (univRepG D4sector.f spec) l (wUG D4sector.f spec),
      univMapG_wordOp hs l⟩
  letI : FiniteDimensional ℂ twoZeroQuot :=
    Module.Finite.of_surjective (univMapG hs) hsurj
  have hpbw : Module.finrank ℂ
      (D4FusionContact.Polynomial.universalPBWGr spec) ≤ 784 :=
    (LinearMap.finrank_le_finrank_of_surjective
      (D4FusionContact.Polynomial.m2ModelMap_surjective hU)).trans
        D4FusionContact.Polynomial.m2Model_finrank_le
  exact ⟨inferInstance, (LinearMap.finrank_le_finrank_of_surjective hsurj).trans
    (hsource.2.trans hpbw)⟩

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.two_pure_word
#print axioms VOA.DeligneAudit.Toroidal.two_zero_cyclic
#print axioms VOA.DeligneAudit.Toroidal.two_zero_rank_bound
