import VOA.DeligneAudit.D4LeviKSKeyMultiplicity

/-! The all-m D4 Demazure rank bound from the completed Levi multiplicity proof. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

theorem ksXYZKey_pairFinalKey (k : RadicalKey)
    (he : k.e = 0) (hu : k.u = 0) (hup : k.up = 0) (hy : k.y ≤ k.x) :
    k = pairFinalKey (k.x - k.y) k.y k.z k.degree := by
  cases k with
  | mk e x u up y z degree =>
      change e = 0 at he
      change u = 0 at hu
      change up = 0 at hup
      change y ≤ x at hy
      simp [pairFinalKey, he, hu, hup, Nat.sub_add_cancel hy]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Every ordered key quotient satisfies the corrected graded multiplicity bound. -/
theorem d4_key_multiplicity_bound (ρ : CurrentModule D4sector.f V) (w : V)
    (m : ℕ) (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (i : Fin (globalKeyBox m).card) :
    Module.finrank ℂ
      (keyLayer ρ w (keyEnum m i) ⧸ (keyPrefix ρ w m i.val).comap
        (keyLayer ρ w (keyEnum m i)).subtype) ≤
      ksCorrectedBoxCount m (keyEnum m i) := by
  classical
  let k := keyEnum m i
  by_cases he : k.e = 0
  · by_cases hu : k.u = 0
    · by_cases hup : k.up = 0
      · by_cases hy : k.y ≤ k.x
        · have hk := ksXYZKey_pairFinalKey k he hu hup hy
          have hh := ksKey_quot_finrank_le_corrected ρ w m i.val
            (k.x - k.y) k.y k.z k.degree h i.isLt hk
          rw [← hk] at hh
          exact hh
        · have hneg : ∃ j : Fin 3, keyLabel m j k < 0 := by
            refine ⟨0, ?_⟩
            simp only [keyLabel, Fin.isValue, ↓reduceIte, hu, hup, Nat.cast_zero]
            omega
          have hle : keyLayer ρ w k ≤ keyPrefix ρ w m i.val := by
            rw [keyPrefix_eq_higher ρ w m h i.val i.isLt]
            exact keyLayer_le_higher_of_non_dominant ρ w m h k hneg
          rw [ksKey_quot_finrank_eq_image]
          have hz : (keyLayer ρ w k).map (keyPrefix ρ w m i.val).mkQ = ⊥ := by
            apply eq_bot_iff.mpr
            rintro v ⟨u, hu, rfl⟩
            change (keyPrefix ρ w m i.val).mkQ u = 0
            exact (Submodule.Quotient.mk_eq_zero _).mpr (hle hu)
          change Module.finrank ℂ
            ((keyLayer ρ w k).map (keyPrefix ρ w m i.val).mkQ) ≤ _
          rw [hz]
          simp
      · rw [keyQuot_finrank_zero_of_excluded ρ w m h i.val i.isLt
          (Or.inr (Or.inr hup))]
        exact Nat.zero_le _
    · rw [keyQuot_finrank_zero_of_excluded ρ w m h i.val i.isLt (Or.inr (Or.inl hu))]
      exact Nat.zero_le _
  · rw [keyQuot_finrank_zero_of_excluded ρ w m h i.val i.isLt (Or.inl he)]
    exact Nat.zero_le _

/-- Every saturated level-one D4 cyclic current module has rank at most `29^m`. -/
theorem d4_all_weight_rank (ρ : CurrentModule D4sector.f V) (w : V)
    (m : ℕ) (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) :
    FiniteDimensional ℂ (cycSubG ρ w) ∧ Module.finrank ℂ (cycSubG ρ w) ≤ 29 ^ m :=
  d4_rank_of_corrected_key_box_bounds ρ w m h (d4_key_multiplicity_bound ρ w m h)

/-- The unconditional, literature-free D4 level-one Demazure rank bound. -/
theorem d4_demazureUnivRank : DemazureUnivRank := by
  apply d4_demazureUnivRank_of_corrected_key_box_bounds
  intro m hm i
  exact d4_key_multiplicity_bound
    (univRepG D4sector.f (ravFam D4sector m 0))
    (wUG D4sector.f (ravFam D4sector m 0)) m
    (univG_sat D4sector.f (ravFam D4sector m 0)) i

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksXYZKey_pairFinalKey
#print axioms VOA.DeligneAudit.D4Levi.d4_key_multiplicity_bound
#print axioms VOA.DeligneAudit.D4Levi.d4_all_weight_rank
#print axioms VOA.DeligneAudit.D4Levi.d4_demazureUnivRank
