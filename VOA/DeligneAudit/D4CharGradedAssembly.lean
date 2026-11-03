import VOA.DeligneAudit.D4CharGradedKeyCount
import VOA.DeligneAudit.D4CharGradedFiltration
import VOA.DeligneAudit.D4CharRealizationSqueeze

/-! The remaining L1 input consists only of the supported graded key quotients. -/

namespace VOA.DeligneAudit.D4Char

open SectorWeyl UnivG DeligneSector.D4 D4Levi LeviKeyFiltration
open DeligneCharacter

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- A zero ungraded quotient gives a zero quotient after intersecting with any degree. -/
theorem intersect_quotient_rank_zero (G F T : Submodule ℂ V)
    [FiniteDimensional ℂ (T ⧸ F.comap T.subtype)]
    (hz : Module.finrank ℂ (T ⧸ F.comap T.subtype) = 0) :
    Module.finrank ℂ ((G ⊓ T : Submodule ℂ V) ⧸
      (G ⊓ F).comap (G ⊓ T).subtype) = 0 := by
  haveI : Subsingleton (T ⧸ F.comap T.subtype) :=
    (Module.finrank_zero_iff (R := ℂ)).mp hz
  have ht : T ≤ F := by
    intro v hv
    have hq : (F.comap T.subtype).mkQ ⟨v, hv⟩ = 0 := Subsingleton.elim _ _
    exact (Submodule.Quotient.mk_eq_zero (F.comap T.subtype)).mp hq
  have he : (G ⊓ F).comap (G ⊓ T).subtype = ⊤ := by
    apply top_unique
    intro v _
    exact ⟨v.property.1, ht v.property.2⟩
  rw [he]
  exact Module.finrank_zero_of_subsingleton

theorem gradedKeyStep_unsupported (n : ℕ) (ρ : CurrentModule D4sector.f V) (w : V)
    (h : Sat D4sector.f ρ w (ravFam D4sector n 0)) (N : ℕ)
    (i : Fin (globalKeyBox n).card)
    (hk : ¬ ksCorrectedSupported n (keyEnum n i)) :
    Module.finrank ℂ (StepQuot (gradedKeyPrefix ρ w n N) i.val) = 0 := by
  have hb := keyPrefix_step_rank ρ w n h i.val i.isLt
  have hm := d4_key_multiplicity_bound ρ w n h i
  rw [ksCorrectedBoxCount_zero_of_not_supported n (keyEnum n i) hk] at hm
  haveI := hb.1
  have hz : Module.finrank ℂ (StepQuot (keyPrefix ρ w n) i.val) = 0 := by
    have he : Module.finrank ℂ
        (keyLayer ρ w (keyEnum n i) ⧸ (keyPrefix ρ w n i.val).comap
          (keyLayer ρ w (keyEnum n i)).subtype) = 0 := Nat.eq_zero_of_le_zero hm
    have hh := hb.2
    rw [he, mul_zero] at hh
    exact Nat.eq_zero_of_le_zero hh
  exact intersect_quotient_rank_zero (cycDeg ρ w N)
    (keyPrefix ρ w n i.val) (keyPrefix ρ w n (i.val + 1)) hz

theorem gradedKeyStep_above_degree (R : RelSpec 28) (n N : ℕ)
    (i : Fin (globalKeyBox n).card) (hi : N < (keyEnum n i).degree) :
    Module.finrank ℂ (StepQuot
      (gradedKeyPrefix (univRepG D4sector.f R) (wUG D4sector.f R) n N) i.val) = 0 := by
  change Module.finrank ℂ
    (gradedKeyPrefix (univRepG D4sector.f R) (wUG D4sector.f R) n N (i.val + 1) ⧸
      (gradedKeyPrefix (univRepG D4sector.f R) (wUG D4sector.f R) n N i.val).comap
        (gradedKeyPrefix (univRepG D4sector.f R) (wUG D4sector.f R)
          n N (i.val + 1)).subtype) = 0
  rw [gradedKeyPrefix_univ_step R n N i.val i.isLt,
    gradedKeyOrbit_eq_bot_of_lt _ _ _ _ hi, sup_bot_eq]
  have he : ∀ S : Submodule ℂ (UModG D4sector.f R), S.comap S.subtype = ⊤ := by
    intro S
    ext v
    simp
  rw [he]
  exact Module.finrank_zero_of_subsingleton

/-- Sharp type-A estimates are needed only for supported keys below the requested degree. -/
def SupportedGradedKeyBound : Prop :=
  ∀ n N : ℕ, ∀ i : Fin (globalKeyBox n).card,
    ksCorrectedSupported n (keyEnum n i) → (keyEnum n i).degree ≤ N →
      Module.finrank ℂ (StepQuot
        (gradedKeyPrefix (univRepG D4sector.f (ravFam D4sector n 0))
          (wUG D4sector.f (ravFam D4sector n 0)) n N) i.val) ≤
        gradedKeyContribution n (keyEnum n i) N

theorem gradedLeviBound_of_supported_keys (hkeys : SupportedGradedKeyBound) :
    GradedLeviBound := by
  apply gradedLeviBound_iff_universal.mpr
  intro n N
  let ρ := univRepG D4sector.f (ravFam D4sector n 0)
  let w := wUG D4sector.f (ravFam D4sector n 0)
  have h := univG_sat D4sector.f (ravFam D4sector n 0)
  have hs (i : Fin (globalKeyBox n).card) :
      Module.finrank ℂ (StepQuot (gradedKeyPrefix ρ w n N) i.val) ≤
        gradedKeyContribution n (keyEnum n i) N := by
    by_cases hk : ksCorrectedSupported n (keyEnum n i)
    · by_cases hd : (keyEnum n i).degree ≤ N
      · exact hkeys n N i hk hd
      · rw [gradedKeyStep_above_degree _ n N i (Nat.lt_of_not_ge hd)]
        exact Nat.zero_le _
    · rw [gradedKeyStep_unsupported n ρ w h N i hk]
      exact Nat.zero_le _
  calc
    Module.finrank ℂ (cycDeg ρ w N) =
        ∑ i : Fin (globalKeyBox n).card,
          Module.finrank ℂ (StepQuot (gradedKeyPrefix ρ w n N) i.val) := by
      rw [Finset.sum_fin_eq_sum_range]
      rw [d4_degree_finrank_eq_steps n ρ w h N]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_range.mp hi, dif_pos]
    _ ≤ ∑ i : Fin (globalKeyBox n).card,
        gradedKeyContribution n (keyEnum n i) N := Finset.sum_le_sum (fun i _ => hs i)
    _ ≤ d4LeviHilb n N := gradedKeyContribution_enum_sum_le n N

theorem d4_demazureRealization_of_supported_keys (hkeys : SupportedGradedKeyBound) :
    ∀ n, DemazureRealizationG D4sector (ravFam D4sector) D4Wp.hilbSeriesZ n :=
  d4_demazureRealization_of_gradedLeviBound (gradedLeviBound_of_supported_keys hkeys)

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.intersect_quotient_rank_zero
#print axioms VOA.DeligneAudit.D4Char.gradedKeyStep_unsupported
#print axioms VOA.DeligneAudit.D4Char.gradedKeyStep_above_degree
#print axioms VOA.DeligneAudit.D4Char.gradedLeviBound_of_supported_keys
#print axioms VOA.DeligneAudit.D4Char.d4_demazureRealization_of_supported_keys
