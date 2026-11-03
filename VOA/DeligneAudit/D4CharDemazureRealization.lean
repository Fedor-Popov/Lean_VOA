import VOA.DeligneAudit.D4CharKeyOrbitGraded

/-! The unconditional all-degree D4 Levi bound and Demazure character realization. -/

namespace VOA.DeligneAudit.D4Char

open SectorWeyl UnivG DeligneSector.D4 D4Levi LeviKeyFiltration DeligneCharacter

noncomputable section

theorem d4_supported_graded_keys : SupportedGradedKeyBound := by
  intro n N i hk hd
  let R := ravFam D4sector n 0
  let ρ := univRepG D4sector.f R
  let w := wUG D4sector.f R
  let k := keyEnum n i
  let F := keyPrefix ρ w n i.val
  let T := keyPrefix ρ w n (i.val + 1)
  let S := keyLayer ρ w k
  let r := Module.finrank ℂ (S ⧸ F.comap S.subtype)
  let L := leviClassHilb (ksKeyClass n k) (N - k.degree)
  let P := projUG D4sector.f R N
  have h := univG_sat D4sector.f R
  have hF : F = higherOrbit ρ w n k := keyPrefix_eq_higher ρ w n h i.val i.isLt
  have hFP : F.map P ≤ F := by
    change (keyPrefix ρ w n i.val).map (projUG D4sector.f R N) ≤ _
    rw [projUG_keyPrefix]
    exact inf_le_right
  have hb : FiniteDimensional ℂ (((keyOrbit ρ w k).map P).map F.mkQ) ∧
      Module.finrank ℂ (((keyOrbit ρ w k).map P).map F.mkQ) ≤ L * r := by
    dsimp only [r, S, P]
    rw [projUG_keyOrbit, hF]
    exact universal_key_orbit_graded_bound n N k hk hd
  have hT : T = F ⊔ ⨆ _ : Fin 1, keyOrbit ρ w k := by
    change keyPrefix ρ w n (i.val + 1) =
      keyPrefix ρ w n i.val ⊔ ⨆ _ : Fin 1, keyOrbit ρ w k
    rw [keyPrefix_step ρ w n i.val i.isLt, iSup_unique]
  have hs := projected_step_rank P
    (currentGrading_idem (universalCurrentGrading (f := D4sector.f) R) N)
    F T hFP 1 (L * r) (fun _ : Fin 1 => keyOrbit ρ w k) hT
    (fun _ => hb.1) (fun _ => hb.2)
  have hr : r ≤ ksCorrectedBoxCount n k := d4_key_multiplicity_bound ρ w n h i
  have hstep : Module.finrank ℂ (StepQuot (gradedKeyPrefix ρ w n N) i.val) ≤
      L * r := by
    have hh := hs.2
    have heq : (fun j : ℕ => (keyPrefix ρ w n j).map P) =
        gradedKeyPrefix ρ w n N := by
      funext j
      exact projUG_keyPrefix R n N j
    change Module.finrank ℂ
      (StepQuot (fun j : ℕ => (keyPrefix ρ w n j).map P) i.val) ≤ (L * r) * 1 at hh
    rw [heq, mul_one] at hh
    exact hh
  change Module.finrank ℂ (StepQuot (gradedKeyPrefix ρ w n N) i.val) ≤
    gradedKeyContribution n k N
  rw [gradedKeyContribution, if_pos hd]
  exact hstep.trans ((Nat.mul_le_mul_left L hr).trans_eq (Nat.mul_comm _ _))

/-- L1: the sharp Levi character bounds every Sat module in every degree. -/
theorem d4_gradedLeviBound : GradedLeviBound :=
  gradedLeviBound_of_supported_keys d4_supported_graded_keys

theorem d4_finrank_cycDeg_le (n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : CurrentModule D4sector.f V) (w : V)
    (h : Sat D4sector.f ρ w (ravFam D4sector n 0)) (N : ℕ) :
    Module.finrank ℂ (cycDeg ρ w N) ≤ d4LeviHilb n N :=
  d4_gradedLeviBound n V ρ w h N

/-- The all-`n` Demazure realization hD, with no residual character or rank hypotheses. -/
theorem d4_demazureRealization :
    ∀ n, DemazureRealizationG D4sector (ravFam D4sector) D4Wp.hilbSeriesZ n :=
  d4_demazureRealization_of_gradedLeviBound d4_gradedLeviBound

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.d4_supported_graded_keys
#print axioms VOA.DeligneAudit.D4Char.d4_gradedLeviBound
#print axioms VOA.DeligneAudit.D4Char.d4_finrank_cycDeg_le
#print axioms VOA.DeligneAudit.D4Char.d4_demazureRealization
