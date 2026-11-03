import VOA.Classification.COne.OrbIcoZTop
import VOA.Classification.COne.OrbIcoSDesc

/-! The absent weight-four primary and the initial condition for the mode recurrence. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbOdd OrbSpan OrbPrim OrbIco OrbIcoS OrbOctaR OrbC2b OrbC2c OrbZhu


/-- There are no positive-weight icosahedral primaries below weight thirty-six. -/
theorem ico_prim_low_zero {N : ℤ} (hpos : 0 < N) (hN : N < 36)
    {y : (orbifold ico).carrier} (hy : y ∈ prim Wi N) : y = 0 := by
  have hg := ((mem_prim _).mp hy).1
  have hs := grading_lt_100 N (by omega) hg
  have hl : ∀ z ∈ OrbIcoS.twoSeedSpan, piHom Wi N z ∈ lowerDesc Wi N := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨ks, rfl | rfl⟩ := hz
      · have hw := virWord_grading Wi Wi.vacuum_mem ks
        by_cases he : 0 + (OrbOctaR.wordWeight ks : ℤ) = N
        · rw [piHom_of_mem Wi (he ▸ hw)]
          cases ks with
          | nil => simp [OrbOctaR.wordWeight] at he; omega
          | cons k ks =>
            refine Submodule.subset_span ⟨k, virWord Wi ks Wi.vacuum, ?_, rfl⟩
            have ht := virWord_grading Wi Wi.vacuum_mem ks
            have hh : N - (k : ℤ) - 1 = 0 + (OrbOctaR.wordWeight ks : ℤ) := by
              simp only [OrbOctaR.wordWeight, List.map_cons, List.sum_cons, Nat.cast_add,
                Nat.cast_one] at he ⊢
              omega
            rw [hh]; exact ht
        · rw [piHom_of_mem_ne Wi he hw]
          exact Submodule.zero_mem _
      · have hw := virWord_grading Wi Xico_grading ks
        rw [piHom_of_mem_ne Wi (by omega : (36 : ℤ) + OrbOctaR.wordWeight ks ≠ N) hw]
        exact Submodule.zero_mem _
    | zero => simp
    | add z t _ _ hz ht => rw [map_add]; exact Submodule.add_mem _ hz ht
    | smul c z _ hz => rw [map_smul]; exact Submodule.smul_mem _ c hz
  have hmem : y ∈ prim Wi N ⊓ lowerDesc Wi N :=
    ⟨hy, by simpa only [piHom_of_mem Wi hg] using hl y hs⟩
  rw [prim_inf_lowerDesc (W := Wi)
    ((v2VirUnitary_holds.some).restrict (orbifold ico)) N] at hmem
  exact (Submodule.mem_bot ℂ).mp hmem

/-- The first five coefficients in the vacuum channel, with top mode as the seed. -/
def lowWords : ℕ → VVec
  | 0 => [(1, [])]
  | 1 => []
  | 2 => [(72, [2])]
  | 3 => [(36, [3])]
  | 4 => [(-268, [4]), (1448/3, [2, 2])]
  | _ => []

def lowExtra1 : ℕ → VVec
  | 2 => [(216, [1])]
  | 4 => [(2896, [2, 1])]
  | _ => []

def lowExtra2 : ℕ → VVec
  | 3 => [(180, [1])]
  | _ => []

def lowCheckV (m : ℕ) (v r : VVec) : Bool :=
  match bindV (lowerF 0 1 64 m) v with
  | some t => isZeroK (normK (t ++ scaleV (-1) r))
  | none => false

theorem lowCheck_one : ∀ n : Fin 4,
    lowCheckV 1 (lowWords (n + 1))
      (scaleV (n : ℚ) (lowWords n) ++ lowExtra1 (n + 1)) = true := by decide +kernel

theorem lowCheck_two : ∀ n : Fin 3,
    lowCheckV 2 (lowWords (n + 2))
      (scaleV ((n : ℚ) + 36) (lowWords n) ++ lowExtra2 (n + 2)) = true := by decide +kernel

theorem lowWords_spec : ∀ n : Fin 5, ∀ p ∈ lowWords n, p.2.sum = n := by decide +kernel

private abbrev topState := Wi.smul Xico 71 Xico

private theorem topState_grading : topState ∈ Wi.grading 0 := by
  convert Wi.grading_mode _ Xico_grading _ Xico_grading 71 using 2

private theorem topState_Lneg1 : Wi.L (-1) topState = 0 := by
  change Wi.L (-1) (Wi.smul Xico 71 Xico) = 0
  have h := topState_grading
  rw [Wi.vacuum_grade, Submodule.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  change Wi.L (-1) topState = 0
  rw [← hc, map_smul, L_neg_one_vacuum, smul_zero]

private theorem topState_pos : ∀ m : ℕ, 1 ≤ m → Wi.L (m : ℤ) topState = 0 := by
  intro m hm
  have h := L_mem_grading_ Wi topState_grading (m : ℤ)
  rw [Wi.positivity _ (by omega)] at h
  exact (Submodule.mem_bot ℂ).mp h

private theorem lowCheckV_sound {m : ℕ} {v r : VVec} (hk : lowCheckV m v r = true) :
    Wi.L (m : ℤ) (evV Wi topState v) = evV Wi topState r := by
  have hc : Wi.centralCharge = ((1 : ℚ) : ℂ) := by
    change (V2m 1 le_rfl).centralCharge = _
    simpa using V2m_centralCharge 1 le_rfl
  have hz : Wi.L 0 topState = ((0 : ℚ) : ℂ) • topState := by
    rw [Wi.L_zero_grading _ topState_grading]; norm_num
  unfold lowCheckV at hk
  split at hk
  · rename_i t ht
    have he := evV_eq_zero_of_isZeroK (W := Wi) (x := topState) hk
    rw [evV_append, evV_scaleV,
      bindV_sound (fun w r h => lowerF_sound hc topState_pos hz _ _ w r h) v t ht] at he
    simpa only [Rat.cast_neg, Rat.cast_one, neg_one_smul, add_neg_eq_zero] using he
  · exact absurd hk (by simp)

private theorem lowWords_L1 (n : ℕ) (hn : n < 4) :
    Wi.L 1 (evV Wi topState (lowWords (n + 1))) =
      (n : ℂ) • evV Wi topState (lowWords n) := by
  have h := lowCheckV_sound (lowCheck_one ⟨n, hn⟩)
  rw [evV_append, evV_scaleV] at h
  have hz : evV Wi topState (lowExtra1 (n + 1)) = 0 := by
    interval_cases n <;> simp [lowExtra1, evV, evW, topState_Lneg1]
  simpa only [hz, add_zero, Rat.cast_natCast] using h

private theorem lowWords_L2 (n : ℕ) (hn : n < 3) :
    Wi.L 2 (evV Wi topState (lowWords (n + 2))) =
      ((n : ℂ) + 36) • evV Wi topState (lowWords n) := by
  have h := lowCheckV_sound (lowCheck_two ⟨n, hn⟩)
  rw [evV_append, evV_scaleV] at h
  have hz : evV Wi topState (lowExtra2 (n + 2)) = 0 := by
    interval_cases n <;> simp [lowExtra2, evV, evW, topState_Lneg1]
  simpa only [hz, add_zero, Rat.cast_add, Rat.cast_natCast, Rat.cast_ofNat] using h

private abbrev selfState (n : ℕ) := Wi.smul Xico (71 - (n : ℤ)) Xico

private theorem X_pos : ∀ m : ℕ, 1 ≤ m → Wi.L (m : ℤ) Xico = 0 := by
  intro m hm
  have h := ((mem_prim _).mp X_primary).2 (m - 1)
  rwa [show ((m - 1 : ℕ) : ℤ) + 1 = m by omega] at h

private theorem X_L1 : Wi.L 1 Xico = 0 := by simpa using X_pos 1 (by decide)
private theorem X_L2 : Wi.L 2 Xico = 0 := by simpa using X_pos 2 (by decide)

private theorem selfState_grading (n : ℕ) : selfState n ∈ Wi.grading n := by
  convert Wi.grading_mode _ Xico_grading _ Xico_grading (71 - (n : ℤ)) using 2
  ring

private theorem selfState_L1 (n : ℕ) : Wi.L 1 (selfState (n + 1)) =
    (n : ℂ) • selfState n := by
  rw [selfState, L_smul_primary Xico_grading X_pos, X_L1,
    PreVertexAlgebra.smul_zero_right, zero_add]
  congr 1 <;> push_cast <;> ring

private theorem selfState_L2 (n : ℕ) : Wi.L 2 (selfState (n + 2)) =
    ((n : ℂ) + 36) • selfState n := by
  rw [selfState, L_smul_primary Xico_grading X_pos, X_L2,
    PreVertexAlgebra.smul_zero_right, zero_add]
  congr 1 <;> push_cast <;> ring

private theorem selfState_L2_one : Wi.L 2 (selfState 1) = 0 := by
  rw [selfState, L_smul_primary Xico_grading X_pos, X_L2,
    PreVertexAlgebra.smul_zero_right, zero_add]
  have hg := Wi.grading_mode _ Xico_grading _ Xico_grading 72
  norm_num only at hg ⊢
  rw [Wi.positivity _ (by norm_num)] at hg
  have hz : Wi.smul Xico 72 Xico = 0 := (Submodule.mem_bot ℂ).mp hg
  rw [hz, smul_zero]

theorem selfState_low (n : ℕ) (hn : n ≤ 4) :
    selfState n = evV Wi topState (lowWords n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [selfState, lowWords, evV, evW, topState]
    | succ n =>
      apply sub_eq_zero.mp
      apply ico_prim_low_zero (N := ((n + 1 : ℕ) : ℤ)) (by omega) (by omega)
      rw [mem_prim]
      refine ⟨Submodule.sub_mem _ (selfState_grading _) ?_, fun m => ?_⟩
      · have h := evV_mem_grading topState_grading
          (fun p hp => lowWords_spec ⟨n + 1, by omega⟩ p hp)
        simpa only [zero_add] using h
      · have h1 : Wi.L 1 (selfState (n + 1) - evV Wi topState (lowWords (n + 1))) = 0 := by
          rw [map_sub, selfState_L1, lowWords_L1 n (by omega), ih n (by omega) (by omega),
            sub_self]
        have h2 : Wi.L 2 (selfState (n + 1) - evV Wi topState (lowWords (n + 1))) = 0 := by
          rcases n with _ | n
          · rw [map_sub, selfState_L2_one]
            simp [lowWords, evV]
          · rw [show n + 1 + 1 = n + 2 by omega, map_sub, selfState_L2,
              lowWords_L2 n (by omega), ih n (by omega) (by omega), sub_self]
        have h := L_pos_of_L1_L2 h1 h2 (m + 1) (by omega)
        simpa using h

/-- The only low-primary-channel input needed by the finite P25 certificate. -/
theorem low_mode67 : selfMode 67 =
    Polynomial.aeval (omegaL Wi) (zp [0, 484/3, 1448/3]) (selfMode 71) := by
  have h := congrArg (mk Wi) (selfState_low 4 (by decide))
  have hp : posV (lowWords 4) = true := by decide +kernel
  rw [mk_evV Wi topState_grading _ hp] at h
  have hc : ptrim (zhuV 0 (lowWords 4)) = [0, 484/3, 1448/3] := by decide +kernel
  simp only [Nat.cast_zero] at h
  rw [← zp_ptrim, hc] at h
  exact h

end VOA.Classification.COne.OrbIcoZ
