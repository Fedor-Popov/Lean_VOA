import VOA.DeligneAudit.D4LevelReductionCentralGraded

/-!
The descending current-degree filtration of the pure central multiplicity space.
Its homogeneous Grassmannian spanning fibers give the finite cyclic quotient bounds.
-/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.D4Levi
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)

/-- Pure central orbits of strictly higher current degree. -/
noncomputable def centralHigherDegree (a d : ℕ) : Submodule ℂ V :=
  ⨆ e : ℕ, ⨆ (_ : d < e), keyOrbit ρ w (centralLetterKey a e)

theorem centralHigherDegree_stable (a d : ℕ) (c : Fin 28) (r : ℕ) (hc : IsLevi c) :
    centralHigherDegree ρ w a d ≤ (centralHigherDegree ρ w a d).comap (ρ.op c r) := by
  apply iSup_le
  intro e
  apply iSup_le
  intro he v hv
  change ρ.op c r v ∈ centralHigherDegree ρ w a d
  exact Submodule.mem_iSup_of_mem e (Submodule.mem_iSup_of_mem he
    (levi_op_orbit ρ w (centralLetterKey a e) c r hc hv))

/-- No central orbit survives beyond the finite radical mode-degree bound. -/
theorem centralOrbit_eq_bot_of_degree_gt (m a d : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (hd : 2 * m * a < d) :
    keyOrbit ρ w (centralLetterKey a d) = ⊥ := by
  apply keyOrbit_eq_bot_of_keyLayer_bot
  apply keyLayer_eq_bot_of_degree_gt ρ w m h
  simpa [keyDepth, centralLetterKey] using hd

/-- The higher-degree filtration is supported on the same finite mode box. -/
theorem centralHigherDegree_le_finite (m a d : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) :
    centralHigherDegree ρ w a d ≤
      ⨆ e ∈ Finset.range (2 * m * a + 1), ⨆ (_ : d < e),
        keyOrbit ρ w (centralLetterKey a e) := by
  apply iSup_le
  intro e
  apply iSup_le
  intro he
  by_cases hd : e < 2 * m * a + 1
  · exact le_iSup_of_le e (le_iSup_of_le (Finset.mem_range.mpr hd)
      (le_iSup_of_le he le_rfl))
  · rw [centralOrbit_eq_bot_of_degree_gt ρ w m a e h (by omega)]
    exact bot_le

/-- A homogeneous central orbit quotient has the local exterior-square rank bound. -/
theorem centralOrbit_quotient_rank_le (b c d : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector (b + c) 0)) :
    Module.finrank ℂ ((keyOrbit ρ w (centralLetterKey c d)).map
      (centralHigherDegree ρ w c d ⊔
        levelFiltration ρ w (b + c) b ((b : ℤ) + 1)).mkQ) ≤
      6 ^ b * (centralGradedBox (b + c) c d).card := by
  let T := levelFiltration ρ w (b + c) b ((b : ℤ) + 1)
  let N := centralHigherDegree ρ w c d ⊔ T
  have hN : ∀ e r, IsLevi e → N ≤ N.comap (ρ.op e r) :=
    leviInvariant_sup ρ _ T (centralHigherDegree_stable ρ w c d)
      (levelFiltration_stable ρ w (b + c) b ((b : ℤ) + 1))
  have hdegree (s : ℕ) (hs : 0 < s) :
      keyLayer ρ w (centralLetterKey c (d + s)) ≤ N := by
    apply (keyLayer_le_orbit ρ w _).trans
    apply le_sup_of_le_left
    exact le_iSup_of_le (d + s) (le_iSup_of_le (by omega : d < d + s) le_rfl)
  have hpos : ∀ v ∈ keyLayer ρ w (centralLetterKey c d),
      ∀ r, 0 < r → ρ.op (0 : Fin 28) r v ∈ N := by
    intro v hv r hr
    apply hdegree r hr
    simpa [keyShift, centralLetterKey] using extra_pos_key ρ w (b + c) h r hr _ hv
  have hb := keyOrbit_quotient_rank_le ρ w (b + c) N hN h
    (centralLetterKey c d) (6 ^ b) hpos (by
      intro v hv
      apply centralKey_quotient_rank_le ρ w b c d h N
        (quotientLevi_invariant ρ N hN) le_sup_right hv
      intro i s hs
      change (leviSign (A3Sector.simpleH i) : ℂ) •
        ρ.op (leviColour (A3Sector.simpleH i)) s v ∈ N
      apply N.smul_mem
      apply hdegree s hs
      simpa [keyShift, centralLetterKey] using
        cartan_pos_maps_key ρ w (b + c) h i s hs _ hv)
  have hdim : Module.finrank ℂ
      (keyLayer ρ w (centralLetterKey c d) ⧸
        N.comap (keyLayer ρ w (centralLetterKey c d)).subtype) ≤
      (centralGradedBox (b + c) c d).card := by
    rw [ksKey_quot_finrank_eq_image]
    apply (SL4T.quotientImage_finrank_antitone _ T N le_sup_right).trans
    have hh := centralKey_quotient_finrank_le_gradedBox ρ w (b + c) c d (by omega) h
    dsimp only at hh
    have heq : levelFiltration ρ w (b + c) ((b + c : ℕ) - (c : ℤ))
        ((b + c : ℕ) - (c : ℤ) + 1) = T := by
      simp [T, Nat.cast_add]
    rw [heq, ksKey_quot_finrank_eq_image] at hh
    exact hh
  exact hb.2.trans (Nat.mul_le_mul_left _ hdim)

/-- The untruncated central boundary already has the binomial exterior-square bound. -/
theorem centralBoundary_rank_le (b c : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector (b + c) 0)) :
    Module.finrank ℂ (LevelPiece ρ w (b + c) b b) ≤
      (b + c).choose c * 6 ^ b := by
  classical
  let E := levelFiltration ρ w (b + c) b b
  let T := levelFiltration ρ w (b + c) b ((b : ℤ) + 1)
  let S := fun d => (keyOrbit ρ w (centralLetterKey c d)).map T.mkQ
  let H := fun d => (centralHigherDegree ρ w c d).map T.mkQ
  let degrees := Finset.range (2 * (b + c) * c + 1)
  have hedge : E = (⨆ d : ℕ, keyOrbit ρ w (centralLetterKey c d)) ⊔ T := by
    simpa only [Nat.cast_add, add_sub_cancel_right] using
      centralBoundary_eq_orbits_sup_next ρ w (b + c) c h
  have hfinite : (⨆ d : ℕ, keyOrbit ρ w (centralLetterKey c d)) =
      ⨆ d ∈ degrees, keyOrbit ρ w (centralLetterKey c d) := by
    apply le_antisymm
    · apply iSup_le
      intro d
      by_cases hd : d ∈ degrees
      · exact le_iSup_of_le d (le_iSup_of_le hd le_rfl)
      · rw [centralOrbit_eq_bot_of_degree_gt ρ w (b + c) c d h (by
          simpa only [degrees, Finset.mem_range, not_lt, Nat.add_one_le_iff] using hd)]
        exact bot_le
    · exact iSup_le fun d => iSup_le fun _ =>
        le_iSup (fun e : ℕ => keyOrbit ρ w (centralLetterKey c e)) d
  have hH : ∀ d ∈ degrees,
      H d ≤ ⨆ e ∈ degrees, ⨆ (_ : -(e : ℤ) < -(d : ℤ)), S e := by
    intro d _
    have hh := Submodule.map_mono (f := T.mkQ)
      (centralHigherDegree_le_finite ρ w (b + c) c d h)
    simp only [Submodule.map_iSup] at hh
    apply hh.trans
    apply iSup_le
    intro e
    apply iSup_le
    intro he
    apply iSup_le
    intro hde
    exact le_iSup_of_le e (le_iSup_of_le he
      (le_iSup_of_le (by omega : -(e : ℤ) < -(d : ℤ)) le_rfl))
  have hstep (d : ℕ) : Module.finrank ℂ ((S d).map (H d).mkQ) ≤
      6 ^ b * (centralGradedBox (b + c) c d).card := by
    rw [quotientImage_twice_finrank]
    exact centralOrbit_quotient_rank_le ρ w b c d h
  have htotal := SL4T.finiteFiltration_finrank_le S H (fun d => -(d : ℤ))
    (fun d => 6 ^ b * (centralGradedBox (b + c) c d).card)
    degrees hH (fun d _ => hstep d)
  have hspan : (⨆ d ∈ degrees, S d) = E.map T.mkQ := by
    rw [hedge, Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq, hfinite]
    simp only [S, Submodule.map_iSup]
  rw [hspan, ← Finset.mul_sum] at htotal
  have hbound := htotal.trans (Nat.mul_le_mul_left _
    (centralGradedBox_sum_le (b + c) c (by omega) degrees))
  change Module.finrank ℂ (E ⧸ T.comap E.subtype) ≤ _
  rw [ksKey_quot_finrank_eq_image]
  simpa only [Nat.mul_comm] using hbound

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.centralHigherDegree_stable
#print axioms VOA.DeligneAudit.D4LevelReduction.centralOrbit_eq_bot_of_degree_gt
#print axioms VOA.DeligneAudit.D4LevelReduction.centralHigherDegree_le_finite
#print axioms VOA.DeligneAudit.D4LevelReduction.centralOrbit_quotient_rank_le
#print axioms VOA.DeligneAudit.D4LevelReduction.centralBoundary_rank_le
