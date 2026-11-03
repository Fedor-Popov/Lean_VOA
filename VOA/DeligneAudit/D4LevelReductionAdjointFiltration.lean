import VOA.DeligneAudit.D4LevelReductionOrbitRank
import VOA.DeligneAudit.D4LevelReductionAdjointGraded
import VOA.DeligneAudit.D4LevelReductionAdjointBounds

/-!
The descending current-degree filtration of the pure adjoint multiplicity space.
Its homogeneous Grassmannian spanning fibers give the finite cyclic quotient bounds.
-/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.D4Levi
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)

/-- High images of any invariant Levi subspace remain invariant. -/
theorem currentTail_stable_of_leviInvariant (S : Submodule ℂ V) (n : ℕ)
    (hS : ∀ a r, IsLevi a → S ≤ S.comap (ρ.op a r))
    (a : Fin 28) (s : ℕ) (ha : IsLevi a) :
    currentTail ρ S {c | IsLevi c} n ≤
      (currentTail ρ S {c | IsLevi c} n).comap (ρ.op a s) := by
  intro v hv
  change ρ.op a s v ∈ currentTail ρ S {c | IsLevi c} n
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨b, hb, r, hr, u, hu, rfl⟩ := hz
      rw [sub_eq_iff_eq_add.mp (ρ.comm a b s r u)]
      apply Submodule.add_mem
      · apply Submodule.sum_mem
        intro c _
        by_cases hc : IsLevi c
        · exact (currentTail ρ S {c | IsLevi c} n).smul_mem _
            (currentTail_contains ρ S _ n hc (by omega) hu)
        · rw [reductiveLevi_bracket_support a b c ha hb hc, zero_smul]
          exact Submodule.zero_mem _
      · exact currentTail_contains ρ S _ n hb hr (hS a s ha hu)
  | zero => simpa using (currentTail ρ S {c | IsLevi c} n).zero_mem
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | smul c x _ hx => simpa using Submodule.smul_mem _ c hx

/-- The sum of two invariant subspaces is invariant. -/
theorem leviInvariant_sup (S T : Submodule ℂ V)
    (hS : ∀ a r, IsLevi a → S ≤ S.comap (ρ.op a r))
    (hT : ∀ a r, IsLevi a → T ≤ T.comap (ρ.op a r))
    (a : Fin 28) (r : ℕ) (ha : IsLevi a) :
    S ⊔ T ≤ (S ⊔ T).comap (ρ.op a r) := by
  apply sup_le
  · exact (hS a r ha).trans (Submodule.comap_mono le_sup_left)
  · exact (hT a r ha).trans (Submodule.comap_mono le_sup_right)

/-- Pure adjoint orbits of strictly higher current degree. -/
noncomputable def adjointHigherDegree (a d : ℕ) : Submodule ℂ V :=
  ⨆ e : ℕ, ⨆ (_ : d < e), keyOrbit ρ w (adjointLetterKey a e)

theorem adjointHigherDegree_stable (a d : ℕ) (c : Fin 28) (r : ℕ) (hc : IsLevi c) :
    adjointHigherDegree ρ w a d ≤ (adjointHigherDegree ρ w a d).comap (ρ.op c r) := by
  apply iSup_le
  intro e
  apply iSup_le
  intro he v hv
  change ρ.op c r v ∈ adjointHigherDegree ρ w a d
  exact Submodule.mem_iSup_of_mem e (Submodule.mem_iSup_of_mem he
    (levi_op_orbit ρ w (adjointLetterKey a e) c r hc hv))

/-- No adjoint orbit survives beyond the finite radical mode-degree bound. -/
theorem adjointOrbit_eq_bot_of_degree_gt (m a d : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (hd : 2 * m * a < d) :
    keyOrbit ρ w (adjointLetterKey a d) = ⊥ := by
  apply keyOrbit_eq_bot_of_keyLayer_bot
  apply keyLayer_eq_bot_of_degree_gt ρ w m h
  simpa [keyDepth, adjointLetterKey] using hd

/-- The higher-degree filtration is supported on the same finite mode box. -/
theorem adjointHigherDegree_le_finite (m a d : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) :
    adjointHigherDegree ρ w a d ≤
      ⨆ e ∈ Finset.range (2 * m * a + 1), ⨆ (_ : d < e),
        keyOrbit ρ w (adjointLetterKey a e) := by
  apply iSup_le
  intro e
  apply iSup_le
  intro he
  by_cases hd : e < 2 * m * a + 1
  · exact le_iSup_of_le e (le_iSup_of_le (Finset.mem_range.mpr hd)
      (le_iSup_of_le he le_rfl))
  · rw [adjointOrbit_eq_bot_of_degree_gt ρ w m a e h (by omega)]
    exact bot_le

/-- A degree step in any quotient containing the current tail has the mixed sl₄ bound. -/
theorem adjointOrbit_quotient_rank_le (a b d : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector (a + b) 0)) (T : Submodule ℂ V)
    (hT : ∀ c r, IsLevi c → T ≤ T.comap (ρ.op c r))
    (htail : currentTail ρ
      (levelFiltration ρ w (a + b) b (2 * (a : ℤ) + b))
        {c | IsLevi c} (a + b) ≤ T) :
    Module.finrank ℂ ((keyOrbit ρ w (adjointLetterKey a d)).map
      (adjointHigherDegree ρ w a d ⊔ T).mkQ) ≤
        (15 ^ a * 6 ^ b) * (adjointGradedBox (a + b) a d).card := by
  let N := adjointHigherDegree ρ w a d ⊔ T
  haveI : FiniteDimensional ℂ (keyLayer ρ w (adjointLetterKey a d)) :=
    keyLayer_finite ρ w _
  have hN : ∀ c r, IsLevi c → N ≤ N.comap (ρ.op c r) :=
    leviInvariant_sup ρ _ T (adjointHigherDegree_stable ρ w a d) hT
  have hdegree (s : ℕ) (hs : 0 < s) :
      keyLayer ρ w (adjointLetterKey a (d + s)) ≤ N := by
    apply (keyLayer_le_orbit ρ w _).trans
    apply le_sup_of_le_left
    exact le_iSup_of_le (d + s) (le_iSup_of_le (by omega : d < d + s) le_rfl)
  have hpos : ∀ v ∈ keyLayer ρ w (adjointLetterKey a d),
      ∀ r, 0 < r → ρ.op (0 : Fin 28) r v ∈ N := by
    intro v hv r hr
    exact hdegree r hr (adjointKey_extra_pos_mem ρ w (a + b) a d h r hr hv)
  have hb := keyOrbit_quotient_rank_le ρ w (a + b) N hN h
    (adjointLetterKey a d) (15 ^ a * 6 ^ b) hpos (by
      intro v hv
      apply adjointKey_truncated_quotient_rank_le ρ w a b d h N
        (quotientLevi_invariant ρ N hN) hv
      · intro i s hs
        change (leviSign (A3Sector.simpleH i) : ℂ) •
          ρ.op (leviColour (A3Sector.simpleH i)) s v ∈ N
        exact N.smul_mem _ (hdegree s hs
          (adjointKey_cartan_pos_mem ρ w (a + b) a d h i s hs hv))
      · intro e s hs
        apply N.smul_mem
        apply (show T ≤ N from le_sup_right)
        apply htail
        apply currentTail_contains ρ _ _ (a + b) (leviColour_isLevi e) hs
        have horbit := keyLayer_le_orbit ρ w _ hv
        exact keyOrbit_le_levelFiltration_of_sat ρ w (a + b) h _ _ _ (by
          simp [keyAlphaGrade, keyDepth, adjointLetterKey]) (by
          simp only [keyLeviLevel, adjointLetterKey, Nat.cast_add, Nat.cast_zero]
          omega) horbit)
  have hdim : Module.finrank ℂ
      (keyLayer ρ w (adjointLetterKey a d) ⧸
        N.comap (keyLayer ρ w (adjointLetterKey a d)).subtype) ≤
      Module.finrank ℂ (keyLayer ρ w (adjointLetterKey a d)) :=
    Submodule.finrank_quotient_le _
  exact hb.2.trans (Nat.mul_le_mul_left _ (hdim.trans
    (adjointKey_finrank_le_gradedBox ρ w (a + b) a d (by omega) h)))

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.currentTail_stable_of_leviInvariant
#print axioms VOA.DeligneAudit.D4LevelReduction.leviInvariant_sup
#print axioms VOA.DeligneAudit.D4LevelReduction.adjointHigherDegree_stable
#print axioms VOA.DeligneAudit.D4LevelReduction.adjointOrbit_eq_bot_of_degree_gt
#print axioms VOA.DeligneAudit.D4LevelReduction.adjointHigherDegree_le_finite
#print axioms VOA.DeligneAudit.D4LevelReduction.adjointOrbit_quotient_rank_le
