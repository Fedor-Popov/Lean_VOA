import VOA.DeligneAudit.SL4TTruncationCutoff
import VOA.DeligneAudit.SL4TMixedSecondLeviBlockBound

/-!
Universal local Weyl modules with an independent current cutoff, including the middle-weight
module with one fewer mode than sites.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.UnivG VOA.DeligneAudit.A3Sector

/-- The universal local Weyl module at three arbitrary labels and an independent cutoff. -/
abbrev TruncatedLabelModule (a b c M : ℕ) :=
  UModG bracketTable (truncatedWeylSpec (weightABC a b c) M)

/-- Local Weyl finiteness holds for every current cutoff, including zero. -/
theorem truncatedLabelModule_finite_and_local_bound (a b c M : ℕ) :
    FiniteDimensional ℂ (TruncatedLabelModule a b c M) ∧
      Module.finrank ℂ (TruncatedLabelModule a b c M) ≤ 4 ^ a * 6 ^ b * 4 ^ c := by
  let R := truncatedWeylSpec (weightABC a b c) M
  have hw := ((truncatedWeylSpec_sat_iff _ _ _ _).mp (univG_sat bracketTable R)).1
  obtain ⟨hf, hr⟩ := a3_all_weight_rank (univRepG bracketTable R)
    (wUG bracketTable R) a b c hw
  rw [presentedCurrent_cyclic] at hf hr
  haveI : FiniteDimensional ℂ (⊤ : Submodule ℂ (TruncatedLabelModule a b c M)) := hf
  haveI : FiniteDimensional ℂ (TruncatedLabelModule a b c M) :=
    Module.Finite.of_surjective Submodule.topEquiv.toLinearMap Submodule.topEquiv.surjective
  exact ⟨inferInstance, by simpa only [finrank_top] using hr⟩

/-- Every high current vanishes on the entire universal truncated module. -/
theorem truncatedLabelModule_current_zero (a b c M : ℕ)
    (x : Fin 15) (s : ℕ) (hs : M ≤ s) (v : TruncatedLabelModule a b c M) :
    (univRepG bracketTable (truncatedWeylSpec (weightABC a b c) M)).op x s v = 0 := by
  let R := truncatedWeylSpec (weightABC a b c) M
  have ht := ((truncatedWeylSpec_sat_iff _ _ _ _).mp (univG_sat bracketTable R)).2
  apply current_truncation_on_cyclic (univRepG bracketTable R)
    (wUG bracketTable R) M ht v _ x s hs
  rw [presentedCurrent_cyclic]
  exact Submodule.mem_top

/-- A bound on a universal presentation is equivalent to the bound on all cyclic realizations. -/
theorem truncatedLabelModule_rank_iff_cyclic (a b c M D : ℕ) :
    Module.finrank ℂ (TruncatedLabelModule a b c M) ≤ D ↔
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
        (ρ : CurrentModule bracketTable V) (w : V),
        LocalWeylRel ρ w (weightABC a b c) →
        (∀ x, ρ.op x M w = 0) →
        FiniteDimensional ℂ (cycSubG ρ w) ∧ Module.finrank ℂ (cycSubG ρ w) ≤ D := by
  constructor
  · intro hr V _ _ ρ w hw ht
    haveI := (truncatedLabelModule_finite_and_local_bound a b c M).1
    have hs := (truncatedWeylSpec_sat_iff_cutoff ρ w (weightABC a b c) M).mpr ⟨hw, ht⟩
    obtain ⟨hf, hb⟩ := presentedCurrent_cyclic_rank_le hs
    exact ⟨hf, hb.trans hr⟩
  · intro h
    let R := truncatedWeylSpec (weightABC a b c) M
    have hs := (truncatedWeylSpec_sat_iff_cutoff _ _ _ _).mp (univG_sat bracketTable R)
    obtain ⟨_, hr⟩ := h _ (univRepG bracketTable R) (wUG bracketTable R) hs.1 hs.2
    rw [presentedCurrent_cyclic, finrank_top] at hr
    exact hr

/-- The middle-weight module whose cutoff is one fewer than its number of sites. -/
abbrev DoubledSiteModule (B : ℕ) := TruncatedLabelModule 0 B 0 (B - 1)

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Both retained Cartans vanish in the second Levi quotient above the original cutoff. -/
theorem secondLeviQuotientCartan_truncated
    (ρ : CurrentModule bracketTable V) (w : V) (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c)) (M : ℕ)
    (ht : ∀ i s v, M ≤ s → ρ.op i s v = 0)
    (d : Fin 3 → ℕ) (e₁ e₂ : ℕ) (i : Fin 2) (s : ℕ) (hs : M ≤ s)
    (v : (V ⧸ higherRadicalCountClosure ρ w d) ⧸
      higherSecondLeviCountClosure (radicalCountQuotCurrent ρ w d)
        (radicalGrassmannianAmbientEvaluation ρ w a b c h d) e₁ e₂) :
    secondLeviQuotientCartan (radicalCountQuotCurrent ρ w d)
      (radicalGrassmannianAmbientEvaluation ρ w a b c h d) e₁ e₂ i s v = 0 := by
  obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective _ v
  change Submodule.mkQ _ ((radicalCountQuotCurrent ρ w d).op
    (if i = 0 then 6 else 7) s u) = 0
  rw [radicalCountQuot_truncated ρ w M ht d _ s hs u, map_zero]

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.truncatedLabelModule_finite_and_local_bound
#print axioms VOA.DeligneAudit.SL4T.truncatedLabelModule_current_zero
#print axioms VOA.DeligneAudit.SL4T.truncatedLabelModule_rank_iff_cyclic
#print axioms VOA.DeligneAudit.SL4T.secondLeviQuotientCartan_truncated
