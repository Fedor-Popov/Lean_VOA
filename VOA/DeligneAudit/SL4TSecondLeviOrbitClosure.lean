import VOA.DeligneAudit.SL4TMixedSecondLeviBlockBound
import VOA.DeligneAudit.SL4TCurrentTruncationExact

/-! The second Levi closure agrees with the last-root orbit after passing to the count quotient. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector

/-- A current-generated span is invariant under an operator whose commutators preserve it. -/
theorem currentSpan_invariant_of_commutators
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (E H F : ℕ → Module.End ℂ W) (S : Set W) (K : Module.End ℂ W)
    (hb : ∀ x ∈ S, K x ∈ currentSpan E H F S)
    (he : ∀ s x, x ∈ currentSpan E H F S → K (E s x) - E s (K x) ∈ currentSpan E H F S)
    (hh : ∀ s x, x ∈ currentSpan E H F S → K (H s x) - H s (K x) ∈ currentSpan E H F S)
    (hf : ∀ s x, x ∈ currentSpan E H F S → K (F s x) - F s (K x) ∈ currentSpan E H F S) :
    currentSpan E H F S ≤ (currentSpan E H F S).comap K := by
  let P := currentSpan E H F S
  have hP := currentSpan_stable (E := E) (H := H) (F := F) S
  have hle : P ≤ P ⊓ P.comap K := by
    apply currentSpan_le
    · intro x hx
      exact ⟨subset_currentSpan S hx, hb x hx⟩
    · refine ⟨?_, ?_, ?_⟩ <;> intro s x hx
      · refine ⟨hP.1 s hx.1, ?_⟩
        exact (P.sub_mem_iff_left (hP.1 s hx.2)).mp (he s x hx.1)
      · refine ⟨hP.2.1 s hx.1, ?_⟩
        exact (P.sub_mem_iff_left (hP.2.1 s hx.2)).mp (hh s x hx.1)
      · refine ⟨hP.2.2 s hx.1, ?_⟩
        exact (P.sub_mem_iff_left (hP.2.2 s hx.2)).mp (hf s x hx.1)
  exact hle.trans inf_le_right

variable {B V : Type} [CommRing B] [Algebra ℂ B]
variable [AddCommGroup V] [Module ℂ V]
variable (Q : CurrentModule VOA.AffineSl3.bracketTable V) (β : B →ₗ[ℂ] V)

/-- The retained first Cartan normalizes the last-root current orbit. -/
theorem secondLeviOrbit_otherCartan (e₁ e₂ : ℕ)
    (hb : ∀ s, secondLeviMultiplicity Q β e₁ e₂ ≤
      (secondLeviMultiplicity Q β e₁ e₂).comap
        (secondLeviQuotientCartan Q β e₁ e₂ 0 s)) (s : ℕ) :
    secondLeviOrbit Q β e₁ e₂ ≤ (secondLeviOrbit Q β e₁ e₂).comap
      (secondLeviQuotientCartan Q β e₁ e₂ 0 s) := by
  let N := higherSecondLeviCountClosure Q β e₁ e₂
  let E := secondLeviQuotientRaising Q β e₁ e₂
  let H := secondLeviQuotientCartan Q β e₁ e₂ 1
  let F := secondLeviQuotientLowering Q β e₁ e₂
  let K := secondLeviQuotientCartan Q β e₁ e₂ 0
  have hP := currentSpan_stable (E := E) (H := H) (F := F)
    (secondLeviMultiplicity Q β e₁ e₂ : Set _)
  apply currentSpan_invariant_of_commutators E H F _ (K s)
  · intro x hx
    exact subset_currentSpan _ (hb s hx)
  · intro t x hx
    have hc : K s (E t x) - E t (K s x) = - E (s + t) x := by
      obtain ⟨v, rfl⟩ := N.mkQ_surjective x
      change N.mkQ (Q.op 6 s (Q.op 1 t v)) - N.mkQ (Q.op 1 t (Q.op 6 s v)) = _
      rw [← map_sub, Q.comm]
      simp [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable]
      rfl
    rw [hc]
    exact Submodule.neg_mem _ (hP.1 _ hx)
  · intro t x hx
    have hc : K s (H t x) - H t (K s x) = 0 := by
      obtain ⟨v, rfl⟩ := N.mkQ_surjective x
      change N.mkQ (Q.op 6 s (Q.op 7 t v)) - N.mkQ (Q.op 7 t (Q.op 6 s v)) = 0
      rw [← map_sub, Q.comm]
      simp [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable]
    rw [hc]
    exact Submodule.zero_mem _
  · intro t x hx
    have hc : K s (F t x) - F t (K s x) = F (s + t) x := by
      obtain ⟨v, rfl⟩ := N.mkQ_surjective x
      change N.mkQ (Q.op 6 s (Q.op 4 t v)) - N.mkQ (Q.op 4 t (Q.op 6 s v)) = _
      rw [← map_sub, Q.comm]
      simp [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable]
      rfl
    rw [hc]
    exact hP.2.2 _ hx

/-- Retaining the other Cartan adds no vectors to the second quotient orbit. -/
theorem secondLeviClosure_map_eq_orbit (e₁ e₂ : ℕ)
    (hb : ∀ s, secondLeviMultiplicity Q β e₁ e₂ ≤
      (secondLeviMultiplicity Q β e₁ e₂).comap
        (secondLeviQuotientCartan Q β e₁ e₂ 0 s)) :
    (a2LeviClosure Q (secondLeviCountLayer Q β e₁ e₂)).map
      (higherSecondLeviCountClosure Q β e₁ e₂).mkQ = secondLeviOrbit Q β e₁ e₂ := by
  let N := higherSecondLeviCountClosure Q β e₁ e₂
  let T := a2LeviClosure Q (secondLeviCountLayer Q β e₁ e₂)
  let P := secondLeviOrbit Q β e₁ e₂
  have hp := currentSpan_stable
    (E := secondLeviQuotientRaising Q β e₁ e₂)
    (H := secondLeviQuotientCartan Q β e₁ e₂ 1)
    (F := secondLeviQuotientLowering Q β e₁ e₂)
    (secondLeviMultiplicity Q β e₁ e₂ : Set _)
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply a2LeviClosure_le_of_inv
    · intro x hx
      exact subset_currentSpan _ ⟨x, hx, rfl⟩
    · intro i s hi x hx
      rcases hi with rfl | rfl | rfl | rfl
      · exact hp.1 s hx
      · exact hp.2.2 s hx
      · exact secondLeviOrbit_otherCartan Q β e₁ e₂ hb s hx
      · exact hp.2.1 s hx
  · apply currentSpan_le
    · rintro x ⟨y, hy, rfl⟩
      exact ⟨y, a2LeviClosure_contains Q _ hy, rfl⟩
    · refine ⟨?_, ?_, ?_⟩ <;> intro s x hx <;> obtain ⟨y, hy, rfl⟩ := hx
      · exact ⟨Q.op 1 s y, a2LeviClosure_inv Q _ 1 s (by simp [a2Levi]) hy, rfl⟩
      · exact ⟨Q.op 7 s y, a2LeviClosure_inv Q _ 7 s (by simp [a2Levi]) hy, rfl⟩
      · exact ⟨Q.op 4 s y, a2LeviClosure_inv Q _ 4 s (by simp [a2Levi]) hy, rfl⟩

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.currentSpan_invariant_of_commutators
#print axioms VOA.DeligneAudit.SL4T.secondLeviOrbit_otherCartan
#print axioms VOA.DeligneAudit.SL4T.secondLeviClosure_map_eq_orbit
