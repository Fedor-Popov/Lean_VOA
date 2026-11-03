import VOA.DeligneAudit.D4LevelReductionAdjointMultiplicity

/-! Highest-weight and degree-raising Cartan relations on the adjoint edge. -/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi

/-- Raising a pure adjoint word introduces a first-root letter. -/
theorem adjoint_raise_replacement_has_firstRoot (i : Fin 3) (s : ℕ)
    {l q : List (Fin 6 × ℕ)} (h : RaiseReplaces i s l q)
    (hl : ∀ p ∈ l, p.1 = 1) : 0 < q.countP (fun p => p.1 = 0) := by
  induction h with
  | @head j r k n l h =>
      have hj : j = 1 := hl (j, r) (by simp)
      subst j
      fin_cases i <;> simp [raiseAction] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
  | @tail j r l q h ih =>
      have ht := ih (fun p hp => hl p (List.mem_cons_of_mem (j, r) hp))
      simp only [List.countP_cons]
      omega

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)

/-- All simple positive Levi currents annihilate every pure adjoint-key vector. -/
theorem adjointKey_simple_raise_zero (m a d : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (i : Fin 3) (s : ℕ) {v : V} (hv : v ∈ keyLayer ρ w (adjointLetterKey a d)) :
    ρ.op (leviColour (A3Sector.simpleE i)) s v = 0 := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨l, hl, rfl⟩ := hv
      have hcol := adjointKey_word_colours a d l hl
      have hzero : raiseWordSpan ρ w i s l = ⊥ := by
        apply eq_bot_iff.mpr
        rw [raiseWordSpan, Submodule.span_le]
        rintro z ⟨q, hq, rfl⟩
        rw [radicalWord_zero_of_E ρ w m h q
          (adjoint_raise_replacement_has_firstRoot i s hq hcol)]
        exact Submodule.zero_mem _
      have hm := simple_raise_word_span ρ w m h i s l
      rw [hzero] at hm
      exact (Submodule.mem_bot ℂ).mp hm
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | smul c x _ hx => simp [map_smul, hx]

/-- All positive sl₄ currents annihilate the adjoint-key vectors before any quotient. -/
theorem adjointKey_all_raise_zero (m a d : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    {v : V} (hv : v ∈ keyLayer ρ w (adjointLetterKey a d))
    (e : Fin 15) (he : e.val < 6) (s : ℕ) : (leviCurrent ρ).op e s v = 0 := by
  apply positive_zero_of_simple (leviCurrent ρ) v _ e he s
  intro i r
  have hz := adjointKey_simple_raise_zero ρ w m a d h i r hv
  fin_cases i <;> simpa [leviCurrent, leviSign, A3Sector.simpleE] using hz

/-- Positive simple Cartan currents increase the adjoint-key degree. -/
theorem adjointKey_cartan_pos_mem (m a d : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (i : Fin 3)
    (s : ℕ) (hs : 0 < s) {v : V} (hv : v ∈ keyLayer ρ w (adjointLetterKey a d)) :
    ρ.op (leviColour (A3Sector.simpleH i)) s v ∈
      keyLayer ρ w (adjointLetterKey a (d + s)) := by
  simpa [keyShift, adjointLetterKey] using
    cartan_pos_maps_key ρ w m h i s hs (adjointLetterKey a d) hv

/-- Positive modes of the extra reductive Cartan also increase degree. -/
theorem adjointKey_extra_pos_mem (m a d : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (s : ℕ) (hs : 0 < s) {v : V} (hv : v ∈ keyLayer ρ w (adjointLetterKey a d)) :
    ρ.op (0 : Fin 28) s v ∈ keyLayer ρ w (adjointLetterKey a (d + s)) := by
  simpa [keyShift, adjointLetterKey] using
    extra_pos_key ρ w m h s hs (adjointLetterKey a d) hv

/-- The adjoint edge has the symmetric outer labels required by the mixed sl₄ bound. -/
theorem adjointKey_cartan_weight (a b d : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector (a + b) 0))
    (i : Fin 3) {v : V} (hv : v ∈ keyLayer ρ w (adjointLetterKey a d)) :
    (leviCurrent ρ).op (A3Sector.simpleH i) 0 v =
      (A3Sector.weightABC a b a i : ℂ) • v := by
  have hw := cartan_weight_key ρ w (a + b) h i (adjointLetterKey a d) hv
  fin_cases i <;>
    simpa [leviCurrent, leviSign, A3Sector.simpleH, A3Sector.weightABC,
      keyLabel, adjointLetterKey, Nat.cast_add, Int.cast_add, Int.cast_sub] using hw

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.adjoint_raise_replacement_has_firstRoot
#print axioms VOA.DeligneAudit.D4LevelReduction.adjointKey_simple_raise_zero
#print axioms VOA.DeligneAudit.D4LevelReduction.adjointKey_all_raise_zero
#print axioms VOA.DeligneAudit.D4LevelReduction.adjointKey_cartan_pos_mem
#print axioms VOA.DeligneAudit.D4LevelReduction.adjointKey_extra_pos_mem
#print axioms VOA.DeligneAudit.D4LevelReduction.adjointKey_cartan_weight
