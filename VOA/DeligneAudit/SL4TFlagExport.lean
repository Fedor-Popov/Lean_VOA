import VOA.DeligneAudit.SL4TSpanningFlag

/-! # Natural-indexed generators and prefix spans for an ordered spanning chain -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

variable {R : Type*} [CommRing R] [Algebra ℂ R]

theorem SpanningChain.export {A : Ideal R[X]} {I J : Ideal R} {ns : List ℕ}
    (h : SpanningChain A I J ns) :
    ∃ (v : ℕ → R) (F : ℕ → Ideal R), F 0 = I ∧ F ns.length = J ∧
      (∀ i < ns.length,
        (F (i + 1)).restrictScalars ℂ = (F i).restrictScalars ℂ ⊔ ℂ ∙ v i) ∧
      (∀ i < ns.length,
        Polynomial.C (v i) * X ^ (ns.getD i 0) ∈ (F i).map Polynomial.C ⊔ A) := by
  induction h with
  | nil I =>
      exact ⟨fun _ => 0, fun _ => I, rfl, rfl, by simp, by simp⟩
  | @cons I K J ns x n hs hr ht ih =>
      obtain ⟨v, F, h0, htop, hstep, hrel⟩ := ih
      let w : ℕ → R := fun i => match i with | 0 => x | j + 1 => v j
      let G : ℕ → Ideal R := fun i => match i with | 0 => I | j + 1 => F j
      refine ⟨w, G, rfl, htop, ?_, ?_⟩
      · intro i hi
        cases i with
        | zero => simpa only [G, w, h0] using hs
        | succ i => exact hstep i (by simpa only [List.length_cons, Nat.succ_lt_succ_iff]
            using hi)
      · intro i hi
        cases i with
        | zero => simpa only [G, w, List.getD_cons_zero] using hr
        | succ i => exact hrel i (by simpa only [List.length_cons, Nat.succ_lt_succ_iff]
            using hi)

def generatorPrefix (v : ℕ → R) (k : ℕ) : Submodule ℂ R :=
  Submodule.span ℂ {x | ∃ i < k, v i = x}

theorem generatorPrefix_zero (v : ℕ → R) : generatorPrefix v 0 = ⊥ := by
  simp [generatorPrefix]

theorem generatorPrefix_succ (v : ℕ → R) (k : ℕ) :
    generatorPrefix v (k + 1) = generatorPrefix v k ⊔ ℂ ∙ v k := by
  have hs : {x | ∃ i < k + 1, v i = x} = {x | ∃ i < k, v i = x} ∪ {v k} := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact Or.inl ⟨i, hi, rfl⟩
      · exact Or.inr rfl
    · rintro (⟨i, hi, rfl⟩ | rfl)
      · exact ⟨i, by omega, rfl⟩
      · exact ⟨k, by omega, rfl⟩
  simp only [generatorPrefix, hs, Submodule.span_union]

theorem idealFlag_eq_prefix (v : ℕ → R) (F : ℕ → Ideal R) (n : ℕ)
    (h0 : F 0 = ⊥)
    (hstep : ∀ i < n,
      (F (i + 1)).restrictScalars ℂ = (F i).restrictScalars ℂ ⊔ ℂ ∙ v i) :
    ∀ k ≤ n, (F k).restrictScalars ℂ = generatorPrefix v k := by
  intro k hk
  induction k with
  | zero => rw [h0, generatorPrefix_zero, Submodule.restrictScalars_bot]
  | succ k ih => rw [hstep k (by omega), generatorPrefix_succ, ih (by omega)]

theorem SpanningChain.prefix_export {A : Ideal R[X]} {ns : List ℕ}
    (h : SpanningChain A ⊥ ⊤ ns) :
    ∃ (v : ℕ → R) (F : ℕ → Ideal R),
      (∀ k ≤ ns.length, (F k).restrictScalars ℂ = generatorPrefix v k) ∧
      F ns.length = ⊤ ∧
      (∀ i < ns.length,
        Polynomial.C (v i) * X ^ (ns.getD i 0) ∈ (F i).map Polynomial.C ⊔ A) := by
  obtain ⟨v, F, h0, ht, hs, hr⟩ := h.export
  exact ⟨v, F, idealFlag_eq_prefix v F ns.length h0 hs, ht, hr⟩

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.SpanningChain.export
#print axioms VOA.DeligneAudit.SL4T.generatorPrefix_zero
#print axioms VOA.DeligneAudit.SL4T.generatorPrefix_succ
#print axioms VOA.DeligneAudit.SL4T.idealFlag_eq_prefix
#print axioms VOA.DeligneAudit.SL4T.SpanningChain.prefix_export
