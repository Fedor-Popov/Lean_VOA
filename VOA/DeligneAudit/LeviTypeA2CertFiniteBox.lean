import VOA.DeligneAudit.LeviTypeA2CertSupport

/-! The exact letter-count input for finite support of radical keys. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : VOA.DeligneAudit.SectorWeyl.CurrentModule
    VOA.AffineSl3.bracketTable V) (w : V)

/-- The remaining graded sl₂ box consequence needed to bound radical counts.
The compound colour has root weight `p + q`, so its raw cutoff is `p + q`. -/
def A2RadicalCountCutoff (p q : ℕ) : Prop :=
  ∀ l : List (Fin 2 × ℕ),
    (p < l.countP (fun x => x.1 = 0) ∨
      p + q < l.countP (fun x => x.1 = 1)) →
    radicalWord (a2RadicalOp ρ) l • w = 0

theorem a2KeyLayer_eq_bot_of_count (p q : ℕ) (k : A2RadicalKey)
    (hc : A2RadicalCountCutoff ρ w p q)
    (hk : p < k.d₁ ∨ p + q < k.d₂) :
    a2KeyLayer ρ w k = ⊥ := by
  rw [a2KeyLayer, eq_bot_iff, Submodule.span_le]
  intro z hz
  obtain ⟨l, hd₁, hd₂, _, _, rfl⟩ := hz
  rw [hc l (by simpa only [hd₁, hd₂] using hk)]
  exact Submodule.zero_mem _

/-- Conditional finite support: every nonzero key layer lies in the explicit box. -/
theorem a2KeyBox_contains_nonzero (p q : ℕ) (k : A2RadicalKey)
    (h : A2LocalWeylRel ρ w p q)
    (hc : A2RadicalCountCutoff ρ w p q)
    (hk : a2KeyLayer ρ w k ≠ ⊥) :
    k ∈ a2KeyBox p q := by
  have h₁ : k.d₁ ≤ p := by
    by_contra hn
    exact hk (a2KeyLayer_eq_bot_of_count ρ w p q k hc (Or.inl (by omega)))
  have h₂ : k.d₂ ≤ p + q := by
    by_contra hn
    exact hk (a2KeyLayer_eq_bot_of_count ρ w p q k hc (Or.inr (by omega)))
  have hdegree : k.degree ≤ (p + q) * (2 * p + q) := by
    by_contra hn
    have hsmall : k.d₁ + k.d₂ ≤ 2 * p + q := by omega
    have hmul : (p + q) * (k.d₁ + k.d₂) ≤
        (p + q) * (2 * p + q) := Nat.mul_le_mul_left _ hsmall
    exact hk (a2KeyLayer_eq_bot_of_degree_gt ρ w p q k h (by omega))
  exact mem_a2KeyBox p q k h₁ h₂ hdegree

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2KeyLayer_eq_bot_of_count
#print axioms VOA.DeligneAudit.A3Sector.a2KeyBox_contains_nonzero
