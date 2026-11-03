import VOA.DeligneAudit.LeviTypeA3GradedThirdStep

/-! The remaining lexicographic word induction implies the fixed-key KS bound. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.LeviConversion

noncomputable section

/-- The exact residual word statement: every sorted radical word reduces to
the three sharp boxes, or to the higher-key Levi closure. -/
def a3WordEffectiveKS : Prop :=
  ∀ (a b c : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : CurrentModule bracketTable V) (w : V),
    LocalWeylRel ρ w (weightABC a b c) →
      ∀ (xs ys zs : List ℕ),
        (aWord (fun i => ρ.op (F 0) i) xs *
          (ys.map fun i => ρ.op (F 1) i).prod *
          (zs.map fun i => ρ.op (F 2) i).prod) w ∈
          a3EffectiveTarget ρ w a b c
            ⟨xs.length, ys.length, zs.length, xs.sum + ys.sum + zs.sum⟩

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

theorem a3_effective_span_of_words (a b c : ℕ)
    (hword : ∀ xs ys zs : List ℕ,
      (aWord (fun i => ρ.op (F 0) i) xs *
        (ys.map fun i => ρ.op (F 1) i).prod *
        (zs.map fun i => ρ.op (F 2) i).prod) w ∈
        a3EffectiveTarget ρ w a b c
          ⟨xs.length, ys.length, zs.length, xs.sum + ys.sum + zs.sum⟩)
    (k : A3RadicalKey) :
    a3KeyLayer ρ w k ≤ a3EffectiveTarget ρ w a b c k := by
  rw [a3KeyLayer_eq_sorted, a3SortedKeySpan, Submodule.span_le]
  intro v hv
  obtain ⟨xs, ys, zs, hx, hy, hz, hd, rfl⟩ := hv
  simpa only [hx, hy, hz, hd] using hword xs ys zs

theorem a3_fixedKeyKS_of_word_effective (hword : a3WordEffectiveKS) :
    a3FixedKeyKS := by
  apply a3_fixedKeyKS_of_effective_span
  intro a b c V _ _ ρ w h k
  exact a3_effective_span_of_words ρ w a b c
    (hword a b c V ρ w h) k

theorem a3_typeABound_of_word_effective (hword : a3WordEffectiveKS) :
    TypeABound :=
  a3_typeABound_of_fixedKeyKS (a3_fixedKeyKS_of_word_effective hword)

end
end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_effective_span_of_words
#print axioms VOA.DeligneAudit.A3Sector.a3_fixedKeyKS_of_word_effective
#print axioms VOA.DeligneAudit.A3Sector.a3_typeABound_of_word_effective
