import VOA.DeligneAudit.LeviTypeA3GradedInductionInner

/-! Lexicographic mode-sum induction closes the all-weight type-A₃ bound. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.Sl2Weyl
open VOA.DeligneAudit.LeviConversion

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

theorem a3_sorted_word_effective (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (xs ys zs : List ℕ) :
    (aWord (fun i => ρ.op (F 0) i) xs *
      (ys.map fun i => ρ.op (F 1) i).prod *
      (zs.map fun i => ρ.op (F 2) i).prod) w ∈
      a3EffectiveTarget ρ w a b c
        ⟨xs.length, ys.length, zs.length, xs.sum + ys.sum + zs.sum⟩ := by
  suffices hall : ∀ σ : ℕ, ∀ xs ys zs : List ℕ, xs.sum = σ →
      (aWord (fun i => ρ.op (F 0) i) xs *
        (ys.map fun i => ρ.op (F 1) i).prod *
        (zs.map fun i => ρ.op (F 2) i).prod) w ∈
        a3EffectiveTarget ρ w a b c
          ⟨xs.length, ys.length, zs.length, xs.sum + ys.sum + zs.sum⟩ by
    exact hall xs.sum xs ys zs rfl
  intro σ
  induction σ using Nat.strong_induction_on with
  | h σ ih =>
    intro xs ys zs hsum
    have hbox := a3_first_box_sorted ρ w a b c h xs ys zs
    have hle : a3FirstBoxSortedSpan ρ w a xs ys zs ≤
        a3EffectiveTarget ρ w a b c
          ⟨xs.length, ys.length, zs.length, xs.sum + ys.sum + zs.sum⟩ := by
      rw [a3FirstBoxSortedSpan, Submodule.span_le]
      intro v hv
      obtain ⟨f, hf, hwf, rfl⟩ := hv
      rw [a2_evAlg_monomial_word]
      have houter : ∀ us vs ts : List ℕ, us.sum < xs.sum →
          (aWord (fun i => ρ.op (F 0) i) us *
            (vs.map fun i => ρ.op (F 1) i).prod *
            (ts.map fun i => ρ.op (F 2) i).prod) w ∈
            a3EffectiveTarget ρ w a b c
              ⟨us.length, vs.length, ts.length, us.sum + vs.sum + ts.sum⟩ := by
        intro us vs ts hs
        exact ih us.sum (by omega) us vs ts rfl
      have hh := a3_boxed_first_word_effective ρ w a b c h f
        xs.length xs.sum hf hwf houter ys zs
      simpa only [mul_assoc, Module.End.mul_apply] using hh
    exact hle hbox

theorem a3_word_effectiveKS : a3WordEffectiveKS := by
  intro a b c V _ _ ρ w h xs ys zs
  exact a3_sorted_word_effective ρ w a b c h xs ys zs

theorem a3_fixedKeyKS : a3FixedKeyKS :=
  a3_fixedKeyKS_of_word_effective a3_word_effectiveKS

theorem a3_all_weight_rank (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c)) :
    FiniteDimensional ℂ (VOA.DeligneAudit.UnivG.cycSubG ρ w) ∧
      Module.finrank ℂ (VOA.DeligneAudit.UnivG.cycSubG ρ w) ≤
        4 ^ a * 6 ^ b * 4 ^ c :=
  a3_all_weight_rank_of_ks ρ w a b c h (a3_fixedKeyKS a b c V ρ w h)

theorem a3_typeABound : TypeABound :=
  a3_typeABound_of_word_effective a3_word_effectiveKS

end
end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_sorted_word_effective
#print axioms VOA.DeligneAudit.A3Sector.a3_word_effectiveKS
#print axioms VOA.DeligneAudit.A3Sector.a3_fixedKeyKS
#print axioms VOA.DeligneAudit.A3Sector.a3_all_weight_rank
#print axioms VOA.DeligneAudit.A3Sector.a3_typeABound
