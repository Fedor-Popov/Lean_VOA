import VOA.DeligneAudit.LeviTypeA3GradedInductionStep

/-! The inner mode-sum induction, with the first box monomial held fixed. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.Sl2Weyl
open VOA.DeligneAudit.LeviConversion

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

theorem a3_boxed_first_word_effective (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (f : ℕ →₀ ℕ) (d₁ r : ℕ)
    (hf : BoxP a f) (hwf : Finsupp.weight om f = (d₁, r))
    (houter : ∀ xs ys zs : List ℕ, xs.sum < r →
      (aWord (fun i => ρ.op (F 0) i) xs *
        (ys.map fun i => ρ.op (F 1) i).prod *
        (zs.map fun i => ρ.op (F 2) i).prod) w ∈
        a3EffectiveTarget ρ w a b c
          ⟨xs.length, ys.length, zs.length, xs.sum + ys.sum + zs.sum⟩)
    (ys zs : List ℕ) :
    (aWord (fun i => ρ.op (F 0) i) (VOA.DeligneAudit.CLAssembly.lst f) *
      (ys.map fun i => ρ.op (F 1) i).prod *
      (zs.map fun i => ρ.op (F 2) i).prod) w ∈
      a3EffectiveTarget ρ w a b c
        ⟨d₁, ys.length, zs.length, r + ys.sum + zs.sum⟩ := by
  let fs := VOA.DeligneAudit.CLAssembly.lst f
  have hlenf : fs.length = d₁ := by
    simpa [fs, a2_lst_length, a3_box_weight_first] using
      congrArg Prod.fst hwf
  have hsumf : fs.sum = r := by
    simpa [fs, a2_lst_sum] using congrArg Prod.snd hwf
  have h₁ : d₁ ≤ a := by
    have hd := a3_box_degree_le a f hf
    have hw := congrArg Prod.fst hwf
    rw [a3_box_weight_first] at hw
    omega
  suffices hall : ∀ σ : ℕ, ∀ ys zs : List ℕ, ys.sum = σ →
      (aWord (fun i => ρ.op (F 0) i) fs *
        (ys.map fun i => ρ.op (F 1) i).prod *
        (zs.map fun i => ρ.op (F 2) i).prod) w ∈
        a3EffectiveTarget ρ w a b c
          ⟨d₁, ys.length, zs.length, r + ys.sum + zs.sum⟩ by
    exact hall ys.sum ys zs rfl
  intro σ
  induction σ using Nat.strong_induction_on with
  | h σ ih =>
    intro ys zs hsum
    let k : A3RadicalKey :=
      ⟨d₁, ys.length, zs.length, r + ys.sum + zs.sum⟩
    have hstep := a3_two_box_word_one_step_fixed ρ w a b c h f d₁ r
      hwf ys zs
    have hbox : a3PairBoxSpan ρ w 0 fs zs b ys.length ys.sum ≤
        a3EffectiveTarget ρ w a b c k := by
      rw [a3PairBoxSpan, Submodule.span_le]
      intro v hv
      obtain ⟨g, hg, hwg, rfl⟩ := hv
      rw [a2_evAlg_monomial_word]
      have h₂ : ys.length ≤ b := by
        have hd := a3_box_degree_le b g hg
        have hw := congrArg Prod.fst hwg
        rw [a3_box_weight_first] at hw
        omega
      have ht := a3_three_box_word_one_step_total ρ w a b c h
        f g d₁ ys.length r ys.sum hf hg hwf hwg zs h₁ h₂
      have hlower : a3PairModeLowerSpan ρ w 1 fs ys.length zs.length
          (ys.sum + zs.sum) ys.sum ≤ a3EffectiveTarget ρ w a b c k := by
        have hle := a3_second_lower_le_effective ρ w a b c fs
          ys.length zs.length (ys.sum + zs.sum) ys.sum
          (by
            intro ys' zs' hy hz hd hs
            have hh := ih ys'.sum (by omega) ys' zs' rfl
            simpa only [hy, hz, hlenf, hsumf, hd, Nat.add_assoc] using hh)
        simpa only [k, hlenf, hsumf, Nat.add_assoc] using hle
      have hhigher : a3HigherLeviClosure ρ w b c k ≤
          a3EffectiveTarget ρ w a b c k :=
        a3_higher_le_effective ρ w a b c k
      have ht' : (aWord (fun i => ρ.op (F 0) i) fs *
          ((VOA.DeligneAudit.CLAssembly.lst g).map
            fun i => ρ.op (F 1) i).prod *
          (zs.map fun i => ρ.op (F 2) i).prod) w ∈
          a3EffectiveTarget ρ w a b c k ⊔
            (a3PairModeLowerSpan ρ w 1 fs ys.length zs.length
              (ys.sum + zs.sum) ys.sum ⊔
              a3HigherLeviClosure ρ w b c k) := by
        simpa only [a3ConvA, a3ConvB, a3ConvSpectator,
          k, mul_assoc, Module.End.mul_apply] using ht
      have hle : a3EffectiveTarget ρ w a b c k ⊔
          (a3PairModeLowerSpan ρ w 1 fs ys.length zs.length
            (ys.sum + zs.sum) ys.sum ⊔
            a3HigherLeviClosure ρ w b c k) ≤
            a3EffectiveTarget ρ w a b c k :=
        sup_le le_rfl (sup_le hlower hhigher)
      simpa only [a3ConvA, a3ConvB, a3ConvSpectator,
        mul_assoc, Module.End.mul_apply] using hle ht'
    have hlower : a3PairModeLowerSpan ρ w 0 zs d₁ ys.length
        (r + ys.sum) r ≤ a3EffectiveTarget ρ w a b c k := by
      have hle := a3_first_lower_le_effective ρ w a b c zs d₁
        ys.length (r + ys.sum) r (by
          intro xs' ys' hx hy hd hs
          have hh := houter xs' ys' zs hs
          simpa only [hx, hy, hd, Nat.add_assoc] using hh)
      simpa only [k, Nat.add_assoc] using hle
    have hhigher : a3HigherLeviClosure ρ w b c k ≤
        a3EffectiveTarget ρ w a b c k :=
      a3_higher_le_effective ρ w a b c k
    have hle := sup_le hbox (sup_le hlower hhigher)
    exact hle hstep

end
end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_boxed_first_word_effective
