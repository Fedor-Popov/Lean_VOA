import VOA.DeligneAudit.LeviTypeA3GradedBoxExcess

/-! The second-pair step also handles F₃ counts beyond the sharp box. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.Sl2Weyl
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

theorem a3_three_box_word_one_step_total (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (f g : ℕ →₀ ℕ) (d₁ d₂ r s : ℕ)
    (hf : BoxP a f) (hg : BoxP b g)
    (hwf : Finsupp.weight om f = (d₁, r))
    (hwg : Finsupp.weight om g = (d₂, s))
    (zs : List ℕ) (h₁ : d₁ ≤ a) (h₂ : d₂ ≤ b) :
    let k : A3RadicalKey :=
      ⟨d₁, d₂, zs.length, r + s + zs.sum⟩
    (aWord (fun i => ρ.op (F 0) i) (VOA.DeligneAudit.CLAssembly.lst f) *
      ((VOA.DeligneAudit.CLAssembly.lst g).map
        fun i => ρ.op (F 1) i).prod *
      (zs.map fun i => ρ.op (F 2) i).prod) w ∈
        a3EffectiveTarget ρ w a b c k ⊔
          (a3PairModeLowerSpan ρ w 1
            (VOA.DeligneAudit.CLAssembly.lst f) d₂ zs.length
            (s + zs.sum) s ⊔
              a3HigherLeviClosure ρ w b c k) := by
  by_cases h₃ : zs.length ≤ c
  · exact a3_three_box_word_one_step ρ w a b c h f g d₁ d₂ r s
      hf hg hwf hwg zs h₁ h₂ h₃
  let fs := VOA.DeligneAudit.CLAssembly.lst f
  let gs := VOA.DeligneAudit.CLAssembly.lst g
  let k : A3RadicalKey := ⟨d₁, d₂, zs.length, r + s + zs.sum⟩
  have hlenf : fs.length = d₁ := by
    simpa [fs, a2_lst_length, Finsupp.weight_apply, om,
      Finsupp.degree_apply, Finsupp.sum, Prod.fst_sum] using
      congrArg Prod.fst hwf
  have hsumf : fs.sum = r := by
    simpa [fs, a2_lst_sum] using congrArg Prod.snd hwf
  have hleng : gs.length = d₂ := by
    simpa [gs, a2_lst_length, Finsupp.weight_apply, om,
      Finsupp.degree_apply, Finsupp.sum, Prod.fst_sum] using
      congrArg Prod.fst hwg
  have hsumg : gs.sum = s := by
    simpa [gs, a2_lst_sum] using congrArg Prod.snd hwg
  have hstep := a3_pair_word_one_step ρ w a b c h 1 gs zs fs
  have hstep' :
      (aWord (fun i => ρ.op (F 1) i) gs *
        (zs.map fun i => ρ.op (F 2) i).prod *
        (fs.map fun i => ρ.op (F 0) i).prod) w ∈
          a3PairBoxSpan ρ w 1 gs fs c zs.length zs.sum ⊔
            (a3PairModeLowerSpan ρ w 1 fs d₂ zs.length
              (s + zs.sum) s ⊔ a3HigherLeviClosure ρ w b c k) := by
    simpa only [a3ConvA, a3ConvB, a3ConvSpectator, weightABC,
      hleng, hsumg, hlenf, hsumf, k, mul_assoc,
      Module.End.mul_apply, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hstep
  rw [a3_rotate_radical_words ρ w fs gs zs] at hstep'
  have hzero : a3PairBoxSpan ρ w 1 gs fs c zs.length zs.sum = ⊥ :=
    a3PairBoxSpan_eq_bot_of_excess ρ w 1 gs fs c zs.length zs.sum
      (by omega)
  rw [hzero, bot_sup_eq] at hstep'
  exact (show
      a3PairModeLowerSpan ρ w 1 fs d₂ zs.length (s + zs.sum) s ⊔
        a3HigherLeviClosure ρ w b c k ≤
      a3EffectiveTarget ρ w a b c k ⊔
        (a3PairModeLowerSpan ρ w 1 fs d₂ zs.length (s + zs.sum) s ⊔
          a3HigherLeviClosure ρ w b c k) from le_sup_right) hstep'

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_three_box_word_one_step_total
