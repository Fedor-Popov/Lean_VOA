import VOA.DeligneAudit.LeviTypeA3GradedThirdBridge

/-! One first-pair reduction after the exact F₁ Garland box. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.Sl2Weyl
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

/-- With F₁ boxed, one F₂ box step has a lower F₁ mode-sum remainder. -/
theorem a3_two_box_word_one_step (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (f : ℕ →₀ ℕ) (d₁ r : ℕ)
    (hf : BoxP a f) (hwf : Finsupp.weight om f = (d₁, r))
    (ys zs : List ℕ) :
    let k : A3RadicalKey :=
      ⟨d₁, ys.length, zs.length, r + ys.sum + zs.sum⟩
    (aWord (fun i => ρ.op (F 0) i) (VOA.DeligneAudit.CLAssembly.lst f) *
      (ys.map fun i => ρ.op (F 1) i).prod *
      (zs.map fun i => ρ.op (F 2) i).prod) w ∈
        a3TwoBoxKeySpan ρ w a b k ⊔
          (a3PairModeLowerSpan ρ w 0 zs d₁ ys.length (r + ys.sum) r ⊔
            a3HigherLeviClosure ρ w b c k) := by
  let xs := VOA.DeligneAudit.CLAssembly.lst f
  let k : A3RadicalKey :=
    ⟨d₁, ys.length, zs.length, r + ys.sum + zs.sum⟩
  have hlen : xs.length = d₁ := by
    simpa [xs, a2_lst_length, Finsupp.weight_apply, om,
      Finsupp.degree_apply, Finsupp.sum, Prod.fst_sum] using
      congrArg Prod.fst hwf
  have hsum : xs.sum = r := by
    simpa [xs, a2_lst_sum] using congrArg Prod.snd hwf
  have hstep := a3_pair_word_one_step ρ w a b c h 0 xs ys zs
  have hbox : a3PairBoxSpan ρ w 0 xs zs b ys.length ys.sum ≤
      a3TwoBoxKeySpan ρ w a b k := by
    exact a3_pair_zero_box_le_two ρ w a b k f zs r ys.sum
      hf hwf rfl rfl
  have hstep' :
      (aWord (fun i => ρ.op (F 0) i) xs *
        (ys.map fun i => ρ.op (F 1) i).prod *
        (zs.map fun i => ρ.op (F 2) i).prod) w ∈
          a3PairBoxSpan ρ w 0 xs zs b ys.length ys.sum ⊔
            (a3PairModeLowerSpan ρ w 0 zs d₁ ys.length
              (r + ys.sum) r ⊔ a3HigherLeviClosure ρ w b c k) := by
    simpa only [a3ConvA, a3ConvB, a3ConvSpectator, weightABC,
      Fin.succ_zero_eq_one, hlen, hsum, k, mul_assoc,
      Module.End.mul_apply, Nat.add_assoc] using hstep
  exact (sup_le (hbox.trans le_sup_left) le_sup_right) hstep'

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_two_box_word_one_step
