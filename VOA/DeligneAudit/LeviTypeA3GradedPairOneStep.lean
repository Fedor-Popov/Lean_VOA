import VOA.DeligneAudit.LeviTypeA3GradedFirstAggregate
import VOA.DeligneAudit.LeviTypeA3GradedPairBox

/-! Apply either adjacent-pair Garland box to a concrete mode word. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

theorem a3_pair_word_one_step (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (j : Fin 2) (xs ys zs : List ℕ) :
    let A : ℕ → Module.End ℂ V := fun s => ρ.op (F (a3ConvA j)) s
    let B : ℕ → Module.End ℂ V := fun s => ρ.op (F (a3ConvB j)) s
    let R : Module.End ℂ V :=
      (zs.map fun s => ρ.op (F (a3ConvSpectator j)) s).prod
    let m := (weightABC a b c) (Fin.succ j)
    let K : A3RadicalKey :=
      if j = 0 then ⟨xs.length, ys.length, zs.length,
        xs.sum + ys.sum + zs.sum⟩
      else ⟨zs.length, xs.length, ys.length,
        xs.sum + ys.sum + zs.sum⟩
    (aWord A xs * (ys.map B).prod) (R w) ∈
      a3PairBoxSpan ρ w j xs zs m ys.length ys.sum ⊔
        (a3PairModeLowerSpan ρ w j zs xs.length ys.length
          (xs.sum + ys.sum) xs.sum ⊔
          a3HigherLeviClosure ρ w b c K) := by
  have hstep := a3_pair_box_fixed_key ρ w a b c h j xs zs
    ys.length ys.sum (a2_mono_hom ys)
  simpa only [VOA.DeligneAudit.CLAssembly.evAlg_mono] using hstep

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_pair_word_one_step
