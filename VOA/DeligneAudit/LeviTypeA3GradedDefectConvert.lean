import VOA.DeligneAudit.LeviTypeA3ConvAbsorb
import VOA.DeligneAudit.LeviTypeA2CertGradedDefectWords
import VOA.DeligneAudit.LeviTypeA2CertGradedDefectWeight

/-! A fixed-degree Garland defect is a graded conversion target in either radical pair. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.Sl2Weyl
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

theorem a3_convB_comm (j : Fin 2) (i t : ℕ) :
    ρ.op (F (a3ConvB j)) i * ρ.op (F (a3ConvB j)) t =
      ρ.op (F (a3ConvB j)) t * ρ.op (F (a3ConvB j)) i :=
  a3_conversion_radical_comm ρ _ _ i t

/-- Each explicit Garland defect for either adjacent radical pair reduces to
smaller mode sum in its source colour or to the higher-key Levi closure. -/
theorem a3_explicit_defect_reduces (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (j : Fin 2) (xs zs : List ℕ) (f : ℕ →₀ ℕ)
    (k s t d : ℕ) (hk : 1 ≤ k)
    (hks : (weightABC a b c) (Fin.succ j) + 1 ≤ k + s)
    (hw : Finsupp.weight om f + (k, s) = (t, d)) :
    let A : ℕ → Module.End ℂ V := fun i => ρ.op (F (a3ConvA j)) i
    let B : ℕ → Module.End ℂ V := fun i => ρ.op (F (a3ConvB j)) i
    let R : Module.End ℂ V :=
      (zs.map fun i => ρ.op (F (a3ConvSpectator j)) i).prod
    (aWord A xs * Sl2Weyl.evAlg B (a3_convB_comm ρ j)
      (MvPolynomial.monomial f 1 * xx k s)) (R w) ∈
      gradedLowerModeSpan A B xs (VOA.DeligneAudit.CLAssembly.lst f) k
        (xs.sum + d) R w ⊔
      a3HigherLeviClosure ρ w b c
        (a3ConvKey j k (xs.sum + d + zs.sum) xs
          (VOA.DeligneAudit.CLAssembly.lst f) zs) := by
  let A : ℕ → Module.End ℂ V := fun i => ρ.op (F (a3ConvA j)) i
  let B : ℕ → Module.End ℂ V := fun i => ρ.op (F (a3ConvB j)) i
  let R : Module.End ℂ V :=
    (zs.map fun i => ρ.op (F (a3ConvSpectator j)) i).prod
  let ys := VOA.DeligneAudit.CLAssembly.lst f
  have hdegree : xs.sum + ys.sum + s = xs.sum + d := by
    dsimp [ys]
    rw [a2_lst_sum]
    have hs := congrArg Prod.snd hw
    simp only [Prod.snd_add] at hs
    omega
  have htarget :
      (aWord A xs * Sl2Weyl.evAlg B (a3_convB_comm ρ j)
        (MvPolynomial.monomial f 1 * xx k s)) (R w) =
      boxTarget A B k s xs ys R w := by
    rw [a2_graded_defect_as_boxTarget A B (a3_convB_comm ρ j)
      xs f k s (R w)]
    simp [ys, boxTarget, mul_smul, mul_assoc]
  change (aWord A xs * Sl2Weyl.evAlg B (a3_convB_comm ρ j)
      (MvPolynomial.monomial f 1 * xx k s)) (R w) ∈
    gradedLowerModeSpan A B xs ys k (xs.sum + d) R w ⊔
      a3HigherLeviClosure ρ w b c
        (a3ConvKey j k (xs.sum + d + zs.sum) xs ys zs)
  rw [htarget]
  have hconv := a3_box_conversion_graded ρ w a b c h j k s hk hks
    xs ys zs (xs.sum + d + zs.sum)
  simpa only [A, B, R, ys, hdegree] using hconv

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_convB_comm
#print axioms VOA.DeligneAudit.A3Sector.a3_explicit_defect_reduces
