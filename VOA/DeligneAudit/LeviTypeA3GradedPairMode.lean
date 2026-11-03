import VOA.DeligneAudit.LeviTypeA3GradedDefectConvert
import VOA.DeligneAudit.LeviTypeA2CertGradedDefectEval

/-! A common lower-mode span for either adjacent radical pair. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.Sl2Weyl
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

def a3PairModeLowerSpan (j : Fin 2) (zs : List ℕ)
    (xlen ylen degree σ : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ xs ys : List ℕ,
    xs.length = xlen ∧ ys.length = ylen ∧
      xs.sum + ys.sum = degree ∧ xs.sum < σ ∧
        v = (aWord (fun i => ρ.op (F (a3ConvA j)) i) xs *
          (ys.map fun i => ρ.op (F (a3ConvB j)) i).prod) (
            (zs.map fun i => ρ.op (F (a3ConvSpectator j)) i).prod w)}

theorem a3_gradedLower_le_pairMode (j : Fin 2) (xs ys zs : List ℕ)
    (k degree : ℕ) :
    gradedLowerModeSpan
      (fun i => ρ.op (F (a3ConvA j)) i)
      (fun i => ρ.op (F (a3ConvB j)) i)
      xs ys k degree
      (zs.map fun i => ρ.op (F (a3ConvSpectator j)) i).prod w ≤
    a3PairModeLowerSpan ρ w j zs xs.length (ys.length + k)
      degree xs.sum := by
  rw [gradedLowerModeSpan, a3PairModeLowerSpan, Submodule.span_le]
  rintro v ⟨as, bs, ha, hb, hd, hs, rfl⟩
  exact Submodule.subset_span ⟨as, bs, ha, hb, hd, hs, by simp [mul_smul]⟩

/-- All fixed-degree Garland defects enter the same smaller source-mode
span, independently of the monomial multiplier. -/
theorem a3_defect_reduces_pairMode (a b c : ℕ)
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
      a3PairModeLowerSpan ρ w j zs xs.length t (xs.sum + d) xs.sum ⊔
      a3HigherLeviClosure ρ w b c
        (a3ConvKey j k (xs.sum + d + zs.sum) xs
          (VOA.DeligneAudit.CLAssembly.lst f) zs) := by
  let ys := VOA.DeligneAudit.CLAssembly.lst f
  have hlen : ys.length + k = t := by
    dsimp [ys]
    rw [a2_lst_length]
    have ht := congrArg Prod.fst hw
    simp only [Prod.fst_add] at ht
    omega
  have h := a3_explicit_defect_reduces ρ w a b c h j xs zs f k s t d
    hk hks hw
  have hle := a3_gradedLower_le_pairMode ρ w j xs ys zs k
    (xs.sum + d)
  rw [hlen] at hle
  exact (sup_le_sup_right hle _) h

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_gradedLower_le_pairMode
#print axioms VOA.DeligneAudit.A3Sector.a3_defect_reduces_pairMode
