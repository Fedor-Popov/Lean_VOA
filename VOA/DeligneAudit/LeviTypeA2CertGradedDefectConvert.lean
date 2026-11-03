import VOA.DeligneAudit.LeviTypeA2CertGradedDefectWeight

/-! Each fixed-bidegree F₂ defect admits the graded Levi conversion. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.Sl2Weyl VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

/-- A single F₂ Garland defect at a fixed radical key reduces to
smaller first-colour mode sum or a strictly higher key. -/
theorem a2_f2_explicit_defect_reduces (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q)
    (xs : List ℕ) (f : ℕ →₀ ℕ) (k s b d₂ : ℕ)
    (hk : 1 ≤ k) (hks : q + 1 ≤ k + s)
    (hw : Finsupp.weight om f + (k, s) = (b, d₂)) :
    let F : ℕ → Module.End ℂ V := fun i => ρ.op 5 i
    let hFF : ∀ i j, F i * F j = F j * F i := by
      intro i j
      apply sub_eq_zero.mp
      simp [F, op_comm_end, Fin.sum_univ_eight,
        VOA.AffineSl3.bracketTable]
    (aWord (fun i => ρ.op 3 i) xs *
      Sl2Weyl.evAlg F hFF (MvPolynomial.monomial f 1 * xx k s)) w ∈
      gradedLowerModeSpan (fun i => ρ.op 3 i) F xs
        (VOA.DeligneAudit.CLAssembly.lst f) k (xs.sum + d₂) 1 w ⊔
      a2LeviClosure ρ
        (a2HigherKeySpan ρ w q ⟨xs.length, b, xs.sum + d₂⟩) := by
  let F : ℕ → Module.End ℂ V := fun i => ρ.op 5 i
  let hFF : ∀ i j, F i * F j = F j * F i := by
    intro i j
    apply sub_eq_zero.mp
    simp [F, op_comm_end, Fin.sum_univ_eight,
      VOA.AffineSl3.bracketTable]
  let ys := VOA.DeligneAudit.CLAssembly.lst f
  have hlen : ys.length + k = b := by
    dsimp [ys]
    rw [a2_lst_length]
    simpa using congrArg Prod.fst hw
  have hsum : ys.sum + s = d₂ := by
    dsimp [ys]
    rw [a2_lst_sum]
    simpa using congrArg Prod.snd hw
  have hconvert := a2_f2_box_conversion_graded ρ w p q h
    k s hk hks xs ys
  have htarget :
      boxTarget (fun i => ρ.op 3 i) F k s xs ys 1 w =
      (aWord (fun i => ρ.op 3 i) xs *
        Sl2Weyl.evAlg F hFF (MvPolynomial.monomial f 1 * xx k s)) w := by
    exact (a2_graded_defect_as_boxTarget
      (fun i => ρ.op 3 i) F hFF xs f k s w).symm
  rw [htarget] at hconvert
  have hdegree : xs.sum + ys.sum + s = xs.sum + d₂ := by omega
  simpa only [F, hlen, hdegree] using hconvert

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_f2_explicit_defect_reduces
