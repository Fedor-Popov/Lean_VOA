import VOA.DeligneAudit.LeviTypeA2CertGradedInduction

/-! Strong induction passes from sorted words to the whole radical key layer. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.LeviTypeA VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

private theorem a2_split_modes_sum (l : List (Fin 2 × ℕ)) :
    (firstModes l).sum + (secondModes l).sum =
      (l.map Prod.snd).sum := by
  induction l with
  | nil => simp [firstModes, secondModes]
  | cons x l ih =>
      rcases x with ⟨i, s⟩
      fin_cases i <;>
        simp [firstModes, secondModes] at * <;> omega

/-- At a fixed key, radical generators are spanned by both box families
modulo the Levi closure of strictly higher keys. -/
theorem a2KeyLayer_le_two_boxes (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) (k : A2RadicalKey) :
    a2KeyLayer ρ w k ≤
      a2TwoBoxKeySpan ρ w p q k.d₁ k.d₂ k.degree ⊔
        a2LeviClosure ρ (a2HigherKeySpan ρ w q k) := by
  rw [a2KeyLayer, Submodule.span_le]
  intro z hz
  obtain ⟨l, hfirst, hsecond, hdegree, _, rfl⟩ := hz
  let xs := firstModes l
  let ys := secondModes l
  have hxa : xs.length = k.d₁ := by
    calc
      _ = l.countP (fun x => x.1 = 0) := by
        simp [xs, firstModes, List.countP_eq_length_filter]
      _ = k.d₁ := hfirst
  have hyb : ys.length = k.d₂ := by
    calc
      _ = l.countP (fun x => x.1 = 1) := by
        simp [ys, secondModes, List.countP_eq_length_filter]
      _ = k.d₂ := hsecond
  have hsum : xs.sum + ys.sum = k.degree := by
    exact (a2_split_modes_sum l).trans hdegree
  have hboxes := a2_radical_word_two_boxes ρ w p q h xs ys
  have hword : radicalWord (a2RadicalOp ρ) l • w =
      (aWord (fun i => ρ.op 3 i) xs *
        (ys.map fun i => ρ.op 5 i).prod) w := by
    rw [radicalWord_split ρ l]
    rfl
  rw [hword]
  simpa only [hxa, hyb, hsum] using hboxes

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2KeyLayer_le_two_boxes
