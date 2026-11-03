import VOA.DeligneAudit.LeviTypeA2CertF2Higher

/-! The full lower Wick sum is absorbed by higher radical keys. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.LeviConversion
open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

theorem a2_f2_lower_wick_higher (q k s : ℕ) (xs ys : List ℕ)
    (d : ℕ) (t : List ℕ × List ℕ)
    (ht : t ∈ choices (xs ++ List.replicate k 0))
    (hlt : t.2.length < k) :
    conversionTerm (fun i => ρ.op 4 i) (fun i => ρ.op 3 i)
      (fun i => ρ.op 5 i) k s t •
      (((ys.map fun i => ρ.op 5 i).prod * 1) • w) ∈
        a2LeviClosure ρ
          (a2HigherKeySpan ρ w q ⟨xs.length, ys.length + k, d⟩) := by
  let N := a2LeviClosure ρ
    (a2HigherKeySpan ρ w q ⟨xs.length, ys.length + k, d⟩)
  have hsum :
      (∑ z ∈ Finset.antidiagonal s,
        (PowerSeries.coeff z.1
            (fCurrent (fun i => ρ.op 4 i) ^ (k - t.2.length)) *
          aWord (fun i => ρ.op 3 i) t.1) *
          PowerSeries.coeff z.2 (bWord (fun i => ρ.op 5 i) t.2)) •
        ((ys.map fun i => ρ.op 5 i).prod • w) ∈ N := by
    rw [Finset.sum_smul]
    apply N.sum_mem
    intro z hz
    exact a2_f2_lower_wick_summand ρ w q k xs ys t ht hlt d z
  have hscalar (c : ℂ) :
      (algebraMap ℂ (Module.End ℂ V) c) •
        ((∑ z ∈ Finset.antidiagonal s,
          (PowerSeries.coeff z.1
              (fCurrent (fun i => ρ.op 4 i) ^ (k - t.2.length)) *
            aWord (fun i => ρ.op 3 i) t.1) *
            PowerSeries.coeff z.2 (bWord (fun i => ρ.op 5 i) t.2)) •
          ((ys.map fun i => ρ.op 5 i).prod • w)) ∈ N := by
    simpa using N.smul_mem c hsum
  have hcast : ((-1 : Module.End ℂ V) ^ t.2.length *
      (k.descFactorial t.2.length : Module.End ℂ V)) =
      algebraMap ℂ (Module.End ℂ V)
        ((-1 : ℂ) ^ t.2.length * (k.descFactorial t.2.length : ℂ)) := by
    simp
  unfold conversionTerm
  rw [hcast, mul_smul]
  simpa only [mul_one] using
    hscalar ((-1 : ℂ) ^ t.2.length * (k.descFactorial t.2.length : ℂ))

/-- F₂ Garland defects convert to smaller first-colour mode sum modulo
the Levi closure of all strictly higher keys. -/
theorem a2_f2_box_conversion_higher (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) (k s : ℕ)
    (hk : 1 ≤ k) (hks : q + 1 ≤ k + s)
    (xs ys : List ℕ) (d : ℕ) :
    boxTarget (fun i => ρ.op 3 i) (fun i => ρ.op 5 i)
      k s xs ys 1 w ∈
      lowerModeSpan (fun i => ρ.op 3 i) (fun i => ρ.op 5 i)
        xs 1 w ⊔
      a2LeviClosure ρ
        (a2HigherKeySpan ρ w q ⟨xs.length, ys.length + k, d⟩) := by
  apply a2_f2_box_conversion ρ w p q h k s hk hks xs ys _
  intro t ht hlt
  exact a2_f2_lower_wick_higher ρ w q k s xs ys d t ht hlt

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_f2_lower_wick_higher
#print axioms VOA.DeligneAudit.A3Sector.a2_f2_box_conversion_higher
