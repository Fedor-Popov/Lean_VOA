import VOA.DeligneAudit.LeviTypeA3ConvHigher

/-! Both graded conversions with their lower Wick sums absorbed. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

theorem a3_lower_wick_term (b c k s d : ℕ)
    (j : Fin 2) (xs ys zs : List ℕ)
    (p : List ℕ × List ℕ)
    (hp : p ∈ choices (xs ++ List.replicate k 0))
    (hshort : p.2.length < k) :
    let f : ℕ → Module.End ℂ V := fun i => ρ.op (leviF j) i
    let A : ℕ → Module.End ℂ V := fun i => ρ.op (F (a3ConvA j)) i
    let B : ℕ → Module.End ℂ V := fun i => ρ.op (F (a3ConvB j)) i
    let R : Module.End ℂ V :=
      (zs.map fun i => ρ.op (F (a3ConvSpectator j)) i).prod
    conversionTerm f A B k s p • (((ys.map B).prod * R) • w) ∈
      a3HigherLeviClosure ρ w b c (a3ConvKey j k d xs ys zs) := by
  let N := a3HigherLeviClosure ρ w b c (a3ConvKey j k d xs ys zs)
  let f : ℕ → Module.End ℂ V := fun i => ρ.op (leviF j) i
  let A : ℕ → Module.End ℂ V := fun i => ρ.op (F (a3ConvA j)) i
  let B : ℕ → Module.End ℂ V := fun i => ρ.op (F (a3ConvB j)) i
  let R : Module.End ℂ V :=
    (zs.map fun i => ρ.op (F (a3ConvSpectator j)) i).prod
  have hsum :
      (∑ z ∈ Finset.antidiagonal s,
        (PowerSeries.coeff z.1 (fCurrent f ^ (k - p.2.length)) *
          aWord A p.1) * PowerSeries.coeff z.2 (bWord B p.2)) •
        (((ys.map B).prod * R) • w) ∈ N := by
    rw [Finset.sum_smul]
    apply N.sum_mem
    intro z hz
    exact a3_lower_wick_summand ρ w b c k d j xs ys zs p hp hshort z
  have hscalar (z : ℂ) :
      (algebraMap ℂ (Module.End ℂ V) z) •
        ((∑ x ∈ Finset.antidiagonal s,
          (PowerSeries.coeff x.1 (fCurrent f ^ (k - p.2.length)) *
            aWord A p.1) * PowerSeries.coeff x.2 (bWord B p.2)) •
          (((ys.map B).prod * R) • w)) ∈ N := by
    simpa using N.smul_mem z hsum
  have hcast : ((-1 : Module.End ℂ V) ^ p.2.length *
      (k.descFactorial p.2.length : Module.End ℂ V)) =
      algebraMap ℂ (Module.End ℂ V)
        ((-1 : ℂ) ^ p.2.length * (k.descFactorial p.2.length : ℂ)) := by
    simp
  unfold conversionTerm
  rw [hcast]
  simpa only [mul_smul] using
    hscalar ((-1 : ℂ) ^ p.2.length * (k.descFactorial p.2.length : ℂ))

theorem a3_box_conversion_graded (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (j : Fin 2) (k s : ℕ) (hk : 1 ≤ k)
    (hks : (weightABC a b c) (Fin.succ j) + 1 ≤ k + s)
    (xs ys zs : List ℕ) (d : ℕ) :
    let A : ℕ → Module.End ℂ V := fun i => ρ.op (F (a3ConvA j)) i
    let B : ℕ → Module.End ℂ V := fun i => ρ.op (F (a3ConvB j)) i
    let R : Module.End ℂ V :=
      (zs.map fun i => ρ.op (F (a3ConvSpectator j)) i).prod
    boxTarget A B k s xs ys R w ∈
      gradedLowerModeSpan A B xs ys k (xs.sum + ys.sum + s) R w ⊔
        a3HigherLeviClosure ρ w b c (a3ConvKey j k d xs ys zs) := by
  apply a3_box_conversion_graded_of_higher ρ w a b c h j k s hk hks
    xs ys zs (a3HigherLeviClosure ρ w b c (a3ConvKey j k d xs ys zs))
  dsimp only
  intro p hp hshort
  exact a3_lower_wick_term ρ w b c k s d j xs ys zs p hp hshort

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_lower_wick_term
#print axioms VOA.DeligneAudit.A3Sector.a3_box_conversion_graded
