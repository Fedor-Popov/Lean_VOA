import VOA.DeligneAudit.LeviTypeA3ConversionComm

/-! Both graded root-string conversions, pending absorption of lower Wick terms. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

/-- The graded KS conversion for either adjacent radical pair. The hypothesis
identifies the lower Wick terms in a caller-provided higher-key submodule. -/
theorem a3_box_conversion_graded_of_higher (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (j : Fin 2) (k s : ℕ) (hk : 1 ≤ k)
    (hks : (weightABC a b c) (Fin.succ j) + 1 ≤ k + s)
    (xs ys zs : List ℕ) (N : Submodule ℂ V)
    (hHigher :
      let f : ℕ → Module.End ℂ V := fun i => ρ.op (leviF j) i
      let A : ℕ → Module.End ℂ V := fun i => ρ.op (F (a3ConvA j)) i
      let B : ℕ → Module.End ℂ V := fun i => ρ.op (F (a3ConvB j)) i
      let R : Module.End ℂ V :=
        (zs.map fun i => ρ.op (F (a3ConvSpectator j)) i).prod
      ∀ p ∈ choices (xs ++ List.replicate k 0), p.2.length < k →
        conversionTerm f A B k s p • (((ys.map B).prod * R) • w) ∈ N) :
    let A : ℕ → Module.End ℂ V := fun i => ρ.op (F (a3ConvA j)) i
    let B : ℕ → Module.End ℂ V := fun i => ρ.op (F (a3ConvB j)) i
    let R : Module.End ℂ V :=
      (zs.map fun i => ρ.op (F (a3ConvSpectator j)) i).prod
    boxTarget A B k s xs ys R w ∈
      gradedLowerModeSpan A B xs ys k (xs.sum + ys.sum + s) R w ⊔ N := by
  let f : ℕ → Module.End ℂ V := fun i => ρ.op (leviF j) i
  let A : ℕ → Module.End ℂ V := fun i => ρ.op (F (a3ConvA j)) i
  let B : ℕ → Module.End ℂ V := fun i => ρ.op (F (a3ConvB j)) i
  let R : Module.End ℂ V :=
    (zs.map fun i => ρ.op (F (a3ConvSpectator j)) i).prod
  have hfa : ∀ i t, f i * A t - A t * f i = B (i + t) := by
    intro i t
    exact a3_conversion_step ρ j i t
  have hfb : ∀ i t, f i * B t = B t * f i := by
    intro i t
    exact a3_conversion_other ρ j (a3ConvB j) (Or.inl rfl) i t
  have hab : ∀ i t, A i * B t = B t * A i := by
    intro i t
    exact a3_conversion_radical_comm ρ (a3ConvA j) (a3ConvB j) i t
  have haa : ∀ i t, A i * A t = A t * A i := by
    intro i t
    exact a3_conversion_radical_comm ρ (a3ConvA j) (a3ConvA j) i t
  have hRf : ∀ i, R * f i = f i * R := by
    intro i
    exact a3_conversion_spectator_comm ρ j zs i
  have hfj : simpleF (Fin.succ j) = leviF j := by
    fin_cases j <;> rfl
  have hkill : PowerSeries.coeff s (fCurrent f ^ k) • w = 0 := by
    simpa only [hfj] using
      a3_simple_conversion_kill ρ w a b c h (Fin.succ j) k s hk hks
  exact box_conversion_graded f A B hfa hfb hab haa k s xs ys R w
    hRf hkill (by intro z v; simp) N hHigher

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_box_conversion_graded_of_higher
