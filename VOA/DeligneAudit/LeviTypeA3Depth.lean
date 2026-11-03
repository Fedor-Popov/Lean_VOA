import VOA.DeligneAudit.LeviTypeA3FiniteBox

/-! Global radical-depth cutoff from the three sharp colour counts. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : VOA.DeligneAudit.SectorWeyl.CurrentModule bracketTable V) (w : V)

theorem a3_radical_counts_sum (l : List (Fin 3 × ℕ)) :
    l.countP (fun x => x.1 = 0) + l.countP (fun x => x.1 = 1) +
      l.countP (fun x => x.1 = 2) = l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
      rcases x with ⟨i, s⟩
      fin_cases i <;> simp_all <;> omega

/-- A radical word longer than the sum of its three colour limits vanishes. -/
theorem a3_radicalWord_zero_of_depth_gt (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (l : List (Fin 3 × ℕ))
    (hl : 3 * a + 2 * b + c < l.length) :
    radicalWord (radicalOp ρ) l • w = 0 := by
  have hsum := a3_radical_counts_sum l
  by_cases h₀ : a < l.countP (fun x => x.1 = 0)
  · exact a3_radicalWord_zero_of_count ρ w a b c h 0 l
      (by simpa using h₀)
  by_cases h₁ : a + b < l.countP (fun x => x.1 = 1)
  · exact a3_radicalWord_zero_of_count ρ w a b c h 1 l
      (by simpa using h₁)
  have h₂ : a + b + c < l.countP (fun x => x.1 = 2) := by omega
  exact a3_radicalWord_zero_of_count ρ w a b c h 2 l
    (by simpa using h₂)

/-- No radical layer survives above depth `3a+2b+c`. -/
theorem a3_radicalLayer_eq_bot_of_depth_gt (a b c j : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (hj : 3 * a + 2 * b + c < j) :
    radicalLayer (radicalOp ρ) w j = ⊥ := by
  rw [radicalLayer, eq_bot_iff, Submodule.span_le]
  intro z hz
  obtain ⟨l, hlen, rfl⟩ := hz
  rw [a3_radicalWord_zero_of_depth_gt ρ w a b c h l (by omega)]
  exact Submodule.zero_mem _

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_radical_counts_sum
#print axioms VOA.DeligneAudit.A3Sector.a3_radicalWord_zero_of_depth_gt
#print axioms VOA.DeligneAudit.A3Sector.a3_radicalLayer_eq_bot_of_depth_gt
