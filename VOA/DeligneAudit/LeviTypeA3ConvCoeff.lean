import VOA.DeligneAudit.LeviTypeA3ConvCount

/-! Shifted radical-current coefficients preserve three-colour letter counts. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

theorem a3_bWord_coeff_count (i : Fin 3) (ls : List ℕ)
    (s d₁ d₂ d₃ : ℕ) {v : V}
    (hv : v ∈ a3CountSpan ρ w d₁ d₂ d₃) :
    PowerSeries.coeff s (bWord (fun t => ρ.op (F i) t) ls) • v ∈
      a3CountSpan ρ w
        (d₁ + if i = 0 then ls.length else 0)
        (d₂ + if i = 1 then ls.length else 0)
        (d₃ + if i = 2 then ls.length else 0) := by
  induction ls generalizing s d₁ d₂ d₃ v with
  | nil =>
      by_cases hs : s = 0
      · subst s
        simpa [bWord] using hv
      · simp [bWord, hs]
  | cons x xs ih =>
      change PowerSeries.coeff s
        (bTail (fun t => ρ.op (F i) t) x *
          bWord (fun t => ρ.op (F i) t) xs) • v ∈ _
      rw [PowerSeries.coeff_mul, Finset.sum_smul]
      apply (a3CountSpan ρ w
        (d₁ + if i = 0 then (x :: xs).length else 0)
        (d₂ + if i = 1 then (x :: xs).length else 0)
        (d₃ + if i = 2 then (x :: xs).length else 0)).sum_mem
      intro z hz
      have htail := ih z.2 d₁ d₂ d₃ hv
      have h := a3CountSpan_op ρ w i (x + z.1) _ _ _ htail
      fin_cases i <;>
        simpa [bTail, mul_smul, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using h

theorem a3_fCurrent_pow_preserves (j : Fin 2)
    (S : Submodule ℂ V) (n s : ℕ)
    {v : V} (hv : v ∈ a3LeviClosure ρ S) :
    PowerSeries.coeff s
      (fCurrent (fun t => ρ.op (leviF j) t) ^ n) • v ∈
        a3LeviClosure ρ S := by
  induction n generalizing s v with
  | zero =>
      by_cases hs : s = 0
      · subst s
        simpa [fCurrent] using hv
      · simp [hs]
  | succ n ih =>
      rw [pow_succ, PowerSeries.coeff_mul, Finset.sum_smul]
      apply (a3LeviClosure ρ S).sum_mem
      intro z hz
      have hf : ρ.op (leviF j) z.2 v ∈ a3LeviClosure ρ S := by
        fin_cases j
        · exact a3LeviClosure_inv ρ S 3 z.2 hv
        · exact a3LeviClosure_inv ρ S 4 z.2 hv
      simpa [fCurrent, mul_smul] using ih z.1 hf

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_bWord_coeff_count
#print axioms VOA.DeligneAudit.A3Sector.a3_fCurrent_pow_preserves
