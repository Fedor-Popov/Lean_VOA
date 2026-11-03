import VOA.DeligneAudit.LeviTypeA2CertCountSpan

/-! Current coefficients preserve radical letter counts. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.LeviConversion
open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

/-- A coefficient of shifted compound currents contributes exactly one
compound radical letter per current factor. -/
theorem a2_bWord_coeff_count (ls : List ℕ) (s a b : ℕ) {v : V}
    (hv : v ∈ a2CountSpan ρ w a b) :
    PowerSeries.coeff s (bWord (fun i => ρ.op 5 i) ls) • v ∈
      a2CountSpan ρ w a (b + ls.length) := by
  induction ls generalizing s a b v with
  | nil =>
    by_cases hs : s = 0
    · subst s
      simpa [bWord] using hv
    · simp [bWord, hs]
  | cons x ls ih =>
    have hb : bWord (fun i => ρ.op 5 i) (x :: ls) =
        bTail (fun i => ρ.op 5 i) x * bWord (fun i => ρ.op 5 i) ls := rfl
    rw [hb, PowerSeries.coeff_mul, Finset.sum_smul]
    apply (a2CountSpan ρ w a (b + (x :: ls).length)).sum_mem
    intro z hz
    have htail := ih z.2 a b hv
    have h := a2CountSpan_second ρ w a (b + ls.length) (x + z.1) htail
    simpa [bTail, mul_smul, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using h

/-- Every coefficient of a node-two current power preserves a Levi closure. -/
theorem a2_fCurrent_pow_preserves (S : Submodule ℂ V)
    (n s : ℕ) {v : V} (hv : v ∈ a2LeviClosure ρ S) :
    PowerSeries.coeff s (fCurrent (fun i => ρ.op 4 i) ^ n) • v ∈
      a2LeviClosure ρ S := by
  induction n generalizing s v with
  | zero =>
    by_cases hs : s = 0
    · subst s
      simpa [fCurrent] using hv
    · simp [hs]
  | succ n ih =>
    rw [pow_succ, PowerSeries.coeff_mul, Finset.sum_smul]
    apply (a2LeviClosure ρ S).sum_mem
    intro z hz
    have hf : ρ.op 4 z.2 v ∈ a2LeviClosure ρ S :=
      a2LeviClosure_inv ρ S 4 z.2 (Or.inr (Or.inl rfl)) hv
    simpa [fCurrent, mul_smul] using ih z.1 hf

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_bWord_coeff_count
#print axioms VOA.DeligneAudit.A3Sector.a2_fCurrent_pow_preserves
