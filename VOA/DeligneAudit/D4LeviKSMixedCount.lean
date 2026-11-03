import VOA.DeligneAudit.D4LeviKSMixedTop

/-! Fixed XYZ letter counts for coefficients of shifted radical current products. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)

theorem x_transport_coeff_count (rs : List ℕ) (s x y z : ℕ)
    {v : V} (hv : v ∈ xyzCountSpan ρ w x y z) :
    PowerSeries.coeff s (rs.map (transportCurrent (xOp ρ))).prod v ∈
      xyzCountSpan ρ w (x + rs.length) y z := by
  induction rs generalizing s x y z v with
  | nil =>
      by_cases hs : s = 0
      · subst s
        simpa using hv
      · simp [hs]
  | cons r rs ih =>
      change PowerSeries.coeff s
        (transportCurrent (xOp ρ) r *
          (rs.map (transportCurrent (xOp ρ))).prod) v ∈ _
      rw [PowerSeries.coeff_mul]
      change (∑ q ∈ Finset.antidiagonal s,
        PowerSeries.coeff q.1 (transportCurrent (xOp ρ) r) *
          PowerSeries.coeff q.2
            (rs.map (transportCurrent (xOp ρ))).prod) • v ∈ _
      rw [Finset.sum_smul]
      apply (xyzCountSpan ρ w (x + (r :: rs).length) y z).sum_mem
      intro q hq
      have ht := ih q.2 x y z hv
      have hx := xyzCountSpan_op ρ w 1 (r + q.1)
        (x + rs.length) y z (Or.inl rfl) ht
      simpa [transportCurrent, xOp, mul_smul, Nat.add_assoc] using hx

theorem y_transport_coeff_count (rs : List ℕ) (s x y z : ℕ)
    {v : V} (hv : v ∈ xyzCountSpan ρ w x y z) :
    PowerSeries.coeff s (rs.map (transportCurrent (yOp ρ))).prod v ∈
      xyzCountSpan ρ w x (y + rs.length) z := by
  induction rs generalizing s x y z v with
  | nil =>
      by_cases hs : s = 0
      · subst s
        simpa using hv
      · simp [hs]
  | cons r rs ih =>
      change PowerSeries.coeff s
        (transportCurrent (yOp ρ) r *
          (rs.map (transportCurrent (yOp ρ))).prod) v ∈ _
      rw [PowerSeries.coeff_mul]
      change (∑ q ∈ Finset.antidiagonal s,
        PowerSeries.coeff q.1 (transportCurrent (yOp ρ) r) *
          PowerSeries.coeff q.2
            (rs.map (transportCurrent (yOp ρ))).prod) • v ∈ _
      rw [Finset.sum_smul]
      apply (xyzCountSpan ρ w x (y + (r :: rs).length) z).sum_mem
      intro q hq
      have ht := ih q.2 x y z hv
      have hy := xyzCountSpan_op ρ w 4 (r + q.1)
        x (y + rs.length) z (Or.inr (Or.inl rfl)) ht
      simpa [transportCurrent, yOp, mul_smul, Nat.add_assoc] using hy

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.x_transport_coeff_count
#print axioms VOA.DeligneAudit.D4Levi.y_transport_coeff_count
