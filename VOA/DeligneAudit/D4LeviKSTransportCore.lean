import VOA.DeligneAudit.D4LeviKSTransportSeries

/-! Exact mixed Garland relations at the D4 cyclic source. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

private theorem factorial_smul_zero (n : ℕ) (A : Module.End ℂ V)
    (h : (n.factorial • A) w = 0) : A w = 0 := by
  have hh : (n.factorial : ℂ) • A w = 0 := by
    simpa only [Nat.cast_smul_eq_nsmul, map_nsmul] using h
  exact (smul_eq_zero.mp hh).resolve_left (by exact_mod_cast Nat.factorial_ne_zero n)

private theorem descFactorial_smul_zero (n k : ℕ) (hk : k ≤ n)
    (A : Module.End ℂ V) (h : (n.descFactorial k • A) w = 0) : A w = 0 := by
  have hh : (n.descFactorial k : ℂ) • A w = 0 := by
    simpa only [Nat.cast_smul_eq_nsmul, map_nsmul] using h
  have hn : (n.descFactorial k : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hk))
  exact (smul_eq_zero.mp hh).resolve_left hn

/-- Partial f₂ transport leaves a mixed f₂/X Garland relation at the source. -/
theorem x_partial_garland_zero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (rs : List ℕ) (n s : ℕ) (hk : 1 ≤ n + rs.length)
    (hks : m + 1 ≤ n + rs.length + s) :
    (PowerSeries.coeff s
      (fCurrent (fOp ρ) ^ n *
        (rs.map (transportCurrent (xOp ρ))).prod)) w = 0 := by
  have ht := fTwo_garland_transport_zero ρ w m h
    (n + rs.length) s hk hks rs
  rw [fTwo_garland_partial_transport ρ rs n s] at ht
  exact descFactorial_smul_zero w (n + rs.length) rs.length (by omega) _ ht

/-- Partial f₂₃₄ transport leaves a mixed f₂₃₄/Y Garland relation. -/
theorem y_partial_garland_zero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (rs : List ℕ) (n s : ℕ) (hk : 1 ≤ n + rs.length)
    (hks : m + 1 ≤ n + rs.length + s) :
    (PowerSeries.coeff s
      (fCurrent (fTopOp ρ) ^ n *
        (rs.map (transportCurrent (yOp ρ))).prod)) w = 0 := by
  have ht := fTop_garland_transport_zero ρ w m h
    (n + rs.length) s hk hks rs
  rw [fTop_garland_partial_transport ρ rs n s] at ht
  exact descFactorial_smul_zero w (n + rs.length) rs.length (by omega) _ ht

/-- Every admissible mixed X Garland coefficient kills the cyclic source. -/
theorem x_mixed_garland_zero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (rs : List ℕ) (s : ℕ) (hk : 1 ≤ rs.length)
    (hks : m + 1 ≤ rs.length + s) :
    (PowerSeries.coeff s
      (rs.map (transportCurrent (xOp ρ))).prod) w = 0 := by
  have ht := fTwo_garland_transport_zero ρ w m h rs.length s hk hks rs
  rw [fTwo_garland_full_transport ρ rs s] at ht
  exact factorial_smul_zero w rs.length _ ht

/-- Every admissible mixed Y Garland coefficient kills the cyclic source. -/
theorem y_mixed_garland_zero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (rs : List ℕ) (s : ℕ) (hk : 1 ≤ rs.length)
    (hks : m + 1 ≤ rs.length + s) :
    (PowerSeries.coeff s
      (rs.map (transportCurrent (yOp ρ))).prod) w = 0 := by
  have ht := fTop_garland_transport_zero ρ w m h rs.length s hk hks rs
  rw [fTop_garland_full_transport ρ rs s] at ht
  exact factorial_smul_zero w rs.length _ ht

/-- An arbitrary left radical spectator preserves the exact X relation. -/
theorem x_mixed_garland_spectator_zero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (rs : List ℕ) (s : ℕ) (hk : 1 ≤ rs.length)
    (hks : m + 1 ≤ rs.length + s) (T : Module.End ℂ V) :
    (T * PowerSeries.coeff s
      (rs.map (transportCurrent (xOp ρ))).prod) w = 0 := by
  simp [Module.End.mul_apply, x_mixed_garland_zero ρ w m h rs s hk hks]

/-- An arbitrary left radical spectator preserves the exact Y relation. -/
theorem y_mixed_garland_spectator_zero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (rs : List ℕ) (s : ℕ) (hk : 1 ≤ rs.length)
    (hks : m + 1 ≤ rs.length + s) (T : Module.End ℂ V) :
    (T * PowerSeries.coeff s
      (rs.map (transportCurrent (yOp ρ))).prod) w = 0 := by
  simp [Module.End.mul_apply, y_mixed_garland_zero ρ w m h rs s hk hks]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.x_mixed_garland_zero
#print axioms VOA.DeligneAudit.D4Levi.y_mixed_garland_zero
#print axioms VOA.DeligneAudit.D4Levi.x_partial_garland_zero
#print axioms VOA.DeligneAudit.D4Levi.y_partial_garland_zero
#print axioms VOA.DeligneAudit.D4Levi.x_mixed_garland_spectator_zero
#print axioms VOA.DeligneAudit.D4Levi.y_mixed_garland_spectator_zero
