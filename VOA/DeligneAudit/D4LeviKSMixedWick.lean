import VOA.DeligneAudit.D4LeviKSTransportCore

/-! Wick dressing of a partially transported Garland coefficient. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

/-- A Wick identity remains valid when the annihilating Garland power has a
    commuting radical power series on its right. The finite sum includes every
    contraction and every convolution of the transported modes. -/
theorem mixed_wick_zero (f a b : ℕ → Module.End ℂ V)
    (hfa : ∀ i j, f i * a j - a j * f i = b (i + j))
    (hfb : ∀ i j, f i * b j = b j * f i)
    (hab : ∀ i j, a i * b j = b j * a i)
    (k s : ℕ) (xs : List ℕ) (B : PowerSeries (Module.End ℂ V))
    (hkill : (PowerSeries.coeff s (fCurrent f ^ k * B)) w = 0) :
    (∑ q ∈ Finset.antidiagonal s,
      ((choices xs).map (conversionTerm f a b k q.1)).sum *
        PowerSeries.coeff q.2 B) w = 0 := by
  have hw := wick_series f a b hfa hfb hab k xs
  have hs : (∑ q ∈ Finset.antidiagonal s,
      ((choices xs).map (conversionTerm f a b k q.1)).sum *
        PowerSeries.coeff q.2 B) =
      PowerSeries.coeff s
        (wickSum (fCurrent f) (aConst a) (bTail b) k xs * B) := by
    rw [PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro q hq
    rw [coeff_wickSum]
  rw [hs, ← hw, aConst_word, mul_assoc, PowerSeries.coeff_C_mul]
  simp [Module.End.mul_apply, hkill]

/-- XZG Wick dressing: partial E-transport of the f₂ Garland element, followed
    by Y letters. Terms with all `c` contractions have only X, Y and Z colours;
    the remaining terms retain positive f₂ degree. -/
theorem x_mixed_wick_zero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (rs ys : List ℕ) (c s : ℕ)
    (hK : 1 ≤ rs.length)
    (hks : m + 1 ≤ c + rs.length + s) :
    (∑ q ∈ Finset.antidiagonal s,
      ((choices (ys ++ List.replicate c 0)).map
        (conversionTerm (fOp ρ) (yOp ρ) (zOp ρ) c q.1)).sum *
        PowerSeries.coeff q.2
          (rs.map (transportCurrent (xOp ρ))).prod) w = 0 := by
  apply mixed_wick_zero w (fOp ρ) (yOp ρ) (zOp ρ)
    (fTwo_y_comm ρ) (fTwo_z_comm ρ)
    (fun i j => by
      ext v
      simpa [yOp, zOp] using radical_ops_comm ρ 4 5 i j v)
  exact x_partial_garland_zero ρ w m h rs c s (by omega) hks

/-- YZG Wick dressing: the corresponding partial f₂₃₄/Y transport, dressed
    with X letters. -/
theorem y_mixed_wick_zero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (rs xs : List ℕ) (c s : ℕ)
    (hK : 1 ≤ rs.length)
    (hks : m + 1 ≤ c + rs.length + s) :
    (∑ q ∈ Finset.antidiagonal s,
      ((choices (xs ++ List.replicate c 0)).map
        (conversionTerm (fTopOp ρ) (xOp ρ) (zOp ρ) c q.1)).sum *
        PowerSeries.coeff q.2
          (rs.map (transportCurrent (yOp ρ))).prod) w = 0 := by
  apply mixed_wick_zero w (fTopOp ρ) (xOp ρ) (zOp ρ)
    (fTop_x_comm ρ) (fTop_z_comm ρ)
    (fun i j => by
      ext v
      simpa [xOp, zOp] using radical_ops_comm ρ 1 5 i j v)
  exact y_partial_garland_zero ρ w m h rs c s (by omega) hks

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.mixed_wick_zero
#print axioms VOA.DeligneAudit.D4Levi.x_mixed_wick_zero
#print axioms VOA.DeligneAudit.D4Levi.y_mixed_wick_zero
