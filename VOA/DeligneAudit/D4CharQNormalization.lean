import VOA.DeligneAudit.D4CharGTIndependent

/-! Pochhammer units and the Q normalization, including integral formal power series. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open VOA.DeligneGaussian

noncomputable section

variable {R : Type*} [CommRing R]

/-- The unit hypothesis needed for normalized q-Whittaker functions. -/
def PochhammerUnits (q : R) : Prop := ∀ n, IsUnit (CarrierChain.qpochGen q n)

/-- A bundled Pochhammer unit; its value is exactly the finite product. -/
def gtPochUnit (q : R) (h : PochhammerUnits q) (n : ℕ) : Rˣ := (h n).unit

@[simp] theorem gtPochUnit_val (q : R) (h : PochhammerUnits q) (n : ℕ) :
    (gtPochUnit q h n : R) = CarrierChain.qpochGen q n := (h n).unit_spec

@[simp] theorem gtPochUnit_zero (q : R) (h : PochhammerUnits q) :
    gtPochUnit q h 0 = 1 := by
  apply Units.ext
  simp

/-- Every Pochhammer product at the formal parameter is a unit over any base ring. -/
theorem powerSeries_pochhammerUnits (A : Type*) [CommRing A] :
    PochhammerUnits (PowerSeries.X : PowerSeries A) := by
  intro n
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  have hc : PowerSeries.constantCoeff
      (CarrierChain.qpochGen (PowerSeries.X : PowerSeries A) n) = 1 := by
    simp [CarrierChain.qpochGen, map_prod]
  rw [hc]
  exact isUnit_one

/-- Adjacent gaps, with a final zero appended to the partition. -/
def gtGap {N : ℕ} (lam : Fin N → ℤ) (i : Fin N) : ℕ :=
  (Fin.snoc (α := fun _ => ℤ) lam 0 i.castSucc - Fin.snoc (α := fun _ => ℤ) lam 0 i.succ).toNat

@[simp] theorem gtGap_castSucc {N : ℕ} (lam : Fin (N + 1) → ℤ) (i : Fin N) :
    gtGap lam i.castSucc = (lam i.castSucc - lam i.succ).toNat := by
  simp [gtGap, ← Fin.castSucc_succ]

@[simp] theorem gtGap_last {N : ℕ} (lam : Fin (N + 1) → ℤ) :
    gtGap lam (Fin.last N) = (lam (Fin.last N)).toNat := by
  simp [gtGap]

/-- The normalization b_lambda, as a unit rather than a field quotient. -/
def gtNormUnit (q : R) (h : PochhammerUnits q) {N : ℕ} (lam : Fin N → ℤ) : Rˣ :=
  ∏ i, (gtPochUnit q h (gtGap lam i))⁻¹

/-- The terminal factor in the normalized GT branching formula. -/
theorem gtNormUnit_succ (q : R) (h : PochhammerUnits q) {N : ℕ}
    (lam : Fin (N + 1) → ℤ) :
    gtNormUnit q h lam =
      (∏ i : Fin N, (gtPochUnit q h (lam i.castSucc - lam i.succ).toNat)⁻¹) *
        (gtPochUnit q h (lam (Fin.last N)).toNat)⁻¹ := by
  rw [gtNormUnit, Fin.prod_univ_castSucc]
  simp

/-- The inverse normalization is the product of the numerator Pochhammer factors. -/
theorem gtNormUnit_inv_val (q : R) (h : PochhammerUnits q) {N : ℕ}
    (lam : Fin N → ℤ) :
    ((gtNormUnit q h lam)⁻¹ : Rˣ) = ∏ i, gtPochUnit q h (gtGap lam i) := by
  simp [gtNormUnit, ← Finset.prod_inv_distrib]

/-- Gaussian normalization, valid over rings with zero divisors as well. -/
theorem gtGaussian_normalized (q : R) (h : PochhammerUnits q) (n k : ℕ) (hk : k ≤ n) :
    qbinom q n k * ((gtPochUnit q h n)⁻¹ : Rˣ) =
      (((gtPochUnit q h k)⁻¹ : Rˣ) : R) * ((gtPochUnit q h (n - k))⁻¹ : Rˣ) := by
  have hb := CarrierChain.qbinom_mul_qpochGen q n k hk
  have he := congrArg
    (fun x : R => x * ((gtPochUnit q h n)⁻¹ : Rˣ) *
      ((gtPochUnit q h k)⁻¹ : Rˣ) * ((gtPochUnit q h (n - k))⁻¹ : Rˣ)) hb
  simp only [← gtPochUnit_val q h] at he
  simpa only [mul_assoc, mul_comm, mul_left_comm, Units.val_mul, Units.mul_inv,
    mul_one, one_mul] using he

/-- Q evaluated at unit variables. For partitions, the normalization is b_lambda P_lambda. -/
def gtQ (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ) (N : ℕ) (lam : Fin N → ℤ) : R :=
  (gtNormUnit q h lam : R) * gtEval q u N lam

/-- Normalized branching coefficient on the interlacing region. -/
def gtQBranch (q : R) (h : PochhammerUnits q) {N : ℕ}
    (lam : Fin (N + 1) → ℤ) (μ : Fin N → ℤ) : R :=
  gtPsi q lam μ * (gtNormUnit q h lam : R) * ((gtNormUnit q h μ)⁻¹ : Rˣ)

/-- Normalized GT branching, with no division in the coefficient ring. -/
theorem gtQ_branching (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (N : ℕ) (lam : Fin (N + 1) → ℤ) :
    gtQ q h u (N + 1) lam = ∑ μ ∈ gtRows lam,
      gtQBranch q h lam μ * (((u N) ^ ((∑ i, lam i) - ∑ i, μ i) : Rˣ) : R) * gtQ q h u N μ := by
  rw [gtQ, gtEval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro μ _
  simp only [gtQBranch, gtQ]
  have hc : (((gtNormUnit q h μ)⁻¹ : Rˣ) : R) * (gtNormUnit q h μ : R) = 1 :=
    Units.inv_mul _
  calc
    _ = (gtNormUnit q h lam : R) *
        (gtPsi q lam μ * (((u N) ^ ((∑ i, lam i) - ∑ i, μ i) : Rˣ) : R) *
          gtEval q u N μ) *
        ((((gtNormUnit q h μ)⁻¹ : Rˣ) : R) * (gtNormUnit q h μ : R)) := by
      rw [hc, mul_one]
    _ = _ := by ring

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.powerSeries_pochhammerUnits
#print axioms VOA.DeligneAudit.D4Char.gtNormUnit_succ
#print axioms VOA.DeligneAudit.D4Char.gtGaussian_normalized
#print axioms VOA.DeligneAudit.D4Char.gtQ_branching
