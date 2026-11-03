import VOA.DeligneAudit.D4CharKernelScalars

/-! The rank-two GT factors of mixed Cauchy are the actual Rogers--Szego polynomials. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open VOA.DeligneGaussian DeligneCharacter

noncomputable section

/-- A Laurent monomial with coefficient one, bundled as a unit. -/
def rsMonUnit (v : D4K.V) : D4K.Rˣ where
  val := D4K.mon v 1
  inv := D4K.mon (-v) 1
  val_inv := by rw [D4K.mon_mul_mon, add_neg_cancel, mul_one]; rfl
  inv_val := by rw [D4K.mon_mul_mon, neg_add_cancel, mul_one]; rfl

/-- The exponent-lattice homomorphism into Laurent monomial units. -/
def rsMonUnitHom : Multiplicative D4K.V →* D4K.Rˣ where
  toFun v := rsMonUnit (Multiplicative.toAdd v)
  map_one' := by apply Units.ext; rfl
  map_mul' v w := by
    apply Units.ext
    change D4K.mon _ 1 = D4K.mon _ 1 * D4K.mon _ 1
    rw [D4K.mon_mul_mon, mul_one]
    rfl

theorem rsMonUnit_zpow (v : D4K.V) (a : ℤ) :
    ((rsMonUnit v ^ a : D4K.Rˣ) : D4K.R) = D4K.mon (a • v) 1 := by
  have h := map_zpow rsMonUnitHom (Multiplicative.ofAdd v) a
  change rsMonUnit (a • v) = rsMonUnit v ^ a at h
  rw [← h]
  rfl

/-- The ordered alphabet (x,x^-1) of the paper. Only its first two entries are used. -/
def rsXAlphabet (i : ℕ) : D4K.Rˣ := if i = 0 then rsMonUnit D4K.xv else rsMonUnit (-D4K.xv)

theorem rsXAlphabet_det : (rsXAlphabet 0 : D4K.R) * (rsXAlphabet 1 : D4K.R) = 1 := by
  simp only [rsXAlphabet, ite_true, if_pos rfl, if_neg (by decide : (1 : ℕ) ≠ 0)]
  change D4K.mon D4K.xv 1 * D4K.mon (-D4K.xv) 1 = 1
  rw [D4K.mon_mul_mon, add_neg_cancel, mul_one]
  rfl

/-- GT in the one-row case gives H_k, including the full Gaussian sum. -/
theorem rsGT_oneRow (k : ℕ) :
    gtEval rsNome rsXAlphabet 2 ![(k : ℤ), 0] = rsH k := by
  rw [gtEval]
  have hs := sum_gtRows_two_nat (A := D4K.R) k 0
  simp only [Nat.cast_zero] at hs
  rw [hs]
  rw [show Finset.Icc 0 k = Finset.range (k + 1) by ext i; simp]
  unfold rsH
  rw [← Finset.sum_range_reflect
    (fun j => D4K.mon (((k : ℤ) - 2 * j) • D4K.xv) (qbinom D4K.qq k j)) (k + 1)]
  apply Finset.sum_congr rfl
  intro r hr
  have hrk : r ≤ k := by simpa using Finset.mem_range.mp hr
  simp only [gtPsi, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Fin.castSucc_zero, sub_zero, Int.toNat_natCast, Int.toNat_sub, gtEval_one,
    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.add_sub_cancel]
  simp only [rsXAlphabet, ite_true, if_pos rfl, if_neg (by decide : (1 : ℕ) ≠ 0),
    rsMonUnit_zpow]
  rw [rsNome, ← A2.map_qbinom rsCoeff]
  rw [D4K.algebraMap_mul_mon, mul_one, D4K.mon_mul_mon, mul_one]
  congr 1
  rw [smul_neg, ← neg_smul, ← add_smul]
  congr 1
  omega

/-- Removing the determinant factor identifies every two-row P with H_(a-b). -/
theorem rsGT_two (a b : ℕ) (hab : b ≤ a) :
    gtEval rsNome rsXAlphabet 2 ![(a : ℤ), (b : ℤ)] = rsH (a - b) := by
  have h := gtEval_two_shift rsNome rsXAlphabet (a - b) 0 b
  rw [Nat.sub_add_cancel hab, zero_add, rsXAlphabet_det, one_pow, one_mul, Nat.cast_zero,
    rsGT_oneRow] at h
  exact h

/-- The precise Q normalization of each rank-two mixed-Cauchy factor. -/
theorem rsQ_two (a b : ℕ) (hab : b ≤ a) :
    gtQ rsNome rsPochhammerUnits rsXAlphabet 2 ![(a : ℤ), (b : ℤ)] =
      ((D4K.qpoch (a - b))⁻¹ * (D4K.qpoch b)⁻¹) • rsH (a - b) := by
  rw [gtQ_two_eq, rsGT_two a b hab, rsInvPoch_R, rsInvPoch_R,
    ← map_mul, ← Algebra.smul_def]

/-- Orthogonality of the normalized GT factors, with no coefficient comparison assumed. -/
theorem rsMoment_Q_mul (a b c d : ℕ) (hab : b ≤ a) (hcd : d ≤ c) :
    rsMoment (gtQ rsNome rsPochhammerUnits rsXAlphabet 2 ![(a : ℤ), (b : ℤ)] *
      gtQ rsNome rsPochhammerUnits rsXAlphabet 2 ![(c : ℤ), (d : ℤ)]) =
      if a - b = c - d then
        ((D4K.qpoch (a - b))⁻¹ * (D4K.qpoch b)⁻¹ * (D4K.qpoch d)⁻¹) • (1 : D4K.R)
      else 0 := by
  rw [rsQ_two a b hab, rsQ_two c d hcd, smul_mul_smul, map_smul, rsMoment_orthogonal]
  by_cases he : a - b = c - d
  · rw [if_pos he, if_pos he, ← he, smul_smul]
    apply congrArg (fun t : D4K.Kq => t • (1 : D4K.R))
    have hq := D4K.qpoch_ne_zero (a - b)
    field_simp
  · rw [if_neg he, if_neg he, smul_zero]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.rsMonUnit_zpow
#print axioms VOA.DeligneAudit.D4Char.rsXAlphabet_det
#print axioms VOA.DeligneAudit.D4Char.rsGT_oneRow
#print axioms VOA.DeligneAudit.D4Char.rsGT_two
#print axioms VOA.DeligneAudit.D4Char.rsQ_two
#print axioms VOA.DeligneAudit.D4Char.rsMoment_Q_mul
