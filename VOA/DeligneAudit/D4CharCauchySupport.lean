import VOA.DeligneAudit.D4CharCauchySubsets
import VOA.DeligneAudit.D4CharCauchyTwo

/-! Normalization and exact support of the C(2,N) coefficient on integer rows. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

/-- The x^r coefficient after removing its one-row Q normalization. -/
def gtCauchyWeight (q : R) (h : PochhammerUnits q) (r : ℕ) {N : ℕ}
    (lam : Fin (N + 2) → ℤ) : R :=
  gtInvPoch q h (lam 0 - r) * gtInvPoch q h (r - lam 1) * gtInvPoch q h (lam 1) *
    gtCauchyTailDelta (List.ofFn fun i : Fin N => lam i.succ.succ)

theorem gtCauchyWeight_eq (q : R) (h : PochhammerUnits q) (r : ℕ) {N : ℕ}
    (lam : Fin (N + 2) → ℤ) :
    gtCauchyWeight q h r lam = gtInvPoch q h r * gtCauchySeed q h r lam := by
  simp only [gtCauchyWeight, gtCauchySeed, gtQCoeff_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Int.toNat_natCast]
  have hh := gtPoch_mul_invPoch q h r
  linear_combination
    -(gtInvPoch q h (lam 0 - r) * gtInvPoch q h (r - lam 1) *
      gtInvPoch q h (lam 1) *
      gtCauchyTailDelta (List.ofFn fun i : Fin N => lam i.succ.succ)) * hh

/-- The local identity with exactly the normalization of gtCauchyTwoCoeff. -/
theorem gtCauchyWeight_subsets (q : R) (h : PochhammerUnits q) (r N : ℕ)
    (lam : Fin (N + 2) → ℤ) :
    (∑ S : Finset (Fin (N + 2)), (-1) ^ S.card *
      gtCauchyWeight q h r (gtLowerSubset lam S) *
        pieriCoeff q (gtLowerSubset lam S) S) =
      q ^ ((∑ i, lam i) - r).toNat * gtCauchyWeight q h r lam := by
  simp only [gtCauchyWeight_eq]
  have hh := congrArg (fun x => gtInvPoch q h r * x) (gtCauchySeed_subsets q h r N lam)
  simp only [Finset.mul_sum] at hh
  convert hh using 1
  · apply Finset.sum_congr rfl
    intro S _
    ring
  · ring

/-- Nonzero coefficients force the complete interlacing and trailing-zero conditions. -/
theorem gtCauchyWeight_support (q : R) (h : PochhammerUnits q) (r : ℕ) {N : ℕ}
    (lam : Fin (N + 2) → ℤ) (hn : gtCauchyWeight q h r lam ≠ 0) :
    0 ≤ lam 1 ∧ lam 1 ≤ r ∧ (r : ℤ) ≤ lam 0 ∧
      ∀ i : Fin N, lam i.succ.succ = 0 := by
  have hb : 0 ≤ lam 1 := by
    by_contra hb
    have hz := gtInvPoch_of_neg q h (show lam 1 < 0 by omega)
    exact hn (by simp [gtCauchyWeight, hz])
  have hbr : lam 1 ≤ r := by
    by_contra hbr
    have hz := gtInvPoch_of_neg q h (show (r : ℤ) - lam 1 < 0 by omega)
    exact hn (by simp [gtCauchyWeight, hz])
  have hra : (r : ℤ) ≤ lam 0 := by
    by_contra hra
    have hz := gtInvPoch_of_neg q h (show lam 0 - r < 0 by omega)
    exact hn (by simp [gtCauchyWeight, hz])
  refine ⟨hb, hbr, hra, ?_⟩
  by_contra ht
  exact hn (by simp [gtCauchyWeight, gtCauchyTailDelta, List.mem_ofFn, ht])

theorem gtCauchyWeight_sum (q : R) (h : PochhammerUnits q) (r : ℕ) {N : ℕ}
    (lam : Fin (N + 2) → ℤ) (hn : gtCauchyWeight q h r lam ≠ 0) :
    (∑ i, lam i) = lam 0 + lam 1 := by
  obtain ⟨_, _, _, ht⟩ := gtCauchyWeight_support q h r lam hn
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [ht]

theorem gtCauchyWeight_degree (q : R) (h : PochhammerUnits q) (r : ℕ) {N : ℕ}
    (lam : Fin (N + 2) → ℤ) (hn : gtCauchyWeight q h r lam ≠ 0) :
    (r : ℤ) ≤ ∑ i, lam i := by
  rw [gtCauchyWeight_sum q h r lam hn]
  obtain ⟨hb, _, ha, _⟩ := gtCauchyWeight_support q h r lam hn
  omega

theorem gtCauchyWeight_dominant (q : R) (h : PochhammerUnits q) (r : ℕ) {N : ℕ}
    (lam : Fin (N + 2) → ℤ) (hn : gtCauchyWeight q h r lam ≠ 0) : Antitone lam := by
  obtain ⟨hb, hbr, hra, ht⟩ := gtCauchyWeight_support q h r lam hn
  have hpos : ∀ i, 0 ≤ lam i := by
    intro i
    refine Fin.cases (by omega) (fun j => ?_) i
    refine Fin.cases (by simpa using hb) (fun k => ?_) j
    simp [ht]
  apply Fin.antitone_iff_succ_le.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hra.trans' hbr
  · rw [ht]
    exact hpos _

theorem gtCauchyWeight_bounds (q : R) (h : PochhammerUnits q) (r : ℕ) {N : ℕ}
    (lam : Fin (N + 2) → ℤ) (hn : gtCauchyWeight q h r lam ≠ 0)
    (i : Fin (N + 2)) : 0 ≤ lam i ∧ lam i ≤ ∑ j, lam j := by
  obtain ⟨hb, hbr, hra, ht⟩ := gtCauchyWeight_support q h r lam hn
  rw [gtCauchyWeight_sum q h r lam hn]
  refine Fin.cases ?_ (fun j => ?_) i
  · change 0 ≤ lam 0 ∧ lam 0 ≤ lam 0 + lam 1
    constructor <;> omega
  · refine Fin.cases ?_ (fun k => ?_) j
    · change 0 ≤ lam 1 ∧ lam 1 ≤ lam 0 + lam 1
      constructor <;> omega
    · rw [ht]
      constructor <;> omega

theorem gtTwoRow_sum (N a b : ℕ) : (∑ i, gtTwoRow N a b i) = (a : ℤ) + b := by
  simp [gtTwoRow, Fin.sum_univ_succ]

theorem gtCauchyWeight_twoRow (q : R) (h : PochhammerUnits q) (N r s b : ℕ)
    (hb : b ≤ min r s) :
    gtCauchyWeight q h r (gtTwoRow N (r + s - b) b) =
      gtInvPoch q h (r - b : ℕ) * gtInvPoch q h (s - b : ℕ) * gtInvPoch q h b := by
  have hr : b ≤ r := hb.trans (min_le_left _ _)
  have hs : b ≤ s := hb.trans (min_le_right _ _)
  have he : ((r + s - b : ℕ) : ℤ) - r = ((s - b : ℕ) : ℤ) := by omega
  simp only [gtCauchyWeight, gtTwoRow, Fin.cons_zero, Fin.cons_one, Fin.cons_succ]
  rw [he, ← Int.natCast_sub hr]
  simp [gtCauchyTailDelta, mul_comm]

/-- At a fixed degree the second part is the only free row index. -/
theorem gtCauchyWeight_shape (q : R) (h : PochhammerUnits q) (r s : ℕ) {N : ℕ}
    (lam : Fin (N + 2) → ℤ) (hn : gtCauchyWeight q h r lam ≠ 0)
    (hd : (∑ i, lam i) = (r + s : ℕ)) :
    (lam 1).toNat ≤ min r s ∧ lam = gtTwoRow N (r + s - (lam 1).toNat) (lam 1).toNat := by
  obtain ⟨hb, hbr, hra, ht⟩ := gtCauchyWeight_support q h r lam hn
  rw [gtCauchyWeight_sum q h r lam hn] at hd
  refine ⟨by omega, ?_⟩
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [gtTwoRow, Fin.cons_zero]
    omega
  · refine Fin.cases ?_ (fun k => ?_) j
    · simp only [gtTwoRow, Fin.cons_succ, Fin.cons_zero]
      change lam 1 = _
      omega
    · simp [gtTwoRow, ht]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtCauchyWeight_eq
#print axioms VOA.DeligneAudit.D4Char.gtCauchyWeight_subsets
#print axioms VOA.DeligneAudit.D4Char.gtCauchyWeight_support
#print axioms VOA.DeligneAudit.D4Char.gtCauchyWeight_degree
#print axioms VOA.DeligneAudit.D4Char.gtCauchyWeight_dominant
#print axioms VOA.DeligneAudit.D4Char.gtCauchyWeight_bounds
#print axioms VOA.DeligneAudit.D4Char.gtTwoRow_sum
#print axioms VOA.DeligneAudit.D4Char.gtCauchyWeight_twoRow
#print axioms VOA.DeligneAudit.D4Char.gtCauchyWeight_shape
