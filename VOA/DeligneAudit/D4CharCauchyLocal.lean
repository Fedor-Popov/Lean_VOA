import VOA.DeligneAudit.D4CharCauchyTail

/-! The full finite local coefficient comparison for C(2,N), in Boolean subset notation. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

/-- A signed Pieri path, with its incoming bit specified. -/
def gtCauchyPath (q : R) : ℤ → Bool → List (ℤ × Bool) → R
  | _, _, [] => 1
  | a, s, (b, t) :: bs =>
      (if t then -1 else 1) * gtCauchyBond q a b s t * gtCauchyPath q b t bs

/-- The same path restricted to a zero source tail. -/
def gtCauchyZeroPath (q : R) : ℤ → Bool → List (ℤ × Bool) → R
  | _, _, [] => 1
  | a, s, (b, t) :: bs => gtCauchyTailEdge q a b s t * gtCauchyZeroPath q b t bs

theorem gtCauchyZeroPath_eq (q : R) (a : ℤ) (s : Bool) (bs : List (ℤ × Bool)) :
    gtCauchyZeroPath q a s bs = gtCauchyPath q a s bs *
      gtCauchyTailDelta (bs.map fun p => p.1 - pieriBit p.2) := by
  induction bs generalizing a s with
  | nil => simp [gtCauchyZeroPath, gtCauchyPath, gtCauchyTailDelta]
  | cons p bs ih =>
      obtain ⟨b, t⟩ := p
      simp only [gtCauchyZeroPath, gtCauchyPath, List.map_cons, gtCauchyTailDelta_cons]
      rw [ih]
      by_cases hb : b = pieriBit t
      · simp [gtCauchyTailEdge, hb, mul_assoc]
      · simp [gtCauchyTailEdge, hb, sub_eq_zero]

theorem gtCauchyZeroPath_sum (q : R) (a : ℤ) (s : Bool) (N : ℕ)
    (lam : Fin N → ℤ) :
    (∑ t : Fin N → Bool,
      gtCauchyZeroPath q a s (List.ofFn fun i => (lam i, t i))) =
        gtCauchyTail q a s (List.ofFn lam) := by
  induction N generalizing a s with
  | zero => simp [gtCauchyZeroPath, gtCauchyTail]
  | succ N ih =>
      rw [← (Fin.consEquiv fun _ : Fin (N + 1) => Bool).sum_comp]
      simp only [Fintype.sum_prod_type, Fin.consEquiv_apply, List.ofFn_succ,
        Fin.cons_zero, Fin.cons_succ, gtCauchyZeroPath, gtCauchyTail]
      simp_rw [← Finset.mul_sum, ih]

/-- The two-row branching coefficient, extended by zero on all other rows. -/
def gtCauchySeed (q : R) (h : PochhammerUnits q) (c : ℤ) {N : ℕ}
    (lam : Fin (N + 2) → ℤ) : R :=
  gtQCoeff q h ![lam 0, lam 1] ![c] *
    gtCauchyTailDelta (List.ofFn fun i : Fin N => lam i.succ.succ)

/-- Sum the first two bits and the entire tail; X and B finish the calculation. -/
theorem gtCauchyPath_seed_sum (q : R) (h : PochhammerUnits q) (c : ℤ) (N : ℕ)
    (lam : Fin (N + 2) → ℤ) :
    (∑ s : Fin (N + 2) → Bool,
      gtCauchyPath q (lam 0) true (List.ofFn fun i => (lam i, s i)) *
        gtCauchySeed q h c (pieriLower lam s)) =
      q ^ (lam 0 + lam 1 - c).toNat * gtCauchySeed q h c lam := by
  rw [← (Fin.consEquiv fun _ : Fin (N + 2) => Bool).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.consEquiv_apply]
  apply Eq.trans (b := ∑ s : Bool, ∑ t : Bool,
    (if s then -1 else 1) * (if t then -1 else 1) *
      gtCauchyBond q (lam 0) (lam 1) s t *
      gtQCoeff q h ![lam 0 - pieriBit s, lam 1 - pieriBit t] ![c] *
      gtCauchyTail q (lam 1) t (List.ofFn fun i : Fin N => lam i.succ.succ))
  · apply Finset.sum_congr rfl
    intro s _
    rw [← (Fin.consEquiv fun _ : Fin (N + 1) => Bool).sum_comp]
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro t _
    rw [← gtCauchyZeroPath_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [gtCauchyZeroPath_eq]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, gtCauchySeed, pieriLower,
      List.ofFn_succ, gtCauchyPath,
      Fin.cons_zero, Fin.cons_succ, Fin.succ_zero_eq_one, gtCauchyBond,
      Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte, mul_one,
      List.map_ofFn]
    simp only [Fin.cons_one, Fin.cons_zero, Function.comp_def]
    ring
  · simp only [Fintype.sum_bool, gtCauchyBond, pieriBit, Bool.not_true, Bool.not_false,
      Bool.true_and, Bool.false_and, ↓reduceIte]
    have hh := gtCauchyHead_tail q h (lam 0) (lam 1) c
      (List.ofFn fun i : Fin N => lam i.succ.succ)
    dsimp [gtCauchyHeadStates, gtCauchySeed] at hh ⊢
    simp only [sub_zero] at *
    linear_combination hh

/-- The edge product for the signed lowering operator. -/
def gtCauchyBitCoeff (q : R) : (N : ℕ) → (Fin N → ℤ) → (Fin N → Bool) → R
  | 0, _, _ => 1
  | N + 1, lam, s => (-1) ^ pieriStateSize s *
      ∏ i : Fin N, gtCauchyBond q (lam i.castSucc) (lam i.succ)
        (s i.castSucc) (s i.succ)

theorem gtCauchyPath_eq_bitCoeff (q : R) (a : ℤ) (s : Bool) (N : ℕ)
    (lam : Fin (N + 1) → ℤ) (t : Fin (N + 1) → Bool) :
    gtCauchyPath q a s (List.ofFn fun i => (lam i, t i)) =
      gtCauchyBond q a (lam 0) s (t 0) * gtCauchyBitCoeff q (N + 1) lam t := by
  induction N generalizing a s with
  | zero =>
      simp [gtCauchyPath, gtCauchyBitCoeff, pieriStateSize, List.ofFn_succ]
      cases t 0 <;> simp [mul_comm]
  | succ N ih =>
      rw [List.ofFn_succ, gtCauchyPath, ih]
      simp only [gtCauchyBitCoeff, pieriStateSize, Fin.sum_univ_succ,
        Fin.prod_univ_succ, Fin.castSucc_zero, Fin.castSucc_succ, pow_add]
      cases t 0 <;> simp <;> ring

/-- Local transpose-Pieri identity on every integer row, with no dominance assumption. -/
theorem gtCauchySeed_bits (q : R) (h : PochhammerUnits q) (c : ℤ) (N : ℕ)
    (lam : Fin (N + 2) → ℤ) :
    (∑ s : Fin (N + 2) → Bool,
      gtCauchyBitCoeff q (N + 2) lam s * gtCauchySeed q h c (pieriLower lam s)) =
      q ^ ((∑ i, lam i) - c).toNat * gtCauchySeed q h c lam := by
  have hh := gtCauchyPath_seed_sum q h c N lam
  simp only [gtCauchyPath_eq_bitCoeff, gtCauchyBond, Bool.not_true,
    Bool.and_false, Bool.false_eq_true, ↓reduceIte, one_mul] at hh
  rw [hh]
  by_cases ht : ∀ i : Fin N, lam i.succ.succ = 0
  · have hs : (∑ i, lam i) = lam 0 + lam 1 := by
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp [ht]
    rw [hs]
  · have hz : gtCauchySeed q h c lam = 0 := by
      simp [gtCauchySeed, gtCauchyTailDelta, List.mem_ofFn, ht]
    rw [hz, mul_zero, mul_zero]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtCauchyZeroPath_eq
#print axioms VOA.DeligneAudit.D4Char.gtCauchyZeroPath_sum
#print axioms VOA.DeligneAudit.D4Char.gtCauchyPath_seed_sum
#print axioms VOA.DeligneAudit.D4Char.gtCauchyPath_eq_bitCoeff
#print axioms VOA.DeligneAudit.D4Char.gtCauchySeed_bits
