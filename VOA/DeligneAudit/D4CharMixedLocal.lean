import VOA.DeligneAudit.D4CharMixedSeparator

/-!
Stable mixed-Cauchy coefficient comparison with an arbitrary negative-block function.
Every integer output row and every Pieri subset is included. In particular, the theorem
annihilates all nonzero output entries at the separating middle position.
-/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

/-- A two-row head, one separating zero, and an arbitrary function on the remaining row. -/
def gtMixedSeed (q : R) (h : PochhammerUnits q) (c : ℤ) {N : ℕ}
    (f : (Fin N → ℤ) → R) (lam : Fin (N + 3) → ℤ) : R :=
  gtQCoeff q h ![lam 0, lam 1] ![c] *
    if lam 2 = 0 then f (fun i => lam i.succ.succ.succ) else 0

/-- Signed raising on the negative block, with the incoming zero fixed and unselected. -/
def gtMixedTailAction (q : R) {N : ℕ} (f : (Fin N → ℤ) → R)
    (lam : Fin N → ℤ) : R :=
  ∑ s : Fin N → Bool,
    gtCauchyPath q 0 false (List.ofFn fun i => (lam i, s i)) * f (pieriLower lam s)

/-- The middle zero separates the two head states from any negative-block continuation. -/
theorem gtMixedSeed_path (q : R) (h : PochhammerUnits q) (c : ℤ) (N : ℕ)
    (f : (Fin N → ℤ) → R) (lam : Fin (N + 3) → ℤ) :
    (∑ s : Fin (N + 3) → Bool,
      gtCauchyPath q (lam 0) true (List.ofFn fun i => (lam i, s i)) *
        gtMixedSeed q h c f (pieriLower lam s)) =
      q ^ (lam 0 + lam 1 - c).toNat * gtQCoeff q h ![lam 0, lam 1] ![c] *
        (if lam 2 = 0 then
          gtMixedTailAction q f (fun i => lam i.succ.succ.succ) else 0) := by
  rw [← (Fin.consEquiv fun _ : Fin (N + 3) => Bool).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.consEquiv_apply]
  apply Eq.trans (b := ∑ s : Bool, ∑ t : Bool, ∑ v : Bool,
    (if s then -1 else 1) * (if t then -1 else 1) *
      gtCauchyBond q (lam 0) (lam 1) s t *
      gtQCoeff q h ![lam 0 - pieriBit s, lam 1 - pieriBit t] ![c] *
      gtCauchyTailEdge q (lam 1) (lam 2) t v *
      (∑ w : Fin N → Bool,
        gtCauchyPath q (lam 2) v
            (List.ofFn fun i : Fin N => (lam i.succ.succ.succ, w i)) *
          f (pieriLower (fun i => lam i.succ.succ.succ) w)))
  · apply Finset.sum_congr rfl
    intro s _
    rw [← (Fin.consEquiv fun _ : Fin (N + 2) => Bool).sum_comp]
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro t _
    rw [← (Fin.consEquiv fun _ : Fin (N + 1) => Bool).sum_comp]
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, List.ofFn_succ,
      gtCauchyPath, gtMixedSeed, pieriLower,
      Fin.cons_zero, Fin.cons_succ, Fin.succ_zero_eq_one]
    change (if s then -1 else 1) * gtCauchyBond q (lam 0) (lam 0) true s *
        ((if t then -1 else 1) * gtCauchyBond q (lam 0) (lam 1) s t *
          ((if v then -1 else 1) * gtCauchyBond q (lam 1) (lam 2) t v *
            gtCauchyPath q (lam 2) v
              (List.ofFn fun i : Fin N => (lam i.succ.succ.succ, w i)))) *
        (gtQCoeff q h ![lam 0 - pieriBit s, lam 1 - pieriBit t] ![c] *
          if lam 2 - pieriBit v = 0 then
            f (pieriLower (fun i => lam i.succ.succ.succ) w) else 0) = _
    by_cases hz : lam 2 = pieriBit v
    · simp only [gtCauchyTailEdge, sub_eq_zero, hz, ↓reduceIte,
        gtCauchyBond, Bool.not_true, Bool.and_false, Bool.false_eq_true]
      ring
    · simp only [gtCauchyTailEdge, sub_eq_zero, hz, ↓reduceIte, mul_zero, zero_mul]
  · rw [gtMixed_two_bits]
    by_cases hz : lam 2 = 0
    · simp only [hz, ↓reduceIte, gtMixedTailAction]
    · simp [hz]

/-- The complete mixed local identity in Boolean notation. -/
theorem gtMixedSeed_bits (q : R) (h : PochhammerUnits q) (c : ℤ) (N : ℕ)
    (f : (Fin N → ℤ) → R) (lam : Fin (N + 3) → ℤ) :
    (∑ s : Fin (N + 3) → Bool,
      gtCauchyBitCoeff q (N + 3) lam s * gtMixedSeed q h c f (pieriLower lam s)) =
      q ^ (lam 0 + lam 1 - c).toNat * gtQCoeff q h ![lam 0, lam 1] ![c] *
        (if lam 2 = 0 then
          gtMixedTailAction q f (fun i => lam i.succ.succ.succ) else 0) := by
  have hs := gtMixedSeed_path q h c N f lam
  simpa only [gtCauchyPath_eq_bitCoeff, gtCauchyBond, Bool.not_true,
    Bool.and_false, Bool.false_eq_true, ↓reduceIte, one_mul] using hs

/-- The exact finite-subset form consumed by e-Pieri at rank five (take N = 2). -/
theorem gtMixedSeed_subsets (q : R) (h : PochhammerUnits q) (c : ℤ) (N : ℕ)
    (f : (Fin N → ℤ) → R) (lam : Fin (N + 3) → ℤ) :
    (∑ S : Finset (Fin (N + 3)), (-1) ^ S.card *
      gtMixedSeed q h c f (gtLowerSubset lam S) *
        pieriCoeff q (gtLowerSubset lam S) S) =
      q ^ (lam 0 + lam 1 - c).toNat * gtQCoeff q h ![lam 0, lam 1] ![c] *
        (if lam 2 = 0 then
          gtMixedTailAction q f (fun i => lam i.succ.succ.succ) else 0) := by
  have hs := gtMixedSeed_bits q h c N f lam
  rw [← (pieriIndicatorEquiv (N + 3)).sum_comp] at hs
  change (∑ S : Finset (Fin (N + 3)),
    gtCauchyBitCoeff q (N + 3) lam (pieriIndicator S) *
      gtMixedSeed q h c f (pieriLower lam (pieriIndicator S))) = _ at hs
  simp only [gtCauchyBitCoeff_indicator, pieriLower_indicator] at hs
  rw [← hs]
  apply Finset.sum_congr rfl
  intro S _
  ring

/-- Every bad middle row vanishes, with no restriction on either of the adjacent blocks. -/
theorem gtMixedSeed_bad_middle (q : R) (h : PochhammerUnits q) (c : ℤ) (N : ℕ)
    (f : (Fin N → ℤ) → R) (lam : Fin (N + 3) → ℤ) (hz : lam 2 ≠ 0) :
    (∑ S : Finset (Fin (N + 3)), (-1) ^ S.card *
      gtMixedSeed q h c f (gtLowerSubset lam S) *
        pieriCoeff q (gtLowerSubset lam S) S) = 0 := by
  rw [gtMixedSeed_subsets]
  simp [hz]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtMixedSeed_path
#print axioms VOA.DeligneAudit.D4Char.gtMixedSeed_bits
#print axioms VOA.DeligneAudit.D4Char.gtMixedSeed_subsets
#print axioms VOA.DeligneAudit.D4Char.gtMixedSeed_bad_middle
