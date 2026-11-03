import VOA.DeligneAudit.D4CharGPTwo

/-!
The separating zero in the stable mixed-Cauchy shift. The continuation is arbitrary:
the negative block is retained, and is not replaced by a zero tail.
-/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

/-- B kills a selected separating zero regardless of the continuation to its right. -/
theorem gtMixed_separator (q : R) (b z : ℤ) (A B : R) (f : Bool → R)
    (hB : A * (1 - q ^ b.toNat) + B = 0) :
    A * (∑ t : Bool, gtCauchyTailEdge q b z false t * f t) +
      B * (∑ t : Bool, gtCauchyTailEdge q b z true t * f t) =
      if z = 0 then (A + B) * f false else 0 := by
  simp only [Fintype.sum_bool]
  by_cases hz : z = 0
  · subst z
    simp [gtCauchyTailEdge, gtCauchyBond, pieriBit]
    ring
  · by_cases hz' : z = 1
    · subst z
      simp only [gtCauchyTailEdge, gtCauchyBond, pieriBit, Bool.not_false,
        Bool.not_true, Bool.and_self, Bool.and_false, Bool.false_eq_true,
        ↓reduceIte, sub_add_cancel, one_ne_zero, zero_mul, mul_one, add_zero]
      calc
        _ = -(A * (1 - q ^ b.toNat) + B) * f true := by ring
        _ = 0 := by rw [hB]; ring
    · simp [gtCauchyTailEdge, pieriBit, hz, hz']

/-- X and B at the rank-two head, with a completely unrestricted negative continuation. -/
theorem gtMixed_two_head (q : R) (h : PochhammerUnits q)
    (a b c z : ℤ) (f : Bool → R) :
    (gtCauchyHeadStates q h a b c).1 *
        (∑ t : Bool, gtCauchyTailEdge q b z false t * f t) +
      (gtCauchyHeadStates q h a b c).2 *
        (∑ t : Bool, gtCauchyTailEdge q b z true t * f t) =
      q ^ (a + b - c).toNat * gtQCoeff q h ![a, b] ![c] *
        (if z = 0 then f false else 0) := by
  rw [gtMixed_separator q b z _ _ f]
  · have ht : (gtCauchyHeadStates q h a b c).1 +
        (gtCauchyHeadStates q h a b c).2 =
        q ^ (a + b - c).toNat * gtQCoeff q h ![a, b] ![c] :=
      gtQ_two_state_total q h a b c
    rw [ht]
    split_ifs <;> simp
  · simpa only [gtCauchyHeadStates, mul_comm] using
      gtQ_two_state_boundary q h a b c

/-- Rank-one X and B at the same separator, needed for the first mixed-Cauchy step. -/
theorem gtMixed_one_head (q : R) (h : PochhammerUnits q)
    (a z : ℤ) (f : Bool → R) :
    gtInvPoch q h a * (∑ t : Bool, gtCauchyTailEdge q a z false t * f t) -
      gtInvPoch q h (a - 1) * (∑ t : Bool, gtCauchyTailEdge q a z true t * f t) =
      q ^ a.toNat * gtInvPoch q h a * (if z = 0 then f false else 0) := by
  have hb : gtInvPoch q h a * (1 - q ^ a.toNat) + -gtInvPoch q h (a - 1) = 0 := by
    rw [gtInvPoch_lower]
    ring
  have ht : gtInvPoch q h a + -gtInvPoch q h (a - 1) =
      q ^ a.toNat * gtInvPoch q h a := by
    rw [gtInvPoch_lower]
    ring
  have hs := gtMixed_separator q a z (gtInvPoch q h a) (-gtInvPoch q h (a - 1)) f hb
  rw [ht] at hs
  simpa only [neg_mul, ← sub_eq_add_neg, mul_ite, mul_zero] using hs

/-- The three positive-side bits, in the exact signed edge convention of e-Pieri. -/
theorem gtMixed_two_bits (q : R) (h : PochhammerUnits q)
    (a b c z : ℤ) (f : Bool → R) :
    (∑ s : Bool, ∑ t : Bool, ∑ v : Bool,
      (if s then -1 else 1) * (if t then -1 else 1) *
        gtCauchyBond q a b s t *
        gtQCoeff q h ![a - pieriBit s, b - pieriBit t] ![c] *
        gtCauchyTailEdge q b z t v * f v) =
      q ^ (a + b - c).toNat * gtQCoeff q h ![a, b] ![c] *
        (if z = 0 then f false else 0) := by
  have hs := gtMixed_two_head q h a b c z f
  simp only [Fintype.sum_bool, gtCauchyHeadStates] at hs ⊢
  simp only [gtCauchyBond, pieriBit, Bool.not_true, Bool.not_false,
    Bool.true_and, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    sub_zero, mul_one, one_mul] at hs ⊢
  linear_combination hs

/-- The same calculation with the one-row normalization for the preceding x variable. -/
theorem gtMixed_two_bits_normalized (q : R) (h : PochhammerUnits q)
    (a b z : ℤ) (r : ℕ) (f : Bool → R) :
    (∑ s : Bool, ∑ t : Bool, ∑ v : Bool,
      (if s then -1 else 1) * (if t then -1 else 1) *
        gtCauchyBond q a b s t *
        (gtInvPoch q h r * gtQCoeff q h ![a - pieriBit s, b - pieriBit t] ![r]) *
        gtCauchyTailEdge q b z t v * f v) =
      q ^ (a + b - r).toNat * (gtInvPoch q h r * gtQCoeff q h ![a, b] ![r]) *
        (if z = 0 then f false else 0) := by
  have hs := congrArg (fun x : R => gtInvPoch q h r * x)
    (gtMixed_two_bits q h a b r z f)
  simp only [Finset.mul_sum] at hs
  convert hs using 1
  · apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro v _
    ring
  · ring

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtMixed_separator
#print axioms VOA.DeligneAudit.D4Char.gtMixed_two_head
#print axioms VOA.DeligneAudit.D4Char.gtMixed_one_head
#print axioms VOA.DeligneAudit.D4Char.gtMixed_two_bits
#print axioms VOA.DeligneAudit.D4Char.gtMixed_two_bits_normalized
