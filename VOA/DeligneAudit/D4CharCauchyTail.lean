import VOA.DeligneAudit.D4CharQXB

/-!
The trailing-zero block in the coefficient comparison for C(2,N).
The row entries are arbitrary integers. The two-state boundary identity kills every
nonzero output tail, including all initial columns of ones of arbitrary length.
-/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

/-- The entering-edge factor when the indicated boxes have been removed. -/
def gtCauchyBond (q : R) (a b : ℤ) (s t : Bool) : R :=
  if t && !s then 1 - q ^ (a - b + 1).toNat else 1

/-- One tail position: its source entry must be zero. -/
def gtCauchyTailEdge (q : R) (a b : ℤ) (s t : Bool) : R :=
  if b = pieriBit t then (if t then -1 else 1) * gtCauchyBond q a b s t else 0

/-- Sum over the removed boxes in a trailing block, with its incoming state fixed. -/
def gtCauchyTail (q : R) : ℤ → Bool → List ℤ → R
  | _, _, [] => 1
  | a, s, b :: bs => ∑ t : Bool, gtCauchyTailEdge q a b s t * gtCauchyTail q b t bs

/-- The delta function on the all-zero tail. -/
def gtCauchyTailDelta (bs : List ℤ) : R := if ∀ b ∈ bs, b = 0 then 1 else 0

theorem gtCauchyTailDelta_nil : gtCauchyTailDelta ([] : List ℤ) = (1 : R) := by
  simp [gtCauchyTailDelta]

theorem gtCauchyTailDelta_cons (b : ℤ) (bs : List ℤ) :
    gtCauchyTailDelta (b :: bs) = if b = 0 then (gtCauchyTailDelta bs : R) else 0 := by
  by_cases hb : b = 0 <;> simp [gtCauchyTailDelta, hb]

/-- After an unselected zero, no later selected box can contribute. -/
theorem gtCauchyTail_zero_state (q : R) (bs : List ℤ) :
    gtCauchyTail q 0 false bs = gtCauchyTailDelta bs := by
  induction bs with
  | nil => simp [gtCauchyTail, gtCauchyTailDelta]
  | cons b bs ih =>
      rw [gtCauchyTail, Fintype.sum_bool, gtCauchyTailDelta_cons]
      by_cases hb : b = 0
      · subst b
        simpa [gtCauchyTailEdge, gtCauchyBond, pieriBit] using ih
      · by_cases hb' : b = 1
        · subst b
          simp [gtCauchyTailEdge, gtCauchyBond, pieriBit]
        · simp [gtCauchyTailEdge, pieriBit, hb, hb']

/-- B cancels the first selected tail box; all remaining nonzero tails then vanish. -/
theorem gtCauchyTail_boundary (q : R) (b : ℤ) (A B : R)
    (hB : A * (1 - q ^ b.toNat) + B = 0) (bs : List ℤ) :
    A * gtCauchyTail q b false bs + B * gtCauchyTail q b true bs =
      (A + B) * gtCauchyTailDelta bs := by
  cases bs with
  | nil => simp [gtCauchyTail, gtCauchyTailDelta]
  | cons c cs =>
      simp only [gtCauchyTail, Fintype.sum_bool, gtCauchyTailDelta_cons]
      by_cases hc : c = 0
      · subst c
        simp [gtCauchyTailEdge, gtCauchyBond, pieriBit, gtCauchyTail_zero_state]
        ring
      · by_cases hc' : c = 1
        · subst c
          simp only [gtCauchyTailEdge, pieriBit, gtCauchyBond, Bool.not_false,
            Bool.not_true, Bool.and_self, Bool.and_false, Bool.false_eq_true,
            ↓reduceIte, sub_add_cancel, one_ne_zero, zero_mul, mul_one,
            add_zero, mul_zero]
          calc
            _ = -(A * (1 - q ^ b.toNat) + B) * gtCauchyTail q 1 true cs := by ring
            _ = 0 := by rw [hB]; ring
        · simp [gtCauchyTailEdge, pieriBit, hc, hc']

/-- The rank-two initial states, before processing the zero block. -/
def gtCauchyHeadStates (q : R) (h : PochhammerUnits q) (a b c : ℤ) : R × R :=
  (gtQCoeff q h ![a, b] ![c] - gtQCoeff q h ![a - 1, b] ![c],
    gtQCoeff q h ![a - 1, b - 1] ![c] -
      (1 - q ^ (a - b + 1).toNat) * gtQCoeff q h ![a, b - 1] ![c])

/-- The complete local X/B calculation, with any number of trailing positions. -/
theorem gtCauchyHead_tail (q : R) (h : PochhammerUnits q) (a b c : ℤ)
    (bs : List ℤ) :
    (gtCauchyHeadStates q h a b c).1 * gtCauchyTail q b false bs +
        (gtCauchyHeadStates q h a b c).2 * gtCauchyTail q b true bs =
      q ^ (a + b - c).toNat * gtQCoeff q h ![a, b] ![c] * gtCauchyTailDelta bs := by
  rw [gtCauchyTail_boundary]
  · rw [show (gtCauchyHeadStates q h a b c).1 +
        (gtCauchyHeadStates q h a b c).2 =
        q ^ (a + b - c).toNat * gtQCoeff q h ![a, b] ![c] from
      gtQ_two_state_total q h a b c]
  · simpa only [gtCauchyHeadStates, mul_comm] using
      gtQ_two_state_boundary q h a b c

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtCauchyTail_zero_state
#print axioms VOA.DeligneAudit.D4Char.gtCauchyTail_boundary
#print axioms VOA.DeligneAudit.D4Char.gtCauchyHead_tail
