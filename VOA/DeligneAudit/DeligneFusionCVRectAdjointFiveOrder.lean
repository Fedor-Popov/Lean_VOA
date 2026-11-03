import VOA.DeligneAudit.DeligneFusionCVRectAdjointShift

/-! # Concrete orders for the five-monomial y/z branch -/

namespace VOA.DeligneAudit.A2.CVRectAdjointFiveOrder

open VOA.DeligneAudit.A2.CVRectIntegrationOrder
open VOA.DeligneAudit.A2.CVRectAdjointOrder

def tailBackground (active center : List ℕ) (p q : ℕ) : ℕ :=
  excess active (p + q) + excess center q

def fiveTailOrder (active center : List ℕ) (p q _r : ℕ) : ℕ :=
  tailBackground active center p q + fiveOrder q p

def threeTailOrder (active center : List ℕ) (p q _r : ℕ) : ℕ :=
  tailBackground active center p q + p + (q - 1)

def twoTailOrder (active center : List ℕ) (p q _r : ℕ) : ℕ :=
  tailBackground active center p q + (q - 2)

theorem fiveCapacity_high_load (p q : ℕ) (hp : fiveCapacity q ≤ p) : 1 ≤ p + q := by
  unfold fiveCapacity at hp
  split_ifs at hp <;> omega

theorem five_special_decrement (active center : List ℕ) (p q r : ℕ) :
    threeTailOrder active center p q r =
      if p < fiveCapacity q then fiveTailOrder active center p q r
      else fiveTailOrder active center p q r + 1 := by
  have hh := fiveOrder_special_decrement q p
  unfold threeTailOrder fiveTailOrder
  split_ifs at hh ⊢ <;> omega

theorem five_special_high (active center : List ℕ)
    (hactive : ∀ k ∈ active, k ≤ 1) (p q r : ℕ) (hp : fiveCapacity q ≤ p) :
    fiveTailOrder active center (p + 1) q r =
      fiveTailOrder active center p q r + active.length + 1 := by
  have hload := fiveCapacity_high_load p q hp
  have he := excess_succ_eq active (p + q)
    (fun k hk => (hactive k hk).trans hload)
  have hf : fiveOrder q (p + 1) = fiveOrder q p + 1 := by
    rw [fiveOrder_piecewise, fiveOrder_piecewise]
    omega
  unfold fiveTailOrder tailBackground
  rw [show p + 1 + q = p + q + 1 by omega, he, hf]
  omega

theorem five_tail_succ_le (p q : ℕ) : fiveOrder q (p + 1) ≤ fiveOrder q p + 1 := by
  unfold fiveOrder
  omega

theorem five_ordinary_low (active center : List ℕ) (K p q r : ℕ)
    (hp : p + 1 + q < K) :
    fiveTailOrder (K :: active) center (p + 1) q r ≤
      fiveTailOrder (K :: active) center p q r + (active.length + 1) := by
  have he := excess_succ_le active (p + q)
  rw [show p + q + 1 = p + 1 + q by omega] at he
  have ha := five_tail_succ_le p q
  simp only [fiveTailOrder, tailBackground, excess, List.map_cons, List.sum_cons] at *
  omega

theorem five_ordinary_high (active center : List ℕ) (K p q r : ℕ)
    (hK : 2 ≤ K) (hmax : ∀ k ∈ active, k ≤ K) (hp : K ≤ p + q) :
    fiveTailOrder (K :: active) center (p + 1) q r =
      fiveTailOrder (K :: active) center p q r + (active.length + 1) + 1 := by
  have he := excess_succ_eq active (p + q) (fun k hk => (hmax k hk).trans hp)
  rw [show p + q + 1 = p + 1 + q by omega] at he
  have ha := fiveOrder_succ_eq q p (by omega)
  simp only [fiveTailOrder, tailBackground, excess, List.map_cons, List.sum_cons] at *
  omega

theorem five_ordinary_decrement (active center : List ℕ) (K p q r : ℕ) (hK : 1 ≤ K) :
    fiveTailOrder ((K - 1) :: active) center p q r =
      if p + q < K then fiveTailOrder (K :: active) center p q r
      else fiveTailOrder (K :: active) center p q r + 1 := by
  simp only [fiveTailOrder, tailBackground, excess, List.map_cons, List.sum_cons]
  split_ifs <;> omega

theorem five_special_shift_le (active center : List ℕ) (p q r m : ℕ) (hm : m ≤ p) :
    twoTailOrder active center p q r ≤
      fiveTailOrder active center m q r + active.length * (p - m) := by
  have he := CVRectShift.excess_le_sub_add active (p + q) (p - m)
  rw [show p + q - (p - m) = m + q by omega] at he
  have ha : q - 2 ≤ fiveOrder q m := by unfold fiveOrder; omega
  unfold twoTailOrder fiveTailOrder tailBackground
  omega

theorem five_ordinary_shift_le (active center : List ℕ) (K p q r m : ℕ) (hm : m ≤ p) :
    fiveTailOrder active (K :: center) p q r ≤
      fiveTailOrder (K :: active) center m q r + (active.length + 1) * (p - m) := by
  have he := CVRectStarShift.leaf_shift_order_le active [] center K p q 0 m hm
  have ha : fiveOrder q p ≤ fiveOrder q m + (p - m) := by unfold fiveOrder; omega
  simp only [CVRectStarIdeal.starOrder, excess, List.map_nil, List.sum_nil,
    Nat.add_zero] at he
  simp only [fiveTailOrder, tailBackground, excess, Nat.add_mul, Nat.one_mul]
  omega

end VOA.DeligneAudit.A2.CVRectAdjointFiveOrder

#print axioms VOA.DeligneAudit.A2.CVRectAdjointFiveOrder.five_special_high
#print axioms VOA.DeligneAudit.A2.CVRectAdjointFiveOrder.five_ordinary_high
