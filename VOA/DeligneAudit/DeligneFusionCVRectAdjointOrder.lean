import VOA.DeligneAudit.DeligneFusionCVRectStarIdeal

/-!
# Orders for an adjoint FFLV site and its two leaf branches

The adjoint site's local monomials satisfy `p ≤ 1`, `r ≤ 1`,
and `p+q+r ≤ 2`. Its x-leaf shift has five monomials and its
primitive branch has three. The arithmetic below is the input
to actual coefficient-ideal maps, not an assumed dimension recursion.
-/

namespace VOA.DeligneAudit.A2.CVRectAdjointOrder

open VOA.DeligneAudit.A2.CVRectIntegrationOrder

def adjOrder (p q r : ℕ) : ℕ := max (max (p - 1) (r - 1)) (p + q + r - 2)

def fiveOrder (q r : ℕ) : ℕ := max (r - 1) (q + r - 2)

def threeOrder (p q r : ℕ) : ℕ := p + (q + r - 1)

def adjCapacity (q r : ℕ) : ℕ := if q = 0 ∨ (q = 1 ∧ r = 0) then 1 else 0

def fiveCapacity (q : ℕ) : ℕ := if q ≤ 1 then 1 else 0

def background (left right center : List ℕ) (p q r : ℕ) : ℕ :=
  excess left (p + q) + excess right (q + r) + excess center q

def adjointOrder (left right center : List ℕ) (p q r : ℕ) : ℕ :=
  background left right center p q r + adjOrder p q r

def fiveSiteOrder (left right center : List ℕ) (p q r : ℕ) : ℕ :=
  background left right center p q r + fiveOrder q r

def threeSiteOrder (left right center : List ℕ) (p q r : ℕ) : ℕ :=
  background left right center p q r + threeOrder p q r

theorem adjCapacity_le_one (q r : ℕ) : adjCapacity q r ≤ 1 := by
  unfold adjCapacity
  split_ifs <;> omega

theorem adjOrder_piecewise (p q r : ℕ) :
    adjOrder p q r = fiveOrder q r + (p - adjCapacity q r) := by
  unfold adjOrder fiveOrder adjCapacity
  split_ifs <;> omega

theorem adjOrder_succ_le (p q r : ℕ) :
    adjOrder (p + 1) q r ≤ adjOrder p q r + 1 := by
  unfold adjOrder
  omega

theorem adjOrder_succ_eq (p q r : ℕ) (hpq : 2 ≤ p + q) :
    adjOrder (p + 1) q r = adjOrder p q r + 1 := by
  unfold adjOrder
  omega

theorem adjCapacity_high_load (p q r : ℕ) (hp : adjCapacity q r ≤ p) :
    1 ≤ p + q := by
  unfold adjCapacity at hp
  split_ifs at hp <;> omega

theorem adjOrder_special_succ (p q r : ℕ) (hp : adjCapacity q r ≤ p) :
    adjOrder (p + 1) q r = adjOrder p q r + 1 := by
  rw [adjOrder_piecewise, adjOrder_piecewise]
  omega

theorem adjOrder_special_decrement (p q r : ℕ) :
    threeOrder p q r =
      if p < adjCapacity q r then adjOrder p q r else adjOrder p q r + 1 := by
  unfold threeOrder adjOrder adjCapacity
  split_ifs <;> omega

theorem adjOrder_shift_le (p m q r : ℕ) (_hm : m ≤ p) :
    fiveOrder q r ≤ adjOrder m q r := by
  rw [adjOrder_piecewise]
  omega

/-- The special adjoint-site primitive has the exact low/high order
pattern required by the two finite inductions. -/
theorem adjoint_special_decrement (left right center : List ℕ) (p q r : ℕ) :
    threeSiteOrder left right center p q r =
      if p < adjCapacity q r then adjointOrder left right center p q r
      else adjointOrder left right center p q r + 1 := by
  unfold threeSiteOrder adjointOrder
  rw [adjOrder_special_decrement]
  split_ifs <;> omega

theorem adjoint_special_high (left right center : List ℕ)
    (hleft : ∀ k ∈ left, k ≤ 1) (p q r : ℕ) (hp : adjCapacity q r ≤ p) :
    adjointOrder left right center (p + 1) q r =
      adjointOrder left right center p q r + left.length + 1 := by
  have hload := adjCapacity_high_load p q r hp
  have he := excess_succ_eq left (p + q)
    (fun k hk => (hleft k hk).trans hload)
  have ha := adjOrder_special_succ p q r hp
  unfold adjointOrder background
  rw [show p + 1 + q = p + q + 1 by omega, he, ha]
  omega

/-- Ordinary rectangle sites of capacity at least two can be reduced
before selecting the adjoint site itself. -/
theorem adjoint_ordinary_low (left right center : List ℕ) (K p q r : ℕ)
    (hp : p + 1 + q < K) :
    adjointOrder (K :: left) right center (p + 1) q r ≤
      adjointOrder (K :: left) right center p q r + (left.length + 1) := by
  have he := excess_succ_le left (p + q)
  rw [show p + q + 1 = p + 1 + q by omega] at he
  have ha := adjOrder_succ_le p q r
  simp only [adjointOrder, background, excess, List.map_cons, List.sum_cons] at *
  omega

theorem adjoint_ordinary_high (left right center : List ℕ) (K p q r : ℕ)
    (hK : 2 ≤ K) (hmax : ∀ k ∈ left, k ≤ K) (hp : K ≤ p + q) :
    adjointOrder (K :: left) right center (p + 1) q r =
      adjointOrder (K :: left) right center p q r + (left.length + 1) + 1 := by
  have he := excess_succ_eq left (p + q) (fun k hk => (hmax k hk).trans hp)
  rw [show p + q + 1 = p + 1 + q by omega] at he
  have ha := adjOrder_succ_eq p q r (by omega)
  simp only [adjointOrder, background, excess, List.map_cons, List.sum_cons] at *
  omega

theorem adjoint_ordinary_decrement (left right center : List ℕ) (K p q r : ℕ)
    (hK : 1 ≤ K) :
    adjointOrder ((K - 1) :: left) right center p q r =
      if p + q < K then adjointOrder (K :: left) right center p q r
      else adjointOrder (K :: left) right center p q r + 1 := by
  simp only [adjointOrder, background, excess, List.map_cons, List.sum_cons]
  split_ifs <;> omega

theorem fiveCapacity_le_one (q : ℕ) : fiveCapacity q ≤ 1 := by
  unfold fiveCapacity
  split_ifs <;> omega

theorem fiveOrder_piecewise (q r : ℕ) :
    fiveOrder q r = (q - 2) + (r - fiveCapacity q) := by
  unfold fiveOrder fiveCapacity
  split_ifs <;> omega

theorem fiveOrder_special_decrement (q r : ℕ) :
    r + (q - 1) = if r < fiveCapacity q then fiveOrder q r else fiveOrder q r + 1 := by
  unfold fiveOrder fiveCapacity
  split_ifs <;> omega

theorem fiveOrder_succ_eq (q r : ℕ) (hqr : 2 ≤ q + r) :
    fiveOrder q (r + 1) = fiveOrder q r + 1 := by
  unfold fiveOrder
  omega

end VOA.DeligneAudit.A2.CVRectAdjointOrder

#print axioms VOA.DeligneAudit.A2.CVRectAdjointOrder.adjoint_special_high
#print axioms VOA.DeligneAudit.A2.CVRectAdjointOrder.adjoint_ordinary_high
#print axioms VOA.DeligneAudit.A2.CVRectAdjointOrder.fiveOrder_special_decrement
