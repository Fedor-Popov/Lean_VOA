import VOA.DeligneAudit.DeligneFusionCVRectAdjointOrder
import VOA.DeligneAudit.DeligneFusionCVRectStarShift

/-!
# Ordinary left-leaf order arithmetic for the five-shape family

The extra five-shape order depends only on the middle and right powers.
It is unchanged through ordinary left-current integration and shift, so
every positive selected capacity follows the actual STAR leaf recursion.
-/

namespace VOA.DeligneAudit.A2.CVRectAdjointFiveLeft

open VOA.DeligneAudit.A2.CVRectIntegrationOrder
open VOA.DeligneAudit.A2.CVRectAdjointOrder

theorem left_low (left right center : List ℕ) (K p q r : ℕ)
    (hp : p + 1 + q < K) :
    fiveSiteOrder (K :: left) right center (p + 1) q r ≤
      fiveSiteOrder (K :: left) right center p q r + left.length := by
  have he := excess_succ_le left (p + q)
  rw [show p + q + 1 = p + 1 + q by omega] at he
  simp only [fiveSiteOrder, background, excess, List.map_cons, List.sum_cons] at *
  omega

theorem left_high (left right center : List ℕ) (K p q r : ℕ)
    (hmax : ∀ k ∈ left, k ≤ K) (hp : K ≤ p + q) :
    fiveSiteOrder (K :: left) right center (p + 1) q r =
      fiveSiteOrder (K :: left) right center p q r + left.length + 1 := by
  have he := excess_succ_eq left (p + q) (fun k hk => (hmax k hk).trans hp)
  rw [show p + q + 1 = p + 1 + q by omega] at he
  simp only [fiveSiteOrder, background, excess, List.map_cons, List.sum_cons] at *
  omega

theorem left_decrement (left right center : List ℕ) (K p q r : ℕ)
    (hK : 1 ≤ K) :
    fiveSiteOrder ((K - 1) :: left) right center p q r =
      if p + q < K then fiveSiteOrder (K :: left) right center p q r
      else fiveSiteOrder (K :: left) right center p q r + 1 := by
  simp only [fiveSiteOrder, background, excess, List.map_cons, List.sum_cons]
  split_ifs <;> omega

theorem left_shift_le (left right center : List ℕ) (K p q r m : ℕ) (hm : m ≤ p) :
    fiveSiteOrder left right (K :: center) p q r ≤
      fiveSiteOrder (K :: left) right center m q r + left.length * (p - m) := by
  have he := CVRectStarShift.leaf_shift_order_le left right center K p q r m hm
  simp only [CVRectStarIdeal.starOrder] at he
  unfold fiveSiteOrder background
  omega

theorem left_zero_order (left right center : List ℕ) :
    fiveSiteOrder (0 :: left) right center =
      fun p q r => fiveSiteOrder left right center p q r + p + q := by
  funext p q r
  simp only [fiveSiteOrder, background, excess, List.map_cons, List.sum_cons,
    Nat.sub_zero]
  omega

theorem left_perm_order {left left' : List ℕ} (hp : left.Perm left')
    (right center : List ℕ) :
    fiveSiteOrder left right center = fiveSiteOrder left' right center := by
  funext p q r
  simp only [fiveSiteOrder, background, excess, (hp.map (fun k => p + q - k)).sum_eq]

end VOA.DeligneAudit.A2.CVRectAdjointFiveLeft

#print axioms VOA.DeligneAudit.A2.CVRectAdjointFiveLeft.left_high
#print axioms VOA.DeligneAudit.A2.CVRectAdjointFiveLeft.left_shift_le
