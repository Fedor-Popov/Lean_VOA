import VOA.DeligneAudit.DeligneFusionCVRectFilteredCurrent
import VOA.DeligneAudit.DeligneFusionCVRectCommutative

/-!
# Exact arithmetic between reversed STAR order and clipped source regions

The current reversal and source region agree including arbitrary capacities.
For an empty current color its exponent must be zero; nonzero powers of an
empty color are dealt with by the actual zero-current lemmas separately.
-/

namespace VOA.DeligneAudit.A2.CVRectFiltered

open VOA.DeligneAudit.A2.CVRectIntegrationOrder
open VOA.DeligneAudit.A2.CVRectCommutative
open VOA.DeligneAudit.A2.CVRectStarIdeal

theorem excess_add_clipped (ξ : List ℕ) (d : ℕ) :
    excess ξ d + clippedSum ξ d = ξ.length * d := by
  induction ξ with
  | nil => simp [excess, clippedSum]
  | cons a ξ ih =>
      have ha : d - a + min d a = d := by omega
      simp only [excess, clippedSum, List.map_cons, List.sum_cons, List.length_cons,
        Nat.add_mul, one_mul] at ih ⊢
      omega

theorem pred_mul_add (N p : ℕ) (hp : N = 0 → p = 0) :
    (N - 1) * p + p = N * p := by
  cases N with
  | zero => simp [hp rfl]
  | succ N => simp [Nat.add_mul]

theorem reverseDegree_add_total (Nx Ny Nz p q r : ℕ)
    (hx : Nx = 0 → p = 0) (hy : Ny = 0 → q = 0) (hz : Nz = 0 → r = 0) :
    reverseDegree Nx Ny Nz p q r + (p + q + r) = Nx * p + Ny * q + Nz * r := by
  have hX := pred_mul_add Nx p hx
  have hY := pred_mul_add Ny q hy
  have hZ := pred_mul_add Nz r hz
  unfold reverseDegree
  omega

/-- The exact relation between STAR excess order and the source clipped
capacity sum, before taking the complementary coefficient index. -/
theorem starOrder_add_clipped (left right center : List ℕ) (p q r : ℕ) :
    starOrder left right center p q r +
        (clippedSum left (p + q) + clippedSum right (q + r) + clippedSum center q) =
      left.length * p + (left.length + right.length + center.length) * q +
        right.length * r := by
  have hL := excess_add_clipped left (p + q)
  have hR := excess_add_clipped right (q + r)
  have hC := excess_add_clipped center q
  unfold starOrder
  calc
    _ = left.length * (p + q) + right.length * (q + r) + center.length * q := by omega
    _ = _ := by ring

/-- Low reversed STAR coefficients correspond to the strict optimized source
region. All zero-padding and exponent conditions are explicit. -/
theorem star_reverse_region (left right center : List ℕ) (p q r j : ℕ)
    (hx : left.length = 0 → p = 0)
    (hy : left.length + right.length + center.length = 0 → q = 0)
    (hz : right.length = 0 → r = 0)
    (hj : j < starOrder left right center p q r)
    (hD : j ≤ reverseDegree left.length (left.length + right.length + center.length)
      right.length p q r) :
    clippedSum left (p + q) + clippedSum right (q + r) + clippedSum center q <
      (reverseDegree left.length (left.length + right.length + center.length)
        right.length p q r - j) + (p + q + r) := by
  have hA := reverseDegree_add_total left.length
    (left.length + right.length + center.length) right.length p q r hx hy hz
  have hB := starOrder_add_clipped left right center p q r
  omega

end VOA.DeligneAudit.A2.CVRectFiltered

#print axioms VOA.DeligneAudit.A2.CVRectFiltered.star_reverse_region
