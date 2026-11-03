import Mathlib

/-!
# Counting and termination for the two-color rectangular recursion

These are the arithmetic identities for the actual shift/integration
recursion. They do not assume or assert a module dimension recurrence.
The finite polynomial quotient maps must supply that recurrence.
-/

namespace VOA.DeligneAudit.A2.CVRectCount

/-- A two-color site of capacity `k` has this triangular count. -/
def rectangleWeight (k : ℕ) : ℕ := (k + 2).choose 2

/-- The product expected from two-color and one-color site capacities. -/
def familyWeight (two one : List ℕ) : ℕ :=
  (two.map rectangleWeight).prod * (one.map (fun k => k + 1)).prod

theorem rectangleWeight_zero : rectangleWeight 0 = 1 := by decide
theorem rectangleWeight_one : rectangleWeight 1 = 3 := by decide
theorem rectangleWeight_two : rectangleWeight 2 = 6 := by decide
theorem rectangleWeight_three : rectangleWeight 3 = 10 := by decide

theorem rectangleWeight_succ (k : ℕ) :
    rectangleWeight (k + 1) = (k + 2) + rectangleWeight k := by
  simpa only [rectangleWeight, Nat.choose_one_right, Nat.add_assoc] using
    Nat.choose_succ_succ (k + 2) 1

theorem rectangleWeight_pos (K : ℕ) (hK : 1 ≤ K) :
    rectangleWeight K = (K + 1) + rectangleWeight (K - 1) := by
  cases K with
  | zero => omega
  | succ k => simpa only [Nat.add_sub_cancel] using rectangleWeight_succ k

/-- Pascal's identity gives the two actual pieces of a two-color site. -/
theorem familyWeight_active (two one : List ℕ) (K : ℕ) (hK : 1 ≤ K) :
    familyWeight (K :: two) one =
      familyWeight two (K :: one) + familyWeight ((K - 1) :: two) one := by
  simp only [familyWeight, List.map_cons, List.prod_cons, rectangleWeight_pos K hK]
  ring

/-- The last remaining color has the one-color capacity recursion. -/
theorem familyWeight_inactive (two one : List ℕ) (K : ℕ) (hK : 1 ≤ K) :
    familyWeight two (K :: one) =
      familyWeight two one + familyWeight two ((K - 1) :: one) := by
  have hK' : K - 1 + 1 = K := by omega
  simp only [familyWeight, List.map_cons, List.prod_cons, hK']
  ring

theorem familyWeight_active_zero (two one : List ℕ) :
    familyWeight (0 :: two) one = familyWeight two one := by
  simp only [familyWeight, List.map_cons, List.prod_cons, rectangleWeight_zero, one_mul]

theorem familyWeight_inactive_zero (two one : List ℕ) :
    familyWeight two (0 :: one) = familyWeight two one := by
  simp only [familyWeight, List.map_cons, List.prod_cons, Nat.zero_add, one_mul]

/-- Capacities plus the number of active colors strictly decreases in
each branch, including the shift branch whose capacities do not change. -/
def complexity (two one : List ℕ) : ℕ :=
  two.sum + one.sum + 2 * two.length + one.length

theorem complexity_shift (two one : List ℕ) (K : ℕ) :
    complexity two (K :: one) < complexity (K :: two) one := by
  simp only [complexity, List.sum_cons, List.length_cons]
  omega

theorem complexity_active_decrement (two one : List ℕ) (K : ℕ) (hK : 1 ≤ K) :
    complexity ((K - 1) :: two) one < complexity (K :: two) one := by
  simp only [complexity, List.sum_cons, List.length_cons]
  omega

theorem complexity_inactive_remove (two one : List ℕ) (K : ℕ) :
    complexity two one < complexity two (K :: one) := by
  simp only [complexity, List.sum_cons, List.length_cons]
  omega

theorem complexity_inactive_decrement (two one : List ℕ) (K : ℕ) (hK : 1 ≤ K) :
    complexity two ((K - 1) :: one) < complexity two (K :: one) := by
  simp only [complexity, List.sum_cons, List.length_cons]
  omega

theorem complexity_active_zero_remove (two one : List ℕ) :
    complexity two one < complexity (0 :: two) one := by
  simp only [complexity, List.sum_cons, List.length_cons]
  omega

/-- The initial one-orientation three-level count is exactly `3^e 6^n 10^r`. -/
theorem familyWeight_parts (r n e : ℕ) :
    familyWeight (List.replicate r 3 ++ List.replicate n 2 ++ List.replicate e 1) [] =
      3 ^ e * 6 ^ n * 10 ^ r := by
  simp only [familyWeight, List.map_append, List.prod_append, List.map_replicate,
    List.prod_replicate, rectangleWeight_three, rectangleWeight_two, rectangleWeight_one,
    List.map_nil, List.prod_nil, mul_one]
  ring

end VOA.DeligneAudit.A2.CVRectCount

#print axioms VOA.DeligneAudit.A2.CVRectCount.familyWeight_active
#print axioms VOA.DeligneAudit.A2.CVRectCount.familyWeight_inactive
#print axioms VOA.DeligneAudit.A2.CVRectCount.familyWeight_parts
