import Mathlib.Data.List.Sort
import Mathlib.Tactic

/-! A positive additive weight for the finite D4 monomial-row certificate.
Row validity is a computable finite proposition, independent of ideal membership. -/
namespace VOA.DeligneAudit.D4FusionContact.M2Certificate

def wordWeight (w : List (Fin 18)) : ℕ :=
  (w.map fun v => 5 ^ (17 - v.val)).sum

theorem wordWeight_append (a b : List (Fin 18)) :
    wordWeight (a ++ b) = wordWeight a + wordWeight b := by
  simp [wordWeight, List.map_append, List.sum_append]

theorem wordWeight_perm {a b : List (Fin 18)} (h : a.Perm b) :
    wordWeight a = wordWeight b := (h.map _).sum_eq

theorem wordWeight_sort (w : List (Fin 18)) :
    wordWeight (w.insertionSort (· ≤ ·)) = wordWeight w :=
  wordWeight_perm (List.perm_insertionSort (· ≤ ·) w)

/-- A nonempty row has a nonzero head coefficient, and every tail word
has the same length and strictly smaller additive weight. -/
def ReducingRow : List (List (Fin 18) × ℤ) → Prop
  | [] => False
  | (lead, c) :: tail => c ≠ 0 ∧ tail.Forall (fun t =>
      t.1.length = lead.length ∧ wordWeight t.1 < wordWeight lead)

instance (row : List (List (Fin 18) × ℤ)) : Decidable (ReducingRow row) := by
  cases row with
  | nil => exact isFalse id
  | cons t l =>
    obtain ⟨lead, c⟩ := t
    exact inferInstanceAs (Decidable (c ≠ 0 ∧ l.Forall (fun t =>
      t.1.length = lead.length ∧ wordWeight t.1 < wordWeight lead)))

end VOA.DeligneAudit.D4FusionContact.M2Certificate

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.wordWeight_append
#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.wordWeight_perm
