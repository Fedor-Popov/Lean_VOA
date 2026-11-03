import VOA.DeligneAudit.DeligneCharacterDemazure

/-! Complete one-site D4 character, including its support. The certificate
is checked by the kernel and is independent of representation theory. -/
namespace VOA.DeligneAudit.D4Small
open VOA.DeligneAudit.DeligneCharacter

def charOne : LPoly := [
  (([0, 0, 0, 0], 0), 1),
  (([-1, -1, 0, 0], -1), 1),
  (([-1, 0, 0, 0], -1), 1),
  (([-1, -1, -1, 0], -1), 1),
  (([0, 0, 0, 0], -1), 4),
  (([0, -1, 0, -1], -1), 1),
  (([0, 0, 0, -1], -1), 1),
  (([0, -1, -1, -1], -1), 1),
  (([-1, -2, -1, -1], -1), 1),
  (([-1, -1, -1, -1], -1), 1),
  (([-1, -1, 0, -1], -1), 1),
  (([0, -1, -1, 0], -1), 1),
  (([0, 0, -1, 0], -1), 1),
  (([1, 1, 1, 1], -1), 1),
  (([1, 2, 1, 1], -1), 1),
  (([1, 1, 0, 1], -1), 1),
  (([0, 0, 0, 1], -1), 1),
  (([0, 1, 0, 1], -1), 1),
  (([0, 1, 1, 1], -1), 1),
  (([1, 0, 0, 0], -1), 1),
  (([1, 1, 0, 0], -1), 1),
  (([0, -1, 0, 0], -1), 1),
  (([0, 1, 0, 0], -1), 1),
  (([1, 1, 1, 0], -1), 1),
  (([0, 0, 1, 0], -1), 1),
  (([0, 1, 1, 0], -1), 1)]

set_option maxHeartbeats 2000000 in
-- The complete nine-operator character is checked by this finite kernel certificate.
theorem charOne_eq :
    demazureChar [[2, -1, 0, 0], [-1, 2, -1, -1], [0, -1, 2, 0], [0, -1, 0, 2]]
      [1, 2, 1, 1] [1, 0, 2, 1, 3, 1, 2, 0, 1] 1 = charOne := by
  decide +kernel

/-- The full regraded integer character is 28 + q. -/
theorem charOne_coeff (N : ℕ) :
    (((charOne.filter fun (t : Term) => decide (t.1.2 + 1 = (N : ℤ))).map
      fun t => t.2).sum) = if N = 0 then 28 else if N = 1 then 1 else 0 := by
  by_cases h0 : N = 0
  · subst N; decide +kernel
  by_cases h1 : N = 1
  · subst N; decide +kernel
  have h0' : (0 : ℤ) ≠ (N : ℤ) := by omega
  have h1' : (1 : ℤ) ≠ (N : ℤ) := by omega
  simp [charOne, h0, h1, h0', h1']

end VOA.DeligneAudit.D4Small

#print axioms VOA.DeligneAudit.D4Small.charOne_eq
#print axioms VOA.DeligneAudit.D4Small.charOne_coeff
