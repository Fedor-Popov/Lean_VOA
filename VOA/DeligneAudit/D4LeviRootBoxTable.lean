import VOA.DeligneAudit.D4LeviOrbitBasis

/-! Six rank-one current triples for the negative radical roots. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.DeligneSector.Sparse

def rootSign : Fin 6 → ℤ
  | 0 => 1
  | _ => -1

def rootWeight (m : ℕ) (j : Fin 6) : ℕ :=
  if j = 0 then 0 else if j = 5 then 2 * m else m

theorem rootExponent_eq (m : ℕ) (j : Fin 6) :
    rootExponent m (radicalColour j) = rootWeight m j + 1 := by
  fin_cases j <;> simp [rootExponent, rootWeight, radicalColour]

set_option maxHeartbeats 8000000 in
-- Exhaustive sparse-table support check across six roots and 28 colours.
theorem root_ef_cartan_support :
    ∀ j : Fin 6, ∀ c : Fin 28, 4 ≤ c.val →
      fZ br (positiveColour j) (radicalColour j) c = 0 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Exhaustive double-bracket check across six rank-one triples.
theorem root_hf_table :
    ∀ j : Fin 6, ∀ d : Fin 28,
      rootSign j *
        (∑ c : Fin 28,
          fZ br (positiveColour j) (radicalColour j) c *
            fZ br c (radicalColour j) d) =
        if d = radicalColour j then -2 else 0 := by
  decide +kernel

theorem root_ef_cartan_supportC (j : Fin 6) (c : Fin 28)
    (hc : 4 ≤ c.val) :
    fD4 (positiveColour j) (radicalColour j) c = 0 := by
  simpa only [fD4, fC, fZ, Int.cast_zero] using
    congrArg (fun n : ℤ => (n : ℂ))
      (root_ef_cartan_support j c hc)

theorem root_hf_tableC (j : Fin 6) (d : Fin 28) :
    (rootSign j : ℂ) *
      (∑ c : Fin 28,
        fD4 (positiveColour j) (radicalColour j) c *
          fD4 c (radicalColour j) d) =
      if d = radicalColour j then (-2 : ℂ) else 0 := by
  simpa only [fD4, fC, fZ, Int.cast_mul, Int.cast_sum, Int.cast_ite,
    Int.cast_ofNat, Int.cast_neg, Int.cast_zero] using
      congrArg (fun n : ℤ => (n : ℂ)) (root_hf_table j d)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rootExponent_eq
#print axioms VOA.DeligneAudit.D4Levi.root_ef_cartan_support
#print axioms VOA.DeligneAudit.D4Levi.root_hf_table
#print axioms VOA.DeligneAudit.D4Levi.root_ef_cartan_supportC
#print axioms VOA.DeligneAudit.D4Levi.root_hf_tableC
