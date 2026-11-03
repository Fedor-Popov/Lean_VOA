import VOA.Classification.COne.OrbC2hSeed16
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2b OrbC2c OrbC2e OrbC2f OrbC2g LatMod

section General
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)

theorem wordSum_cons (x : V) (t : ℚ × List ℕ) (ts : List (ℚ × List ℕ)) :
    wordSum W x (t::ts) = (t.1:ℂ) • virWord W t.2 x + wordSum W x ts := rfl

theorem wordSum_flatten (x : V) (ts : List (List (ℚ × List ℕ))) :
    wordSum W x ts.flatten = (ts.map (wordSum W x)).sum := by
  simp [wordSum, List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def]
  rfl

theorem wordSum_perm (x : V) {ts us : List (ℚ × List ℕ)} (h : ts.Perm us) :
    wordSum W x ts = wordSum W x us := (h.map _).sum_eq

theorem remainder_of_full_sum (U X : V) (n : ℤ) (p q : ℕ) (a b : ℚ)
    (ts us : List (ℚ × List ℕ))
    (h : W.smul U n U =
      wordSum W W.vacuum ((a,List.replicate p 1)::ts) +
      wordSum W X ((b,List.replicate q 1)::us)) :
    modeRemainder W U X n p q (a:ℂ) (b:ℂ) = wordSum W W.vacuum ts + wordSum W X us := by
  rw [modeRemainder, h, wordSum_cons, wordSum_cons, virWord_ones, virWord_ones]
  module
end General

local notation "A" => V2m 4 four_ge_one
local notation "P" => V2mPlus 4 four_ge_one

theorem plus_self_eq_of_lattice_sum (n : ℤ) (ts us : List (ℚ × List ℕ))
    (h : ((P).smul normalizedNine n normalizedNine : LatModuleGen (latP 4)) =
      wordSum A (A).vacuum ts + wordSum A (weightSixteen : LatModuleGen (latP 4)) us) :
    (P).smul normalizedNine n normalizedNine =
      wordSum P (P).vacuum ts + wordSum P weightSixteen us := by
  apply Subtype.val_injective
  change ((P).smul normalizedNine n normalizedNine : LatModuleGen (latP 4)) =
    ((wordSum P (P).vacuum ts : VP 4 four_ge_one) : LatModuleGen (latP 4)) +
    ((wordSum P weightSixteen us : VP 4 four_ge_one) : LatModuleGen (latP 4))
  rw [coe_wordSum, coe_wordSum]
  exact h
end VOA.Classification.COne.OrbC2h
