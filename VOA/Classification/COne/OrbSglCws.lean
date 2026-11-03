import VOA.Classification.COne.OrbSglSkew
import VOA.Classification.COne.OrbSglWords
import VOA.Classification.COne.OrbSglSkJ0
import VOA.Classification.COne.OrbSglSkJ1
import VOA.Classification.COne.OrbSglSkJ2
import VOA.Classification.COne.OrbSglSkJ3
import VOA.Classification.COne.OrbSglSkJ4
import VOA.Classification.COne.OrbSglSkJ5
import VOA.Classification.COne.OrbSglSkJ6
import VOA.Classification.COne.OrbSglSkJ7
import VOA.Classification.COne.OrbSglSkJ8
import VOA.Classification.COne.OrbSglSkJ9
import VOA.Classification.COne.OrbSglSkJ10
import VOA.Classification.COne.OrbSglSkJ11
import VOA.Classification.COne.OrbSglSkJ12
import VOA.Classification.COne.OrbSglSkE0
import VOA.Classification.COne.OrbSglSkE1
import VOA.Classification.COne.OrbSglSkE2
import VOA.Classification.COne.OrbSglSkE3
import VOA.Classification.COne.OrbSglSkE4
import VOA.Classification.COne.OrbSglSkE5
import VOA.Classification.COne.OrbSglSkE6
import VOA.Classification.COne.OrbSglSkE7
import VOA.Classification.COne.OrbSglSkE8
import VOA.Classification.COne.OrbSglSkE9
import VOA.Classification.COne.OrbSglSkE10
import VOA.Classification.COne.OrbSglSkE11
import VOA.Classification.COne.OrbSglSkE12

/-!
# OrbSgl (9): `u₍₁₅₎ v' = c' u` with `c' = -190512/5`

`u = weightNine`, `v' = wsP = v_num − x₀` (the weight-16 primary of `V₈⁺`).

* `nine_smul_sixteen`: `u₍₁₅₎ v_num = 374283666 u`: commutator formula
  `u₍₁₅₎a₍₋₉₎a = Σ_{k<13} C(15,k) (u₍ₖ₎a)₍₆₋ₖ₎a` (`comm_finite`), each term certified in
  `OrbSglSk{J,E}{k}` (`sk_Jk`, `sk_Ek`), the sum in `termSum_cert`.
* `nine_smul_x0` (`OrbSglWords`): `u₍₁₅₎ x₀ = (1871608842/5) u`.
* `nine_smul_wsP`: `u₍₁₅₎ v' = (-190512/5) u`.
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000

noncomputable section

namespace VOA.Classification.COne.OrbSgl

open VOA VertexOperatorAlgebra VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational
  OrbC2g OrbC2h OrbC2c OrbC2e OrbC2f PlusC2 PlusC2Eval PlusUnitary

local notation "V8" => V2m 4 four_ge_one

/-- The commutator expansion. -/
theorem nine_smul_pair (isJ : Bool) :
    (V8).smul (weightNine : LatModuleGen (latP 4)) 15
        ((V8).smul (aVec isJ : LatModuleGen (latP 4)) (-9) (aVec isJ)) =
      ∑ k ∈ Finset.range 13, ((Nat.choose 15 k : ℕ) : ℂ) •
        (V8).smul ((V8).smul (weightNine : LatModuleGen (latP 4)) k (aVec isJ)) (6 - (k : ℕ))
          (aVec isJ : LatModuleGen (latP 4)) := by
  have hnine : (weightNine : LatModuleGen (latP 4)) ∈ (V8).grading 9 := weightNine_mem_grading
  rw [comm_finite (V8) hnine (aVec_mem' isJ) 15 (-9) 13 (by norm_num),
    OrbC2f.smul_eq_zero_of_weights (V8) hnine (aVec_mem' isJ) (n := 15) (by norm_num),
    PreVertexAlgebra.smul_zero_right, zero_add]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [show (15 : ℤ) = ((15 : ℕ) : ℤ) from rfl,
    FieldCombinatorics.gBinom_natCast_eq_choose (by simp at hk; omega)]
  congr 2

/-- The certified term vectors. -/
def termF : Bool → ℕ → SectorVector
  | true, k => [termJ_0, termJ_1, termJ_2, termJ_3, termJ_4, termJ_5, termJ_6, termJ_7, termJ_8, termJ_9, termJ_10, termJ_11, termJ_12].getD k []
  | false, k => [termE_0, termE_1, termE_2, termE_3, termE_4, termE_5, termE_6, termE_7, termE_8, termE_9, termE_10, termE_11, termE_12].getD k []

theorem termF_value (isJ : Bool) (k : ℕ) (hk : k < 13) :
    evaluate (termF isJ k) = ((Nat.choose 15 k : ℕ) : ℂ) •
      (V8).smul ((V8).smul (weightNine : LatModuleGen (latP 4)) k (aVec isJ)) (6 - (k : ℕ))
        (aVec isJ : LatModuleGen (latP 4)) := by
  cases isJ
  · interval_cases k
    · exact sk_E0
    · exact sk_E1
    · exact sk_E2
    · exact sk_E3
    · exact sk_E4
    · exact sk_E5
    · exact sk_E6
    · exact sk_E7
    · exact sk_E8
    · exact sk_E9
    · exact sk_E10
    · exact sk_E11
    · exact sk_E12
  · interval_cases k
    · exact sk_J0
    · exact sk_J1
    · exact sk_J2
    · exact sk_J3
    · exact sk_J4
    · exact sk_J5
    · exact sk_J6
    · exact sk_J7
    · exact sk_J8
    · exact sk_J9
    · exact sk_J10
    · exact sk_J11
    · exact sk_J12

theorem weightSixteen_coe : (weightSixteen : LatModuleGen (latP 4)) =
    (V8).smul (aVec true : LatModuleGen (latP 4)) (-9) (aVec true) +
      (27 : ℂ) • (V8).smul (aVec false : LatModuleGen (latP 4)) (-9) (aVec false) := by
  simp only [weightSixteen, aVec, Submodule.coe_add, Submodule.coe_smul, V2mPlus_smul_coe]
  rfl

theorem evaluate_termSum : evaluate termSum =
    ∑ k ∈ Finset.range 13, evaluate (termF true k) +
      (27 : ℂ) • ∑ k ∈ Finset.range 13, evaluate (termF false k) := by
  simp only [termSum, termF, List.flatten_cons, List.flatten_nil, List.append_nil,
    evaluate_append, evaluate_scaleVector, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, List.getD_cons_succ, List.getD_cons_zero]
  push_cast
  simp only [smul_add, add_assoc]

/-- `u₍₁₅₎ v_num = 374283666 u`. -/
theorem nine_smul_sixteen :
    (V8).smul (weightNine : LatModuleGen (latP 4)) 15 (weightSixteen : LatModuleGen (latP 4)) =
      (374283666 : ℂ) • (weightNine : LatModuleGen (latP 4)) := by
  rw [weightSixteen_coe, PreVertexAlgebra.smul_add_right, PreVertexAlgebra.smul_smul_right,
    nine_smul_pair true, nine_smul_pair false,
    ← Finset.sum_congr rfl fun k hk => termF_value true k (Finset.mem_range.mp hk),
    ← Finset.sum_congr rfl fun k hk => termF_value false k (Finset.mem_range.mp hk),
    ← evaluate_termSum, vector_eq_of_certificate _ _ termSum_cert, evaluate_scaleVector,
    nine_value]
  push_cast
  rfl

/-- `u₍₁₅₎ v' = (-190512/5) u` in `V₈⁺`. -/
theorem nine_smul_wsP :
    (V2mPlus 4 four_ge_one).smul weightNine 15 wsP = ((-190512 / 5 : ℚ) : ℂ) • weightNine := by
  have h16 : (V2mPlus 4 four_ge_one).smul weightNine 15 weightSixteen =
      (374283666 : ℂ) • weightNine := by
    apply Subtype.ext
    rw [V2mPlus_smul_coe, nine_smul_sixteen, Submodule.coe_smul]
  rw [wsP, show weightSixteen - x0P = weightSixteen + (-1 : ℂ) • x0P by
      rw [neg_one_smul, sub_eq_add_neg],
    PreVertexAlgebra.smul_add_right, PreVertexAlgebra.smul_smul_right, h16, nine_smul_x0, smul_smul,
    ← add_smul]
  congr 1
  push_cast
  norm_num

end VOA.Classification.COne.OrbSgl
