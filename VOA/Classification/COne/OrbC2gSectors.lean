import VOA.Classification.COne.OrbC2gEvaluator
import VOA.Classification.COne.OrbC2fIterate

/-! # Certified finite-sector descriptions of the weight-20/22 self-products -/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
namespace VOA.Classification.COne.OrbC2g
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  MvPolynomial VOA.SparseRational PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e OrbC2f LatMod

abbrev SectorVector := List (ℤ × RawPoly ℕ)

noncomputable def evaluate : SectorVector → LatModuleGen (latP 4)
  | [] => 0
  | (d,P) :: S => sector d (evRc (a0 4) (cα 4) P) + evaluate S

def scaleVector (q : ℚ) (S : SectorVector) : SectorVector :=
  S.map fun t => (t.1, scaleR q t.2)

def neutralVector (Q : RawPoly ℕ) (n : ℤ) (S : SectorVector) : SectorVector :=
  S.map fun t => (t.1, neutralAction Q n t.1 t.2)

def exponentialVector (b n : ℤ) (S : SectorVector) : SectorVector :=
  S.map fun t => (b+t.1, exponentialAction b t.1 n t.2)

def eVector (n : ℤ) (S : SectorVector) : SectorVector :=
  exponentialVector 1 n S ++ exponentialVector (-1) n S

theorem evaluate_append (S T : SectorVector) :
    evaluate (S ++ T) = evaluate S + evaluate T := by
  induction S with
  | nil => simp [evaluate]
  | cons s S ih => rcases s with ⟨d,P⟩; simp [evaluate, ih, add_assoc]

theorem evaluate_scaleVector (q : ℚ) (S : SectorVector) :
    evaluate (scaleVector q S) = (q : ℂ) • evaluate S := by
  induction S with
  | nil => simp [scaleVector, evaluate]
  | cons s S ih =>
    rcases s with ⟨d,P⟩
    simp only [scaleVector, List.map_cons, evaluate, evRc_scaleR, map_smul]
    change _ + evaluate (scaleVector q S) = _
    rw [ih, smul_add]

theorem evaluate_neutralVector (Q : RawPoly ℕ) (n : ℤ) (S : SectorVector) :
    evaluate (neutralVector Q n S) = (V2m 4 four_ge_one).smul (ls 4 Q) n (evaluate S) := by
  induction S with
  | nil => simp [neutralVector, evaluate, PreVertexAlgebra.smul_zero_right]
  | cons s S ih =>
    rcases s with ⟨d,P⟩
    simp only [neutralVector, List.map_cons, evaluate, ← neutralAction_sound]
    change _ + evaluate (neutralVector Q n S) = _
    rw [ih, PreVertexAlgebra.smul_add_right]

theorem evaluate_exponentialVector (b n : ℤ) (S : SectorVector) :
    evaluate (exponentialVector b n S) =
      (V2m 4 four_ge_one).smul (latChargeGen (latP 4) b) n (evaluate S) := by
  induction S with
  | nil => simp [exponentialVector, evaluate, PreVertexAlgebra.smul_zero_right]
  | cons s S ih =>
    rcases s with ⟨d,P⟩
    simp only [exponentialVector, List.map_cons, evaluate, ← exponentialAction_sound]
    change _ + evaluate (exponentialVector b n S) = _
    rw [ih, PreVertexAlgebra.smul_add_right]

theorem evaluate_eVector (n : ℤ) (S : SectorVector) :
    evaluate (eVector n S) =
      (V2m 4 four_ge_one).smul (EP 4 four_ge_one) n (evaluate S) := by
  rw [eVector, evaluate_append, evaluate_exponentialVector, evaluate_exponentialVector,
    EP_coe, PreVertexAlgebra.smul_add_left]

def jVector : SectorVector := [(0, liftR JR)]
def eGroundVector : SectorVector := [(1, [(1, [])]), (-1, [(1, [])])]

theorem evaluate_jVector : evaluate jVector = (J 4 four_ge_one : LatModuleGen (latP 4)) := by
  rw [hasN_J]
  simp [jVector, evaluate, evRc_liftR, sector, ls]
  rfl

theorem evaluate_eGroundVector :
    evaluate eGroundVector = (EP 4 four_ge_one : LatModuleGen (latP 4)) := by
  rw [EP_coe]
  simp [eGroundVector, evaluate, evRc_cons, evRc_nil, evalWordC_nil, sector]
  rfl

def nineVector : SectorVector :=
  neutralVector JR (-2) eGroundVector ++ scaleVector (-1) (eVector (-2) jVector)

theorem evaluate_nineVector : evaluate nineVector = (weightNine : LatModuleGen (latP 4)) := by
  rw [nineVector, evaluate_append, evaluate_neutralVector, evaluate_eGroundVector,
    evaluate_scaleVector, evaluate_eVector, evaluate_jVector]
  simp only [weightNine, Submodule.coe_sub, V2mPlus_smul_coe]
  rw [show (J 4 four_ge_one : LatModuleGen (latP 4)) = ls 4 JR from hasN_J _ _]
  norm_num only [Rat.cast_neg, Rat.cast_one, neg_one_smul, sub_eq_add_neg]


def iterateVector (n : ℤ) (i : ℕ) (S : SectorVector) : SectorVector :=
  scaleVector (i+1)
    (neutralVector JR (-2-i) (eVector (n+i) S) ++
      scaleVector (-1) (eVector (-2+n-i) (neutralVector JR i S)) ++
      scaleVector (-1) (eVector (-2-i) (neutralVector JR (n+i) S)) ++
      neutralVector JR (-2+n-i) (eVector i S))

theorem evaluate_iterateVector (n : ℤ) (i : ℕ) :
    evaluate (iterateVector n i nineVector) =
      (seedIterateTerm n i weightNine : LatModuleGen (latP 4)) := by
  have hc : (-1 : ℂ)^i * gBinom (-2) i = (i : ℂ)+1 := by
    rw [gBinom_neg_two, ← mul_assoc, ← mul_pow]
    norm_num
    ring
  simp only [iterateVector, evaluate_scaleVector, evaluate_append, evaluate_neutralVector,
    evaluate_eVector, evaluate_nineVector, seedIterateTerm, Submodule.coe_smul,
    Submodule.coe_sub, V2mPlus_smul_coe, hc]
  norm_num only [Rat.cast_add, Rat.cast_natCast, Rat.cast_one, Rat.cast_neg,
    neg_one_smul, zpow_neg, neg_neg, even_two, Even.neg_pow, one_pow, inv_one, one_smul]
  simp only [show (J 4 four_ge_one : LatModuleGen (latP 4)) = ls 4 JR from hasN_J _ _]
  module

/-- Executable finite coefficient vector for the normalized self-product. -/
def selfVector (n : ℤ) (B : ℕ) : SectorVector :=
  scaleVector (1/8) ((List.range B).flatMap fun i => iterateVector n i nineVector)

theorem evaluate_flatMap_range (B : ℕ) (S : ℕ → SectorVector) :
    evaluate ((List.range B).flatMap S) = ∑ i ∈ Finset.range B, evaluate (S i) := by
  induction B with
  | zero => simp [evaluate]
  | succ B ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton,
      evaluate_append, ih, Finset.sum_range_succ]

/-- A raw coefficient vector connected to the actual weight-20 VOA state. -/
theorem normalizedNine_neg_three_vector :
    ((V2mPlus 4 four_ge_one).smul normalizedNine (-3) normalizedNine :
      LatModuleGen (latP 4)) = evaluate (selfVector (-3) 16) := by
  rw [normalizedNine_self, weightNine_self_neg_three]
  simp only [selfVector, evaluate_scaleVector, evaluate_flatMap_range,
    evaluate_iterateVector, Submodule.coe_smul, Submodule.coe_sum]
  norm_num

/-- A raw coefficient vector connected to the actual weight-22 VOA state. -/
theorem normalizedNine_neg_five_vector :
    ((V2mPlus 4 four_ge_one).smul normalizedNine (-5) normalizedNine :
      LatModuleGen (latP 4)) = evaluate (selfVector (-5) 18) := by
  rw [normalizedNine_self, weightNine_self_neg_five]
  simp only [selfVector, evaluate_scaleVector, evaluate_flatMap_range,
    evaluate_iterateVector, Submodule.coe_smul, Submodule.coe_sum]
  norm_num

end VOA.Classification.COne.OrbC2g
