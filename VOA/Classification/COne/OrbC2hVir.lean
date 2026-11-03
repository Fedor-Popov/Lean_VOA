import VOA.Classification.COne.OrbC2hBounded
import VOA.Classification.COne.OrbC2hNine
import VOA.Classification.COne.OrbC2hRemainders
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
set_option maxHeartbeats 40000
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

local notation "A" => V2m 4 four_ge_one
local notation "P" => V2mPlus 4 four_ge_one

def virS : List ℕ → SectorVector → SectorVector
  | [], S => S
  | k::ks, S => compact (neutralBoundS omR (-(k:ℤ)) (virS ks S))

theorem evaluate_virS (ks : List ℕ) (S : SectorVector) :
    evaluate (virS ks S) = virWord A ks (evaluate S) := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    rw [virS, evaluate_compact, evaluate_neutralBoundS, ih, virWord]
    have ho : ls 4 omR = (A).conformalVector := (omega_coe 4 four_ge_one).symm
    rw [ho]
    change (A).smul (A).conformalVector (-(k:ℤ)) _ =
      (A).smul (A).conformalVector (-(k:ℤ)-1+1) _
    rw [sub_add_cancel]

def wordSumS (ts : List (ℚ × List ℕ)) (S : SectorVector) : SectorVector :=
  ts.flatMap fun t => scaleVector t.1 (virS t.2 S)

theorem evaluate_flatMap (ts : List α) (f : α → SectorVector) :
    evaluate (ts.flatMap f) = (ts.map fun t => evaluate (f t)).sum := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [List.flatMap_cons, evaluate_append, ih,
      List.map_cons, List.sum_cons]

theorem evaluate_wordSumS (ts : List (ℚ × List ℕ)) (S : SectorVector) :
    evaluate (wordSumS ts S) = wordSum A (evaluate S) ts := by
  simp only [wordSumS, evaluate_flatMap, evaluate_scaleVector, evaluate_virS, wordSum]

def vacuumData : SectorVector := [(0,[(1,[])])]

theorem vacuumData_value : evaluate vacuumData = (A).vacuum := by
  simp [vacuumData, evaluate, evRc_cons, evRc_nil, evalWordC_nil, sector]
  rfl

def sixteenS : SectorVector := compact
  (neutralS JR (-9) jVector ++ scaleVector 27 (eS (-9) eGroundVector))

theorem sixteenS_value : evaluate sixteenS = (weightSixteen : LatModuleGen (latP 4)) := by
  rw [sixteenS, evaluate_compact, evaluate_append, evaluate_neutralS,
    evaluate_scaleVector, evaluate_eS, evaluate_jVector, evaluate_eGroundVector]
  change _ = (A).smul (J 4 four_ge_one) (-9) (J 4 four_ge_one) +
    (27:ℂ) • (A).smul (EP 4 four_ge_one) (-9) (EP 4 four_ge_one)
  rw [← hasN_J 4 four_ge_one]
  norm_num


theorem coe_virWord (ks : List ℕ) (x : VP 4 four_ge_one) :
    ((virWord P ks x : VP 4 four_ge_one) : LatModuleGen (latP 4)) = virWord A ks x := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    change (A).L (-(k:ℤ)-1) ((virWord P ks x : VP 4 four_ge_one) : LatModuleGen (latP 4)) =
      (A).L (-(k:ℤ)-1) (virWord A ks x)
    rw [ih]

theorem coe_wordSum (x : VP 4 four_ge_one) (ts : List (ℚ × List ℕ)) :
    ((wordSum P x ts : VP 4 four_ge_one) : LatModuleGen (latP 4)) = wordSum A x ts := by
  change (VP 4 four_ge_one).subtype (wordSum P x ts) = _
  simp only [wordSum, map_list_sum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  simp only [Function.comp_apply, map_smul]
  exact congrArg ((t.1 : ℂ) • ·) (coe_virWord t.2 x)

theorem virWord_ones {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (n : ℕ) (x : V) :
    virWord W (List.replicate n 1) x = (W.L (-2)^n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, virWord, ih, pow_succ', Module.End.mul_apply]
    rfl

end VOA.Classification.COne.OrbC2h
