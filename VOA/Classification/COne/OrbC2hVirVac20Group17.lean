import VOA.Classification.COne.OrbC2hVirVacCache29
import VOA.Classification.COne.OrbC2hVirVac20Group16
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def vac20Group17Terms : List (ℚ × List ℕ) := [(80660746644060835136/65900835, [19])]

def vac20Group17Data_sector0 : RawPoly ℕ := [(80660746644060835136/65900835, [1, 19]), (80660746644060835136/65900835, [2, 18]), (80660746644060835136/65900835, [3, 17]), (80660746644060835136/65900835, [4, 16]), (80660746644060835136/65900835, [5, 15]), (80660746644060835136/65900835, [6, 14]), (80660746644060835136/65900835, [7, 13]), (80660746644060835136/65900835, [8, 12]), (80660746644060835136/65900835, [9, 11]), (40330373322030417568/65900835, [10, 10])]

def vac20Group17Data : SectorVector := [(0, vac20Group17Data_sector0)]

theorem vac20Group17_check : zipMany 100000 [scaleVector (80660746644060835136/65900835) vVac465Data] = vac20Group17Data := by decide +kernel

theorem vac20Group17_value : wordSum (V2m 4 four_ge_one) (evaluate vacuumData) vac20Group17Terms = evaluate vac20Group17Data := by
  rw [← vac20Group17_check, evaluate_zipMany]
  simp only [vac20Group17Terms, wordSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    evaluate_scaleVector, vVac465_value]

end VOA.Classification.COne.OrbC2h
