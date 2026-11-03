import VOA.Classification.COne.OrbC2hCertificates
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def nineData_sector0 : RawPoly ℕ := [(1, [0, 1, 1, 1, 1, 1]), (10, [0, 1, 1, 3]), (15/2, [0, 1, 2, 2]), (6, [0, 5]), (20, [1, 1, 1, 2]), (30, [1, 4]), (20, [2, 3])]

def nineData_sector1 : RawPoly ℕ := [(-1, [0, 1, 1, 1, 1, 1]), (-10, [0, 1, 1, 3]), (-15/2, [0, 1, 2, 2]), (-6, [0, 5]), (20, [1, 1, 1, 2]), (30, [1, 4]), (20, [2, 3])]

def nineData : SectorVector := [(-1, nineData_sector0), (1, nineData_sector1)]
theorem nine_check : VectorCertificate nineS nineData := by decide +kernel

theorem nine_value : evaluate nineData = (weightNine : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ nine_check, evaluate_nineS]

theorem nine_value_vector : evaluate nineData = evaluate nineVector := by
  rw [nine_value, evaluate_nineVector]
end VOA.Classification.COne.OrbC2h
