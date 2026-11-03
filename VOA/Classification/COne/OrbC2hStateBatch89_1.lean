import VOA.Classification.COne.OrbC2hStateBatch89_0
import VOA.Classification.COne.OrbC2hReflection
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hBucketSectors
import VOA.Classification.COne.OrbC2hStateNode17
import VOA.Classification.COne.OrbC2hBounded
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node89Piece16Input_sector0 : RawPoly ℕ := [(-560, [1, 1, 1, 1, 1, 1])]

def node89Piece16Input : SectorVector := [(1, node89Piece16Input_sector0)]
def node89Piece16Output_sector0 : RawPoly ℕ := reflectPoly node89Piece5Output_sector1

def node89Piece16Output_sector1 : RawPoly ℕ := reflectPoly node89Piece5Output_sector0

def node89Piece16Output : SectorVector := [(0, node89Piece16Output_sector0), (2, node89Piece16Output_sector1)]

theorem node89Piece16_check : (reflectVector node89Piece5Output).reverse = node89Piece16Output := by rfl

theorem node89Piece16_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-9)
    (evaluate node89Piece16Input) = evaluate node89Piece16Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-9) _ _ _ _
    node89Piece5_value (by decide +kernel) node89Piece16_check

def node89Piece17Input_sector0 : RawPoly ℕ := [(-4960, [1, 1, 1, 3])]

def node89Piece17Input : SectorVector := [(1, node89Piece17Input_sector0)]
def node89Piece17Output_sector0 : RawPoly ℕ := reflectPoly node89Piece6Output_sector1

def node89Piece17Output_sector1 : RawPoly ℕ := reflectPoly node89Piece6Output_sector0

def node89Piece17Output : SectorVector := [(0, node89Piece17Output_sector0), (2, node89Piece17Output_sector1)]

theorem node89Piece17_check : (reflectVector node89Piece6Output).reverse = node89Piece17Output := by rfl

theorem node89Piece17_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-9)
    (evaluate node89Piece17Input) = evaluate node89Piece17Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-9) _ _ _ _
    node89Piece6_value (by decide +kernel) node89Piece17_check

def node89Piece18Input_sector0 : RawPoly ℕ := [(-1080, [1, 1, 2, 2])]

def node89Piece18Input : SectorVector := [(1, node89Piece18Input_sector0)]
def node89Piece18Output_sector0 : RawPoly ℕ := reflectPoly node89Piece7Output_sector1

def node89Piece18Output_sector1 : RawPoly ℕ := reflectPoly node89Piece7Output_sector0

def node89Piece18Output : SectorVector := [(0, node89Piece18Output_sector0), (2, node89Piece18Output_sector1)]

theorem node89Piece18_check : (reflectVector node89Piece7Output).reverse = node89Piece18Output := by rfl

theorem node89Piece18_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-9)
    (evaluate node89Piece18Input) = evaluate node89Piece18Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-9) _ _ _ _
    node89Piece7_value (by decide +kernel) node89Piece18_check

def node89Piece19Input_sector0 : RawPoly ℕ := [(-16560, [1, 5])]

def node89Piece19Input : SectorVector := [(1, node89Piece19Input_sector0)]
def node89Piece19Output_sector0 : RawPoly ℕ := reflectPoly node89Piece8Output_sector1

def node89Piece19Output_sector1 : RawPoly ℕ := reflectPoly node89Piece8Output_sector0

def node89Piece19Output : SectorVector := [(0, node89Piece19Output_sector0), (2, node89Piece19Output_sector1)]

theorem node89Piece19_check : (reflectVector node89Piece8Output).reverse = node89Piece19Output := by rfl

theorem node89Piece19_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-9)
    (evaluate node89Piece19Input) = evaluate node89Piece19Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-9) _ _ _ _
    node89Piece8_value (by decide +kernel) node89Piece19_check

def node89Piece20Input_sector0 : RawPoly ℕ := [(-720, [2, 4])]

def node89Piece20Input : SectorVector := [(1, node89Piece20Input_sector0)]
def node89Piece20Output_sector0 : RawPoly ℕ := reflectPoly node89Piece9Output_sector1

def node89Piece20Output_sector1 : RawPoly ℕ := reflectPoly node89Piece9Output_sector0

def node89Piece20Output : SectorVector := [(0, node89Piece20Output_sector0), (2, node89Piece20Output_sector1)]

theorem node89Piece20_check : (reflectVector node89Piece9Output).reverse = node89Piece20Output := by rfl

theorem node89Piece20_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-9)
    (evaluate node89Piece20Input) = evaluate node89Piece20Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-9) _ _ _ _
    node89Piece9_value (by decide +kernel) node89Piece20_check

def node89Piece21Input_sector0 : RawPoly ℕ := [(640, [3, 3])]

def node89Piece21Input : SectorVector := [(1, node89Piece21Input_sector0)]
def node89Piece21Output_sector0 : RawPoly ℕ := reflectPoly node89Piece10Output_sector1

def node89Piece21Output_sector1 : RawPoly ℕ := reflectPoly node89Piece10Output_sector0

def node89Piece21Output : SectorVector := [(0, node89Piece21Output_sector0), (2, node89Piece21Output_sector1)]

theorem node89Piece21_check : (reflectVector node89Piece10Output).reverse = node89Piece21Output := by rfl

theorem node89Piece21_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-9)
    (evaluate node89Piece21Input) = evaluate node89Piece21Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-9) _ _ _ _
    node89Piece10_value (by decide +kernel) node89Piece21_check

end VOA.Classification.COne.OrbC2h
