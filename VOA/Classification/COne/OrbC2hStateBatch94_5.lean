import VOA.Classification.COne.OrbC2hStateBatch94_2
import VOA.Classification.COne.OrbC2hReflection
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hBucketSectors
import VOA.Classification.COne.OrbC2hStateBatch94_3
import VOA.Classification.COne.OrbC2hStateNode10
import VOA.Classification.COne.OrbC2hBounded
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node94Piece80Input_sector0 : RawPoly ℕ := [(1200, [4, 6])]

def node94Piece80Input : SectorVector := [(1, node94Piece80Input_sector0)]
def node94Piece80Output_sector0 : RawPoly ℕ := reflectPoly node94Piece39Output_sector1

def node94Piece80Output_sector1 : RawPoly ℕ := reflectPoly node94Piece39Output_sector0

def node94Piece80Output : SectorVector := [(0, node94Piece80Output_sector0), (2, node94Piece80Output_sector1)]

theorem node94Piece80_check : (reflectVector node94Piece39Output).reverse = node94Piece80Output := by rfl

theorem node94Piece80_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece80Input) = evaluate node94Piece80Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece39_value (by decide +kernel) node94Piece80_check

def node94Piece81Input_sector0 : RawPoly ℕ := [(-288, [5, 5])]

def node94Piece81Input : SectorVector := [(1, node94Piece81Input_sector0)]
def node94Piece81Output_sector0 : RawPoly ℕ := reflectPoly node94Piece40Output_sector1

def node94Piece81Output_sector1 : RawPoly ℕ := reflectPoly node94Piece40Output_sector0

def node94Piece81Output : SectorVector := [(0, node94Piece81Output_sector0), (2, node94Piece81Output_sector1)]

theorem node94Piece81_check : (reflectVector node94Piece40Output).reverse = node94Piece81Output := by rfl

theorem node94Piece81_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece81Input) = evaluate node94Piece81Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece40_value (by decide +kernel) node94Piece81_check

end VOA.Classification.COne.OrbC2h
