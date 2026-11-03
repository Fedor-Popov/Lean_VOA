import VOA.Classification.COne.OrbC2hStateBatch90_3
import VOA.Classification.COne.OrbC2hStateBatch90_2
import VOA.Classification.COne.OrbC2hReflection
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hBucketSectors
import VOA.Classification.COne.OrbC2hStateBatch90_4
import VOA.Classification.COne.OrbC2hStateNode2
import VOA.Classification.COne.OrbC2hBounded
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node90Piece96Input_sector0 : RawPoly ℕ := [(-2580, [1, 2, 2, 6])]

def node90Piece96Input : SectorVector := [(1, node90Piece96Input_sector0)]
def node90Piece96Output_sector0 : RawPoly ℕ := reflectPoly node90Piece42Output_sector1

def node90Piece96Output_sector1 : RawPoly ℕ := reflectPoly node90Piece42Output_sector0

def node90Piece96Output : SectorVector := [(0, node90Piece96Output_sector0), (2, node90Piece96Output_sector1)]

theorem node90Piece96_check : (reflectVector node90Piece42Output).reverse = node90Piece96Output := by rfl

theorem node90Piece96_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece96Input) = evaluate node90Piece96Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece42_value (by decide +kernel) node90Piece96_check

def node90Piece97Input_sector0 : RawPoly ℕ := [(-2352, [1, 2, 3, 5])]

def node90Piece97Input : SectorVector := [(1, node90Piece97Input_sector0)]
def node90Piece97Output_sector0 : RawPoly ℕ := reflectPoly node90Piece43Output_sector1

def node90Piece97Output_sector1 : RawPoly ℕ := reflectPoly node90Piece43Output_sector0

def node90Piece97Output : SectorVector := [(0, node90Piece97Output_sector0), (2, node90Piece97Output_sector1)]

theorem node90Piece97_check : (reflectVector node90Piece43Output).reverse = node90Piece97Output := by rfl

theorem node90Piece97_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece97Input) = evaluate node90Piece97Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece43_value (by decide +kernel) node90Piece97_check

def node90Piece98Input_sector0 : RawPoly ℕ := [(3690, [1, 2, 4, 4])]

def node90Piece98Input : SectorVector := [(1, node90Piece98Input_sector0)]
def node90Piece98Output_sector0 : RawPoly ℕ := reflectPoly node90Piece44Output_sector1

def node90Piece98Output_sector1 : RawPoly ℕ := reflectPoly node90Piece44Output_sector0

def node90Piece98Output : SectorVector := [(0, node90Piece98Output_sector0), (2, node90Piece98Output_sector1)]

theorem node90Piece98_check : (reflectVector node90Piece44Output).reverse = node90Piece98Output := by rfl

theorem node90Piece98_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece98Input) = evaluate node90Piece98Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece44_value (by decide +kernel) node90Piece98_check

def node90Piece99Input_sector0 : RawPoly ℕ := [(480, [1, 3, 3, 4])]

def node90Piece99Input : SectorVector := [(1, node90Piece99Input_sector0)]
def node90Piece99Output_sector0 : RawPoly ℕ := reflectPoly node90Piece45Output_sector1

def node90Piece99Output_sector1 : RawPoly ℕ := reflectPoly node90Piece45Output_sector0

def node90Piece99Output : SectorVector := [(0, node90Piece99Output_sector0), (2, node90Piece99Output_sector1)]

theorem node90Piece99_check : (reflectVector node90Piece45Output).reverse = node90Piece99Output := by rfl

theorem node90Piece99_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece99Input) = evaluate node90Piece99Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece45_value (by decide +kernel) node90Piece99_check

def node90Piece100Input_sector0 : RawPoly ℕ := [(-31320, [1, 10])]

def node90Piece100Input : SectorVector := [(1, node90Piece100Input_sector0)]
def node90Piece100Output_sector0 : RawPoly ℕ := reflectPoly node90Piece46Output_sector1

def node90Piece100Output_sector1 : RawPoly ℕ := reflectPoly node90Piece46Output_sector0

def node90Piece100Output : SectorVector := [(0, node90Piece100Output_sector0), (2, node90Piece100Output_sector1)]

theorem node90Piece100_check : (reflectVector node90Piece46Output).reverse = node90Piece100Output := by rfl

theorem node90Piece100_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece100Input) = evaluate node90Piece100Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece46_value (by decide +kernel) node90Piece100_check

def node90Piece101Input_sector0 : RawPoly ℕ := [(-912, [2, 2, 2, 5])]

def node90Piece101Input : SectorVector := [(1, node90Piece101Input_sector0)]
def node90Piece101Output_sector0 : RawPoly ℕ := reflectPoly node90Piece47Output_sector1

def node90Piece101Output_sector1 : RawPoly ℕ := reflectPoly node90Piece47Output_sector0

def node90Piece101Output : SectorVector := [(0, node90Piece101Output_sector0), (2, node90Piece101Output_sector1)]

theorem node90Piece101_check : (reflectVector node90Piece47Output).reverse = node90Piece101Output := by rfl

theorem node90Piece101_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece101Input) = evaluate node90Piece101Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece47_value (by decide +kernel) node90Piece101_check

def node90Piece102Input_sector0 : RawPoly ℕ := [(2820, [2, 2, 3, 4])]

def node90Piece102Input : SectorVector := [(1, node90Piece102Input_sector0)]
def node90Piece102Output_sector0 : RawPoly ℕ := reflectPoly node90Piece48Output_sector1

def node90Piece102Output_sector1 : RawPoly ℕ := reflectPoly node90Piece48Output_sector0

def node90Piece102Output : SectorVector := [(0, node90Piece102Output_sector0), (2, node90Piece102Output_sector1)]

theorem node90Piece102_check : (reflectVector node90Piece48Output).reverse = node90Piece102Output := by rfl

theorem node90Piece102_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece102Input) = evaluate node90Piece102Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece48_value (by decide +kernel) node90Piece102_check

def node90Piece103Input_sector0 : RawPoly ℕ := [(1760, [2, 3, 3, 3])]

def node90Piece103Input : SectorVector := [(1, node90Piece103Input_sector0)]
def node90Piece103Output_sector0 : RawPoly ℕ := reflectPoly node90Piece49Output_sector1

def node90Piece103Output_sector1 : RawPoly ℕ := reflectPoly node90Piece49Output_sector0

def node90Piece103Output : SectorVector := [(0, node90Piece103Output_sector0), (2, node90Piece103Output_sector1)]

theorem node90Piece103_check : (reflectVector node90Piece49Output).reverse = node90Piece103Output := by rfl

theorem node90Piece103_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece103Input) = evaluate node90Piece103Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece49_value (by decide +kernel) node90Piece103_check

def node90Piece104Input_sector0 : RawPoly ℕ := [(-9840, [2, 9])]

def node90Piece104Input : SectorVector := [(1, node90Piece104Input_sector0)]
def node90Piece104Output_sector0 : RawPoly ℕ := reflectPoly node90Piece50Output_sector1

def node90Piece104Output_sector1 : RawPoly ℕ := reflectPoly node90Piece50Output_sector0

def node90Piece104Output : SectorVector := [(0, node90Piece104Output_sector0), (2, node90Piece104Output_sector1)]

theorem node90Piece104_check : (reflectVector node90Piece50Output).reverse = node90Piece104Output := by rfl

theorem node90Piece104_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece104Input) = evaluate node90Piece104Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece50_value (by decide +kernel) node90Piece104_check

def node90Piece105Input_sector0 : RawPoly ℕ := [(-2760, [3, 8])]

def node90Piece105Input : SectorVector := [(1, node90Piece105Input_sector0)]
def node90Piece105Output_sector0 : RawPoly ℕ := reflectPoly node90Piece51Output_sector1

def node90Piece105Output_sector1 : RawPoly ℕ := reflectPoly node90Piece51Output_sector0

def node90Piece105Output : SectorVector := [(0, node90Piece105Output_sector0), (2, node90Piece105Output_sector1)]

theorem node90Piece105_check : (reflectVector node90Piece51Output).reverse = node90Piece105Output := by rfl

theorem node90Piece105_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece105Input) = evaluate node90Piece105Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece51_value (by decide +kernel) node90Piece105_check

def node90Piece106Input_sector0 : RawPoly ℕ := [(720, [4, 7])]

def node90Piece106Input : SectorVector := [(1, node90Piece106Input_sector0)]
def node90Piece106Output_sector0 : RawPoly ℕ := reflectPoly node90Piece52Output_sector1

def node90Piece106Output_sector1 : RawPoly ℕ := reflectPoly node90Piece52Output_sector0

def node90Piece106Output : SectorVector := [(0, node90Piece106Output_sector0), (2, node90Piece106Output_sector1)]

theorem node90Piece106_check : (reflectVector node90Piece52Output).reverse = node90Piece106Output := by rfl

theorem node90Piece106_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece106Input) = evaluate node90Piece106Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece52_value (by decide +kernel) node90Piece106_check

def node90Piece107Input_sector0 : RawPoly ℕ := [(240, [5, 6])]

def node90Piece107Input : SectorVector := [(1, node90Piece107Input_sector0)]
def node90Piece107Output_sector0 : RawPoly ℕ := reflectPoly node90Piece53Output_sector1

def node90Piece107Output_sector1 : RawPoly ℕ := reflectPoly node90Piece53Output_sector0

def node90Piece107Output : SectorVector := [(0, node90Piece107Output_sector0), (2, node90Piece107Output_sector1)]

theorem node90Piece107_check : (reflectVector node90Piece53Output).reverse = node90Piece107Output := by rfl

theorem node90Piece107_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece107Input) = evaluate node90Piece107Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece53_value (by decide +kernel) node90Piece107_check

end VOA.Classification.COne.OrbC2h
