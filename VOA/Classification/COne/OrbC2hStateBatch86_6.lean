import VOA.Classification.COne.OrbC2hStateBatch86_2
import VOA.Classification.COne.OrbC2hStateBatch86_1
import VOA.Classification.COne.OrbC2hReflection
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hBucketSectors
import VOA.Classification.COne.OrbC2hStateBatch86_4
import VOA.Classification.COne.OrbC2hStateNode83
import VOA.Classification.COne.OrbC2hBounded
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node86Piece96Input_sector0 : RawPoly ℕ := [(-456, [0, 1, 5, 6])]

def node86Piece96Input : SectorVector := [(1, node86Piece96Input_sector0)]
def node86Piece96Output_sector0 : RawPoly ℕ := reflectPoly node86Piece25Output_sector1

def node86Piece96Output_sector1 : RawPoly ℕ := reflectPoly node86Piece25Output_sector0

def node86Piece96Output : SectorVector := [(0, node86Piece96Output_sector0), (2, node86Piece96Output_sector1)]

theorem node86Piece96_check : (reflectVector node86Piece25Output).reverse = node86Piece96Output := by rfl

theorem node86Piece96_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece96Input) = evaluate node86Piece96Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece25_value (by decide +kernel) node86Piece96_check

def node86Piece97Input_sector0 : RawPoly ℕ := [(-90, [0, 2, 2, 2, 2, 4])]

def node86Piece97Input : SectorVector := [(1, node86Piece97Input_sector0)]
def node86Piece97Output_sector0 : RawPoly ℕ := reflectPoly node86Piece26Output_sector1

def node86Piece97Output_sector1 : RawPoly ℕ := reflectPoly node86Piece26Output_sector0

def node86Piece97Output : SectorVector := [(0, node86Piece97Output_sector0), (2, node86Piece97Output_sector1)]

theorem node86Piece97_check : (reflectVector node86Piece26Output).reverse = node86Piece97Output := by rfl

theorem node86Piece97_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece97Input) = evaluate node86Piece97Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece26_value (by decide +kernel) node86Piece97_check

def node86Piece98Input_sector0 : RawPoly ℕ := [(150, [0, 2, 2, 2, 3, 3])]

def node86Piece98Input : SectorVector := [(1, node86Piece98Input_sector0)]
def node86Piece98Output_sector0 : RawPoly ℕ := reflectPoly node86Piece27Output_sector1

def node86Piece98Output_sector1 : RawPoly ℕ := reflectPoly node86Piece27Output_sector0

def node86Piece98Output : SectorVector := [(0, node86Piece98Output_sector0), (2, node86Piece98Output_sector1)]

theorem node86Piece98_check : (reflectVector node86Piece27Output).reverse = node86Piece98Output := by rfl

theorem node86Piece98_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece98Input) = evaluate node86Piece98Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece27_value (by decide +kernel) node86Piece98_check

def node86Piece99Input_sector0 : RawPoly ℕ := [(315, [0, 2, 2, 8])]

def node86Piece99Input : SectorVector := [(1, node86Piece99Input_sector0)]
def node86Piece99Output_sector0 : RawPoly ℕ := reflectPoly node86Piece28Output_sector1

def node86Piece99Output_sector1 : RawPoly ℕ := reflectPoly node86Piece28Output_sector0

def node86Piece99Output : SectorVector := [(0, node86Piece99Output_sector0), (2, node86Piece99Output_sector1)]

theorem node86Piece99_check : (reflectVector node86Piece28Output).reverse = node86Piece99Output := by rfl

theorem node86Piece99_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece99Input) = evaluate node86Piece99Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece28_value (by decide +kernel) node86Piece99_check

def node86Piece100Input_sector0 : RawPoly ℕ := [(360, [0, 2, 3, 7])]

def node86Piece100Input : SectorVector := [(1, node86Piece100Input_sector0)]
def node86Piece100Output_sector0 : RawPoly ℕ := reflectPoly node86Piece29Output_sector1

def node86Piece100Output_sector1 : RawPoly ℕ := reflectPoly node86Piece29Output_sector0

def node86Piece100Output : SectorVector := [(0, node86Piece100Output_sector0), (2, node86Piece100Output_sector1)]

theorem node86Piece100_check : (reflectVector node86Piece29Output).reverse = node86Piece100Output := by rfl

theorem node86Piece100_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece100Input) = evaluate node86Piece100Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece29_value (by decide +kernel) node86Piece100_check

def node86Piece101Input_sector0 : RawPoly ℕ := [(720, [0, 2, 4, 6])]

def node86Piece101Input : SectorVector := [(1, node86Piece101Input_sector0)]
def node86Piece101Output_sector0 : RawPoly ℕ := reflectPoly node86Piece30Output_sector1

def node86Piece101Output_sector1 : RawPoly ℕ := reflectPoly node86Piece30Output_sector0

def node86Piece101Output : SectorVector := [(0, node86Piece101Output_sector0), (2, node86Piece101Output_sector1)]

theorem node86Piece101_check : (reflectVector node86Piece30Output).reverse = node86Piece101Output := by rfl

theorem node86Piece101_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece101Input) = evaluate node86Piece101Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece30_value (by decide +kernel) node86Piece101_check

def node86Piece102Input_sector0 : RawPoly ℕ := [(-576, [0, 2, 5, 5])]

def node86Piece102Input : SectorVector := [(1, node86Piece102Input_sector0)]
def node86Piece102Output_sector0 : RawPoly ℕ := reflectPoly node86Piece31Output_sector1

def node86Piece102Output_sector1 : RawPoly ℕ := reflectPoly node86Piece31Output_sector0

def node86Piece102Output : SectorVector := [(0, node86Piece102Output_sector0), (2, node86Piece102Output_sector1)]

theorem node86Piece102_check : (reflectVector node86Piece31Output).reverse = node86Piece102Output := by rfl

theorem node86Piece102_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece102Input) = evaluate node86Piece102Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece31_value (by decide +kernel) node86Piece102_check

def node86Piece103Input_sector0 : RawPoly ℕ := [(360, [0, 3, 3, 6])]

def node86Piece103Input : SectorVector := [(1, node86Piece103Input_sector0)]
def node86Piece103Output_sector0 : RawPoly ℕ := reflectPoly node86Piece32Output_sector1

def node86Piece103Output_sector1 : RawPoly ℕ := reflectPoly node86Piece32Output_sector0

def node86Piece103Output : SectorVector := [(0, node86Piece103Output_sector0), (2, node86Piece103Output_sector1)]

theorem node86Piece103_check : (reflectVector node86Piece32Output).reverse = node86Piece103Output := by rfl

theorem node86Piece103_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece103Input) = evaluate node86Piece103Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece32_value (by decide +kernel) node86Piece103_check

def node86Piece104Input_sector0 : RawPoly ℕ := [(84, [0, 3, 4, 5])]

def node86Piece104Input : SectorVector := [(1, node86Piece104Input_sector0)]
def node86Piece104Output_sector0 : RawPoly ℕ := reflectPoly node86Piece33Output_sector1

def node86Piece104Output_sector1 : RawPoly ℕ := reflectPoly node86Piece33Output_sector0

def node86Piece104Output : SectorVector := [(0, node86Piece104Output_sector0), (2, node86Piece104Output_sector1)]

theorem node86Piece104_check : (reflectVector node86Piece33Output).reverse = node86Piece104Output := by rfl

theorem node86Piece104_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece104Input) = evaluate node86Piece104Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece33_value (by decide +kernel) node86Piece104_check

def node86Piece105Input_sector0 : RawPoly ℕ := [(240, [0, 4, 4, 4])]

def node86Piece105Input : SectorVector := [(1, node86Piece105Input_sector0)]
def node86Piece105Output_sector0 : RawPoly ℕ := reflectPoly node86Piece34Output_sector1

def node86Piece105Output_sector1 : RawPoly ℕ := reflectPoly node86Piece34Output_sector0

def node86Piece105Output : SectorVector := [(0, node86Piece105Output_sector0), (2, node86Piece105Output_sector1)]

theorem node86Piece105_check : (reflectVector node86Piece34Output).reverse = node86Piece105Output := by rfl

theorem node86Piece105_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece105Input) = evaluate node86Piece105Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece34_value (by decide +kernel) node86Piece105_check

def node86Piece106Input_sector0 : RawPoly ℕ := [(11940, [0, 12])]

def node86Piece106Input : SectorVector := [(1, node86Piece106Input_sector0)]
def node86Piece106Output_sector0 : RawPoly ℕ := reflectPoly node86Piece35Output_sector1

def node86Piece106Output_sector1 : RawPoly ℕ := reflectPoly node86Piece35Output_sector0

def node86Piece106Output : SectorVector := [(0, node86Piece106Output_sector0), (2, node86Piece106Output_sector1)]

theorem node86Piece106_check : (reflectVector node86Piece35Output).reverse = node86Piece106Output := by rfl

theorem node86Piece106_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece106Input) = evaluate node86Piece106Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece35_value (by decide +kernel) node86Piece106_check

def node86Piece107Input_sector0 : RawPoly ℕ := [(-96, [1, 1, 1, 1, 1, 1, 1, 5])]

def node86Piece107Input : SectorVector := [(1, node86Piece107Input_sector0)]
def node86Piece107Output_sector0 : RawPoly ℕ := reflectPoly node86Piece36Output_sector1

def node86Piece107Output_sector1 : RawPoly ℕ := reflectPoly node86Piece36Output_sector0

def node86Piece107Output : SectorVector := [(0, node86Piece107Output_sector0), (2, node86Piece107Output_sector1)]

theorem node86Piece107_check : (reflectVector node86Piece36Output).reverse = node86Piece107Output := by rfl

theorem node86Piece107_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece107Input) = evaluate node86Piece107Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece36_value (by decide +kernel) node86Piece107_check

def node86Piece108Input_sector0 : RawPoly ℕ := [(-112, [1, 1, 1, 1, 1, 1, 2, 4])]

def node86Piece108Input : SectorVector := [(1, node86Piece108Input_sector0)]
def node86Piece108Output_sector0 : RawPoly ℕ := reflectPoly node86Piece37Output_sector1

def node86Piece108Output_sector1 : RawPoly ℕ := reflectPoly node86Piece37Output_sector0

def node86Piece108Output : SectorVector := [(0, node86Piece108Output_sector0), (2, node86Piece108Output_sector1)]

theorem node86Piece108_check : (reflectVector node86Piece37Output).reverse = node86Piece108Output := by rfl

theorem node86Piece108_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece108Input) = evaluate node86Piece108Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece37_value (by decide +kernel) node86Piece108_check

def node86Piece109Input_sector0 : RawPoly ℕ := [(-96, [1, 1, 1, 1, 1, 1, 3, 3])]

def node86Piece109Input : SectorVector := [(1, node86Piece109Input_sector0)]
def node86Piece109Output_sector0 : RawPoly ℕ := reflectPoly node86Piece38Output_sector1

def node86Piece109Output_sector1 : RawPoly ℕ := reflectPoly node86Piece38Output_sector0

def node86Piece109Output : SectorVector := [(0, node86Piece109Output_sector0), (2, node86Piece109Output_sector1)]

theorem node86Piece109_check : (reflectVector node86Piece38Output).reverse = node86Piece109Output := by rfl

theorem node86Piece109_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece109Input) = evaluate node86Piece109Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece38_value (by decide +kernel) node86Piece109_check

def node86Piece110Input_sector0 : RawPoly ℕ := [(144, [1, 1, 1, 1, 1, 2, 2, 3])]

def node86Piece110Input : SectorVector := [(1, node86Piece110Input_sector0)]
def node86Piece110Output_sector0 : RawPoly ℕ := reflectPoly node86Piece39Output_sector1

def node86Piece110Output_sector1 : RawPoly ℕ := reflectPoly node86Piece39Output_sector0

def node86Piece110Output : SectorVector := [(0, node86Piece110Output_sector0), (2, node86Piece110Output_sector1)]

theorem node86Piece110_check : (reflectVector node86Piece39Output).reverse = node86Piece110Output := by rfl

theorem node86Piece110_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece110Input) = evaluate node86Piece110Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece39_value (by decide +kernel) node86Piece110_check

def node86Piece111Input_sector0 : RawPoly ℕ := [(-336, [1, 1, 1, 1, 1, 7])]

def node86Piece111Input : SectorVector := [(1, node86Piece111Input_sector0)]
def node86Piece111Output_sector0 : RawPoly ℕ := reflectPoly node86Piece40Output_sector1

def node86Piece111Output_sector1 : RawPoly ℕ := reflectPoly node86Piece40Output_sector0

def node86Piece111Output : SectorVector := [(0, node86Piece111Output_sector0), (2, node86Piece111Output_sector1)]

theorem node86Piece111_check : (reflectVector node86Piece40Output).reverse = node86Piece111Output := by rfl

theorem node86Piece111_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece111Input) = evaluate node86Piece111Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece40_value (by decide +kernel) node86Piece111_check

end VOA.Classification.COne.OrbC2h
