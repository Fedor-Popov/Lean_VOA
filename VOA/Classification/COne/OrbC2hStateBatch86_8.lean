import VOA.Classification.COne.OrbC2hStateBatch86_4
import VOA.Classification.COne.OrbC2hStateBatch86_3
import VOA.Classification.COne.OrbC2hReflection
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hBucketSectors
import VOA.Classification.COne.OrbC2hStateBatch86_6
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

def node86Piece128Input_sector0 : RawPoly ℕ := [(-1360, [1, 2, 3, 6])]

def node86Piece128Input : SectorVector := [(1, node86Piece128Input_sector0)]
def node86Piece128Output_sector0 : RawPoly ℕ := reflectPoly node86Piece57Output_sector1

def node86Piece128Output_sector1 : RawPoly ℕ := reflectPoly node86Piece57Output_sector0

def node86Piece128Output : SectorVector := [(0, node86Piece128Output_sector0), (2, node86Piece128Output_sector1)]

theorem node86Piece128_check : (reflectVector node86Piece57Output).reverse = node86Piece128Output := by rfl

theorem node86Piece128_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece128Input) = evaluate node86Piece128Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece57_value (by decide +kernel) node86Piece128_check

def node86Piece129Input_sector0 : RawPoly ℕ := [(2448, [1, 2, 4, 5])]

def node86Piece129Input : SectorVector := [(1, node86Piece129Input_sector0)]
def node86Piece129Output_sector0 : RawPoly ℕ := reflectPoly node86Piece58Output_sector1

def node86Piece129Output_sector1 : RawPoly ℕ := reflectPoly node86Piece58Output_sector0

def node86Piece129Output : SectorVector := [(0, node86Piece129Output_sector0), (2, node86Piece129Output_sector1)]

theorem node86Piece129_check : (reflectVector node86Piece58Output).reverse = node86Piece129Output := by rfl

theorem node86Piece129_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece129Input) = evaluate node86Piece129Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece58_value (by decide +kernel) node86Piece129_check

def node86Piece130Input_sector0 : RawPoly ℕ := [(-2016, [1, 3, 3, 5])]

def node86Piece130Input : SectorVector := [(1, node86Piece130Input_sector0)]
def node86Piece130Output_sector0 : RawPoly ℕ := reflectPoly node86Piece59Output_sector1

def node86Piece130Output_sector1 : RawPoly ℕ := reflectPoly node86Piece59Output_sector0

def node86Piece130Output : SectorVector := [(0, node86Piece130Output_sector0), (2, node86Piece130Output_sector1)]

theorem node86Piece130_check : (reflectVector node86Piece59Output).reverse = node86Piece130Output := by rfl

theorem node86Piece130_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece130Input) = evaluate node86Piece130Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece59_value (by decide +kernel) node86Piece130_check

def node86Piece131Input_sector0 : RawPoly ℕ := [(3900, [1, 3, 4, 4])]

def node86Piece131Input : SectorVector := [(1, node86Piece131Input_sector0)]
def node86Piece131Output_sector0 : RawPoly ℕ := reflectPoly node86Piece60Output_sector1

def node86Piece131Output_sector1 : RawPoly ℕ := reflectPoly node86Piece60Output_sector0

def node86Piece131Output : SectorVector := [(0, node86Piece131Output_sector0), (2, node86Piece131Output_sector1)]

theorem node86Piece131_check : (reflectVector node86Piece60Output).reverse = node86Piece131Output := by rfl

theorem node86Piece131_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece131Input) = evaluate node86Piece131Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece60_value (by decide +kernel) node86Piece131_check

def node86Piece132Input_sector0 : RawPoly ℕ := [(-35280, [1, 11])]

def node86Piece132Input : SectorVector := [(1, node86Piece132Input_sector0)]
def node86Piece132Output_sector0 : RawPoly ℕ := reflectPoly node86Piece61Output_sector1

def node86Piece132Output_sector1 : RawPoly ℕ := reflectPoly node86Piece61Output_sector0

def node86Piece132Output : SectorVector := [(0, node86Piece132Output_sector0), (2, node86Piece132Output_sector1)]

theorem node86Piece132_check : (reflectVector node86Piece61Output).reverse = node86Piece132Output := by rfl

theorem node86Piece132_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece132Input) = evaluate node86Piece132Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece61_value (by decide +kernel) node86Piece132_check

def node86Piece133Input_sector0 : RawPoly ℕ := [(-720, [2, 2, 2, 6])]

def node86Piece133Input : SectorVector := [(1, node86Piece133Input_sector0)]
def node86Piece133Output_sector0 : RawPoly ℕ := reflectPoly node86Piece62Output_sector1

def node86Piece133Output_sector1 : RawPoly ℕ := reflectPoly node86Piece62Output_sector0

def node86Piece133Output : SectorVector := [(0, node86Piece133Output_sector0), (2, node86Piece133Output_sector1)]

theorem node86Piece133_check : (reflectVector node86Piece62Output).reverse = node86Piece133Output := by rfl

theorem node86Piece133_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece133Input) = evaluate node86Piece133Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece62_value (by decide +kernel) node86Piece133_check

def node86Piece134Input_sector0 : RawPoly ℕ := [(1824, [2, 2, 3, 5])]

def node86Piece134Input : SectorVector := [(1, node86Piece134Input_sector0)]
def node86Piece134Output_sector0 : RawPoly ℕ := reflectPoly node86Piece63Output_sector1

def node86Piece134Output_sector1 : RawPoly ℕ := reflectPoly node86Piece63Output_sector0

def node86Piece134Output : SectorVector := [(0, node86Piece134Output_sector0), (2, node86Piece134Output_sector1)]

theorem node86Piece134_check : (reflectVector node86Piece63Output).reverse = node86Piece134Output := by rfl

theorem node86Piece134_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece134Input) = evaluate node86Piece134Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece63_value (by decide +kernel) node86Piece134_check

def node86Piece135Input_sector0 : RawPoly ℕ := [(360, [2, 2, 4, 4])]

def node86Piece135Input : SectorVector := [(1, node86Piece135Input_sector0)]
def node86Piece135Output_sector0 : RawPoly ℕ := reflectPoly node86Piece64Output_sector1

def node86Piece135Output_sector1 : RawPoly ℕ := reflectPoly node86Piece64Output_sector0

def node86Piece135Output : SectorVector := [(0, node86Piece135Output_sector0), (2, node86Piece135Output_sector1)]

theorem node86Piece135_check : (reflectVector node86Piece64Output).reverse = node86Piece135Output := by rfl

theorem node86Piece135_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece135Input) = evaluate node86Piece135Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece64_value (by decide +kernel) node86Piece135_check

def node86Piece136Input_sector0 : RawPoly ℕ := [(4160, [2, 3, 3, 4])]

def node86Piece136Input : SectorVector := [(1, node86Piece136Input_sector0)]
def node86Piece136Output_sector0 : RawPoly ℕ := reflectPoly node86Piece65Output_sector1

def node86Piece136Output_sector1 : RawPoly ℕ := reflectPoly node86Piece65Output_sector0

def node86Piece136Output : SectorVector := [(0, node86Piece136Output_sector0), (2, node86Piece136Output_sector1)]

theorem node86Piece136_check : (reflectVector node86Piece65Output).reverse = node86Piece136Output := by rfl

theorem node86Piece136_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece136Input) = evaluate node86Piece136Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece65_value (by decide +kernel) node86Piece136_check

def node86Piece137Input_sector0 : RawPoly ℕ := [(-11520, [2, 10])]

def node86Piece137Input : SectorVector := [(1, node86Piece137Input_sector0)]
def node86Piece137Output_sector0 : RawPoly ℕ := reflectPoly node86Piece66Output_sector1

def node86Piece137Output_sector1 : RawPoly ℕ := reflectPoly node86Piece66Output_sector0

def node86Piece137Output : SectorVector := [(0, node86Piece137Output_sector0), (2, node86Piece137Output_sector1)]

theorem node86Piece137_check : (reflectVector node86Piece66Output).reverse = node86Piece137Output := by rfl

theorem node86Piece137_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece137Input) = evaluate node86Piece137Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece66_value (by decide +kernel) node86Piece137_check

def node86Piece138Input_sector0 : RawPoly ℕ := [(160, [3, 3, 3, 3])]

def node86Piece138Input : SectorVector := [(1, node86Piece138Input_sector0)]
def node86Piece138Output_sector0 : RawPoly ℕ := reflectPoly node86Piece67Output_sector1

def node86Piece138Output_sector1 : RawPoly ℕ := reflectPoly node86Piece67Output_sector0

def node86Piece138Output : SectorVector := [(0, node86Piece138Output_sector0), (2, node86Piece138Output_sector1)]

theorem node86Piece138_check : (reflectVector node86Piece67Output).reverse = node86Piece138Output := by rfl

theorem node86Piece138_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece138Input) = evaluate node86Piece138Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece67_value (by decide +kernel) node86Piece138_check

def node86Piece139Input_sector0 : RawPoly ℕ := [(-3680, [3, 9])]

def node86Piece139Input : SectorVector := [(1, node86Piece139Input_sector0)]
def node86Piece139Output_sector0 : RawPoly ℕ := reflectPoly node86Piece68Output_sector1

def node86Piece139Output_sector1 : RawPoly ℕ := reflectPoly node86Piece68Output_sector0

def node86Piece139Output : SectorVector := [(0, node86Piece139Output_sector0), (2, node86Piece139Output_sector1)]

theorem node86Piece139_check : (reflectVector node86Piece68Output).reverse = node86Piece139Output := by rfl

theorem node86Piece139_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece139Input) = evaluate node86Piece139Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece68_value (by decide +kernel) node86Piece139_check

def node86Piece140Input_sector0 : RawPoly ℕ := [(180, [4, 8])]

def node86Piece140Input : SectorVector := [(1, node86Piece140Input_sector0)]
def node86Piece140Output_sector0 : RawPoly ℕ := reflectPoly node86Piece69Output_sector1

def node86Piece140Output_sector1 : RawPoly ℕ := reflectPoly node86Piece69Output_sector0

def node86Piece140Output : SectorVector := [(0, node86Piece140Output_sector0), (2, node86Piece140Output_sector1)]

theorem node86Piece140_check : (reflectVector node86Piece69Output).reverse = node86Piece140Output := by rfl

theorem node86Piece140_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece140Input) = evaluate node86Piece140Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece69_value (by decide +kernel) node86Piece140_check

def node86Piece141Input_sector0 : RawPoly ℕ := [(864, [5, 7])]

def node86Piece141Input : SectorVector := [(1, node86Piece141Input_sector0)]
def node86Piece141Output_sector0 : RawPoly ℕ := reflectPoly node86Piece70Output_sector1

def node86Piece141Output_sector1 : RawPoly ℕ := reflectPoly node86Piece70Output_sector0

def node86Piece141Output : SectorVector := [(0, node86Piece141Output_sector0), (2, node86Piece141Output_sector1)]

theorem node86Piece141_check : (reflectVector node86Piece70Output).reverse = node86Piece141Output := by rfl

theorem node86Piece141_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece141Input) = evaluate node86Piece141Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece70_value (by decide +kernel) node86Piece141_check

end VOA.Classification.COne.OrbC2h
