import VOA.Classification.COne.OrbC2hReflection
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hBucketSectors
import VOA.Classification.COne.OrbC2hStateBatch98_1
import VOA.Classification.COne.OrbC2hStateNode18
import VOA.Classification.COne.OrbC2hBounded
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def node98Piece48Input_sector0 : RawPoly ℕ := [(1660, [1, 1, 1, 1, 2, 3])]

def node98Piece48Input : SectorVector := [(1, node98Piece48Input_sector0)]
def node98Piece48Output_sector0 : RawPoly ℕ := reflectPoly node98Piece18Output_sector1

def node98Piece48Output_sector1 : RawPoly ℕ := reflectPoly node98Piece18Output_sector0

def node98Piece48Output : SectorVector := [(0, node98Piece48Output_sector0), (2, node98Piece48Output_sector1)]

theorem node98Piece48_check : (reflectVector node98Piece18Output).reverse = node98Piece48Output := by rfl

theorem node98Piece48_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-6)
    (evaluate node98Piece48Input) = evaluate node98Piece48Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-6) _ _ _ _
    node98Piece18_value (by decide +kernel) node98Piece48_check

def node98Piece49Input_sector0 : RawPoly ℕ := [(1150, [1, 1, 1, 2, 2, 2])]

def node98Piece49Input : SectorVector := [(1, node98Piece49Input_sector0)]
def node98Piece49Output_sector0 : RawPoly ℕ := reflectPoly node98Piece19Output_sector1

def node98Piece49Output_sector1 : RawPoly ℕ := reflectPoly node98Piece19Output_sector0

def node98Piece49Output : SectorVector := [(0, node98Piece49Output_sector0), (2, node98Piece49Output_sector1)]

theorem node98Piece49_check : (reflectVector node98Piece19Output).reverse = node98Piece49Output := by rfl

theorem node98Piece49_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-6)
    (evaluate node98Piece49Input) = evaluate node98Piece49Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-6) _ _ _ _
    node98Piece19_value (by decide +kernel) node98Piece49_check

def node98Piece50Input_sector0 : RawPoly ℕ := [(-2600, [1, 1, 1, 6])]

def node98Piece50Input : SectorVector := [(1, node98Piece50Input_sector0)]
def node98Piece50Output_sector0 : RawPoly ℕ := reflectPoly node98Piece20Output_sector1

def node98Piece50Output_sector1 : RawPoly ℕ := reflectPoly node98Piece20Output_sector0

def node98Piece50Output : SectorVector := [(0, node98Piece50Output_sector0), (2, node98Piece50Output_sector1)]

theorem node98Piece50_check : (reflectVector node98Piece20Output).reverse = node98Piece50Output := by rfl

theorem node98Piece50_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-6)
    (evaluate node98Piece50Input) = evaluate node98Piece50Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-6) _ _ _ _
    node98Piece20_value (by decide +kernel) node98Piece50_check

def node98Piece51Input_sector0 : RawPoly ℕ := [(-936, [1, 1, 2, 5])]

def node98Piece51Input : SectorVector := [(1, node98Piece51Input_sector0)]
def node98Piece51Output_sector0 : RawPoly ℕ := reflectPoly node98Piece21Output_sector1

def node98Piece51Output_sector1 : RawPoly ℕ := reflectPoly node98Piece21Output_sector0

def node98Piece51Output : SectorVector := [(0, node98Piece51Output_sector0), (2, node98Piece51Output_sector1)]

theorem node98Piece51_check : (reflectVector node98Piece21Output).reverse = node98Piece51Output := by rfl

theorem node98Piece51_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-6)
    (evaluate node98Piece51Input) = evaluate node98Piece51Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-6) _ _ _ _
    node98Piece21_value (by decide +kernel) node98Piece51_check

def node98Piece52Input_sector0 : RawPoly ℕ := [(-1380, [1, 1, 3, 4])]

def node98Piece52Input : SectorVector := [(1, node98Piece52Input_sector0)]
def node98Piece52Output_sector0 : RawPoly ℕ := reflectPoly node98Piece22Output_sector1

def node98Piece52Output_sector1 : RawPoly ℕ := reflectPoly node98Piece22Output_sector0

def node98Piece52Output : SectorVector := [(0, node98Piece52Output_sector0), (2, node98Piece52Output_sector1)]

theorem node98Piece52_check : (reflectVector node98Piece22Output).reverse = node98Piece52Output := by rfl

theorem node98Piece52_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-6)
    (evaluate node98Piece52Input) = evaluate node98Piece52Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-6) _ _ _ _
    node98Piece22_value (by decide +kernel) node98Piece52_check

def node98Piece53Input_sector0 : RawPoly ℕ := [(-1935, [1, 2, 2, 4])]

def node98Piece53Input : SectorVector := [(1, node98Piece53Input_sector0)]
def node98Piece53Output_sector0 : RawPoly ℕ := reflectPoly node98Piece23Output_sector1

def node98Piece53Output_sector1 : RawPoly ℕ := reflectPoly node98Piece23Output_sector0

def node98Piece53Output : SectorVector := [(0, node98Piece53Output_sector0), (2, node98Piece53Output_sector1)]

theorem node98Piece53_check : (reflectVector node98Piece23Output).reverse = node98Piece53Output := by rfl

theorem node98Piece53_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-6)
    (evaluate node98Piece53Input) = evaluate node98Piece53Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-6) _ _ _ _
    node98Piece23_value (by decide +kernel) node98Piece53_check

def node98Piece54Input_sector0 : RawPoly ℕ := [(-1000, [1, 2, 3, 3])]

def node98Piece54Input : SectorVector := [(1, node98Piece54Input_sector0)]
def node98Piece54Output_sector0 : RawPoly ℕ := reflectPoly node98Piece24Output_sector1

def node98Piece54Output_sector1 : RawPoly ℕ := reflectPoly node98Piece24Output_sector0

def node98Piece54Output : SectorVector := [(0, node98Piece54Output_sector0), (2, node98Piece54Output_sector1)]

theorem node98Piece54_check : (reflectVector node98Piece24Output).reverse = node98Piece54Output := by rfl

theorem node98Piece54_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-6)
    (evaluate node98Piece54Input) = evaluate node98Piece54Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-6) _ _ _ _
    node98Piece24_value (by decide +kernel) node98Piece54_check

def node98Piece55Input_sector0 : RawPoly ℕ := [(-24120, [1, 8])]

def node98Piece55Input : SectorVector := [(1, node98Piece55Input_sector0)]
def node98Piece55Output_sector0 : RawPoly ℕ := reflectPoly node98Piece25Output_sector1

def node98Piece55Output_sector1 : RawPoly ℕ := reflectPoly node98Piece25Output_sector0

def node98Piece55Output : SectorVector := [(0, node98Piece55Output_sector0), (2, node98Piece55Output_sector1)]

theorem node98Piece55_check : (reflectVector node98Piece25Output).reverse = node98Piece55Output := by rfl

theorem node98Piece55_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-6)
    (evaluate node98Piece55Input) = evaluate node98Piece55Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-6) _ _ _ _
    node98Piece25_value (by decide +kernel) node98Piece55_check

def node98Piece56Input_sector0 : RawPoly ℕ := [(430, [2, 2, 2, 3])]

def node98Piece56Input : SectorVector := [(1, node98Piece56Input_sector0)]
def node98Piece56Output_sector0 : RawPoly ℕ := reflectPoly node98Piece26Output_sector1

def node98Piece56Output_sector1 : RawPoly ℕ := reflectPoly node98Piece26Output_sector0

def node98Piece56Output : SectorVector := [(0, node98Piece56Output_sector0), (2, node98Piece56Output_sector1)]

theorem node98Piece56_check : (reflectVector node98Piece26Output).reverse = node98Piece56Output := by rfl

theorem node98Piece56_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-6)
    (evaluate node98Piece56Input) = evaluate node98Piece56Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-6) _ _ _ _
    node98Piece26_value (by decide +kernel) node98Piece56_check

def node98Piece57Input_sector0 : RawPoly ℕ := [(-6840, [2, 7])]

def node98Piece57Input : SectorVector := [(1, node98Piece57Input_sector0)]
def node98Piece57Output_sector0 : RawPoly ℕ := reflectPoly node98Piece27Output_sector1

def node98Piece57Output_sector1 : RawPoly ℕ := reflectPoly node98Piece27Output_sector0

def node98Piece57Output : SectorVector := [(0, node98Piece57Output_sector0), (2, node98Piece57Output_sector1)]

theorem node98Piece57_check : (reflectVector node98Piece27Output).reverse = node98Piece57Output := by rfl

theorem node98Piece57_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-6)
    (evaluate node98Piece57Input) = evaluate node98Piece57Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-6) _ _ _ _
    node98Piece27_value (by decide +kernel) node98Piece57_check

def node98Piece58Input_sector0 : RawPoly ℕ := [(-1160, [3, 6])]

def node98Piece58Input : SectorVector := [(1, node98Piece58Input_sector0)]
def node98Piece58Output_sector0 : RawPoly ℕ := reflectPoly node98Piece28Output_sector1

def node98Piece58Output_sector1 : RawPoly ℕ := reflectPoly node98Piece28Output_sector0

def node98Piece58Output : SectorVector := [(0, node98Piece58Output_sector0), (2, node98Piece58Output_sector1)]

theorem node98Piece58_check : (reflectVector node98Piece28Output).reverse = node98Piece58Output := by rfl

theorem node98Piece58_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-6)
    (evaluate node98Piece58Input) = evaluate node98Piece58Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-6) _ _ _ _
    node98Piece28_value (by decide +kernel) node98Piece58_check

def node98Piece59Input_sector0 : RawPoly ℕ := [(900, [4, 5])]

def node98Piece59Input : SectorVector := [(1, node98Piece59Input_sector0)]
def node98Piece59Output_sector0 : RawPoly ℕ := reflectPoly node98Piece29Output_sector1

def node98Piece59Output_sector1 : RawPoly ℕ := reflectPoly node98Piece29Output_sector0

def node98Piece59Output : SectorVector := [(0, node98Piece59Output_sector0), (2, node98Piece59Output_sector1)]

theorem node98Piece59_check : (reflectVector node98Piece29Output).reverse = node98Piece59Output := by rfl

theorem node98Piece59_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-6)
    (evaluate node98Piece59Input) = evaluate node98Piece59Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-6) _ _ _ _
    node98Piece29_value (by decide +kernel) node98Piece59_check

end VOA.Classification.COne.OrbC2h
