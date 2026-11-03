import VOA.Classification.COne.OrbC2hStateBatch94_0
import VOA.Classification.COne.OrbC2hReflection
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hBucketSectors
import VOA.Classification.COne.OrbC2hStateBatch94_1
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

def node94Piece48Input_sector0 : RawPoly ℕ := [(-45, [0, 1, 1, 2, 2, 4])]

def node94Piece48Input : SectorVector := [(1, node94Piece48Input_sector0)]
def node94Piece48Output_sector0 : RawPoly ℕ := reflectPoly node94Piece7Output_sector1

def node94Piece48Output_sector1 : RawPoly ℕ := reflectPoly node94Piece7Output_sector0

def node94Piece48Output : SectorVector := [(0, node94Piece48Output_sector0), (2, node94Piece48Output_sector1)]

theorem node94Piece48_check : (reflectVector node94Piece7Output).reverse = node94Piece48Output := by rfl

theorem node94Piece48_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece48Input) = evaluate node94Piece48Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece7_value (by decide +kernel) node94Piece48_check

def node94Piece49Input_sector0 : RawPoly ℕ := [(-1240, [0, 1, 1, 2, 3, 3])]

def node94Piece49Input : SectorVector := [(1, node94Piece49Input_sector0)]
def node94Piece49Output_sector0 : RawPoly ℕ := reflectPoly node94Piece8Output_sector1

def node94Piece49Output_sector1 : RawPoly ℕ := reflectPoly node94Piece8Output_sector0

def node94Piece49Output : SectorVector := [(0, node94Piece49Output_sector0), (2, node94Piece49Output_sector1)]

theorem node94Piece49_check : (reflectVector node94Piece8Output).reverse = node94Piece49Output := by rfl

theorem node94Piece49_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece49Input) = evaluate node94Piece49Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece8_value (by decide +kernel) node94Piece49_check

def node94Piece50Input_sector0 : RawPoly ℕ := [(4500, [0, 1, 1, 8])]

def node94Piece50Input : SectorVector := [(1, node94Piece50Input_sector0)]
def node94Piece50Output_sector0 : RawPoly ℕ := reflectPoly node94Piece9Output_sector1

def node94Piece50Output_sector1 : RawPoly ℕ := reflectPoly node94Piece9Output_sector0

def node94Piece50Output : SectorVector := [(0, node94Piece50Output_sector0), (2, node94Piece50Output_sector1)]

theorem node94Piece50_check : (reflectVector node94Piece9Output).reverse = node94Piece50Output := by rfl

theorem node94Piece50_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece50Input) = evaluate node94Piece50Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece9_value (by decide +kernel) node94Piece50_check

def node94Piece51Input_sector0 : RawPoly ℕ := [(-1130, [0, 1, 2, 2, 2, 3])]

def node94Piece51Input : SectorVector := [(1, node94Piece51Input_sector0)]
def node94Piece51Output_sector0 : RawPoly ℕ := reflectPoly node94Piece10Output_sector1

def node94Piece51Output_sector1 : RawPoly ℕ := reflectPoly node94Piece10Output_sector0

def node94Piece51Output : SectorVector := [(0, node94Piece51Output_sector0), (2, node94Piece51Output_sector1)]

theorem node94Piece51_check : (reflectVector node94Piece10Output).reverse = node94Piece51Output := by rfl

theorem node94Piece51_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece51Input) = evaluate node94Piece51Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece10_value (by decide +kernel) node94Piece51_check

def node94Piece52Input_sector0 : RawPoly ℕ := [(2160, [0, 1, 2, 7])]

def node94Piece52Input : SectorVector := [(1, node94Piece52Input_sector0)]
def node94Piece52Output_sector0 : RawPoly ℕ := reflectPoly node94Piece11Output_sector1

def node94Piece52Output_sector1 : RawPoly ℕ := reflectPoly node94Piece11Output_sector0

def node94Piece52Output : SectorVector := [(0, node94Piece52Output_sector0), (2, node94Piece52Output_sector1)]

theorem node94Piece52_check : (reflectVector node94Piece11Output).reverse = node94Piece52Output := by rfl

theorem node94Piece52_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece52Input) = evaluate node94Piece52Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece11_value (by decide +kernel) node94Piece52_check

def node94Piece53Input_sector0 : RawPoly ℕ := [(-80, [0, 1, 3, 6])]

def node94Piece53Input : SectorVector := [(1, node94Piece53Input_sector0)]
def node94Piece53Output_sector0 : RawPoly ℕ := reflectPoly node94Piece12Output_sector1

def node94Piece53Output_sector1 : RawPoly ℕ := reflectPoly node94Piece12Output_sector0

def node94Piece53Output : SectorVector := [(0, node94Piece53Output_sector0), (2, node94Piece53Output_sector1)]

theorem node94Piece53_check : (reflectVector node94Piece12Output).reverse = node94Piece53Output := by rfl

theorem node94Piece53_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece53Input) = evaluate node94Piece53Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece12_value (by decide +kernel) node94Piece53_check

def node94Piece54Input_sector0 : RawPoly ℕ := [(360, [0, 1, 4, 5])]

def node94Piece54Input : SectorVector := [(1, node94Piece54Input_sector0)]
def node94Piece54Output_sector0 : RawPoly ℕ := reflectPoly node94Piece13Output_sector1

def node94Piece54Output_sector1 : RawPoly ℕ := reflectPoly node94Piece13Output_sector0

def node94Piece54Output : SectorVector := [(0, node94Piece54Output_sector0), (2, node94Piece54Output_sector1)]

theorem node94Piece54_check : (reflectVector node94Piece13Output).reverse = node94Piece54Output := by rfl

theorem node94Piece54_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece54Input) = evaluate node94Piece54Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece13_value (by decide +kernel) node94Piece54_check

def node94Piece55Input_sector0 : RawPoly ℕ := [(-30, [0, 2, 2, 2, 2, 2])]

def node94Piece55Input : SectorVector := [(1, node94Piece55Input_sector0)]
def node94Piece55Output_sector0 : RawPoly ℕ := reflectPoly node94Piece14Output_sector1

def node94Piece55Output_sector1 : RawPoly ℕ := reflectPoly node94Piece14Output_sector0

def node94Piece55Output : SectorVector := [(0, node94Piece55Output_sector0), (2, node94Piece55Output_sector1)]

theorem node94Piece55_check : (reflectVector node94Piece14Output).reverse = node94Piece55Output := by rfl

theorem node94Piece55_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece55Input) = evaluate node94Piece55Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece14_value (by decide +kernel) node94Piece55_check

def node94Piece56Input_sector0 : RawPoly ℕ := [(60, [0, 2, 2, 6])]

def node94Piece56Input : SectorVector := [(1, node94Piece56Input_sector0)]
def node94Piece56Output_sector0 : RawPoly ℕ := reflectPoly node94Piece15Output_sector1

def node94Piece56Output_sector1 : RawPoly ℕ := reflectPoly node94Piece15Output_sector0

def node94Piece56Output : SectorVector := [(0, node94Piece56Output_sector0), (2, node94Piece56Output_sector1)]

theorem node94Piece56_check : (reflectVector node94Piece15Output).reverse = node94Piece56Output := by rfl

theorem node94Piece56_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece56Input) = evaluate node94Piece56Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece15_value (by decide +kernel) node94Piece56_check

def node94Piece57Input_sector0 : RawPoly ℕ := [(240, [0, 2, 3, 5])]

def node94Piece57Input : SectorVector := [(1, node94Piece57Input_sector0)]
def node94Piece57Output_sector0 : RawPoly ℕ := reflectPoly node94Piece16Output_sector1

def node94Piece57Output_sector1 : RawPoly ℕ := reflectPoly node94Piece16Output_sector0

def node94Piece57Output : SectorVector := [(0, node94Piece57Output_sector0), (2, node94Piece57Output_sector1)]

theorem node94Piece57_check : (reflectVector node94Piece16Output).reverse = node94Piece57Output := by rfl

theorem node94Piece57_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece57Input) = evaluate node94Piece57Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece16_value (by decide +kernel) node94Piece57_check

def node94Piece58Input_sector0 : RawPoly ℕ := [(720, [0, 2, 4, 4])]

def node94Piece58Input : SectorVector := [(1, node94Piece58Input_sector0)]
def node94Piece58Output_sector0 : RawPoly ℕ := reflectPoly node94Piece17Output_sector1

def node94Piece58Output_sector1 : RawPoly ℕ := reflectPoly node94Piece17Output_sector0

def node94Piece58Output : SectorVector := [(0, node94Piece58Output_sector0), (2, node94Piece58Output_sector1)]

theorem node94Piece58_check : (reflectVector node94Piece17Output).reverse = node94Piece58Output := by rfl

theorem node94Piece58_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece58Input) = evaluate node94Piece58Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece17_value (by decide +kernel) node94Piece58_check

def node94Piece59Input_sector0 : RawPoly ℕ := [(720, [0, 3, 3, 4])]

def node94Piece59Input : SectorVector := [(1, node94Piece59Input_sector0)]
def node94Piece59Output_sector0 : RawPoly ℕ := reflectPoly node94Piece18Output_sector1

def node94Piece59Output_sector1 : RawPoly ℕ := reflectPoly node94Piece18Output_sector0

def node94Piece59Output : SectorVector := [(0, node94Piece59Output_sector0), (2, node94Piece59Output_sector1)]

theorem node94Piece59_check : (reflectVector node94Piece18Output).reverse = node94Piece59Output := by rfl

theorem node94Piece59_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece59Input) = evaluate node94Piece59Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece18_value (by decide +kernel) node94Piece59_check

def node94Piece60Input_sector0 : RawPoly ℕ := [(9720, [0, 10])]

def node94Piece60Input : SectorVector := [(1, node94Piece60Input_sector0)]
def node94Piece60Output_sector0 : RawPoly ℕ := reflectPoly node94Piece19Output_sector1

def node94Piece60Output_sector1 : RawPoly ℕ := reflectPoly node94Piece19Output_sector0

def node94Piece60Output : SectorVector := [(0, node94Piece60Output_sector0), (2, node94Piece60Output_sector1)]

theorem node94Piece60_check : (reflectVector node94Piece19Output).reverse = node94Piece60Output := by rfl

theorem node94Piece60_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece60Input) = evaluate node94Piece60Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece19_value (by decide +kernel) node94Piece60_check

def node94Piece61Input_sector0 : RawPoly ℕ := [(-96, [1, 1, 1, 1, 1, 1, 1, 3])]

def node94Piece61Input : SectorVector := [(1, node94Piece61Input_sector0)]
def node94Piece61Output_sector0 : RawPoly ℕ := reflectPoly node94Piece20Output_sector1

def node94Piece61Output_sector1 : RawPoly ℕ := reflectPoly node94Piece20Output_sector0

def node94Piece61Output : SectorVector := [(0, node94Piece61Output_sector0), (2, node94Piece61Output_sector1)]

theorem node94Piece61_check : (reflectVector node94Piece20Output).reverse = node94Piece61Output := by rfl

theorem node94Piece61_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece61Input) = evaluate node94Piece61Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece20_value (by decide +kernel) node94Piece61_check

def node94Piece62Input_sector0 : RawPoly ℕ := [(-16, [1, 1, 1, 1, 1, 1, 2, 2])]

def node94Piece62Input : SectorVector := [(1, node94Piece62Input_sector0)]
def node94Piece62Output_sector0 : RawPoly ℕ := reflectPoly node94Piece21Output_sector1

def node94Piece62Output_sector1 : RawPoly ℕ := reflectPoly node94Piece21Output_sector0

def node94Piece62Output : SectorVector := [(0, node94Piece62Output_sector0), (2, node94Piece62Output_sector1)]

theorem node94Piece62_check : (reflectVector node94Piece21Output).reverse = node94Piece62Output := by rfl

theorem node94Piece62_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece62Input) = evaluate node94Piece62Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece21_value (by decide +kernel) node94Piece62_check

def node94Piece63Input_sector0 : RawPoly ℕ := [(-528, [1, 1, 1, 1, 1, 5])]

def node94Piece63Input : SectorVector := [(1, node94Piece63Input_sector0)]
def node94Piece63Output_sector0 : RawPoly ℕ := reflectPoly node94Piece22Output_sector1

def node94Piece63Output_sector1 : RawPoly ℕ := reflectPoly node94Piece22Output_sector0

def node94Piece63Output : SectorVector := [(0, node94Piece63Output_sector0), (2, node94Piece63Output_sector1)]

theorem node94Piece63_check : (reflectVector node94Piece22Output).reverse = node94Piece63Output := by rfl

theorem node94Piece63_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece63Input) = evaluate node94Piece63Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece22_value (by decide +kernel) node94Piece63_check

end VOA.Classification.COne.OrbC2h
