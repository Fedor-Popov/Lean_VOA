import VOA.Classification.COne.OrbC2hStateBatch86_3
import VOA.Classification.COne.OrbC2hStateBatch86_2
import VOA.Classification.COne.OrbC2hReflection
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hBucketSectors
import VOA.Classification.COne.OrbC2hStateBatch86_5
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

def node86Piece112Input_sector0 : RawPoly ℕ := [(80, [1, 1, 1, 1, 2, 2, 2, 2])]

def node86Piece112Input : SectorVector := [(1, node86Piece112Input_sector0)]
def node86Piece112Output_sector0 : RawPoly ℕ := reflectPoly node86Piece41Output_sector1

def node86Piece112Output_sector1 : RawPoly ℕ := reflectPoly node86Piece41Output_sector0

def node86Piece112Output : SectorVector := [(0, node86Piece112Output_sector0), (2, node86Piece112Output_sector1)]

theorem node86Piece112_check : (reflectVector node86Piece41Output).reverse = node86Piece112Output := by rfl

theorem node86Piece112_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece112Input) = evaluate node86Piece112Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece41_value (by decide +kernel) node86Piece112_check

def node86Piece113Input_sector0 : RawPoly ℕ := [(2240, [1, 1, 1, 1, 2, 6])]

def node86Piece113Input : SectorVector := [(1, node86Piece113Input_sector0)]
def node86Piece113Output_sector0 : RawPoly ℕ := reflectPoly node86Piece42Output_sector1

def node86Piece113Output_sector1 : RawPoly ℕ := reflectPoly node86Piece42Output_sector0

def node86Piece113Output : SectorVector := [(0, node86Piece113Output_sector0), (2, node86Piece113Output_sector1)]

theorem node86Piece113_check : (reflectVector node86Piece42Output).reverse = node86Piece113Output := by rfl

theorem node86Piece113_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece113Input) = evaluate node86Piece113Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece42_value (by decide +kernel) node86Piece113_check

def node86Piece114Input_sector0 : RawPoly ℕ := [(-960, [1, 1, 1, 1, 3, 5])]

def node86Piece114Input : SectorVector := [(1, node86Piece114Input_sector0)]
def node86Piece114Output_sector0 : RawPoly ℕ := reflectPoly node86Piece43Output_sector1

def node86Piece114Output_sector1 : RawPoly ℕ := reflectPoly node86Piece43Output_sector0

def node86Piece114Output : SectorVector := [(0, node86Piece114Output_sector0), (2, node86Piece114Output_sector1)]

theorem node86Piece114_check : (reflectVector node86Piece43Output).reverse = node86Piece114Output := by rfl

theorem node86Piece114_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece114Input) = evaluate node86Piece114Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece43_value (by decide +kernel) node86Piece114_check

def node86Piece115Input_sector0 : RawPoly ℕ := [(120, [1, 1, 1, 1, 4, 4])]

def node86Piece115Input : SectorVector := [(1, node86Piece115Input_sector0)]
def node86Piece115Output_sector0 : RawPoly ℕ := reflectPoly node86Piece44Output_sector1

def node86Piece115Output_sector1 : RawPoly ℕ := reflectPoly node86Piece44Output_sector0

def node86Piece115Output : SectorVector := [(0, node86Piece115Output_sector0), (2, node86Piece115Output_sector1)]

theorem node86Piece115_check : (reflectVector node86Piece44Output).reverse = node86Piece115Output := by rfl

theorem node86Piece115_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece115Input) = evaluate node86Piece115Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece44_value (by decide +kernel) node86Piece115_check

def node86Piece116Input_sector0 : RawPoly ℕ := [(3120, [1, 1, 1, 2, 2, 5])]

def node86Piece116Input : SectorVector := [(1, node86Piece116Input_sector0)]
def node86Piece116Output_sector0 : RawPoly ℕ := reflectPoly node86Piece45Output_sector1

def node86Piece116Output_sector1 : RawPoly ℕ := reflectPoly node86Piece45Output_sector0

def node86Piece116Output : SectorVector := [(0, node86Piece116Output_sector0), (2, node86Piece116Output_sector1)]

theorem node86Piece116_check : (reflectVector node86Piece45Output).reverse = node86Piece116Output := by rfl

theorem node86Piece116_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece116Input) = evaluate node86Piece116Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece45_value (by decide +kernel) node86Piece116_check

def node86Piece117Input_sector0 : RawPoly ℕ := [(3040, [1, 1, 1, 2, 3, 4])]

def node86Piece117Input : SectorVector := [(1, node86Piece117Input_sector0)]
def node86Piece117Output_sector0 : RawPoly ℕ := reflectPoly node86Piece46Output_sector1

def node86Piece117Output_sector1 : RawPoly ℕ := reflectPoly node86Piece46Output_sector0

def node86Piece117Output : SectorVector := [(0, node86Piece117Output_sector0), (2, node86Piece117Output_sector1)]

theorem node86Piece117_check : (reflectVector node86Piece46Output).reverse = node86Piece117Output := by rfl

theorem node86Piece117_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece117Input) = evaluate node86Piece117Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece46_value (by decide +kernel) node86Piece117_check

def node86Piece118Input_sector0 : RawPoly ℕ := [(-800, [1, 1, 1, 3, 3, 3])]

def node86Piece118Input : SectorVector := [(1, node86Piece118Input_sector0)]
def node86Piece118Output_sector0 : RawPoly ℕ := reflectPoly node86Piece47Output_sector1

def node86Piece118Output_sector1 : RawPoly ℕ := reflectPoly node86Piece47Output_sector0

def node86Piece118Output : SectorVector := [(0, node86Piece118Output_sector0), (2, node86Piece118Output_sector1)]

theorem node86Piece118_check : (reflectVector node86Piece47Output).reverse = node86Piece118Output := by rfl

theorem node86Piece118_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece118Input) = evaluate node86Piece118Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece47_value (by decide +kernel) node86Piece118_check

def node86Piece119Input_sector0 : RawPoly ℕ := [(-5120, [1, 1, 1, 9])]

def node86Piece119Input : SectorVector := [(1, node86Piece119Input_sector0)]
def node86Piece119Output_sector0 : RawPoly ℕ := reflectPoly node86Piece48Output_sector1

def node86Piece119Output_sector1 : RawPoly ℕ := reflectPoly node86Piece48Output_sector0

def node86Piece119Output : SectorVector := [(0, node86Piece119Output_sector0), (2, node86Piece119Output_sector1)]

theorem node86Piece119_check : (reflectVector node86Piece48Output).reverse = node86Piece119Output := by rfl

theorem node86Piece119_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece119Input) = evaluate node86Piece119Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece48_value (by decide +kernel) node86Piece119_check

def node86Piece120Input_sector0 : RawPoly ℕ := [(-600, [1, 1, 2, 2, 2, 4])]

def node86Piece120Input : SectorVector := [(1, node86Piece120Input_sector0)]
def node86Piece120Output_sector0 : RawPoly ℕ := reflectPoly node86Piece49Output_sector1

def node86Piece120Output_sector1 : RawPoly ℕ := reflectPoly node86Piece49Output_sector0

def node86Piece120Output : SectorVector := [(0, node86Piece120Output_sector0), (2, node86Piece120Output_sector1)]

theorem node86Piece120_check : (reflectVector node86Piece49Output).reverse = node86Piece120Output := by rfl

theorem node86Piece120_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece120Input) = evaluate node86Piece120Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece49_value (by decide +kernel) node86Piece120_check

def node86Piece121Input_sector0 : RawPoly ℕ := [(-720, [1, 1, 2, 2, 3, 3])]

def node86Piece121Input : SectorVector := [(1, node86Piece121Input_sector0)]
def node86Piece121Output_sector0 : RawPoly ℕ := reflectPoly node86Piece50Output_sector1

def node86Piece121Output_sector1 : RawPoly ℕ := reflectPoly node86Piece50Output_sector0

def node86Piece121Output : SectorVector := [(0, node86Piece121Output_sector0), (2, node86Piece121Output_sector1)]

theorem node86Piece121_check : (reflectVector node86Piece50Output).reverse = node86Piece121Output := by rfl

theorem node86Piece121_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece121Input) = evaluate node86Piece121Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece50_value (by decide +kernel) node86Piece121_check

def node86Piece122Input_sector0 : RawPoly ℕ := [(-3240, [1, 1, 2, 8])]

def node86Piece122Input : SectorVector := [(1, node86Piece122Input_sector0)]
def node86Piece122Output_sector0 : RawPoly ℕ := reflectPoly node86Piece51Output_sector1

def node86Piece122Output_sector1 : RawPoly ℕ := reflectPoly node86Piece51Output_sector0

def node86Piece122Output : SectorVector := [(0, node86Piece122Output_sector0), (2, node86Piece122Output_sector1)]

theorem node86Piece122_check : (reflectVector node86Piece51Output).reverse = node86Piece122Output := by rfl

theorem node86Piece122_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece122Input) = evaluate node86Piece122Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece51_value (by decide +kernel) node86Piece122_check

def node86Piece123Input_sector0 : RawPoly ℕ := [(-1920, [1, 1, 3, 7])]

def node86Piece123Input : SectorVector := [(1, node86Piece123Input_sector0)]
def node86Piece123Output_sector0 : RawPoly ℕ := reflectPoly node86Piece52Output_sector1

def node86Piece123Output_sector1 : RawPoly ℕ := reflectPoly node86Piece52Output_sector0

def node86Piece123Output : SectorVector := [(0, node86Piece123Output_sector0), (2, node86Piece123Output_sector1)]

theorem node86Piece123_check : (reflectVector node86Piece52Output).reverse = node86Piece123Output := by rfl

theorem node86Piece123_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece123Input) = evaluate node86Piece123Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece52_value (by decide +kernel) node86Piece123_check

def node86Piece124Input_sector0 : RawPoly ℕ := [(2640, [1, 1, 4, 6])]

def node86Piece124Input : SectorVector := [(1, node86Piece124Input_sector0)]
def node86Piece124Output_sector0 : RawPoly ℕ := reflectPoly node86Piece53Output_sector1

def node86Piece124Output_sector1 : RawPoly ℕ := reflectPoly node86Piece53Output_sector0

def node86Piece124Output : SectorVector := [(0, node86Piece124Output_sector0), (2, node86Piece124Output_sector1)]

theorem node86Piece124_check : (reflectVector node86Piece53Output).reverse = node86Piece124Output := by rfl

theorem node86Piece124_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece124Input) = evaluate node86Piece124Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece53_value (by decide +kernel) node86Piece124_check

def node86Piece125Input_sector0 : RawPoly ℕ := [(-576, [1, 1, 5, 5])]

def node86Piece125Input : SectorVector := [(1, node86Piece125Input_sector0)]
def node86Piece125Output_sector0 : RawPoly ℕ := reflectPoly node86Piece54Output_sector1

def node86Piece125Output_sector1 : RawPoly ℕ := reflectPoly node86Piece54Output_sector0

def node86Piece125Output : SectorVector := [(0, node86Piece125Output_sector0), (2, node86Piece125Output_sector1)]

theorem node86Piece125_check : (reflectVector node86Piece54Output).reverse = node86Piece125Output := by rfl

theorem node86Piece125_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece125Input) = evaluate node86Piece125Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece54_value (by decide +kernel) node86Piece125_check

def node86Piece126Input_sector0 : RawPoly ℕ := [(-640, [1, 2, 2, 2, 2, 3])]

def node86Piece126Input : SectorVector := [(1, node86Piece126Input_sector0)]
def node86Piece126Output_sector0 : RawPoly ℕ := reflectPoly node86Piece55Output_sector1

def node86Piece126Output_sector1 : RawPoly ℕ := reflectPoly node86Piece55Output_sector0

def node86Piece126Output : SectorVector := [(0, node86Piece126Output_sector0), (2, node86Piece126Output_sector1)]

theorem node86Piece126_check : (reflectVector node86Piece55Output).reverse = node86Piece126Output := by rfl

theorem node86Piece126_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece126Input) = evaluate node86Piece126Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece55_value (by decide +kernel) node86Piece126_check

def node86Piece127Input_sector0 : RawPoly ℕ := [(-1800, [1, 2, 2, 7])]

def node86Piece127Input : SectorVector := [(1, node86Piece127Input_sector0)]
def node86Piece127Output_sector0 : RawPoly ℕ := reflectPoly node86Piece56Output_sector1

def node86Piece127Output_sector1 : RawPoly ℕ := reflectPoly node86Piece56Output_sector0

def node86Piece127Output : SectorVector := [(0, node86Piece127Output_sector0), (2, node86Piece127Output_sector1)]

theorem node86Piece127_check : (reflectVector node86Piece56Output).reverse = node86Piece127Output := by rfl

theorem node86Piece127_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece127Input) = evaluate node86Piece127Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece56_value (by decide +kernel) node86Piece127_check

end VOA.Classification.COne.OrbC2h
