import VOA.Classification.COne.OrbC2hStateBatch90_1
import VOA.Classification.COne.OrbC2hStateBatch90_0
import VOA.Classification.COne.OrbC2hReflection
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hBucketSectors
import VOA.Classification.COne.OrbC2hStateBatch90_2
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

def node90Piece64Input_sector0 : RawPoly ℕ := [(360, [0, 1, 1, 1, 4, 4])]

def node90Piece64Input : SectorVector := [(1, node90Piece64Input_sector0)]
def node90Piece64Output_sector0 : RawPoly ℕ := reflectPoly node90Piece10Output_sector1

def node90Piece64Output_sector1 : RawPoly ℕ := reflectPoly node90Piece10Output_sector0

def node90Piece64Output : SectorVector := [(0, node90Piece64Output_sector0), (2, node90Piece64Output_sector1)]

theorem node90Piece64_check : (reflectVector node90Piece10Output).reverse = node90Piece64Output := by rfl

theorem node90Piece64_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece64Input) = evaluate node90Piece64Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece10_value (by decide +kernel) node90Piece64_check

def node90Piece65Input_sector0 : RawPoly ℕ := [(-396, [0, 1, 1, 2, 2, 5])]

def node90Piece65Input : SectorVector := [(1, node90Piece65Input_sector0)]
def node90Piece65Output_sector0 : RawPoly ℕ := reflectPoly node90Piece11Output_sector1

def node90Piece65Output_sector1 : RawPoly ℕ := reflectPoly node90Piece11Output_sector0

def node90Piece65Output : SectorVector := [(0, node90Piece65Output_sector0), (2, node90Piece65Output_sector1)]

theorem node90Piece65_check : (reflectVector node90Piece11Output).reverse = node90Piece65Output := by rfl

theorem node90Piece65_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece65Input) = evaluate node90Piece65Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece11_value (by decide +kernel) node90Piece65_check

def node90Piece66Input_sector0 : RawPoly ℕ := [(-510, [0, 1, 1, 2, 3, 4])]

def node90Piece66Input : SectorVector := [(1, node90Piece66Input_sector0)]
def node90Piece66Output_sector0 : RawPoly ℕ := reflectPoly node90Piece12Output_sector1

def node90Piece66Output_sector1 : RawPoly ℕ := reflectPoly node90Piece12Output_sector0

def node90Piece66Output : SectorVector := [(0, node90Piece66Output_sector0), (2, node90Piece66Output_sector1)]

theorem node90Piece66_check : (reflectVector node90Piece12Output).reverse = node90Piece66Output := by rfl

theorem node90Piece66_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece66Input) = evaluate node90Piece66Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece12_value (by decide +kernel) node90Piece66_check

def node90Piece67Input_sector0 : RawPoly ℕ := [(-880, [0, 1, 1, 3, 3, 3])]

def node90Piece67Input : SectorVector := [(1, node90Piece67Input_sector0)]
def node90Piece67Output_sector0 : RawPoly ℕ := reflectPoly node90Piece13Output_sector1

def node90Piece67Output_sector1 : RawPoly ℕ := reflectPoly node90Piece13Output_sector0

def node90Piece67Output : SectorVector := [(0, node90Piece67Output_sector0), (2, node90Piece67Output_sector1)]

theorem node90Piece67_check : (reflectVector node90Piece13Output).reverse = node90Piece67Output := by rfl

theorem node90Piece67_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece67Input) = evaluate node90Piece67Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece13_value (by decide +kernel) node90Piece67_check

def node90Piece68Input_sector0 : RawPoly ℕ := [(5280, [0, 1, 1, 9])]

def node90Piece68Input : SectorVector := [(1, node90Piece68Input_sector0)]
def node90Piece68Output_sector0 : RawPoly ℕ := reflectPoly node90Piece14Output_sector1

def node90Piece68Output_sector1 : RawPoly ℕ := reflectPoly node90Piece14Output_sector0

def node90Piece68Output : SectorVector := [(0, node90Piece68Output_sector0), (2, node90Piece68Output_sector1)]

theorem node90Piece68_check : (reflectVector node90Piece14Output).reverse = node90Piece68Output := by rfl

theorem node90Piece68_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece68Input) = evaluate node90Piece68Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece14_value (by decide +kernel) node90Piece68_check

def node90Piece69Input_sector0 : RawPoly ℕ := [(-2325/2, [0, 1, 2, 2, 2, 4])]

def node90Piece69Input : SectorVector := [(1, node90Piece69Input_sector0)]
def node90Piece69Output_sector0 : RawPoly ℕ := reflectPoly node90Piece15Output_sector1

def node90Piece69Output_sector1 : RawPoly ℕ := reflectPoly node90Piece15Output_sector0

def node90Piece69Output : SectorVector := [(0, node90Piece69Output_sector0), (2, node90Piece69Output_sector1)]

theorem node90Piece69_check : (reflectVector node90Piece15Output).reverse = node90Piece69Output := by rfl

theorem node90Piece69_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece69Input) = evaluate node90Piece69Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece15_value (by decide +kernel) node90Piece69_check

def node90Piece70Input_sector0 : RawPoly ℕ := [(-600, [0, 1, 2, 2, 3, 3])]

def node90Piece70Input : SectorVector := [(1, node90Piece70Input_sector0)]
def node90Piece70Output_sector0 : RawPoly ℕ := reflectPoly node90Piece16Output_sector1

def node90Piece70Output_sector1 : RawPoly ℕ := reflectPoly node90Piece16Output_sector0

def node90Piece70Output : SectorVector := [(0, node90Piece70Output_sector0), (2, node90Piece70Output_sector1)]

theorem node90Piece70_check : (reflectVector node90Piece16Output).reverse = node90Piece70Output := by rfl

theorem node90Piece70_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece70Input) = evaluate node90Piece70Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece16_value (by decide +kernel) node90Piece70_check

def node90Piece71Input_sector0 : RawPoly ℕ := [(2790, [0, 1, 2, 8])]

def node90Piece71Input : SectorVector := [(1, node90Piece71Input_sector0)]
def node90Piece71Output_sector0 : RawPoly ℕ := reflectPoly node90Piece17Output_sector1

def node90Piece71Output_sector1 : RawPoly ℕ := reflectPoly node90Piece17Output_sector0

def node90Piece71Output : SectorVector := [(0, node90Piece71Output_sector0), (2, node90Piece71Output_sector1)]

theorem node90Piece71_check : (reflectVector node90Piece17Output).reverse = node90Piece71Output := by rfl

theorem node90Piece71_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece71Input) = evaluate node90Piece71Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece17_value (by decide +kernel) node90Piece71_check

def node90Piece72Input_sector0 : RawPoly ℕ := [(240, [0, 1, 3, 7])]

def node90Piece72Input : SectorVector := [(1, node90Piece72Input_sector0)]
def node90Piece72Output_sector0 : RawPoly ℕ := reflectPoly node90Piece18Output_sector1

def node90Piece72Output_sector1 : RawPoly ℕ := reflectPoly node90Piece18Output_sector0

def node90Piece72Output : SectorVector := [(0, node90Piece72Output_sector0), (2, node90Piece72Output_sector1)]

theorem node90Piece72_check : (reflectVector node90Piece18Output).reverse = node90Piece72Output := by rfl

theorem node90Piece72_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece72Input) = evaluate node90Piece72Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece18_value (by decide +kernel) node90Piece72_check

def node90Piece73Input_sector0 : RawPoly ℕ := [(570, [0, 1, 4, 6])]

def node90Piece73Input : SectorVector := [(1, node90Piece73Input_sector0)]
def node90Piece73Output_sector0 : RawPoly ℕ := reflectPoly node90Piece19Output_sector1

def node90Piece73Output_sector1 : RawPoly ℕ := reflectPoly node90Piece19Output_sector0

def node90Piece73Output : SectorVector := [(0, node90Piece73Output_sector0), (2, node90Piece73Output_sector1)]

theorem node90Piece73_check : (reflectVector node90Piece19Output).reverse = node90Piece73Output := by rfl

theorem node90Piece73_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece73Input) = evaluate node90Piece73Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece19_value (by decide +kernel) node90Piece73_check

def node90Piece74Input_sector0 : RawPoly ℕ := [(-504, [0, 1, 5, 5])]

def node90Piece74Input : SectorVector := [(1, node90Piece74Input_sector0)]
def node90Piece74Output_sector0 : RawPoly ℕ := reflectPoly node90Piece20Output_sector1

def node90Piece74Output_sector1 : RawPoly ℕ := reflectPoly node90Piece20Output_sector0

def node90Piece74Output : SectorVector := [(0, node90Piece74Output_sector0), (2, node90Piece74Output_sector1)]

theorem node90Piece74_check : (reflectVector node90Piece20Output).reverse = node90Piece74Output := by rfl

theorem node90Piece74_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece74Input) = evaluate node90Piece74Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece20_value (by decide +kernel) node90Piece74_check

def node90Piece75Input_sector0 : RawPoly ℕ := [(-10, [0, 2, 2, 2, 2, 3])]

def node90Piece75Input : SectorVector := [(1, node90Piece75Input_sector0)]
def node90Piece75Output_sector0 : RawPoly ℕ := reflectPoly node90Piece21Output_sector1

def node90Piece75Output_sector1 : RawPoly ℕ := reflectPoly node90Piece21Output_sector0

def node90Piece75Output : SectorVector := [(0, node90Piece75Output_sector0), (2, node90Piece75Output_sector1)]

theorem node90Piece75_check : (reflectVector node90Piece21Output).reverse = node90Piece75Output := by rfl

theorem node90Piece75_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece75Input) = evaluate node90Piece75Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece21_value (by decide +kernel) node90Piece75_check

def node90Piece76Input_sector0 : RawPoly ℕ := [(180, [0, 2, 2, 7])]

def node90Piece76Input : SectorVector := [(1, node90Piece76Input_sector0)]
def node90Piece76Output_sector0 : RawPoly ℕ := reflectPoly node90Piece22Output_sector1

def node90Piece76Output_sector1 : RawPoly ℕ := reflectPoly node90Piece22Output_sector0

def node90Piece76Output : SectorVector := [(0, node90Piece76Output_sector0), (2, node90Piece76Output_sector1)]

theorem node90Piece76_check : (reflectVector node90Piece22Output).reverse = node90Piece76Output := by rfl

theorem node90Piece76_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece76Input) = evaluate node90Piece76Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece22_value (by decide +kernel) node90Piece76_check

def node90Piece77Input_sector0 : RawPoly ℕ := [(620, [0, 2, 3, 6])]

def node90Piece77Input : SectorVector := [(1, node90Piece77Input_sector0)]
def node90Piece77Output_sector0 : RawPoly ℕ := reflectPoly node90Piece23Output_sector1

def node90Piece77Output_sector1 : RawPoly ℕ := reflectPoly node90Piece23Output_sector0

def node90Piece77Output : SectorVector := [(0, node90Piece77Output_sector0), (2, node90Piece77Output_sector1)]

theorem node90Piece77_check : (reflectVector node90Piece23Output).reverse = node90Piece77Output := by rfl

theorem node90Piece77_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece77Input) = evaluate node90Piece77Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece23_value (by decide +kernel) node90Piece77_check

def node90Piece78Input_sector0 : RawPoly ℕ := [(126, [0, 2, 4, 5])]

def node90Piece78Input : SectorVector := [(1, node90Piece78Input_sector0)]
def node90Piece78Output_sector0 : RawPoly ℕ := reflectPoly node90Piece24Output_sector1

def node90Piece78Output_sector1 : RawPoly ℕ := reflectPoly node90Piece24Output_sector0

def node90Piece78Output : SectorVector := [(0, node90Piece78Output_sector0), (2, node90Piece78Output_sector1)]

theorem node90Piece78_check : (reflectVector node90Piece24Output).reverse = node90Piece78Output := by rfl

theorem node90Piece78_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece78Input) = evaluate node90Piece78Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece24_value (by decide +kernel) node90Piece78_check

def node90Piece79Input_sector0 : RawPoly ℕ := [(48, [0, 3, 3, 5])]

def node90Piece79Input : SectorVector := [(1, node90Piece79Input_sector0)]
def node90Piece79Output_sector0 : RawPoly ℕ := reflectPoly node90Piece25Output_sector1

def node90Piece79Output_sector1 : RawPoly ℕ := reflectPoly node90Piece25Output_sector0

def node90Piece79Output : SectorVector := [(0, node90Piece79Output_sector0), (2, node90Piece79Output_sector1)]

theorem node90Piece79_check : (reflectVector node90Piece25Output).reverse = node90Piece79Output := by rfl

theorem node90Piece79_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece79Input) = evaluate node90Piece79Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece25_value (by decide +kernel) node90Piece79_check

end VOA.Classification.COne.OrbC2h
