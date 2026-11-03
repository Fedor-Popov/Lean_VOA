import VOA.Classification.COne.OrbC2hStateBatch94_1
import VOA.Classification.COne.OrbC2hReflection
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hBucketSectors
import VOA.Classification.COne.OrbC2hStateBatch94_2
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

def node94Piece64Input_sector0 : RawPoly ℕ := [(2640, [1, 1, 1, 1, 2, 4])]

def node94Piece64Input : SectorVector := [(1, node94Piece64Input_sector0)]
def node94Piece64Output_sector0 : RawPoly ℕ := reflectPoly node94Piece23Output_sector1

def node94Piece64Output_sector1 : RawPoly ℕ := reflectPoly node94Piece23Output_sector0

def node94Piece64Output : SectorVector := [(0, node94Piece64Output_sector0), (2, node94Piece64Output_sector1)]

theorem node94Piece64_check : (reflectVector node94Piece23Output).reverse = node94Piece64Output := by rfl

theorem node94Piece64_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece64Input) = evaluate node94Piece64Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece23_value (by decide +kernel) node94Piece64_check

def node94Piece65Input_sector0 : RawPoly ℕ := [(-960, [1, 1, 1, 1, 3, 3])]

def node94Piece65Input : SectorVector := [(1, node94Piece65Input_sector0)]
def node94Piece65Output_sector0 : RawPoly ℕ := reflectPoly node94Piece24Output_sector1

def node94Piece65Output_sector1 : RawPoly ℕ := reflectPoly node94Piece24Output_sector0

def node94Piece65Output : SectorVector := [(0, node94Piece65Output_sector0), (2, node94Piece65Output_sector1)]

theorem node94Piece65_check : (reflectVector node94Piece24Output).reverse = node94Piece65Output := by rfl

theorem node94Piece65_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece65Input) = evaluate node94Piece65Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece24_value (by decide +kernel) node94Piece65_check

def node94Piece66Input_sector0 : RawPoly ℕ := [(2320, [1, 1, 1, 2, 2, 3])]

def node94Piece66Input : SectorVector := [(1, node94Piece66Input_sector0)]
def node94Piece66Output_sector0 : RawPoly ℕ := reflectPoly node94Piece25Output_sector1

def node94Piece66Output_sector1 : RawPoly ℕ := reflectPoly node94Piece25Output_sector0

def node94Piece66Output : SectorVector := [(0, node94Piece66Output_sector0), (2, node94Piece66Output_sector1)]

theorem node94Piece66_check : (reflectVector node94Piece25Output).reverse = node94Piece66Output := by rfl

theorem node94Piece66_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece66Input) = evaluate node94Piece66Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece25_value (by decide +kernel) node94Piece66_check

def node94Piece67Input_sector0 : RawPoly ℕ := [(-3360, [1, 1, 1, 7])]

def node94Piece67Input : SectorVector := [(1, node94Piece67Input_sector0)]
def node94Piece67Output_sector0 : RawPoly ℕ := reflectPoly node94Piece26Output_sector1

def node94Piece67Output_sector1 : RawPoly ℕ := reflectPoly node94Piece26Output_sector0

def node94Piece67Output : SectorVector := [(0, node94Piece67Output_sector0), (2, node94Piece67Output_sector1)]

theorem node94Piece67_check : (reflectVector node94Piece26Output).reverse = node94Piece67Output := by rfl

theorem node94Piece67_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece67Input) = evaluate node94Piece67Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece26_value (by decide +kernel) node94Piece67_check

def node94Piece68Input_sector0 : RawPoly ℕ := [(-480, [1, 1, 2, 2, 2, 2])]

def node94Piece68Input : SectorVector := [(1, node94Piece68Input_sector0)]
def node94Piece68Output_sector0 : RawPoly ℕ := reflectPoly node94Piece27Output_sector1

def node94Piece68Output_sector1 : RawPoly ℕ := reflectPoly node94Piece27Output_sector0

def node94Piece68Output : SectorVector := [(0, node94Piece68Output_sector0), (2, node94Piece68Output_sector1)]

theorem node94Piece68_check : (reflectVector node94Piece27Output).reverse = node94Piece68Output := by rfl

theorem node94Piece68_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece68Input) = evaluate node94Piece68Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece27_value (by decide +kernel) node94Piece68_check

def node94Piece69Input_sector0 : RawPoly ℕ := [(-1200, [1, 1, 2, 6])]

def node94Piece69Input : SectorVector := [(1, node94Piece69Input_sector0)]
def node94Piece69Output_sector0 : RawPoly ℕ := reflectPoly node94Piece28Output_sector1

def node94Piece69Output_sector1 : RawPoly ℕ := reflectPoly node94Piece28Output_sector0

def node94Piece69Output : SectorVector := [(0, node94Piece69Output_sector0), (2, node94Piece69Output_sector1)]

theorem node94Piece69_check : (reflectVector node94Piece28Output).reverse = node94Piece69Output := by rfl

theorem node94Piece69_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece69Input) = evaluate node94Piece69Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece28_value (by decide +kernel) node94Piece69_check

def node94Piece70Input_sector0 : RawPoly ℕ := [(-4416, [1, 1, 3, 5])]

def node94Piece70Input : SectorVector := [(1, node94Piece70Input_sector0)]
def node94Piece70Output_sector0 : RawPoly ℕ := reflectPoly node94Piece29Output_sector1

def node94Piece70Output_sector1 : RawPoly ℕ := reflectPoly node94Piece29Output_sector0

def node94Piece70Output : SectorVector := [(0, node94Piece70Output_sector0), (2, node94Piece70Output_sector1)]

theorem node94Piece70_check : (reflectVector node94Piece29Output).reverse = node94Piece70Output := by rfl

theorem node94Piece70_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece70Input) = evaluate node94Piece70Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece29_value (by decide +kernel) node94Piece70_check

def node94Piece71Input_sector0 : RawPoly ℕ := [(3060, [1, 1, 4, 4])]

def node94Piece71Input : SectorVector := [(1, node94Piece71Input_sector0)]
def node94Piece71Output_sector0 : RawPoly ℕ := reflectPoly node94Piece30Output_sector1

def node94Piece71Output_sector1 : RawPoly ℕ := reflectPoly node94Piece30Output_sector0

def node94Piece71Output : SectorVector := [(0, node94Piece71Output_sector0), (2, node94Piece71Output_sector1)]

theorem node94Piece71_check : (reflectVector node94Piece30Output).reverse = node94Piece71Output := by rfl

theorem node94Piece71_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece71Input) = evaluate node94Piece71Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece30_value (by decide +kernel) node94Piece71_check

def node94Piece72Input_sector0 : RawPoly ℕ := [(-3816, [1, 2, 2, 5])]

def node94Piece72Input : SectorVector := [(1, node94Piece72Input_sector0)]
def node94Piece72Output_sector0 : RawPoly ℕ := reflectPoly node94Piece31Output_sector1

def node94Piece72Output_sector1 : RawPoly ℕ := reflectPoly node94Piece31Output_sector0

def node94Piece72Output : SectorVector := [(0, node94Piece72Output_sector0), (2, node94Piece72Output_sector1)]

theorem node94Piece72_check : (reflectVector node94Piece31Output).reverse = node94Piece72Output := by rfl

theorem node94Piece72_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece72Input) = evaluate node94Piece72Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece31_value (by decide +kernel) node94Piece72_check

def node94Piece73Input_sector0 : RawPoly ℕ := [(2640, [1, 2, 3, 4])]

def node94Piece73Input : SectorVector := [(1, node94Piece73Input_sector0)]
def node94Piece73Output_sector0 : RawPoly ℕ := reflectPoly node94Piece32Output_sector1

def node94Piece73Output_sector1 : RawPoly ℕ := reflectPoly node94Piece32Output_sector0

def node94Piece73Output : SectorVector := [(0, node94Piece73Output_sector0), (2, node94Piece73Output_sector1)]

theorem node94Piece73_check : (reflectVector node94Piece32Output).reverse = node94Piece73Output := by rfl

theorem node94Piece73_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece73Input) = evaluate node94Piece73Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece32_value (by decide +kernel) node94Piece73_check

def node94Piece74Input_sector0 : RawPoly ℕ := [(-960, [1, 3, 3, 3])]

def node94Piece74Input : SectorVector := [(1, node94Piece74Input_sector0)]
def node94Piece74Output_sector0 : RawPoly ℕ := reflectPoly node94Piece33Output_sector1

def node94Piece74Output_sector1 : RawPoly ℕ := reflectPoly node94Piece33Output_sector0

def node94Piece74Output : SectorVector := [(0, node94Piece74Output_sector0), (2, node94Piece74Output_sector1)]

theorem node94Piece74_check : (reflectVector node94Piece33Output).reverse = node94Piece74Output := by rfl

theorem node94Piece74_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece74Input) = evaluate node94Piece74Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece33_value (by decide +kernel) node94Piece74_check

def node94Piece75Input_sector0 : RawPoly ℕ := [(-27600, [1, 9])]

def node94Piece75Input : SectorVector := [(1, node94Piece75Input_sector0)]
def node94Piece75Output_sector0 : RawPoly ℕ := reflectPoly node94Piece34Output_sector1

def node94Piece75Output_sector1 : RawPoly ℕ := reflectPoly node94Piece34Output_sector0

def node94Piece75Output : SectorVector := [(0, node94Piece75Output_sector0), (2, node94Piece75Output_sector1)]

theorem node94Piece75_check : (reflectVector node94Piece34Output).reverse = node94Piece75Output := by rfl

theorem node94Piece75_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece75Input) = evaluate node94Piece75Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece34_value (by decide +kernel) node94Piece75_check

def node94Piece76Input_sector0 : RawPoly ℕ := [(-600, [2, 2, 2, 4])]

def node94Piece76Input : SectorVector := [(1, node94Piece76Input_sector0)]
def node94Piece76Output_sector0 : RawPoly ℕ := reflectPoly node94Piece35Output_sector1

def node94Piece76Output_sector1 : RawPoly ℕ := reflectPoly node94Piece35Output_sector0

def node94Piece76Output : SectorVector := [(0, node94Piece76Output_sector0), (2, node94Piece76Output_sector1)]

theorem node94Piece76_check : (reflectVector node94Piece35Output).reverse = node94Piece76Output := by rfl

theorem node94Piece76_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece76Input) = evaluate node94Piece76Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece35_value (by decide +kernel) node94Piece76_check

def node94Piece77Input_sector0 : RawPoly ℕ := [(2480, [2, 2, 3, 3])]

def node94Piece77Input : SectorVector := [(1, node94Piece77Input_sector0)]
def node94Piece77Output_sector0 : RawPoly ℕ := reflectPoly node94Piece36Output_sector1

def node94Piece77Output_sector1 : RawPoly ℕ := reflectPoly node94Piece36Output_sector0

def node94Piece77Output : SectorVector := [(0, node94Piece77Output_sector0), (2, node94Piece77Output_sector1)]

theorem node94Piece77_check : (reflectVector node94Piece36Output).reverse = node94Piece77Output := by rfl

theorem node94Piece77_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece77Input) = evaluate node94Piece77Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece36_value (by decide +kernel) node94Piece77_check

def node94Piece78Input_sector0 : RawPoly ℕ := [(-8280, [2, 8])]

def node94Piece78Input : SectorVector := [(1, node94Piece78Input_sector0)]
def node94Piece78Output_sector0 : RawPoly ℕ := reflectPoly node94Piece37Output_sector1

def node94Piece78Output_sector1 : RawPoly ℕ := reflectPoly node94Piece37Output_sector0

def node94Piece78Output : SectorVector := [(0, node94Piece78Output_sector0), (2, node94Piece78Output_sector1)]

theorem node94Piece78_check : (reflectVector node94Piece37Output).reverse = node94Piece78Output := by rfl

theorem node94Piece78_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece78Input) = evaluate node94Piece78Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece37_value (by decide +kernel) node94Piece78_check

def node94Piece79Input_sector0 : RawPoly ℕ := [(-1920, [3, 7])]

def node94Piece79Input : SectorVector := [(1, node94Piece79Input_sector0)]
def node94Piece79Output_sector0 : RawPoly ℕ := reflectPoly node94Piece38Output_sector1

def node94Piece79Output_sector1 : RawPoly ℕ := reflectPoly node94Piece38Output_sector0

def node94Piece79Output : SectorVector := [(0, node94Piece79Output_sector0), (2, node94Piece79Output_sector1)]

theorem node94Piece79_check : (reflectVector node94Piece38Output).reverse = node94Piece79Output := by rfl

theorem node94Piece79_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-5)
    (evaluate node94Piece79Input) = evaluate node94Piece79Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-5) _ _ _ _
    node94Piece38_value (by decide +kernel) node94Piece79_check

end VOA.Classification.COne.OrbC2h
