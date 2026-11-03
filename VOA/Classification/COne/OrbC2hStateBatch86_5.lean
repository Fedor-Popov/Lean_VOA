import VOA.Classification.COne.OrbC2hStateBatch86_1
import VOA.Classification.COne.OrbC2hStateBatch86_0
import VOA.Classification.COne.OrbC2hReflection
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hBucketSectors
import VOA.Classification.COne.OrbC2hStateBatch86_3
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

def node86Piece80Input_sector0 : RawPoly ℕ := [(110, [0, 1, 1, 1, 2, 2, 2, 3])]

def node86Piece80Input : SectorVector := [(1, node86Piece80Input_sector0)]
def node86Piece80Output_sector0 : RawPoly ℕ := reflectPoly node86Piece9Output_sector1

def node86Piece80Output_sector1 : RawPoly ℕ := reflectPoly node86Piece9Output_sector0

def node86Piece80Output : SectorVector := [(0, node86Piece80Output_sector0), (2, node86Piece80Output_sector1)]

theorem node86Piece80_check : (reflectVector node86Piece9Output).reverse = node86Piece80Output := by rfl

theorem node86Piece80_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece80Input) = evaluate node86Piece80Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece9_value (by decide +kernel) node86Piece80_check

def node86Piece81Input_sector0 : RawPoly ℕ := [(720, [0, 1, 1, 1, 2, 7])]

def node86Piece81Input : SectorVector := [(1, node86Piece81Input_sector0)]
def node86Piece81Output_sector0 : RawPoly ℕ := reflectPoly node86Piece10Output_sector1

def node86Piece81Output_sector1 : RawPoly ℕ := reflectPoly node86Piece10Output_sector0

def node86Piece81Output : SectorVector := [(0, node86Piece81Output_sector0), (2, node86Piece81Output_sector1)]

theorem node86Piece81_check : (reflectVector node86Piece10Output).reverse = node86Piece81Output := by rfl

theorem node86Piece81_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece81Input) = evaluate node86Piece81Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece10_value (by decide +kernel) node86Piece81_check

def node86Piece82Input_sector0 : RawPoly ℕ := [(-1000, [0, 1, 1, 1, 3, 6])]

def node86Piece82Input : SectorVector := [(1, node86Piece82Input_sector0)]
def node86Piece82Output_sector0 : RawPoly ℕ := reflectPoly node86Piece11Output_sector1

def node86Piece82Output_sector1 : RawPoly ℕ := reflectPoly node86Piece11Output_sector0

def node86Piece82Output : SectorVector := [(0, node86Piece82Output_sector0), (2, node86Piece82Output_sector1)]

theorem node86Piece82_check : (reflectVector node86Piece11Output).reverse = node86Piece82Output := by rfl

theorem node86Piece82_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece82Input) = evaluate node86Piece82Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece11_value (by decide +kernel) node86Piece82_check

def node86Piece83Input_sector0 : RawPoly ℕ := [(336, [0, 1, 1, 1, 4, 5])]

def node86Piece83Input : SectorVector := [(1, node86Piece83Input_sector0)]
def node86Piece83Output_sector0 : RawPoly ℕ := reflectPoly node86Piece12Output_sector1

def node86Piece83Output_sector1 : RawPoly ℕ := reflectPoly node86Piece12Output_sector0

def node86Piece83Output : SectorVector := [(0, node86Piece83Output_sector0), (2, node86Piece83Output_sector1)]

theorem node86Piece83_check : (reflectVector node86Piece12Output).reverse = node86Piece83Output := by rfl

theorem node86Piece83_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece83Input) = evaluate node86Piece83Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece12_value (by decide +kernel) node86Piece83_check

def node86Piece84Input_sector0 : RawPoly ℕ := [(-30, [0, 1, 1, 2, 2, 2, 2, 2])]

def node86Piece84Input : SectorVector := [(1, node86Piece84Input_sector0)]
def node86Piece84Output_sector0 : RawPoly ℕ := reflectPoly node86Piece13Output_sector1

def node86Piece84Output_sector1 : RawPoly ℕ := reflectPoly node86Piece13Output_sector0

def node86Piece84Output : SectorVector := [(0, node86Piece84Output_sector0), (2, node86Piece84Output_sector1)]

theorem node86Piece84_check : (reflectVector node86Piece13Output).reverse = node86Piece84Output := by rfl

theorem node86Piece84_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece84Input) = evaluate node86Piece84Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece13_value (by decide +kernel) node86Piece84_check

def node86Piece85Input_sector0 : RawPoly ℕ := [(-300, [0, 1, 1, 2, 2, 6])]

def node86Piece85Input : SectorVector := [(1, node86Piece85Input_sector0)]
def node86Piece85Output_sector0 : RawPoly ℕ := reflectPoly node86Piece14Output_sector1

def node86Piece85Output_sector1 : RawPoly ℕ := reflectPoly node86Piece14Output_sector0

def node86Piece85Output : SectorVector := [(0, node86Piece85Output_sector0), (2, node86Piece85Output_sector1)]

theorem node86Piece85_check : (reflectVector node86Piece14Output).reverse = node86Piece85Output := by rfl

theorem node86Piece85_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece85Input) = evaluate node86Piece85Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece14_value (by decide +kernel) node86Piece85_check

def node86Piece86Input_sector0 : RawPoly ℕ := [(-1272, [0, 1, 1, 2, 3, 5])]

def node86Piece86Input : SectorVector := [(1, node86Piece86Input_sector0)]
def node86Piece86Output_sector0 : RawPoly ℕ := reflectPoly node86Piece15Output_sector1

def node86Piece86Output_sector1 : RawPoly ℕ := reflectPoly node86Piece15Output_sector0

def node86Piece86Output : SectorVector := [(0, node86Piece86Output_sector0), (2, node86Piece86Output_sector1)]

theorem node86Piece86_check : (reflectVector node86Piece15Output).reverse = node86Piece86Output := by rfl

theorem node86Piece86_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece86Input) = evaluate node86Piece86Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece15_value (by decide +kernel) node86Piece86_check

def node86Piece87Input_sector0 : RawPoly ℕ := [(720, [0, 1, 1, 2, 4, 4])]

def node86Piece87Input : SectorVector := [(1, node86Piece87Input_sector0)]
def node86Piece87Output_sector0 : RawPoly ℕ := reflectPoly node86Piece16Output_sector1

def node86Piece87Output_sector1 : RawPoly ℕ := reflectPoly node86Piece16Output_sector0

def node86Piece87Output : SectorVector := [(0, node86Piece87Output_sector0), (2, node86Piece87Output_sector1)]

theorem node86Piece87_check : (reflectVector node86Piece16Output).reverse = node86Piece87Output := by rfl

theorem node86Piece87_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece87Input) = evaluate node86Piece87Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece16_value (by decide +kernel) node86Piece87_check

def node86Piece88Input_sector0 : RawPoly ℕ := [(-1540, [0, 1, 1, 3, 3, 4])]

def node86Piece88Input : SectorVector := [(1, node86Piece88Input_sector0)]
def node86Piece88Output_sector0 : RawPoly ℕ := reflectPoly node86Piece17Output_sector1

def node86Piece88Output_sector1 : RawPoly ℕ := reflectPoly node86Piece17Output_sector0

def node86Piece88Output : SectorVector := [(0, node86Piece88Output_sector0), (2, node86Piece88Output_sector1)]

theorem node86Piece88_check : (reflectVector node86Piece17Output).reverse = node86Piece88Output := by rfl

theorem node86Piece88_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece88Input) = evaluate node86Piece88Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece17_value (by decide +kernel) node86Piece88_check

def node86Piece89Input_sector0 : RawPoly ℕ := [(6120, [0, 1, 1, 10])]

def node86Piece89Input : SectorVector := [(1, node86Piece89Input_sector0)]
def node86Piece89Output_sector0 : RawPoly ℕ := reflectPoly node86Piece18Output_sector1

def node86Piece89Output_sector1 : RawPoly ℕ := reflectPoly node86Piece18Output_sector0

def node86Piece89Output : SectorVector := [(0, node86Piece89Output_sector0), (2, node86Piece89Output_sector1)]

theorem node86Piece89_check : (reflectVector node86Piece18Output).reverse = node86Piece89Output := by rfl

theorem node86Piece89_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece89Input) = evaluate node86Piece89Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece18_value (by decide +kernel) node86Piece89_check

def node86Piece90Input_sector0 : RawPoly ℕ := [(-1284, [0, 1, 2, 2, 2, 5])]

def node86Piece90Input : SectorVector := [(1, node86Piece90Input_sector0)]
def node86Piece90Output_sector0 : RawPoly ℕ := reflectPoly node86Piece19Output_sector1

def node86Piece90Output_sector1 : RawPoly ℕ := reflectPoly node86Piece19Output_sector0

def node86Piece90Output : SectorVector := [(0, node86Piece90Output_sector0), (2, node86Piece90Output_sector1)]

theorem node86Piece90_check : (reflectVector node86Piece19Output).reverse = node86Piece90Output := by rfl

theorem node86Piece90_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece90Input) = evaluate node86Piece90Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece19_value (by decide +kernel) node86Piece90_check

def node86Piece91Input_sector0 : RawPoly ℕ := [(-1095, [0, 1, 2, 2, 3, 4])]

def node86Piece91Input : SectorVector := [(1, node86Piece91Input_sector0)]
def node86Piece91Output_sector0 : RawPoly ℕ := reflectPoly node86Piece20Output_sector1

def node86Piece91Output_sector1 : RawPoly ℕ := reflectPoly node86Piece20Output_sector0

def node86Piece91Output : SectorVector := [(0, node86Piece91Output_sector0), (2, node86Piece91Output_sector1)]

theorem node86Piece91_check : (reflectVector node86Piece20Output).reverse = node86Piece91Output := by rfl

theorem node86Piece91_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece91Input) = evaluate node86Piece91Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece20_value (by decide +kernel) node86Piece91_check

def node86Piece92Input_sector0 : RawPoly ℕ := [(-120, [0, 1, 2, 3, 3, 3])]

def node86Piece92Input : SectorVector := [(1, node86Piece92Input_sector0)]
def node86Piece92Output_sector0 : RawPoly ℕ := reflectPoly node86Piece21Output_sector1

def node86Piece92Output_sector1 : RawPoly ℕ := reflectPoly node86Piece21Output_sector0

def node86Piece92Output : SectorVector := [(0, node86Piece92Output_sector0), (2, node86Piece92Output_sector1)]

theorem node86Piece92_check : (reflectVector node86Piece21Output).reverse = node86Piece92Output := by rfl

theorem node86Piece92_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece92Input) = evaluate node86Piece92Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece21_value (by decide +kernel) node86Piece92_check

def node86Piece93Input_sector0 : RawPoly ℕ := [(3480, [0, 1, 2, 9])]

def node86Piece93Input : SectorVector := [(1, node86Piece93Input_sector0)]
def node86Piece93Output_sector0 : RawPoly ℕ := reflectPoly node86Piece22Output_sector1

def node86Piece93Output_sector1 : RawPoly ℕ := reflectPoly node86Piece22Output_sector0

def node86Piece93Output : SectorVector := [(0, node86Piece93Output_sector0), (2, node86Piece93Output_sector1)]

theorem node86Piece93_check : (reflectVector node86Piece22Output).reverse = node86Piece93Output := by rfl

theorem node86Piece93_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece93Input) = evaluate node86Piece93Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece22_value (by decide +kernel) node86Piece93_check

def node86Piece94Input_sector0 : RawPoly ℕ := [(600, [0, 1, 3, 8])]

def node86Piece94Input : SectorVector := [(1, node86Piece94Input_sector0)]
def node86Piece94Output_sector0 : RawPoly ℕ := reflectPoly node86Piece23Output_sector1

def node86Piece94Output_sector1 : RawPoly ℕ := reflectPoly node86Piece23Output_sector0

def node86Piece94Output : SectorVector := [(0, node86Piece94Output_sector0), (2, node86Piece94Output_sector1)]

theorem node86Piece94_check : (reflectVector node86Piece23Output).reverse = node86Piece94Output := by rfl

theorem node86Piece94_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece94Input) = evaluate node86Piece94Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece23_value (by decide +kernel) node86Piece94_check

def node86Piece95Input_sector0 : RawPoly ℕ := [(180, [0, 1, 4, 7])]

def node86Piece95Input : SectorVector := [(1, node86Piece95Input_sector0)]
def node86Piece95Output_sector0 : RawPoly ℕ := reflectPoly node86Piece24Output_sector1

def node86Piece95Output_sector1 : RawPoly ℕ := reflectPoly node86Piece24Output_sector0

def node86Piece95Output : SectorVector := [(0, node86Piece95Output_sector0), (2, node86Piece95Output_sector1)]

theorem node86Piece95_check : (reflectVector node86Piece24Output).reverse = node86Piece95Output := by rfl

theorem node86Piece95_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-3)
    (evaluate node86Piece95Input) = evaluate node86Piece95Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-3) _ _ _ _
    node86Piece24_value (by decide +kernel) node86Piece95_check

end VOA.Classification.COne.OrbC2h
