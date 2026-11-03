import VOA.Classification.COne.OrbC2hStateBatch90_2
import VOA.Classification.COne.OrbC2hStateBatch90_1
import VOA.Classification.COne.OrbC2hReflection
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hBucketSectors
import VOA.Classification.COne.OrbC2hStateBatch90_3
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

def node90Piece80Input_sector0 : RawPoly ℕ := [(720, [0, 3, 4, 4])]

def node90Piece80Input : SectorVector := [(1, node90Piece80Input_sector0)]
def node90Piece80Output_sector0 : RawPoly ℕ := reflectPoly node90Piece26Output_sector1

def node90Piece80Output_sector1 : RawPoly ℕ := reflectPoly node90Piece26Output_sector0

def node90Piece80Output : SectorVector := [(0, node90Piece80Output_sector0), (2, node90Piece80Output_sector1)]

theorem node90Piece80_check : (reflectVector node90Piece26Output).reverse = node90Piece80Output := by rfl

theorem node90Piece80_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece80Input) = evaluate node90Piece80Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece26_value (by decide +kernel) node90Piece80_check

def node90Piece81Input_sector0 : RawPoly ℕ := [(10800, [0, 11])]

def node90Piece81Input : SectorVector := [(1, node90Piece81Input_sector0)]
def node90Piece81Output_sector0 : RawPoly ℕ := reflectPoly node90Piece27Output_sector1

def node90Piece81Output_sector1 : RawPoly ℕ := reflectPoly node90Piece27Output_sector0

def node90Piece81Output : SectorVector := [(0, node90Piece81Output_sector0), (2, node90Piece81Output_sector1)]

theorem node90Piece81_check : (reflectVector node90Piece27Output).reverse = node90Piece81Output := by rfl

theorem node90Piece81_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece81Input) = evaluate node90Piece81Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece27_value (by decide +kernel) node90Piece81_check

def node90Piece82Input_sector0 : RawPoly ℕ := [(-96, [1, 1, 1, 1, 1, 1, 1, 4])]

def node90Piece82Input : SectorVector := [(1, node90Piece82Input_sector0)]
def node90Piece82Output_sector0 : RawPoly ℕ := reflectPoly node90Piece28Output_sector1

def node90Piece82Output_sector1 : RawPoly ℕ := reflectPoly node90Piece28Output_sector0

def node90Piece82Output : SectorVector := [(0, node90Piece82Output_sector0), (2, node90Piece82Output_sector1)]

theorem node90Piece82_check : (reflectVector node90Piece28Output).reverse = node90Piece82Output := by rfl

theorem node90Piece82_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece82Input) = evaluate node90Piece82Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece28_value (by decide +kernel) node90Piece82_check

def node90Piece83Input_sector0 : RawPoly ℕ := [(-112, [1, 1, 1, 1, 1, 1, 2, 3])]

def node90Piece83Input : SectorVector := [(1, node90Piece83Input_sector0)]
def node90Piece83Output_sector0 : RawPoly ℕ := reflectPoly node90Piece29Output_sector1

def node90Piece83Output_sector1 : RawPoly ℕ := reflectPoly node90Piece29Output_sector0

def node90Piece83Output : SectorVector := [(0, node90Piece83Output_sector0), (2, node90Piece83Output_sector1)]

theorem node90Piece83_check : (reflectVector node90Piece29Output).reverse = node90Piece83Output := by rfl

theorem node90Piece83_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece83Input) = evaluate node90Piece83Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece29_value (by decide +kernel) node90Piece83_check

def node90Piece84Input_sector0 : RawPoly ℕ := [(88, [1, 1, 1, 1, 1, 2, 2, 2])]

def node90Piece84Input : SectorVector := [(1, node90Piece84Input_sector0)]
def node90Piece84Output_sector0 : RawPoly ℕ := reflectPoly node90Piece30Output_sector1

def node90Piece84Output_sector1 : RawPoly ℕ := reflectPoly node90Piece30Output_sector0

def node90Piece84Output : SectorVector := [(0, node90Piece84Output_sector0), (2, node90Piece84Output_sector1)]

theorem node90Piece84_check : (reflectVector node90Piece30Output).reverse = node90Piece84Output := by rfl

theorem node90Piece84_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece84Input) = evaluate node90Piece84Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece30_value (by decide +kernel) node90Piece84_check

def node90Piece85Input_sector0 : RawPoly ℕ := [(-440, [1, 1, 1, 1, 1, 6])]

def node90Piece85Input : SectorVector := [(1, node90Piece85Input_sector0)]
def node90Piece85Output_sector0 : RawPoly ℕ := reflectPoly node90Piece31Output_sector1

def node90Piece85Output_sector1 : RawPoly ℕ := reflectPoly node90Piece31Output_sector0

def node90Piece85Output : SectorVector := [(0, node90Piece85Output_sector0), (2, node90Piece85Output_sector1)]

theorem node90Piece85_check : (reflectVector node90Piece31Output).reverse = node90Piece85Output := by rfl

theorem node90Piece85_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece85Input) = evaluate node90Piece85Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece31_value (by decide +kernel) node90Piece85_check

def node90Piece86Input_sector0 : RawPoly ℕ := [(2400, [1, 1, 1, 1, 2, 5])]

def node90Piece86Input : SectorVector := [(1, node90Piece86Input_sector0)]
def node90Piece86Output_sector0 : RawPoly ℕ := reflectPoly node90Piece32Output_sector1

def node90Piece86Output_sector1 : RawPoly ℕ := reflectPoly node90Piece32Output_sector0

def node90Piece86Output : SectorVector := [(0, node90Piece86Output_sector0), (2, node90Piece86Output_sector1)]

theorem node90Piece86_check : (reflectVector node90Piece32Output).reverse = node90Piece86Output := by rfl

theorem node90Piece86_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece86Input) = evaluate node90Piece86Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece32_value (by decide +kernel) node90Piece86_check

def node90Piece87Input_sector0 : RawPoly ℕ := [(-840, [1, 1, 1, 1, 3, 4])]

def node90Piece87Input : SectorVector := [(1, node90Piece87Input_sector0)]
def node90Piece87Output_sector0 : RawPoly ℕ := reflectPoly node90Piece33Output_sector1

def node90Piece87Output_sector1 : RawPoly ℕ := reflectPoly node90Piece33Output_sector0

def node90Piece87Output : SectorVector := [(0, node90Piece87Output_sector0), (2, node90Piece87Output_sector1)]

theorem node90Piece87_check : (reflectVector node90Piece33Output).reverse = node90Piece87Output := by rfl

theorem node90Piece87_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece87Input) = evaluate node90Piece87Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece33_value (by decide +kernel) node90Piece87_check

def node90Piece88Input_sector0 : RawPoly ℕ := [(3360, [1, 1, 1, 2, 2, 4])]

def node90Piece88Input : SectorVector := [(1, node90Piece88Input_sector0)]
def node90Piece88Output_sector0 : RawPoly ℕ := reflectPoly node90Piece34Output_sector1

def node90Piece88Output_sector1 : RawPoly ℕ := reflectPoly node90Piece34Output_sector0

def node90Piece88Output : SectorVector := [(0, node90Piece88Output_sector0), (2, node90Piece88Output_sector1)]

theorem node90Piece88_check : (reflectVector node90Piece34Output).reverse = node90Piece88Output := by rfl

theorem node90Piece88_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece88Input) = evaluate node90Piece88Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece34_value (by decide +kernel) node90Piece88_check

def node90Piece89Input_sector0 : RawPoly ℕ := [(400, [1, 1, 1, 2, 3, 3])]

def node90Piece89Input : SectorVector := [(1, node90Piece89Input_sector0)]
def node90Piece89Output_sector0 : RawPoly ℕ := reflectPoly node90Piece35Output_sector1

def node90Piece89Output_sector1 : RawPoly ℕ := reflectPoly node90Piece35Output_sector0

def node90Piece89Output : SectorVector := [(0, node90Piece89Output_sector0), (2, node90Piece89Output_sector1)]

theorem node90Piece89_check : (reflectVector node90Piece35Output).reverse = node90Piece89Output := by rfl

theorem node90Piece89_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece89Input) = evaluate node90Piece89Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece35_value (by decide +kernel) node90Piece89_check

def node90Piece90Input_sector0 : RawPoly ℕ := [(-4200, [1, 1, 1, 8])]

def node90Piece90Input : SectorVector := [(1, node90Piece90Input_sector0)]
def node90Piece90Output_sector0 : RawPoly ℕ := reflectPoly node90Piece36Output_sector1

def node90Piece90Output_sector1 : RawPoly ℕ := reflectPoly node90Piece36Output_sector0

def node90Piece90Output : SectorVector := [(0, node90Piece90Output_sector0), (2, node90Piece90Output_sector1)]

theorem node90Piece90_check : (reflectVector node90Piece36Output).reverse = node90Piece90Output := by rfl

theorem node90Piece90_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece90Input) = evaluate node90Piece90Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece36_value (by decide +kernel) node90Piece90_check

def node90Piece91Input_sector0 : RawPoly ℕ := [(-920, [1, 1, 2, 2, 2, 3])]

def node90Piece91Input : SectorVector := [(1, node90Piece91Input_sector0)]
def node90Piece91Output_sector0 : RawPoly ℕ := reflectPoly node90Piece37Output_sector1

def node90Piece91Output_sector1 : RawPoly ℕ := reflectPoly node90Piece37Output_sector0

def node90Piece91Output : SectorVector := [(0, node90Piece91Output_sector0), (2, node90Piece91Output_sector1)]

theorem node90Piece91_check : (reflectVector node90Piece37Output).reverse = node90Piece91Output := by rfl

theorem node90Piece91_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece91Input) = evaluate node90Piece91Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece37_value (by decide +kernel) node90Piece91_check

def node90Piece92Input_sector0 : RawPoly ℕ := [(-2160, [1, 1, 2, 7])]

def node90Piece92Input : SectorVector := [(1, node90Piece92Input_sector0)]
def node90Piece92Output_sector0 : RawPoly ℕ := reflectPoly node90Piece38Output_sector1

def node90Piece92Output_sector1 : RawPoly ℕ := reflectPoly node90Piece38Output_sector0

def node90Piece92Output : SectorVector := [(0, node90Piece92Output_sector0), (2, node90Piece92Output_sector1)]

theorem node90Piece92_check : (reflectVector node90Piece38Output).reverse = node90Piece92Output := by rfl

theorem node90Piece92_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece92Input) = evaluate node90Piece92Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece38_value (by decide +kernel) node90Piece92_check

def node90Piece93Input_sector0 : RawPoly ℕ := [(-2960, [1, 1, 3, 6])]

def node90Piece93Input : SectorVector := [(1, node90Piece93Input_sector0)]
def node90Piece93Output_sector0 : RawPoly ℕ := reflectPoly node90Piece39Output_sector1

def node90Piece93Output_sector1 : RawPoly ℕ := reflectPoly node90Piece39Output_sector0

def node90Piece93Output : SectorVector := [(0, node90Piece93Output_sector0), (2, node90Piece93Output_sector1)]

theorem node90Piece93_check : (reflectVector node90Piece39Output).reverse = node90Piece93Output := by rfl

theorem node90Piece93_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece93Input) = evaluate node90Piece93Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece39_value (by decide +kernel) node90Piece93_check

def node90Piece94Input_sector0 : RawPoly ℕ := [(2304, [1, 1, 4, 5])]

def node90Piece94Input : SectorVector := [(1, node90Piece94Input_sector0)]
def node90Piece94Output_sector0 : RawPoly ℕ := reflectPoly node90Piece40Output_sector1

def node90Piece94Output_sector1 : RawPoly ℕ := reflectPoly node90Piece40Output_sector0

def node90Piece94Output : SectorVector := [(0, node90Piece94Output_sector0), (2, node90Piece94Output_sector1)]

theorem node90Piece94_check : (reflectVector node90Piece40Output).reverse = node90Piece94Output := by rfl

theorem node90Piece94_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece94Input) = evaluate node90Piece94Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece40_value (by decide +kernel) node90Piece94_check

def node90Piece95Input_sector0 : RawPoly ℕ := [(-240, [1, 2, 2, 2, 2, 2])]

def node90Piece95Input : SectorVector := [(1, node90Piece95Input_sector0)]
def node90Piece95Output_sector0 : RawPoly ℕ := reflectPoly node90Piece41Output_sector1

def node90Piece95Output_sector1 : RawPoly ℕ := reflectPoly node90Piece41Output_sector0

def node90Piece95Output : SectorVector := [(0, node90Piece95Output_sector0), (2, node90Piece95Output_sector1)]

theorem node90Piece95_check : (reflectVector node90Piece41Output).reverse = node90Piece95Output := by rfl

theorem node90Piece95_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-4)
    (evaluate node90Piece95Input) = evaluate node90Piece95Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-4) _ _ _ _
    node90Piece41_value (by decide +kernel) node90Piece95_check

end VOA.Classification.COne.OrbC2h
