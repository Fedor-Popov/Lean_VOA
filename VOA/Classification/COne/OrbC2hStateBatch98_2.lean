import VOA.Classification.COne.OrbC2hStateBatch98_1
import VOA.Classification.COne.OrbC2hReflection
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hBucketSectors
import VOA.Classification.COne.OrbC2hStateBatch98_0
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

def node98Piece32Input_sector0 : RawPoly ℕ := [(123, [0, 1, 1, 1, 1, 1, 2, 2])]

def node98Piece32Input : SectorVector := [(1, node98Piece32Input_sector0)]
def node98Piece32Output_sector0 : RawPoly ℕ := reflectPoly node98Piece2Output_sector1

def node98Piece32Output_sector1 : RawPoly ℕ := reflectPoly node98Piece2Output_sector0

def node98Piece32Output : SectorVector := [(0, node98Piece32Output_sector0), (2, node98Piece32Output_sector1)]

theorem node98Piece32_check : (reflectVector node98Piece2Output).reverse = node98Piece32Output := by rfl

theorem node98Piece32_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-6)
    (evaluate node98Piece32Input) = evaluate node98Piece32Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-6) _ _ _ _
    node98Piece2_value (by decide +kernel) node98Piece32_check

def node98Piece33Input_sector0 : RawPoly ℕ := [(84, [0, 1, 1, 1, 1, 5])]

def node98Piece33Input : SectorVector := [(1, node98Piece33Input_sector0)]
def node98Piece33Output_sector0 : RawPoly ℕ := reflectPoly node98Piece3Output_sector1

def node98Piece33Output_sector1 : RawPoly ℕ := reflectPoly node98Piece3Output_sector0

def node98Piece33Output : SectorVector := [(0, node98Piece33Output_sector0), (2, node98Piece33Output_sector1)]

theorem node98Piece33_check : (reflectVector node98Piece3Output).reverse = node98Piece33Output := by rfl

theorem node98Piece33_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-6)
    (evaluate node98Piece33Input) = evaluate node98Piece33Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-6) _ _ _ _
    node98Piece3_value (by decide +kernel) node98Piece33_check

def node98Piece34Input_sector0 : RawPoly ℕ := [(1740, [0, 1, 1, 1, 2, 4])]

def node98Piece34Input : SectorVector := [(1, node98Piece34Input_sector0)]
def node98Piece34Output_sector0 : RawPoly ℕ := reflectPoly node98Piece4Output_sector1

def node98Piece34Output_sector1 : RawPoly ℕ := reflectPoly node98Piece4Output_sector0

def node98Piece34Output : SectorVector := [(0, node98Piece34Output_sector0), (2, node98Piece34Output_sector1)]

theorem node98Piece34_check : (reflectVector node98Piece4Output).reverse = node98Piece34Output := by rfl

theorem node98Piece34_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-6)
    (evaluate node98Piece34Input) = evaluate node98Piece34Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-6) _ _ _ _
    node98Piece4_value (by decide +kernel) node98Piece34_check

def node98Piece35Input_sector0 : RawPoly ℕ := [(-1180, [0, 1, 1, 1, 3, 3])]

def node98Piece35Input : SectorVector := [(1, node98Piece35Input_sector0)]
def node98Piece35Output_sector0 : RawPoly ℕ := reflectPoly node98Piece5Output_sector1

def node98Piece35Output_sector1 : RawPoly ℕ := reflectPoly node98Piece5Output_sector0

def node98Piece35Output : SectorVector := [(0, node98Piece35Output_sector0), (2, node98Piece35Output_sector1)]

theorem node98Piece35_check : (reflectVector node98Piece5Output).reverse = node98Piece35Output := by rfl

theorem node98Piece35_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-6)
    (evaluate node98Piece35Input) = evaluate node98Piece35Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-6) _ _ _ _
    node98Piece5_value (by decide +kernel) node98Piece35_check

def node98Piece36Input_sector0 : RawPoly ℕ := [(-930, [0, 1, 1, 2, 2, 3])]

def node98Piece36Input : SectorVector := [(1, node98Piece36Input_sector0)]
def node98Piece36Output_sector0 : RawPoly ℕ := reflectPoly node98Piece6Output_sector1

def node98Piece36Output_sector1 : RawPoly ℕ := reflectPoly node98Piece6Output_sector0

def node98Piece36Output : SectorVector := [(0, node98Piece36Output_sector0), (2, node98Piece36Output_sector1)]

theorem node98Piece36_check : (reflectVector node98Piece6Output).reverse = node98Piece36Output := by rfl

theorem node98Piece36_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-6)
    (evaluate node98Piece36Input) = evaluate node98Piece36Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-6) _ _ _ _
    node98Piece6_value (by decide +kernel) node98Piece36_check

def node98Piece37Input_sector0 : RawPoly ℕ := [(3780, [0, 1, 1, 7])]

def node98Piece37Input : SectorVector := [(1, node98Piece37Input_sector0)]
def node98Piece37Output_sector0 : RawPoly ℕ := reflectPoly node98Piece7Output_sector1

def node98Piece37Output_sector1 : RawPoly ℕ := reflectPoly node98Piece7Output_sector0

def node98Piece37Output : SectorVector := [(0, node98Piece37Output_sector0), (2, node98Piece37Output_sector1)]

theorem node98Piece37_check : (reflectVector node98Piece7Output).reverse = node98Piece37Output := by rfl

theorem node98Piece37_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-6)
    (evaluate node98Piece37Input) = evaluate node98Piece37Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-6) _ _ _ _
    node98Piece7_value (by decide +kernel) node98Piece37_check

def node98Piece38Input_sector0 : RawPoly ℕ := [(-2325/4, [0, 1, 2, 2, 2, 2])]

def node98Piece38Input : SectorVector := [(1, node98Piece38Input_sector0)]
def node98Piece38Output_sector0 : RawPoly ℕ := reflectPoly node98Piece8Output_sector1

def node98Piece38Output_sector1 : RawPoly ℕ := reflectPoly node98Piece8Output_sector0

def node98Piece38Output : SectorVector := [(0, node98Piece38Output_sector0), (2, node98Piece38Output_sector1)]

theorem node98Piece38_check : (reflectVector node98Piece8Output).reverse = node98Piece38Output := by rfl

theorem node98Piece38_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-6)
    (evaluate node98Piece38Input) = evaluate node98Piece38Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-6) _ _ _ _
    node98Piece8_value (by decide +kernel) node98Piece38_check

def node98Piece39Input_sector0 : RawPoly ℕ := [(1590, [0, 1, 2, 6])]

def node98Piece39Input : SectorVector := [(1, node98Piece39Input_sector0)]
def node98Piece39Output_sector0 : RawPoly ℕ := reflectPoly node98Piece9Output_sector1

def node98Piece39Output_sector1 : RawPoly ℕ := reflectPoly node98Piece9Output_sector0

def node98Piece39Output : SectorVector := [(0, node98Piece39Output_sector0), (2, node98Piece39Output_sector1)]

theorem node98Piece39_check : (reflectVector node98Piece9Output).reverse = node98Piece39Output := by rfl

theorem node98Piece39_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-6)
    (evaluate node98Piece39Input) = evaluate node98Piece39Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-6) _ _ _ _
    node98Piece9_value (by decide +kernel) node98Piece39_check

def node98Piece40Input_sector0 : RawPoly ℕ := [(-924, [0, 1, 3, 5])]

def node98Piece40Input : SectorVector := [(1, node98Piece40Input_sector0)]
def node98Piece40Output_sector0 : RawPoly ℕ := reflectPoly node98Piece10Output_sector1

def node98Piece40Output_sector1 : RawPoly ℕ := reflectPoly node98Piece10Output_sector0

def node98Piece40Output : SectorVector := [(0, node98Piece40Output_sector0), (2, node98Piece40Output_sector1)]

theorem node98Piece40_check : (reflectVector node98Piece10Output).reverse = node98Piece40Output := by rfl

theorem node98Piece40_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-6)
    (evaluate node98Piece40Input) = evaluate node98Piece40Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-6) _ _ _ _
    node98Piece10_value (by decide +kernel) node98Piece40_check

def node98Piece41Input_sector0 : RawPoly ℕ := [(1170, [0, 1, 4, 4])]

def node98Piece41Input : SectorVector := [(1, node98Piece41Input_sector0)]
def node98Piece41Output_sector0 : RawPoly ℕ := reflectPoly node98Piece11Output_sector1

def node98Piece41Output_sector1 : RawPoly ℕ := reflectPoly node98Piece11Output_sector0

def node98Piece41Output : SectorVector := [(0, node98Piece41Output_sector0), (2, node98Piece41Output_sector1)]

theorem node98Piece41_check : (reflectVector node98Piece11Output).reverse = node98Piece41Output := by rfl

theorem node98Piece41_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-6)
    (evaluate node98Piece41Input) = evaluate node98Piece41Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-6) _ _ _ _
    node98Piece11_value (by decide +kernel) node98Piece41_check

def node98Piece42Input_sector0 : RawPoly ℕ := [(-342, [0, 2, 2, 5])]

def node98Piece42Input : SectorVector := [(1, node98Piece42Input_sector0)]
def node98Piece42Output_sector0 : RawPoly ℕ := reflectPoly node98Piece12Output_sector1

def node98Piece42Output_sector1 : RawPoly ℕ := reflectPoly node98Piece12Output_sector0

def node98Piece42Output : SectorVector := [(0, node98Piece42Output_sector0), (2, node98Piece42Output_sector1)]

theorem node98Piece42_check : (reflectVector node98Piece12Output).reverse = node98Piece42Output := by rfl

theorem node98Piece42_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-6)
    (evaluate node98Piece42Input) = evaluate node98Piece42Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-6) _ _ _ _
    node98Piece12_value (by decide +kernel) node98Piece42_check

def node98Piece43Input_sector0 : RawPoly ℕ := [(1740, [0, 2, 3, 4])]

def node98Piece43Input : SectorVector := [(1, node98Piece43Input_sector0)]
def node98Piece43Output_sector0 : RawPoly ℕ := reflectPoly node98Piece13Output_sector1

def node98Piece43Output_sector1 : RawPoly ℕ := reflectPoly node98Piece13Output_sector0

def node98Piece43Output : SectorVector := [(0, node98Piece43Output_sector0), (2, node98Piece43Output_sector1)]

theorem node98Piece43_check : (reflectVector node98Piece13Output).reverse = node98Piece43Output := by rfl

theorem node98Piece43_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-6)
    (evaluate node98Piece43Input) = evaluate node98Piece43Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-6) _ _ _ _
    node98Piece13_value (by decide +kernel) node98Piece43_check

def node98Piece44Input_sector0 : RawPoly ℕ := [(240, [0, 3, 3, 3])]

def node98Piece44Input : SectorVector := [(1, node98Piece44Input_sector0)]
def node98Piece44Output_sector0 : RawPoly ℕ := reflectPoly node98Piece14Output_sector1

def node98Piece44Output_sector1 : RawPoly ℕ := reflectPoly node98Piece14Output_sector0

def node98Piece44Output : SectorVector := [(0, node98Piece44Output_sector0), (2, node98Piece44Output_sector1)]

theorem node98Piece44_check : (reflectVector node98Piece14Output).reverse = node98Piece44Output := by rfl

theorem node98Piece44_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-6)
    (evaluate node98Piece44Input) = evaluate node98Piece44Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-6) _ _ _ _
    node98Piece14_value (by decide +kernel) node98Piece44_check

def node98Piece45Input_sector0 : RawPoly ℕ := [(8700, [0, 9])]

def node98Piece45Input : SectorVector := [(1, node98Piece45Input_sector0)]
def node98Piece45Output_sector0 : RawPoly ℕ := reflectPoly node98Piece15Output_sector1

def node98Piece45Output_sector1 : RawPoly ℕ := reflectPoly node98Piece15Output_sector0

def node98Piece45Output : SectorVector := [(0, node98Piece45Output_sector0), (2, node98Piece45Output_sector1)]

theorem node98Piece45_check : (reflectVector node98Piece15Output).reverse = node98Piece45Output := by rfl

theorem node98Piece45_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-6)
    (evaluate node98Piece45Input) = evaluate node98Piece45Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-6) _ _ _ _
    node98Piece15_value (by decide +kernel) node98Piece45_check

def node98Piece46Input_sector0 : RawPoly ℕ := [(-76, [1, 1, 1, 1, 1, 1, 1, 2])]

def node98Piece46Input : SectorVector := [(1, node98Piece46Input_sector0)]
def node98Piece46Output_sector0 : RawPoly ℕ := reflectPoly node98Piece16Output_sector1

def node98Piece46Output_sector1 : RawPoly ℕ := reflectPoly node98Piece16Output_sector0

def node98Piece46Output : SectorVector := [(0, node98Piece46Output_sector0), (2, node98Piece46Output_sector1)]

theorem node98Piece46_check : (reflectVector node98Piece16Output).reverse = node98Piece46Output := by rfl

theorem node98Piece46_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-6)
    (evaluate node98Piece46Input) = evaluate node98Piece46Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-6) _ _ _ _
    node98Piece16_value (by decide +kernel) node98Piece46_check

def node98Piece47Input_sector0 : RawPoly ℕ := [(-570, [1, 1, 1, 1, 1, 4])]

def node98Piece47Input : SectorVector := [(1, node98Piece47Input_sector0)]
def node98Piece47Output_sector0 : RawPoly ℕ := reflectPoly node98Piece17Output_sector1

def node98Piece47Output_sector1 : RawPoly ℕ := reflectPoly node98Piece17Output_sector0

def node98Piece47Output : SectorVector := [(0, node98Piece47Output_sector0), (2, node98Piece47Output_sector1)]

theorem node98Piece47_check : (reflectVector node98Piece17Output).reverse = node98Piece47Output := by rfl

theorem node98Piece47_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-6)
    (evaluate node98Piece47Input) = evaluate node98Piece47Output := by
  exact mode_of_reflection (EP 4 four_ge_one) (-6) _ _ _ _
    node98Piece17_value (by decide +kernel) node98Piece47_check

end VOA.Classification.COne.OrbC2h
