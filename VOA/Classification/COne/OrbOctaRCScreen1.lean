import VOA.Classification.COne.OrbOctaRCScreenBlocks
import VOA.Classification.COne.OrbOctaRCScreenCache00

/-! One exact screening step, checked in blocks of eight source monomials. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbOctaRC
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational HeisenbergN
  PlusC2Eval PlusUnitary PlusC2 OrbC2e OrbC2g OrbC2h LatMod OrbRat6 OrbPrim

def screenState0 : RawPoly ℕ :=
  [(1, [])]

def screenState1 : RawPoly ℕ :=
  [(-1 / 630, [0, 1, 1, 1, 1, 1, 1, 1]),
   (-1 / 18, [0, 1, 1, 1, 1, 3]),
   (-1 / 12, [0, 1, 1, 1, 2, 2]),
   (-1 / 5, [0, 1, 1, 5]),
   (-1 / 4, [0, 1, 2, 4]),
   (-1 / 9, [0, 1, 3, 3]),
   (-1 / 12, [0, 2, 2, 3]),
   (-1 / 7, [0, 7]),
   (1 / 30, [1, 1, 1, 1, 1, 2]),
   (1 / 6, [1, 1, 1, 4]),
   (1 / 3, [1, 1, 2, 3]),
   (1 / 12, [1, 2, 2, 2]),
   (1 / 3, [1, 6]),
   (1 / 5, [2, 5]),
   (1 / 6, [3, 4])]

def screen1Input0 : RawPoly ℕ :=
  [(1, [])]

def screen1Row0 : RawPoly ℕ :=
  [(-1 / 630, [0, 1, 1, 1, 1, 1, 1, 1]),
   (-1 / 18, [0, 1, 1, 1, 1, 3]),
   (-1 / 12, [0, 1, 1, 1, 2, 2]),
   (-1 / 5, [0, 1, 1, 5]),
   (-1 / 4, [0, 1, 2, 4]),
   (-1 / 9, [0, 1, 3, 3]),
   (-1 / 12, [0, 2, 2, 3]),
   (-1 / 7, [0, 7]),
   (1 / 30, [1, 1, 1, 1, 1, 2]),
   (1 / 6, [1, 1, 1, 4]),
   (1 / 3, [1, 1, 2, 3]),
   (1 / 12, [1, 2, 2, 2]),
   (1 / 3, [1, 6]),
   (1 / 5, [2, 5]),
   (1 / 6, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen1Row0_check :
    screenTerm (1, []) sc14 = screen1Row0 := by
  decide +kernel

theorem screen1Row0_sound :
    fo (sector (4) (evRc (a0 1) (cα 1) [(1, [])])) =
      sector (4 - 1) (evRc (a0 1) (cα 1) screen1Row0) := by
  rw [← screen1Row0_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc14_sound (a0 1) c hc)

def screen1Rows0 : List (RawPoly ℕ) :=
  [screen1Row0]

def screen1Result0 : RawPoly ℕ :=
  [(-1 / 630, [0, 1, 1, 1, 1, 1, 1, 1]),
   (-1 / 18, [0, 1, 1, 1, 1, 3]),
   (-1 / 12, [0, 1, 1, 1, 2, 2]),
   (-1 / 5, [0, 1, 1, 5]),
   (-1 / 4, [0, 1, 2, 4]),
   (-1 / 9, [0, 1, 3, 3]),
   (-1 / 12, [0, 2, 2, 3]),
   (-1 / 7, [0, 7]),
   (1 / 30, [1, 1, 1, 1, 1, 2]),
   (1 / 6, [1, 1, 1, 4]),
   (1 / 3, [1, 1, 2, 3]),
   (1 / 12, [1, 2, 2, 2]),
   (1 / 3, [1, 6]),
   (1 / 5, [2, 5]),
   (1 / 6, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Merge eight certified screening rows.
set_option maxRecDepth 8192 in
theorem screen1Result0_check : reduceTwo screen1Rows0.flatten = screen1Result0 := by
  decide +kernel

theorem screen1Result0_sound :
    fo (sector (4) (evRc (a0 1) (cα 1) screen1Input0)) =
      sector (4 - 1) (evRc (a0 1) (cα 1) screen1Result0) := by
  apply screenRows_reduce _ _ screen1Rows0 _ _ screen1Result0_check
  exact .cons screen1Row0_sound .nil

def screen1Inputs : List (RawPoly ℕ) :=
  [screen1Input0]

def screen1Results : List (RawPoly ℕ) :=
  [screen1Result0]

set_option maxHeartbeats 3000000 in
-- Reassemble the finite input partition.
set_option maxRecDepth 8192 in
theorem screen1_inputs :
    screenState0 = screen1Inputs.flatten := by
  decide +kernel

set_option maxHeartbeats 3000000 in
-- Merge the independently certified screening blocks.
set_option maxRecDepth 8192 in
theorem screen1_results :
    reduceTwo screen1Results.flatten = screenState1 := by
  decide +kernel

theorem screen1_step :
    fo (sector (4) (evRc (a0 1) (cα 1) screenState0)) =
      sector (3) (evRc (a0 1) (cα 1) screenState1) := by
  rw [screen1_inputs]
  apply screenBlocks_reduce _ _ _ _ _ screen1_results
  exact .cons screen1Result0_sound .nil

theorem vn4_1_value :
    vn 4 1 = sector (3) (evRc (a0 1) (cα 1) screenState1) := by
  have hv : vn 4 1 = fo (vn 4 0) := by
    simp only [vn, pow_succ', Module.End.mul_apply]
  rw [hv]
  have h0 : vn 4 0 = sector 4 (evRc (a0 1) (cα 1) screenState0) := by
    simp [vn, screenState0, evRc_cons, evRc_nil, evalWordC_nil, sector]
    rfl
  rw [h0]
  exact screen1_step

end VOA.Classification.COne.OrbOctaRC
