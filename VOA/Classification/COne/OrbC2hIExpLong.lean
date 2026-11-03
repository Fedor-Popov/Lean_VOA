import VOA.Classification.COne.OrbC2hIExpLongPart8
import VOA.Classification.COne.OrbC2hIExpLongPart9
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA.SparseRational HeisenbergN PlusC2Eval PlusUnitary OrbC2e

def iExpLongEntries : List IExpEntry := [iExpLongEntry0, iExpLongEntry1, iExpLongEntry2, iExpLongEntry3, iExpLongEntry4, iExpLongEntry5, iExpLongEntry6, iExpLongEntry7, iExpLongEntry8, iExpLongEntry9, iExpLongEntry10, iExpLongEntry11, iExpLongEntry12, iExpLongEntry13, iExpLongEntry14, iExpLongEntry15, iExpLongEntry16, iExpLongEntry17, iExpLongEntry18, iExpLongEntry19, iExpLongEntry20, iExpLongEntry21, iExpLongEntry22, iExpLongEntry23, iExpLongEntry24, iExpLongEntry25, iExpLongEntry26, iExpLongEntry27, iExpLongEntry28, iExpLongEntry29, iExpLongEntry30, iExpLongEntry31, iExpLongEntry32, iExpLongEntry33, iExpLongEntry34, iExpLongEntry35, iExpLongEntry36, iExpLongEntry37, iExpLongEntry38, iExpLongEntry39, iExpLongEntry40, iExpLongEntry41, iExpLongEntry42, iExpLongEntry43, iExpLongEntry44, iExpLongEntry45, iExpLongEntry46, iExpLongEntry47, iExpLongEntry48, iExpLongEntry49, iExpLongEntry50, iExpLongEntry51, iExpLongEntry52, iExpLongEntry53, iExpLongEntry54, iExpLongEntry55, iExpLongEntry56, iExpLongEntry57, iExpLongEntry58, iExpLongEntry59, iExpLongEntry60, iExpLongEntry61, iExpLongEntry62, iExpLongEntry63, iExpLongEntry64, iExpLongEntry65, iExpLongEntry66, iExpLongEntry67, iExpLongEntry68, iExpLongEntry69, iExpLongEntry70, iExpLongEntry71, iExpLongEntry72, iExpLongEntry73, iExpLongEntry74, iExpLongEntry75, iExpLongEntry76, iExpLongEntry77, iExpLongEntry78, iExpLongEntry79, iExpLongEntry80, iExpLongEntry81, iExpLongEntry82, iExpLongEntry83, iExpLongEntry84, iExpLongEntry85, iExpLongEntry86, iExpLongEntry87, iExpLongEntry88, iExpLongEntry89, iExpLongEntry90, iExpLongEntry91, iExpLongEntry92, iExpLongEntry93, iExpLongEntry94, iExpLongEntry95, iExpLongEntry96, iExpLongEntry97, iExpLongEntry98, iExpLongEntry99, iExpLongEntry100, iExpLongEntry101, iExpLongEntry102, iExpLongEntry103, iExpLongEntry104, iExpLongEntry105, iExpLongEntry106, iExpLongEntry107, iExpLongEntry108, iExpLongEntry109, iExpLongEntry110, iExpLongEntry111, iExpLongEntry112, iExpLongEntry113, iExpLongEntry114, iExpLongEntry115, iExpLongEntry116, iExpLongEntry117, iExpLongEntry118, iExpLongEntry119, iExpLongEntry120, iExpLongEntry121, iExpLongEntry122, iExpLongEntry123, iExpLongEntry124, iExpLongEntry125, iExpLongEntry126, iExpLongEntry127, iExpLongEntry128, iExpLongEntry129, iExpLongEntry130, iExpLongEntry131, iExpLongEntry132, iExpLongEntry133, iExpLongEntry134, iExpLongEntry135, iExpLongEntry136, iExpLongEntry137, iExpLongEntry138, iExpLongEntry139, iExpLongEntry140, iExpLongEntry141, iExpLongEntry142, iExpLongEntry143, iExpLongEntry144, iExpLongEntry145, iExpLongEntry146, iExpLongEntry147] ++ iExpMemoEntries

def expIntegerLong (w : List ℕ) (s : ℤ) : RawPoly ℕ :=
  if s + (w.sum:ℤ) ≤ 22 then
    scaleR (1/(expDen:ℚ)) (toRatPoly (iExpUsing iExpLongEntries w s))
  else expCached w s

theorem expIntegerLong_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c*c = ((8:ℚ):ℂ)) (w : List ℕ) (s : ℤ) :
    evRc a c (expIntegerLong w s) = evRc a c (expWordR w s) := by
  rw [expIntegerLong]
  split_ifs with hn
  · rw [evRc_scaleR]
    change (((1/(expDen:ℚ):ℚ):ℂ)) • iEval a c (iExpUsing iExpLongEntries w s) = _
    rw [iExpUsing_sound _ _ _ hc _ _ hn, smul_smul]
    have hq : (((1/(expDen:ℚ):ℚ):ℂ)) * (expDen:ℂ) = 1 := by norm_num [expDen]
    rw [hq, one_smul]
  · exact expCached_sound a c hc w s
end VOA.Classification.COne.OrbC2h
