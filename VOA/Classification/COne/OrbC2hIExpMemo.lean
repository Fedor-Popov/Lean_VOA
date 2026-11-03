import VOA.Classification.COne.OrbC2hIExpMemoPart10
import VOA.Classification.COne.OrbC2hIExpMemoPart11
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA.SparseRational HeisenbergN PlusC2Eval PlusUnitary OrbC2e

def iExpMemoEntries : List IExpEntry := [iExpMemoEntry0, iExpMemoEntry1, iExpMemoEntry2, iExpMemoEntry3, iExpMemoEntry4, iExpMemoEntry5, iExpMemoEntry6, iExpMemoEntry7, iExpMemoEntry8, iExpMemoEntry9, iExpMemoEntry10, iExpMemoEntry11, iExpMemoEntry12, iExpMemoEntry13, iExpMemoEntry14, iExpMemoEntry15, iExpMemoEntry16, iExpMemoEntry17, iExpMemoEntry18, iExpMemoEntry19, iExpMemoEntry20, iExpMemoEntry21, iExpMemoEntry22, iExpMemoEntry23, iExpMemoEntry24, iExpMemoEntry25, iExpMemoEntry26, iExpMemoEntry27, iExpMemoEntry28, iExpMemoEntry29, iExpMemoEntry30, iExpMemoEntry31, iExpMemoEntry32, iExpMemoEntry33, iExpMemoEntry34, iExpMemoEntry35, iExpMemoEntry36, iExpMemoEntry37, iExpMemoEntry38, iExpMemoEntry39, iExpMemoEntry40, iExpMemoEntry41, iExpMemoEntry42, iExpMemoEntry43, iExpMemoEntry44, iExpMemoEntry45, iExpMemoEntry46, iExpMemoEntry47, iExpMemoEntry48, iExpMemoEntry49, iExpMemoEntry50, iExpMemoEntry51, iExpMemoEntry52, iExpMemoEntry53, iExpMemoEntry54, iExpMemoEntry55, iExpMemoEntry56, iExpMemoEntry57, iExpMemoEntry58, iExpMemoEntry59, iExpMemoEntry60, iExpMemoEntry61, iExpMemoEntry62, iExpMemoEntry63, iExpMemoEntry64, iExpMemoEntry65, iExpMemoEntry66, iExpMemoEntry67, iExpMemoEntry68, iExpMemoEntry69, iExpMemoEntry70, iExpMemoEntry71, iExpMemoEntry72, iExpMemoEntry73, iExpMemoEntry74, iExpMemoEntry75, iExpMemoEntry76, iExpMemoEntry77, iExpMemoEntry78, iExpMemoEntry79, iExpMemoEntry80, iExpMemoEntry81, iExpMemoEntry82, iExpMemoEntry83, iExpMemoEntry84, iExpMemoEntry85, iExpMemoEntry86, iExpMemoEntry87, iExpMemoEntry88, iExpMemoEntry89, iExpMemoEntry90, iExpMemoEntry91, iExpMemoEntry92, iExpMemoEntry93, iExpMemoEntry94, iExpMemoEntry95, iExpMemoEntry96, iExpMemoEntry97, iExpMemoEntry98, iExpMemoEntry99, iExpMemoEntry100, iExpMemoEntry101, iExpMemoEntry102, iExpMemoEntry103, iExpMemoEntry104, iExpMemoEntry105, iExpMemoEntry106, iExpMemoEntry107, iExpMemoEntry108, iExpMemoEntry109, iExpMemoEntry110, iExpMemoEntry111, iExpMemoEntry112, iExpMemoEntry113, iExpMemoEntry114, iExpMemoEntry115, iExpMemoEntry116, iExpMemoEntry117, iExpMemoEntry118, iExpMemoEntry119, iExpMemoEntry120, iExpMemoEntry121, iExpMemoEntry122, iExpMemoEntry123, iExpMemoEntry124, iExpMemoEntry125, iExpMemoEntry126, iExpMemoEntry127, iExpMemoEntry128, iExpMemoEntry129, iExpMemoEntry130, iExpMemoEntry131, iExpMemoEntry132, iExpMemoEntry133, iExpMemoEntry134, iExpMemoEntry135, iExpMemoEntry136, iExpMemoEntry137, iExpMemoEntry138, iExpMemoEntry139, iExpMemoEntry140, iExpMemoEntry141, iExpMemoEntry142, iExpMemoEntry143, iExpMemoEntry144, iExpMemoEntry145, iExpMemoEntry146, iExpMemoEntry147, iExpMemoEntry148, iExpMemoEntry149, iExpMemoEntry150, iExpMemoEntry151, iExpMemoEntry152, iExpMemoEntry153, iExpMemoEntry154, iExpMemoEntry155, iExpMemoEntry156, iExpMemoEntry157, iExpMemoEntry158, iExpMemoEntry159, iExpMemoEntry160, iExpMemoEntry161, iExpMemoEntry162, iExpMemoEntry163, iExpMemoEntry164, iExpMemoEntry165, iExpMemoEntry166, iExpMemoEntry167, iExpMemoEntry168, iExpMemoEntry169, iExpMemoEntry170, iExpMemoEntry171, iExpMemoEntry172, iExpMemoEntry173, iExpMemoEntry174, iExpMemoEntry175, iExpMemoEntry176, iExpMemoEntry177, iExpMemoEntry178, iExpMemoEntry179, iExpMemoEntry180, iExpMemoEntry181, iExpMemoEntry182, iExpMemoEntry183, iExpMemoEntry184, iExpMemoEntry185, iExpMemoEntry186]

def expIntegerMemo (w : List ℕ) (s : ℤ) : RawPoly ℕ :=
  if s + (w.sum:ℤ) ≤ 22 then
    scaleR (1/(expDen:ℚ)) (toRatPoly (iExpUsing iExpMemoEntries w s))
  else expCached w s

theorem expIntegerMemo_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c*c = ((8:ℚ):ℂ)) (w : List ℕ) (s : ℤ) :
    evRc a c (expIntegerMemo w s) = evRc a c (expWordR w s) := by
  rw [expIntegerMemo]
  split_ifs with hn
  · rw [evRc_scaleR]
    change (((1/(expDen:ℚ):ℚ):ℂ)) • iEval a c (iExpUsing iExpMemoEntries w s) = _
    rw [iExpUsing_sound _ _ _ hc _ _ hn, smul_smul]
    have hq : (((1/(expDen:ℚ):ℚ):ℂ)) * (expDen:ℂ) = 1 := by norm_num [expDen]
    rw [hq, one_smul]
  · exact expCached_sound a c hc w s
end VOA.Classification.COne.OrbC2h
