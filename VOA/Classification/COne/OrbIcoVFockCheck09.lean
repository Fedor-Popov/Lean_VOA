import VOA.Classification.COne.OrbIcoVFockData

set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 16384
namespace VOA.Classification.COne.OrbIcoV
open VOA.SparseRational

theorem fockBSAData_step_9 :
    normalizeQ (rawScale 36 (rawPrepend 0 (fockBSAData 9)) ++ fockBSASourceData 9) = [] := by
  set_option maxHeartbeats 20000000 in
  decide +kernel

end VOA.Classification.COne.OrbIcoV
