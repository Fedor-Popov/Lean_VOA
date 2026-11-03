import VOA.Classification.COne.OrbC2hSeed16
import VOA.Classification.COne.OrbC2hDirectNeutral
import VOA.Classification.COne.OrbC2hSumPieces
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

theorem virWord_cached_step (k : ℕ) (ks : List ℕ) (v : LatModuleGen (latP 4))
    (S T : SectorVector)
    (hp : evaluate S = virWord (V2m 4 four_ge_one) ks v)
    (hc : neutralDirectS omR (-(k:ℤ)) S = T) :
    evaluate T = virWord (V2m 4 four_ge_one) (k::ks) v := by
  rw [← hc, evaluate_neutralDirectS, hp, virWord]
  have ho : ls 4 omR = (V2m 4 four_ge_one).conformalVector := (omega_coe 4 four_ge_one).symm
  rw [ho]
  change (V2m 4 four_ge_one).smul _ (-(k:ℤ)) _ =
    (V2m 4 four_ge_one).smul _ (-(k:ℤ)-1+1) _
  rw [sub_add_cancel]

end VOA.Classification.COne.OrbC2h
