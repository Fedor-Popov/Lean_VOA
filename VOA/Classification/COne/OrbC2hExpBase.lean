import VOA.Classification.COne.OrbC2hSchurReduced
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational HeisenbergN
  PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def expFast : List ℕ → ℤ → RawPoly ℕ
  | [], s => if 0 ≤ s then schurMemo s.toNat else []
  | 0 :: w, s => prependC 0 (expFast w s)
  | (i+1) :: w, s => fastNormFuel (prependC (i+1) (expFast w s) ++
      scaleR (-1) (prependC 0 (expFast w (s+i+1))))

theorem expFast_sound {r : ℕ} (a : Fin r) (c : ℂ) (w : List ℕ) (s : ℤ) :
    evRc a c (expFast w s) = evRc a c (expWordR w s) := by
  induction w generalizing s with
  | nil => simp only [expFast, expWordR]; split_ifs <;> simp only [schurMemo_sound]
  | cons i w ih =>
    cases i <;> simp only [expFast, expWordR, evRc_normR, evRc_fastNormFuel, evRc_append,
      evRc_scaleR, evRc_prependC, ih]

def expPolyFast (s : ℤ) (P : RawPoly ℕ) : RawPoly ℕ :=
  fastNormFuel (P.flatMap fun t => scaleR t.1 (expFast t.2 s))

theorem expPolyFast_sound {r : ℕ} (a : Fin r) (c : ℂ) (s : ℤ) (P : RawPoly ℕ) :
    evRc a c (expPolyFast s P) = evRc a c (expPolyR s P) := by
  simp only [expPolyFast, expPolyR, evRc_normR, evRc_fastNormFuel, evRc_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  rw [evRc_scaleR, evRc_scaleR, expFast_sound]

/-- Charge reduction at every exponential step; valid when the charge square is eight. -/
def expReduced : List ℕ → ℤ → RawPoly ℕ
  | [], s => if 0 ≤ s then schurReducedMemo s.toNat else []
  | 0 :: w, s => prependC 0 (expReduced w s)
  | (i+1) :: w, s => fastReduce (prependC (i+1) (expReduced w s) ++
      scaleR (-1) (prependC 0 (expReduced w (s+i+1))))

theorem expReduced_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c*c = ((8:ℚ):ℂ)) (w : List ℕ) (s : ℤ) :
    evRc a c (expReduced w s) = evRc a c (expWordR w s) := by
  induction w generalizing s with
  | nil =>
    simp only [expReduced, expWordR]
    split_ifs <;> simp only [schurReducedMemo_sound _ _ hc, schurMemo_sound]
  | cons i w ih =>
    cases i <;> simp only [expReduced, expWordR, evRc_normR,
      evRc_fastReduce_of_sq _ _ hc, evRc_append, evRc_scaleR, evRc_prependC, ih]

end VOA.Classification.COne.OrbC2h
