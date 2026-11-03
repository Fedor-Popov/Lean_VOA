import VOA.Classification.COne.OrbIcoVVacSparse

/-! Fixed PBW-word coefficient continuity in the actual vacuum family. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA HeisenbergN MvPolynomial VOA.SparseRational VOA.VirasoroScreening
  InverseDS.VirasoroVerma InverseDS.LeeYangFockVirasoro Filter Topology

def vacDescData : List ℕ → RawPoly ℕ
  | [] => [(1, [])]
  | k::w => vacRawMode (k+1) (vacDescData w)

theorem vacDescData_sound (s : ℂ) (hs : s ≠ 0) (w : List ℕ) :
    vacFamilyMap s (negWord (familyCharge s) (vacFamilyWeight s) w) =
      fockRawEval s (vacDescData w) := by
  induction w with
  | nil =>
    rw [negWord_nil, vacFamilyMap, chargedFockMap, universalMap_highestVector]
    simp [vacDescData, fockRawEval, evalRaw, evalWord, vacuumN]
  | cons k w ih =>
    rw [negWord_cons, vacFamilyMap, chargedFockMap_mode]
    change sectorVirasoro _ _ (-(k:ℤ)-1) (vacFamilyMap s (negWord _ _ w)) = _
    rw [ih, vacDescData, vacRawMode_sound s hs (k+1) (by omega)]
    rw [show -((k+1 : ℕ) : ℤ) = -(k : ℤ)-1 by omega]

def vacLevelCoefficient (N : ℕ) (a : VermaPartitions N → ℂ)
    (s : ℂ) (d : (ℕ × Fin 1) →₀ ℕ) : ℂ :=
  ∑ w : VermaPartitions N, a w * coeff d (fockRawEval s (vacDescData w.val))

theorem vacLevelCoefficient_sound (N : ℕ) (a : VermaPartitions N → ℂ)
    (s : ℂ) (hs : s ≠ 0) (d : (ℕ × Fin 1) →₀ ℕ) :
    coeff d (vacFamilyMap s (vermaLevelState (familyCharge s) (vacFamilyWeight s) N a)) =
      vacLevelCoefficient N a s d := by
  simp only [vermaLevelState, map_sum, map_smul, vacLevelCoefficient,
    MvPolynomial.coeff_sum, coeff_smul, vacDescData_sound s hs]
  rfl

theorem vacLevelCoefficient_continuousAt (N : ℕ) (a : VermaPartitions N → ℂ)
    (s₀ : ℂ) (hs : s₀ ≠ 0) (d : (ℕ × Fin 1) →₀ ℕ) :
    ContinuousAt (fun s => vacLevelCoefficient N a s d) s₀ := by
  unfold vacLevelCoefficient
  apply tendsto_finsetSum
  intro w hw
  exact continuousAt_const.mul (fockRawEval_coeff_continuousAt s₀ hs _ d)


end VOA.Classification.COne.OrbIcoV
