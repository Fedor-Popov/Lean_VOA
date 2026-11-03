import VOA.Classification.COne.OrbIcoVCasimir

/-! Scalar first-oscillator evaluation of the already-certified screening state.
No oscillator expansion is needed. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  VOA.SparseRational PlusC2Eval OrbIco OrbPrim OrbRat6 OrbIcoT OrbOctaR

abbrev firstProbe := OrbOctaR.firstOscillator

theorem firstProbe_vVar (a : (latP 1).carrier) (j : ℕ) :
    firstProbe (vVar (latP 1) a j) =
      if j = 0 then chargeCoord (latP 1) a (LatMod.a0 1) else 0 := by
  rw [vVar, map_sum]
  have hu : ∀ i : Fin (rank (latP 1)), i = LatMod.a0 1 := by
    intro i
    have hi : i.val < 1 := by simpa [rank_latP] using i.isLt
    apply Fin.ext
    simp only [LatMod.a0, Fin.val_mk]
    omega
  rw [Finset.sum_eq_single (LatMod.a0 1)]
  · simp [firstProbe, OrbOctaR.firstOscillator]
  · intro b _ hb
    exact (hb (hu b)).elim
  · simp

theorem firstProbe_vSchur (a : (latP 1).carrier) (n : ℕ) :
    firstProbe (vSchur (latP 1) a n) =
      chargeCoord (latP 1) a (LatMod.a0 1) ^ n / (n.factorial : ℂ) := by
  induction n with
  | zero => simp [vSchur_zero]
  | succ n ih =>
    rw [vSchur_succ, map_smul, map_sum]
    have hs : ∑ j ∈ Finset.range (n + 1),
        firstProbe (vVar (latP 1) a j * vSchur (latP 1) a (n - j)) =
        chargeCoord (latP 1) a (LatMod.a0 1) * firstProbe (vSchur (latP 1) a n) := by
      rw [Finset.sum_eq_single 0]
      · simp [map_mul, firstProbe_vVar]
      · intro j _ hj
        simp [map_mul, firstProbe_vVar, hj]
      · simp
    rw [hs, ih, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    simp only [smul_eq_mul, pow_succ, div_eq_mul_inv, mul_inv_rev]
    ring

def schurWeight (w : List ℕ) : ℚ :=
  (w.map fun j => (j.factorial : ℚ)⁻¹).prod

theorem firstProbe_shWord (w : List ℕ) :
    firstProbe (shWord w) =
      chargeCoord (latP 1) (-1 : ℤ) (LatMod.a0 1) ^ w.sum * (schurWeight w : ℂ) := by
  induction w with
  | nil => simp [shWord_nil, schurWeight]
  | cons i w ih =>
    rw [shWord_cons, map_mul, firstProbe_vSchur, ih]
    simp only [List.sum_cons, schurWeight, List.map_cons, List.prod_cons,
      Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast, pow_add, div_eq_mul_inv]
    ring

def schurProbeSum (P : RawPoly ℕ) : ℚ :=
  (P.map fun t => t.1 * schurWeight t.2).sum

theorem firstProbe_shEval (P : RawPoly ℕ) (N : ℕ)
    (h : ∀ t ∈ P, t.2.sum = N) :
    firstProbe (shEval P) =
      chargeCoord (latP 1) (-1 : ℤ) (LatMod.a0 1) ^ N * (schurProbeSum P : ℂ) := by
  induction P with
  | nil => simp [shEval_nil, schurProbeSum]
  | cons t P ih =>
    rw [shEval_cons, map_add, map_smul, firstProbe_shWord,
      (h t (by simp)), ih (fun t ht => h t (by simp [ht]))]
    simp only [schurProbeSum, List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_mul,
      smul_eq_mul]
    ring

end VOA.Classification.COne.OrbIcoV
