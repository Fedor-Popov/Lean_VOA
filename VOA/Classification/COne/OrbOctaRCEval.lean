import VOA.Classification.COne.OrbOctaRSpan
import VOA.Classification.COne.OrbC2hExpBase

/-! Certified charge-sector evaluation for the norm-two lattice. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbOctaRC
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  MvPolynomial VOA.SparseRational PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e
  OrbC2g OrbC2h LatMod

def neutralActionOne (Q : RawPoly ℕ) (n d : ℤ) (P : RawPoly ℕ) : RawPoly ℕ :=
  reduceR 2 (onOscillators
    (fun R => chargeScale d (polyActWC Q (-n-1) (liftR R))) P)

def exponentialActionOne (b d n : ℤ) (P : RawPoly ℕ) : RawPoly ℕ :=
  reduceR 2 (onOscillators
    (fun R => chargeScale b (expPolyR (-n-1-2*b*d) (liftR R))) P)

noncomputable def sector (d : ℤ) : FockN (rank (latP 1)) →ₗ[ℂ] LatModuleGen (latP 1) where
  toFun p := latStateGen (latP 1) p d
  map_add' := fun _ _ => latStateGen_add_boson _ _ _ _
  map_smul' := fun _ _ => latStateGen_csmul _ _ _ _

theorem chargeCoord_one (d : ℤ) :
    chargeCoord (latP 1) d (a0 1) = (d : ℂ) * cα 1 := by
  have h (k : ℕ) : chargeCoord (latP 1) (k : ℤ) (a0 1) = (k : ℂ) * cα 1 := by
    induction k with
    | zero =>
      simpa only [Nat.cast_zero, zero_mul] using chargeCoord_zero (latP 1) (a0 1)
    | succ k ih =>
      have hh := chargeCoord_add (latP 1) ((k : ℤ) : (latP 1).carrier)
        ((1 : ℤ) : (latP 1).carrier) (a0 1)
      change chargeCoord (latP 1) (↑k+1 : ℤ) (a0 1) =
        chargeCoord (latP 1) (k : ℤ) (a0 1) + cα 1 at hh
      rw [Nat.cast_succ, hh, ih]
      push_cast
      ring
  cases d with
  | ofNat k => exact h k
  | negSucc k =>
    have hh := OrbC2e.chargeCoord_neg (latP 1)
      ((↑(k+1) : ℤ) : (latP 1).carrier) (a0 1)
    change chargeCoord (latP 1) (-(↑(k+1) : ℤ)) (a0 1) =
      -chargeCoord (latP 1) (↑(k+1) : ℤ) (a0 1) at hh
    change chargeCoord (latP 1) (-(↑(k+1) : ℤ)) (a0 1) = _
    rw [hh, h]
    push_cast
    ring

theorem evRc_reduce_two (P : RawPoly ℕ) :
    evRc (a0 1) (cα 1) (reduceR 2 P) = evRc (a0 1) (cα 1) P := by
  apply evRc_reduceR
  convert cα_sq 1 le_rfl using 1
  norm_num

/-- Correctness of neutral-left evaluation in every integral charge sector. -/
theorem neutralActionOne_sound (Q P : RawPoly ℕ) (n d : ℤ) :
    (V2m 1 le_rfl).smul (ls 1 Q) n (sector d (evRc (a0 1) (cα 1) P)) =
      sector d (evRc (a0 1) (cα 1) (neutralActionOne Q n d P)) := by
  let g := (mode ((V2m 1 le_rfl).Y (ls 1 Q)) n).comp (sector d)
  rw [neutralActionOne, evRc_reduce_two]
  symm
  apply onOscillators_sound (a0 1) (cα 1) (sector d) g
  intro R
  rw [evRc_chargeScale]
  norm_cast
  rw [← chargeCoord_one]
  have h := V2m_smul_evRcW 1 le_rfl Q n d (liftR R)
  rw [evRc_liftR] at h
  exact h.symm

/-- Correctness of exponential-left evaluation, including the output charge. -/
theorem exponentialActionOne_sound (b d n : ℤ) (P : RawPoly ℕ) :
    (V2m 1 le_rfl).smul (latChargeGen (latP 1) b) n
        (sector d (evRc (a0 1) (cα 1) P)) =
      sector (b+d) (evRc (a0 1) (cα 1) (exponentialActionOne b d n P)) := by
  let g := (mode ((V2m 1 le_rfl).Y (latChargeGen (latP 1) b)) n).comp (sector d)
  rw [exponentialActionOne, evRc_reduce_two]
  symm
  apply onOscillators_sound (a0 1) (cα 1) (sector (b+d)) g
  intro R
  rw [evRc_chargeScale]
  norm_cast
  rw [← chargeCoord_one]
  have h := V2m_charge_smul_evRc 1 le_rfl b d n (liftR R)
  rw [evRc_liftR, PlusCharacterTable.rankOne_cocycle, one_smul] at h
  simpa only [latP_form, Nat.cast_ofNat, show (2 : ℤ)*1=2 by norm_num] using h.symm

end VOA.Classification.COne.OrbOctaRC
