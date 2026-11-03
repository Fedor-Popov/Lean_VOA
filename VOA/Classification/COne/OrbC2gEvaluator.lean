import VOA.Classification.COne.OrbC2fRemainders

/-! # Charge-sector arithmetic for the tetrahedral certificates

The symbolic variable zero always denotes the fundamental charge coordinate,
including in the neutral sector. Other variables denote oscillators. This
allows repeated charged and neutral left actions without changing coordinates.
-/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
namespace VOA.Classification.COne.OrbC2g
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  MvPolynomial VOA.SparseRational PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e LatMod

/-- Substitute `d*c` for the symbolic charge variable. -/
def chargeScale (d : ℚ) (P : RawPoly ℕ) : RawPoly ℕ :=
  P.map fun t => (d ^ t.2.count 0 * t.1, t.2)

theorem evRc_chargeScale {r : ℕ} (a : Fin r) (c : ℂ) (d : ℚ) (P : RawPoly ℕ) :
    evRc a c (chargeScale d P) = evRc a ((d : ℂ) * c) P := by
  have hw : ∀ w : List ℕ, evalWord (xvc a ((d : ℂ) * c)) w =
      ((d : ℂ) ^ w.count 0) • evalWord (xvc a c) w := by
    intro w
    induction w with
    | nil => simp [evalWordC_nil]
    | cons i w ih =>
      rw [evalWordC_cons, evalWordC_cons, ih]
      cases i with
      | zero => simp [xvc, pow_succ, MvPolynomial.smul_eq_C_mul]; ring
      | succ i => simp [xvc]
  induction P with
  | nil => rfl
  | cons t P ih =>
    rcases t with ⟨q,w⟩
    rw [chargeScale, List.map_cons, evRc_cons, evRc_cons, hw]
    change _ + evRc a c (chargeScale d P) = _
    rw [ih, smul_smul]
    push_cast
    rw [mul_comm (q : ℂ)]

/-- Delete scalar variables, and return to the neutral oscillator indexing. -/
def oscillators : List ℕ → List ℕ
  | [] => []
  | 0 :: w => oscillators w
  | (i+1) :: w => i :: oscillators w

theorem evalWord_split {r : ℕ} (a : Fin r) (c : ℂ) (w : List ℕ) :
    evalWord (xvc a c) w = c ^ w.count 0 • evalWord (xv a) (oscillators w) := by
  induction w with
  | nil => simp [oscillators, evalWordC_nil, evalWord_nil]
  | cons i w ih =>
    rw [evalWordC_cons, ih]
    cases i with
    | zero => simp [oscillators, xvc, pow_succ, MvPolynomial.smul_eq_C_mul]; ring
    | succ i => simp [oscillators, xvc, evalWord_cons]

/-- Multiply a polynomial by `c^k`. -/
def chargePower : ℕ → RawPoly ℕ → RawPoly ℕ
  | 0, P => P
  | k+1, P => prependC 0 (chargePower k P)

theorem evRc_chargePower {r : ℕ} (a : Fin r) (c : ℂ) (k : ℕ) (P : RawPoly ℕ) :
    evRc a c (chargePower k P) = c^k • evRc a c P := by
  induction k with
  | zero => simp [chargePower]
  | succ k ih =>
    rw [chargePower, evRc_prependC, ih]
    simp [xvc, pow_succ, MvPolynomial.smul_eq_C_mul]
    ring

/-- Apply an operation to oscillator words while retaining scalar charge powers. -/
def onOscillators (f : RawPoly ℕ → RawPoly ℕ) (P : RawPoly ℕ) : RawPoly ℕ :=
  P.flatMap fun t => scaleR t.1 (chargePower (t.2.count 0) (f [(1, oscillators t.2)]))

/-- Neutral-left action, with right charge `d` in fundamental-charge units. -/
def neutralAction (Q : RawPoly ℕ) (n d : ℤ) (P : RawPoly ℕ) : RawPoly ℕ :=
  reduceR 8 (onOscillators
    (fun R => chargeScale d (polyActWC Q (-n-1) (liftR R))) P)

/-- Exponential-left action, with left/right charges `b,d`. -/
def exponentialAction (b d n : ℤ) (P : RawPoly ℕ) : RawPoly ℕ :=
  reduceR 8 (onOscillators
    (fun R => chargeScale b (expPolyR (-n-1-8*b*d) (liftR R))) P)

section Semantics
variable {r : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem onOscillators_sound (a : Fin r) (c : ℂ)
    (f g : FockN r →ₗ[ℂ] M) (F : RawPoly ℕ → RawPoly ℕ)
    (hF : ∀ R, f (evRc a c (F R)) = g (evR a R)) (P : RawPoly ℕ) :
    f (evRc a c (onOscillators F P)) = g (evRc a c P) := by
  induction P with
  | nil => simp [onOscillators, evRc_nil]
  | cons t P ih =>
    rcases t with ⟨q,w⟩
    simp only [onOscillators] at ih
    rw [onOscillators, List.flatMap_cons, evRc_append, map_add,
      evRc_scaleR, map_smul, evRc_chargePower, map_smul, hF, ih,
      evRc_cons, map_add, map_smul, evalWord_split, map_smul]
    simp [evR_cons, evR_nil]

end Semantics

noncomputable def sector (d : ℤ) : FockN (rank (latP 4)) →ₗ[ℂ] LatModuleGen (latP 4) where
  toFun p := latStateGen (latP 4) p d
  map_add' := fun _ _ => latStateGen_add_boson _ _ _ _
  map_smul' := fun _ _ => latStateGen_csmul _ _ _ _

theorem chargeCoord_four (d : ℤ) :
    chargeCoord (latP 4) d (a0 4) = (d : ℂ) * cα 4 := by
  have h (k : ℕ) : chargeCoord (latP 4) (k : ℤ) (a0 4) = (k : ℂ) * cα 4 := by
    induction k with
    | zero =>
      simpa only [Nat.cast_zero, zero_mul] using chargeCoord_zero (latP 4) (a0 4)
    | succ k ih =>
      have hh := chargeCoord_add (latP 4) ((k : ℤ) : (latP 4).carrier)
        ((1 : ℤ) : (latP 4).carrier) (a0 4)
      change chargeCoord (latP 4) (↑k+1 : ℤ) (a0 4) =
        chargeCoord (latP 4) (k : ℤ) (a0 4) + cα 4 at hh
      rw [Nat.cast_succ, hh, ih]
      push_cast
      ring
  cases d with
  | ofNat k => exact h k
  | negSucc k =>
    have hh := OrbC2e.chargeCoord_neg (latP 4)
      ((↑(k+1) : ℤ) : (latP 4).carrier) (a0 4)
    change chargeCoord (latP 4) (-(↑(k+1) : ℤ)) (a0 4) =
      -chargeCoord (latP 4) (↑(k+1) : ℤ) (a0 4) at hh
    change chargeCoord (latP 4) (-(↑(k+1) : ℤ)) (a0 4) = _
    rw [hh, h]
    push_cast
    ring

theorem evRc_reduce_eight (P : RawPoly ℕ) :
    evRc (a0 4) (cα 4) (reduceR 8 P) = evRc (a0 4) (cα 4) P := by
  apply evRc_reduceR
  convert cα_sq 4 four_ge_one using 1
  norm_num

/-- Correctness of neutral-left evaluation in every integral charge sector. -/
theorem neutralAction_sound (Q P : RawPoly ℕ) (n d : ℤ) :
    (V2m 4 four_ge_one).smul (ls 4 Q) n (sector d (evRc (a0 4) (cα 4) P)) =
      sector d (evRc (a0 4) (cα 4) (neutralAction Q n d P)) := by
  let g := (mode ((V2m 4 four_ge_one).Y (ls 4 Q)) n).comp (sector d)
  rw [neutralAction, evRc_reduce_eight]
  symm
  apply onOscillators_sound (a0 4) (cα 4) (sector d) g
  intro R
  rw [evRc_chargeScale]
  norm_cast
  rw [← chargeCoord_four]
  have h := V2m_smul_evRcW 4 four_ge_one Q n d (liftR R)
  rw [evRc_liftR] at h
  exact h.symm

/-- Correctness of exponential-left evaluation, including the output charge. -/
theorem exponentialAction_sound (b d n : ℤ) (P : RawPoly ℕ) :
    (V2m 4 four_ge_one).smul (latChargeGen (latP 4) b) n
        (sector d (evRc (a0 4) (cα 4) P)) =
      sector (b+d) (evRc (a0 4) (cα 4) (exponentialAction b d n P)) := by
  let g := (mode ((V2m 4 four_ge_one).Y (latChargeGen (latP 4) b)) n).comp (sector d)
  rw [exponentialAction, evRc_reduce_eight]
  symm
  apply onOscillators_sound (a0 4) (cα 4) (sector (b+d)) g
  intro R
  rw [evRc_chargeScale]
  norm_cast
  rw [← chargeCoord_four]
  have h := V2m_charge_smul_evRc 4 four_ge_one b d n (liftR R)
  rw [evRc_liftR, PlusCharacterTable.rankOne_cocycle, one_smul] at h
  simpa only [latP_form, Nat.cast_ofNat, show (2 : ℤ)*4=8 by norm_num] using h.symm

end VOA.Classification.COne.OrbC2g

