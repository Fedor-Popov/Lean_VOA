import VOA.Classification.COne.OrbC2fRemainders
import VOA.Classification.COne.OrbC2fIterate
import VOA.Modules.Translation

/-! # A multi-sector evaluator for the weight-nine tetrahedral generator in `V₈`

States of the rank-one lattice VOA `V₈ = V2m 4` are represented as finite lists of
`(charge sector, raw polynomial)` pairs.  Raw variable `0` is the fundamental charge
coordinate `cα 4` (with `cα² = 8`), raw variable `i+1` is the oscillator `h(-i-1)`.

* `actJ`, `actE`: certified left actions of the neutral generator `J` (`JR`) and of the
  charged generator `E = e^{β} + e^{-β}` in every charge sector.  The single-sector arithmetic
  (`neutralAction`, `exponentialAction`) follows the pattern of the evaluator
  `OrbC2gEvaluator`; it is reproduced here so that this file does not depend on in-progress work.
* `actU`: certified action of the dressed weight-nine generator
  `U = J₍₋₂₎E − E₍₋₂₎J` (`OrbC2e.weightNine`), through the finite Borcherds iterate
  (`OrbC2f.mode_iterate_finite`).  The cutoff is justified by the actual grading.
* `bucket`: sector-wise normal form, used for the final comparison.
-/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

namespace VOA.Classification.COne.OrbRat3
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  MvPolynomial VOA.SparseRational PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e LatMod

/-! ## Single-sector arithmetic -/

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

/-- The charge-`d` sector of `V₈`. -/
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


/-! ## Memoized creation coefficients

`schurR` recomputes every lower Schur polynomial at each step (exponential cost in the kernel).
`schurTab n` builds the list `[S₀, …, Sₙ]` incrementally; `exponentialActionM` uses it and is
proved equal to `exponentialAction`. -/

def schurStep (T : List (RawPoly ℕ)) (n : ℕ) : RawPoly ℕ :=
  normR (scaleR ((n+1 : ℚ)⁻¹)
    ((List.range (n+1)).flatMap fun i => prependC 0 (prependC (i+1) (T.getD (n-i) []))))

def schurTab : ℕ → List (RawPoly ℕ)
  | 0 => [[(1, [])]]
  | n+1 => schurTab n ++ [schurStep (schurTab n) n]

theorem schurTab_length (n : ℕ) : (schurTab n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [schurTab, ih]

theorem flatMap_congr' {α β : Type*} (l : List α) (f g : α → List β)
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem schurTab_getD (n : ℕ) : ∀ k ≤ n, (schurTab n).getD k [] = schurR k := by
  induction n with
  | zero =>
    intro k hk
    obtain rfl : k = 0 := by omega
    simp [schurTab, schurR]
  | succ n ih =>
    intro k hk
    rcases Nat.lt_or_ge k (n+1) with hlt | hge
    · rw [schurTab, List.getD_append _ _ _ _ (by rw [schurTab_length]; exact hlt)]
      exact ih k (by omega)
    · obtain rfl : k = n + 1 := by omega
      rw [schurTab, List.getD_append_right _ _ _ _ (by rw [schurTab_length])]
      simp only [schurTab_length, Nat.sub_self, List.getD_cons_zero]
      rw [schurR, schurStep]
      congr 2
      apply flatMap_congr'
      intro i _
      rw [ih (n - i) (by omega)]

theorem schurTab_getD_default (n k : ℕ) : (schurTab n).getD k (schurR k) = schurR k := by
  rcases Nat.lt_or_ge k (n+1) with hlt | hge
  · rw [List.getD_eq_getElem _ _ (by rw [schurTab_length]; exact hlt), ← schurTab_getD n k
      (by omega), List.getD_eq_getElem _ _ (by rw [schurTab_length]; exact hlt)]
  · exact List.getD_eq_default _ _ (by rw [schurTab_length]; omega)

/-- The precomputed table used by the certificates. -/
def schurT : List (RawPoly ℕ) := schurTab 24

def expWordM : List ℕ → ℤ → RawPoly ℕ
  | [], s => if 0 ≤ s then schurT.getD s.toNat (schurR s.toNat) else []
  | 0 :: w, s => prependC 0 (expWordM w s)
  | (i+1) :: w, s => normR (prependC (i+1) (expWordM w s) ++
      scaleR (-1) (prependC 0 (expWordM w (s+i+1))))

theorem expWordM_eq : ∀ (w : List ℕ) (s : ℤ), expWordM w s = expWordR w s
  | [], s => by rw [expWordM, expWordR, schurT, schurTab_getD_default]
  | 0 :: w, s => by rw [expWordM, expWordR, expWordM_eq w s]
  | (i+1) :: w, s => by rw [expWordM, expWordR, expWordM_eq w s, expWordM_eq w (s+i+1)]

def expPolyM (s : ℤ) (P : RawPoly ℕ) : RawPoly ℕ :=
  normR (P.flatMap fun t => scaleR t.1 (expWordM t.2 s))

theorem expPolyM_eq (s : ℤ) (P : RawPoly ℕ) : expPolyM s P = expPolyR s P := by
  simp only [expPolyM, expPolyR, expWordM_eq]

/-- Exponential-left action with memoized creation coefficients. -/
def exponentialActionM (b d n : ℤ) (P : RawPoly ℕ) : RawPoly ℕ :=
  reduceR 8 (onOscillators
    (fun R => chargeScale b (expPolyM (-n-1-8*b*d) (liftR R))) P)

theorem exponentialActionM_eq (b d n : ℤ) (P : RawPoly ℕ) :
    exponentialActionM b d n P = exponentialAction b d n P := by
  simp only [exponentialActionM, exponentialAction, expPolyM_eq]

/-! ## Multi-sector states -/

/-- A finite multi-sector state description. -/
abbrev St := List (ℤ × RawPoly ℕ)

/-- The actual `V₈` state described by `s`. -/
noncomputable def evalSt (s : St) : LatModuleGen (latP 4) :=
  (s.map fun p => sector p.1 (evRc (a0 4) (cα 4) p.2)).sum

@[simp] theorem evalSt_nil : evalSt [] = 0 := rfl

theorem evalSt_cons (p : ℤ × RawPoly ℕ) (s : St) :
    evalSt (p :: s) = sector p.1 (evRc (a0 4) (cα 4) p.2) + evalSt s := by
  simp [evalSt]

theorem evalSt_append (s t : St) : evalSt (s ++ t) = evalSt s + evalSt t := by
  simp [evalSt]

def scaleSt (q : ℚ) (s : St) : St := s.map fun p => (p.1, scaleR q p.2)

theorem evalSt_scaleSt (q : ℚ) (s : St) : evalSt (scaleSt q s) = (q : ℂ) • evalSt s := by
  induction s with
  | nil => simp [scaleSt]
  | cons p s ih =>
    change evalSt ((p.1, scaleR q p.2) :: scaleSt q s) = _
    rw [evalSt_cons, evalSt_cons, ih, evRc_scaleR, map_smul, smul_add]

theorem evalSt_flatMap {α : Type*} (l : List α) (f : α → St) :
    evalSt (l.flatMap f) = (l.map fun a => evalSt (f a)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.flatMap_cons, evalSt_append, ih, List.map_cons, List.sum_cons]

/-- The neutral generator `J` of `V₈⁺`, as a `V₈` state. -/
noncomputable abbrev Jc : LatModuleGen (latP 4) := ls 4 JR

/-- The charged generator `E = e^{β} + e^{-β}`, as a `V₈` state. -/
noncomputable abbrev Ec : LatModuleGen (latP 4) :=
  latChargeGen (latP 4) ((1 : ℤ) : (latP 4).carrier) +
    latChargeGen (latP 4) ((-1 : ℤ) : (latP 4).carrier)

def actJ (n : ℤ) (s : St) : St := s.map fun p => (p.1, neutralAction JR n p.1 p.2)

def actE (n : ℤ) (s : St) : St := s.flatMap fun p =>
  [(p.1+1, exponentialActionM 1 p.1 n p.2), (p.1-1, exponentialActionM (-1) p.1 n p.2)]

theorem actJ_sound (n : ℤ) (s : St) :
    (V2m 4 four_ge_one).smul Jc n (evalSt s) = evalSt (actJ n s) := by
  induction s with
  | nil => simp [actJ, PreVertexAlgebra.smul_def]
  | cons p s ih =>
    change _ = evalSt ((p.1, neutralAction JR n p.1 p.2) :: actJ n s)
    rw [evalSt_cons, evalSt_cons, PreVertexAlgebra.smul_add_right, ih, neutralAction_sound]

theorem actE_sound (n : ℤ) (s : St) :
    (V2m 4 four_ge_one).smul Ec n (evalSt s) = evalSt (actE n s) := by
  induction s with
  | nil => simp [actE, PreVertexAlgebra.smul_def]
  | cons p s ih =>
    rw [actE, List.flatMap_cons, ← actE, evalSt_append, ← ih, evalSt_cons, evalSt_cons,
      evalSt_cons, evalSt_nil, add_zero, PreVertexAlgebra.smul_add_right,
      PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_left,
      exponentialAction_sound, exponentialAction_sound, exponentialActionM_eq,
      exponentialActionM_eq]
    rw [show (1 : ℤ) + p.1 = p.1 + 1 by ring, show (-1 : ℤ) + p.1 = p.1 - 1 by ring]

/-! ## The dressed weight-nine generator -/

/-- The weight-nine generator as a `V₈` state. -/
noncomputable abbrev Uc : LatModuleGen (latP 4) :=
  ((weightNine : PlusC2.VP 4 four_ge_one) : LatModuleGen (latP 4))

theorem Jc_eq : ((J 4 four_ge_one : PlusC2.VP 4 four_ge_one) : LatModuleGen (latP 4)) = Jc :=
  hasN_J 4 four_ge_one

theorem Ec_eq :
    ((EP 4 four_ge_one : PlusC2.VP 4 four_ge_one) : LatModuleGen (latP 4)) = Ec := rfl

theorem Uc_eq : Uc = (V2m 4 four_ge_one).smul Jc (-2) Ec -
    (V2m 4 four_ge_one).smul Ec (-2) Jc := by
  rw [Uc, weightNine, Submodule.coe_sub, V2mPlus_smul_coe, V2mPlus_smul_coe, Jc_eq, Ec_eq]

theorem Jc_mem : Jc ∈ (V2m 4 four_ge_one).grading 4 := by
  rw [← Jc_eq]; exact J_mem_grading_four 4 four_ge_one

theorem Ec_mem : Ec ∈ (V2m 4 four_ge_one).grading 4 := by
  rw [← Ec_eq]; exact EP_mem_grading 4 four_ge_one

theorem Uc_mem : Uc ∈ (V2m 4 four_ge_one).grading 9 := weightNine_mem_grading

/-- One term of the finite iterate expansion of `U₍ₙ₎`. -/
def termU (n : ℤ) (i : ℕ) (s : St) : St :=
  scaleSt (i+1) (actJ (-2-i) (actE (n+i) s) ++ scaleSt (-1) (actE (-2+n-i) (actJ i s)) ++
    scaleSt (-1) (actE (-2-i) (actJ (n+i) s)) ++ actJ (-2+n-i) (actE i s))

/-- The executable action of `U₍ₙ₎` with iterate cutoff `B`. -/
def actU (n : ℤ) (B : ℕ) (s : St) : St := (List.range B).flatMap fun i => termU n i s

theorem coeff_neg_two (i : ℕ) :
    (-1 : ℂ) ^ i * gBinom (-2) i = (((i : ℚ) + 1 : ℚ) : ℂ) := by
  rw [gBinom_neg_two, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  push_cast; ring

theorem list_range_sum {M : Type*} [AddCommMonoid M] (B : ℕ) (f : ℕ → M) :
    ((List.range B).map f).sum = ∑ i ∈ Finset.range B, f i := by
  induction B with
  | zero => simp
  | succ B ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

theorem termU_sound (n : ℤ) (i : ℕ) (s : St) :
    evalSt (termU n i s) = ((-1 : ℂ)^i * gBinom (-2) i) •
      (((V2m 4 four_ge_one).smul Jc (-2-i) ((V2m 4 four_ge_one).smul Ec (n+i) (evalSt s)) -
        ((-1 : ℂ)^(-2 : ℤ)) • (V2m 4 four_ge_one).smul Ec (-2+n-i)
          ((V2m 4 four_ge_one).smul Jc i (evalSt s))) -
       ((V2m 4 four_ge_one).smul Ec (-2-i) ((V2m 4 four_ge_one).smul Jc (n+i) (evalSt s)) -
        ((-1 : ℂ)^(-2 : ℤ)) • (V2m 4 four_ge_one).smul Jc (-2+n-i)
          ((V2m 4 four_ge_one).smul Ec i (evalSt s)))) := by
  rw [termU, evalSt_scaleSt, evalSt_append, evalSt_append, evalSt_append, evalSt_scaleSt,
    evalSt_scaleSt, ← actE_sound, ← actJ_sound, ← actE_sound, ← actJ_sound, ← actJ_sound,
    ← actE_sound, ← actJ_sound, ← actE_sound, coeff_neg_two]
  have h2 : (-1 : ℂ) ^ (-2 : ℤ) = 1 := by norm_num
  rw [h2]
  push_cast
  module

/-- Soundness of the dressed-generator evaluator on a homogeneous state. -/
theorem actU_sound (n : ℤ) (B : ℕ) (s : St) {r : ℤ}
    (hs : evalSt s ∈ (V2m 4 four_ge_one).grading r) (hB₁ : 4 + r ≤ B) (hB₂ : 4 + r - n ≤ B) :
    (V2m 4 four_ge_one).smul Uc n (evalSt s) = evalSt (actU n B s) := by
  have hsub (a b : LatModuleGen (latP 4)) :
      (V2m 4 four_ge_one).smul (a - b) n (evalSt s) =
        (V2m 4 four_ge_one).smul a n (evalSt s) - (V2m 4 four_ge_one).smul b n (evalSt s) := by
    rw [sub_eq_add_neg, PreVertexAlgebra.smul_add_left, ← neg_one_smul ℂ b,
      PreVertexAlgebra.smul_smul_left, neg_one_smul, ← sub_eq_add_neg]
  rw [Uc_eq, hsub,
    OrbC2f.mode_iterate_finite _ Jc_mem Ec_mem hs (-2) n B hB₁ hB₂,
    OrbC2f.mode_iterate_finite _ Ec_mem Jc_mem hs (-2) n B hB₁ hB₂,
    ← Finset.sum_sub_distrib, actU, evalSt_flatMap, list_range_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [termU_sound]
  simp only [smul_sub]


/-! ## Sector buckets and the weight-one boson -/

/-- Sector-wise normal form over a prescribed list of sectors. -/
def bucket (ds : List ℤ) (s : St) : St :=
  ds.map fun d => (d, reduceR 8 ((s.filter fun p => p.1 = d).flatMap Prod.snd))

theorem sum_sector_filter (ds : List ℤ) (hd : ds.Nodup) :
    ∀ s : St, (∀ p ∈ s, p.1 ∈ ds) →
      (ds.map fun d => sector d (evRc (a0 4) (cα 4)
        ((s.filter fun p => p.1 = d).flatMap Prod.snd))).sum = evalSt s
  | [], _ => by simp [evRc_nil]
  | p :: s, hs => by
    have ih := sum_sector_filter ds hd s (fun q hq => hs q (List.mem_cons_of_mem _ hq))
    have hp : p.1 ∈ ds := hs p List.mem_cons_self
    have hterm : ∀ d, sector d (evRc (a0 4) (cα 4)
        (((p :: s).filter fun q => q.1 = d).flatMap Prod.snd)) =
        (if p.1 = d then sector d (evRc (a0 4) (cα 4) p.2) else 0) +
          sector d (evRc (a0 4) (cα 4) ((s.filter fun q => q.1 = d).flatMap Prod.snd)) := by
      intro d
      by_cases h : p.1 = d
      · rw [List.filter_cons_of_pos (by simpa using h), List.flatMap_cons, evRc_append,
          map_add, if_pos h]
      · rw [List.filter_cons_of_neg (by simpa using h), if_neg h, zero_add]
    simp only [hterm, List.sum_map_add, ih, evalSt_cons]
    congr 1
    rw [← List.sum_toFinset _ hd, Finset.sum_ite_eq]
    simp [hp]

/-- Bucketing does not change the described state. -/
theorem evalSt_bucket (ds : List ℤ) (hd : ds.Nodup) (s : St) (hs : ∀ p ∈ s, p.1 ∈ ds) :
    evalSt (bucket ds s) = evalSt s := by
  rw [← sum_sector_filter ds hd s hs, bucket, evalSt]
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro d _
  simp only [Function.comp_apply, evRc_reduce_eight]

/-- The weight-one boson `h(-1)1` of `V₈`. -/
noncomputable abbrev hV : LatModuleGen (latP 4) := bosonState (latP 4) (a0 4)

def hSt : St := [(0, [(1, [1])])]

theorem sector_one (v : ℚ) : sector 0 (evRc (a0 4) (cα 4) [(v, [1])]) = (v : ℂ) • hV := by
  have h1 : evRc (a0 4) (cα 4) [(v, [1])] = (v : ℂ) • evRc (a0 4) (cα 4) (liftR [(1, [0])]) := by
    simp [evRc_cons, evRc_nil, liftR]
  rw [h1, map_smul, evRc_liftR, hV, bosonState_eq_evR]
  rfl

theorem evalSt_hSt : evalSt hSt = hV := by
  rw [hSt, evalSt_cons, evalSt_nil, add_zero, sector_one]
  simp

theorem hV_mem : hV ∈ (V2m 4 four_ge_one).grading 1 := by
  have h := h_mem_grading 4 four_ge_one
  rw [hV, bosonState_eq_evR]
  exact h

theorem evalSt_three (P : RawPoly ℕ) :
    evalSt [(-2, []), (0, P), (2, [])] = sector 0 (evRc (a0 4) (cα 4) P) := by
  simp [evalSt_cons, evRc_nil]

end VOA.Classification.COne.OrbRat3
