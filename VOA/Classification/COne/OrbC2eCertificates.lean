import VOA.Classification.COne.OrbC2eExponential
import VOA.Classification.COne.PlusSplitHalfCharacters

/-! # Symbolic charge substitution and norm-reduction certificates -/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

namespace VOA.Classification.COne.OrbC2e
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  MvPolynomial VOA.SparseRational PlusC2Eval PlusUnitary PlusC2 LatMod

def liftR (P : RawPoly ℕ) : RawPoly ℕ := P.map fun t => (t.1, t.2.map (·+1))

def negChargeR (P : RawPoly ℕ) : RawPoly ℕ :=
  P.map fun t => ((-1 : ℚ) ^ t.2.count 0 * t.1, t.2)

/-- Reduce adjacent charge pairs using c²=K. Applied after normalization,
this reduces every charge exponent to at most one. -/
def reduceWordR (K : ℚ) : List ℕ → RawPoly ℕ
  | [] => [(1, [])]
  | [i] => [(1, [i])]
  | i :: j :: w => if i = 0 ∧ j = 0 then scaleR K (reduceWordR K w)
      else prependC i (reduceWordR K (j :: w))

def reduceR (K : ℚ) (P : RawPoly ℕ) : RawPoly ℕ :=
  normR ((normR P).flatMap fun t => scaleR t.1 (reduceWordR K t.2))

theorem evRc_liftR {r : ℕ} (a : Fin r) (c : ℂ) (P : RawPoly ℕ) :
    evRc a c (liftR P) = evR a P := by
  have hw : ∀ w : List ℕ, evalWord (xvc a c) (w.map (·+1)) = evalWord (xv a) w := by
    intro w
    induction w with
    | nil => rfl
    | cons i w ih => rw [List.map_cons, evalWordC_cons, evalWord_cons, ih]; rfl
  induction P with
  | nil => rfl
  | cons t P ih =>
    rcases t with ⟨q,w⟩
    rw [liftR, List.map_cons, evRc_cons, evR_cons, hw]
    exact congrArg (_ + ·) ih

theorem evRc_negChargeR {r : ℕ} (a : Fin r) (c : ℂ) (P : RawPoly ℕ) :
    evRc a c (negChargeR P) = evRc a (-c) P := by
  have hw : ∀ w : List ℕ, evalWord (xvc a (-c)) w =
      ((-1 : ℂ) ^ w.count 0) • evalWord (xvc a c) w := by
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
    rw [negChargeR, List.map_cons, evRc_cons, evRc_cons, hw]
    change _ + evRc a c (negChargeR P) = _
    rw [ih, smul_smul]
    push_cast
    rw [mul_comm (q : ℂ)]

theorem evRc_reduceWordR {r : ℕ} (a : Fin r) (c : ℂ) (K : ℚ)
    (hc : c * c = (K : ℂ)) : ∀ w : List ℕ,
    evRc a c (reduceWordR K w) = evalWord (xvc a c) w
  | [] => by simp [reduceWordR, evRc_cons, evRc_nil, evalWordC_nil]
  | [i] => by simp [reduceWordR, evRc_cons, evRc_nil]
  | i :: j :: w => by
    rw [reduceWordR]
    split_ifs with h
    · obtain ⟨rfl,rfl⟩ := h
      rw [evRc_scaleR, evRc_reduceWordR a c K hc w, evalWordC_cons, evalWordC_cons]
      simp only [xvc, MvPolynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul, hc]
    · rw [evRc_prependC, evRc_reduceWordR a c K hc (j :: w), evalWordC_cons]
      rfl

theorem evRc_reduceR {r : ℕ} (a : Fin r) (c : ℂ) (K : ℚ)
    (hc : c * c = (K : ℂ)) (P : RawPoly ℕ) : evRc a c (reduceR K P) = evRc a c P := by
  rw [reduceR, evRc_normR, evRc_flatMap]
  have h : ∀ Q : RawPoly ℕ,
      (Q.map fun t => evRc a c (scaleR t.1 (reduceWordR K t.2))).sum = evRc a c Q := by
    intro Q
    induction Q with
    | nil => simp [evRc_nil]
    | cons t Q ih =>
      rcases t with ⟨q,w⟩
      rw [List.map_cons, List.sum_cons, evRc_scaleR, evRc_reduceWordR a c K hc,
        ih, evRc_cons]
  rw [h, evRc_normR]

/-- Polynomial certificate to an actual Fock-state equality at norm eight. -/
theorem norm_eight_eq_of_cert (P : RawPoly ℕ) (Q : RawPoly ℕ)
    (h : normR (reduceR 8 P) = normR (liftR Q)) :
    evRc (a0 4) (cα 4) P = evR (a0 4) Q := by
  have he := congrArg (evRc (a0 4) (cα 4)) h
  rw [evRc_normR, evRc_reduceR, evRc_normR, evRc_liftR] at he
  · exact he
  · convert cα_sq 4 (by norm_num) using 1
    norm_num

/-- Charge reduction also preserves the actual projected plus state. -/
theorem hasC_of_reduceR_eq {y : VP 4 (by norm_num)} {P Q : RawPoly ℕ}
    (hy : HasC 4 (by norm_num) y P) (h : reduceR 8 P = normR Q) :
    HasC 4 (by norm_num) y Q := by
  have hc : cα 4 * cα 4 = ((8 : ℚ) : ℂ) := by
    convert cα_sq 4 (by norm_num) using 1
    norm_num
  have he := congrArg (evRc (a0 4) (cα 4)) h
  rw [evRc_reduceR _ _ _ hc, evRc_normR] at he
  rw [HasC, hy, stP, stP, he]

end VOA.Classification.COne.OrbC2e
