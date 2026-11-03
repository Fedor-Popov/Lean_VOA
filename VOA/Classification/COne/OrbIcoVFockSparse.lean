import VOA.Classification.COne.OrbIcoVFockModes
import VOA.Core.SparseRational

/-! Executable sparse negative modes in the actual first-row Fock family.
Variable zero is the scalar s⁻²; positive variable i is s times the
creation oscillator of energy i. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA HeisenbergN MvPolynomial VOA.SparseRational
  InverseDS.LeeYangFockVirasoro

def fockRawVar (s : ℂ) : ℕ → FF
  | 0 => MvPolynomial.C (s⁻¹ ^ 2)
  | i + 1 => familyVariable s i

def fockRawEval (s : ℂ) (P : RawPoly ℕ) : FF := evalRaw (fockRawVar s) P

def rawPrepend (i : ℕ) (P : RawPoly ℕ) : RawPoly ℕ :=
  P.map fun t => (t.1, i :: t.2)

def rawScale (q : ℚ) (P : RawPoly ℕ) : RawPoly ℕ :=
  P.map fun t => (q * t.1, t.2)

def rawXPow (r : ℕ) (P : RawPoly ℕ) : RawPoly ℕ :=
  P.map fun t => (t.1, List.replicate r 0 ++ t.2)

def fockCreation (k : ℕ) : RawPoly ℕ :=
  [(((k : ℚ) - 1) / 2, [k]), ((13 - (k : ℚ)) / 2, [0, k])] ++
    ((List.range (k - 1)).map fun i => (1 / 4, [0, i + 1, k - 1 - i]))

def fockWordMode (k : ℕ) : List ℕ → RawPoly ℕ
  | [] => fockCreation k
  | i :: w => rawPrepend i (fockWordMode k w) ++
      if i = 0 then [] else [((i : ℚ), (i + k) :: w)]

def fockRawMode (k : ℕ) (P : RawPoly ℕ) : RawPoly ℕ :=
  P.flatMap fun t => rawScale t.1 (fockWordMode k t.2)

theorem eval_rawPrepend {A : Type*} [CommRing A] [Algebra ℚ A]
    (x : ℕ → A) (i : ℕ) (P : RawPoly ℕ) :
    evalRaw x (rawPrepend i P) = x i * evalRaw x P := by
  induction P with
  | nil => simp [rawPrepend, evalRaw]
  | cons t P ih =>
    rcases t with ⟨q,w⟩
    change algebraMap ℚ A q * evalWord x (i :: w) +
      evalRaw x (rawPrepend i P) = _
    rw [ih]
    simp only [evalRaw, evalWord, List.map_cons, List.prod_cons, List.sum_cons]
    ring

theorem fockRawEval_append (s : ℂ) (P Q : RawPoly ℕ) :
    fockRawEval s (P ++ Q) = fockRawEval s P + fockRawEval s Q :=
  evalRaw_append _ _ _

theorem fockRawEval_prepend (s : ℂ) (i : ℕ) (P : RawPoly ℕ) :
    fockRawEval s (rawPrepend i P) = fockRawVar s i * fockRawEval s P :=
  eval_rawPrepend _ _ _

theorem eval_rawScale (s : ℂ) (q : ℚ) (P : RawPoly ℕ) :
    fockRawEval s (rawScale q P) = (q : ℂ) • fockRawEval s P := by
  rw [fockRawEval, rawScale, evalRaw_scale]
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply ℚ ℂ FF]
  rfl

theorem eval_rawXPow (s : ℂ) (r : ℕ) (P : RawPoly ℕ) :
    fockRawEval s (rawXPow r P) = (s⁻¹ ^ 2) ^ r • fockRawEval s P := by
  induction r with
  | zero => simp [rawXPow, fockRawEval]
  | succ r ih =>
    have he : rawXPow (r+1) P = rawPrepend 0 (rawXPow r P) := by
      simp only [rawXPow, rawPrepend, List.map_map, List.replicate_succ,
        List.cons_append]
      rfl
    rw [he]
    change evalRaw (fockRawVar s) (rawPrepend 0 (rawXPow r P)) = _
    rw [eval_rawPrepend]
    change MvPolynomial.C (s⁻¹ ^ 2) * fockRawEval s (rawXPow r P) = _
    rw [ih, ← smul_eq_C_mul, smul_smul, pow_succ]
    congr 1
    ring

theorem sector_family_mul_var (s : ℂ) (k : ℕ) (hk : 0 < k)
    (i : ℕ) (P : FF) :
    sectorVirasoro (familyBackground s) (familyMomentum s) (-(k : ℤ))
      (fockRawVar s i * P) =
      fockRawVar s i * sectorVirasoro (familyBackground s) (familyMomentum s)
        (-(k : ℤ)) P +
      if i = 0 then 0 else (i : ℂ) • (fockRawVar s (i+k) * P) := by
  cases i with
  | zero => simp [fockRawVar, ← smul_eq_C_mul]
  | succ i =>
    simp only [fockRawVar, familyVariable, Nat.succ_ne_zero, if_false,
      smul_mul_assoc, map_smul]
    rw [sector_negative_X _ _ k hk]
    simp only [smul_add, smul_smul]
    have he : i + 1 + k = (i+k) + 1 := by omega
    rw [he]
    simp only [fockRawVar, familyVariable, smul_mul_assoc]
    module

theorem fock_list_sum_range {A : Type*} [AddCommMonoid A] (n : ℕ) (f : ℕ → A) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, Finset.sum_range_succ]

theorem fockRawVar_pos (s : ℂ) (i : ℕ) (hi : 0 < i) :
    fockRawVar s i = familyVariable s (i-1) := by
  cases i with
  | zero => omega
  | succ i => rfl

theorem fock_rat_mul (q : ℚ) (P : FF) :
    algebraMap ℚ FF q * P = (q : ℂ) • P := by
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply ℚ ℂ FF]
  rfl

theorem fockCreation_sound (s : ℂ) (hs : s ≠ 0) (k : ℕ) (hk : 0 < k) :
    fockRawEval s (fockCreation k) =
      sectorVirasoro (familyBackground s) (familyMomentum s) (-(k : ℤ)) (vacuumN 1) := by
  rw [sector_negative_vacuum _ _ k hk]
  unfold fockRawEval fockCreation
  rw [evalRaw_append]
  have hlin : evalRaw (fockRawVar s)
      [(((k : ℚ)-1)/2, [k]), ((13-(k : ℚ))/2, [0,k])] =
      (familyMomentum s + ((k : ℂ)-1)*familyBackground s) • X (k-1, (0 : Fin 1)) := by
    simp only [evalRaw, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      evalWord, List.prod_cons, List.prod_nil, mul_one, fock_rat_mul, add_zero,
      Rat.cast_div, Rat.cast_sub, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one]
    rw [fockRawVar_pos s k hk]
    change (((k : ℂ)-1)/2) • familyVariable s (k-1) +
      ((13-(k : ℂ))/2) • (MvPolynomial.C (s⁻¹^2) * familyVariable s (k-1)) = _
    simp only [familyVariable, ← smul_eq_C_mul, smul_smul]
    rw [← add_smul]
    congr 1
    unfold familyMomentum familyBackground
    field_simp
    ring
  rw [hlin]
  have hquad : evalRaw (fockRawVar s)
      ((List.range (k-1)).map fun i => ((1/4 : ℚ), [0,i+1,k-1-i])) =
      (1/4 : ℂ) • ∑ i ∈ Finset.range (k-1),
        X (i, (0 : Fin 1)) * X (k-2-i, (0 : Fin 1)) := by
    unfold evalRaw
    rw [List.map_map, fock_list_sum_range, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i < k-1 := Finset.mem_range.mp hi
    simp only [Function.comp_apply, evalWord, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, fock_rat_mul]
    rw [fockRawVar_pos s (k-1-i) (by omega)]
    have he : k-1-i-1 = k-2-i := by omega
    rw [he]
    simp only [fockRawVar, familyVariable, smul_mul_assoc, mul_smul_comm,
      ← smul_eq_C_mul, smul_smul]
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    congr 1
    field_simp
  rw [hquad]
  abel

theorem fockWordMode_sound (s : ℂ) (hs : s ≠ 0) (k : ℕ) (hk : 0 < k)
    (w : List ℕ) :
    fockRawEval s (fockWordMode k w) =
      sectorVirasoro (familyBackground s) (familyMomentum s) (-(k : ℤ))
        (evalWord (fockRawVar s) w) := by
  induction w with
  | nil => simpa [fockWordMode, evalWord, vacuumN] using fockCreation_sound s hs k hk
  | cons i w ih =>
    rw [fockWordMode, fockRawEval_append, fockRawEval_prepend, ih]
    change _ = sectorVirasoro _ _ _ (fockRawVar s i * evalWord (fockRawVar s) w)
    rw [sector_family_mul_var s k hk]
    by_cases hi : i=0
    · simp [hi, fockRawEval, evalRaw]
    · simp [hi, fockRawEval, evalRaw, evalWord, smul_eq_C_mul]

theorem fockRawMode_sound (s : ℂ) (hs : s ≠ 0) (k : ℕ) (hk : 0 < k)
    (P : RawPoly ℕ) :
    fockRawEval s (fockRawMode k P) =
      sectorVirasoro (familyBackground s) (familyMomentum s) (-(k : ℤ))
        (fockRawEval s P) := by
  induction P with
  | nil => simp [fockRawMode, fockRawEval, evalRaw]
  | cons t P ih =>
    rcases t with ⟨q,w⟩
    change fockRawEval s (rawScale q (fockWordMode k w) ++ fockRawMode k P) = _
    rw [fockRawEval_append, eval_rawScale, fockWordMode_sound s hs k hk, ih]
    change _ = sectorVirasoro _ _ _
      (algebraMap ℚ FF q * evalWord (fockRawVar s) w + fockRawEval s P)
    rw [fock_rat_mul, map_add, map_smul]

end VOA.Classification.COne.OrbIcoV
