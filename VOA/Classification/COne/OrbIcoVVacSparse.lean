import VOA.Classification.COne.OrbIcoVFockLow

/-! Actual continuous vacuum Fock family, with the first-row translation
singular vector killed at every parameter. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA HeisenbergN MvPolynomial VOA.SparseRational
  InverseDS.LeeYangFockVirasoro InverseDS.VirasoroVerma VOA.VirasoroScreening

abbrev vacFamilyMomentum (_s : ℂ) : ℂ := 0

abbrev vacFamilyWeight (s : ℂ) : ℂ :=
  (vacFamilyMomentum s)^2-2*familyBackground s*vacFamilyMomentum s

abbrev vacFamilyMap (s : ℂ) := chargedFockMap (familyBackground s) (vacFamilyMomentum s)

def vacCreation (k : ℕ) : RawPoly ℕ :=
  [(((k : ℚ)-1)/2,[k]),((1-(k : ℚ))/2,[0,k])] ++
    ((List.range (k-1)).map fun i => (1/4,[0,i+1,k-1-i]))

def vacWordMode (k : ℕ) : List ℕ → RawPoly ℕ
  | [] => vacCreation k
  | i::w => rawPrepend i (vacWordMode k w) ++
      if i=0 then [] else [((i:ℚ),(i+k)::w)]

def vacRawMode (k : ℕ) (P : RawPoly ℕ) : RawPoly ℕ :=
  P.flatMap fun t => rawScale t.1 (vacWordMode k t.2)

theorem sector_vac_family_mul_var (s : ℂ) (k : ℕ) (hk : 0 < k)
    (i : ℕ) (P : FF) :
    sectorVirasoro (familyBackground s) (vacFamilyMomentum s) (-(k : ℤ))
      (fockRawVar s i * P) =
      fockRawVar s i * sectorVirasoro (familyBackground s) (vacFamilyMomentum s)
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

theorem vacCreation_sound (s : ℂ) (hs : s ≠ 0) (k : ℕ) (hk : 0 < k) :
    fockRawEval s (vacCreation k) =
      sectorVirasoro (familyBackground s) (vacFamilyMomentum s) (-(k : ℤ)) (vacuumN 1) := by
  rw [sector_negative_vacuum _ _ k hk]
  unfold fockRawEval vacCreation
  rw [evalRaw_append]
  have hlin : evalRaw (fockRawVar s)
      [(((k : ℚ)-1)/2, [k]), ((1-(k : ℚ))/2, [0,k])] =
      (vacFamilyMomentum s + ((k : ℂ)-1)*familyBackground s) • X (k-1, (0 : Fin 1)) := by
    simp only [evalRaw, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      evalWord, List.prod_cons, List.prod_nil, mul_one, fock_rat_mul, add_zero,
      Rat.cast_div, Rat.cast_sub, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one]
    rw [fockRawVar_pos s k hk]
    change (((k : ℂ)-1)/2) • familyVariable s (k-1) +
      ((1-(k : ℂ))/2) • (MvPolynomial.C (s⁻¹^2) * familyVariable s (k-1)) = _
    simp only [familyVariable, ← smul_eq_C_mul, smul_smul]
    rw [← add_smul]
    congr 1
    unfold vacFamilyMomentum familyBackground
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

theorem vacWordMode_sound (s : ℂ) (hs : s ≠ 0) (k : ℕ) (hk : 0 < k)
    (w : List ℕ) :
    fockRawEval s (vacWordMode k w) =
      sectorVirasoro (familyBackground s) (vacFamilyMomentum s) (-(k : ℤ))
        (evalWord (fockRawVar s) w) := by
  induction w with
  | nil => simpa [vacWordMode, evalWord, vacuumN] using vacCreation_sound s hs k hk
  | cons i w ih =>
    rw [vacWordMode, fockRawEval_append, fockRawEval_prepend, ih]
    change _ = sectorVirasoro _ _ _ (fockRawVar s i * evalWord (fockRawVar s) w)
    rw [sector_vac_family_mul_var s k hk]
    by_cases hi : i=0
    · simp [hi, fockRawEval, evalRaw]
    · simp [hi, fockRawEval, evalRaw, evalWord, smul_eq_C_mul]

theorem vacRawMode_sound (s : ℂ) (hs : s ≠ 0) (k : ℕ) (hk : 0 < k)
    (P : RawPoly ℕ) :
    fockRawEval s (vacRawMode k P) =
      sectorVirasoro (familyBackground s) (vacFamilyMomentum s) (-(k : ℤ))
        (fockRawEval s P) := by
  induction P with
  | nil => simp [vacRawMode, fockRawEval, evalRaw]
  | cons t P ih =>
    rcases t with ⟨q,w⟩
    change fockRawEval s (rawScale q (vacWordMode k w) ++ vacRawMode k P) = _
    rw [fockRawEval_append, eval_rawScale, vacWordMode_sound s hs k hk, ih]
    change _ = sectorVirasoro _ _ _
      (algebraMap ℚ FF q * evalWord (fockRawVar s) w + fockRawEval s P)
    rw [fock_rat_mul, map_add, map_smul]


end VOA.Classification.COne.OrbIcoV
