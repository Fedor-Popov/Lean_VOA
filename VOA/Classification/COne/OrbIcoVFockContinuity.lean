import VOA.Classification.COne.OrbIcoVFockKernel

/-! Coefficientwise continuity of actual fixed-word first-row Fock
families. Each word is a finite rational sparse polynomial, and all
parameter dependence lies in s and s⁻². -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA HeisenbergN MvPolynomial VOA.SparseRational VOA.VirasoroScreening
  InverseDS.VirasoroVerma InverseDS.LeeYangFockVirasoro Filter Topology

def fockBaseVar : ℕ → FF
  | 0 => 1
  | i+1 => X (i, (0 : Fin 1))

def fockWordScalar (s : ℂ) (w : List ℕ) : ℂ :=
  (w.map fun i => if i=0 then s⁻¹^2 else s).prod

theorem fockRawVar_scalar (s : ℂ) (i : ℕ) :
    fockRawVar s i = (if i=0 then s⁻¹^2 else s) • fockBaseVar i := by
  cases i <;> simp [fockRawVar, fockBaseVar, familyVariable, smul_eq_C_mul]

theorem fockWord_scalar (s : ℂ) (w : List ℕ) :
    evalWord (fockRawVar s) w = fockWordScalar s w • evalWord fockBaseVar w := by
  induction w with
  | nil => simp [evalWord, fockWordScalar]
  | cons i w ih =>
    change fockRawVar s i * evalWord (fockRawVar s) w = _
    rw [fockRawVar_scalar, ih]
    simp only [evalWord, fockWordScalar, List.map_cons, List.prod_cons,
      smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [mul_comm]

theorem fockWordScalar_continuousAt (s₀ : ℂ) (hs : s₀ ≠ 0) (w : List ℕ) :
    ContinuousAt (fun s => fockWordScalar s w) s₀ := by
  induction w with
  | nil => exact continuousAt_const
  | cons i w ih =>
    change ContinuousAt (fun s => (if i=0 then s⁻¹^2 else s) * fockWordScalar s w) s₀
    by_cases hi : i=0
    · simp only [hi, if_true]
      exact ((continuousAt_id.inv₀ hs).pow 2).mul ih
    · simp only [if_neg hi]
      exact continuousAt_id.mul ih

theorem fockRawEval_coeff_continuousAt (s₀ : ℂ) (hs : s₀ ≠ 0)
    (P : RawPoly ℕ) (d : (ℕ × Fin 1) →₀ ℕ) :
    ContinuousAt (fun s => coeff d (fockRawEval s P)) s₀ := by
  induction P with
  | nil => simpa [fockRawEval, evalRaw] using (continuousAt_const :
      ContinuousAt (fun _ : ℂ => (0 : ℂ)) s₀)
  | cons t P ih =>
    rcases t with ⟨q,w⟩
    have he (s : ℂ) : coeff d (fockRawEval s ((q,w)::P)) =
        (q : ℂ)*fockWordScalar s w*coeff d (evalWord fockBaseVar w) +
          coeff d (fockRawEval s P) := by
      change coeff d (algebraMap ℚ FF q * evalWord (fockRawVar s) w + fockRawEval s P) = _
      rw [fock_rat_mul, fockWord_scalar, coeff_add, coeff_smul, coeff_smul]
      simp only [smul_eq_mul]
      ring
    simp_rw [he]
    exact ((continuousAt_const.mul (fockWordScalar_continuousAt s₀ hs w)).mul
      continuousAt_const).add ih

def fockDescData : List ℕ → RawPoly ℕ
  | [] => [(1, [])]
  | k::w => fockRawMode (k+1) (fockDescData w)

theorem fockDescData_sound (s : ℂ) (hs : s ≠ 0) (w : List ℕ) :
    familyMap s (negWord (familyCharge s) (familyWeight s) w) =
      fockRawEval s (fockDescData w) := by
  induction w with
  | nil =>
    rw [negWord_nil, familyMap, chargedFockMap, universalMap_highestVector]
    simp [fockDescData, fockRawEval, evalRaw, evalWord, vacuumN]
  | cons k w ih =>
    rw [negWord_cons, familyMap, chargedFockMap_mode]
    change sectorVirasoro _ _ (-(k:ℤ)-1) (familyMap s (negWord _ _ w)) = _
    rw [ih, fockDescData, fockRawMode_sound s hs (k+1) (by omega)]
    rw [show -((k+1 : ℕ) : ℤ) = -(k : ℤ)-1 by omega]

def familyLevelCoefficient (N : ℕ) (a : VermaPartitions N → ℂ)
    (s : ℂ) (d : (ℕ × Fin 1) →₀ ℕ) : ℂ :=
  ∑ w : VermaPartitions N, a w * coeff d (fockRawEval s (fockDescData w.val))

theorem familyLevelCoefficient_sound (N : ℕ) (a : VermaPartitions N → ℂ)
    (s : ℂ) (hs : s ≠ 0) (d : (ℕ × Fin 1) →₀ ℕ) :
    coeff d (familyMap s (vermaLevelState (familyCharge s) (familyWeight s) N a)) =
      familyLevelCoefficient N a s d := by
  simp only [vermaLevelState, map_sum, map_smul, familyLevelCoefficient,
    MvPolynomial.coeff_sum, coeff_smul, fockDescData_sound s hs]
  rfl

theorem familyLevelCoefficient_continuousAt (N : ℕ) (a : VermaPartitions N → ℂ)
    (s₀ : ℂ) (hs : s₀ ≠ 0) (d : (ℕ × Fin 1) →₀ ℕ) :
    ContinuousAt (fun s => familyLevelCoefficient N a s d) s₀ := by
  unfold familyLevelCoefficient
  apply tendsto_finsetSum
  intro w hw
  exact continuousAt_const.mul (fockRawEval_coeff_continuousAt s₀ hs _ d)

end VOA.Classification.COne.OrbIcoV
