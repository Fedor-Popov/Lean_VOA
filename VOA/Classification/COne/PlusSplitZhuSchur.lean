import VOA.Classification.COne.PlusSplitZhuBoundary

/-! Uniform Schur expansion of E * E in the VOA and in its actual Zhu quotient.
The expansion is not yet a reduction to the finite normal-form list. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusZhuSchur
open VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
open PlusUnitary PlusC2 PlusZhuNormalForms

/-- Explicit rational Schur polynomials in power-sum variables X_0, X_1, ... .
The recursion is S_0 = 1, S_(n+1) = sum_(j=0)^n X_j S_(n-j)/(n+1). -/
def schur : ℕ → MvPolynomial ℕ ℚ
  | 0 => 1
  | n + 1 => ((n + 1 : ℚ)⁻¹) •
      ∑ j ∈ Finset.range (n + 1), MvPolynomial.X j * schur (n - j)

/-- Specialization of the explicit rational polynomial to lattice oscillators. -/
theorem schur_aeval (L : IntegralLattice) (a : L.carrier) (n : ℕ) :
    MvPolynomial.aeval (vVar L a) (schur n) = vSchur L a n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [schur, vSchur_zero]
    | succ n =>
      rw [schur, map_smul, map_sum, vSchur_succ]
      have he : ∀ j ∈ Finset.range (n + 1),
          MvPolynomial.aeval (vVar L a) (MvPolynomial.X j * schur (n - j)) =
            vVar L a j * vSchur L a (n - j) := by
        intro j hj
        rw [map_mul, MvPolynomial.aeval_X, ih _ (by omega)]
      rw [Finset.sum_congr rfl he]
      rw [← Rat.cast_smul_eq_qsmul ℂ]
      push_cast
      rfl

/-- The complete E-square polynomial in abstract oscillator variables. -/
def squarePolynomial (m : ℕ) : MvPolynomial ℕ ℚ :=
  ∑ i ∈ Finset.range (m + 1), (m.choose i : ℚ) •
    (schur (2 * m - i) + MvPolynomial.aeval (fun j => -MvPolynomial.X j)
      (schur (2 * m - i)))

theorem squarePolynomial_aeval (m : ℕ) (L : IntegralLattice) (a : L.carrier) :
    MvPolynomial.aeval (vVar L a) (squarePolynomial m) =
      ∑ i ∈ Finset.range (m + 1), (m.choose i : ℂ) •
        (vSchur L a (2 * m - i) + vSchur L (-a) (2 * m - i)) := by
  have hn (j : ℕ) : -vVar L a j = vVar L (-a) j := by
    simp only [vVar, chargeCoord_neg, neg_smul, Finset.sum_neg_distrib]
  rw [squarePolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, map_add, schur_aeval, MvPolynomial.comp_aeval_apply]
  simp only [map_neg, MvPolynomial.aeval_X, hn, schur_aeval]
  rw [← Rat.cast_smul_eq_qsmul ℂ]
  push_cast
  rfl

variable (m : ℕ) (hm : 1 ≤ m)

/-- The neutral even Schur state S_d(alpha) + S_d(-alpha). -/
def evenSchur (d : ℕ) : VP m hm :=
  (2 : ℂ) • PP m hm (latStateGen (latP m) (vSchur (latP m) (1 : ℤ) d) 0)

theorem evenSchur_coe (d : ℕ) :
    ((evenSchur m hm d : VP m hm) : LatModuleGen (latP m)) =
      latStateGen (latP m) (vSchur (latP m) (1 : ℤ) d) 0 +
      latStateGen (latP m) (vSchur (latP m) (-1 : ℤ) d) 0 := by
  change (2 : ℂ) • ((PP m hm _ : VP m hm) : LatModuleGen (latP m)) = _
  rw [PP_coe, thetaLat_latStateGen, sigmaN_vSchur, neg_zero, smul_smul]
  norm_num
  rfl

theorem charge_same (i : ℕ) (a : ℤ) (ha : a = 1 ∨ a = -1) :
    (V2m m hm).smul (latChargeGen (latP m) a) ((i : ℤ) - 1)
      (latChargeGen (latP m) a) = 0 := by
  unfold V2m
  change (latticeVOAGen (latP m) _ _).smul (latChargeGen (latP m) a)
    ((i : ℤ) - 1) (latStateGen (latP m) (vacuumN _) a) = 0
  rw [latVOA_smul_latChargeGen_state, latP_form, EEVec_vacuum]
  have hm1 : (1 : ℤ) ≤ m := by exact_mod_cast hm
  rw [if_neg (by rcases ha with rfl | rfl <;> nlinarith)]
  simp [latStateGen]

theorem charge_opposite (i : ℕ) (hi : i ≤ 2 * m) (a : ℤ)
    (ha : a = 1 ∨ a = -1) :
    (V2m m hm).smul (latChargeGen (latP m) a) ((i : ℤ) - 1)
      (latChargeGen (latP m) (-a)) =
      latStateGen (latP m) (vSchur (latP m) a (2 * m - i)) 0 := by
  unfold V2m
  rw [show latChargeGen (latP m) (-a) = latStateGen (latP m) (vacuumN _) (-a) from rfl,
    latVOA_smul_latChargeGen_state, latP_form, EEVec_vacuum]
  have ht : -((i : ℤ) - 1) - 1 - 2 * (m : ℤ) * a * -a = ((2 * m - i : ℕ) : ℤ) := by
    rw [Nat.cast_sub hi]
    push_cast
    rcases ha with rfl | rfl <;> ring
  rw [ht, if_pos (Int.natCast_nonneg _), Int.toNat_natCast,
    PlusCharacterTable.rankOne_cocycle, one_smul]
  congr 1
  exact add_neg_cancel a

/-- All modes entering the Zhu product, with their exact Schur coefficients. -/
theorem E_mode_E (i : ℕ) (hi : i ≤ 2 * m) :
    (V2mPlus m hm).smul (EP m hm) ((i : ℤ) - 1) (EP m hm) =
      evenSchur m hm (2 * m - i) := by
  apply Subtype.ext
  rw [V2mPlus_smul_coe, EP_coe, PreVertexAlgebra.smul_add_left,
    PreVertexAlgebra.smul_add_right, PreVertexAlgebra.smul_add_right,
    charge_same m hm i 1 (Or.inl rfl), charge_same m hm i (-1) (Or.inr rfl),
    charge_opposite m hm i hi 1 (Or.inl rfl)]
  have hn := charge_opposite m hm i hi (-1) (Or.inr rfl)
  norm_num only [neg_neg] at hn
  rw [hn, zero_add, add_zero, evenSchur_coe]

/-- The explicit binomial-Schur state representing E * E. -/
def squareState : VP m hm :=
  ∑ i ∈ Finset.range (m + 1), (m.choose i : ℂ) • evenSchur m hm (2 * m - i)

/-- Dong--Nagatomo Lemma 5.4, as an equality of states, uniformly in m. -/
theorem E_zhuMul_E : zhuMul (V2mPlus m hm) (EP m hm) (EP m hm) = squareState m hm := by
  rw [zhuMul_homogeneous _ (EP_mem_grading m hm)]
  simp only [Int.toNat_natCast, squareState]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ m := by have := Finset.mem_range.mp hi; omega
  rw [cbz_natCast_eq_choose hi', E_mode_E m hm i (by omega)]

/-- The expansion with a single explicit rational oscillator polynomial. -/
theorem E_zhuMul_E_coe :
    ((zhuMul (V2mPlus m hm) (EP m hm) (EP m hm) : VP m hm) :
      LatModuleGen (latP m)) =
      latStateGen (latP m)
        (MvPolynomial.aeval (vVar (latP m) (1 : ℤ)) (squarePolynomial m)) 0 := by
  rw [E_zhuMul_E, squareState, squarePolynomial_aeval]
  simp only [Submodule.coe_sum, Submodule.coe_smul, evenSchur_coe,
    latStateGen, TensorProduct.sum_tmul, TensorProduct.smul_tmul,
    TensorProduct.add_tmul, TensorProduct.tmul_smul, smul_add]
  rfl

@[reducible] local instance schurRing : Ring (VOA.A (V2mPlus m hm)) := instRingA _
@[reducible] local instance schurAlgebra : Algebra ℂ (VOA.A (V2mPlus m hm)) := instAlgebraA _

/-- The same formula holds in the full quotient, retaining any radical. -/
theorem E_squared_schur :
    generator m hm 2 ^ 2 =
      ∑ i ∈ Finset.range (m + 1), (m.choose i : ℂ) •
        VOA.mk (V2mPlus m hm) (evenSchur m hm (2 * m - i)) := by
  rw [pow_two]
  change VOA.mk (V2mPlus m hm) (EP m hm) * VOA.mk (V2mPlus m hm) (EP m hm) = _
  rw [← mk_zhuMul, E_zhuMul_E, squareState, map_sum]
  simp only [map_smul]

end VOA.Classification.COne.PlusZhuSchur
