/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.SymbolModelJetImage
import VOA.Examples.CyclicEvalEndpoint

/-!
# The cyclic dual vector of the polynomial image `A_r` (input (A) for the image)

Evaluation at the base point is a
cyclic vector of the restricted dual of `A_r`, with highest Cartan algebra the symmetric
polynomials in `r` variables. Here this is proved for the concrete `A_r = jetImage r`:

* `killU` — the algebra map `u ↦ 0`; it commutes with every `h_m`, fixes the evaluation, kills
  the coefficients of `X, Y, J` and fixes those of `Z = v²`, so it maps `A_r` into `Z`-products;
* `jetDer_h_zprod` — `h_m (Z_{a_1} ⋯ Z_{a_r}) = -2 Σ_i [m ≤ a_i] Z_{a_1} ⋯ Z_{a_i - m} ⋯ Z_{a_r}`;
* `cartanCalc_zSeries` — on the generating series `𝒵 = Σ_a Z_{a_1} ⋯ Z_{a_r} s^a` the Cartan
  calculus `F ↦ F(-h_1, -h_2, …)` acts by multiplication by `cartanEval r F`
  (`H_{i+1} ↦ 2 Σ_j s_j^{i+1}`); hence it kills every `Z`-product when `F ∈ I_r`;
* `jetCyclicDual r : CyclicDual (jetImgRho r) bHZero bHPos (jetDeg r) r` — **input (A) for the
  polynomial image, proved outright**: cyclic (`jet_cyclic`), supported in conformal degree `r`,
  of charge `2r`, with the relations (A1).

Everything is proved outright.
-/

namespace VOA.SymbolModel

open MvPolynomial VOA.CyclicEval VOA.InvariantSymbol

noncomputable section

/-! ### Killing `u` -/

/-- `u_j ↦ 0`, `v_j ↦ v_j`. -/
def killU : JetPoly →ₐ[ℂ] JetPoly := aeval fun x => if x.1 = 0 then 0 else X x

@[simp] theorem killU_X (x : Fin 2 × ℕ) : killU (X x) = if x.1 = 0 then 0 else X x := aeval_X _ _

theorem killU_shiftVar_zero (m j : ℕ) : killU (shiftVar 0 m j) = 0 := by
  unfold shiftVar; split_ifs <;> simp

theorem killU_shiftVar_one (m j : ℕ) : killU (shiftVar 1 m j) = shiftVar 1 m j := by
  unfold shiftVar; split_ifs <;> simp

theorem evalBase_killU (Q : JetPoly) : evalBase (killU Q) = evalBase Q := by
  have h : evalBase.comp killU = evalBase := algHom_ext fun x => by
    obtain ⟨b, j⟩ := x
    simp only [AlgHom.comp_apply, killU_X]
    split_ifs with hb
    · simp [evalBase, baseVal, hb]
    · rfl
  exact AlgHom.congr_fun h Q

theorem killU_jetDer_h (m : ℕ) (Q : JetPoly) :
    killU (jetDer (2, m) Q) = jetDer (2, m) (killU Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [← algebraMap_eq, Derivation.map_algebraMap, AlgHom.commutes, Derivation.map_algebraMap,
      map_zero]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p x hp =>
    rw [Derivation.leibniz, map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add,
      map_mul, map_mul, hp, smul_eq_mul, smul_eq_mul]
    congr 1
    obtain ⟨b, j⟩ := x
    congr 1
    fin_cases b
    · simp [jetDerVal, killU_shiftVar_zero]
    · simp [jetDerVal, killU_shiftVar_one]

/-! ### `killU` on the generators -/

/-- `killU` as a ring hom. -/
abbrev killUR : JetPoly →+* JetPoly := killU

theorem killU_coeff (f : JetSer) (n : ℕ) :
    killU (PowerSeries.coeff n f) = PowerSeries.coeff n (PowerSeries.map killUR f) := by
  rw [PowerSeries.coeff_map]; rfl

theorem map_killU_colSer_zero : PowerSeries.map killUR (colSer 0) = 0 := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_map, colSer, PowerSeries.coeff_mk]; simp

theorem map_killU_colSer_one : PowerSeries.map killUR (colSer 1) = colSer 1 := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_map, colSer, PowerSeries.coeff_mk]; simp

theorem map_killU_dS (f : JetSer) :
    PowerSeries.map killUR (dS f) = dS (PowerSeries.map killUR f) := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_map, PowerSeries.coeff_derivative, PowerSeries.coeff_derivative,
    PowerSeries.coeff_map, map_mul]
  congr 1
  rw [map_add, map_natCast, map_one]

theorem killU_genCoeff (g : Fin 4) (a : ℕ) :
    killU (genCoeff g a) = if g = 2 then genCoeff g a else 0 := by
  rw [genCoeff, killU_coeff]
  fin_cases g
  · simp [genSer_zero, xSer, map_killU_colSer_zero]
  · simp [genSer_one, ySer, map_killU_colSer_zero]
  · simp [genSer_two, zSer, map_killU_colSer_one]
  · simp [genSer_three, jSer, map_killU_dS, map_killU_colSer_zero]

/-- The span of the coefficients of `Z = v²`. -/
def zSpan : Submodule ℂ JetPoly := Submodule.span ℂ (Set.range (genCoeff 2))

theorem killU_genSpan : ∀ x ∈ genSpan, killU x ∈ zSpan := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨g, a⟩, rfl⟩ := hx
    rw [killU_genCoeff]
    split_ifs with hg
    · subst hg; exact Submodule.subset_span ⟨a, rfl⟩
    · exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/-- The product `Z_{a_1} ⋯ Z_{a_r}`. -/
def zprod {r : ℕ} (a : Fin r → ℕ) : JetPoly := ∏ i, genCoeff 2 (a i)

theorem zSpan_pow_le (r : ℕ) : zSpan ^ r ≤ Submodule.span ℂ (Set.range (zprod (r := r))) := by
  induction r with
  | zero =>
    rw [pow_zero, Submodule.one_eq_span]
    exact Submodule.span_mono (by
      rintro _ rfl
      exact ⟨Fin.elim0, by simp [zprod]⟩)
  | succ r ih =>
    rw [pow_succ]
    refine (Submodule.mul_le.mpr fun m hm n hn => Submodule.mul_mem_mul (ih hm) hn).trans ?_
    rw [zSpan, Submodule.span_mul_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨x, ⟨a, rfl⟩, y, ⟨b, rfl⟩, rfl⟩
    refine ⟨Fin.snoc a b, ?_⟩
    simp [zprod, Fin.prod_univ_castSucc]

theorem killU_jetImage (r : ℕ) : ∀ x ∈ jetImage r, killU x ∈ zSpan ^ r := by
  induction r with
  | zero =>
    intro x hx
    rw [jetImage, pow_zero, Submodule.mem_one] at hx
    obtain ⟨c, rfl⟩ := hx
    rw [AlgHom.commutes, pow_zero]
    exact Submodule.algebraMap_mem c
  | succ r ih =>
    intro x hx
    rw [jetImage, pow_succ] at hx
    rw [pow_succ]
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro m hm n hn
      rw [map_mul]
      exact Submodule.mul_mem_mul (ih m hm) (killU_genSpan n hn)
    · intro x y hx hy; rw [map_add]; exact add_mem hx hy

/-! ### `h_m` on `Z`-products -/

theorem jetDer_h_zCoeff (m n : ℕ) :
    jetDer (2, m) (genCoeff 2 n) = -2 * (if m ≤ n then genCoeff 2 (n - m) else 0) := by
  rw [jetDer_genCoeff, genSer_two, serD_zSer, serD_h_v]
  have : -(sX ^ m * colSer 1) * colSer 1 + colSer 1 * -(sX ^ m * colSer 1) =
      -(2 : JetSer) * (sX ^ m * zSer) := by rw [zSer]; ring
  rw [this, show (-(2 : JetSer)) = PowerSeries.C (-2 : JetPoly) by rw [map_neg, map_ofNat],
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  rfl

theorem derivation_prod {ι : Type*} [DecidableEq ι] (D : Derivation ℂ JetPoly JetPoly)
    (s : Finset ι) (f : ι → JetPoly) :
    D (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * D (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha, Finset.erase_insert ha,
      smul_eq_mul, smul_eq_mul, Finset.mul_sum, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hia : i ≠ a := fun h => ha (h ▸ hi)
    rw [Finset.erase_insert_of_ne (Ne.symm hia), Finset.prod_insert (fun h => ha
      (Finset.mem_of_mem_erase h))]
    ring

/-- **`h_m` on a `Z`-product.** -/
theorem jetDer_h_zprod {r : ℕ} (m : ℕ) (a : Fin r → ℕ) :
    jetDer (2, m) (zprod a) = ∑ i, (∏ j ∈ Finset.univ.erase i, genCoeff 2 (a j)) *
      (-2 * (if m ≤ a i then genCoeff 2 (a i - m) else 0)) := by
  rw [zprod, derivation_prod]
  simp only [jetDer_h_zCoeff]

/-- `h₀` acts by `-2r` on `Z`-products. -/
theorem jetDer_h0_zprod {r : ℕ} (a : Fin r → ℕ) :
    jetDer (2, 0) (zprod a) = (-(2 * (r : ℂ))) • zprod a := by
  rw [jetDer_h_zprod]
  simp only [zero_le, if_true, Nat.sub_zero]
  have : ∀ i, (∏ j ∈ Finset.univ.erase i, genCoeff 2 (a j)) * (-2 * genCoeff 2 (a i)) =
      (-2 : JetPoly) * zprod a := by
    intro i
    rw [zprod, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]; ring
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Algebra.smul_def]
  simp only [map_neg, map_mul, map_ofNat, map_natCast]
  ring

theorem jetDer_h0_span_zprod (r : ℕ) :
    ∀ x ∈ Submodule.span ℂ (Set.range (zprod (r := r))),
      jetDer (2, 0) x = (-(2 * (r : ℂ))) • x := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact jetDer_h0_zprod a
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul c x _ hx => rw [Derivation.map_smul, hx, smul_comm]

theorem jetDer_h0_zSpan_pow (r : ℕ) :
    ∀ x ∈ zSpan ^ r, jetDer (2, 0) x = (-(2 * (r : ℂ))) • x :=
  fun x hx => jetDer_h0_span_zprod r x (zSpan_pow_le r hx)

/-! ### Commutation of the Cartan derivations -/

theorem jetDer_h_shiftVar_zero (a b j : ℕ) :
    jetDer (2, a) (shiftVar 0 b j) = shiftVar 0 (b + a) j := by
  unfold shiftVar
  by_cases h1 : b ≤ j
  · rw [if_pos h1, jetDer_X]
    simp only [jetDerVal, shiftVar]
    simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
    by_cases h2 : b + a ≤ j
    · rw [if_pos (by omega), if_pos h2, Nat.sub_sub]
    · rw [if_neg (by omega), if_neg h2]
  · rw [if_neg h1, map_zero, if_neg (by omega)]

theorem jetDer_h_shiftVar_one (a b j : ℕ) :
    jetDer (2, a) (shiftVar 1 b j) = -shiftVar 1 (b + a) j := by
  unfold shiftVar
  by_cases h1 : b ≤ j
  · rw [if_pos h1, jetDer_X]
    simp only [jetDerVal, shiftVar]
    simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
    by_cases h2 : b + a ≤ j
    · rw [if_pos (by omega), if_pos h2, Nat.sub_sub]
    · rw [if_neg (by omega), if_neg h2, neg_zero]
  · rw [if_neg h1, map_zero, if_neg (by omega), neg_zero]

/-- The Cartan derivations `h_a`, `h_b` commute. -/
theorem jetDer_h_comm (a b : ℕ) (Q : JetPoly) :
    jetDer (2, a) (jetDer (2, b) Q) = jetDer (2, b) (jetDer (2, a) Q) := by
  have h : ⁅jetDer (2, a), jetDer (2, b)⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    rintro ⟨c, j⟩
    rw [Derivation.commutator_apply, Derivation.zero_apply, jetDer_X, jetDer_X]
    fin_cases c
    · simp only [jetDerVal, Fin.isValue, Fin.reduceEq, ↓reduceIte, Fin.zero_eta]
      rw [jetDer_h_shiftVar_zero, jetDer_h_shiftVar_zero, add_comm, sub_self]
    · simp only [jetDerVal, Fin.isValue, Fin.reduceEq, ↓reduceIte, Fin.mk_one, map_neg]
      rw [jetDer_h_shiftVar_one, jetDer_h_shiftVar_one, add_comm, sub_self]
  have := congrArg (fun D : Derivation ℂ JetPoly JetPoly => D Q) h
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at this
  exact sub_eq_zero.mp this

theorem jetCartanCommute : CartanCommute jetRho bHPos := fun i j =>
  LinearMap.ext fun Q => jetDer_h_comm (i + 1) (j + 1) Q

/-! ### The generating series of `Z`-products -/

/-- `𝒵 = Σ_a Z_{a_1} ⋯ Z_{a_r} s^a`. -/
def zSeries (r : ℕ) : MvPowerSeries (Fin r) JetPoly := fun a => zprod (r := r) a

theorem coeff_zSeries (r : ℕ) (a : Fin r →₀ ℕ) :
    MvPowerSeries.coeff a (zSeries r) = zprod (r := r) a := rfl

/-- A linear map applied coefficientwise. -/
def serDM {r : ℕ} (T : JetPoly →ₗ[ℂ] JetPoly) (f : MvPowerSeries (Fin r) JetPoly) :
    MvPowerSeries (Fin r) JetPoly := fun a => T (MvPowerSeries.coeff a f)

theorem coeff_serDM {r : ℕ} (T : JetPoly →ₗ[ℂ] JetPoly) (f : MvPowerSeries (Fin r) JetPoly)
    (a : Fin r →₀ ℕ) : MvPowerSeries.coeff a (serDM T f) = T (MvPowerSeries.coeff a f) := rfl

/-- Scalar polynomials as jet-coefficient power series. -/
def liftHom (r : ℕ) : MvPolynomial (Fin r) ℂ →+* MvPowerSeries (Fin r) JetPoly :=
  (MvPowerSeries.map (algebraMap ℂ JetPoly)).comp MvPolynomial.coeToMvPowerSeries.ringHom

theorem coeff_liftHom (r : ℕ) (γ : MvPolynomial (Fin r) ℂ) (a : Fin r →₀ ℕ) :
    MvPowerSeries.coeff a (liftHom r γ) = algebraMap ℂ JetPoly (MvPolynomial.coeff a γ) := by
  simp [liftHom, MvPowerSeries.coeff_map, MvPolynomial.coeff_coe]

theorem serDM_liftHom_mul {r : ℕ} (T : JetPoly →ₗ[ℂ] JetPoly) (γ : MvPolynomial (Fin r) ℂ)
    (f : MvPowerSeries (Fin r) JetPoly) :
    serDM T (liftHom r γ * f) = liftHom r γ * serDM T f := by
  classical
  refine MvPowerSeries.ext fun a => ?_
  rw [coeff_serDM, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [coeff_liftHom, ← Algebra.smul_def, map_smul, Algebra.smul_def, coeff_serDM]

theorem liftHom_psum (r m : ℕ) :
    liftHom r (MvPolynomial.C 2 * psum (Fin r) ℂ m) =
      ∑ i, MvPowerSeries.C (2 : JetPoly) * MvPowerSeries.X i ^ m := by
  simp only [liftHom, psum, RingHom.comp_apply, map_mul, map_sum, map_pow,
    MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_C, MvPolynomial.coe_X,
    MvPowerSeries.map_C, MvPowerSeries.map_X, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2

theorem coeff_X_pow_mul_zSeries {r : ℕ} (i : Fin r) (m : ℕ) (a : Fin r →₀ ℕ) :
    MvPowerSeries.coeff a (MvPowerSeries.X i ^ m * zSeries r) =
      if m ≤ a i then zprod (r := r) (a - Finsupp.single i m) else 0 := by
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial_mul, one_mul, coeff_zSeries]
  congr 1
  exact propext Finsupp.single_le_iff

theorem zprod_sub_single {r : ℕ} (i : Fin r) (m : ℕ) (a : Fin r →₀ ℕ) :
    zprod (r := r) (a - Finsupp.single i m) =
      (∏ j ∈ Finset.univ.erase i, genCoeff 2 (a j)) * genCoeff 2 (a i - m) := by
  classical
  rw [zprod, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  congr 1
  · refine Finset.prod_congr rfl fun j hj => ?_
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [Ne.symm hji]
  · simp

/-- **`h_m` on the generating series**: multiplication by `-2 Σ_i s_i^m`. -/
theorem serDM_h_zSeries (r m : ℕ) :
    serDM (jetRho (2, m)) (zSeries r) =
      -(liftHom r (MvPolynomial.C 2 * psum (Fin r) ℂ m)) * zSeries r := by
  refine MvPowerSeries.ext fun a => ?_
  rw [coeff_serDM, coeff_zSeries, jetRho_apply, jetDer_h_zprod, liftHom_psum, neg_mul,
    map_neg, Finset.sum_mul, map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, MvPowerSeries.coeff_C_mul, coeff_X_pow_mul_zSeries]
  split_ifs with h
  · rw [zprod_sub_single]; ring
  · simp

theorem serDM_add {r : ℕ} (T T' : JetPoly →ₗ[ℂ] JetPoly) (f : MvPowerSeries (Fin r) JetPoly) :
    serDM (T + T') f = serDM T f + serDM T' f := rfl

theorem serDM_mul {r : ℕ} (T T' : JetPoly →ₗ[ℂ] JetPoly) (f : MvPowerSeries (Fin r) JetPoly) :
    serDM (T * T') f = serDM T (serDM T' f) := rfl

theorem serDM_neg {r : ℕ} (T : JetPoly →ₗ[ℂ] JetPoly) (f : MvPowerSeries (Fin r) JetPoly) :
    serDM (-T) f = -serDM T f := rfl

/-- The Cartan calculus on the full jet ring. -/
abbrev jetCalc : MvPolynomial ℕ ℂ →ₐ[ℂ] Module.End ℂ JetPoly :=
  cartanCalc jetRho bHPos jetCartanCommute

/-- **The Cartan calculus on `𝒵` is multiplication by `cartanEval r F`.** -/
theorem cartanCalc_zSeries (r : ℕ) (F : MvPolynomial ℕ ℂ) :
    serDM (jetCalc F) (zSeries r) = liftHom r (cartanEval r F) * zSeries r := by
  induction F using MvPolynomial.induction_on with
  | C c =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgHom.commutes, MvPolynomial.algebraMap_eq,
      Algebra.algebraMap_eq_smul_one]
    refine MvPowerSeries.ext fun a => ?_
    rw [coeff_serDM, LinearMap.smul_apply, Module.End.one_apply, liftHom, RingHom.comp_apply]
    simp [MvPolynomial.coe_C, MvPowerSeries.map_C, MvPowerSeries.coeff_C_mul, Algebra.smul_def]
  | add p q hp hq => rw [map_add, serDM_add, hp, hq, map_add, map_add, add_mul]
  | mul_X p i hp =>
    have hX : cartanEval r (X i) = cartanGen r i := aeval_X _ _
    rw [show cartanEval r (p * X i) = cartanEval r p * cartanGen r i by rw [map_mul, hX],
      map_mul, serDM_mul, cartanCalc_X, serDM_neg, serDM_h_zSeries, neg_mul, neg_neg,
      serDM_liftHom_mul, hp, cartanGen]
    simp only [map_mul]
    ring

theorem jetCalc_zprod (r : ℕ) {F : MvPolynomial ℕ ℂ} (hF : F ∈ cartanIdeal r)
    (a : Fin r → ℕ) : jetCalc F (zprod a) = 0 := by
  have h := congrArg (MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm a))
    (cartanCalc_zSeries r F)
  have hF' : cartanEval r F = 0 := hF
  rw [hF', map_zero, zero_mul, map_zero, coeff_serDM, coeff_zSeries] at h
  simpa using h

theorem jetCalc_span_zprod (r : ℕ) {F : MvPolynomial ℕ ℂ} (hF : F ∈ cartanIdeal r) :
    ∀ x ∈ Submodule.span ℂ (Set.range (zprod (r := r))), jetCalc F x = 0 := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact jetCalc_zprod r hF a
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

theorem jetCalc_zSpan_pow (r : ℕ) {F : MvPolynomial ℕ ℂ} (hF : F ∈ cartanIdeal r) :
    ∀ x ∈ zSpan ^ r, jetCalc F x = 0 :=
  fun x hx => jetCalc_span_zprod r hF x (zSpan_pow_le r hx)

end

end VOA.SymbolModel
