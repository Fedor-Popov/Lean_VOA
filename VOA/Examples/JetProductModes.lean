/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.AdamovicSymbolJet

/-!
# Symmetric-function operators on the jet ring

The derivation `D_k : u(s) ↦ s^k u(s), v(s) ↦ s^k v(s)` of `ℂ[u_j, v_j]` multiplies each of the
four generator series `X = u², Y = uv, Z = v², J = u'v - uv'` by `2 s^k`.  Consequently, on the
products `P_{w,a} = ∏_i G_{w_i, a_i}` of `r` generator coefficients, `D_k / 2` acts on generating
functions `Σ_a φ(P_{w,a}) t^a` as multiplication by the power sum `p_k(t_1, …, t_r)`.

* `sDer k` — the derivation `D_k`;
* `Pga w a` — the product `∏_i G_{w_i, a_i}` (in `A_r`, of jet weight `Σ a_i + #J`);
* `Gam φ w` — the generating series `Σ_a φ(P_{w,a}) t^a` of a functional `φ`;
* `realizable_esymmPow` — every monomial `∏ e_{i+1}^{α_i}` in the elementary symmetric
  polynomials of `t_1, …, t_r` is realized by an operator `E` on the jet ring:
  `Gam (φ ∘ E) w = e^α · Gam φ w` for all `φ, w` (Newton's identities).

Everything is proved outright.
-/

namespace VOA.JetProduct

open MvPolynomial VOA.SymbolModel
open scoped BigOperators

noncomputable section

/-! ### The derivation `D_k` -/

/-- The derivation `u(s) ↦ s^k u(s)`, `v(s) ↦ s^k v(s)`. -/
def sDer (k : ℕ) : Derivation ℂ JetPoly JetPoly := mkDerivation ℂ fun x => shiftVar x.1 k x.2

@[simp] theorem sDer_X (k : ℕ) (x : Fin 2 × ℕ) : sDer k (X x) = shiftVar x.1 k x.2 :=
  mkDerivation_X _ _ _

theorem serD_sDer_col (k : ℕ) (b : Fin 2) :
    serD (sDer k).toLinearMap (colSer b) = sX ^ k * colSer b := by
  ext n
  rw [coeff_X_pow_mul_colSer, coeff_serD]
  simp [colSer]

theorem serD_sDer_gen (k : ℕ) (g : Fin 4) :
    serD (sDer k).toLinearMap (genSer g) = sX ^ k * (genSer g + genSer g) := by
  fin_cases g
  · change serD _ xSer = _
    rw [serD_xSer, serD_sDer_col]
    simp only [genSer, Fin.zero_eta, Matrix.cons_val_zero, xSer]; ring
  · change serD _ ySer = _
    rw [serD_ySer, serD_sDer_col, serD_sDer_col]
    simp only [genSer, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, ySer]; ring
  · change serD _ zSer = _
    rw [serD_zSer, serD_sDer_col]
    simp only [genSer, Fin.reduceFinMk, Matrix.cons_val, zSer]; ring
  · change serD _ jSer = _
    rw [serD_jSer, serD_sDer_col, serD_sDer_col, Derivation.leibniz, Derivation.leibniz]
    simp only [genSer, Fin.reduceFinMk, Matrix.cons_val, jSer, smul_eq_mul]; ring

theorem sDer_genCoeff (k : ℕ) (g : Fin 4) (a : ℕ) :
    sDer k (genCoeff g a) = if k ≤ a then 2 * genCoeff g (a - k) else 0 := by
  have h := congrArg (PowerSeries.coeff a) (serD_sDer_gen k g)
  rw [coeff_serD, PowerSeries.coeff_X_pow_mul'] at h
  change sDer k (genCoeff g a) = _
  rw [show (sDer k) (genCoeff g a) = (sDer k).toLinearMap (PowerSeries.coeff a (genSer g)) from rfl,
    h]
  split_ifs
  · rw [map_add, two_mul]; rfl
  · rfl

/-- The Leibniz rule for a finite product. -/
theorem deriv_prod {ι : Type*} [DecidableEq ι] (D : Derivation ℂ JetPoly JetPoly)
    (f : ι → JetPoly) (s : Finset ι) :
    D (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * D (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Derivation.leibniz, ih, Finset.sum_insert hi,
      Finset.erase_insert hi, smul_eq_mul, smul_eq_mul, Finset.mul_sum, add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := fun h => hi (h ▸ hj)
    rw [Finset.erase_insert_of_ne hji.symm,
      Finset.prod_insert (fun h => hi (Finset.mem_of_mem_erase h))]
    ring

/-! ### Products of generator coefficients -/

/-- The product `∏_i G_{w_i, a_i}` of `r` generator coefficients. -/
def Pga {r : ℕ} (w : Fin r → Fin 4) (a : Fin r →₀ ℕ) : JetPoly := ∏ i, genCoeff (w i) (a i)

theorem sDer_Pga {r : ℕ} (k : ℕ) (w : Fin r → Fin 4) (a : Fin r →₀ ℕ) :
    sDer k (Pga w a) = ∑ i, if k ≤ a i then 2 * Pga w (a - Finsupp.single i k) else 0 := by
  classical
  rw [Pga, deriv_prod]
  apply Finset.sum_congr rfl
  intro i _
  rw [sDer_genCoeff]
  split_ifs with h
  · rw [Pga, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    have hrest : ∏ j ∈ Finset.univ.erase i, genCoeff (w j) ((a - Finsupp.single i k) j) =
        ∏ j ∈ Finset.univ.erase i, genCoeff (w j) (a j) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Finset.ne_of_mem_erase hj).symm,
        Nat.sub_zero]
    rw [hrest, Finsupp.tsub_apply, Finsupp.single_eq_same]
    ring
  · rw [mul_zero]

/-! ### Generating series of functionals -/

/-- The generating series `Σ_a φ(P_{w,a}) t^a`. -/
def Gam {r : ℕ} (φ : JetPoly →ₗ[ℂ] ℂ) (w : Fin r → Fin 4) : MvPowerSeries (Fin r) ℂ :=
  fun a => φ (Pga w a)

theorem coeff_Gam {r : ℕ} (φ : JetPoly →ₗ[ℂ] ℂ) (w : Fin r → Fin 4) (a : Fin r →₀ ℕ) :
    MvPowerSeries.coeff a (Gam φ w) = φ (Pga w a) := rfl

/-- The operator `D_k / 2`. -/
def halfSDer (k : ℕ) : Module.End ℂ JetPoly := (1 / 2 : ℂ) • (sDer k).toLinearMap

theorem coe_psum_coeff {r : ℕ} (k : ℕ) (F : MvPowerSeries (Fin r) ℂ) (a : Fin r →₀ ℕ) :
    MvPowerSeries.coeff a (((psum (Fin r) ℂ k : MvPolynomial (Fin r) ℂ) :
      MvPowerSeries (Fin r) ℂ) * F) =
      ∑ i, if k ≤ a i then MvPowerSeries.coeff (a - Finsupp.single i k) F else 0 := by
  rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, psum, map_sum, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_pow, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_X,
    MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial_mul, one_mul]
  congr 1
  apply propext
  rw [Finsupp.single_le_iff]

/-- `D_k / 2` acts on generating series as multiplication by the power sum `p_k(t)`. -/
theorem Gam_halfSDer {r : ℕ} (k : ℕ) (φ : JetPoly →ₗ[ℂ] ℂ) (w : Fin r → Fin 4) :
    Gam (φ ∘ₗ halfSDer k) w = ((psum (Fin r) ℂ k : MvPolynomial (Fin r) ℂ) :
      MvPowerSeries (Fin r) ℂ) * Gam φ w := by
  ext a
  rw [coe_psum_coeff, coeff_Gam]
  simp only [LinearMap.coe_comp, Function.comp_apply, halfSDer, LinearMap.smul_apply,
    Derivation.coeFn_coe, sDer_Pga, map_smul, map_sum]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · rw [coeff_Gam, smul_eq_mul, show (2 : JetPoly) * Pga w (a - Finsupp.single i k) =
      (2 : ℂ) • Pga w (a - Finsupp.single i k) by rw [MvPolynomial.smul_eq_C_mul]; rfl, map_smul,
      smul_eq_mul]
    ring
  · simp

/-! ### Realizable multipliers -/

/-- A polynomial `f(t)` is realizable if some operator acts on all generating series as
multiplication by `f`. -/
def Realizable (r : ℕ) (f : MvPolynomial (Fin r) ℂ) : Prop :=
  ∃ E : Module.End ℂ JetPoly, ∀ (φ : JetPoly →ₗ[ℂ] ℂ) (w : Fin r → Fin 4),
    Gam (φ ∘ₗ E) w = (f : MvPowerSeries (Fin r) ℂ) * Gam φ w

/-- The realizable polynomials form a subalgebra. -/
def realizableSubalgebra (r : ℕ) : Subalgebra ℂ (MvPolynomial (Fin r) ℂ) where
  carrier := {f | Realizable r f}
  mul_mem' := by
    rintro f g ⟨E, hE⟩ ⟨E', hE'⟩
    refine ⟨E * E', fun φ w => ?_⟩
    rw [Module.End.mul_eq_comp, ← LinearMap.comp_assoc, hE', hE, MvPolynomial.coe_mul]
    ring
  add_mem' := by
    rintro f g ⟨E, hE⟩ ⟨E', hE'⟩
    refine ⟨E + E', fun φ w => ?_⟩
    ext a
    have h1 := congrArg (MvPowerSeries.coeff a) (hE φ w)
    have h2 := congrArg (MvPowerSeries.coeff a) (hE' φ w)
    rw [coeff_Gam] at h1 h2 ⊢
    rw [MvPolynomial.coe_add, add_mul, map_add, ← h1, ← h2]
    simp
  algebraMap_mem' := by
    intro c
    refine ⟨c • (1 : Module.End ℂ JetPoly), fun φ w => ?_⟩
    ext a
    rw [coeff_Gam, MvPolynomial.algebraMap_eq, MvPolynomial.coe_C,
      MvPowerSeries.coeff_C_mul, coeff_Gam]
    simp

theorem realizable_psum (r k : ℕ) (_hk : 1 ≤ k) :
    psum (Fin r) ℂ k ∈ realizableSubalgebra r :=
  ⟨halfSDer k, fun φ w => Gam_halfSDer k φ w⟩

theorem realizable_esymm (r : ℕ) : ∀ k, esymm (Fin r) ℂ k ∈ realizableSubalgebra r := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [esymm_zero]; exact Subalgebra.one_mem _
  have hmul : (k : MvPolynomial (Fin r) ℂ) * esymm (Fin r) ℂ k ∈ realizableSubalgebra r := by
    rw [mul_esymm_eq_sum]
    refine Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.neg_mem _
      (Subalgebra.one_mem _)) _) (Subalgebra.sum_mem _ fun a ha => ?_)
    rw [Finset.mem_filter, Finset.mem_antidiagonal] at ha
    refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _
      (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _) (ih a.1 ha.2)) ?_
    exact realizable_psum r a.2 (by omega)
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have : esymm (Fin r) ℂ k = (k : ℂ)⁻¹ • ((k : MvPolynomial (Fin r) ℂ) * esymm (Fin r) ℂ k) := by
    rw [smul_eq_C_mul, ← mul_assoc,
      ← map_natCast (MvPolynomial.C : ℂ →+* MvPolynomial (Fin r) ℂ), ← map_mul,
      inv_mul_cancel₀ hk', map_one, one_mul]
  rw [this]
  exact Subalgebra.smul_mem _ hmul _

/-- The monomial `∏_i e_{i+1}(t)^{α_i}` in the elementary symmetric polynomials. -/
def esymmPow {r : ℕ} (α : Fin r → ℕ) : MvPolynomial (Fin r) ℂ :=
  ∏ i : Fin r, esymm (Fin r) ℂ ((i : ℕ) + 1) ^ α i

/-- Every elementary-symmetric monomial is realizable. -/
theorem realizable_esymmPow {r : ℕ} (α : Fin r → ℕ) : Realizable r (esymmPow α) :=
  Subalgebra.prod_mem _ fun _ _ => Subalgebra.pow_mem _ (realizable_esymm r _) _

/-- The operator realizing `e^α`. -/
def opE {r : ℕ} (α : Fin r → ℕ) : Module.End ℂ JetPoly := (realizable_esymmPow α).choose

theorem Gam_opE {r : ℕ} (α : Fin r → ℕ) (φ : JetPoly →ₗ[ℂ] ℂ) (w : Fin r → Fin 4) :
    Gam (φ ∘ₗ opE α) w = (esymmPow α : MvPowerSeries (Fin r) ℂ) * Gam φ w :=
  (realizable_esymmPow α).choose_spec φ w

end

end VOA.JetProduct
