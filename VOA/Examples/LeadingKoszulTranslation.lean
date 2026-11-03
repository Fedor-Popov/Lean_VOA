/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.LeadingKoszulWeyl
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Algebra.Algebra.Rat

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

/-!
# The translated polynomial sequence `x_i + a_i` is Koszul-regular

This file instantiates `WeylDatum` for the sequence of the explicit leading contraction in
the coset BRST–Koszul transfer argument:
over a commutative `ℚ`-algebra `A` (in that argument, the commutative symbol algebra `gr A`;
no freeness, reducedness or regularity *inside* `A` is used) and finitely many free
variables `x_i` (the auxiliary universal PBW symbols at a fixed weight), the sequence

  `U_i = x_i + a_i`, `a_i ∈ A` arbitrary,

acting by multiplication on `A[x]`, with partner derivations `∂/∂x_i`.

## Results

* `translationEquiv` : the `A`-algebra automorphism `x ↦ x + a` of `A[x]`, with
  `pderiv_translation` (`∂_i` commutes with it).
* `translatedWeyl a : WeylDatum A ι A[x]` — in particular `L + k` is bijective for `k ≥ 1`
  (`L = Σ (x_i + a_i) ∂_i` is the Euler operator conjugated by the translation).
* `translatedAug a` : the augmentation `ε = evaluation at x = -a` (`translatedAug_ε`).
* `translated_exists_kd_eq` (**Koszul acyclicity in positive degree** for `x + a`) and
  `translatedKoszulH0Equiv` (**Koszul `H₀ ≅ A`, with every `x_i` eliminated as `-a_i`**).

Everything is proved outright.
-/

namespace VOA.LeadingKoszul

open MvPolynomial

universe u w

variable {A : Type u} [CommRing A] [Algebra ℚ A]
variable {ι : Type w} [Fintype ι] [LinearOrder ι]

namespace Translation

/-- The total degree `Σ_i m_i` of an exponent. -/
def wt (m : ι →₀ ℕ) : ℕ := ∑ i, m i

theorem wt_eq_zero {m : ι →₀ ℕ} (h : wt m = 0) : m = 0 := by
  ext i
  exact (Finset.sum_eq_zero_iff.mp h) i (Finset.mem_univ i)

/-- Linear maps out of `A[x]` agree if they agree on the monomials `x^m`. -/
theorem lin_ext {M : Type*} [AddCommGroup M] [Module A M]
    {f g : MvPolynomial ι A →ₗ[A] M} (h : ∀ m, f (monomial m 1) = g (monomial m 1)) : f = g :=
  (basisMonomials ι A).ext fun m => by simpa [coe_basisMonomials] using h m

variable (A ι) in
/-- The Euler operator `Σ_i x_i ∂_i`. -/
noncomputable def euler : MvPolynomial ι A →ₗ[A] MvPolynomial ι A :=
  ∑ i, (LinearMap.mulLeft A (X i : MvPolynomial ι A)).comp (pderiv i).toLinearMap

theorem euler_apply (p : MvPolynomial ι A) : euler A ι p = ∑ i, X i * pderiv i p := by
  simp [euler, LinearMap.sum_apply]

theorem euler_monomial (m : ι →₀ ℕ) (r : A) :
    euler A ι (monomial m r) = (wt m : A) • monomial m r := by
  rw [euler_apply]
  simp_rw [X_mul_pderiv_monomial]
  rw [← Finset.sum_smul, Nat.cast_smul_eq_nsmul, wt]

/-- Coefficientwise scaling of monomials. -/
noncomputable def scal (c : (ι →₀ ℕ) → A) : MvPolynomial ι A →ₗ[A] MvPolynomial ι A :=
  (basisMonomials ι A).constr A fun m => c m • monomial m 1

theorem scal_monomial (c : (ι →₀ ℕ) → A) (m : ι →₀ ℕ) (r : A) :
    scal c (monomial m r) = monomial m (c m * r) := by
  have hb : (basisMonomials ι A) m = monomial m 1 := by simp [coe_basisMonomials]
  rw [show monomial m r = r • (monomial m 1 : MvPolynomial ι A) by
      rw [smul_monomial, smul_eq_mul, mul_one], map_smul, ← hb, scal, Module.Basis.constr_basis,
    smul_smul, smul_monomial, smul_eq_mul, mul_one, mul_comm]

/-- `Euler + (k + 1)`. -/
noncomputable def ek (k : ℕ) : MvPolynomial ι A →ₗ[A] MvPolynomial ι A :=
  euler A ι + ((k + 1 : ℕ) : A) • LinearMap.id

theorem ek_monomial (k : ℕ) (m : ι →₀ ℕ) (r : A) :
    ek k (monomial m r) = monomial m (((wt m + k + 1 : ℕ) : A) * r) := by
  simp only [ek, LinearMap.add_apply, euler_monomial, LinearMap.smul_apply, LinearMap.id_apply,
    smul_monomial, smul_eq_mul]
  rw [← map_add]
  congr 1
  push_cast; ring

/-- In a `ℚ`-algebra a positive natural number is invertible. -/
theorem natInv_mul (n : ℕ) (hn : n ≠ 0) :
    algebraMap ℚ A ((n : ℚ)⁻¹) * (n : A) = 1 := by
  rw [← map_natCast (algebraMap ℚ A) n, ← map_mul, inv_mul_cancel₀ (by exact_mod_cast hn),
    map_one]

/-- The inverse of `ek k`. -/
noncomputable def ekInv (k : ℕ) : MvPolynomial ι A →ₗ[A] MvPolynomial ι A :=
  scal fun m => algebraMap ℚ A (((wt m + k + 1 : ℕ) : ℚ)⁻¹)

theorem ek_ekInv (k : ℕ) : (ek k).comp (ekInv k) = (LinearMap.id : MvPolynomial ι A →ₗ[A] _) := by
  refine lin_ext fun m => ?_
  rw [LinearMap.comp_apply, ekInv, scal_monomial, ek_monomial, mul_one, mul_comm,
    natInv_mul _ (by omega), LinearMap.id_apply]

theorem ekInv_ek (k : ℕ) : (ekInv k).comp (ek k) = (LinearMap.id : MvPolynomial ι A →ₗ[A] _) := by
  refine lin_ext fun m => ?_
  rw [LinearMap.comp_apply, ekInv, ek_monomial, scal_monomial, mul_one,
    natInv_mul _ (by omega), LinearMap.id_apply]

theorem ek_bijective (k : ℕ) : Function.Bijective (ek k : MvPolynomial ι A →ₗ[A] _) := by
  constructor
  · intro p q h
    have := congrArg (ekInv k) h
    rwa [← LinearMap.comp_apply, ekInv_ek, LinearMap.id_apply, ← LinearMap.comp_apply,
      ekInv_ek, LinearMap.id_apply] at this
  · intro p
    exact ⟨ekInv k p, by rw [← LinearMap.comp_apply, ek_ekInv, LinearMap.id_apply]⟩

/-- A partial inverse of the Euler operator, killing constants. -/
noncomputable def eulerInv : MvPolynomial ι A →ₗ[A] MvPolynomial ι A :=
  scal fun m => if wt m = 0 then 0 else algebraMap ℚ A ((wt m : ℚ)⁻¹)

/-- `euler ∘ eulerInv + C ∘ coeff₀ = id`. -/
theorem euler_eulerInv (p : MvPolynomial ι A) :
    euler A ι (eulerInv p) + C (coeff 0 p) = p := by
  have h : (euler A ι).comp eulerInv + (Algebra.linearMap A (MvPolynomial ι A)).comp (lcoeff A 0)
      = LinearMap.id := by
    refine lin_ext fun m => ?_
    simp only [LinearMap.add_apply, LinearMap.comp_apply, eulerInv, scal_monomial, mul_one,
      euler_monomial, lcoeff_apply, coeff_monomial, Algebra.linearMap_apply, LinearMap.id_apply]
    by_cases hm : wt m = 0
    · have := wt_eq_zero hm
      subst this
      simp [algebraMap_eq, hm]
    · have hm' : m ≠ 0 := by rintro rfl; exact hm (by simp [wt])
      rw [if_neg hm, if_neg hm', map_zero, add_zero, smul_monomial, smul_eq_mul,
        mul_comm, natInv_mul _ hm]
  have := LinearMap.congr_fun h p
  simpa [algebraMap_eq] using this

theorem coeff_zero_euler (p : MvPolynomial ι A) : coeff 0 (euler A ι p) = 0 := by
  have h : (lcoeff A 0).comp (euler A ι) = 0 := by
    refine lin_ext fun m => ?_
    simp only [LinearMap.comp_apply, euler_monomial, lcoeff_apply, coeff_smul, coeff_monomial,
      LinearMap.zero_apply, smul_eq_mul]
    by_cases hm : m = 0
    · subst hm; simp [wt]
    · simp [hm]
  exact LinearMap.congr_fun h p

/-! ### The translation `x ↦ x + a` -/

variable (a : ι → A)

/-- The translation `x_i ↦ x_i + a_i`. -/
noncomputable def tr : MvPolynomial ι A →ₐ[A] MvPolynomial ι A := aeval fun i => X i + C (a i)

/-- The inverse translation `x_i ↦ x_i - a_i`. -/
noncomputable def trInv : MvPolynomial ι A →ₐ[A] MvPolynomial ι A := aeval fun i => X i - C (a i)

theorem tr_trInv (p : MvPolynomial ι A) : tr a (trInv a p) = p := by
  have : (tr a).comp (trInv a) = AlgHom.id A _ := by
    refine algHom_ext fun i => ?_
    simp [tr, trInv, algebraMap_eq]
  exact AlgHom.congr_fun this p

theorem trInv_tr (p : MvPolynomial ι A) : trInv a (tr a p) = p := by
  have : (trInv a).comp (tr a) = AlgHom.id A _ := by
    refine algHom_ext fun i => ?_
    simp [tr, trInv, algebraMap_eq]
  exact AlgHom.congr_fun this p

/-- The translation as an algebra automorphism. -/
noncomputable def translationEquiv : MvPolynomial ι A ≃ₐ[A] MvPolynomial ι A :=
  AlgEquiv.ofAlgHom (tr a) (trInv a) (AlgHom.ext (tr_trInv a)) (AlgHom.ext (trInv_tr a))

theorem tr_C (r : A) : tr a (C r) = C r := by simp [tr, algebraMap_eq]

theorem tr_X (i : ι) : tr a (X i) = X i + C (a i) := by simp [tr]

/-- `∂_i` commutes with the translation (chain rule). -/
theorem pderiv_translation (i : ι) (p : MvPolynomial ι A) :
    pderiv i (tr a p) = tr a (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C r => rw [tr_C, pderiv_C, map_zero]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p j hp =>
    rw [map_mul, tr_X, pderiv_mul, hp, pderiv_mul, map_add (tr a), map_mul, map_mul, tr_X]
    congr 2
    rw [map_add, pderiv_C, add_zero]
    by_cases hij : j = i
    · subst hij; simp
    · rw [pderiv_X_of_ne hij, map_zero]

/-! ### The Weyl datum -/

/-- `∂_i ∂_j = ∂_j ∂_i`. -/
theorem pderiv_comm (i j : ι) (v : MvPolynomial ι A) :
    pderiv i (pderiv j v) = pderiv j (pderiv i v) := by
  have : ⁅(pderiv i : Derivation A (MvPolynomial ι A) (MvPolynomial ι A)), pderiv j⁆ = (0 : Derivation A (MvPolynomial ι A) (MvPolynomial ι A)) := by
    refine derivation_ext fun k => ?_
    rw [Derivation.commutator_apply]
    simp only [pderiv_X, Pi.single_apply]
    rw [apply_ite (pderiv j), apply_ite (pderiv i), pderiv_one, pderiv_one, map_zero, map_zero]
    simp
  have h := congrArg (fun D : Derivation A (MvPolynomial ι A) (MvPolynomial ι A) => D v) this
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at h
  exact sub_eq_zero.mp h

theorem pderiv_u (i j : ι) (v : MvPolynomial ι A) :
    pderiv i ((X j + C (a j)) * v) = (X j + C (a j)) * pderiv i v + if i = j then v else 0 := by
  rw [pderiv_mul, map_add, pderiv_C, add_zero]
  by_cases h : i = j
  · subst h; simp [add_comm]
  · rw [pderiv_X_of_ne (Ne.symm h), if_neg h]; simp

theorem sum_u_pderiv_tr (q : MvPolynomial ι A) :
    ∑ i, (X i + C (a i)) * pderiv i (tr a q) = tr a (euler A ι q) := by
  rw [euler_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pderiv_translation, map_mul, tr_X]

/-- **The Weyl datum of the translated sequence `x_i + a_i`.** -/
noncomputable def translatedWeyl : WeylDatum A ι (MvPolynomial ι A) where
  u i := LinearMap.mulLeft A (X i + C (a i))
  D i := (pderiv i).toLinearMap
  u_comm i j v := mul_left_comm _ _ _
  D_comm i j v := pderiv_comm i j v
  D_u i j v := pderiv_u a i j v
  bij k := by
    have hfun : ⇑(∑ i, (LinearMap.mulLeft A (X i + C (a i))).comp (pderiv i).toLinearMap +
        ((k + 1 : ℕ) : A) • (LinearMap.id : MvPolynomial ι A →ₗ[A] _)) =
        tr a ∘ ek k ∘ trInv a := by
      funext p
      simp only [Function.comp_apply, LinearMap.add_apply, LinearMap.sum_apply,
        LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe,
        LinearMap.smul_apply, LinearMap.id_apply]
      conv_lhs => rw [← tr_trInv a p]
      rw [sum_u_pderiv_tr, ek, LinearMap.add_apply, map_add, LinearMap.smul_apply,
        LinearMap.id_apply, map_smul]
    rw [hfun]
    exact (translationEquiv a).bijective.comp ((ek_bijective k).comp (translationEquiv a).symm.bijective)

theorem translatedWeyl_L (v : MvPolynomial ι A) :
    (translatedWeyl a).L v = ∑ i, (X i + C (a i)) * pderiv i v := by
  rw [WeylDatum.L_apply]; rfl

theorem trInv_L (v : MvPolynomial ι A) :
    trInv a ((translatedWeyl a).L v) = euler A ι (trInv a v) := by
  rw [translatedWeyl_L]
  conv_lhs => rw [← tr_trInv a v]
  rw [sum_u_pderiv_tr, trInv_tr]

/-- **The augmentation of the translated sequence**: `ε = coeff₀ ∘ (x ↦ x - a)`, which is
evaluation at `x = -a` (`translatedAug_ε`). -/
noncomputable def translatedAug : (translatedWeyl a).Augmentation A where
  ε := (lcoeff A 0).comp (trInv a).toLinearMap
  σ := (tr a).toLinearMap.comp (Algebra.linearMap A (MvPolynomial ι A))
  G := (tr a).toLinearMap.comp (eulerInv.comp (trInv a).toLinearMap)
  ε_L v := by
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, lcoeff_apply]
    rw [trInv_L, coeff_zero_euler]
  ε_σ q := by
    simp [algebraMap_eq]
  split v := by
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, lcoeff_apply,
      Algebra.linearMap_apply, algebraMap_eq]
    rw [translatedWeyl_L, sum_u_pderiv_tr, ← map_add, euler_eulerInv, tr_trInv]

/-- The augmentation is **evaluation at `x = -a`**: every `x_i` is eliminated as `-a_i`. -/
theorem translatedAug_ε (p : MvPolynomial ι A) :
    (translatedAug a).ε p = eval (fun i => -a i) p := by
  change coeff 0 (trInv a p) = _
  rw [← constantCoeff_eq]
  have : (constantCoeff : MvPolynomial ι A →+* A).comp (trInv a).toRingHom =
      eval fun i => -a i := by
    refine ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp [trInv, algebraMap_eq]
    · simp [trInv]
  exact RingHom.congr_fun this p

/-- **Koszul acyclicity of `x + a` in positive degree.** -/
theorem translated_exists_kd_eq (l : ℕ) (f : Finset ι → MvPolynomial ι A)
    (hf : ∀ S, S.card ≠ l + 1 → f S = 0) (hd : (translatedWeyl a).kd f = 0) :
    ∃ g, (∀ S, S.card ≠ l + 2 → g S = 0) ∧ (translatedWeyl a).kd g = f :=
  (translatedWeyl a).exists_kd_eq l f hf hd

/-- **Koszul `H₀` of `x + a` is `A`**, the class of `p` going to `p(x = -a)`. -/
noncomputable def translatedKoszulH0Equiv :
    (MvPolynomial ι A ⧸ ⨆ i, LinearMap.range ((translatedWeyl a).u i)) ≃ₗ[A] A :=
  (translatedAug a).koszulH0Equiv

theorem translatedKoszulH0Equiv_mk (p : MvPolynomial ι A) :
    translatedKoszulH0Equiv a (Submodule.Quotient.mk p) = eval (fun i => -a i) p :=
  translatedAug_ε a p

end Translation

end VOA.LeadingKoszul
