/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.InvFormFock
import VOA.Moonshine.LatticeTwistedModule
import VOA.Moonshine.TwistedSectorDim

/-!
# The invariant form on `S[θ] ⊗ T` and the twisted generators  (Moonshine step M8c, form part 2)

`twForm r B_T := fockForm r ⊗ B_T` on `S[θ] ⊗ T` (`B(p ⊗ t, p' ⊗ t') = F(p,p') B_T(t,t')`), for any
bilinear form `B_T` on `T`.

* `twForm_symm` (from symmetric `B_T`), `twForm_map` (adjoints of product operators).
* `twForm_modeTT` — `B(h_a(k/2) x, y) = −B(x, h_a(−k/2) y)`.
* `twForm_YTg`, `twForm_YTL` — for the twisted exponential field
  `Y^T(e^α)₍k/2₎ = 2^{−⟨α,α⟩} DD(−k−2+⟨α,α⟩) ⊗ e_α`:
  `B(Y^T(e^α)₍k/2₎ x, y) = (−1)^{⟨α,α⟩/2} B(x, Y^T(e^α)₍(2⟨α,α⟩−k−4)/2₎ y)`, **given** the `T`-law
  `B_T(e_α t, t') = (−1)^{⟨α,α⟩/2} B_T(t, e_α t')`.  This is exactly the FHL formula for the
  primary vector `e^α` of weight `N = ⟨α,α⟩/2` (`(−1)^N z^{−2N} Y(e^α, z⁻¹)`, fractional mode
  `m ↦ 2N − m − 2`).  **Sign finding:** the convention of `TFormLeech.TForm_eT` (sign
  `(−1)^{⟨α,α⟩/2}`, no `e_γ` twist) is the compatible one; the Fock part contributes no sign.
* `YML_echg`, `YML_hgen` — the lattice twisted module on `e^α` and on `h_b(−1)𝟙`.
* Nondegeneracy: `tcoeff` (the `T`-coefficient of `X^m`), `twForm_monomial_right`
  (`B(x, X^m ⊗ t') = F(X^m,X^m) B_T(tcoeff_m x, t')`), `twForm_nondegenerate_twGrading`
  (nondegenerate on each graded piece `S[θ]_d ⊗ T` whenever `B_T` is), `twForm_orth_twGrading`
  (distinct graded pieces are orthogonal).

## Status
All declarations proved; no `sorry`/axioms.  Unconditional (the `T`-law is an explicit
hypothesis, discharged for the Leech `T` in `InvFormTP.lean` by `TForm_eT`).
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.InvForm
open MvPolynomial VOA.TwistedHeisenberg VOA.Moonshine.LatticeTwisted TwistedReduction
open Module (End)
open scoped TensorProduct

variable {r : ℕ} {Tm : Type*} [AddCommGroup Tm] [Module ℂ Tm]

/-- The form on `S[θ] ⊗ T`: `B(p ⊗ t, p' ⊗ t') = F(p, p') · B_T(t, t')`. -/
noncomputable def twForm (r : ℕ) (BT : LinearMap.BilinForm ℂ Tm) :
    LinearMap.BilinForm ℂ (FockT r ⊗[ℂ] Tm) :=
  (fockForm r).tmul BT

theorem twForm_tmul (BT : LinearMap.BilinForm ℂ Tm) (p p' : FockT r) (t t' : Tm) :
    twForm r BT (p ⊗ₜ t) (p' ⊗ₜ t') = BT t t' * fockForm r p p' := rfl

theorem twForm_symm {BT : LinearMap.BilinForm ℂ Tm} (hBT : ∀ t t', BT t t' = BT t' t)
    (x y : FockT r ⊗[ℂ] Tm) : twForm r BT x y = twForm r BT y x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => rw [map_add, LinearMap.add_apply, h₁, h₂, map_add]
  | tmul p t =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ => rw [map_add, h₁, h₂, map_add, LinearMap.add_apply]
    | tmul p' t' => rw [twForm_tmul, twForm_tmul, hBT, fockForm_symm]

/-- **Adjoints of product operators.** -/
theorem twForm_map (BT : LinearMap.BilinForm ℂ Tm) {X X' : End ℂ (FockT r)} {g g' : End ℂ Tm}
    {s₁ s₂ : ℂ} (hX : ∀ p q, fockForm r (X p) q = s₁ * fockForm r p (X' q))
    (hg : ∀ t t', BT (g t) t' = s₂ * BT t (g' t')) (x y : FockT r ⊗[ℂ] Tm) :
    twForm r BT (TensorProduct.map X g x) y
      = (s₁ * s₂) * twForm r BT x (TensorProduct.map X' g' y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => rw [map_add, map_add, LinearMap.add_apply, h₁, h₂, map_add,
      LinearMap.add_apply, mul_add]
  | tmul p t =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ => rw [map_add, h₁, h₂, map_add, map_add, mul_add]
    | tmul p' t' =>
      rw [TensorProduct.map_tmul, TensorProduct.map_tmul, twForm_tmul, twForm_tmul, hX, hg]
      ring

/-- **Oscillators**: `B(h_a(k/2) x, y) = −B(x, h_a(−k/2) y)` on `S[θ] ⊗ T`. -/
theorem twForm_modeTT (BT : LinearMap.BilinForm ℂ Tm) (a : Fin r) (k : ℤ)
    (x y : FockT r ⊗[ℂ] Tm) :
    twForm r BT (modeTT (Tm := Tm) a k x) y = -twForm r BT x (modeTT (Tm := Tm) a (-k) y) := by
  have h := twForm_map BT (X := modeT r a k) (X' := modeT r a (-k)) (g := LinearMap.id)
    (g' := LinearMap.id) (s₁ := -1) (s₂ := 1)
    (fun p q => by rw [fockForm_modeT]; ring) (fun t t' => by simp) x y
  simp only [mul_one, neg_one_mul] at h
  exact h

/-- **The twisted exponential fields**: with `B_T(g t, t') = s · B_T(t, g' t')`,
`B(Y_g(k) x, y) = s · B(x, Y_{g'}(2c₀ − k − 4) y)`. -/
theorem twForm_YTg (BT : LinearMap.BilinForm ℂ Tm) (v : Fin r → ℂ) (c0 : ℤ) (κ : ℂ)
    {g g' : End ℂ Tm} {s : ℂ} (hg : ∀ t t', BT (g t) t' = s * BT t (g' t')) (k : ℤ)
    (x y : FockT r ⊗[ℂ] Tm) :
    twForm r BT (YTg v c0 κ g k x) y = s * twForm r BT x (YTg v c0 κ g' (2 * c0 - k - 4) y) := by
  rw [YTg, YTg, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, map_smul,
    LinearMap.smul_apply,
    twForm_map BT (X' := DD v (-(-k - 2 + c0))) (s₁ := 1) (fun p q => by rw [fockForm_DD]; ring) hg,
    show -(-k - 2 + c0) = -(2 * c0 - k - 4) - 2 + c0 by ring]
  simp only [smul_eq_mul]; ring


/-! ## Nondegeneracy on the graded pieces -/

theorem cVar_ne_zero (v : ℕ × Fin r) : cVar v ≠ 0 := by
  rw [cVar, neg_ne_zero]
  intro h
  have h' := congrArg Complex.re h
  norm_num at h'
  have : (0 : ℝ) ≤ v.1 := Nat.cast_nonneg _
  linarith

theorem fockWt_ne_zero (d : (ℕ × Fin r) →₀ ℕ) : fockWt d ≠ 0 := by
  rw [fockWt, Finsupp.prod]
  refine Finset.prod_ne_zero_iff.mpr fun v _ => mul_ne_zero (pow_ne_zero _ (cVar_ne_zero v)) ?_
  exact_mod_cast Nat.factorial_ne_zero _

/-- The `T`-coefficient of the monomial `X^m` in `x ∈ S[θ] ⊗ T`. -/
noncomputable def tcoeff (m : (ℕ × Fin r) →₀ ℕ) (x : FockT r ⊗[ℂ] Tm) : Tm :=
  TensorProduct.equivFinsuppOfBasisLeft (basisMonomials (ℕ × Fin r) ℂ) x m

theorem tcoeff_tmul (m : (ℕ × Fin r) →₀ ℕ) (p : FockT r) (t : Tm) :
    tcoeff m (p ⊗ₜ t) = coeff m p • t := by
  rw [tcoeff, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
  rfl

theorem tcoeff_add (m : (ℕ × Fin r) →₀ ℕ) (x y : FockT r ⊗[ℂ] Tm) :
    tcoeff m (x + y) = tcoeff m x + tcoeff m y := by
  simp [tcoeff]

theorem twForm_monomial_right (BT : LinearMap.BilinForm ℂ Tm) (m : (ℕ × Fin r) →₀ ℕ) (t' : Tm)
    (x : FockT r ⊗[ℂ] Tm) :
    twForm r BT x (monomial m 1 ⊗ₜ t') = fockWt m * BT (tcoeff m x) t' := by
  induction x using TensorProduct.induction_on with
  | zero => simp [tcoeff]
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add, LinearMap.add_apply, h₁, h₂, tcoeff_add, map_add, LinearMap.add_apply, mul_add]
  | tmul p t =>
    rw [twForm_tmul, tcoeff_tmul, fockForm_symm, fockForm_monomial, map_smul, LinearMap.smul_apply,
      smul_eq_mul]
    ring

theorem eq_zero_of_tcoeff (x : FockT r ⊗[ℂ] Tm) (h : ∀ m, tcoeff m x = 0) : x = 0 := by
  apply (TensorProduct.equivFinsuppOfBasisLeft (basisMonomials (ℕ × Fin r) ℂ)).injective
  rw [map_zero]
  ext m
  exact h m

theorem tcoeff_eq_zero_of_mem_twGrading {d : ℕ} {x : FockT r ⊗[ℂ] Tm}
    (hx : x ∈ TwistedSector.twGrading r Tm d) {m : (ℕ × Fin r) →₀ ℕ}
    (hm : Finsupp.weight wT m ≠ d) : tcoeff m x = 0 := by
  obtain ⟨z, rfl⟩ := hx
  induction z using TensorProduct.induction_on with
  | zero => simp [tcoeff]
  | add z₁ z₂ h₁ h₂ => rw [map_add, tcoeff_add, h₁, h₂, add_zero]
  | tmul p t =>
    rw [LinearMap.rTensor_tmul, Submodule.subtype_apply, tcoeff_tmul]
    have hp : coeff m (p : FockT r) = 0 := by
      by_contra hc
      exact hm (p.2 hc)
    rw [hp, zero_smul]

/-- **Nondegeneracy on each graded piece** `S[θ]_d ⊗ T`, for any nondegenerate `B_T`. -/
theorem twForm_nondegenerate_twGrading {BT : LinearMap.BilinForm ℂ Tm} (hBT : BT.Nondegenerate)
    {d : ℕ} {x : FockT r ⊗[ℂ] Tm} (hx : x ∈ TwistedSector.twGrading r Tm d) (hx0 : x ≠ 0) :
    ∃ m : (ℕ × Fin r) →₀ ℕ, ∃ t' : Tm, monomial m 1 ⊗ₜ t' ∈ TwistedSector.twGrading r Tm d ∧
      twForm r BT x (monomial m 1 ⊗ₜ t') ≠ 0 := by
  obtain ⟨m, hm⟩ : ∃ m, tcoeff m x ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (eq_zero_of_tcoeff x h)
  obtain ⟨t', ht'⟩ : ∃ t', BT (tcoeff m x) t' ≠ 0 := by
    by_contra h
    push Not at h
    exact hm (hBT.1 _ h)
  have hw : Finsupp.weight wT m = d := by
    by_contra h
    exact hm (tcoeff_eq_zero_of_mem_twGrading hx h)
  refine ⟨m, t', TwistedSector.tmul_mem_twGrading r Tm (isWeightedHomogeneous_monomial _ _ _ hw) _, ?_⟩
  rw [twForm_monomial_right]
  exact mul_ne_zero (fockWt_ne_zero m) ht'

/-- **Distinct graded pieces are orthogonal.** -/
theorem twForm_orth_twGrading (BT : LinearMap.BilinForm ℂ Tm) {d d' : ℕ} (hdd : d ≠ d')
    {x y : FockT r ⊗[ℂ] Tm} (hx : x ∈ TwistedSector.twGrading r Tm d)
    (hy : y ∈ TwistedSector.twGrading r Tm d') : twForm r BT x y = 0 := by
  obtain ⟨z, rfl⟩ := hy
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, add_zero]
  | tmul p t =>
    rw [LinearMap.rTensor_tmul, Submodule.subtype_apply]
    obtain ⟨p, hp⟩ := p
    simp only
    rw [p.as_sum, TensorProduct.sum_tmul, map_sum]
    refine Finset.sum_eq_zero fun m hm => ?_
    have hw : Finsupp.weight wT m = d' := hp (mem_support_iff.mp hm)
    rw [show monomial m (coeff m p) = coeff m p • monomial m (1 : ℂ) by
        rw [smul_monomial, smul_eq_mul, mul_one], ← TensorProduct.smul_tmul', map_smul,
      twForm_monomial_right, tcoeff_eq_zero_of_mem_twGrading hx (by rw [hw]; exact Ne.symm hdd),
      map_zero, LinearMap.zero_apply, mul_zero, smul_zero]

/-! ## The lattice twisted module -/

section Lattice

open IntegralLattice LatGen Extraspecial HeisenbergN

variable (L : IntegralLattice.{0}) (hEven : L.Even) (hU : IsUnit (gramMat L).det)
  (hPos : L.PosDef)

/-- **`Y^T(e^α)` is self-adjoint up to the contragredient sign**, given the `T`-law
`B_T(e_α t, t') = (−1)^{⟨α,α⟩/2} B_T(t, e_α t')`. -/
theorem twForm_YTL (BT : LinearMap.BilinForm ℂ (Rep (cocMat L) (isUnit_det_cocMat L hEven hU)))
    (hT : ∀ (α : L.carrier) t t', BT (eT L hEven hU α t) t'
      = (-1 : ℂ) ^ (L.form α α / 2) * BT t (eT L hEven hU α t'))
    (α : L.carrier) (k : ℤ) (x y : MT L hEven hU) :
    twForm (rank L) BT (YTL L hEven hU α k x) y
      = (-1 : ℂ) ^ (L.form α α / 2) *
          twForm (rank L) BT x (YTL L hEven hU α (2 * L.form α α - k - 4) y) :=
  twForm_YTg BT _ _ _ (hT α) k x y

include hPos in
theorem YML_echg (α : L.carrier) (k : ℤ) : YML L hEven hU (echg L α) k = YTL L hEven hU α k := by
  rw [YML_apply, FL_echg L hEven hU hPos]
  change mode (resc (YTL L hEven hU α) 2 k) 0 = _
  rw [mode_resc, mul_zero, zero_add]

include hPos in
theorem YML_hgen (b : Fin (rank L)) (k : ℤ) :
    YML L hEven hU (hgen L b) k = modeTT (Tm := Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) b k := by
  rw [YML_apply, hgen, FL_charge_zero L hEven hU hPos, mode_rTFld, FT_val, mode_resc, mul_zero,
    zero_add, YT_X]
  rfl

end Lattice

end VOA.Moonshine.InvForm
