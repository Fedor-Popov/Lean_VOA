/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.NondegFock
import VOA.Moonshine.InvFormTwisted

/-!
# An explicit invariant bilinear form on a lattice VOA  (Moonshine step M8c, `hnd` part 2)

For an even lattice `L`, on `V_L = FockN(rank L) ⊗ ℂ{L}`:

  `B(p ⊗ e^α, q ⊗ e^β) = δ_{α+β,0} · c(α) · F(p, q)`,   `c(α) = (−1)^{⟨α,α⟩/2} ε(α,α)`,

where `F = uForm` is the (negative) Fock form of `Moonshine.NondegFock` and `ε = latticeCocycle`.

**Sign finding.**  Invariance at `u = e^γ` (primary, weight `N = ⟨γ,γ⟩/2`, contragredient field
`(−1)^N z^{−2N} Y(e^γ, z⁻¹)`), with `Y(e^γ)` acting by `ε(γ,β) EE(γ) ⊗ e^{γ+β}` on `p ⊗ e^β`,
reduces (via `uForm_EEVec`) to `ε(γ,β) c(γ+β) = (−1)^N ε(γ,−γ−β) c(β)`, i.e. to
`c(γ+β) = (−1)^N ε(γ,γ) c(β)`.  The library cocycle does **not** satisfy `ε(γ,γ) = (−1)^N` (it is
built from a basis with only `ε(α,β)ε(β,α) = (−1)^{⟨α,β⟩}`), so the charge sign `c` is not
constant: `c(α) = (−1)^{⟨α,α⟩/2} ε(α,α)` is the unique solution with `c(0) = 1`, and it is a
character (`chSign_add`), even (`chSign_neg`) and a sign.

* `chForm` — the charge pairing `(e^α, e^β) = δ_{α+β,0} c(α)`; `latForm := uForm ⊗ chForm`.
* `latForm_symm`, `latForm_Yeαvec` — `B(e^γ₍ₙ₎ x, y) = (−1)^N B(x, e^γ₍₂N−n−2₎ y)`.
* `latForm_nondeg` — `x ≠ 0 ⟹ ∃ y, B(x,y) ≠ 0` (monomials ⊗ `e^α` pair with monomials ⊗ `e^{−α}`).
* `latForm_thetaLat` — `θ` is an isometry.
* `latForm_orth_grading` — distinct `L₀`-weight spaces are orthogonal.

## Status
All declarations proved; no `sorry`/axioms.  Unconditional (hypothesis `L.Even` where used).
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.Nondeg

open MvPolynomial VOA VOA.IntegralLattice VOA.LatGen HeisenbergN
open scoped TensorProduct

variable (L : IntegralLattice)

/-! ## The charge sign `c(α) = (−1)^{⟨α,α⟩/2} ε(α,α)` -/

/-- The charge sign `c(α) = (−1)^{⟨α,α⟩/2} ε(α,α)`. -/
noncomputable def chSign (α : L.carrier) : ℂ :=
  (-1 : ℂ) ^ (LatGen.halfNorm L α) * latticeCocycle L α α

theorem chSign_zero : chSign L 0 = 1 := by
  simp [chSign, LatGen.halfNorm, latticeCocycle_zero_left]

theorem chSign_neg (α : L.carrier) : chSign L (-α) = chSign L α := by
  rw [chSign, chSign, LatGen.halfNorm_neg, latticeCocycle_neg_neg]

theorem neg_one_zpow_mul_self (k : ℤ) : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
  rw [← zpow_add₀ (by norm_num)]
  exact Even.neg_one_zpow ⟨k, rfl⟩

theorem halfNorm_add (hEven : L.Even) (α β : L.carrier) :
    LatGen.halfNorm L (α + β) = LatGen.halfNorm L α + LatGen.halfNorm L β + L.form α β := by
  have h1 := two_halfNorm L hEven (α + β)
  have h2 := two_halfNorm L hEven α
  have h3 := two_halfNorm L hEven β
  have hs := IntegralLattice.form_symm L β α
  simp only [map_add, LinearMap.add_apply] at h1
  omega

/-- `c` is a character. -/
theorem chSign_add (hEven : L.Even) (α β : L.carrier) :
    chSign L (α + β) = chSign L α * chSign L β := by
  have hc := latticeCocycle_comm L hEven α β
  have hn : (-1 : ℂ) ≠ 0 := by norm_num
  rw [chSign, chSign, chSign, halfNorm_add L hEven, zpow_add₀ hn, zpow_add₀ hn,
    latticeCocycle_add_left, latticeCocycle_add_right, latticeCocycle_add_right]
  have hs := neg_one_zpow_mul_self (L.form α β)
  calc (-1 : ℂ) ^ LatGen.halfNorm L α * (-1) ^ LatGen.halfNorm L β * (-1) ^ L.form α β *
        (latticeCocycle L α α * latticeCocycle L α β *
          (latticeCocycle L β α * latticeCocycle L β β))
      = (-1 : ℂ) ^ LatGen.halfNorm L α * (-1) ^ LatGen.halfNorm L β *
          ((-1) ^ L.form α β * (latticeCocycle L α β * latticeCocycle L β α)) *
          (latticeCocycle L α α * latticeCocycle L β β) := by ring
    _ = _ := by rw [hc, hs]; ring

theorem chSign_ne_zero (α : L.carrier) : chSign L α ≠ 0 := by
  refine mul_ne_zero (zpow_ne_zero _ (by norm_num)) ?_
  intro h
  have := latticeCocycle_sq L α α
  rw [h, mul_zero] at this
  exact zero_ne_one this

/-! ## The charge pairing and the lattice form -/

/-- The charge pairing `(e^α, e^β) = δ_{α+β,0} c(α)` on `ℂ{L}`. -/
noncomputable def chForm : LinearMap.BilinForm ℂ (L.carrier →₀ ℂ) :=
  Finsupp.lsum ℂ fun α => LinearMap.smulRight LinearMap.id (chSign L α • Finsupp.lapply (-α))

theorem chForm_single (α : L.carrier) (a : ℂ) (g : L.carrier →₀ ℂ) :
    chForm L (Finsupp.single α a) g = a * (chSign L α * g (-α)) := by
  rw [chForm]
  erw [Finsupp.lsum_single]
  simp

open Classical in
theorem chForm_single_single (α β : L.carrier) (a b : ℂ) :
    chForm L (Finsupp.single α a) (Finsupp.single β b)
      = if α + β = 0 then a * b * chSign L α else 0 := by
  rw [chForm_single, Finsupp.single_apply]
  by_cases h : α + β = 0
  · rw [if_pos (by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h), if_pos h]; ring
  · rw [if_neg (by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h), if_neg h]; ring

theorem chForm_symm (f g : L.carrier →₀ ℂ) : chForm L f g = chForm L g f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => rw [map_add, LinearMap.add_apply, h₁, h₂, map_add]
  | single α a =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g₁ g₂ h₁ h₂ => rw [map_add, h₁, h₂, map_add, LinearMap.add_apply]
    | single β b =>
      rw [chForm_single_single, chForm_single_single]
      by_cases h : α + β = 0
      · have hβ : β = -α := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
        subst hβ
        rw [if_pos h, if_pos (by rw [add_comm]; exact h), chSign_neg]; ring
      · rw [if_neg h, if_neg (by rw [add_comm]; exact h)]

/-- **The explicit invariant form on `V_L`**: `B(p ⊗ f, q ⊗ g) = chForm(f,g) · F(p,q)`. -/
noncomputable def latForm : LinearMap.BilinForm ℂ (LatModuleGen L) :=
  (uForm (rank L)).tmul (chForm L)

theorem latForm_tmul (p q : FockN (rank L)) (f g : L.carrier →₀ ℂ) :
    latForm L (p ⊗ₜ f) (q ⊗ₜ g) = chForm L f g * uForm (rank L) p q := rfl

open Classical in
theorem latForm_state (p q : FockN (rank L)) (α β : L.carrier) :
    latForm L (latStateGen L p α) (latStateGen L q β)
      = (if α + β = 0 then chSign L α else 0) * uForm (rank L) p q := by
  rw [latStateGen, latStateGen, latForm_tmul, eGen, eGen, chForm_single_single]
  simp

theorem latForm_symm (x y : LatModuleGen L) : latForm L x y = latForm L y x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => rw [map_add, LinearMap.add_apply, h₁, h₂, map_add]
  | tmul p f =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ => rw [map_add, h₁, h₂, map_add, LinearMap.add_apply]
    | tmul q g => rw [latForm_tmul, latForm_tmul, chForm_symm, uForm_symm]

/-- Induction over the spanning states `p ⊗ e^α`. -/
theorem induction_latState {P : LatModuleGen L → Prop} (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y)) (hsmul : ∀ (c : ℂ) x, P x → P (c • x))
    (hst : ∀ p α, P (latStateGen L p α)) (x : LatModuleGen L) : P x := by
  have hx : x ∈ Submodule.span ℂ (Set.range (fun q : FockN (rank L) × L.carrier =>
      latStateGen L q.1 q.2)) := by
    rw [latStateGen_span]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨⟨p, α⟩, rfl⟩ := hy; exact hst p α
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul c x _ hx => exact hsmul c x hx

/-! ## Invariance at the charged vectors `e^γ` -/

theorem latForm_Yeαvec_state (hEven : L.Even) (γ : L.carrier) (n : ℤ) (p q : FockN (rank L))
    (β δ : L.carrier) :
    latForm L (mode (Yeαvec L γ) n (latStateGen L p β)) (latStateGen L q δ)
      = (-1 : ℂ) ^ (LatGen.halfNorm L γ) * latForm L (latStateGen L p β)
          (mode (Yeαvec L γ) (2 * LatGen.halfNorm L γ - n - 2) (latStateGen L q δ)) := by
  rw [mode_apply, mode_apply, Yeαvec_tmul, Yeαvec_tmul, map_smul, LinearMap.smul_apply,
    smul_eq_mul, map_smul, smul_eq_mul, latForm_state, latForm_state]
  by_cases h : γ + β + δ = 0
  · have hδ : δ = -(γ + β) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
    subst hδ
    have h2 := two_halfNorm L hEven γ
    rw [if_pos (show γ + β + -(γ + β) = 0 by abel), if_pos (show β + (γ + -(γ + β)) = 0 by abel),
      uForm_EEVec]
    have hidx : -(-n - 1 - L.form γ β)
        = -(2 * LatGen.halfNorm L γ - n - 2) - 1 - L.form γ (-(γ + β)) := by
      simp only [map_neg, map_add]
      omega
    rw [hidx, latticeCocycle_neg_right, latticeCocycle_add_right, chSign_add L hEven, chSign]
    ring
  · rw [if_neg (show ¬(γ + β + δ = 0) from h),
      if_neg (show ¬(β + (γ + δ) = 0) by intro h'; apply h; rw [← h']; abel)]
    ring

/-- **FHL invariance of `latForm` at `e^γ`**: `B(e^γ₍ₙ₎ x, y) = (−1)^N B(x, e^γ₍₂N−n−2₎ y)`,
`N = ⟨γ,γ⟩/2` (the contragredient of the primary field `Y(e^γ,z)`). -/
theorem latForm_Yeαvec (hEven : L.Even) (γ : L.carrier) (n : ℤ) (x y : LatModuleGen L) :
    latForm L (mode (Yeαvec L γ) n x) y
      = (-1 : ℂ) ^ (LatGen.halfNorm L γ) *
          latForm L x (mode (Yeαvec L γ) (2 * LatGen.halfNorm L γ - n - 2) y) := by
  induction x using induction_latState L with
  | h0 => simp
  | hadd x₁ x₂ h₁ h₂ => rw [map_add, map_add, LinearMap.add_apply, h₁, h₂, map_add,
      LinearMap.add_apply, mul_add]
  | hsmul c x hx => rw [map_smul, map_smul, LinearMap.smul_apply, hx, map_smul,
      LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]; ring
  | hst p β =>
    induction y using induction_latState L with
    | h0 => simp
    | hadd y₁ y₂ h₁ h₂ => rw [map_add, h₁, h₂, map_add, map_add, mul_add]
    | hsmul c y hy => rw [map_smul, smul_eq_mul, hy, map_smul, map_smul, smul_eq_mul]; ring
    | hst q δ => exact latForm_Yeαvec_state L hEven γ n p q β δ

/-! ## Nondegeneracy -/

theorem latForm_monomial_right (m : (ℕ × Fin (rank L)) →₀ ℕ) (g : L.carrier →₀ ℂ)
    (x : LatModuleGen L) :
    latForm L x (monomial m 1 ⊗ₜ g) = uWt m * chForm L (InvForm.tcoeff m x) g := by
  induction x using TensorProduct.induction_on with
  | zero => simp [InvForm.tcoeff]
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add, LinearMap.add_apply, h₁, h₂, InvForm.tcoeff_add, map_add, LinearMap.add_apply,
      mul_add]
  | tmul p f =>
    rw [latForm_tmul, InvForm.tcoeff_tmul, uForm_symm, uForm_monomial, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
    ring

/-- **`latForm` is nondegenerate on `V_L`.** -/
theorem latForm_nondeg (x : LatModuleGen L) (hx : x ≠ 0) : ∃ y, latForm L x y ≠ 0 := by
  obtain ⟨m, hm⟩ : ∃ m, InvForm.tcoeff m x ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (InvForm.eq_zero_of_tcoeff x h)
  obtain ⟨α, hα⟩ : ∃ α, InvForm.tcoeff m x α ≠ 0 := by
    by_contra h
    push Not at h
    exact hm (Finsupp.ext h)
  refine ⟨monomial m 1 ⊗ₜ Finsupp.single (-α) 1, ?_⟩
  rw [latForm_monomial_right, chForm_symm, chForm_single, neg_neg, one_mul]
  exact mul_ne_zero (uWt_ne_zero m) (mul_ne_zero (chSign_ne_zero L _) hα)

/-! ## `θ` is an isometry -/

theorem latForm_thetaLat (x y : LatModuleGen L) :
    latForm L (thetaLat L x) (thetaLat L y) = latForm L x y := by
  induction x using induction_latState L with
  | h0 => simp
  | hadd x₁ x₂ h₁ h₂ => rw [map_add, map_add, LinearMap.add_apply, h₁, h₂, map_add,
      LinearMap.add_apply]
  | hsmul c x hx => rw [map_smul, map_smul, LinearMap.smul_apply, hx, map_smul,
      LinearMap.smul_apply]
  | hst p β =>
    induction y using induction_latState L with
    | h0 => simp
    | hadd y₁ y₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add]
    | hsmul c y hy => rw [map_smul, map_smul, hy, map_smul]
    | hst q δ =>
      rw [thetaLat_latStateGen, thetaLat_latStateGen, latForm_state, latForm_state,
        uForm_sigmaN, chSign_neg, show -β + -δ = -(β + δ) by abel, neg_eq_zero]

/-! ## Orthogonality of the weight spaces -/

theorem latForm_orth_grading {m n : ℤ} (hmn : m ≠ n) {x y : LatModuleGen L}
    (hx : x ∈ gradingLatGen L m) (hy : y ∈ gradingLatGen L n) : latForm L x y = 0 := by
  rw [gradingLatGen] at hx hy
  refine Submodule.iSup_induction _ (motive := fun x => latForm L x y = 0) hx (fun α x' hx' => ?_)
    (by simp) (fun a b ha hb => by
      simp only at ha hb ⊢; rw [map_add, LinearMap.add_apply, ha, hb, add_zero])
  obtain ⟨p, hp, rfl⟩ := hx'
  refine Submodule.iSup_induction _ (motive := fun y => latForm L (mkEα L α p) y = 0) hy
    (fun δ y' hy' => ?_) (by simp) (fun a b ha hb => by
      simp only at ha hb ⊢; rw [map_add, ha, hb, add_zero])
  obtain ⟨q, hq, rfl⟩ := hy'
  rw [mkEα_apply, mkEα_apply, ← latStateGen, ← latStateGen, latForm_state]
  by_cases h : α + δ = 0
  · have hδ : δ = -α := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
    subst hδ
    rw [LatGen.halfNorm_neg] at hq
    rw [uForm_orth_gradingZN (by omega) hp hq, mul_zero]
  · rw [if_neg h, zero_mul]

end VOA.Moonshine.Nondeg
