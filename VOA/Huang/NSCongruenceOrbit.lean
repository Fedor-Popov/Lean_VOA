/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.NgSchauenburgMixedArithmetic
import VOA.Huang.NgSchauenburgTOrbits
import VOA.Huang.NSCongruenceBridge

/-!
# Projective congruence from orbit-only mixed equivariance

The consumer `projectiveCongruence_of_mixed_primitive_rescaling` asks for
equivariance of the actual mixed indicators at **every** integer row, and for primitive
rescaling at every first index including `0`.  The arithmetic only ever evaluates the indicator
family on the SL(2,ℤ)-orbit of the row `(1,0)` (the primitive rows), and the rescaling is only
needed at rows `(s,-r)` with `s ≠ 0`: the case of a vanishing `(0,1)` entry is removed by
right-multiplying with `T^N`, which acts trivially in the mixed representation.

This file proves:

* `one_zero_invariant_of_orbit` — the abstract arithmetic with orbit-only equivariance and
  `s ≠ 0` rescaling;
* `projectiveKernel_of_orbit_rescaling` — the categorical consumer;
* `orbitEquivariance_of_moves` — orbit equivariance from the two generator moves (`T` and `S`)
  along the orbit only;
* `mixedTMove_of_twistIdentity` — the `T` move on all rows from the mixed twist identity;
* `mixedRescaling_of_twist_cyclotomic` — the `s ≠ 0` rescaling from the mixed twist identity and
  cyclotomic membership of the `(s,-1)` values;
* `nsProjectiveKernelAll_of_mixedResiduals` — the kernel half of NS 6.8 for every modular
  category from the three residual Props `MixedTwistIdentity`, `MixedSMoveOrbit`,
  `MixedRowCyclotomic`.

The three residual Props are not proved in this file.  `MixedTwistIdentity` is proved in
`NSCongruenceTwist` (`mixedTwistIdentity_holds`).  `MixedSMoveOrbit` and `MixedRowCyclotomic` remain
open; both are true consequences of Ng–Schauenburg (0806.2493, Thm 5.4 transported to
`C ⊠ C^rev`, and Prop 5.7 / Lemma 6.4).  See `NSCongruenceMain`.
-/

noncomputable section
set_option linter.unusedSectionVars false

namespace VOA.Huang.NSCongruence

open VOA.Huang.NgSchauenburg
open scoped MatrixGroups

/-! ## Abstract orbit arithmetic -/

section Abstract

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem le_one_apply (w : W) : (1 : W ≃ₗ[ℂ] W) w = w := rfl

theorem le_inv_apply_apply (e : W ≃ₗ[ℂ] W) (w : W) : e⁻¹ (e w) = w := by
  rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]

theorem modularInvolution_one : modularInvolution (1 : SL(2, ℤ)) = 1 :=
  map_one modularOuterAutomorphism

theorem rowAction_one_zero (γ : SL(2, ℤ)) : rowAction 1 0 γ = (γ 0 0, γ 0 1) := by
  simp [rowAction]

theorem modularInvolution_T_zpow (k : ℤ) :
    modularInvolution (ModularGroup.T ^ k) = (ModularGroup.T ^ k)⁻¹ := by
  change modularOuterAutomorphism _ = _
  rw [map_zpow]
  change (modularInvolution ModularGroup.T) ^ _ = _
  rw [modularInvolution_T, inv_zpow]

/-- Orbit-only form of the primitive-row argument.  Equivariance is only assumed along the
orbit of `(1,0)`, and rescaling only at a nonzero first index. -/
theorem one_zero_invariant_of_orbit
    (σ : SL(2, ℤ) →* (W ≃ₗ[ℂ] W)) (I : ℤ → ℤ → W → ℂ) (N : ℕ) (hN : 0 < N)
    (he : ∀ γ z, I (rowAction 1 0 γ).1 (rowAction 1 0 γ).2 z =
      I 1 0 (σ (modularInvolution γ) z))
    (hT : (σ ModularGroup.T) ^ N = 1)
    (hscale : ∀ a b : ℤ, b ≠ 0 → IsCoprime a b → (a : ZMod N) = 1 →
      ∀ z, I b (-a) z = I b (-1) z)
    (γ : SL(2, ℤ)) (hγ : InPrincipalCongruence N γ) (z : W) :
    I 1 0 (σ γ z) = I 1 0 z := by
  have hTN (k : ℤ) (hk : (N : ℤ) ∣ k) : σ (ModularGroup.T ^ k) = 1 := by
    obtain ⟨q, rfl⟩ := hk
    rw [map_zpow, zpow_mul, zpow_natCast, hT, one_zpow]
  -- The core step for an element of `Γ(N)` with nonzero `(0,1)` entry.
  have hcore (δ : SL(2, ℤ)) (hδ : InPrincipalCongruence N δ) (hb : δ 0 1 ≠ 0) (w : W) :
      I 1 0 (σ (modularInvolution δ) w) = I 1 0 w := by
    obtain ⟨hab, ha, hb0⟩ := principal_first_row N δ hδ
    have hSS : σ ModularGroup.S⁻¹ (σ ModularGroup.S w) = w := by
      rw [map_inv, le_inv_apply_apply]
    -- `S` step at the row of `δ`.
    have h2 := he (δ * ModularGroup.S) (σ ModularGroup.S w)
    rw [rowAction_mul, rowAction_one_zero, rowAction_S, modularInvolution_mul,
      modularInvolution_S, map_mul, LinearEquiv.mul_apply, hSS] at h2
    -- `S` step at the row `(1, b)` of `T^b`.
    obtain ⟨q, hq⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb0
    have h3 := he (ModularGroup.T ^ (δ 0 1) * ModularGroup.S) (σ ModularGroup.S w)
    rw [rowAction_mul, rowAction_one_zero, rowAction_S, modularInvolution_mul,
      modularInvolution_S, modularInvolution_T_zpow, map_mul, LinearEquiv.mul_apply, hSS,
      map_inv, hTN _ ⟨q, hq⟩, inv_one, le_one_apply] at h3
    simp only [ModularGroup.coe_T_zpow] at h3
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at h3
    dsimp only at h2 h3
    rw [← h2, hscale _ _ hb hab ha, h3]
  -- Remove a vanishing `(0,1)` entry with `T^N`.
  have hδ := modularInvolution_inPrincipalCongruence hγ
  have hinv : modularInvolution (modularInvolution γ) = γ := modularInvolution_involutive γ
  by_cases hb : (modularInvolution γ) 0 1 = 0
  · set δ := modularInvolution γ * ModularGroup.T ^ (N : ℤ) with hδdef
    have hδΓ : InPrincipalCongruence N δ := by
      have := (NSFinish.inPrincipalCongruence_iff N (modularInvolution γ)).mp hδ
      have hT' := NSFinish.T_pow_mem_Gamma N
      exact (NSFinish.inPrincipalCongruence_iff N δ).mpr (Subgroup.mul_mem _ this hT')
    have ha0 : (modularInvolution γ) 0 0 ≠ 0 := by
      intro h0
      have hdet := NSFinish.det_eq (modularInvolution γ)
      rw [h0, hb] at hdet
      simp at hdet
    have hδb : δ 0 1 ≠ 0 := by
      rw [hδdef, NSFinish.mul_apply', NSFinish.T_zpow_apply]
      simp [hb, ha0, hN.ne']
    have hc := hcore δ hδΓ hδb z
    rw [hδdef, modularInvolution_mul, hinv, modularInvolution_T_zpow, map_mul,
      LinearEquiv.mul_apply, map_inv, hTN _ (dvd_refl _), inv_one,
      le_one_apply] at hc
    exact hc
  · have hc := hcore (modularInvolution γ) hδ hb z
    rwa [hinv] at hc

end Abstract

/-! ## The mixed residuals -/

universe v u
open CategoryTheory MonoidalCategory Limits BraidedCategory
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

/-- The actual mixed central objects `X_i ⊠ X_j`. -/
abbrev mixedFamily (F : SphericalFusion C) : F.Label × F.Label → Center C :=
  fun p => mixedCenter (F.simple p.1) (F.simple p.2)

/-- The linear functional of mixed indicators at the row `(m,l)` with probe `X_a`. -/
abbrev mixedRow (F : SphericalFusion C) (a : F.Label) (m l : ℤ) :
    (F.Label × F.Label → ℂ) →ₗ[ℂ] ℂ :=
  equivariantIndicator F (mixedFamily F) (F.simple a) m l

open Classical in
/-- **Residual-shaped contract (orbit equivariance).**  Equivariance of the actual mixed
indicators along the SL(2,ℤ)-orbit of the row `(1,0)`, for every genuine modular lift. -/
def MixedOrbitEquivariance (F : SphericalFusion C) (M : Modular F) : Prop :=
  ∀ ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)), IsModularRepresentation F M ρ →
    ∀ (a : F.Label) (γ : SL(2, ℤ)) (z : F.Label × F.Label → ℂ),
      mixedRow F a (rowAction 1 0 γ).1 (rowAction 1 0 γ).2 z =
        mixedRow F a 1 0 (mixedRepresentation ρ (modularInvolution γ) z)

/-- **Residual-shaped contract (rescaling).**  Primitive Galois rescaling at nonzero first
index. -/
def MixedPrimitiveRescaling (F : SphericalFusion C) (M : Modular F) : Prop :=
  ∀ (a i j : F.Label) (r s : ℤ), s ≠ 0 → IsCoprime r s →
    Int.ModEq M.toRibbon.twistOrder r 1 →
      generalizedIndicatorAll F (mixedCenter (F.simple i) (F.simple j)) (F.simple a) s (-r) =
        generalizedIndicatorAll F (mixedCenter (F.simple i) (F.simple j)) (F.simple a) s (-1)

open Classical in
/-- **Projective congruence at the raw twist order from orbit equivariance and nonzero-index
rescaling.** -/
theorem projectiveKernel_of_orbit_rescaling (F : SphericalFusion C) (M : Modular F)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hr : IsModularRepresentation F M ρ)
    (he : MixedOrbitEquivariance F M) (hs : MixedPrimitiveRescaling F M) :
    ProjectiveKernelContainsGamma ρ M.toRibbon.twistOrder := by
  apply projectiveCongruence_of_mixed_invariance F M ρ hr
  intro γ hγ a z
  refine one_zero_invariant_of_orbit (mixedRepresentation ρ)
    (fun m l w => mixedRow F a m l w) M.toRibbon.twistOrder M.toRibbon.finite_twist.1
    (he ρ hr a) (mixedRepresentation_T_period F M ρ hr) ?_ γ hγ z
  intro r s hs0 hrs hrN w
  have hmod : Int.ModEq M.toRibbon.twistOrder r 1 :=
    (ZMod.intCast_eq_intCast_iff r 1 _).mp (by simpa using hrN)
  simp only [mixedRow, equivariantIndicator, LinearMap.coe_mk, AddHom.coe_mk,
    hs a _ _ r s hs0 hrs hmod]

/-! ## Generator moves -/

open Classical in
/-- **T move.**  The `T` generator step of the mixed indicators, on every row.  Proved for every
modular category in `NSCongruenceMain.mixedTMove_holds`. -/
def MixedTMove (F : SphericalFusion C) (M : Modular F) : Prop :=
  ∀ ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)), IsModularRepresentation F M ρ →
    ∀ (a : F.Label) (m l : ℤ) (z : F.Label × F.Label → ℂ),
      mixedRow F a m (l + m) z = mixedRow F a m l (mixedRepresentation ρ ModularGroup.T⁻¹ z)

open Classical in
/-- **Residual (S move along the orbit).**  The `S` generator step of the mixed indicators, at
every primitive row, i.e. every row `(m,l) = (1,0)·γ`.  This is the core categorical content of
Ng–Schauenburg Theorem 5.4, specialised to the mixed objects and to primitive rows. -/
def MixedSMoveOrbit (F : SphericalFusion C) (M : Modular F) : Prop :=
  ∀ ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)), IsModularRepresentation F M ρ →
    ∀ (a : F.Label) (γ : SL(2, ℤ)) (z : F.Label × F.Label → ℂ),
      mixedRow F a (rowAction 1 0 γ).2 (-(rowAction 1 0 γ).1) z =
        mixedRow F a (rowAction 1 0 γ).1 (rowAction 1 0 γ).2
          (mixedRepresentation ρ ModularGroup.S⁻¹ z)

open Classical in
/-- **Orbit equivariance from the two generator moves.**  Closure induction over the
generators `S, T` of SL(2,ℤ), for the stronger statement uniform in the base row. -/
theorem orbitEquivariance_of_moves (F : SphericalFusion C) (M : Modular F)
    (hT : MixedTMove F M) (hS : MixedSMoveOrbit F M) : MixedOrbitEquivariance F M := by
  intro ρ hr a γ z
  let σ := mixedRepresentation ρ
  let I : ℤ × ℤ → (F.Label × F.Label → ℂ) → ℂ := fun r w => mixedRow F a r.1 r.2 w
  -- `Q δ`: equivariance of `δ` at every row of the orbit.
  let Q : SL(2, ℤ) → Prop := fun δ => ∀ (g : SL(2, ℤ)) (w : F.Label × F.Label → ℂ),
    I (rowAction 1 0 (g * δ)) w = I (rowAction 1 0 g) (σ (modularInvolution δ) w)
  have hQ : ∀ δ, Q δ := by
    intro δ
    have hg : δ ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
      simp [SpecialLinearGroup.SL2Z_generators]
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases (show x = ModularGroup.S ∨ x = ModularGroup.T by simpa using hx) with rfl | rfl
      · intro g w
        have h := hS ρ hr a g w
        rw [rowAction_mul, rowAction_S, modularInvolution_S]
        exact h
      · intro g w
        have h := hT ρ hr a (rowAction 1 0 g).1 (rowAction 1 0 g).2 w
        rw [rowAction_mul, rowAction_T, modularInvolution_T]
        exact h
    | one =>
      intro g w
      rw [mul_one, modularInvolution_one, map_one, le_one_apply]
    | mul x y _ _ hx hy =>
      intro g w
      rw [← mul_assoc, hy (g * x), hx g, modularInvolution_mul, map_mul,
        LinearEquiv.mul_apply]
    | inv x _ hx =>
      intro g w
      have h := hx (g * x⁻¹) (σ (modularInvolution x⁻¹) w)
      rw [inv_mul_cancel_right, ← LinearEquiv.mul_apply, ← map_mul,
        ← modularInvolution_mul, mul_inv_cancel] at h
      rw [modularInvolution_one, map_one, le_one_apply] at h
      exact h.symm
  have h := hQ γ 1 z
  simpa [rowAction] using h

/-! ## The `T` move from the mixed twist identity -/

/-- **Mixed twist identity.**  On each mixed object `X_i ⊠ X_j` the pivotal structure is
`θ_i / θ_j` times the central Drinfeld morphism.  Proved for every modular category in
`NSCongruenceTwist.mixedTwistIdentity_holds`. -/
def MixedTwistIdentity (F : SphericalFusion C) (M : Modular F) : Prop :=
  ∀ i j : F.Label,
    (F.j (mixedCenter (F.simple i) (F.simple j)).1).hom =
      (M.twistScalar i / M.twistScalar j) •
        centralDrinfeldMorphism (mixedCenter (F.simple i) (F.simple j))

open Classical in
theorem mixedRepresentation_T_inv (F : SphericalFusion C) (M : Modular F)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hr : IsModularRepresentation F M ρ) (z : F.Label × F.Label → ℂ) (p : F.Label × F.Label) :
    mixedRepresentation ρ ModularGroup.T⁻¹ z p =
      (M.twistScalar p.1 / M.twistScalar p.2)⁻¹ * z p := by
  have h := mixedRepresentation_T F M ρ hr (mixedRepresentation ρ ModularGroup.T⁻¹ z) p
  rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    le_one_apply] at h
  have hne : M.twistScalar p.1 / M.twistScalar p.2 ≠ 0 :=
    div_ne_zero (M.toRibbon.twistScalar_ne_zero _) (M.toRibbon.twistScalar_ne_zero _)
  rw [h, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

open Classical in
/-- **The T move on every row from the mixed twist identity.** -/
theorem mixedTMove_of_twistIdentity (F : SphericalFusion C) (M : Modular F)
    (hj : MixedTwistIdentity F M) : MixedTMove F M := by
  intro ρ hr a m l z
  simp only [mixedRow, equivariantIndicator, LinearMap.coe_mk, AddHom.coe_mk,
    mixedRepresentation_T_inv F M ρ hr]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hne : M.twistScalar p.1 / M.twistScalar p.2 ≠ 0 :=
    div_ne_zero (M.toRibbon.twistScalar_ne_zero _) (M.toRibbon.twistScalar_ne_zero _)
  rw [generalizedIndicatorAll_add_degree F _ _ hne (hj p.1 p.2)]
  ring

/-! ## Rescaling from the twist identity and cyclotomic membership -/

/-- **Residual (cyclotomic membership).**  For nonzero first index `s`, the mixed indicator at
the row `(s,-1)` lies in `ℚ(ζ_N)`, `N` the raw twist order (NS Prop 5.7 / Lemma 6.4). -/
def MixedRowCyclotomic (F : SphericalFusion C) (M : Modular F) : Prop :=
  ∀ (a i j : F.Label) (s : ℤ), s ≠ 0 →
    generalizedIndicatorAll F (mixedCenter (F.simple i) (F.simple j)) (F.simple a) s (-1) ∈
      Algebra.adjoin ℚ
        ({Complex.exp (2 * Real.pi * Complex.I / M.toRibbon.twistOrder)} : Set ℂ)

theorem twistScalar_pow_twistOrder {F : SphericalFusion C} (M : Modular F) (i : F.Label) :
    M.twistScalar i ^ M.toRibbon.twistOrder = 1 :=
  congrFun (pow_orderOf_eq_one (fun j : F.Label => M.toRibbon.twistScalar j)) i

theorem exp_pow_succ (n N : ℕ) (hN : 0 < N) :
    Complex.exp (2 * Real.pi * Complex.I / ((n + 1 : ℕ) * N : ℕ)) ^ (n + 1) =
      Complex.exp (2 * Real.pi * Complex.I / N) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hn' : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  push_cast at hn'
  field_simp

theorem gcd_eq_one_of_coprime_modEq {r s : ℤ} {N : ℕ} (hrs : IsCoprime r s)
    (hr : Int.ModEq N r 1) (n : ℕ) (hs : s = (n + 1 : ℕ) ∨ s = -((n + 1 : ℕ) : ℤ)) :
    Int.gcd r ((n + 1) * N : ℕ) = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one]
  push_cast
  apply IsCoprime.mul_right
  · rcases hs with hs | hs
    · simpa [hs] using hrs
    · rw [hs] at hrs
      exact_mod_cast hrs.neg_right
  · obtain ⟨k, hk⟩ := (Int.ModEq.dvd hr.symm)
    exact ⟨1, -k, by linear_combination hk⟩

/-- **Nonzero-index rescaling from the twist identity and cyclotomic membership.**  Uses the
proved integer Galois trace argument `generalizedIndicatorInt_zmul_eq_of_modEq`. -/
theorem mixedRescaling_of_twist_cyclotomic (F : SphericalFusion C) (M : Modular F)
    (hj : MixedTwistIdentity F M) (hc : MixedRowCyclotomic F M) :
    MixedPrimitiveRescaling F M := by
  intro a i j r s hs0 hrs hr
  set N := M.toRibbon.twistOrder with hNdef
  have hN : 0 < N := M.toRibbon.finite_twist.1
  set t := M.twistScalar i / M.twistScalar j with htdef
  have ht : t ≠ 0 :=
    div_ne_zero (M.toRibbon.twistScalar_ne_zero _) (M.toRibbon.twistScalar_ne_zero _)
  have htN : t ^ N = 1 := by
    rw [htdef, div_pow, twistScalar_pow_twistOrder, twistScalar_pow_twistOrder, div_one]
  have hmem := hc a i j s hs0
  rcases lt_or_gt_of_ne hs0 with hneg | hpos
  · -- negative first index: dual probe, second index negated
    set n := s.natAbs - 1 with hn
    have hsn : s = -((n + 1 : ℕ) : ℤ) := by omega
    have hpos' : ¬ (0 < s) := by omega
    have hzero : ¬ (s = 0) := hs0
    simp only [generalizedIndicatorAll, if_neg hpos', if_neg hzero, neg_neg] at hmem ⊢
    rw [← hn] at hmem ⊢
    have hζ := Complex.isPrimitiveRoot_exp ((n + 1) * N) (by positivity)
    have h := generalizedIndicatorInt_zmul_eq_of_modEq F
      (mixedCenter (F.simple i) (F.simple j)) (F.simple a)ᘁ n hN ht (hj i j) htN hζ r 1
      (gcd_eq_one_of_coprime_modEq hrs hr n (Or.inr hsn)) hr
      (by rw [exp_pow_succ n N hN]; exact hmem)
    simpa using h
  · set n := s.toNat - 1 with hn
    have hsn : s = ((n + 1 : ℕ) : ℤ) := by omega
    simp only [generalizedIndicatorAll, if_pos hpos] at hmem ⊢
    rw [← hn] at hmem ⊢
    have hζ := Complex.isPrimitiveRoot_exp ((n + 1) * N) (by positivity)
    have h := generalizedIndicatorInt_zmul_eq_of_modEq F
      (mixedCenter (F.simple i) (F.simple j)) (F.simple a) n hN ht (hj i j) htN hζ r (-1)
      (gcd_eq_one_of_coprime_modEq hrs hr n (Or.inl hsn)) hr
      (by rw [exp_pow_succ n N hN]; exact hmem)
    simpa using h

/-! ## Assembly -/

open Classical in
/-- **Projective congruence of every modular lift at the raw twist order, from the three
mixed residuals.** -/
theorem projectiveKernel_of_mixedResiduals (F : SphericalFusion C) (M : Modular F)
    (hj : MixedTwistIdentity F M) (hS : MixedSMoveOrbit F M) (hc : MixedRowCyclotomic F M)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hr : IsModularRepresentation F M ρ) :
    ProjectiveKernelContainsGamma ρ M.toRibbon.twistOrder :=
  projectiveKernel_of_orbit_rescaling F M ρ hr
    (orbitEquivariance_of_moves F M (mixedTMove_of_twistIdentity F M hj) hS)
    (mixedRescaling_of_twist_cyclotomic F M hj hc)

end VOA.Huang.NSCongruence

namespace VOA.Huang.DLNBridge

open CategoryTheory MonoidalCategory Limits
open VOA.Huang.NgSchauenburg VOA.Huang.NSCongruence

universe u v w

/-- The three mixed residuals, for every modular category. -/
def NSMixedResidualsAll : Prop :=
  ∀ (C : Type w) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]
    (F : SphericalFusion C) (M : Modular F),
    MixedTwistIdentity F M ∧ MixedSMoveOrbit F M ∧ MixedRowCyclotomic F M

/-- **The kernel half of NS 6.8 from the three mixed residuals.** -/
theorem nsProjectiveKernelAll_of_mixedResiduals (h : NSMixedResidualsAll.{v, w}) :
    NSProjectiveKernelAll.{v, w} := by
  intro C _ _ _ _ _ _ _ _ _ _ F M
  obtain ⟨hj, hS, hc⟩ := h C F M
  exact ⟨M.toRibbon.twistOrder, M.toRibbon.finite_twist.1,
    fun ρ hρ => projectiveKernel_of_mixedResiduals F M hj hS hc ρ hρ⟩

/-- **Both classification inputs from the mixed residuals**, DLN 3.10, DLN 2.3 and the
scaled twist law. -/
theorem dln_inputs_of_mixedResiduals (h : NSMixedResidualsAll.{v, w})
    (hB : ZhuModularRepresentationInput.{u, v, w}) (hlift : MatrixDLNLifting)
    (hT : ZhuGaloisTwistInput.{u}) :
    VOA.Huang.CongruenceGaloisSplit.DLNCongruenceInput.{u} ∧
      VOA.Huang.CongruenceGaloisSplit.GaloisSymmetryNontrivialInput.{u} :=
  dln_inputs_of_NSKernel_twist (nsProjectiveKernelAll_of_mixedResiduals h) hB hlift hT

end VOA.Huang.DLNBridge
