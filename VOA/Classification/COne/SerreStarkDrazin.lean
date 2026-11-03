/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Serre–Stark S5-4a: Drazin decomposition and a growth lemma (finite-dimensional linear algebra)

Abstract input for the level-box argument (route C, step 4).

For an endomorphism `T` of a finite-dimensional complex vector space:

* `DrazinData T`: commuting polynomial expressions `πK`, `πI`, `TD` in `T` with `πK + πI = 1`,
  `πK πI = 0`, `T^d πK = 0` (`d = dim`), `T TD = πI`, `TD πI = TD` (the Fitting decomposition and
  the Drazin inverse); `drazinData T` constructs one from the characteristic polynomial.
* `norm_repr_pow_le`: if every eigenvalue of `T` has norm `< ρ'`, then the coordinates of `T^n x`
  are `O(ρ'^n)` uniformly (Gelfand's formula in the matrix algebra with the `L^∞` operator norm).
* `growth_vanish`: if every eigenvalue of `T` has norm `< ρ`, `σ ρ ≤ 1`, `w = πI w` and
  `ℓ(TD^m w) = O(σ^m)`, then `ℓ(T^k w) = 0` for all `k`.
-/

open Polynomial Module

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-! ## Commuting with polynomial expressions -/

theorem commute_aeval {T S : Module.End ℂ V} (h : Commute S T) (p : ℂ[X]) :
    Commute S (aeval T p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_right hq
  | monomial n a =>
    rw [aeval_monomial]
    exact (show Commute S (algebraMap ℂ (Module.End ℂ V) a) from
      (Algebra.commutes a S).symm).mul_right (h.pow_right n)

/-! ## Drazin data -/

/-- The Fitting decomposition `1 = πK + πI` and the Drazin inverse `TD` of `T`, all polynomial
in `T`. -/
structure DrazinData (T : Module.End ℂ V) where
  pK : ℂ[X]
  pI : ℂ[X]
  pD : ℂ[X]
  e : ℕ
  sum : aeval T pK + aeval T pI = 1
  KI : aeval T pK * aeval T pI = 0
  nil : T ^ e * aeval T pK = 0
  TTD : T * aeval T pD = aeval T pI
  TDI : aeval T pD * aeval T pI = aeval T pD

namespace DrazinData

variable {T : Module.End ℂ V} (D : DrazinData T)

/-- Projection onto the generalized kernel. -/
def πK : Module.End ℂ V := aeval T D.pK
/-- Projection onto the invertible part. -/
def πI : Module.End ℂ V := aeval T D.pI
/-- The Drazin inverse. -/
def TD : Module.End ℂ V := aeval T D.pD

theorem commute_πK {S : Module.End ℂ V} (h : Commute S T) : Commute S D.πK := commute_aeval h _
theorem commute_πI {S : Module.End ℂ V} (h : Commute S T) : Commute S D.πI := commute_aeval h _
theorem commute_TD {S : Module.End ℂ V} (h : Commute S T) : Commute S D.TD := commute_aeval h _

theorem sum' : D.πK + D.πI = 1 := D.sum
theorem KI' : D.πK * D.πI = 0 := D.KI
theorem IK' : D.πI * D.πK = 0 := by
  have : Commute (aeval T D.pI) (aeval T D.pK) := (Commute.all D.pI D.pK).map (aeval T)
  rw [πI, πK, this.eq]; exact D.KI
theorem TTD' : T * D.TD = D.πI := D.TTD
theorem TDT' : D.TD * T = D.πI := by
  rw [TD, ← (commute_aeval (Commute.refl T) D.pD).eq]; exact D.TTD
theorem TDI' : D.TD * D.πI = D.TD := D.TDI
theorem ITD' : D.πI * D.TD = D.TD := by
  have : Commute (aeval T D.pD) (aeval T D.pI) := (Commute.all D.pD D.pI).map (aeval T)
  rw [πI, TD, ← this.eq]; exact D.TDI
theorem nil' : T ^ D.e * D.πK = 0 := D.nil

theorem πI_idem : D.πI * D.πI = D.πI := by
  have h := congrArg (fun A => D.πI * A) D.sum'
  simp only [mul_add, mul_one, D.IK', zero_add] at h
  exact h

theorem πK_idem : D.πK * D.πK = D.πK := by
  have h := congrArg (fun A => D.πK * A) D.sum'
  simp only [mul_add, mul_one, D.KI', add_zero] at h
  exact h

theorem TD_πK : D.TD * D.πK = 0 := by
  rw [← D.TDI', mul_assoc, D.IK', mul_zero]

end DrazinData

/-- Existence of Drazin data (finite dimension), from the characteristic polynomial. -/
theorem nonempty_drazinData [FiniteDimensional ℂ V] (T : Module.End ℂ V) :
    Nonempty (DrazinData T) := by
  classical
  have hχ0 : T.charpoly ≠ 0 := (LinearMap.charpoly_monic T).ne_zero
  obtain ⟨χ', hχ, hndvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd T.charpoly hχ0 0
  simp only [map_zero, sub_zero] at hχ hndvd
  set e := T.charpoly.rootMultiplicity 0
  have hcop : IsCoprime ((X : ℂ[X]) ^ e) χ' :=
    ((Polynomial.irreducible_X.coprime_iff_not_dvd).2 hndvd).pow_left
  obtain ⟨a, b, hab⟩ := hcop
  set c₀ := χ'.coeff 0
  have hc₀ : c₀ ≠ 0 := by
    intro h; apply hndvd; rw [Polynomial.X_dvd_iff]; exact h
  have hdvd : (X : ℂ[X]) ∣ χ' - C c₀ := by
    rw [Polynomial.X_dvd_iff]; simp [c₀]
  obtain ⟨h, hh⟩ := hdvd
  have hCH' : aeval T ((X : ℂ[X]) ^ e * χ') = 0 := by
    rw [← hχ]; exact LinearMap.aeval_self_charpoly T
  refine ⟨{ pK := b * χ'
            pI := a * X ^ e
            pD := -(C c₀⁻¹) * h * (a * X ^ e)
            e := e
            sum := ?_
            KI := ?_
            nil := ?_
            TTD := ?_
            TDI := ?_ }⟩
  · rw [← map_add, add_comm, hab, map_one]
  · rw [← map_mul]
    have : b * χ' * (a * X ^ e) = (a * b) * (X ^ e * χ') := by ring
    rw [this, map_mul, hCH', mul_zero]
  · have : T ^ e * aeval T (b * χ') = aeval T (b * (X ^ e * χ')) := by
      rw [show b * (X ^ e * χ') = X ^ e * (b * χ') by ring, map_mul (aeval T) (X ^ e), map_pow,
        aeval_X]
    rw [this, map_mul, hCH', mul_zero]
  · have e1 : X * (-(C c₀⁻¹) * h * (a * X ^ e)) =
        a * X ^ e - C c₀⁻¹ * a * (X ^ e * χ') := by
      have : X * h = χ' - C c₀ := hh.symm
      have e2 : X * (-(C c₀⁻¹) * h * (a * X ^ e)) = -(C c₀⁻¹) * (X * h) * (a * X ^ e) := by ring
      rw [e2, this]
      have e3 : C c₀⁻¹ * C c₀ = (1 : ℂ[X]) := by rw [← C_mul, inv_mul_cancel₀ hc₀, C_1]
      linear_combination (a * X ^ e) * e3
    have : T * aeval T (-(C c₀⁻¹) * h * (a * X ^ e)) =
        aeval T (X * (-(C c₀⁻¹) * h * (a * X ^ e))) := by
      rw [map_mul (aeval T) X, aeval_X]
    rw [this, e1, map_sub, map_mul (aeval T) (C c₀⁻¹ * a), hCH', mul_zero, sub_zero]
  · rw [← map_mul]
    have : -(C c₀⁻¹) * h * (a * X ^ e) * (a * X ^ e) =
        -(C c₀⁻¹) * h * (a * X ^ e) + C c₀⁻¹ * h * a * b * (X ^ e * χ') := by
      have hb : a * X ^ e = 1 - b * χ' := by rw [← hab]; ring
      linear_combination (-(C c₀⁻¹) * h * (a * X ^ e)) * hb
    rw [this, map_add, map_mul (aeval T) (C c₀⁻¹ * h * a * b), hCH', mul_zero, add_zero]

/-- A choice of Drazin data. -/
def drazinData [FiniteDimensional ℂ V] (T : Module.End ℂ V) : DrazinData T :=
  Classical.choice (nonempty_drazinData T)

/-! ## Power bounds from eigenvalue bounds (Gelfand) -/

section Gelfand

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Powers of a complex square matrix whose spectrum lies in the open disc of radius `ρ'` are
`O(ρ'^n)`. -/
theorem matrix_norm_pow_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℂ) {ρ' : ℝ} (hρ' : 0 < ρ') (hM : ∀ z ∈ spectrum ℂ M, ‖z‖ < ρ') :
    ∃ C : ℝ, ∀ n : ℕ, ‖M ^ n‖ ≤ C * ρ' ^ n := by
  set r : NNReal := ⟨ρ', hρ'.le⟩ with hr
  have hsr : spectralRadius ℂ M < (r : ENNReal) := by
    apply spectrum.spectralRadius_lt_of_forall_lt
    intro z hz
    have := hM z hz
    exact_mod_cast this
  have hG := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius M
  have hev := (hG.eventually (gt_mem_nhds hsr))
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hev
  -- for `n ≥ max n₀ 1`, `‖M^n‖ < ρ'^n`
  have hbig : ∀ n, max n₀ 1 ≤ n → ‖M ^ n‖ ≤ ρ' ^ n := by
    intro n hn
    have h1 := hn₀ n (le_trans (le_max_left _ _) hn)
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    -- `(‖M^n‖₊)^(1/n) < ρ'` in `ℝ≥0∞`
    have h2 : ((‖M ^ n‖₊ : NNReal) : ENNReal) ^ (1 / (n : ℝ)) < (r : ENNReal) := h1
    rw [← ENNReal.coe_rpow_of_nonneg _ (by positivity), ENNReal.coe_lt_coe] at h2
    have h3 : ((‖M ^ n‖₊ : NNReal) : ℝ) ^ (1 / (n : ℝ)) < ρ' := by exact_mod_cast h2
    have h4 : ‖M ^ n‖ ^ (1 / (n : ℝ)) < ρ' := by simpa using h3
    have h5 : ‖M ^ n‖ = (‖M ^ n‖ ^ (1 / (n : ℝ))) ^ n := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), one_div_mul_cancel hnpos.ne',
        Real.rpow_one]
    rw [h5]
    exact pow_le_pow_left₀ (by positivity) h4.le n
  refine ⟨1 + ∑ k ∈ Finset.range (max n₀ 1), ‖M ^ k‖ / ρ' ^ k, fun n => ?_⟩
  by_cases hn : max n₀ 1 ≤ n
  · have hpos : 0 ≤ ∑ k ∈ Finset.range (max n₀ 1), ‖M ^ k‖ / ρ' ^ k :=
      Finset.sum_nonneg fun k _ => by positivity
    calc ‖M ^ n‖ ≤ ρ' ^ n := hbig n hn
      _ ≤ (1 + ∑ k ∈ Finset.range (max n₀ 1), ‖M ^ k‖ / ρ' ^ k) * ρ' ^ n := by
        have : 0 ≤ ρ' ^ n := by positivity
        nlinarith
  · push Not at hn
    have hmem : n ∈ Finset.range (max n₀ 1) := Finset.mem_range.2 hn
    have h1 : ‖M ^ n‖ / ρ' ^ n ≤ ∑ k ∈ Finset.range (max n₀ 1), ‖M ^ k‖ / ρ' ^ k :=
      Finset.single_le_sum (f := fun k => ‖M ^ k‖ / ρ' ^ k) (fun k _ => by positivity) hmem
    have hρn : 0 < ρ' ^ n := by positivity
    rw [div_le_iff₀ hρn] at h1
    nlinarith

end Gelfand

section Coords

open Matrix

variable [FiniteDimensional ℂ V]

/-- Coordinates of `T^n x` are `O(ρ'^n)` if all eigenvalues of `T` have norm `< ρ'`. -/
theorem norm_repr_pow_le {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℂ V)
    (T : Module.End ℂ V) {ρ' : ℝ} (hρ' : 0 < ρ') (hT : ∀ c, T.HasEigenvalue c → ‖c‖ < ρ') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : V) (i : ι),
      ‖b.repr ((T ^ n) x) i‖ ≤ C * ρ' ^ n * ∑ j, ‖b.repr x j‖ := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨0, le_rfl, fun n x i => (IsEmpty.false i).elim⟩
  letI := @Matrix.linftyOpNormedRing ι ℂ _ _ _
  letI := @Matrix.linftyOpNormedAlgebra ℂ ι ℂ _ _ _ _ _
  set M := LinearMap.toMatrixAlgEquiv b T
  have hspec : ∀ z ∈ spectrum ℂ M, ‖z‖ < ρ' := by
    intro z hz
    rw [AlgEquiv.spectrum_eq] at hz
    exact hT z (Module.End.hasEigenvalue_iff_mem_spectrum.2 hz)
  obtain ⟨C, hC⟩ := matrix_norm_pow_le M hρ' hspec
  have hC0 : 0 ≤ C := by
    have := hC 0
    simp only [pow_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  refine ⟨C, hC0, fun n x i => ?_⟩
  have hrep : b.repr ((T ^ n) x) = (M ^ n) *ᵥ b.repr x := by
    rw [← map_pow]
    have : LinearMap.toMatrixAlgEquiv b (T ^ n) = LinearMap.toMatrix b b (T ^ n) := by
      ext i j; rw [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
    rw [this]
    exact (LinearMap.toMatrix_mulVec_repr b b (T ^ n) x).symm
  rw [hrep, Matrix.mulVec, dotProduct]
  calc ‖∑ j, (M ^ n) i j * b.repr x j‖ ≤ ∑ j, ‖(M ^ n) i j‖ * ‖b.repr x j‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp
    _ ≤ ∑ j, ‖M ^ n‖ * ‖b.repr x j‖ := by
        refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [Matrix.linfty_opNorm_def]
        have h1 : ‖(M ^ n) i j‖₊ ≤ ∑ k, ‖(M ^ n) i k‖₊ :=
          Finset.single_le_sum (f := fun k => ‖(M ^ n) i k‖₊) (fun _ _ => by positivity)
            (Finset.mem_univ j)
        have h2 : ∑ k, ‖(M ^ n) i k‖₊ ≤
            (Finset.univ : Finset ι).sup fun i => ∑ k, ‖(M ^ n) i k‖₊ :=
          Finset.le_sup (f := fun i => ∑ k, ‖(M ^ n) i k‖₊) (Finset.mem_univ i)
        exact_mod_cast h1.trans h2
    _ = ‖M ^ n‖ * ∑ j, ‖b.repr x j‖ := by rw [Finset.mul_sum]
    _ ≤ C * ρ' ^ n * ∑ j, ‖b.repr x j‖ :=
        mul_le_mul_of_nonneg_right (hC n) (Finset.sum_nonneg fun _ _ => norm_nonneg _)

end Coords

/-! ## The growth lemma -/

section Growth

variable [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
theorem DrazinData.πI_TD_pow {T : Module.End ℂ V} (D : DrazinData T) {m : ℕ} (hm : 1 ≤ m) :
    D.πI * D.TD ^ m = D.TD ^ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  rw [pow_succ', ← mul_assoc, D.ITD']

omit [FiniteDimensional ℂ V] in
theorem DrazinData.TD_pow_T_pow {T : Module.End ℂ V} (D : DrazinData T) (n : ℕ) {x : V}
    (hx : D.πI x = x) : (D.TD ^ n) ((T ^ n) x) = x := by
  have hc : Commute D.TD T := (D.commute_TD (Commute.refl T)).symm
  have e : D.TD ^ n * T ^ n = D.πI ^ n := by rw [← hc.mul_pow, D.TDT']
  have h1 := congrArg (fun A : Module.End ℂ V => A x) e
  simp only [Module.End.mul_apply] at h1
  rw [h1]
  clear h1 e
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Module.End.mul_apply, hx, ih]

/-- **Growth lemma.** If all eigenvalues of `T` have norm `< ρ`, `0 ≤ σ ≤ 1`, `σ ρ ≤ 1`,
`w = πI w`, and `‖ℓ(TD^m w)‖ ≤ C σ^m` for `m ≥ 1`, then `ℓ(T^k w) = 0` for all `k`. -/
theorem growth_vanish (T : Module.End ℂ V) (D : DrazinData T) (ℓ : V →ₗ[ℂ] ℂ) {ρ σ : ℝ}
    (hT : ∀ c, T.HasEigenvalue c → ‖c‖ < ρ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hσρ : σ * ρ ≤ 1)
    {w : V} (hw : D.πI w = w) {C : ℝ}
    (hb : ∀ m : ℕ, 1 ≤ m → ‖ℓ ((D.TD ^ m) w)‖ ≤ C * σ ^ m) :
    ∀ k : ℕ, ℓ ((T ^ k) w) = 0 := by
  classical
  set W : Submodule ℂ V := Submodule.span ℂ (Set.range fun m : ℕ => (D.TD ^ (m + 1)) w) with hW
  have hgen : ∀ m : ℕ, (D.TD ^ (m + 1)) w ∈ W := fun m => Submodule.subset_span ⟨m, rfl⟩
  -- (a) `W` lies in the invertible part
  have hWI : ∀ x ∈ W, D.πI x = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      have := congrArg (fun A : Module.End ℂ V => A w) (D.πI_TD_pow (m := m + 1) (by omega))
      simpa only [Module.End.mul_apply] using this
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul a x _ hx => rw [map_smul, hx]
  -- (b) `W` is `TD`-stable
  have hWTD : ∀ x ∈ W, D.TD x ∈ W := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      have : D.TD ((D.TD ^ (m + 1)) w) = (D.TD ^ (m + 1 + 1)) w := by
        rw [pow_succ' D.TD (m + 1), Module.End.mul_apply]
      rw [this]; exact hgen (m + 1)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact W.add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact W.smul_mem a hx
  -- (c) `w ∈ W`
  have hwW : w ∈ W := by
    let f : W →ₗ[ℂ] W := D.TD.restrict hWTD
    have hinj : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      have h0 : D.TD (x : V) = 0 := by
        have := congrArg Subtype.val hx
        simpa [f] using this
      have : (x : V) = 0 := by
        rw [← hWI x x.2]
        have e := congrArg (fun A : Module.End ℂ V => A x) D.TTD'
        simp only [Module.End.mul_apply] at e
        rw [← e, h0, map_zero]
      exact Subtype.ext this
    have hsurj : Function.Surjective f := LinearMap.injective_iff_surjective.1 hinj
    obtain ⟨y, hy⟩ := hsurj ⟨D.TD w, by simpa using hgen 0⟩
    have hy' : D.TD (y : V) = D.TD w := congrArg Subtype.val hy
    have hd : (y : V) - w = 0 := by
      have hI : D.πI ((y : V) - w) = (y : V) - w := by rw [map_sub, hWI y y.2, hw]
      rw [← hI]
      have e := congrArg (fun A : Module.End ℂ V => A ((y : V) - w)) D.TTD'
      simp only [Module.End.mul_apply] at e
      rw [← e, map_sub, hy', sub_self, map_zero]
    rw [← sub_eq_zero.1 hd]; exact y.2
  -- (d) `W` is `T`-stable
  have hWT : ∀ x ∈ W, T x ∈ W := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      have e : T ((D.TD ^ (m + 1)) w) = D.πI ((D.TD ^ m) w) := by
        rw [pow_succ', Module.End.mul_apply, ← Module.End.mul_apply T, D.TTD']
      rw [e]
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simpa [hw] using hwW
      · have := congrArg (fun A : Module.End ℂ V => A w) (D.πI_TD_pow (m := m) h)
        simp only [Module.End.mul_apply] at this
        rw [this]
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' h
        exact hgen k
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact W.add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact W.smul_mem a hx
  have hWTpow : ∀ k : ℕ, ∀ x ∈ W, (T ^ k) x ∈ W := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      rw [pow_succ', Module.End.mul_apply]
      exact hWT _ (ih x hx)
  -- (e) the `TD`-orbits of `W` are `O(σ^n)`
  have hbd : ∀ x ∈ W, ∃ C' : ℝ, ∀ n : ℕ, ‖ℓ ((D.TD ^ n) x)‖ ≤ C' * σ ^ n := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      refine ⟨max C 0, fun n => ?_⟩
      have e : (D.TD ^ n) ((D.TD ^ (m + 1)) w) = (D.TD ^ (n + (m + 1))) w := by
        rw [← Module.End.mul_apply, ← pow_add]
      rw [e]
      have h1 := hb (n + (m + 1)) (by omega)
      have hσm : σ ^ (m + 1) ≤ 1 := pow_le_one₀ hσ0 hσ1
      calc ‖ℓ ((D.TD ^ (n + (m + 1))) w)‖ ≤ C * σ ^ (n + (m + 1)) := h1
        _ ≤ max C 0 * σ ^ (n + (m + 1)) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hσ0 _)
        _ = max C 0 * σ ^ n * σ ^ (m + 1) := by rw [pow_add]; ring
        _ ≤ max C 0 * σ ^ n * 1 :=
            mul_le_mul_of_nonneg_left hσm (mul_nonneg (le_max_right _ _) (pow_nonneg hσ0 _))
        _ = max C 0 * σ ^ n := mul_one _
    | zero => exact ⟨0, fun n => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨C₁, h₁⟩ := hx
      obtain ⟨C₂, h₂⟩ := hy
      refine ⟨C₁ + C₂, fun n => ?_⟩
      rw [map_add, map_add]
      calc ‖ℓ ((D.TD ^ n) x) + ℓ ((D.TD ^ n) y)‖ ≤ ‖ℓ ((D.TD ^ n) x)‖ + ‖ℓ ((D.TD ^ n) y)‖ :=
            norm_add_le _ _
        _ ≤ C₁ * σ ^ n + C₂ * σ ^ n := add_le_add (h₁ n) (h₂ n)
        _ = (C₁ + C₂) * σ ^ n := by ring
    | smul a x _ hx =>
      obtain ⟨C₁, h₁⟩ := hx
      refine ⟨‖a‖ * C₁, fun n => ?_⟩
      rw [map_smul, map_smul, smul_eq_mul, norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (h₁ n) (norm_nonneg a)
  -- (f) `ℓ` vanishes on `W`
  have hzero : ∀ x ∈ W, ℓ x = 0 := by
    let TW : Module.End ℂ W := T.restrict hWT
    by_cases hnt : Nontrivial W
    swap
    · intro x hx
      rw [not_nontrivial_iff_subsingleton] at hnt
      have : (⟨x, hx⟩ : W) = 0 := Subsingleton.elim _ _
      have : x = 0 := congrArg Subtype.val this
      rw [this, map_zero]
    -- eigenvalues of `TW` are eigenvalues of `T`
    have hTW : ∀ c, TW.HasEigenvalue c → ‖c‖ < ρ := by
      intro c hc
      obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
      apply hT c
      refine Module.End.hasEigenvalue_of_hasEigenvector (x := (v : V)) ?_
      refine ⟨?_, fun h => hv.2 (Subtype.ext h)⟩
      rw [Module.End.mem_eigenspace_iff]
      have := Module.End.mem_eigenspace_iff.1 hv.1
      exact congrArg Subtype.val this
    -- a radius `ρ'` strictly between the eigenvalues and `ρ`
    have hfin := TW.finite_hasEigenvalue
    obtain ⟨c₀, hc₀⟩ := Module.End.exists_eigenvalue TW
    obtain ⟨cm, hcm, hmax⟩ := Set.exists_max_image _ (fun c : ℂ => ‖c‖) hfin ⟨c₀, hc₀⟩
    have hcmρ := hTW cm hcm
    set ρ' := (‖cm‖ + ρ) / 2 with hρ'
    have hρ'pos : 0 < ρ' := by have := norm_nonneg cm; rw [hρ']; linarith
    have hρ'ρ : ρ' < ρ := by rw [hρ']; linarith
    have hTW' : ∀ c, TW.HasEigenvalue c → ‖c‖ < ρ' := by
      intro c hc
      have := hmax c hc
      rw [hρ']; linarith
    have hσρ' : σ * ρ' < 1 := by
      rcases hσ0.lt_or_eq with h | h
      · calc σ * ρ' < σ * ρ := mul_lt_mul_of_pos_left hρ'ρ h
          _ ≤ 1 := hσρ
      · rw [← h, zero_mul]; norm_num
    let b := Module.finBasis ℂ W
    obtain ⟨C₁, hC₁0, hC₁⟩ := norm_repr_pow_le b TW hρ'pos hTW'
    have hbb : ∀ i, ∃ C' : ℝ, ∀ n : ℕ, ‖ℓ ((D.TD ^ n) (b i : V))‖ ≤ C' * σ ^ n :=
      fun i => hbd _ (b i).2
    choose Cb hCb using hbb
    intro x hx
    set y : W := ⟨x, hx⟩
    set Sy := ∑ j, ‖b.repr y j‖
    set K := C₁ * Sy * ∑ i, |Cb i|
    have hTn : ∀ n : ℕ, ((TW ^ n) y : V) = (T ^ n) x := by
      intro n
      induction n with
      | zero => simp [y]
      | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply]
        change T (((TW ^ n) y : W) : V) = T ((T ^ n) x)
        rw [ih]
    have hbound : ∀ n : ℕ, ‖ℓ x‖ ≤ K * (σ * ρ') ^ n := by
      intro n
      have hx' : x = (D.TD ^ n) ((T ^ n) x) := (D.TD_pow_T_pow n (hWI x hx)).symm
      have hsum : (T ^ n) x = ∑ i, b.repr ((TW ^ n) y) i • (b i : V) := by
        rw [← hTn n]
        have h2 := congrArg (fun z : W => (z : V)) (b.sum_repr ((TW ^ n) y))
        simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
        exact h2.symm
      rw [hx', hsum, map_sum, map_sum]
      simp only [map_smul, smul_eq_mul]
      calc ‖∑ i, b.repr ((TW ^ n) y) i * ℓ ((D.TD ^ n) (b i : V))‖
          ≤ ∑ i, ‖b.repr ((TW ^ n) y) i‖ * ‖ℓ ((D.TD ^ n) (b i : V))‖ := by
            refine (norm_sum_le _ _).trans (le_of_eq ?_)
            simp
        _ ≤ ∑ i, (C₁ * ρ' ^ n * Sy) * (|Cb i| * σ ^ n) := by
            refine Finset.sum_le_sum fun i _ => mul_le_mul (hC₁ n y i) ?_ (norm_nonneg _)
              (by positivity)
            exact (hCb i n).trans (mul_le_mul_of_nonneg_right (le_abs_self _)
              (pow_nonneg hσ0 _))
        _ = K * (σ * ρ') ^ n := by
            simp only [K, Finset.mul_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring_nf
    have ht : Filter.Tendsto (fun n : ℕ => K * (σ * ρ') ^ n) Filter.atTop (nhds 0) := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one (mul_nonneg hσ0 hρ'pos.le) hσρ'
      simpa using this.const_mul K
    have : ‖ℓ x‖ ≤ 0 := ge_of_tendsto ht (Filter.Eventually.of_forall hbound)
    exact norm_le_zero_iff.1 this
  intro k
  exact hzero _ (hWTpow k w hwW)

end Growth

/-! ## The Fricke expansion operators `Η(m)` and their span -/

section Eta

/-- The coefficient operators of `(p y − ψ)(p y − T)^{-1}` expanded in powers of `y`
(invertible part: Neumann series in `y`; nilpotent part: finitely many negative powers):
* `m ≥ 1`: `Η(m) = −p^m TD^{m+1} (T − ψ) πI`;
* `m = 0`: `Η(0) = πK + ψ TD`;
* `m = −j ≤ −1`: `Η(−j) = p^{−j} (T^j − ψ T^{j−1}) πK`. -/
def DrazinData.eta {T : Module.End ℂ V} (D : DrazinData T) (ψ : ℂ) (p : ℕ) (m : ℤ) :
    Module.End ℂ V :=
  if 1 ≤ m then -((p : ℂ) ^ m.toNat) • (D.TD ^ (m.toNat + 1) * (T - ψ • 1) * D.πI)
  else if m = 0 then D.πK + ψ • D.TD
  else ((p : ℂ) ^ (-m).toNat)⁻¹ • ((T ^ (-m).toNat - ψ • T ^ ((-m).toNat - 1)) * D.πK)

theorem DrazinData.eta_pos {T : Module.End ℂ V} (D : DrazinData T) (ψ : ℂ) (p : ℕ) (n : ℕ) :
    D.eta ψ p ((n : ℤ) + 1) =
      -((p : ℂ) ^ (n + 1)) • (D.TD ^ (n + 2) * (T - ψ • 1) * D.πI) := by
  rw [DrazinData.eta, if_pos (by omega)]
  have : ((n : ℤ) + 1).toNat = n + 1 := by omega
  rw [this]

theorem DrazinData.eta_zero {T : Module.End ℂ V} (D : DrazinData T) (ψ : ℂ) (p : ℕ) :
    D.eta ψ p 0 = D.πK + ψ • D.TD := by
  rw [DrazinData.eta, if_neg (by omega), if_pos rfl]

theorem DrazinData.eta_neg {T : Module.End ℂ V} (D : DrazinData T) (ψ : ℂ) (p : ℕ) (n : ℕ) :
    D.eta ψ p (-((n : ℤ) + 1)) =
      ((p : ℂ) ^ (n + 1))⁻¹ • ((T ^ (n + 1) - ψ • T ^ n) * D.πK) := by
  rw [DrazinData.eta, if_neg (by omega), if_neg (by omega)]
  have : (-(-((n : ℤ) + 1))).toNat = n + 1 := by omega
  rw [this, Nat.add_sub_cancel]

variable [FiniteDimensional ℂ V]

/-- `πI` and all `T^k πI` lie in the span of `TD^m`, `m ≥ 1`. -/
theorem DrazinData.pow_πI_mem_span {T : Module.End ℂ V} (D : DrazinData T) (k : ℕ) :
    T ^ k * D.πI ∈ Submodule.span ℂ (Set.range fun m : ℕ => D.TD ^ (m + 1)) := by
  set 𝒯 := Submodule.span ℂ (Set.range fun m : ℕ => D.TD ^ (m + 1)) with h𝒯
  have hgen : ∀ m : ℕ, D.TD ^ (m + 1) ∈ 𝒯 := fun m => Submodule.subset_span ⟨m, rfl⟩
  have hI : ∀ X ∈ 𝒯, D.πI * X = X := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem X hX => obtain ⟨m, rfl⟩ := hX; exact D.πI_TD_pow (by omega)
    | zero => simp
    | add X Y _ _ hX hY => rw [mul_add, hX, hY]
    | smul a X _ hX => rw [mul_smul_comm, hX]
  have hTD : ∀ X ∈ 𝒯, D.TD * X ∈ 𝒯 := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem X hX => obtain ⟨m, rfl⟩ := hX; rw [← pow_succ']; exact hgen (m + 1)
    | zero => simp
    | add X Y _ _ hX hY => rw [mul_add]; exact 𝒯.add_mem hX hY
    | smul a X _ hX => rw [mul_smul_comm]; exact 𝒯.smul_mem a hX
  -- `πI ∈ 𝒯`: left multiplication by `TD` is injective, hence surjective, on `𝒯`
  have hπI : D.πI ∈ 𝒯 := by
    let f : 𝒯 →ₗ[ℂ] 𝒯 := (LinearMap.mulLeft ℂ D.TD).restrict hTD
    have hinj : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro X hX
      have h0 : D.TD * (X : Module.End ℂ V) = 0 := congrArg Subtype.val hX
      apply Subtype.ext
      change (X : Module.End ℂ V) = 0
      rw [← hI X X.2, ← D.TTD', mul_assoc, h0, mul_zero]
    obtain ⟨Y, hY⟩ := (LinearMap.injective_iff_surjective.1 hinj) ⟨D.TD, by simpa using hgen 0⟩
    have hY' : D.TD * (Y : Module.End ℂ V) = D.TD := congrArg Subtype.val hY
    have : D.πI = (Y : Module.End ℂ V) := by
      have := congrArg (fun A => T * A) hY'
      simp only at this
      rw [← mul_assoc, D.TTD', hI Y Y.2] at this
      exact this.symm
    rw [this]; exact Y.2
  have hT : ∀ X ∈ 𝒯, T * X ∈ 𝒯 := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem X hX =>
      obtain ⟨m, rfl⟩ := hX
      simp only
      rw [pow_succ', ← mul_assoc, D.TTD']
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simpa using hπI
      · rw [D.πI_TD_pow h]
        obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' h
        exact hgen j
    | zero => simp
    | add X Y _ _ hX hY => rw [mul_add]; exact 𝒯.add_mem hX hY
    | smul a X _ hX => rw [mul_smul_comm]; exact 𝒯.smul_mem a hX
  induction k with
  | zero => simpa using hπI
  | succ k ih => rw [pow_succ', mul_assoc]; exact hT _ ih

/-- **Spanning lemma.** For `p ≠ 0`, every power `T^k` is a linear combination of the
operators `Η(m)`. -/
theorem DrazinData.pow_mem_span_eta {T : Module.End ℂ V} (D : DrazinData T) (ψ : ℂ) {p : ℕ}
    (hp : p ≠ 0) (k : ℕ) : T ^ k ∈ Submodule.span ℂ (Set.range (D.eta ψ p)) := by
  set S := Submodule.span ℂ (Set.range (D.eta ψ p)) with hS
  have hmem : ∀ m, D.eta ψ p m ∈ S := fun m => Submodule.subset_span ⟨m, rfl⟩
  have hp' : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp
  have hcK : Commute T D.πK := D.commute_πK (Commute.refl T)
  have hcI : Commute T D.πI := D.commute_πI (Commute.refl T)
  have hcD : Commute T D.TD := D.commute_TD (Commute.refl T)
  -- (1) `T^n (T − ψ) πK ∈ S`
  have h1 : ∀ n : ℕ, (T ^ (n + 1) - ψ • T ^ n) * D.πK ∈ S := by
    intro n
    have := S.smul_mem ((p : ℂ) ^ (n + 1)) (hmem (-((n : ℤ) + 1)))
    rwa [D.eta_neg, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hp'), one_smul] at this
  -- (2) `T^k πK ∈ S`
  have h2 : ∀ k : ℕ, T ^ k * D.πK ∈ S := by
    by_cases hψ : ψ = 0
    · intro k
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        have := hmem 0
        rwa [D.eta_zero, hψ, zero_smul, add_zero, ← one_mul D.πK, ← pow_zero T] at this
      · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hk
        have := h1 n
        rwa [hψ, zero_smul, sub_zero] at this
    · intro k
      -- `πK = (T − ψ) Q(T) πK` with `Q = −Σ_{i<e} ψ^{-i-1} T^i`
      have key : T ^ k * D.πK = ∑ i ∈ Finset.range D.e,
          (-(ψ⁻¹ ^ (i + 1))) • ((T ^ (k + i + 1) - ψ • T ^ (k + i)) * D.πK) := by
        have hgeom : ∀ e : ℕ, ∑ i ∈ Finset.range e,
            (-(ψ⁻¹ ^ (i + 1))) • ((T ^ (k + i + 1) - ψ • T ^ (k + i)) * D.πK) =
            T ^ k * D.πK - ψ⁻¹ ^ e • (T ^ (k + e) * D.πK) := by
          intro e
          induction e with
          | zero => simp
          | succ e ih =>
            rw [Finset.sum_range_succ, ih]
            have e1 : ψ⁻¹ ^ (e + 1) * ψ = ψ⁻¹ ^ e := by
              rw [pow_succ, mul_assoc, inv_mul_cancel₀ hψ, mul_one]
            rw [sub_mul, smul_sub, smul_mul_assoc, smul_smul, neg_mul, e1]
            simp only [neg_smul, show k + (e + 1) = k + e + 1 by ring]
            abel
        rw [hgeom D.e]
        have : T ^ (k + D.e) * D.πK = 0 := by rw [pow_add, mul_assoc, D.nil', mul_zero]
        rw [this, smul_zero, sub_zero]
      rw [key]
      exact S.sum_mem fun i _ => S.smul_mem _ (by
        have := h1 (k + i); simpa [add_assoc] using this)
  -- (3) `TD^{m+1} ∈ S`
  have hTDI : ∀ j : ℕ, D.TD ^ (j + 1) * D.πI = D.TD ^ (j + 1) := by
    intro j; rw [pow_succ, mul_assoc, D.TDI']
  have hform : ∀ n : ℕ, D.TD ^ (n + 2) * (T - ψ • 1) * D.πI =
      D.TD ^ (n + 1) - ψ • D.TD ^ (n + 2) := by
    intro n
    have e1 : D.TD ^ (n + 2) * T = D.TD ^ (n + 1) * D.πI := by
      rw [pow_succ D.TD (n + 1), mul_assoc, D.TDT']
    rw [mul_sub, sub_mul, mul_smul_comm, mul_one, smul_mul_assoc, e1, mul_assoc, D.πI_idem,
      hTDI (n + 1), hTDI n]
  have h3 : ∀ m : ℕ, D.TD ^ (m + 1) ∈ S := by
    by_cases hψ : ψ = 0
    · intro m
      have := S.smul_mem (-((p : ℂ) ^ (m + 1))⁻¹) (hmem ((m : ℤ) + 1))
      rw [D.eta_pos, hform, hψ, zero_smul, sub_zero, smul_smul] at this
      rwa [show -((p : ℂ) ^ (m + 1))⁻¹ * -(p : ℂ) ^ (m + 1) = 1 by
        rw [neg_mul_neg, inv_mul_cancel₀ (pow_ne_zero _ hp')], one_smul] at this
    · intro m
      induction m with
      | zero =>
        have h0 := hmem 0
        rw [D.eta_zero] at h0
        have hK : D.πK ∈ S := by simpa using h2 0
        have : ψ • D.TD ∈ S := by simpa using S.sub_mem h0 hK
        have := S.smul_mem ψ⁻¹ this
        rwa [smul_smul, inv_mul_cancel₀ hψ, one_smul, ← pow_one D.TD] at this
      | succ m ih =>
        have hη := hmem ((m : ℤ) + 1)
        rw [D.eta_pos, hform] at hη
        -- `TD^{m+2} = ψ⁻¹ (TD^{m+1} + p^{-(m+1)} Η(m+1))`
        have e : D.TD ^ (m + 1 + 1) = ψ⁻¹ • (D.TD ^ (m + 1) +
            ((p : ℂ) ^ (m + 1))⁻¹ • (-((p : ℂ) ^ (m + 1)) • (D.TD ^ (m + 1) -
              ψ • D.TD ^ (m + 2)))) := by
          rw [smul_smul, mul_neg, inv_mul_cancel₀ (pow_ne_zero _ hp'), neg_one_smul, neg_sub,
            add_sub_cancel, smul_smul, inv_mul_cancel₀ hψ, one_smul]
        rw [e]
        exact S.smul_mem _ (S.add_mem ih (S.smul_mem _ hη))
  -- (4) assemble
  have h4 : T ^ k * D.πI ∈ S := by
    have := D.pow_πI_mem_span k
    refine (Submodule.span_le.2 ?_) this
    rintro _ ⟨m, rfl⟩
    exact h3 m
  have : T ^ k = T ^ k * D.πK + T ^ k * D.πI := by rw [← mul_add, D.sum', mul_one]
  rw [this]
  exact S.add_mem (h2 k) h4

omit [FiniteDimensional ℂ V] in
/-- **The recurrence of the expansion coefficients**:
`p Η(m − 1) − T Η(m) = [m = 1] p − [m = 0] ψ` (the coefficients of `(p y − T) · Σ Η(m) yᵐ`). -/
theorem DrazinData.eta_rec {T : Module.End ℂ V} (D : DrazinData T) (ψ : ℂ) (p : ℕ) (m : ℤ)
    (hp : (p : ℂ) ≠ 0) :
    (p : ℂ) • D.eta ψ p (m - 1) - T * D.eta ψ p m =
      (if m = 1 then (p : ℂ) • 1 else 0) - (if m = 0 then ψ • 1 else 0) := by
  have hTD : T * D.TD = D.πI := D.TTD'
  -- `T TD^{j+2} = TD^{j+1}`
  have hTpow : ∀ j : ℕ, T * D.TD ^ (j + 2) = D.TD ^ (j + 1) := by
    intro j
    rw [pow_succ' D.TD (j + 1), ← mul_assoc, hTD, D.πI_TD_pow (by omega)]
  rcases lt_trichotomy m 0 with hm | hm | hm
  · -- `m = −(n+1)`
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = -((n : ℤ) + 1) := ⟨(-m - 1).toNat, by omega⟩
    rw [if_neg (by omega), if_neg (by omega), sub_zero,
      show -((n : ℤ) + 1) - 1 = -(((n + 1 : ℕ) : ℤ) + 1) by push_cast; ring,
      D.eta_neg, D.eta_neg, smul_smul]
    have hpinv : (p : ℂ) * ((p : ℂ) ^ (n + 1 + 1))⁻¹ = ((p : ℂ) ^ (n + 1))⁻¹ := by
      rw [pow_succ _ (n + 1), mul_inv, ← mul_assoc, mul_comm (p : ℂ), mul_assoc,
        mul_inv_cancel₀ hp, mul_one]
    rw [hpinv, mul_smul_comm, ← smul_sub]
    have : (T ^ (n + 1 + 1) - ψ • T ^ (n + 1)) * D.πK -
        T * ((T ^ (n + 1) - ψ • T ^ n) * D.πK) = 0 := by
      rw [← mul_assoc, mul_sub, mul_smul_comm, ← pow_succ', ← pow_succ', sub_self]
    rw [this, smul_zero]
  · subst hm
    rw [if_neg (by omega), if_pos rfl, zero_sub,
      show (-1 : ℤ) = -(((0 : ℕ) : ℤ) + 1) by norm_num, D.eta_neg, D.eta_zero]
    simp only [zero_add, pow_one, pow_zero]
    rw [smul_smul, mul_inv_cancel₀ hp, one_smul, mul_add, mul_smul_comm, hTD,
      sub_mul, smul_mul_assoc, one_mul, ← D.sum']
    module
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = (n : ℤ) + 1 := ⟨(m - 1).toNat, by omega⟩
    rw [if_neg (show (n : ℤ) + 1 ≠ 0 by omega), sub_zero]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [if_pos (by norm_num), show ((0 : ℕ) : ℤ) + 1 - 1 = 0 by norm_num, D.eta_zero]
      have h1 := D.eta_pos ψ p 0
      simp only [Nat.cast_zero, zero_add, pow_one] at h1 ⊢
      rw [h1]
      -- `T TD² (T − ψ) πI = πI − ψ TD`
      have e1 : T * (D.TD ^ 2 * (T - ψ • 1) * D.πI) = D.πI - ψ • D.TD := by
        rw [← mul_assoc, ← mul_assoc, show (2 : ℕ) = 0 + 2 from rfl, hTpow 0, pow_one,
          mul_sub, sub_mul, mul_smul_comm, mul_one, smul_mul_assoc, D.TDT', D.πI_idem, D.TDI']
      rw [mul_smul_comm, e1, ← D.sum']
      module
    · rw [if_neg (by omega)]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
      rw [show ((k + 1 : ℕ) : ℤ) + 1 - 1 = ((k : ℕ) : ℤ) + 1 by push_cast; ring,
        show ((k + 1 : ℕ) : ℤ) + 1 = (((k + 1 : ℕ) : ℕ) : ℤ) + 1 from rfl, D.eta_pos, D.eta_pos]
      have e2 : T * (D.TD ^ (k + 1 + 2) * (T - ψ • 1) * D.πI) =
          D.TD ^ (k + 2) * (T - ψ • 1) * D.πI := by
        rw [← mul_assoc, ← mul_assoc, hTpow (k + 1)]
      rw [mul_smul_comm, e2]
      module

omit [FiniteDimensional ℂ V] in
/-- `Η(m) = 0` for `m ≤ −(e + 1)`. -/
theorem DrazinData.eta_neg_eq_zero {T : Module.End ℂ V} (D : DrazinData T) (ψ : ℂ) (p : ℕ)
    {n : ℕ} (hn : D.e ≤ n) : D.eta ψ p (-((n : ℤ) + 1)) = 0 := by
  rw [D.eta_neg]
  have h1 : T ^ n * D.πK = 0 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [add_comm, pow_add, mul_assoc, D.nil', mul_zero]
  have h2 : T ^ (n + 1) * D.πK = 0 := by rw [pow_succ', mul_assoc, h1, mul_zero]
  rw [sub_mul, h2, smul_mul_assoc, h1, smul_zero, sub_zero, smul_zero]

end Eta

end SSHecke

end VOA.Classification.COne
