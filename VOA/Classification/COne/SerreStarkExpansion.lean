/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkFEClass
import VOA.Classification.COne.SerreStarkOdd
import VOA.Classification.COne.SerreStarkArith

/-!
# Serre–Stark S5-7a: expansion of the resolvent factors at the other side

For each prime `p ∣ N` the operator `(p y − ψ(p)) (p y − U_p)^{-1}` has the Laurent expansion
`Σ_m Η_p(m) yᵐ` (finitely many negative powers, `Η_p` from `DrazinData.eta`). We prove it in the
matrix algebra (`hatE_mul`: `(p y − M_p) Σ_m yᵐ Η_p(m) = p y − ψ(p)`, from the recurrence
`DrazinData.eta_rec`) and transport it back to the commutative operator algebra through a basis
(`tildeE`, `tildeE_mul`), where products over primes expand by `Finset.prod_univ_sum`.
-/

open Complex Filter Topology
open scoped UpperHalfPlane

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

namespace ClassSetup

variable (S : ClassSetup)

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- `Η_p(m)` as a matrix. -/
def etaM (p : S.ι) (m : ℤ) : S.Mat := S.ιm (S.etaA p m)

theorem coe_Ua (p : S.ι) : ((S.Ua p : S.opAlg) : Module.End ℂ S.V) = S.U p := rfl

theorem etaA_rec (p : S.ι) (m : ℤ) :
    (p.1 : ℂ) • S.etaA p (m - 1) - S.Ua p * S.etaA p m =
      (if m = 1 then (p.1 : ℂ) • 1 else 0) - (if m = 0 then S.ψp p • 1 else 0) := by
  apply Subtype.ext
  have h := (S.Dp p).eta_rec (S.ψp p) p.1 m (Nat.cast_ne_zero.2 (S.prime p).ne_zero)
  simp only [Subalgebra.coe_sub, Subalgebra.coe_smul, Subalgebra.coe_mul, coe_etaA, coe_Ua]
  rw [h]
  split_ifs <;> simp

theorem etaM_rec (p : S.ι) (m : ℤ) :
    (p.1 : ℂ) • S.etaM p (m - 1) - S.Mp p * S.etaM p m =
      (if m = 1 then (p.1 : ℂ) • 1 else 0) - (if m = 0 then S.ψp p • 1 else 0) := by
  have h := congrArg S.ιm (S.etaA_rec p m)
  simp only [map_sub, map_smul, map_mul] at h
  rw [etaM, etaM, Mp, h]
  split_ifs <;> simp

theorem etaM_neg_eq_zero (p : S.ι) {n : ℕ} (hn : (S.Dp p).e ≤ n) :
    S.etaM p (-((n : ℤ) + 1)) = 0 := by
  have : S.etaA p (-((n : ℤ) + 1)) = 0 := by
    apply Subtype.ext
    rw [coe_etaA]
    exact (S.Dp p).eta_neg_eq_zero (S.ψp p) p.1 hn
  rw [etaM, this, map_zero]

/-- Geometric bound for the matrices `Η_p(n)`, `n ≥ 0`. -/
theorem etaM_bound (p : S.ι) : ∃ K R : ℝ, 0 ≤ K ∧ 0 < R ∧ ∀ n : ℕ,
    ‖S.etaM p n‖ ≤ K * R ^ n := by
  set T := S.ιm (S.TDa p)
  set A := S.ιm (S.Ua p - S.ψp p • 1)
  set B := S.ιm (S.πIa p)
  set K := ‖S.etaM p 0‖ + ‖T‖ * ‖A‖ * ‖B‖
  set R := (p.1 : ℝ) * (‖T‖ + 1)
  have hp1 : (1 : ℝ) ≤ p.1 := by exact_mod_cast (S.prime p).one_lt.le
  refine ⟨K, R, by positivity, by positivity, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [Nat.cast_zero, pow_zero, mul_one, K]
    have : 0 ≤ ‖T‖ * ‖A‖ * ‖B‖ := by positivity
    linarith
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    have he : S.etaM p ((k + 1 : ℕ) : ℤ) = -((p.1 : ℂ) ^ (k + 1)) • (T ^ (k + 2) * A * B) := by
      have h1 : S.etaA p ((k : ℤ) + 1) = -((p.1 : ℂ) ^ (k + 1)) •
          (S.TDa p ^ (k + 2) * (S.Ua p - S.ψp p • 1) * S.πIa p) := by
        apply Subtype.ext
        rw [coe_etaA, (S.Dp p).eta_pos]
        simp only [Subalgebra.coe_smul, Subalgebra.coe_mul, SubmonoidClass.coe_pow,
          Subalgebra.coe_sub, Subalgebra.coe_one, coe_Ua]
        rfl
      rw [etaM, show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by push_cast; ring, h1, map_smul, map_mul,
        map_mul, map_pow]
    rw [he, norm_smul, norm_neg, norm_pow, Complex.norm_natCast]
    have h1 : ‖T ^ (k + 2) * A * B‖ ≤ ‖T‖ ^ (k + 2) * ‖A‖ * ‖B‖ := by
      calc ‖T ^ (k + 2) * A * B‖ ≤ ‖T ^ (k + 2) * A‖ * ‖B‖ := norm_mul_le _ _
        _ ≤ ‖T ^ (k + 2)‖ * ‖A‖ * ‖B‖ := by gcongr; exact norm_mul_le _ _
        _ ≤ ‖T‖ ^ (k + 2) * ‖A‖ * ‖B‖ := by gcongr; exact norm_pow_le' _ (by omega)
    have h2 : ‖T‖ ^ (k + 2) ≤ ‖T‖ * (‖T‖ + 1) ^ (k + 1) := by
      rw [pow_succ' ‖T‖ (k + 1)]
      gcongr
      linarith [norm_nonneg T]
    have hK : ‖T‖ * ‖A‖ * ‖B‖ ≤ K := by
      simp only [K]; linarith [norm_nonneg (S.etaM p 0)]
    calc (p.1 : ℝ) ^ (k + 1) * ‖T ^ (k + 2) * A * B‖
        ≤ (p.1 : ℝ) ^ (k + 1) * (‖T‖ * (‖T‖ + 1) ^ (k + 1) * ‖A‖ * ‖B‖) := by
          gcongr
          calc ‖T ^ (k + 2) * A * B‖ ≤ ‖T‖ ^ (k + 2) * ‖A‖ * ‖B‖ := h1
            _ ≤ ‖T‖ * (‖T‖ + 1) ^ (k + 1) * ‖A‖ * ‖B‖ := by gcongr
      _ = (‖T‖ * ‖A‖ * ‖B‖) * R ^ (k + 1) := by simp only [R]; rw [mul_pow]; ring
      _ ≤ K * R ^ (k + 1) := by gcongr

/-! ## The matrix Laurent series -/

/-- `Ê_p(y) = Σ_m yᵐ Η_p(m)`. -/
def hatE (p : S.ι) (y : ℂ) : S.Mat := ∑' m : ℤ, y ^ m • S.etaM p m

theorem summable_etaM (p : S.ι) : ∃ ε > 0, ∀ y : ℂ, y ≠ 0 → ‖y‖ < ε →
    Summable (fun m : ℤ => ‖y ^ m • S.etaM p m‖) := by
  obtain ⟨K, R, hK, hR, hb⟩ := S.etaM_bound p
  refine ⟨R⁻¹, inv_pos.2 hR, fun y hy0 hy => ?_⟩
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · have hq : ‖y‖ * R < 1 := by
      have := mul_lt_mul_of_pos_right hy hR
      rwa [inv_mul_cancel₀ hR.ne'] at this
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      ((summable_geometric_of_lt_one (by positivity) hq).mul_left K)
    simp only [zpow_natCast]
    rw [norm_smul, norm_pow]
    calc ‖y‖ ^ n * ‖S.etaM p n‖ ≤ ‖y‖ ^ n * (K * R ^ n) :=
          mul_le_mul_of_nonneg_left (hb n) (by positivity)
      _ = K * (‖y‖ * R) ^ n := by rw [mul_pow]; ring
  · refine summable_of_ne_finset_zero (s := Finset.range ((S.Dp p).e + 1)) fun n hn => ?_
    rw [Finset.mem_range, not_lt] at hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [show -((k + 1 : ℕ) : ℤ) = -((k : ℤ) + 1) by push_cast; ring,
      S.etaM_neg_eq_zero p (by omega), smul_zero, norm_zero]

theorem hatE_mul (p : S.ι) : ∃ ε > 0, ∀ y : ℂ, y ≠ 0 → ‖y‖ < ε →
    (((p.1 : ℂ) * y) • 1 - S.Mp p) * S.hatE p y = ((p.1 : ℂ) * y - S.ψp p) • 1 := by
  obtain ⟨ε, hε, hsum⟩ := S.summable_etaM p
  refine ⟨ε, hε, fun y hy0 hy => ?_⟩
  set η := S.etaM p
  set M := S.Mp p
  have hs : Summable (fun m : ℤ => y ^ m • η m) := (hsum y hy0 hy).of_norm
  -- the shifted series
  have hs1 : Summable (fun m : ℤ => y ^ m • ((p.1 : ℂ) • η (m - 1))) := by
    have : (fun m : ℤ => y ^ m • ((p.1 : ℂ) • η (m - 1))) =
        (fun m : ℤ => ((p.1 : ℂ) * y) • (y ^ m • η m)) ∘ (Equiv.subRight (1 : ℤ)) := by
      funext m
      simp only [Function.comp_apply, Equiv.subRight_apply, smul_smul]
      congr 1
      rw [zpow_sub₀ hy0, zpow_one]; field_simp
    rw [this, (Equiv.subRight (1 : ℤ)).summable_iff]
    exact hs.const_smul _
  have hs2 : Summable (fun m : ℤ => y ^ m • (M * η m)) := by
    have : (fun m : ℤ => y ^ m • (M * η m)) = fun m => M * (y ^ m • η m) := by
      funext m; rw [mul_smul_comm]
    rw [this]; exact hs.mul_left M
  have hshift : ∑' m : ℤ, y ^ m • ((p.1 : ℂ) • η (m - 1)) =
      ((p.1 : ℂ) * y) • ∑' m : ℤ, y ^ m • η m := by
    have h := (Equiv.addRight (1 : ℤ)).tsum_eq (fun m : ℤ => y ^ m • ((p.1 : ℂ) • η (m - 1)))
    rw [← h]
    have : (fun m : ℤ => y ^ ((Equiv.addRight (1 : ℤ)) m) •
        ((p.1 : ℂ) • η ((Equiv.addRight (1 : ℤ)) m - 1))) =
        fun m : ℤ => ((p.1 : ℂ) * y) • (y ^ m • η m) := by
      funext m
      simp only [Equiv.coe_addRight, add_sub_cancel_right, smul_smul]
      congr 1
      rw [zpow_add₀ hy0, zpow_one]; ring
    rw [this, tsum_const_smul'']
  rw [hatE, ← hs.tsum_mul_left]
  have e1 : ∀ m : ℤ, (((p.1 : ℂ) * y) • 1 - M) * (y ^ m • η m) =
      ((p.1 : ℂ) * y) • (y ^ m • η m) - y ^ m • (M * η m) := by
    intro m; rw [sub_mul, smul_mul_assoc, one_mul, mul_smul_comm]
  simp_rw [e1]
  rw [Summable.tsum_sub (hs.const_smul _) hs2, tsum_const_smul'', ← hshift,
    ← Summable.tsum_sub hs1 hs2]
  have e2 : ∀ m : ℤ, y ^ m • ((p.1 : ℂ) • η (m - 1)) - y ^ m • (M * η m) =
      y ^ m • ((if m = 1 then (p.1 : ℂ) • 1 else 0) - (if m = 0 then S.ψp p • 1 else 0)) := by
    intro m; rw [← smul_sub, ← S.etaM_rec p m]
  simp_rw [e2]
  rw [tsum_eq_sum (s := {0, 1}) (fun m hm => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    rw [if_neg hm.2, if_neg hm.1, sub_zero, smul_zero])]
  rw [Finset.sum_pair (by norm_num)]
  simp only [if_neg (show (0 : ℤ) ≠ 1 by norm_num), zpow_zero, zpow_one,
    one_smul, zero_sub, if_neg (show (1 : ℤ) ≠ 0 by norm_num), sub_zero, if_true]
  module

/-! ## Transport to the commutative operator algebra -/

/-- A basis of the operator algebra. -/
def BA : Module.Basis (Fin (Module.finrank ℂ S.opAlg)) ℂ S.opAlg := Module.finBasis ℂ S.opAlg

/-- Coordinates of `Η_p(m)`. -/
def cco (p : S.ι) (j : Fin (Module.finrank ℂ S.opAlg)) (m : ℤ) : ℂ := S.BA.repr (S.etaA p m) j

theorem entry_le_norm (A : S.Mat) (a b : Fin (Module.finrank ℂ S.V)) : ‖A a b‖ ≤ ‖A‖ := by
  rw [Matrix.linfty_opNorm_def]
  have h1 : ‖A a b‖₊ ≤ ∑ k, ‖A a k‖₊ :=
    Finset.single_le_sum (f := fun k => ‖A a k‖₊) (fun _ _ => by positivity) (Finset.mem_univ b)
  have h2 : ∑ k, ‖A a k‖₊ ≤ (Finset.univ : Finset _).sup fun i => ∑ k, ‖A i k‖₊ :=
    Finset.le_sup (f := fun i => ∑ k, ‖A i k‖₊) (Finset.mem_univ a)
  exact_mod_cast h1.trans h2

theorem linear_bound (φ : S.Mat →ₗ[ℂ] ℂ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ A : S.Mat, ‖φ A‖ ≤ K * ‖A‖ := by
  classical
  refine ⟨∑ a, ∑ b, ‖φ (Matrix.single a b 1)‖, by positivity, fun A => ?_⟩
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  rw [map_sum]
  calc ‖∑ a, φ (∑ b, Matrix.single a b (A a b))‖
      ≤ ∑ a, ∑ b, ‖φ (Matrix.single a b 1)‖ * ‖A‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
        rw [map_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        have : Matrix.single a b (A a b) = A a b • Matrix.single a b (1 : ℂ) := by
          rw [Matrix.smul_single, smul_eq_mul, mul_one]
        rw [this, map_smul, smul_eq_mul, norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_left (S.entry_le_norm A a b) (norm_nonneg _)
    _ = (∑ a, ∑ b, ‖φ (Matrix.single a b 1)‖) * ‖A‖ := by
        rw [Finset.sum_mul]; simp_rw [Finset.sum_mul]

theorem coord_bound : ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ (X : S.opAlg) (j : Fin (Module.finrank ℂ S.opAlg)),
    ‖S.BA.repr X j‖ ≤ Kc * ‖S.ιm X‖ := by
  have hker : LinearMap.ker S.ιm.toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot.2 S.ιm_injective
  obtain ⟨Lft, hLft⟩ := LinearMap.exists_leftInverse_of_injective S.ιm.toLinearMap hker
  have hK : ∀ j, ∃ K : ℝ, 0 ≤ K ∧ ∀ A : S.Mat, ‖(S.BA.coord j).comp Lft A‖ ≤ K * ‖A‖ :=
    fun j => S.linear_bound _
  choose K hK0 hKb using hK
  refine ⟨∑ j, K j, Finset.sum_nonneg fun j _ => hK0 j, fun X j => ?_⟩
  have e : S.BA.repr X j = (S.BA.coord j).comp Lft (S.ιm X) := by
    simp only [LinearMap.coe_comp, Function.comp_apply, Module.Basis.coord_apply]
    congr 2
    have := congrArg (fun F => F X) hLft
    simpa using this.symm
  rw [e]
  calc ‖(S.BA.coord j).comp Lft (S.ιm X)‖ ≤ K j * ‖S.ιm X‖ := hKb j _
    _ ≤ (∑ j, K j) * ‖S.ιm X‖ := by
        gcongr
        exact Finset.single_le_sum (f := K) (fun j _ => hK0 j) (Finset.mem_univ j)

/-- The scalar Laurent series `C_{p,j}(y) = Σ_m c_{p,j}(m) yᵐ`. -/
def Cser (p : S.ι) (j : Fin (Module.finrank ℂ S.opAlg)) (y : ℂ) : ℂ :=
  ∑' m : ℤ, S.cco p j m * y ^ m

theorem summable_cco (p : S.ι) : ∃ ε > 0, ∀ y : ℂ, y ≠ 0 → ‖y‖ < ε →
    ∀ j, Summable (fun m : ℤ => ‖S.cco p j m * y ^ m‖) := by
  obtain ⟨ε, hε, hsum⟩ := S.summable_etaM p
  obtain ⟨Kc, hKc, hc⟩ := S.coord_bound
  refine ⟨ε, hε, fun y hy0 hy j => ?_⟩
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
    ((hsum y hy0 hy).mul_left Kc)
  rw [norm_mul, norm_smul, mul_comm]
  calc ‖y ^ m‖ * ‖S.cco p j m‖ ≤ ‖y ^ m‖ * (Kc * ‖S.etaM p m‖) :=
        mul_le_mul_of_nonneg_left (hc _ j) (norm_nonneg _)
    _ = Kc * (‖y ^ m‖ * ‖S.etaM p m‖) := by ring

/-- `Ẽ_p(y) = Σ_j C_{p,j}(y) B_j` in the operator algebra. -/
def tildeE (p : S.ι) (y : ℂ) : S.opAlg := ∑ j, S.Cser p j y • S.BA j

theorem ιm_tildeE (p : S.ι) : ∃ ε > 0, ∀ y : ℂ, y ≠ 0 → ‖y‖ < ε →
    S.ιm (S.tildeE p y) = S.hatE p y := by
  obtain ⟨ε, hε, hsum⟩ := S.summable_cco p
  refine ⟨ε, hε, fun y hy0 hy => ?_⟩
  rw [tildeE, map_sum, hatE]
  have hterm : ∀ j, S.ιm (S.Cser p j y • S.BA j) =
      ∑' m : ℤ, (S.cco p j m * y ^ m) • S.ιm (S.BA j) := by
    intro j
    rw [map_smul, Cser, Summable.tsum_smul_const ((hsum y hy0 hy j).of_norm)]
  simp_rw [hterm]
  rw [← Summable.tsum_finsetSum (fun j _ =>
    ((hsum y hy0 hy j).of_norm).smul_const _)]
  refine tsum_congr fun m => ?_
  rw [etaM]
  conv_rhs => rw [← S.BA.sum_repr (S.etaA p m)]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_smul, cco, mul_comm]

/-- **The expansion identity** `(p y − U_p) Ẽ_p(y) = p y − ψ(p)` in the operator algebra. -/
theorem tildeE_mul (p : S.ι) : ∃ ε > 0, ∀ y : ℂ, y ≠ 0 → ‖y‖ < ε →
    (((p.1 : ℂ) * y) • 1 - S.Ua p) * S.tildeE p y = ((p.1 : ℂ) * y - S.ψp p) • 1 := by
  obtain ⟨ε₁, hε₁, h₁⟩ := S.hatE_mul p
  obtain ⟨ε₂, hε₂, h₂⟩ := S.ιm_tildeE p
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun y hy0 hy => ?_⟩
  apply S.ιm_injective
  rw [map_mul, map_sub, map_smul, map_one, h₂ y hy0 (lt_of_lt_of_le hy (min_le_right _ _)),
    map_smul, map_one]
  exact h₁ y hy0 (lt_of_lt_of_le hy (min_le_left _ _))

/-! ## The expansion of the resolvent factor -/

/-- With `x = (p y)⁻¹`, `Ẽ_p(y) = (1 − ψ(p) x) (1 − x U_p)^{-1}`. -/
theorem tildeE_eq_inverse (p : S.ι) : ∃ ε > 0, ∀ y : ℂ, y ≠ 0 → ‖y‖ < ε →
    IsUnit (1 - ((p.1 : ℂ) * y)⁻¹ • S.Ua p) →
    S.tildeE p y = (1 - S.ψp p * ((p.1 : ℂ) * y)⁻¹) • Ring.inverse (1 - ((p.1 : ℂ) * y)⁻¹ • S.Ua p) := by
  obtain ⟨ε, hε, h⟩ := S.tildeE_mul p
  refine ⟨ε, hε, fun y hy0 hy hu => ?_⟩
  have hp0 : (p.1 : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (S.prime p).ne_zero
  have hpy : (p.1 : ℂ) * y ≠ 0 := mul_ne_zero hp0 hy0
  set x := ((p.1 : ℂ) * y)⁻¹
  have h1 := congrArg (fun A => x • A) (h y hy0 hy)
  simp only at h1
  have e1 : x • ((((p.1 : ℂ) * y) • 1 - S.Ua p) * S.tildeE p y) =
      (1 - x • S.Ua p) * S.tildeE p y := by
    rw [← smul_mul_assoc, smul_sub, smul_smul, inv_mul_cancel₀ hpy, one_smul]
  have e2 : x • (((p.1 : ℂ) * y - S.ψp p) • (1 : S.opAlg)) = (1 - S.ψp p * x) • 1 := by
    rw [smul_smul]; congr 1; simp only [x]; field_simp
  rw [e1, e2] at h1
  calc S.tildeE p y = Ring.inverse (1 - x • S.Ua p) * ((1 - x • S.Ua p) * S.tildeE p y) := by
        rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]
    _ = (1 - S.ψp p * x) • Ring.inverse (1 - x • S.Ua p) := by
        rw [h1, mul_smul_comm, mul_one]

/-- `y_p(z) = p^{−2z}`. -/
def yv (p : S.ι) (z : ℂ) : ℂ := (p.1 : ℂ) ^ (-(2 * z))

theorem yv_ne_zero (p : S.ι) (z : ℂ) : S.yv p z ≠ 0 :=
  cpow_ne_zero_iff.2 (Or.inl (Nat.cast_ne_zero.2 (S.prime p).ne_zero))

theorem norm_yv (p : S.ι) (z : ℂ) : ‖S.yv p z‖ = (p.1 : ℝ) ^ (-(2 * z.re)) := by
  rw [yv, Complex.norm_natCast_cpow_of_pos (S.prime p).pos]
  congr 1; simp

theorem inv_p_yv (p : S.ι) (z : ℂ) :
    ((p.1 : ℂ) * S.yv p z)⁻¹ = (p.1 : ℂ) ^ (-(2 * (1 / 2 - z))) := by
  have hp0 : (p.1 : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (S.prime p).ne_zero
  rw [yv, show -(2 * (1 / 2 - z)) = 2 * z + (-1) by ring, cpow_add _ _ hp0, cpow_neg_one,
    mul_inv, cpow_neg, inv_inv, mul_comm]

/-- `y_p(z)` is eventually small. -/
theorem eventually_yv_lt (p : S.ι) {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, ∀ z : ℂ, X ≤ z.re → ‖S.yv p z‖ < ε := by
  have hp1 : (1 : ℝ) < p.1 := by exact_mod_cast (S.prime p).one_lt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ε⁻¹ hp1
  refine ⟨n, fun z hz => ?_⟩
  rw [norm_yv, Real.rpow_neg (by linarith), inv_lt_comm₀ (by positivity) hε]
  calc ε⁻¹ < (p.1 : ℝ) ^ n := hn
    _ = (p.1 : ℝ) ^ (n : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (p.1 : ℝ) ^ (2 * z.re) := Real.rpow_le_rpow_of_exponent_le hp1.le (by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith)

theorem prod_smul_comm {ι' : Type*} (s : Finset ι') (c : ι' → ℂ) (a : ι' → S.opAlg) :
    ∏ i ∈ s, c i • a i = (∏ i ∈ s, c i) • ∏ i ∈ s, a i := by
  simp_rw [Algebra.smul_def]
  rw [Finset.prod_mul_distrib, map_prod]

/-- **The resolvent factor is the product of the expansions.** For `Re z` large and
`1/2 − z` good, `F_g(1/2 − z) ∏_{p∣N} (1 − ψ(p) p^{2z−1}) = a_{∏_p Ẽ_p(p^{−2z}) g}(t)`. -/
theorem Fs_mul_prod_eq : ∃ X : ℝ, ∀ z : ℂ, X ≤ z.re → S.Good (1 / 2 - z) → ∀ g : S.V,
    S.Fs (1 / 2 - z) g * ∏ q ∈ S.N.primeFactors, (1 - S.ψ q * (q : ℂ) ^ (-(1 - 2 * z))) =
      S.coeffL S.t (((∏ p, S.tildeE p (S.yv p z) : S.opAlg) : Module.End ℂ S.V) g) := by
  classical
  have hE := fun p => S.tildeE_eq_inverse p
  choose ε hε hEq using hE
  have hX := fun p => S.eventually_yv_lt p (hε p)
  choose X hX using hX
  refine ⟨∑ p, |X p|, fun z hz hgood g => ?_⟩
  have hsmall : ∀ p, ‖S.yv p z‖ < ε p := fun p => hX p z (le_trans (le_trans (le_abs_self _)
    (Finset.single_le_sum (f := fun p => |X p|) (fun _ _ => abs_nonneg _) (Finset.mem_univ p)))
    hz)
  have hunit : ∀ p, IsUnit (1 - ((p.1 : ℂ) * S.yv p z)⁻¹ • S.Ua p) := by
    intro p; rw [S.inv_p_yv]; exact hgood p
  have hprod : ∏ p, S.tildeE p (S.yv p z) =
      (∏ p, (1 - S.ψp p * ((p.1 : ℂ) * S.yv p z)⁻¹)) • S.Rinv (1 / 2 - z) := by
    rw [Rinv, ← S.prod_smul_comm]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [hEq p (S.yv p z) (S.yv_ne_zero p z) (hsmall p) (hunit p), S.inv_p_yv]
  have hscalar : ∏ q ∈ S.N.primeFactors, (1 - S.ψ q * (q : ℂ) ^ (-(1 - 2 * z))) =
      ∏ p, (1 - S.ψp p * ((p.1 : ℂ) * S.yv p z)⁻¹) := by
    rw [← Finset.prod_coe_sort S.N.primeFactors]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [S.inv_p_yv, show -(2 * (1 / 2 - z)) = -(1 - 2 * z) by ring]
    rfl
  rw [hprod, hscalar, Subalgebra.coe_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, Fs,
    mul_comm]

/-! ## The Dirichlet series of the expansion -/

/-- A uniform shift `L₀ ≥ e_p` (nilpotency indices) and `L₀ ≥ N`. -/
def L0 : ℕ := ∑ p, (S.Dp p).e + S.N

theorem e_le_L0 (p : S.ι) : (S.Dp p).e ≤ S.L0 := by
  unfold L0
  have : (S.Dp p).e ≤ ∑ q, (S.Dp q).e :=
    Finset.single_le_sum (f := fun q => (S.Dp q).e) (fun _ _ => Nat.zero_le _) (Finset.mem_univ p)
  omega

theorem cco_eq_zero (p : S.ι) (j : Fin (Module.finrank ℂ S.opAlg)) {m : ℤ} (hm : m < -S.L0) :
    S.cco p j m = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = -((n : ℤ) + 1) := ⟨(-m - 1).toNat, by omega⟩
  have h : S.etaA p (-((n : ℤ) + 1)) = 0 := by
    apply Subtype.ext
    rw [coe_etaA]
    exact (S.Dp p).eta_neg_eq_zero (S.ψp p) p.1 (by have := S.e_le_L0 p; omega)
  unfold cco
  rw [h, LinearEquiv.map_zero]
  rfl

/-- `p^{2k} ↦ c_{p,j}(k − L₀)`. -/
def ccAF (p : S.ι) (j : Fin (Module.finrank ℂ S.opAlg)) : ArithmeticFunction ℂ :=
  sqPowAF p.1 (fun k => S.cco p j ((k : ℤ) - S.L0))

theorem Cser_eq_LSeries (p : S.ι) : ∃ ε > 0, ∀ y : ℂ, y ≠ 0 → ‖y‖ < ε →
    ∀ (j : Fin (Module.finrank ℂ S.opAlg)) (z : ℂ), y = (p.1 : ℂ) ^ (-(2 * z)) →
      LSeriesHasSum (S.ccAF p j) z (y ^ (S.L0 : ℤ) * S.Cser p j y) := by
  obtain ⟨ε, hε, hsum⟩ := S.summable_cco p
  refine ⟨ε, hε, fun y hy0 hy j z hyz => ?_⟩
  apply LSeriesHasSum_sqPowAF (S.prime p)
  rw [← hyz]
  have hinj : Function.Injective fun k : ℕ => (k : ℤ) - S.L0 := fun a b h => by
    have : (a : ℤ) = b := by linarith [h]
    exact_mod_cast this
  have hs : Summable (fun m : ℤ => S.cco p j m * y ^ m) := (hsum y hy0 hy j).of_norm
  have hsupp : Function.support (fun m : ℤ => S.cco p j m * y ^ m) ⊆
      Set.range fun k : ℕ => (k : ℤ) - S.L0 := by
    intro m hm
    by_contra hc
    apply hm
    have : m < -S.L0 := by
      by_contra h'
      exact hc ⟨(m + S.L0).toNat, by
        show (((m + S.L0).toNat : ℕ) : ℤ) - S.L0 = m
        omega⟩
    simp [S.cco_eq_zero p j this]
  have hC : HasSum (fun m : ℤ => S.cco p j m * y ^ m) (S.Cser p j y) := hs.hasSum
  have h1 : HasSum ((fun m : ℤ => S.cco p j m * y ^ m) ∘ fun k : ℕ => (k : ℤ) - S.L0)
      (S.Cser p j y) :=
    (hinj.hasSum_iff (f := fun m : ℤ => S.cco p j m * y ^ m) (fun m hm => by
      by_contra h; exact hm (hsupp h))).2 hC
  have h2 := h1.mul_left (y ^ (S.L0 : ℤ))
  refine h2.congr_fun fun k => ?_
  simp only [Function.comp_apply]
  have hyL : y ^ (S.L0 : ℤ) ≠ 0 := zpow_ne_zero _ hy0
  rw [zpow_sub₀ hy0, zpow_natCast, zpow_natCast]
  rw [zpow_natCast] at hyL
  field_simp

/-! ## The multi-prime expansion -/

/-- Index tuples. -/
abbrev Jt : Type := S.ι → Fin (Module.finrank ℂ S.opAlg)

/-- `w_J = a_{∏_p B_{J(p)} g}(t)`. -/
def wJ (g : S.V) (J : S.Jt) : ℂ := S.coeffL S.t (((∏ p, S.BA (J p) : S.opAlg) :
  Module.End ℂ S.V) g)

/-- `F_J = ∏_p ccAF p (J p)`. -/
def FJ (J : S.Jt) : ArithmeticFunction ℂ := ∏ p, S.ccAF p (J p)

/-- The coefficient function of the expansion. -/
def Hf (g : S.V) (n : ℕ) : ℂ := ∑ J : S.Jt, S.wJ g J * S.FJ J n

theorem coeffL_prod_sum (c : S.ι → Fin (Module.finrank ℂ S.opAlg) → ℂ) (g : S.V) :
    S.coeffL S.t (((∏ p, ∑ j, c p j • S.BA j : S.opAlg) : Module.End ℂ S.V) g) =
      ∑ J : S.Jt, (∏ p, c p (J p)) * S.wJ g J := by
  classical
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp_rw [S.prod_smul_comm]
  rw [AddSubmonoidClass.coe_finsetSum, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [Subalgebra.coe_smul, LinearMap.smul_apply, map_smul, smul_eq_mul]
  rfl

theorem coeffL_prod_tildeE (z : ℂ) (g : S.V) :
    S.coeffL S.t (((∏ p, S.tildeE p (S.yv p z) : S.opAlg) : Module.End ℂ S.V) g) =
      ∑ J : S.Jt, (∏ p, S.Cser p (J p) (S.yv p z)) * S.wJ g J :=
  S.coeffL_prod_sum (fun p j => S.Cser p j (S.yv p z)) g

theorem beta_eq_sum (g : S.V) (m : S.ι → ℤ) :
    S.beta g m = ∑ J : S.Jt, (∏ p, S.cco p (J p) (m p)) * S.wJ g J := by
  rw [beta, ← S.coeffL_prod_sum (fun p j => S.cco p j (m p)) g]
  congr 3
  refine Finset.prod_congr rfl fun p _ => ?_
  exact (S.BA.sum_repr (S.etaA p (m p))).symm

theorem ccAF_support (p : S.ι) (j : Fin (Module.finrank ℂ S.opAlg)) (n : ℕ)
    (h : S.ccAF p j n ≠ 0) : ∃ k, n = p.1 ^ k :=
  sqPowAF_support _ h

/-- `H(∏_p p^{2k_p}) = β_g(k − L₀)`. -/
theorem Hf_apply_pow (g : S.V) (k : S.ι → ℕ) :
    S.Hf g (∏ p, p.1 ^ (2 * k p)) = S.beta g (fun p => (k p : ℤ) - S.L0) := by
  classical
  rw [Hf, beta_eq_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [mul_comm]
  congr 1
  rw [FJ, prod_apply_prod_pow (fun p : S.ι => p.1) S.prime Subtype.val_injective Finset.univ
    (fun p => S.ccAF p (J p)) (fun p n h => S.ccAF_support p (J p) n h) (fun p => 2 * k p)]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [ccAF, sqPowAF_apply_pow (S.prime p)]

/-- **The expansion as a Dirichlet series.** For `Re z` large,
`a_{∏_p Ẽ_p(p^{−2z}) g}(t) = (∏_p p^{2 L₀ z}) · L(H_g, z)`. -/
theorem prod_tildeE_eq_LSeries : ∃ X : ℝ, ∀ z : ℂ, X ≤ z.re → ∀ g : S.V,
    LSeriesSummable (S.Hf g) z ∧
      S.coeffL S.t (((∏ p, S.tildeE p (S.yv p z) : S.opAlg) : Module.End ℂ S.V) g) =
        (∏ p, (S.yv p z) ^ (-(S.L0 : ℤ))) * LSeries (S.Hf g) z := by
  classical
  have hC := fun p => S.Cser_eq_LSeries p
  choose ε hε hCeq using hC
  have hX := fun p => S.eventually_yv_lt p (hε p)
  choose X hX using hX
  refine ⟨∑ p, |X p|, fun z hz g => ?_⟩
  have hsmall : ∀ p, ‖S.yv p z‖ < ε p := fun p => hX p z (le_trans (le_trans (le_abs_self _)
    (Finset.single_le_sum (f := fun p => |X p|) (fun _ _ => abs_nonneg _) (Finset.mem_univ p)))
    hz)
  have hpj : ∀ p j, LSeriesHasSum (S.ccAF p j) z (S.yv p z ^ (S.L0 : ℤ) * S.Cser p j (S.yv p z)) :=
    fun p j => hCeq p (S.yv p z) (S.yv_ne_zero p z) (hsmall p) j z rfl
  -- each factor
  have hCs : ∀ p j, S.Cser p j (S.yv p z) =
      S.yv p z ^ (-(S.L0 : ℤ)) * LSeries (S.ccAF p j) z := by
    intro p j
    rw [(hpj p j).LSeries_eq, ← mul_assoc, ← zpow_add₀ (S.yv_ne_zero p z), neg_add_cancel,
      zpow_zero, one_mul]
  have hFJ : ∀ J : S.Jt, LSeriesSummable (S.FJ J) z ∧
      LSeries (S.FJ J) z = ∏ p, LSeries (S.ccAF p (J p)) z :=
    fun J => LSeries_prod_AF Finset.univ (fun p => S.ccAF p (J p)) z
      (fun p _ => (hpj p (J p)).LSeriesSummable)
  have hHsum : LSeriesSummable (S.Hf g) z := by
    have : S.Hf g = ∑ J : S.Jt, (S.wJ g J • ⇑(S.FJ J)) := by
      funext n; simp [Hf, Finset.sum_apply]
    rw [this]
    exact LSeriesSummable.sum fun J _ => (hFJ J).1.smul _
  refine ⟨hHsum, ?_⟩
  rw [coeffL_prod_tildeE]
  have hL : LSeries (S.Hf g) z = ∑ J : S.Jt, S.wJ g J * LSeries (S.FJ J) z := by
    have : S.Hf g = ∑ J : S.Jt, (S.wJ g J • ⇑(S.FJ J)) := by
      funext n; simp [Hf, Finset.sum_apply]
    rw [this, LSeries_sum fun J _ => (hFJ J).1.smul _]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [LSeries_smul]
  rw [hL, Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [(hFJ J).2]
  simp_rw [hCs]
  rw [Finset.prod_mul_distrib]
  ring

end ClassSetup

end SSHecke

end VOA.Classification.COne
