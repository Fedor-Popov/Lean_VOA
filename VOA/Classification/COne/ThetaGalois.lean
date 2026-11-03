/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.GapsPaper

/-!
# The theta Galois law: reduction to the finite Weil representation (G3)

`ThetaGaloisLaw` (GR Prop. 3.8) is reduced here to a purely algebraic statement,
`WeilGaloisLaw`, about the Weil representation of `SL₂(ℤ)` on `ℂ^{ℤ/2N}` attached to the
rank-one lattice `√(2N) ℤ`, twisted by `η⁻¹`.

## The normalised family

`weilTheta N μ = Θ_{N,μ}(τ) = ∑_{n ≡ μ (2N)} q^{n²/(4N)}` (`= θ_{μ,2N,1/(4N)}`). Every
`θ_{n₀,r,t}` is one of these: `θ_{n₀,r,t} = Θ_{tr², 2trn₀}` (`rankOneTheta_eq_weilTheta`).
The vector `F_μ = Θ_{N,μ}/η` (`weilVec`) transforms with **no** automorphy factor:

* `F_μ(τ+1) = e(μ²/4N − 1/24) F_μ(τ)` (`weilVec_T`),
* `F_μ(−1/τ) = (2N)^{−1/2} ∑_{j mod 2N} e(jμ/2N) F_j(τ)` (`weilVec_S`).

## Main results

* `WeilWord N γ A`: `A` is the product of the matrices `weilS`, `weilT`, `weilTinv` along a word
  in `S, S⁻¹, T, T⁻¹` whose product in `SL₂(ℤ)` is `γ` (`S⁻¹` is sent to `weilS` too, as `S⁻¹` and `S`
  act identically on `ℍ`; classically `weilS² = (μ ↦ −μ)`, trivial on even vectors — not proved
  or used here).
* `exists_weilWord`: every `γ ∈ SL₂(ℤ)` has such an `A` (`SL₂(ℤ) = ⟨S, T⟩`).
* `weilWord_transform`: if `WeilWord N γ A` then `F_μ(γτ) = ∑_j A_{μj} F_j(τ)` on `ℍ`.
* `thetaGaloisLaw_of_weilGaloisLaw : WeilGaloisLaw → ThetaGaloisLaw`.

## What remains

`WeilGaloisLaw` is the finite statement: for `4N ∣ M`, `24 ∣ M`, `ℓ` prime to `M` and
`γ ≡ diag(ℓ, ℓ⁻¹) (mod M)`, every word matrix `A` of `γ` acts on even `2N`-periodic vectors as
`v ↦ (2N/ℓ) v(ℓ ·)`. This is the classical fact that the Weil representation `ρ_{√(2N)ℤ} ⊗ χ_η⁻¹`
factors through `SL₂(ℤ/M)` and is monomial on the diagonal torus with the Jacobi-symbol sign
(a quadratic Gauss-sum evaluation). It is **not** proved here. Checked numerically
(`scratchpad/weil_word_check.py`): 60 random `(N, M, ℓ, γ)` with `γ` decomposed into an `S,T` word
by the Euclidean algorithm, error `< 1e-8`.
-/

open Complex Finset

noncomputable section

namespace VOA.Classification.COne

/-! ## The normalised theta family `Θ_{N,μ}` -/

/-- `Θ_{N,μ}(τ) = ∑_{n ≡ μ (mod 2N)} q^{n²/(4N)} = θ_{μ,2N,1/(4N)}(τ)`. -/
def weilTheta (N : ℕ) (μ : ℤ) (τ : ℂ) : ℂ :=
  rankOneTheta μ ((2 * N : ℕ) : ℤ) (1 / (4 * (N : ℝ))) τ

/-- `θ_{n₀,r,t} = Θ_{tr², 2trn₀}` (termwise: `t (n₀ + r m)² = (2trn₀ + 2tr² m)² / (4tr²)`). -/
theorem rankOneTheta_eq_weilTheta (n₀ : ℤ) {r t : ℕ} (hr : 0 < r) (ht : 0 < t) (τ : ℂ) :
    rankOneTheta n₀ r t τ = weilTheta (t * r ^ 2) (2 * t * r * n₀) τ := by
  unfold weilTheta rankOneTheta
  refine tsum_congr fun m => ?_
  unfold rankOneThetaTerm
  have hr' : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hr.ne'
  have ht' : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.2 ht.ne'
  congr 1
  push_cast
  field_simp
  ring

/-- `Θ_{N,μ}` depends only on `μ mod 2N`. -/
theorem weilTheta_add (N : ℕ) (μ k : ℤ) (τ : ℂ) :
    weilTheta N (μ + 2 * N * k) τ = weilTheta N μ τ := by
  unfold weilTheta rankOneTheta
  conv_rhs => rw [← (Equiv.addRight k).tsum_eq]
  refine tsum_congr fun m => ?_
  unfold rankOneThetaTerm
  simp only [Equiv.coe_addRight]
  congr 3
  push_cast
  ring

theorem weilTheta_congr (N : ℕ) {μ ν : ℤ} (h : μ ≡ ν [ZMOD (2 * N : ℕ)]) (τ : ℂ) :
    weilTheta N μ τ = weilTheta N ν τ := by
  obtain ⟨k, hk⟩ := (Int.ModEq.dvd h.symm)
  have : μ = ν + 2 * N * k := by push_cast at hk; linarith
  rw [this, weilTheta_add]

/-- `Θ_{N,−μ} = Θ_{N,μ}`. -/
theorem weilTheta_neg (N : ℕ) (μ : ℤ) (τ : ℂ) : weilTheta N (-μ) τ = weilTheta N μ τ := by
  unfold weilTheta rankOneTheta
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun m => ?_
  unfold rankOneThetaTerm
  simp only [Equiv.neg_apply]
  congr 3
  push_cast
  ring

/-- `Θ_{N,μ}(τ + 1) = e(μ²/4N) Θ_{N,μ}(τ)`. -/
theorem weilTheta_T {N : ℕ} (hN : 0 < N) (μ : ℤ) (τ : ℂ) :
    weilTheta N μ (τ + 1) =
      cexp (2 * Real.pi * I * (μ : ℂ) ^ 2 / (4 * N)) * weilTheta N μ τ := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  unfold weilTheta
  rw [rankOneTheta_T_twisted μ ((2 * N : ℕ) : ℤ) (1 / (4 * (N : ℝ))) N μ
    (by push_cast; field_simp; ring) (by push_cast; field_simp; ring)]
  congr 2
  push_cast
  field_simp

/-! ## The vector `F_μ = Θ_{N,μ}/η` -/

/-- `F_μ = Θ_{N,μ}/η`. -/
def weilVec (N : ℕ) (μ : ℤ) (τ : ℂ) : ℂ := weilTheta N μ τ / ModularForm.eta τ

theorem weilVec_congr (N : ℕ) {μ ν : ℤ} (h : μ ≡ ν [ZMOD (2 * N : ℕ)]) (τ : ℂ) :
    weilVec N μ τ = weilVec N ν τ := by
  rw [weilVec, weilVec, weilTheta_congr N h]

/-- The `T`-eigenvalue `e(μ²/4N − 1/24)` of `F_μ`. -/
def weilPhase (N : ℕ) (μ : ℤ) : ℂ :=
  cexp (2 * Real.pi * I * (μ : ℂ) ^ 2 / (4 * N)) * cexp (-(2 * Real.pi * I / 24))

theorem weilPhase_ne_zero (N : ℕ) (μ : ℤ) : weilPhase N μ ≠ 0 :=
  mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)

theorem weilVec_T {N : ℕ} (hN : 0 < N) (μ : ℤ) (τ : ℂ) :
    weilVec N μ (τ + 1) = weilPhase N μ * weilVec N μ τ := by
  rw [weilVec, weilVec, weilTheta_T hN, eta_add_one, weilPhase]
  have h1 : cexp (2 * Real.pi * I / 24) * cexp (-(2 * Real.pi * I / 24)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  rw [Complex.exp_neg]
  have h2 : cexp (2 * Real.pi * I / 24) ≠ 0 := Complex.exp_ne_zero _
  rw [div_mul_eq_div_div, mul_div_assoc, mul_div_assoc]
  field_simp

/-- The `S`-matrix: `(2N)^{−1/2} e(jμ/2N)`. -/
def weilS (N : ℕ) : Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ := fun μ j =>
  ((Real.sqrt (2 * N))⁻¹ : ℝ) *
    cexp (2 * Real.pi * I * ((j : ℕ) : ℂ) * (((μ : ℕ) : ℤ) : ℂ) / ((2 * N : ℕ) : ℂ))

theorem weilVec_S {N : ℕ} (hN : 0 < N) (μ : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    weilVec N μ (-1 / τ) =
      ((Real.sqrt (2 * N))⁻¹ : ℝ) * ∑ j : Fin (2 * N),
        cexp (2 * Real.pi * I * ((j : ℕ) : ℂ) * (μ : ℂ) / ((2 * N : ℕ) : ℂ)) *
          weilVec N (j : ℕ) τ := by
  haveI : NeZero (2 * N) := ⟨by omega⟩
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have ht : (0 : ℝ) < 1 / (4 * (N : ℝ)) := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 hN
    positivity
  have h := theta_div_eta_S μ (2 * N) ht hτ
  have e1 : 2 * (1 / (4 * (N : ℝ))) * (((2 * N : ℕ) : ℝ)) ^ 2 = 2 * N := by
    push_cast; field_simp; ring
  have e2 : 1 / (4 * (1 / (4 * (N : ℝ))) * (((2 * N : ℕ) : ℝ)) ^ 2) = 1 / (4 * (N : ℝ)) := by
    push_cast; field_simp; ring
  rw [e1, e2] at h
  exact h

/-- The diagonal `T`-matrix. -/
def weilT (N : ℕ) : Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ :=
  Matrix.diagonal fun μ => weilPhase N ((μ : ℕ) : ℤ)

/-- The diagonal `T⁻¹`-matrix. -/
def weilTinv (N : ℕ) : Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ :=
  Matrix.diagonal fun μ => (weilPhase N ((μ : ℕ) : ℤ))⁻¹

/-! ## Words in `S, T` and their Weil matrices -/

/-- `WeilWord N γ A`: `A` is the product of Weil matrices along a word in `S^{±1}, T^{±1}` with
product `γ`. -/
inductive WeilWord (N : ℕ) :
    Matrix.SpecialLinearGroup (Fin 2) ℤ → Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ → Prop
  | one : WeilWord N 1 1
  | S {γ A} : WeilWord N γ A → WeilWord N (ModularGroup.S * γ) (weilS N * A)
  | Sinv {γ A} : WeilWord N γ A → WeilWord N (ModularGroup.S⁻¹ * γ) (weilS N * A)
  | T {γ A} : WeilWord N γ A → WeilWord N (ModularGroup.T * γ) (weilT N * A)
  | Tinv {γ A} : WeilWord N γ A → WeilWord N (ModularGroup.T⁻¹ * γ) (weilTinv N * A)

theorem WeilWord.mul {N : ℕ} {γ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    {A B : Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ} (h : WeilWord N γ A) (h' : WeilWord N δ B) :
    WeilWord N (γ * δ) (A * B) := by
  induction h with
  | one => simpa using h'
  | S _ ih => rw [mul_assoc, Matrix.mul_assoc]; exact WeilWord.S ih
  | Sinv _ ih => rw [mul_assoc, Matrix.mul_assoc]; exact WeilWord.Sinv ih
  | T _ ih => rw [mul_assoc, Matrix.mul_assoc]; exact WeilWord.T ih
  | Tinv _ ih => rw [mul_assoc, Matrix.mul_assoc]; exact WeilWord.Tinv ih

/-- Every `γ ∈ SL₂(ℤ)` has a Weil word matrix. -/
theorem exists_weilWord (N : ℕ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃ A, WeilWord N γ A := by
  have hγ : γ ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    rw [SpecialLinearGroup.SL2Z_generators]; exact Subgroup.mem_top γ
  induction hγ using Subgroup.closure_induction'' with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨_, by simpa using WeilWord.S (WeilWord.one (N := N))⟩
    · exact ⟨_, by simpa using WeilWord.T (WeilWord.one (N := N))⟩
  | inv_mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨_, by simpa using WeilWord.Sinv (WeilWord.one (N := N))⟩
    · exact ⟨_, by simpa using WeilWord.Tinv (WeilWord.one (N := N))⟩
  | one => exact ⟨1, WeilWord.one⟩
  | mul x y _ _ hx hy =>
    obtain ⟨A, hA⟩ := hx
    obtain ⟨B, hB⟩ := hy
    exact ⟨A * B, hA.mul hB⟩

/-- Composing a linear transformation law with a matrix. -/
theorem sum_matrix_comp {n : ℕ} (B A : Matrix (Fin n) (Fin n) ℂ) (G : Fin n → ℂ)
    (F : Fin n → ℂ) (hG : ∀ j, G j = ∑ k, A j k * F k) (μ : Fin n) :
    ∑ j, B μ j * G j = ∑ k, (B * A) μ k * F k := by
  simp_rw [hG, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sum_diagonal {n : ℕ} (d : Fin n → ℂ) (F : Fin n → ℂ) (μ : Fin n) :
    ∑ j, Matrix.diagonal d μ j * F j = d μ * F μ := by
  simp [Matrix.diagonal_apply]

/-- **The vector-valued transformation law**: `F_μ(γτ) = ∑_j A_{μj} F_j(τ)`. -/
theorem weilWord_transform {N : ℕ} (hN : 0 < N) {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    {A : Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ} (h : WeilWord N γ A) {τ : ℂ} (hτ : 0 < τ.im)
    (μ : Fin (2 * N)) :
    weilVec N (μ : ℕ) (mobius γ τ) = ∑ j, A μ j * weilVec N (j : ℕ) τ := by
  induction h generalizing μ with
  | one => simp [mobius_one, Matrix.one_apply]
  | @S γ A _ ih =>
    rw [mobius_mul _ _ hτ, mobius_S, weilVec_S hN _ (im_mobius_pos γ hτ), Finset.mul_sum,
      ← sum_matrix_comp _ _ _ _ ih]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [weilS]
    ring
  | @Sinv γ A _ ih =>
    rw [mobius_mul _ _ hτ, mobius_S_inv, weilVec_S hN _ (im_mobius_pos γ hτ), Finset.mul_sum,
      ← sum_matrix_comp _ _ _ _ ih]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [weilS]
    ring
  | @T γ A _ ih =>
    rw [mobius_mul _ _ hτ, mobius_T, Nat.cast_one, weilVec_T hN, weilT,
      ← sum_matrix_comp _ _ _ _ ih, sum_diagonal, ih]
  | @Tinv γ A _ ih =>
    have h1 : 0 < (mobius γ τ + (-1 : ℤ)).im := by simpa using im_mobius_pos γ hτ
    have h := weilVec_T hN ((μ : ℕ) : ℤ) (mobius γ τ + (-1 : ℤ))
    rw [show mobius γ τ + ((-1 : ℤ) : ℂ) + 1 = mobius γ τ by push_cast; ring] at h
    rw [mobius_mul _ _ hτ, mobius_T_inv, weilTinv, ← sum_matrix_comp _ _ _ _ ih, sum_diagonal,
      h, ← mul_assoc, inv_mul_cancel₀ (weilPhase_ne_zero _ _), one_mul]

/-! ## The finite residual and the reduction -/

/-- **The Weil Galois law** (finite, algebraic): for `4N ∣ M`, `24 ∣ M`, `ℓ` prime to `M`,
`γ ≡ diag(ℓ, ℓ⁻¹) (mod M)` and any Weil word matrix `A` of `γ`, `A` acts on even
`2N`-periodic vectors as `v ↦ (2N/ℓ) v(ℓ ·)`. -/
def WeilGaloisLaw : Prop :=
  ∀ (N M : ℕ), 0 < N → 4 * N ∣ M → 24 ∣ M →
    ∀ ℓ : ℕ, ℓ.Coprime M → ∀ ℓ' : ℤ, (ℓ : ℤ) * ℓ' ≡ 1 [ZMOD M] →
    ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      γ 0 0 ≡ ℓ [ZMOD M] → γ 1 1 ≡ ℓ' [ZMOD M] → γ 0 1 ≡ 0 [ZMOD M] → γ 1 0 ≡ 0 [ZMOD M] →
      ∀ A, WeilWord N γ A →
      ∀ v : ℤ → ℂ, (∀ x, v (x + 2 * N) = v x) → (∀ x, v (-x) = v x) →
      ∀ μ : Fin (2 * N), ∑ j, A μ j * v (j : ℕ) =
        (jacobiSym (2 * (N : ℤ)) ℓ : ℂ) * v (ℓ * (μ : ℕ))

/-- The representative in `Fin (2N)` of `μ mod 2N`. -/
def weilIdx {N : ℕ} (hN : 0 < N) (μ : ℤ) : Fin (2 * N) :=
  ⟨(μ % (2 * N : ℕ)).toNat, by
    have h1 : 0 ≤ μ % ((2 * N : ℕ) : ℤ) := Int.emod_nonneg _ (by omega)
    have h2 : μ % ((2 * N : ℕ) : ℤ) < (2 * N : ℕ) := Int.emod_lt_of_pos _ (by omega)
    omega⟩

theorem weilIdx_modEq {N : ℕ} (hN : 0 < N) (μ : ℤ) :
    (((weilIdx hN μ : ℕ)) : ℤ) ≡ μ [ZMOD (2 * N : ℕ)] := by
  have h1 : 0 ≤ μ % ((2 * N : ℕ) : ℤ) := Int.emod_nonneg _ (by omega)
  simp only [weilIdx, Int.toNat_of_nonneg h1]
  exact Int.mod_modEq _ _

/-- **G3 reduction**: the theta Galois law follows from the finite Weil Galois law. -/
theorem thetaGaloisLaw_of_weilGaloisLaw (hW : WeilGaloisLaw) : ThetaGaloisLaw := by
  intro n₀ r t M hr ht hdiv h24 ℓ hℓ ℓ' hℓ' γ h00 h11 h01 h10 τ hτ
  set N := t * r ^ 2 with hNdef
  have hN : 0 < N := by positivity
  have h4N : 4 * N ∣ M := by rw [hNdef, ← mul_assoc]; exact hdiv
  set μ : ℤ := 2 * t * r * n₀ with hμ
  obtain ⟨A, hA⟩ := exists_weilWord N γ
  set v : ℤ → ℂ := fun x => weilVec N x τ with hv
  have hper : ∀ x, v (x + 2 * N) = v x := fun x =>
    weilVec_congr N (Int.modEq_iff_dvd.2 ⟨-1, by push_cast; ring⟩) τ
  have hev : ∀ x, v (-x) = v x := fun x => by
    simp only [hv, weilVec, weilTheta_neg]
  have hR := hW N M hN h4N h24 ℓ hℓ ℓ' hℓ' γ h00 h11 h01 h10 A hA v hper hev (weilIdx hN μ)
  have hT := weilWord_transform hN hA hτ (weilIdx hN μ)
  have hγτ : 0 < (mobius γ τ).im := im_mobius_pos γ hτ
  -- the Galois law for `F`
  have hF : weilVec N μ (mobius γ τ) =
      (jacobiSym (2 * (N : ℤ)) ℓ : ℂ) * weilVec N (ℓ * μ) τ := by
    rw [← weilVec_congr N (weilIdx_modEq hN μ), hT, hR]
    congr 1
    exact weilVec_congr N ((weilIdx_modEq hN μ).mul_left _) τ
  -- the Jacobi symbol
  have hJ : jacobiSym (2 * (N : ℤ)) ℓ = jacobiSym (2 * (t : ℤ)) ℓ := by
    have hrℓ : (r : ℤ).gcd ℓ = 1 := by
      have hrM : r ∣ M := (Dvd.intro_left (4 * t * r) (by ring) : r ∣ 4 * t * r ^ 2).trans hdiv
      have hc : Nat.Coprime r ℓ := Nat.Coprime.coprime_dvd_left hrM hℓ.symm
      rw [Int.gcd_natCast_natCast]; exact hc
    rw [hNdef, show (2 * ((t * r ^ 2 : ℕ) : ℤ)) = 2 * t * (r : ℤ) ^ 2 by push_cast; ring,
      jacobiSym.mul_left, jacobiSym.sq_one' hrℓ, mul_one]
  have hη : ModularForm.eta τ ≠ 0 := ModularForm.eta_ne_zero hτ
  have hηγ : ModularForm.eta (mobius γ τ) ≠ 0 := ModularForm.eta_ne_zero hγτ
  rw [rankOneTheta_eq_weilTheta n₀ hr ht, rankOneTheta_eq_weilTheta _ hr ht, ← hJ]
  have e1 : weilTheta (t * r ^ 2) μ (mobius γ τ) = weilVec N μ (mobius γ τ) *
      ModularForm.eta (mobius γ τ) := by
    rw [weilVec]; field_simp; rfl
  have e2 : weilTheta (t * r ^ 2) (2 * t * r * (ℓ * n₀)) τ = weilVec N (ℓ * μ) τ *
      ModularForm.eta τ := by
    rw [weilVec, hμ, show (2 * (t : ℤ) * r * (ℓ * n₀)) = ℓ * (2 * t * r * n₀) by ring]
    field_simp; rfl
  rw [e1, e2, hF]
  ring

end VOA.Classification.COne
