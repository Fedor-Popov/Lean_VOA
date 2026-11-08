/-
Ported from AxiomMath/CFSG (Apache-2.0), https://github.com/AxiomMath/CFSG,
commit 69cb972f587a3ecc035e092253167ff2e303c962 (source toolchain Lean
v4.35.0-rc3 with the module system), files:
  CFSG/Monster/Spin/SignedPerm.lean
  CFSG/Monster/Spin/Defs.lean
  CFSG/Monster/Spin/Coords.lean
Original authors (from the `@misc{axiom-cfsg}` citation, "Lean formalization of the
classification of finite simple groups", 2026):
  Cureton, Dean and Ilin, Vasily and Mehta, Bhavik and Voss, Niels and Cabral, Rafael and
  Defant, Colin and Gregory, Erik and Hill, Aaron and Hong, Letong and Hu, Qinheping and Jamner,
  Dustin and Jiang, Albert and Jordan, Tadeusz and Kurghinyan, Andranik and Lau, Kenny and
  Laurent, Jonathan and Liang, David and Limperg, Jannis and Mahns, Simon and Nugent, Brian and
  Olson, Connor and Ono, Ken and Paul, Eric and Rajan, Dhruv and Ram, Karun and Ray, Charlie and
  Siu, Ho Chung and Swaminathan, Ashvin A. and Thorner, Jesse and Tsaplin, Aleksey and Wang,
  Chenkai.
Port to Lean 4.30.0 / Mathlib v4.30.0 for LeanVOA by Fedor K. Popov (with Claude).
Released under the Apache 2.0 license.  Modifications relative to the source are listed in the
"Port notes" section of the module docstring below.
-/
import VOA.Moonshine.MonsterGriess.CodeCocycle

/-!
# Axiom's Monster port: the product law of the spin matrices `qmatR`

The `4096 × 4096` signed permutation matrices `qmatR R s a δ` (`s : ZMod 2`, `a ∈ C`,
`δ ∈ Cocode`) on `SpinIdx = ZMod 2 × C₀` realise the extraspecial group `2^{1+24}`:

* `qmatR_mul` — `R(s,a,δ) R(t,b,ε) = R(s + t + pair b δ, a + b, δ + ε)`;
* `qmatR_zero` — `R(0,0,0) = 1`;
* `qmatR_transpose` — `R(s,a,δ)ᵀ = R(s + pair a δ, a, δ)`, and `R` is orthogonal
  (`qmatR_transpose_mul_self`, `qmatR_mul_transpose_self`);
* `single_vecMul_qmatR` — the row action on basis vectors.

## Port notes
* Namespace `CFSG.Monster.Spin` ↦ `VOA.Moonshine.MonsterGriess.Spin`; module-system syntax
  dropped; bodies verbatim.  `sgnR`, `spm`, `SpinIdx`, `shift`, `qPerm`, `qSign`, `qmatR` were
  already ported in `Spin.lean` and are used, not repeated.
* Omitted: the `Parker`/`Xmat`/`Dmat`/`Tmat` presentation, `qmatR_injective`, traces,
  `map_qmatR`.
-/

namespace VOA.Moonshine.MonsterGriess.Spin

open VOA.Moonshine.MonsterGriess.Code Matrix

private theorem two_eq_zero' : (2 : ZMod 2) = 0 := rfl

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

/-! ### From `CFSG/Monster/Spin/SignedPerm.lean` -/
theorem zmod2_add_self : ∀ c : ZMod 2, c + c = 0 := by decide

section SignedPermLaws

variable {R : Type*} [CommRing R]

@[simp] theorem sgnR_zero : sgnR R 0 = 1 := rfl

@[simp] theorem sgnR_one : sgnR R 1 = -1 := rfl

theorem sgnR_add (s t : ZMod 2) : sgnR R (s + t) = sgnR R s * sgnR R t := by
  rcases zmod2_cases s with rfl | rfl <;> rcases zmod2_cases t with rfl | rfl
  · simp
  · simp
  · simp
  · rw [zmod2_add_self, sgnR_zero, sgnR_one, neg_mul_neg, mul_one]

theorem sgnR_mul_self (t : ZMod 2) : sgnR R t * sgnR R t = 1 := by
  rw [← sgnR_add, zmod2_add_self, sgnR_zero]

variable {ι : Type*} [DecidableEq ι]

theorem spm_apply (σ : ι → ι) (ε : ι → ZMod 2) (i j : ι) :
    spm R σ ε i j = if j = σ i then sgnR R (ε i) else 0 := rfl

theorem spm_row (σ : ι → ι) (ε : ι → ZMod 2) (i : ι) :
    (spm R σ ε).row i = sgnR R (ε i) • Pi.single (σ i) 1 := by
  ext j
  simp only [row_apply, spm_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero]

theorem spm_id_zero : spm R (fun i : ι => i) (fun _ => 0) = 1 := by
  ext i j
  simp only [spm_apply, sgnR_zero, one_apply, eq_comm]

theorem spm_congr {σ σ' : ι → ι} {ε ε' : ι → ZMod 2} (hσ : ∀ i, σ i = σ' i)
    (hε : ∀ i, ε i = ε' i) : spm R σ ε = spm R σ' ε' := by
  rw [funext hσ, funext hε]

theorem spm_eq_one {σ : ι → ι} {ε : ι → ZMod 2} (hσ : ∀ i, σ i = i) (hε : ∀ i, ε i = 0) :
    spm R σ ε = 1 :=
  (spm_congr hσ hε).trans spm_id_zero

theorem sgnR_smul_spm (s : ZMod 2) (σ : ι → ι) (ε : ι → ZMod 2) :
    sgnR R s • spm R σ ε = spm R σ (fun i => s + ε i) := by
  ext i j
  simp only [smul_apply, spm_apply, smul_eq_mul, mul_ite, mul_zero, sgnR_add]

theorem spm_transpose_of_involutive {σ : ι → ι} (hσ : Function.Involutive σ)
    (ε : ι → ZMod 2) : (spm R σ ε)ᵀ = spm R σ (fun i => ε (σ i)) := by
  ext i j
  simp only [transpose_apply, spm_apply]
  by_cases h : j = σ i
  · subst h
    rw [if_pos (hσ i).symm, if_pos rfl]
  · rw [if_neg h, if_neg]
    rintro rfl
    exact h (hσ j).symm

variable [Fintype ι]

theorem single_vecMul_spm (σ : ι → ι) (ε : ι → ZMod 2) (i : ι) :
    Pi.single i 1 ᵥ* spm R σ ε = sgnR R (ε i) • Pi.single (σ i) 1 := by
  rw [single_one_vecMul, spm_row]

theorem spm_mul_apply (σ : ι → ι) (ε : ι → ZMod 2) (M : Matrix ι ι R) (i j : ι) :
    (spm R σ ε * M) i j = sgnR R (ε i) * M (σ i) j := by
  simp only [mul_apply, spm_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

theorem spm_mul_spm (σ τ : ι → ι) (ε φ : ι → ZMod 2) :
    spm R σ ε * spm R τ φ = spm R (τ ∘ σ) (fun i => ε i + φ (σ i)) := by
  ext i j
  rw [spm_mul_apply, spm_apply, spm_apply, sgnR_add, Function.comp_apply, mul_ite, mul_zero]

theorem spm_transpose_mul_self {σ : ι → ι} (hσ : Function.Involutive σ) (ε : ι → ZMod 2) :
    (spm R σ ε)ᵀ * spm R σ ε = 1 := by
  rw [spm_transpose_of_involutive hσ, spm_mul_spm]
  exact spm_eq_one (fun i => hσ i) (fun i => zmod2_add_self _)

theorem spm_mul_transpose_self {σ : ι → ι} (hσ : Function.Involutive σ) (ε : ι → ZMod 2) :
    spm R σ ε * (spm R σ ε)ᵀ = 1 := by
  rw [spm_transpose_of_involutive hσ, spm_mul_spm]
  refine spm_eq_one (fun i => hσ i) (fun i => ?_)
  simp only [hσ i, zmod2_add_self]

end SignedPermLaws

/-! ### From `CFSG/Monster/Spin/Pairing.lean` and `CFSG/Monster/Spin/Defs.lean` -/
theorem coe_π₀ (u : C) : (π₀ u : C) = u + μ₀ u • ΩC := rfl

@[simp] theorem π₀_coe (c : C₀) : π₀ (c : C) = c := by
  apply Subtype.ext
  rw [coe_π₀, μ₀_coe, zero_smul, add_zero]

theorem coe_shift (a : C) (c : C₀) : (shift a c : C) = c + a + μ₀ a • ΩC := by
  rw [shift, coe_π₀, map_add, μ₀_coe, zero_add]

theorem shift_add (a b : C) (c : C₀) : shift (a + b) c = shift b (shift a c) := by
  simp only [shift, map_add, π₀_coe, add_assoc]

@[simp] theorem shift_zero (c : C₀) : shift 0 c = c := by
  simp only [shift, add_zero, π₀_coe]

theorem shift_shift (a : C) (c : C₀) : shift a (shift a c) = c := by
  rw [← shift_add, add_self_C, shift_zero]

theorem pair_shift (a : C) (c : C₀) (δ : Cocode) :
    pair (shift a c) δ = pair c δ + pair a δ + μ₀ a * pair ΩC δ := by
  rw [coe_shift, pair_add_left, pair_add_left, pair_smul_left]

/-! ### From `CFSG/Monster/Spin/Coords.lean` -/
theorem add_self_cocode (δ : Cocode) : δ + δ = 0 := by
  rw [← two_smul (ZMod 2) δ, two_eq_zero', zero_smul]

theorem qPerm_involutive (a : C) (δ : Cocode) : Function.Involutive (qPerm a δ) := fun i => by
  simp only [qPerm, shift_shift, add_assoc, ← two_mul, two_eq_zero', zero_mul, add_zero]

variable {R : Type*} [CommRing R]

theorem qmatR_apply (s : ZMod 2) (a : C) (δ : Cocode) (i j : SpinIdx) :
    qmatR R s a δ i j = if j = qPerm a δ i then sgnR R (qSign s a δ i) else 0 := rfl

theorem single_vecMul_qmatR (s : ZMod 2) (a : C) (δ : Cocode) (i : SpinIdx) :
    Pi.single i 1 ᵥ* qmatR R s a δ = sgnR R (qSign s a δ i) • Pi.single (qPerm a δ i) 1 :=
  single_vecMul_spm _ _ _

/-- **The product law of the spin matrices**:
`R(s,a,δ) R(t,b,ε) = R(s + t + pair b δ, a + b, δ + ε)`. -/
theorem qmatR_mul (s t : ZMod 2) (a b : C) (δ ε : Cocode) :
    qmatR R s a δ * qmatR R t b ε = qmatR R (s + t + pair b δ) (a + b) (δ + ε) := by
  rw [qmatR, qmatR, qmatR, spm_mul_spm]
  refine spm_congr (fun i => ?_) (fun i => ?_)
  · simp only [Function.comp_apply, qPerm, shift_add, pair_add_right, add_assoc]
  · simp only [qSign, qPerm, shift_add, pair_shift, map_add]
    linear_combination (-pair b δ) * two_eq_zero'

theorem qmatR_zero : qmatR R 0 0 0 = 1 := by
  refine spm_eq_one (fun i => ?_) (fun i => ?_)
  · simp [qPerm]
  · simp [qSign]

theorem sgnR_smul_qmatR (t s : ZMod 2) (a : C) (δ : Cocode) :
    sgnR R t • qmatR R s a δ = qmatR R (t + s) a δ := by
  rw [qmatR, sgnR_smul_spm, qmatR]
  exact spm_congr (fun _ => rfl) (fun i => by simp only [qSign, add_assoc])

theorem qmatR_transpose (s : ZMod 2) (a : C) (δ : Cocode) :
    (qmatR R s a δ)ᵀ = qmatR R (s + pair a δ) a δ := by
  rw [qmatR, spm_transpose_of_involutive (qPerm_involutive a δ), qmatR]
  refine spm_congr (fun _ => rfl) (fun i => ?_)
  simp only [qSign, qPerm, shift_shift, pair_shift]
  linear_combination (-pair a δ) * two_eq_zero'

theorem qmatR_transpose_mul_self (s : ZMod 2) (a : C) (δ : Cocode) :
    (qmatR R s a δ)ᵀ * qmatR R s a δ = 1 :=
  spm_transpose_mul_self (qPerm_involutive a δ) _

theorem qmatR_mul_transpose_self (s : ZMod 2) (a : C) (δ : Cocode) :
    qmatR R s a δ * (qmatR R s a δ)ᵀ = 1 :=
  spm_mul_transpose_self (qPerm_involutive a δ) _

end VOA.Moonshine.MonsterGriess.Spin
