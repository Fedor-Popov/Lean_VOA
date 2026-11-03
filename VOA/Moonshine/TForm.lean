/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.TFormLattice

/-!
# The symmetric invariant form on the Leech `T`  (Moonshine step M8c)

**`TForm : LinearMap.BilinForm ℂ T`** on the `4096`-dimensional extraspecial module of the Leech
lattice, with

* `TForm_symm : TForm t t' = TForm t' t`,
* `TForm_nondegenerate : TForm.Nondegenerate`,
* `TForm_eT : TForm (e_α t) t' = (-1)^{⟨α,α⟩/2} · TForm t (e_α t')`,
* `TForm_eT_eT : TForm (e_α t) (e_α t') = (-1)^{⟨α,α⟩/2} ε(α,α) · TForm t t'`
  (`e_α` is orthogonal up to the sign `(-1)^{⟨α,α⟩/2} ε(α,α)`; recall `e_{-α} = e_α` on `T`),
* `TForm_iota : TForm (X t) t' = TForm t (ι X t')` for every `X ∈ End(T)`, with `ι` the
  anti-involution `e_α ↦ (-1)^{⟨α,α⟩/2} e_α` (`IntegralLattice.iotaL`).

All unconditional.  The construction is `IntegralLattice.exists_TForm` (`TFormLattice.lean`)
applied to explicit **Lagrangian data** `leechLagrangian` in the carrier `Λ ⊆ ℤ²⁴`
(`⟨x,y⟫ = x·y/8`, `Λ = 2A ∪ (u + 2A)`):

* `γ₀ = 8e₀`, `γᵢ = 4e₀ + 4eᵢ` (`1 ≤ i ≤ 11`): pairwise inner products even, `⟨γ,γ⟩/2 ∈ {2,4}`
  even, so their span is totally singular for `Q(α) = ⟨α,α⟩/2 mod 2`;
* partners `g₀ = u = (5,1,…,1)` (`⟨u,8e₀⟩ = 5`) and `gᵢ = 2 rᵢ` with `rᵢ` the `i`-th row of
  the Golay generator `[I₁₂ | B]` lifted to `{0,1}` (`⟨2rᵢ, γⱼ⟩ = δᵢⱼ` for `j ≥ 1`,
  `⟨2rᵢ, 8e₀⟩ = 0`).
The integer identities are closed by `decide +kernel` on explicit vectors (kernel-checked).

## Choice of sign (for M8c)
The sign `(-1)^{⟨α,α⟩/2}` is the one the contragredient vertex operator forces:
`Y(e^{zL₁}(-z^{-2})^{L₀} e^α, z^{-1})` contributes `(-1)^{L₀} e^α = (-1)^{⟨α,α⟩/2} e^α`, and on `T`
`e_{-α} = e_α`.  It is also the only basis-independent choice that is guaranteed symmetric
(see `TFormLattice.lean`); `TForm` is unique up to a scalar (Schur), which this file does not
formalise.  Any extra normalisation of the twisted operators (e.g. a sign `ε(α,-α)` in the
lattice-VOA form) changes the required law by the character `α ↦ (-1)^{⟨α,γ⟩}`, realised by
`TForm (e_γ ·) ·`; that adjustment is left to M8c proper.

## Status
All declarations proved, no `sorry`, kernel `decide` only; `#print axioms TForm_eT` (and
`TForm_symm`, `TForm_nondegenerate`) gives `[propext, Classical.choice, Quot.sound]`.
Imported by the umbrella `VOA/Moonshine.lean`.
-/

namespace VOA.Moonshine.TFormLeech

open VOA.IntegralLattice Module

/-! ### Explicit vectors in `ℤ²⁴` -/

/-- `γᵢ / 2`: `4e₀` for `i = 0`, `2e₀ + 2eᵢ` otherwise. -/
def aVec (i : Fin 12) : Fin 24 → ℤ := fun k =>
  if (i : ℕ) = 0 then (if (k : ℕ) = 0 then 4 else 0)
  else (if (k : ℕ) = 0 ∨ (k : ℕ) = i then 2 else 0)

/-- `γᵢ = 2 aᵢ`. -/
def gamVec (i : Fin 12) : Fin 24 → ℤ := fun k => 2 * aVec i k

/-- The `i`-th row of the Golay generator matrix `[I | B]`, lifted to `{0,1}`. -/
def rowVec (i : Fin 12) : Fin 24 → ℤ := fun k => ((Code.golayEnc (Pi.single i 1) k).val : ℤ)

/-- The partners: `u` for `i = 0`, `2 rᵢ` otherwise. -/
def gVec (i : Fin 12) : Fin 24 → ℤ := fun k =>
  if (i : ℕ) = 0 then Leech.uVec k else 2 * rowVec i k

theorem aVec_mod_two : ∀ i : Fin 12, ∀ k : Fin 24, ((aVec i k : ℤ) : ZMod 2) = 0 := by
  decide +kernel

theorem four_dvd_sum_aVec : ∀ i : Fin 12, (4 : ℤ) ∣ ∑ k, aVec i k := by decide +kernel

theorem four_dvd_sum_rowVec : ∀ i : Fin 12, (4 : ℤ) ∣ ∑ k, rowVec i k := by decide +kernel

theorem gam_gam_even : ∀ i j : Fin 12, (gamVec i ⬝ᵥ gamVec j) / 8 % 2 = 0 := by decide +kernel

theorem gam_halfNorm_even : ∀ i : Fin 12, (gamVec i ⬝ᵥ gamVec i) / 8 / 2 % 2 = 0 := by
  decide +kernel

theorem g_gam_even : ∀ i j : Fin 12, j < i → (gVec i ⬝ᵥ gamVec j) / 8 % 2 = 0 := by
  decide +kernel

theorem g_gam_odd : ∀ i : Fin 12, (gVec i ⬝ᵥ gamVec i) / 8 % 2 = 1 := by decide +kernel

/-! ### Membership in the Leech carrier -/

theorem gamVec_mem (i : Fin 12) : gamVec i ∈ Leech.carrier := by
  refine Or.inl (Leech.mem_subA2.2 ⟨aVec i, ⟨Leech.mem_preG.2 ?_, four_dvd_sum_aVec i⟩, ?_⟩)
  · have : reduceMod 2 24 (aVec i) = 0 := funext fun k => aVec_mod_two i k
    rw [this]; exact Submodule.zero_mem _
  · funext k; simp [gamVec]

theorem reduceMod_rowVec (i : Fin 12) :
    reduceMod 2 24 (rowVec i) = Code.golayEnc (Pi.single i 1) := by
  funext k
  change (((Code.golayEnc (Pi.single i 1) k).val : ℤ) : ZMod 2) = _
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem gVec_mem (i : Fin 12) : gVec i ∈ Leech.carrier := by
  by_cases hi : (i : ℕ) = 0
  · refine Or.inr ?_
    have : gVec i - Leech.uVec = 0 := by funext k; simp [gVec, hi]
    rw [this]; exact Submodule.zero_mem _
  · refine Or.inl (Leech.mem_subA2.2 ⟨rowVec i, ⟨Leech.mem_preG.2 ?_, four_dvd_sum_rowVec i⟩, ?_⟩)
    · rw [reduceMod_rowVec]; exact Code.golayEnc_mem _
    · funext k; simp [gVec, hi]

/-! ### The Lagrangian data -/

theorem leech_form_eq (x y : leech.carrier) :
    leech.form x y = ((show ↥Leech.carrier from x).val ⬝ᵥ (show ↥Leech.carrier from y).val) / 8 :=
  rfl

/-- `γᵢ ∈ Λ` (zero for `i ≥ 12`). -/
noncomputable def γL (i : ℕ) : leech.carrier :=
  if h : i < 12 then (⟨gamVec ⟨i, h⟩, gamVec_mem _⟩ : ↥Leech.carrier) else 0

/-- `gᵢ ∈ Λ` (zero for `i ≥ 12`). -/
noncomputable def gL (i : ℕ) : leech.carrier :=
  if h : i < 12 then (⟨gVec ⟨i, h⟩, gVec_mem _⟩ : ↥Leech.carrier) else 0

/-- **Lagrangian data for the Leech lattice.** -/
noncomputable def leechLagrangian : Lagrangian leech where
  m := 12
  γ := γL
  g := gL
  form_even i hi j hj := by
    rw [γL, γL, dif_pos hi, dif_pos hj, leech_form_eq, Int.even_iff]
    exact gam_gam_even ⟨i, hi⟩ ⟨j, hj⟩
  halfNorm_even i hi := by
    rw [halfNorm, γL, dif_pos hi, leech_form_eq, Int.even_iff]
    exact gam_halfNorm_even ⟨i, hi⟩
  partner_even i hi j hj := by
    rw [gL, γL, dif_pos hi, dif_pos (by omega : j < 12), leech_form_eq, Int.even_iff]
    exact g_gam_even ⟨i, hi⟩ ⟨j, by omega⟩ (by simpa [Fin.lt_def] using hj)
  partner_odd i hi := by
    rw [gL, γL, dif_pos hi, dif_pos hi, leech_form_eq, Int.odd_iff]
    exact g_gam_odd ⟨i, hi⟩
  two_mul_m := by rw [bRank_eq_rank, leech_rank]

/-! ### The form -/

/-- The Leech extraspecial module (as `Rep`, avoiding the slow `ExtraT` abbrev). -/
abbrev TL : Type :=
  Extraspecial.Rep (cocMat leech) (isUnit_det_cocMat leech leech_even leech_isUnit_det_gramMat)

theorem exists_leech :
    ∃ B : LinearMap.BilinForm ℂ TL, (∀ t t', B t t' = B t' t) ∧ B.Nondegenerate ∧
      ∀ X t t', B (X t) t' = B t (iotaL leech leech_even leech_isUnit_det_gramMat X t') :=
  exists_TForm leech_even leech_isUnit_det_gramMat leechLagrangian

/-- **The invariant symmetric form on the Leech `T`.** -/
noncomputable def TForm : LinearMap.BilinForm ℂ TL := exists_leech.choose

theorem TForm_symm (t t' : TL) : TForm t t' = TForm t' t := exists_leech.choose_spec.1 t t'

theorem TForm_nondegenerate : TForm.Nondegenerate := exists_leech.choose_spec.2.1

/-- `B(X t, t') = B(t, ι(X) t')` for `X ∈ End(T)`, `ι(e_α) = (-1)^{⟨α,α⟩/2} e_α`. -/
theorem TForm_iota (X : Module.End ℂ TL) (t t' : TL) :
    TForm (X t) t' = TForm t (iotaL leech leech_even leech_isUnit_det_gramMat X t') :=
  exists_leech.choose_spec.2.2 X t t'

/-- **Invariance law**: `B(e_α t, t') = (-1)^{⟨α,α⟩/2} B(t, e_α t')`. -/
theorem TForm_eT (α : leech.carrier) (t t' : TL) :
    TForm (eT leech leech_even leech_isUnit_det_gramMat α t) t'
      = (-1 : ℂ) ^ (leech.form α α / 2) *
        TForm t (eT leech leech_even leech_isUnit_det_gramMat α t') := by
  rw [TForm_iota, iotaL_eT, LinearMap.smul_apply, map_smul, smul_eq_mul]
  rfl

/-- `e_α` is orthogonal up to sign: `B(e_α t, e_α t') = (-1)^{⟨α,α⟩/2} ε(α,α) B(t, t')`. -/
theorem TForm_eT_eT (α : leech.carrier) (t t' : TL) :
    TForm (eT leech leech_even leech_isUnit_det_gramMat α t)
        (eT leech leech_even leech_isUnit_det_gramMat α t')
      = ((-1 : ℂ) ^ (leech.form α α / 2) * latticeCocycle leech α α) * TForm t t' := by
  rw [TForm_eT, ← Module.End.mul_apply, eT_mul_self', LinearMap.smul_apply, Module.End.one_apply,
    map_smul, smul_eq_mul, mul_assoc]

end VOA.Moonshine.TFormLeech
