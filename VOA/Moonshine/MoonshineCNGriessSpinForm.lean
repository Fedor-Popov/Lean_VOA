/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGriessFrameBlock
import VOA.Moonshine.TForm

/-!
# The invariant form of `T`, read in the spin model, is a multiple of the dot product

`T = TLeechT` carries the symmetric nondegenerate form `TForm` with the invariance law
`B_T(e_α t, t') = (−1)^{⟨α,α⟩/2} B_T(t, e_α t')` (`TForm_eT`).  Through the spin model
`Ψ = spinIso : ℂ^SpinIdx ≅ T` (`MoonshineCNGriessSpinModule`), in which `e_α` is the phased spin
matrix `spinOp(ᾱ)`, this file proves

  `B_T(Ψ v, Ψ w) = κ · (v ⬝ v)`,   `κ = spinFormScale ≠ 0`,

i.e. Axiom's standard form on the spin index (the `W`-block of `bform`) is, up to one scalar, the
invariant form of `V♮` on `T`.  This is the form half of the twisted Griess dictionary.

* `pair_coordOfRed_red` — in Axiom's coordinates `(a, δ)` of the class of `α`,
  `pair a δ = ⟨α,α⟩/2 mod 2` (the quadratic form `qL` of `Λ/2Λ`, `SpinLattice.qL_phi0`);
* `spinOp_transpose`, `spinOp_red_transpose` — `spinOp(ᾱ)ᵀ = (−1)^{⟨α,α⟩/2} spinOp(ᾱ)`
  (from `qmatR_transpose`), so the dot product obeys the same invariance law as `B_T`;
* `spinGram` — the Gram matrix of `(v, w) ↦ B_T(Ψ v, Ψ w)`; it commutes with every `spinOp(ᾱ)`
  (`spinOp_mul_spinGram`), hence with every matrix (`commute_spinGram`, the spin matrices span
  `End(ℂ^SpinIdx)`: `spinAlgHom_surjective`), hence is scalar (Schur);
* ⭐ `TForm_spinIso` and `spinFormScale_ne_zero`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.GriessDictionary

open VOA VOA.Moonshine VOA.IntegralLattice VOA.Moonshine.AutMonster VOA.Moonshine.TFormLeech
open VOA.Moonshine.Extraspecial (alg algBasis)
open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterGriess.Spin
open VOA.Moonshine.MonsterGriess.LeechMatch (leechEquiv)
open Matrix

/-! ## §1  The quadratic form of `Λ/2Λ` in Axiom's coordinates -/

/-- `phi0` of the Axiom coordinates of `ᾱ` is the class of `α`. -/
theorem phi0_coordOfRed_red (α : leech.carrier) :
    SpinLattice.phi0 (coordOfRed (red leech α)) = Submodule.Quotient.mk (leechEquiv α) := by
  apply axiomRed_injective
  rw [← latRedLin_apply, latRedLin_coordOfRed, axiomRed_mk, AddEquiv.symm_apply_apply]

/-- **The spin coordinates see half the norm**: for the Axiom coordinates `(a, δ)` of `ᾱ`,
`pair a δ = ⟨α,α⟩/2 mod 2`. -/
theorem pair_coordOfRed_red (α : leech.carrier) :
    pair (coordOfRed (red leech α)).1 (coordOfRed (red leech α)).2
      = ((leech.form α α / 2 : ℤ) : ZMod 2) := by
  rw [← SpinLattice.qL_phi0, Prod.mk.eta, phi0_coordOfRed_red, ← hInt_leechEquiv]
  exact codeQuadForm_mk MonsterGriess.Code.allOnes_mem_C SpinLattice.weight_mod_four'
    (leechEquiv α)

/-! ## §2  Transposes of the spin matrices -/

/-- `spinOp(p)ᵀ = (−1)^{pair(a,δ)} spinOp(p)`. -/
theorem spinOp_transpose (p : MonsterGriess.Code.C × Cocode) :
    (spinOp p)ᵀ = sgnR ℂ (pair p.1 p.2) • spinOp p := by
  have h := sgnR_smul_qmatR (R := ℂ) (pair p.1 p.2) 0 p.1 p.2
  rw [add_zero] at h
  rw [spinOp, transpose_smul, qmatR_transpose, zero_add, ← h, smul_comm]

/-- **The spin matrix of `ᾱ` is symmetric or antisymmetric with the sign of `B_T`**:
`spinOp(ᾱ)ᵀ = (−1)^{⟨α,α⟩/2} spinOp(ᾱ)`. -/
theorem spinOp_red_transpose (α : leech.carrier) :
    (spinOp (coordOfRed (red leech α)))ᵀ
      = (-1 : ℂ) ^ (leech.form α α / 2) • spinOp (coordOfRed (red leech α)) := by
  rw [spinOp_transpose, pair_coordOfRed_red, sgnR_eq_sgn, ← Extraspecial.neg_one_zpow_eq_sgn]

/-! ## §3  The pulled-back form and its Gram matrix -/

/-- `Ψ` as a `ℂ`-linear map on `ℂ^SpinIdx`. -/
noncomputable def spinIsoC : (SpinIdx → ℂ) →ₗ[ℂ] TLeechT where
  toFun v := spinIso v
  map_add' v w := spinIso.map_add v w
  map_smul' c v := spinIso_smul c v

theorem spinIsoC_apply (v : SpinIdx → ℂ) : spinIsoC v = spinIso v := rfl

theorem spinIsoC_surjective : Function.Surjective spinIsoC := fun t =>
  ⟨(spinIso.symm t : SpinIdx → ℂ), spinIso.apply_symm_apply t⟩

theorem spinIsoC_injective : Function.Injective spinIsoC := fun _ _ h => spinIso.injective h

/-- The invariant form of `T` pulled back to `ℂ^SpinIdx`: `(v, w) ↦ B_T(Ψ v, Ψ w)`. -/
noncomputable def spinPullForm : LinearMap.BilinForm ℂ (SpinIdx → ℂ) :=
  TForm.compl₁₂ spinIsoC spinIsoC

theorem spinPullForm_apply (v w : SpinIdx → ℂ) :
    spinPullForm v w = TForm (spinIso v) (spinIso w) := rfl

/-- The Gram matrix `G_{ij} = B_T(Ψ δᵢ, Ψ δⱼ)` of the pulled-back form. -/
noncomputable def spinGram : Matrix SpinIdx SpinIdx ℂ :=
  LinearMap.BilinForm.toMatrix' spinPullForm

theorem spinPullForm_eq (v w : SpinIdx → ℂ) : spinPullForm v w = v ⬝ᵥ spinGram *ᵥ w := by
  have h := congrArg (fun B : LinearMap.BilinForm ℂ (SpinIdx → ℂ) => B v w)
    (Matrix.toBilin'_toMatrix' spinPullForm)
  simp only at h
  rw [Matrix.toBilin'_apply'] at h
  exact h.symm

/-- The pulled-back form obeys the invariance law of `B_T`:
`B(spinOp(ᾱ) v, w) = (−1)^{⟨α,α⟩/2} B(v, spinOp(ᾱ) w)`. -/
theorem spinPullForm_spinOp (α : leech.carrier) (v w : SpinIdx → ℂ) :
    spinPullForm (spinOp (coordOfRed (red leech α)) *ᵥ v) w
      = (-1 : ℂ) ^ (leech.form α α / 2) * spinPullForm v (spinOp (coordOfRed (red leech α)) *ᵥ w) := by
  rw [spinPullForm_apply, spinPullForm_apply, spinIso_spinOp, spinIso_spinOp, TForm_eT]

/-- **The Gram matrix commutes with every spin matrix of the lattice.** -/
theorem spinOp_mul_spinGram (α : leech.carrier) :
    spinOp (coordOfRed (red leech α)) * spinGram = spinGram * spinOp (coordOfRed (red leech α)) := by
  set S := spinOp (coordOfRed (red leech α)) with hS
  set s : ℂ := (-1 : ℂ) ^ (leech.form α α / 2) with hsdef
  have hs : s ≠ 0 := zpow_ne_zero _ (by norm_num)
  have key : Sᵀ * spinGram = s • (spinGram * S) := by
    apply Matrix.toBilin'.injective
    refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
    have hL : (Matrix.toBilin' (Sᵀ * spinGram)) v w = spinPullForm (S *ᵥ v) w := by
      rw [Matrix.toBilin'_apply', ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose,
        spinPullForm_eq]
    have hR : (Matrix.toBilin' (s • (spinGram * S))) v w = s * spinPullForm v (S *ᵥ w) := by
      rw [Matrix.toBilin'_apply', smul_mulVec, dotProduct_smul, ← mulVec_mulVec,
        spinPullForm_eq, smul_eq_mul]
    rw [hL, hR]
    exact spinPullForm_spinOp α v w
  rw [hS, spinOp_red_transpose, ← hsdef, Matrix.smul_mul, ← hS] at key
  exact smul_right_injective _ hs key

/-- The spin representation, read as matrices. -/
noncomputable def spinMatLin : alg (cocMat leech) →ₗ[ℂ] Matrix SpinIdx SpinIdx ℂ :=
  (Matrix.toLinAlgEquiv' (R := ℂ) (n := SpinIdx)).symm.toLinearMap ∘ₗ spinAlgHom.toLinearMap

theorem spinMatLin_algBasis (x : Fin leech.bRank → ZMod 2) :
    spinMatLin (algBasis (cocMat leech) x) = spinOp (coordOfRed x) := by
  rw [spinMatLin, LinearMap.comp_apply, AlgHom.toLinearMap_apply, spinAlgHom_algBasis,
    AlgEquiv.toLinearMap_apply, AlgEquiv.symm_apply_apply]

theorem spinMatLin_surjective : Function.Surjective spinMatLin := fun Y => by
  obtain ⟨a, ha⟩ := spinAlgHom_surjective (Matrix.toLinAlgEquiv' Y)
  exact ⟨a, by rw [spinMatLin, LinearMap.comp_apply, AlgHom.toLinearMap_apply, ha,
    AlgEquiv.toLinearMap_apply, AlgEquiv.symm_apply_apply]⟩

/-- **Schur, first half**: the Gram matrix commutes with every matrix. -/
theorem commute_spinGram (Y : Matrix SpinIdx SpinIdx ℂ) : Y * spinGram = spinGram * Y := by
  have hext : (LinearMap.mulRight ℂ spinGram) ∘ₗ spinMatLin
      = (LinearMap.mulLeft ℂ spinGram) ∘ₗ spinMatLin := by
    refine (algBasis (cocMat leech)).ext fun x => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.mulRight_apply,
      LinearMap.mulLeft_apply, spinMatLin_algBasis]
    obtain ⟨α, rfl⟩ := red_surjective leech x
    exact spinOp_mul_spinGram α
  obtain ⟨a, rfl⟩ := spinMatLin_surjective Y
  exact congrArg (fun F : alg (cocMat leech) →ₗ[ℂ] Matrix SpinIdx SpinIdx ℂ => F a) hext

/-- The base point `(0, 0)` of the spin index. -/
def spinIdxBase : SpinIdx := ((0 : ZMod 2), (0 : C₀))

/-- **The scale `κ` of `B_T` against the dot product**: `κ = B_T(Ψ δ₀, Ψ δ₀)`. -/
noncomputable def spinFormScale : ℂ := spinGram spinIdxBase spinIdxBase

/-- **Schur, second half**: the Gram matrix is `κ · 1`. -/
theorem spinGram_eq_smul_one : spinGram = spinFormScale • (1 : Matrix SpinIdx SpinIdx ℂ) := by
  obtain ⟨κ, hκ⟩ := (mem_range_scalar_iff_commute_single' (M := spinGram)).mpr
    (fun i j => commute_spinGram _)
  have hκ' : spinGram = κ • (1 : Matrix SpinIdx SpinIdx ℂ) := by
    rw [← hκ, scalar_apply, smul_one_eq_diagonal]
  have h0 : spinFormScale = κ := by
    rw [spinFormScale, hκ', smul_apply, one_apply_eq, smul_eq_mul, mul_one]
  rw [h0]
  exact hκ'

/-- ⭐ **The invariant form of `T` in the spin model**: `B_T(Ψ v, Ψ w) = κ · (v ⬝ w)`. -/
theorem TForm_spinIso (v w : SpinIdx → ℂ) :
    TForm (spinIso v) (spinIso w) = spinFormScale * (v ⬝ᵥ w) := by
  rw [← spinPullForm_apply, spinPullForm_eq, spinGram_eq_smul_one, smul_mulVec, one_mulVec,
    dotProduct_smul, smul_eq_mul]

/-- `κ ≠ 0` (`B_T` is nondegenerate). -/
theorem spinFormScale_ne_zero : spinFormScale ≠ 0 := by
  intro h0
  have hv : spinIsoC (Pi.single spinIdxBase 1) ≠ 0 := by
    intro h
    have h1 := spinIsoC_injective (h.trans (map_zero spinIsoC).symm)
    have := congrFun h1 spinIdxBase
    simp at this
  apply hv
  refine TForm_nondegenerate.1 _ fun t' => ?_
  obtain ⟨w, rfl⟩ := spinIsoC_surjective t'
  rw [spinIsoC_apply, spinIsoC_apply, TForm_spinIso, h0, zero_mul]

end VOA.Moonshine.GriessDictionary
