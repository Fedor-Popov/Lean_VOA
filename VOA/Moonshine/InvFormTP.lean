/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.InvFormTwisted
import VOA.Moonshine.InvFormClosure
import VOA.Moonshine.TForm
import VOA.Moonshine.TwistedPlus
import VOA.Moonshine.CyclicFrameSectors
import VOA.Examples.LatticeCharge
import VOA.Core.BilinearForm
import VOA.Moonshine.LatticeMorphRigid

/-!
# The invariant form on `TP = (V_Λ^T)^+`  (Moonshine step M8c, form part 4)

`TPForm := (fockForm 24 ⊗ TForm)|_{TP}` on the `V_Λ^+`-module
`plusModule : OrdVModule leechVOAPlus TP`.

* `TPForm_symm`.
* `TPForm_nondegenerate` — on every weight space: a nonzero `x ∈ TP_α` pairs nontrivially with
  some `y ∈ TP_α` (`α = k+2`, `TP_α = S[θ]_{2k+1} ⊗ T`, `exists_twGrading_of_mem_weight`).
* `TPForm_weightOrth` — distinct weight spaces are orthogonal.
* Twisted level (all fractional modes, on `S[θ] ⊗ T`): `leechTwForm_YM_echg`
  (`e^α`, sign `(−1)^{⟨α,α⟩/2}`) and `leechTwForm_YM_hgen` (`h_b(−1)𝟙`, sign `−1`) — the FHL
  formula for these primary generators of `V_Λ`.
* `L_one_latChargeGen` — `L₁ e^β = 0` in every lattice VOA (charge + weight argument).
* `TPForm_invariant_frameX0` / `TPForm_fhlInv_frameX0P` — FHL invariance at
  `u = e^β + e^{−β} ∈ V_Λ^+` for every `β ∈ Λ`.
* `interSub_TPForm` (unconditional) — the states of `V_Λ^+` at which `TPForm` is invariant form
  a vertex subalgebra containing every `e^β + e^{−β}`.
* `TPForm_fhlInv_of_generates` — full invariance for every homogeneous `u ∈ V_Λ^+`, **conditional
  on** `V_Λ^+` being generated as a vertex algebra by `{e^β + e^{−β}}` (hypothesis `hgen`).

## Status
All declarations proved; no `sorry`/axioms.  `TPForm`, symmetry, nondegeneracy, orthogonality and
invariance at the generators are unconditional.  Invariance for **all** of `V_Λ^+` is proved only
under the generation hypothesis `hgen`, which is open (not formalised; FLM/Dong–Griess-type
statement).  The oscillator invariance is at the twisted level only: `h_b(−1)𝟙 ∉ V_Λ^+`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.InvForm
open MvPolynomial VOA.TwistedHeisenberg VOA.Moonshine.LatticeTwisted TwistedReduction
open VOA.TwistedSector
open Module (End)
open scoped TensorProduct

section Cast

open IntegralLattice LatGen Extraspecial

variable (L : IntegralLattice.{0}) (hEven : L.Even) (hU : IsUnit (gramMat L).det)
  (hPos : L.PosDef)

/-- `e^α`-invariance, transported along `rank L = r`. -/
theorem cast_twForm_YM_echg {r : ℕ} (h : rank L = r)
    (BT : LinearMap.BilinForm ℂ (Rep (cocMat L) (isUnit_det_cocMat L hEven hU)))
    (hT : ∀ (α : L.carrier) t t', BT (eT L hEven hU α t) t'
      = (-1 : ℂ) ^ (L.form α α / 2) * BT t (eT L hEven hU α t'))
    (α : L.carrier) (k : ℤ) (x y : FockT r ⊗[ℂ] Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) :
    twForm r BT ((h ▸ latticeTwistedModule L hEven hU hPos :
        TwistedModule (thetaAut L hEven hPos) 2
          (FockT r ⊗[ℂ] Rep (cocMat L) (isUnit_det_cocMat L hEven hU))).YM (echg L α) k x) y
      = (-1 : ℂ) ^ (L.form α α / 2) * twForm r BT x
          ((h ▸ latticeTwistedModule L hEven hU hPos :
            TwistedModule (thetaAut L hEven hPos) 2
              (FockT r ⊗[ℂ] Rep (cocMat L) (isUnit_det_cocMat L hEven hU))).YM (echg L α)
            (2 * L.form α α - k - 4) y) := by
  subst h
  simp only [latticeTwistedModule_YM, YML_echg L hEven hU hPos]
  exact twForm_YTL L hEven hU BT hT α k x y

/-- Oscillator invariance, transported along `rank L = r`. -/
theorem cast_twForm_YM_hgen {r : ℕ} (h : rank L = r)
    (BT : LinearMap.BilinForm ℂ (Rep (cocMat L) (isUnit_det_cocMat L hEven hU)))
    (b : Fin (rank L)) (k : ℤ)
    (x y : FockT r ⊗[ℂ] Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) :
    twForm r BT ((h ▸ latticeTwistedModule L hEven hU hPos :
        TwistedModule (thetaAut L hEven hPos) 2
          (FockT r ⊗[ℂ] Rep (cocMat L) (isUnit_det_cocMat L hEven hU))).YM (hgen L b) k x) y
      = -twForm r BT x
          ((h ▸ latticeTwistedModule L hEven hU hPos :
            TwistedModule (thetaAut L hEven hPos) 2
              (FockT r ⊗[ℂ] Rep (cocMat L) (isUnit_det_cocMat L hEven hU))).YM (hgen L b)
            (-k) y) := by
  subst h
  simp only [latticeTwistedModule_YM, YML_hgen L hEven hU hPos]
  exact twForm_modeTT BT b k x y

end Cast

/-! ## `e^β` is quasi-primary: `L₁ e^β = 0` -/

section Primary

open IntegralLattice LatGen HeisenbergN

variable (L : IntegralLattice.{0})

/-- Below the charge-`β` threshold the `β`-coordinate vanishes. -/
theorem gradingLatGen_le_ker_coordEα {β : L.carrier} {k : ℤ} (hk : k < LatGen.halfNorm L β) :
    gradingLatGen L k ≤ LinearMap.ker (coordEα L β) := by
  refine iSup_le fun α => ?_
  by_cases hα : α = β
  · subst hα
    rw [bigradα_eq_bot_of_neg L α (by omega)]
    exact bot_le
  · rintro x ⟨p, -, rfl⟩
    rw [LinearMap.mem_ker, mkEα_apply, coordEα_apply, if_neg (Ne.symm hα)]

theorem eq_zero_of_mem_chargeSec_of_mem_grading {β : L.carrier} {k : ℤ}
    (hk : k < LatGen.halfNorm L β) {x : LatModuleGen L} (hx : x ∈ chargeSec L β)
    (hg : x ∈ gradingLatGen L k) : x = 0 := by
  obtain ⟨p, rfl⟩ := hx
  have h := gradingLatGen_le_ker_coordEα L hk hg
  rw [LinearMap.mem_ker, mkEα_apply, coordEα_apply, if_pos rfl] at h
  rw [h, map_zero]

/-- **`L₁ e^β = 0`** in any lattice VOA: `L₁ e^β` has charge `β` and weight `½⟨β,β⟩ − 1`. -/
theorem L_one_latChargeGen (hEven : L.Even) (hPos : L.PosDef) (β : L.carrier) :
    (latticeVOAGen L hEven hPos).L 1 (latChargeGen L β) = 0 := by
  refine eq_zero_of_mem_chargeSec_of_mem_grading L (β := β) (k := LatGen.halfNorm L β - 1)
    (by omega) ?_
    (VertexOperatorAlgebra.L_one_lower (latticeVOAGen L hEven hPos)
      (k := LatGen.halfNorm L β) (latChargeGen_mem_grading L β))
  have h := YfullGen_shiftsCharge L hEven hPos 0 (omegaLatGen_mem_chargeSec L) β (-(1 + 1) - 1)
    (latChargeGen L β) (mem_chargeSec L β _)
  rwa [zero_add] at h

end Primary

/-! ## The Leech twisted sector -/

open IntegralLattice LatGen Extraspecial TFormLeech

/-- The invariant form on the Leech twisted sector `S[θ] ⊗ T_Λ`. -/
noncomputable def leechTwForm : LinearMap.BilinForm ℂ Tw := twForm 24 TForm

theorem leechTwForm_symm (x y : Tw) : leechTwForm x y = leechTwForm y x :=
  twForm_symm TForm_symm x y

/-- `B(Y^T(e^α)₍k/2₎ x, y) = (−1)^{⟨α,α⟩/2} B(x, Y^T(e^α)₍(2⟨α,α⟩−k−4)/2₎ y)`. -/
theorem leechTwForm_YM_echg (α : leech.carrier) (k : ℤ) (x y : Tw) :
    leechTwForm (leechTwistedModule.YM (echg leech α) k x) y
      = (-1 : ℂ) ^ (leech.form α α / 2) *
          leechTwForm x (leechTwistedModule.YM (echg leech α) (2 * leech.form α α - k - 4) y) :=
  cast_twForm_YM_echg leech leech_even leech_isUnit_det_gramMat leech_posDef leech_rank TForm
    TForm_eT α k x y

/-- `B(h_b(k/2) x, y) = −B(x, h_b(−k/2) y)` on the Leech twisted sector. -/
theorem leechTwForm_YM_hgen (b : Fin (rank leech)) (k : ℤ) (x y : Tw) :
    leechTwForm (leechTwistedModule.YM (hgen leech b) k x) y
      = -leechTwForm x (leechTwistedModule.YM (hgen leech b) (-k) y) :=
  cast_twForm_YM_hgen leech leech_even leech_isUnit_det_gramMat leech_posDef leech_rank TForm b k
    x y


/-! ## The form on `TP = (V_Λ^T)^+` -/

/-- **The form on `TP`**: the restriction of `F ⊗ B_T`. -/
noncomputable def TPForm : LinearMap.BilinForm ℂ TP :=
  leechTwForm.compl₁₂ TP.subtype TP.subtype

@[simp] theorem TPForm_apply (x y : TP) : TPForm x y = leechTwForm (x : Tw) (y : Tw) := rfl

/-- **`TPForm` is symmetric.** -/
theorem TPForm_symm (x y : TP) : TPForm x y = TPForm y x := leechTwForm_symm _ _

/-- A nonzero weight space of `TP` is a doubled-odd graded piece `S[θ]_{2k+1} ⊗ T`, `α = k + 2`. -/
theorem exists_twGrading_of_mem_weight {α : ℂ} (hne : plusModule.weight α ≠ ⊥) :
    ∃ k : ℕ, α = (((k : ℤ) + 2 : ℤ) : ℂ) ∧
      ∀ x ∈ plusModule.weight α, (x : Tw) ∈ twGrading 24 leechT (2 * k + 1) := by
  obtain ⟨n, rfl, hn⟩ := plusModule_weight_ne_bot hne
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) + 2 := ⟨(n - 2).toNat, by omega⟩
  refine ⟨k, rfl, fun x hx => ?_⟩
  have hq : (((k : ℤ) + 2 : ℤ) : ℂ) = (((levelT 24 (2 * k + 1) : ℚ)) : ℂ) := by
    rw [levelT_24_odd]; push_cast; ring
  rw [hq] at hx
  have hmem : (x : Tw) ∈ twFixed 24 leechT ⊓ twWeight 24 leechT (levelT 24 (2 * k + 1)) := by
    rw [← map_plusModule_weight]
    exact Submodule.mem_map_of_mem hx
  rw [← twWeight_levelT]; exact hmem.2

/-- **`TPForm` is nondegenerate on every weight space** of the `V_Λ^+`-module `TP`. -/
theorem TPForm_nondegenerate (α : ℂ) (x : TP) (hx : x ∈ plusModule.weight α) (hx0 : x ≠ 0) :
    ∃ y ∈ plusModule.weight α, TPForm x y ≠ 0 := by
  have hne : plusModule.weight α ≠ ⊥ := fun h => hx0 (by rw [h] at hx; simpa using hx)
  obtain ⟨k, rfl, hk⟩ := exists_twGrading_of_mem_weight hne
  have hgr := hk x hx
  obtain ⟨m, t', hw, hne'⟩ := twForm_nondegenerate_twGrading TForm_nondegenerate hgr
    (fun h => hx0 (Subtype.ext h))
  have hq : (((k : ℤ) + 2 : ℤ) : ℂ) = (((levelT 24 (2 * k + 1) : ℚ)) : ℂ) := by
    rw [levelT_24_odd]; push_cast; ring
  have hfix : monomial m 1 ⊗ₜ t' ∈ twFixed 24 leechT ⊓ twWeight 24 leechT (levelT 24 (2 * k + 1)) :=
    ⟨twGrading_le_twFixed ⟨k, rfl⟩ hw, by rw [twWeight_levelT]; exact hw⟩
  rw [← map_plusModule_weight, ← hq] at hfix
  obtain ⟨y, hy, hyw⟩ := hfix
  refine ⟨y, hy, ?_⟩
  have hyw' : (y : Tw) = monomial m 1 ⊗ₜ t' := hyw
  rw [TPForm_apply, hyw']
  exact hne'

/-- **Distinct weight spaces of `TP` are `TPForm`-orthogonal.** -/
theorem TPForm_weightOrth : WeightOrth plusModule TPForm := by
  intro α β hαβ x hx y hy
  by_cases hα : plusModule.weight α = ⊥
  · rw [hα] at hx; rw [(Submodule.mem_bot ℂ).mp hx, map_zero, LinearMap.zero_apply]
  by_cases hβ : plusModule.weight β = ⊥
  · rw [hβ] at hy; rw [(Submodule.mem_bot ℂ).mp hy, map_zero]
  obtain ⟨k, rfl, hk⟩ := exists_twGrading_of_mem_weight hα
  obtain ⟨k', rfl, hk'⟩ := exists_twGrading_of_mem_weight hβ
  have hkk : 2 * k + 1 ≠ 2 * k' + 1 := by
    intro h; apply hαβ; rw [show k = k' by omega]
  exact twForm_orth_twGrading TForm hkk (hk x hx) (hk' y hy)

/-! ## Invariance on `TP` for the generators `e^β + e^{−β}` -/

theorem leechTwForm_YM_frameX0 (β : leech.carrier) (k : ℤ) (x y : Tw) :
    leechTwForm (leechTwistedModule.YM (frameX0 β) k x) y
      = (-1 : ℂ) ^ (leech.form β β / 2) *
          leechTwForm x (leechTwistedModule.YM (frameX0 β) (2 * leech.form β β - k - 4) y) := by
  have hf : leech.form (-β) (-β) = leech.form β β := by
    simp only [map_neg, LinearMap.neg_apply, neg_neg]
  rw [frameX0, map_add, Pi.add_apply, LinearMap.add_apply, map_add, LinearMap.add_apply]
  rw [leechTwForm_YM_echg β k x y, leechTwForm_YM_echg (-β) k x y, hf]
  simp only [Pi.add_apply, LinearMap.add_apply, map_add, mul_add]

/-- **FHL invariance of `TPForm` for `u = e^β + e^{−β} ∈ V_Λ^+`** (a primary vector of weight
`N = ⟨β,β⟩/2`, so the contragredient field is `(−1)^N z^{−2N} Y(u, z⁻¹)`):
`B(u₍ₙ₎ x, y) = (−1)^N B(x, u₍2N−n−2₎ y)`. -/
theorem TPForm_invariant_frameX0 (β : leech.carrier) (n : ℤ) (x y : TP) :
    TPForm (mode (plusModule.YM (frameX0P β)) n x) y
      = (-1 : ℂ) ^ (leech.form β β / 2) *
          TPForm x (mode (plusModule.YM (frameX0P β)) (leech.form β β - n - 2) y) := by
  rw [TPForm_apply, TPForm_apply, mode_plusModule, mode_plusModule]
  rw [show 2 * (leech.form β β - n - 2) = 2 * leech.form β β - 2 * n - 4 by ring]
  exact leechTwForm_YM_frameX0 β (2 * n) x y


/-! ## FHL invariance in the library's form, and the generator reduction -/

theorem halfNorm_neg (β : leech.carrier) : LatGen.halfNorm leech (-β) = LatGen.halfNorm leech β := by
  simp only [LatGen.halfNorm, map_neg, LinearMap.neg_apply, neg_neg]

theorem frameX0P_mem_grading (β : leech.carrier) :
    frameX0P β ∈ leechVOAPlus.grading (LatGen.halfNorm leech β) := by
  change frameX0 β ∈ gradingLatGen leech (LatGen.halfNorm leech β)
  refine Submodule.add_mem _ (latChargeGen_mem_grading leech β) ?_
  have h := latChargeGen_mem_grading leech (-β)
  rwa [halfNorm_neg] at h

theorem L_one_frameX0P (β : leech.carrier) : leechVOAPlus.L 1 (frameX0P β) = 0 := by
  apply Subtype.ext
  change leechVOA.L 1 (latChargeGen leech β + latChargeGen leech (-β)) = 0
  rw [map_add, leechVOA, L_one_latChargeGen, L_one_latChargeGen, add_zero]

/-- **FHL invariance of `TPForm` at the generators `e^β + e^{−β}`**, in the library's form
(`FHLInv`, the module analogue of `InvariantForm.IsFullyInvariant`). -/
theorem TPForm_fhlInv_frameX0P (β : leech.carrier) :
    FHLInv plusModule TPForm (LatGen.halfNorm leech β) (frameX0P β) := by
  intro n a b
  have h2 : 2 * LatGen.halfNorm leech β = leech.form β β := two_halfNorm leech leech_even β
  rw [Finset.sum_eq_single 0]
  · rw [TPForm_invariant_frameX0, pow_zero, Module.End.one_apply, Nat.factorial_zero,
      Nat.cast_one, inv_one, one_smul, Nat.cast_zero, sub_zero, smul_eq_mul, h2]
    rfl
  · intro j _ hj
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    rw [pow_succ, Module.End.mul_apply, L_one_frameX0P, map_zero, map_zero, mode_zero,
      LinearMap.zero_apply, map_zero, smul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-- **Unconditional closure statement**: the states `u ∈ V_Λ^+` whose action on `TP` is
`TPForm`-adjoint to the contragredient action form a vertex subalgebra (contains `𝟙`, closed under
every `n`-th product) containing every `e^β + e^{−β}`. -/
theorem interSub_TPForm :
    leechVOAPlus.vacuum ∈ interSub plusModule TPForm ∧
    (∀ u ∈ interSub plusModule TPForm, ∀ v ∈ interSub plusModule TPForm, ∀ n : ℤ,
      leechVOAPlus.smul u n v ∈ interSub plusModule TPForm) ∧
    ∀ β : leech.carrier, frameX0P β ∈ interSub plusModule TPForm :=
  ⟨vacuum_mem_interSub, fun _ hu _ hv n => smul_mem_interSub hu hv n,
    fun β => (fhlInv_iff TPForm_weightOrth (frameX0P_mem_grading β)).mp (TPForm_fhlInv_frameX0P β)⟩

/-- **Full FHL invariance of `TPForm`, conditional on generation**: if `V_Λ^+` is generated as
a vertex algebra by the states `e^β + e^{−β}` (`β ∈ Λ`), then `TPForm` is invariant for every
homogeneous `u ∈ V_Λ^+`. -/
theorem TPForm_fhlInv_of_generates
    (hgen : ∀ S : Submodule ℂ VPlus, leechVOAPlus.vacuum ∈ S →
      (∀ u ∈ S, ∀ v ∈ S, ∀ n : ℤ, leechVOAPlus.smul u n v ∈ S) →
      (∀ β : leech.carrier, frameX0P β ∈ S) → S = ⊤)
    {wt : ℤ} {u : VPlus} (hu : u ∈ leechVOAPlus.grading wt) :
    FHLInv plusModule TPForm wt u :=
  fhlInv_of_generates TPForm_weightOrth (Set.range frameX0P)
    (fun S h0 h1 hG => hgen S h0 h1 (fun β => hG ⟨β, rfl⟩))
    (by rintro _ ⟨β, rfl⟩; exact ⟨_, frameX0P_mem_grading β, TPForm_fhlInv_frameX0P β⟩) hu

end VOA.Moonshine.InvForm
