/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.KoszulResidualU
import VOA.Examples.KoszulResidualPoly

/-!
# The Weyl operators of the leading Koszul differential on the matter space

On the matter space `(A ⊗ B) ⊗ U` of the Lee–Yang BRST construction:

* `aLead hA q` — the `R`-raising component (for the interpreted layers `aDeg`) of the creation
  mode `J^a_{-j-1}` on `A` (`q = (a, j)`); `uLead q` — the same on `U`;
* `uDer q = PhiU⁻¹ ∘ ∂_q ∘ PhiU` — the partner derivation on `U`;
* `mLead hA q = aLead q ⊗ 1 ⊗ 1 + 1 ⊗ 1 ⊗ uLead q` and `mDer q = 1 ⊗ 1 ⊗ uDer q`.

Proved:

* `aLead_comm`, `uLead_comm`, `mLead_comm` — the leading creation operators commute (from the
  current algebra and the fact that a mode raises `R` by at most one);
* `PhiU_uLead` — `PhiU ∘ uLead q = x_q · PhiU`;
* `mDer_comm`, `mDer_mLead` — the Weyl relations `[D_q, D_{q'}] = 0`, `[D_q, u_{q'}] = δ_{qq'}`;
* `mL_add_injective` — for every finite set `s` of letters and `c ≥ 1`, the operator
  `L_s + c = Σ_{q ∈ s} u_q D_q + c` is injective on the whole matter space.

Everything is proved outright from `hA`.
-/

namespace VOA.KoszulResidual

open VOA.ConcreteHodge VOA.GradedUnitaryCohomology VOA.VertexOperatorAlgebra
open Sl2CosetConcrete AffineSl2GeneralRigidity AffineSl2BelowCritical AffineVOA AffineVOA.Inst
open VOA.LeeYangTransferAssembly MvPolynomial
open scoped TensorProduct

noncomputable section

/-! ### Components of a composition -/

section Generic

variable {ι : Type*} [AddCommGroup ι] [DecidableEq ι] {E : Type*} [AddCommGroup E] [Module ℂ E]
  {L : ι → Submodule ℂ E}

/-- **The component of a composition.** If `T`, `T'` shift the grading inside `S`, `S'` and
`e' + e` is reached from `S' + S` only through `e'`, the `(e' + e)`-component of `T ∘ T'` is the
composite of the components. -/
theorem compOp_comp_of_mem (hI : DirectSum.IsInternal L) (T T' : E →ₗ[ℂ] E) (e e' : ι)
    (S S' : ι → Prop) (hT : ShiftsInto L T S) (hT' : ShiftsInto L T' S')
    (huniq : ∀ δ δ', S δ → S' δ' → δ' + δ = e' + e → δ' = e')
    {i : ι} {x : E} (hx : x ∈ L i) :
    compOp hI T (· + e) (compOp hI T' (· + e') x) = iproj hI (i + e' + e) (T (T' x)) := by
  rw [compOp_of_mem hI T' _ hx, compOp_of_mem hI T _ (iproj_mem hI _ _)]
  have hTx := hT' i x hx
  -- the predicate is linear in `y`
  refine Submodule.iSup_induction _ (motive := fun y => iproj hI (i + e' + e) (T (iproj hI (i + e') y)) =
      iproj hI (i + e' + e) (T y)) hTx ?_ (by simp) (fun y y' h h' => by
        beta_reduce at h h' ⊢; rw [map_add, map_add, map_add, h, h', map_add, map_add]) |>.symm ▸ ?_
  · intro δ' y hy
    refine Submodule.iSup_induction _ (motive := fun y => iproj hI (i + e' + e) (T (iproj hI (i + e') y)) =
      iproj hI (i + e' + e) (T y)) hy ?_ (by simp) (fun y y' h h' => by
        beta_reduce at h h' ⊢; rw [map_add, map_add, map_add, h, h', map_add, map_add])
    intro hδ' z hz
    by_cases he : δ' = e'
    · subst he; rw [iproj_of_mem_same hI hz]
    · rw [iproj_of_mem_ne hI (fun h => he (add_left_cancel h)) hz, map_zero, map_zero]
      symm
      refine iproj_eq_zero_of_mem_iSup hI (fun j => ∃ δ, S δ ∧ j = i + δ' + δ) ?_ ?_
      · have h := hT (i + δ') z hz
        have hle : shiftTarget L S (i + δ') ≤
            ⨆ (j : ι) (_ : ∃ δ, S δ ∧ j = i + δ' + δ), L j :=
          iSup_le fun δ => iSup_le fun hδ => le_iSup_of_le (i + δ' + δ) (le_iSup_of_le ⟨δ, hδ, rfl⟩ le_rfl)
        exact hle h
      · rintro ⟨δ, hδ, hj⟩
        apply he
        refine huniq δ δ' hδ hδ' ?_
        have : i + (δ' + δ) = i + (e' + e) := by rw [← add_assoc, ← add_assoc]; exact hj.symm
        exact add_left_cancel this
  · rfl

end Generic

/-! ### Letters, shifts and modes -/

/-- The mode index `-j-1` of the letter `q = (a, j)`. -/
abbrev nq (q : LexLetter) : ℤ := -((ofLex q).2 : ℤ) - 1

/-- The shift of the interpreted index by the `R`-raising component of a creation mode. -/
abbrev eq (q : LexLetter) : (ℤ × ℤ) × ℂ := ((2, 0), ((letterWt q : ℕ) : ℂ))

theorem nq_neg (q : LexLetter) : nq q < 0 := by unfold nq; omega

theorem eN_nq (q : LexLetter) : eN (nq q) = 1 := by simp [eN, nq]; omega

theorem eN_neg_nq (q : LexLetter) : eN (-nq q) = 0 := by simp [eN, nq]; omega

theorem neg_nq_cast (q : LexLetter) : (((-nq q : ℤ)) : ℂ) = ((letterWt q : ℕ) : ℂ) := by
  simp only [nq, letterWt]; push_cast; ring

/-- The shifts of a creation mode: `R` by `0` or `1`, weight by `j + 1`. -/
theorem modePred_nq {q : LexLetter} {δ : (ℤ × ℤ) × ℂ} (h : modePred (nq q) δ) :
    ∃ d : ℤ, δ = ((2 * d, 0), ((letterWt q : ℕ) : ℂ)) ∧ 0 ≤ d ∧ d ≤ 1 := by
  obtain ⟨d, rfl, h1, h2⟩ := h
  rw [eN_nq] at h2
  rw [eN_neg_nq] at h1
  exact ⟨d, by rw [neg_nq_cast], by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- The shifts of an arbitrary mode raise `R` by at most one. -/
theorem modePred_le_one {n : ℤ} {δ : (ℤ × ℤ) × ℂ} (h : modePred n δ) :
    ∃ d : ℤ, δ.1 = (2 * d, 0) ∧ d ≤ 1 := by
  obtain ⟨d, rfl, -, h2⟩ := h
  refine ⟨d, rfl, le_trans h2 ?_⟩
  unfold eN; split_ifs <;> norm_num

theorem huniq_nq (q q' : LexLetter) :
    ∀ δ δ', modePred (nq q) δ → modePred (nq q') δ' → δ' + δ = eq q' + eq q → δ' = eq q' := by
  intro δ δ' h h' he
  obtain ⟨d, rfl, hd0, hd1⟩ := modePred_nq h
  obtain ⟨d', rfl, hd0', hd1'⟩ := modePred_nq h'
  have h1 := congrArg (fun x : (ℤ × ℤ) × ℂ => x.1.1) he
  simp only [Prod.fst_add, Prod.snd_add] at h1
  have : d' = 1 := by omega
  subst this
  simp

/-! ### The `A` factor -/

section AFactor

variable (hA : GradedUnitary affineForm affineRealStructure affineFlag)

include hA in
theorem aDeg_isInternal : DirectSum.IsInternal aDeg :=
  layerDeg_isInternal affineForm affineRealStructure affineFlag hA affineGramRefl

/-- **The leading part of a creation mode on `A`**: the `R`-raising component of
`J^a_{-j-1}` for the interpreted layers. -/
def aLead (q : LexLetter) : Module.End ℂ ASpace :=
  compOp (aDeg_isInternal hA) (aMode (ofLex q).1 (nq q)) (· + eq q)

/-- The `(e + e')`-component of a single mode vanishes: modes raise `R` by at most one. -/
theorem iproj_mode_eq_zero_A (c : Fin 3) (n : ℤ) (q q' : LexLetter) {i : (ℤ × ℤ) × ℂ}
    {x : ASpace} (hx : x ∈ aDeg i) :
    iproj (aDeg_isInternal hA) (i + eq q' + eq q) (aMode c n x) = 0 := by
  refine iproj_eq_zero_of_mem_iSup (aDeg_isInternal hA) (fun j => ∃ δ, modePred n δ ∧ j = i + δ)
    ?_ ?_
  · have h := aMode_shifts hA c n i x hx
    have hle : shiftTarget aDeg (modePred n) i ≤
        ⨆ (j : (ℤ × ℤ) × ℂ) (_ : ∃ δ, modePred n δ ∧ j = i + δ), aDeg j :=
      iSup_le fun δ => iSup_le fun hδ => le_iSup_of_le (i + δ) (le_iSup_of_le ⟨δ, hδ, rfl⟩ le_rfl)
    exact hle h
  · rintro ⟨δ, hδ, he⟩
    obtain ⟨d, hd, hd1⟩ := modePred_le_one hδ
    have h1 := congrArg (fun x : (ℤ × ℤ) × ℂ => x.1.1) he
    simp only [Prod.fst_add, hd] at h1
    omega

/-- **The leading creation operators on `A` commute.** -/
theorem aLead_comm (q q' : LexLetter) :
    aLead hA q ∘ₗ aLead hA q' = aLead hA q' ∘ₗ aLead hA q := by
  apply linearMap_ext_internal (aDeg_isInternal hA)
  intro i x hx
  simp only [LinearMap.coe_comp, Function.comp_apply, aLead]
  rw [compOp_comp_of_mem _ _ _ _ _ _ _ (aMode_shifts hA _ _) (aMode_shifts hA _ _)
      (huniq_nq q q') hx,
    compOp_comp_of_mem _ _ _ _ _ _ _ (aMode_shifts hA _ _) (aMode_shifts hA _ _)
      (huniq_nq q' q) hx]
  rw [show i + eq q + eq q' = i + eq q' + eq q by abel, ← sub_eq_zero, ← map_sub]
  have hc := LinearMap.congr_fun (aAction.current_comm (ofLex q).1 (ofLex q').1 (nq q) (nq q')) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply] at hc
  change aMode (ofLex q).1 (nq q) (aMode (ofLex q').1 (nq q') x) -
    aMode (ofLex q').1 (nq q') (aMode (ofLex q).1 (nq q) x) = _ at hc
  rw [hc, if_neg (by have := nq_neg q; have := nq_neg q'; omega), LinearMap.zero_apply, add_zero,
    map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [map_smul]
  change _ • iproj (aDeg_isInternal hA) _ (aMode c (nq q + nq q') x) = 0
  rw [iproj_mode_eq_zero_A hA c _ q q' hx, smul_zero]

theorem aLead_of_mem (q : LexLetter) {i : (ℤ × ℤ) × ℂ} {x : ASpace} (hx : x ∈ aDeg i) :
    aLead hA q x = iproj (aDeg_isInternal hA) (i + eq q) (aMode (ofLex q).1 (nq q) x) :=
  compOp_of_mem _ _ _ hx

theorem aLead_mem (q : LexLetter) {i : (ℤ × ℤ) × ℂ} {x : ASpace} (hx : x ∈ aDeg i) :
    aLead hA q x ∈ aDeg (i + eq q) :=
  compOp_mem _ _ (· + eq q) hx

end AFactor

/-! ### The `U` factor -/

/-- The leading part of a creation mode on `U`. -/
def uLead (q : LexLetter) : Module.End ℂ USpace :=
  compOp uDeg_isInternal (uMode (ofLex q).1 (nq q)) (· + eq q)

theorem layerIndex_add_eq (t : ℕ) (m : ℤ) (q : LexLetter) :
    layerIndex t m + eq q = layerIndex (t + 1) (m + letterWt q) := by
  simp only [layerIndex, eq, Prod.mk_add_mk]
  push_cast
  ring_nf

/-- **On `U`, the leading creation operator is multiplication by the variable.** -/
theorem PhiU_uLead (q : LexLetter) (x : USpace) : PhiU (uLead q x) = X q * PhiU x := by
  have key : PhiU.toLinearMap ∘ₗ uLead q = LinearMap.mulLeft ℂ (X q) ∘ₗ PhiU.toLinearMap := by
    apply linearMap_ext_internal uDeg_isInternal
    intro i y hy
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.mulLeft_apply]
    by_cases hi : ∃ t m, layerIndex t m = i
    · obtain ⟨t, m, rfl⟩ := hi
      rw [uLead, compOp_of_mem _ _ _ hy, layerIndex_add_eq]
      exact PhiU_uP_creation q hy
    · push Not at hi
      rw [uDeg_eq_bot_of hi, Submodule.mem_bot] at hy
      simp [hy]
  exact LinearMap.congr_fun key x

theorem uLead_eq (q : LexLetter) :
    uLead q = PhiU.symm.toLinearMap ∘ₗ LinearMap.mulLeft ℂ (X q) ∘ₗ PhiU.toLinearMap := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearMap.mulLeft_apply]
  rw [← PhiU_uLead, LinearEquiv.symm_apply_apply]

theorem uLead_comm (q q' : LexLetter) : uLead q ∘ₗ uLead q' = uLead q' ∘ₗ uLead q := by
  refine LinearMap.ext fun x => ?_
  apply PhiU.injective
  simp only [LinearMap.coe_comp, Function.comp_apply, PhiU_uLead]
  ring

/-- The partner derivation `∂_q` on `U`. -/
def uDer (q : LexLetter) : Module.End ℂ USpace :=
  PhiU.symm.toLinearMap ∘ₗ (pderiv q : Derivation ℂ (MvPolynomial LexLetter ℂ)
    (MvPolynomial LexLetter ℂ)).toLinearMap ∘ₗ PhiU.toLinearMap

theorem PhiU_uDer (q : LexLetter) (x : USpace) : PhiU (uDer q x) = pderiv q (PhiU x) := by
  simp [uDer]

theorem uDer_comm (q q' : LexLetter) : uDer q ∘ₗ uDer q' = uDer q' ∘ₗ uDer q := by
  refine LinearMap.ext fun x => ?_
  apply PhiU.injective
  simp only [LinearMap.coe_comp, Function.comp_apply, PhiU_uDer]
  exact pderiv_pderiv_comm q q' _

theorem uDer_uLead (q q' : LexLetter) (x : USpace) :
    uDer q (uLead q' x) = uLead q' (uDer q x) + if q = q' then x else 0 := by
  apply PhiU.injective
  rw [map_add, PhiU_uDer, PhiU_uLead, PhiU_uLead, PhiU_uDer, pderiv_X_mul']
  split_ifs <;> simp

/-- The partial-degree projection on `U`. -/
def uProj (s : Finset LexLetter) (d : ℕ) : Module.End ℂ USpace :=
  PhiU.symm.toLinearMap ∘ₗ sProj s d ∘ₗ PhiU.toLinearMap

theorem PhiU_uProj (s : Finset LexLetter) (d : ℕ) (x : USpace) :
    PhiU (uProj s d x) = sProj s d (PhiU x) := by
  simp [uProj]

/-- The partial Euler operator on `U`. -/
theorem uProj_euler (s : Finset LexLetter) (d : ℕ) (x : USpace) :
    uProj s d (∑ q ∈ s, uLead q (uDer q x)) = (d : ℂ) • uProj s d x := by
  apply PhiU.injective
  rw [PhiU_uProj, map_smul, PhiU_uProj, map_sum]
  simp only [PhiU_uLead, PhiU_uDer]
  have h := sProj_sEuler s d (PhiU x)
  simp only [sEuler, LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_comp,
    Function.comp_apply, Derivation.coeFn_coe, LinearMap.mulLeft_apply] at h
  exact h

theorem uProj_uDer (s : Finset LexLetter) {q : LexLetter} (hq : q ∈ s) (d : ℕ) (x : USpace) :
    uProj s d (uDer q x) = uDer q (uProj s (d + 1) x) := by
  apply PhiU.injective
  rw [PhiU_uProj, PhiU_uDer, PhiU_uDer, PhiU_uProj, sProj_pderiv s hq]

theorem exists_uProj_eq_zero (s : Finset LexLetter) (x : USpace) :
    ∃ D : ℕ, ∀ d, D < d → uProj s d x = 0 := by
  obtain ⟨D, hD⟩ := exists_sProj_eq_zero s (PhiU x)
  exact ⟨D, fun d hd => PhiU.injective (by rw [PhiU_uProj, hD d hd, map_zero])⟩

theorem sum_uProj (s : Finset LexLetter) (x : USpace) {D : ℕ}
    (hD : ∀ d, D < d → uProj s d x = 0) : ∑ d ∈ Finset.range (D + 1), uProj s d x = x := by
  apply PhiU.injective
  rw [map_sum]
  simp only [PhiU_uProj]
  ext μ
  rw [coeff_sum]
  simp only [coeff_sProj]
  rw [Finset.sum_ite_eq]
  split_ifs with hμ
  · rfl
  · rw [Finset.mem_range] at hμ
    have h0 := hD (sdeg s μ) (by omega)
    have := congrArg (fun y => coeff μ (PhiU y)) h0
    simp only [PhiU_uProj, coeff_sProj, if_pos rfl, map_zero, coeff_zero] at this
    exact this.symm

/-! ### Sums of operators -/

section Sums

variable {ι : Type*} {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem sum_comp' (s : Finset ι) (f : ι → Module.End ℂ M) (g : Module.End ℂ M) :
    (∑ i ∈ s, f i) ∘ₗ g = ∑ i ∈ s, f i ∘ₗ g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, LinearMap.add_comp, ih]

theorem comp_sum' (s : Finset ι) (f : ι → Module.End ℂ M) (g : Module.End ℂ M) :
    g ∘ₗ (∑ i ∈ s, f i) = ∑ i ∈ s, g ∘ₗ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, LinearMap.comp_add, ih]

theorem map_id_sum {N : Type*} [AddCommGroup N] [Module ℂ N] (s : Finset ι)
    (f : ι → Module.End ℂ M) :
    TensorProduct.map (LinearMap.id : N →ₗ[ℂ] N) (∑ i ∈ s, f i) =
      ∑ i ∈ s, TensorProduct.map LinearMap.id (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [TensorProduct.map_zero_right]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, TensorProduct.map_add_right, ih]

theorem eq_zero_of_smul_eq_zero {a : ℂ} (ha : a ≠ 0) {w : M} (h : a • w = 0) : w = 0 := by
  have := congrArg (fun y => a⁻¹ • y) h
  simp only [smul_smul, inv_mul_cancel₀ ha, one_smul, smul_zero] at this
  exact this

end Sums

/-! ### The matter operators -/

section MatterOps

variable (hA : GradedUnitary affineForm affineRealStructure affineFlag)

/-- The leading creation operator `u_q` on the matter space. -/
def mLead (q : LexLetter) : Module.End ℂ MatterSpace :=
  TensorProduct.map (TensorProduct.map (aLead hA q) LinearMap.id) LinearMap.id +
    TensorProduct.map LinearMap.id (uLead q)

/-- The partner derivation `D_q` on the matter space. -/
def mDer (q : LexLetter) : Module.End ℂ MatterSpace := TensorProduct.map LinearMap.id (uDer q)

theorem mLead_comm (q q' : LexLetter) : mLead hA q ∘ₗ mLead hA q' = mLead hA q' ∘ₗ mLead hA q := by
  simp only [mLead, LinearMap.comp_add, LinearMap.add_comp, ← TensorProduct.map_comp,
    LinearMap.id_comp, LinearMap.comp_id, aLead_comm hA q q', uLead_comm q q']
  abel

theorem mDer_comm (q q' : LexLetter) : mDer q ∘ₗ mDer q' = mDer q' ∘ₗ mDer q := by
  simp only [mDer, ← TensorProduct.map_comp, LinearMap.id_comp, uDer_comm q q']

theorem uDer_comp_uLead (q q' : LexLetter) :
    uDer q ∘ₗ uLead q' = uLead q' ∘ₗ uDer q + if q = q' then LinearMap.id else 0 := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, uDer_uLead, LinearMap.add_apply, LinearMap.comp_apply]
  split_ifs <;> rfl

/-- **The Weyl relation** `D_q u_{q'} = u_{q'} D_q + δ_{q q'}`. -/
theorem mDer_mLead (q q' : LexLetter) :
    mDer q ∘ₗ mLead hA q' = mLead hA q' ∘ₗ mDer q + if q = q' then LinearMap.id else 0 := by
  simp only [mDer, mLead, LinearMap.comp_add, LinearMap.add_comp, ← TensorProduct.map_comp,
    LinearMap.id_comp, LinearMap.comp_id, uDer_comp_uLead]
  split_ifs
  · rw [TensorProduct.map_add_right, TensorProduct.map_id]; abel
  · rw [add_zero, add_zero]

/-- `L_s = Σ_{q ∈ s} u_q D_q`. -/
def mL (s : Finset LexLetter) : Module.End ℂ MatterSpace := ∑ q ∈ s, mLead hA q ∘ₗ mDer q

/-- The partial-degree projection on the matter space (acting on `U`). -/
def mProj (s : Finset LexLetter) (d : ℕ) : Module.End ℂ MatterSpace :=
  TensorProduct.map LinearMap.id (uProj s d)

theorem uProj_comp_euler (s : Finset LexLetter) (d : ℕ) :
    uProj s d ∘ₗ (∑ q ∈ s, uLead q ∘ₗ uDer q) = (d : ℂ) • uProj s d := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply]
  simp only [LinearMap.comp_apply]
  exact uProj_euler s d x

theorem uProj_comp_uDer (s : Finset LexLetter) {q : LexLetter} (hq : q ∈ s) (d : ℕ) :
    uProj s d ∘ₗ uDer q = uDer q ∘ₗ uProj s (d + 1) :=
  LinearMap.ext fun x => uProj_uDer s hq d x

/-- The `A`-part of `L_s`. -/
def mLA (s : Finset LexLetter) : Module.End ℂ MatterSpace :=
  ∑ q ∈ s, TensorProduct.map (TensorProduct.map (aLead hA q) LinearMap.id) (uDer q)

theorem mL_eq (s : Finset LexLetter) :
    mL hA s = mLA hA s + TensorProduct.map LinearMap.id (∑ q ∈ s, uLead q ∘ₗ uDer q) := by
  simp only [mL, mLA, mLead, mDer, LinearMap.add_comp, ← TensorProduct.map_comp,
    LinearMap.id_comp, LinearMap.comp_id, Finset.sum_add_distrib, map_id_sum]

theorem mProj_mL (s : Finset LexLetter) (d : ℕ) :
    mProj s d ∘ₗ mL hA s = (d : ℂ) • mProj s d + mLA hA s ∘ₗ mProj s (d + 1) := by
  rw [mL_eq, LinearMap.comp_add, mProj, ← TensorProduct.map_comp, LinearMap.id_comp,
    uProj_comp_euler, TensorProduct.map_smul_right, add_comm]
  congr 1
  rw [mLA, comp_sum', sum_comp']
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [mProj, ← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.id_comp,
    LinearMap.comp_id, uProj_comp_uDer s hq]

theorem exists_mProj_bound (s : Finset LexLetter) (v : MatterSpace) :
    ∃ D : ℕ, ∀ D', D ≤ D' → (∀ d, D' < d → mProj s d v = 0) ∧
      ∑ d ∈ Finset.range (D' + 1), mProj s d v = v := by
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨0, fun _ _ => ⟨fun _ _ => map_zero _, by simp⟩⟩
  | tmul x y =>
      obtain ⟨D, hD⟩ := exists_uProj_eq_zero s y
      refine ⟨D, fun D' hD' => ⟨fun d hd => ?_, ?_⟩⟩
      · rw [mProj, TensorProduct.map_tmul, hD d (by omega), TensorProduct.tmul_zero]
      · simp only [mProj, TensorProduct.map_tmul, LinearMap.id_apply, ← TensorProduct.tmul_sum]
        rw [sum_uProj s y (fun d hd => hD d (by omega))]
  | add v w hv hw =>
      obtain ⟨D1, h1⟩ := hv
      obtain ⟨D2, h2⟩ := hw
      refine ⟨max D1 D2, fun D' hD' => ⟨fun d hd => ?_, ?_⟩⟩
      · rw [map_add, (h1 D' (le_of_max_le_left hD')).1 d hd,
          (h2 D' (le_of_max_le_right hD')).1 d hd, add_zero]
      · simp only [map_add, Finset.sum_add_distrib]
        rw [(h1 D' (le_of_max_le_left hD')).2, (h2 D' (le_of_max_le_right hD')).2]

/-- **`L_s + c` is injective on the whole matter space, for every `c ≥ 1`.** -/
theorem mL_add_injective (s : Finset LexLetter) {c : ℕ} (hc : 1 ≤ c) {v : MatterSpace}
    (hv : mL hA s v + (c : ℂ) • v = 0) : v = 0 := by
  obtain ⟨D, hD⟩ := exists_mProj_bound s v
  have hstep : ∀ d, mProj s (d + 1) v = 0 → mProj s d v = 0 := by
    intro d hd
    have h := congrArg (mProj s d) hv
    rw [map_add, map_smul, map_zero] at h
    have h2 := LinearMap.congr_fun (mProj_mL hA s d) v
    rw [LinearMap.comp_apply] at h2
    rw [h2, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, hd, map_zero,
      add_zero, ← add_smul] at h
    have hne : ((d : ℂ) + (c : ℂ)) ≠ 0 := by
      have : (0 : ℝ) < (d : ℝ) + c := by positivity
      intro h0
      have h0' := congrArg Complex.re h0
      simp at h0'
      linarith
    exact eq_zero_of_smul_eq_zero hne h
  have hall : ∀ k d, D + 1 ≤ d + k → mProj s d v = 0 := by
    intro k
    induction k with
    | zero => intro d hd; exact (hD D le_rfl).1 d (by omega)
    | succ k ih =>
        intro d hd
        by_cases h : D + 1 ≤ d + k
        · exact ih d h
        · exact hstep d (ih (d + 1) (by omega))
  rw [← (hD D le_rfl).2]
  exact Finset.sum_eq_zero fun d _ => hall (D + 1) d (by omega)

end MatterOps

end

end VOA.KoszulResidual
