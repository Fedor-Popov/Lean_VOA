/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HuangODEDual

/-!
# The contragredient of an irreducible module is irreducible (FHL Prop. 5.3.2)

For the library's unconditional contragredient `contragredientModule A` (`M' = ⨁_α (M_α)*`), we
prove the adjoint relation of FHL (5.2.4) in pairing form,

  `⟨u'₍ₙ₎φ, x⟩ = (−1)^{wt u} Σ_{j ≤ wt u} (1/j!) ⟨φ, (L₁ʲu)₍₂wt−n−2−j₎ x⟩`  (`dualPairing_dualModeEndo`),

for **all** `φ ∈ M'` and `x ∈ M` (not only homogeneous ones), and deduce FHL Prop. 5.3.2:

* the annihilator `S^⊥ ⊆ M` of a submodule `S ⊆ M'` is a submodule (`perp_mode_mem`: strong
  induction on `wt u`; the `j = 0` term of the adjoint relation is `⟨φ, u₍ₖ₎x⟩`, the others have
  lower weight);
* submodules of `M'` are graded (`lof_component_mem`, eigenvalue isolation for `L₀`);
* `S^⊥ = M ⟹ S = 0` (non-degeneracy) and `S^⊥ = 0 ⟹ S = M'` (finite-dimensional duality on each
  weight space): `contragredient_isIrreducible`.

Consequently the contragredient `C₂` input is a special case of the library's `ModuleC2Input`
(Abe–Buhl–Dong), and `huangODEInput_of_moduleC2Input'` : **`ModuleC2Input → HuangODEInput`**;
with V3d: `summable_prodTerm_of_moduleC2Input`, `summable_iterTerm_of_moduleC2Input`
(convergence of products and iterates, conditional on `ModuleC2Input` only).

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.HuangODEContra

open VOA VOA.Huang.Convergence VOA.Huang.HuangODEProduct VOA.Huang.HuangODEC1
  VOA.Huang.HuangODEDual VOA.Huang.FusionC2
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## The pairing `⟨φ, x⟩` -/

section Pairing

variable (A : OrdVModule W M)

/-- The `α`-component of a functional on `M'`. -/
noncomputable abbrev cmp (α : ℂ) : RestrictedDual A →ₗ[ℂ] Module.Dual ℂ (A.weight α) :=
  DirectSum.component ℂ ℂ (fun β => Module.Dual ℂ (A.weight β)) α

theorem dualPairing_add_x (x y : M) (φ : RestrictedDual A) :
    dualPairing A (x + y) φ = dualPairing A x φ + dualPairing A y φ := by
  induction φ using DirectSum.induction_on with
  | zero => erw [map_zero]; try simp
  | of β g =>
    rw [← DirectSum.lof_eq_of ℂ, dualPairing_lof, dualPairing_lof, dualPairing_lof, map_add,
      map_add]
  | add φ ψ hφ hψ => erw [map_add, map_add, map_add, hφ, hψ]; ring

theorem dualPairing_smul_x (c : ℂ) (x : M) (φ : RestrictedDual A) :
    dualPairing A (c • x) φ = c * dualPairing A x φ := by
  induction φ using DirectSum.induction_on with
  | zero => erw [map_zero]; try simp
  | of β g =>
    rw [← DirectSum.lof_eq_of ℂ, dualPairing_lof, dualPairing_lof, map_smul, map_smul,
      smul_eq_mul]
  | add φ ψ hφ hψ => erw [map_add, map_add, hφ, hψ]; ring

theorem dualPairing_zero_x (φ : RestrictedDual A) : dualPairing A 0 φ = 0 := by
  have h := dualPairing_smul_x A 0 0 φ
  rwa [zero_smul, zero_mul] at h

/-- On a homogeneous vector the pairing reads one component. -/
theorem dualPairing_of_mem {α : ℂ} {x : M} (hx : x ∈ A.weight α) (φ : RestrictedDual A) :
    dualPairing A x φ = cmp A α φ ⟨x, hx⟩ := by
  induction φ using DirectSum.induction_on with
  | zero => erw [map_zero]; try rfl
  | of β g =>
    rw [← DirectSum.lof_eq_of ℂ, dualPairing_lof]
    by_cases hβ : β = α
    · subst hβ
      erw [DirectSum.component.lof_self]
      congr 1
      exact internalProjTo_coe A.isInternal β ⟨x, hx⟩
    · rw [internalProjTo_eq_zero_of_ne A hx hβ, map_zero]
      erw [DirectSum.component.of, dif_neg hβ]
      rfl
  | add φ ψ hφ hψ => erw [map_add, map_add, hφ, hψ]; rfl

/-- Non-degeneracy: a functional pairing to zero with all of `M` vanishes. -/
theorem eq_zero_of_dualPairing {φ : RestrictedDual A} (h : ∀ x : M, dualPairing A x φ = 0) :
    φ = 0 := by
  refine DirectSum.ext_component ℂ fun α => ?_
  refine LinearMap.ext fun x => ?_
  have := h x
  rw [dualPairing_of_mem A x.2] at this
  erw [map_zero]
  exact this

/-- **The adjoint relation (FHL 5.2.4), pairing form, for all `φ` and `x`.** -/
theorem dualPairing_dualModeEndo {wt : ℤ} {u : 𝒱} (hu : u ∈ W.grading wt) (n : ℤ)
    (φ : RestrictedDual A) (x : M) :
    dualPairing A x (dualModeEndo A wt u n φ)
      = (-1 : ℂ) ^ wt * ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) *
          dualPairing A (mode (A.YM ((W.L 1 ^ j) u)) (2 * wt - n - 2 - (j : ℤ)) x) φ := by
  have hx : x ∈ ⨆ α : ℂ, A.weight α := by
    rw [A.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  induction hx using Submodule.iSup_induction' with
  | mem α x hx =>
    induction φ using DirectSum.induction_on with
    | zero =>
      erw [map_zero]
      symm
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun j _ => ?_)
      erw [map_zero, mul_zero]
    | of γ g =>
      rw [← DirectSum.lof_eq_of ℂ]
      by_cases hγ : α = dualOutIdx wt n γ
      · subst hγ
        rw [dualModeEndo_pairing_out A wt u n γ g hx, dualCompMap_apply, smul_eq_mul]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_eq_mul, dualPairing_lof]
      · rw [dualModeEndo_lof, dualPairing_lof, internalProjTo_eq_zero_of_ne A hx (Ne.symm hγ),
          map_zero]
        symm
        refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun j _ => ?_)
        rw [dualPairing_lof, internalProjTo_eq_zero_of_ne A (twistMode_mem_weight A hu hx n j)
          (by intro he; apply hγ; rw [he]; simp only [dualOutIdx]; ring), map_zero, mul_zero]
    | add φ ψ hφ hψ =>
      erw [map_add, map_add, hφ, hψ, ← mul_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      erw [map_add, mul_add]
  | zero => simp only [dualPairing_zero_x, map_zero, mul_zero, Finset.sum_const_zero]
  | add x y _ _ hx hy =>
    rw [dualPairing_add_x, hx, hy, ← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_add, dualPairing_add_x, mul_add]

end Pairing

/-! ## The annihilator of a submodule of `M'` is a submodule of `M` -/

section Perp

variable (A : OrdVModule W M)

/-- The annihilator `S^⊥ = {x | ∀ φ ∈ S, ⟨φ, x⟩ = 0}`. -/
def perp (S : Set (RestrictedDual A)) : Submodule ℂ M where
  carrier := {x | ∀ φ ∈ S, dualPairing A x φ = 0}
  add_mem' {x y} hx hy φ hφ := by rw [dualPairing_add_x, hx φ hφ, hy φ hφ, add_zero]
  zero_mem' φ _ := dualPairing_zero_x A φ
  smul_mem' c x hx φ hφ := by
    show dualPairing A (c • x) φ = 0
    rw [dualPairing_smul_x, hx φ hφ, mul_zero]

/-- The weight-`p` case of `perp_mode_mem`, by strong induction on `p`. -/
theorem perp_mode_mem_homog (S : WeakModule.Submodule' (contragredientModule A).toWeakModule) :
    ∀ (p : ℕ) {u : 𝒱}, u ∈ W.grading (p : ℤ) → ∀ (k : ℤ) {x : M}, x ∈ perp A S.carrier →
      ∀ φ ∈ S.carrier, dualPairing A (mode (A.YM u) k x) φ = 0 := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p IH =>
  intro u hu k x hx φ hφ
  have hrel := dualPairing_dualModeEndo A hu (2 * (p : ℤ) - k - 2) φ x
  have hS : dualModeEndo A (p : ℤ) u (2 * (p : ℤ) - k - 2) φ ∈ S.carrier := by
    have := S.act_mem u (2 * (p : ℤ) - k - 2) hφ
    rw [WeakModule.act_def] at this
    change mode (YMdual A u) _ φ ∈ S.carrier at this
    rwa [mode_YMdual_homogeneous A hu] at this
  rw [hx _ hS, Int.toNat_natCast, Finset.sum_range_succ', Finset.sum_eq_zero (fun j hj => by
      simp only [Finset.mem_range] at hj
      have hv := VertexOperatorAlgebra.L_one_pow_mem W hu (j + 1)
      have e : (p : ℤ) - ((j + 1 : ℕ) : ℤ) = ((p - (j + 1) : ℕ) : ℤ) := by
        rw [Nat.cast_sub (by omega)]
      rw [e] at hv
      rw [IH (p - (j + 1)) (by omega) hv _ hx φ hφ, mul_zero]), zero_add] at hrel
  simp only [pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, inv_one,
    one_mul, Nat.cast_zero, sub_zero] at hrel
  have e2 : 2 * (p : ℤ) - (2 * (p : ℤ) - k - 2) - 2 = k := by ring
  rw [e2] at hrel
  have hne : ((-1 : ℂ) ^ (p : ℤ)) ≠ 0 := zpow_ne_zero _ (by norm_num)
  exact (mul_eq_zero.mp hrel.symm).resolve_left hne

/-- **`S^⊥` is a submodule** (FHL Prop. 5.3.2, first half). -/
theorem perp_mode_mem (S : WeakModule.Submodule' (contragredientModule A).toWeakModule)
    (u : 𝒱) (k : ℤ) {x : M} (hx : x ∈ perp A S.carrier) :
    mode (A.YM u) k x ∈ perp A S.carrier := by
  refine induction_grading (W := W) (motive := fun u => mode (A.YM u) k x ∈ perp A S.carrier) u
    (by simp only [map_zero, mode_zero, LinearMap.zero_apply]; exact (perp A _).zero_mem)
    (fun a b ha hb => by
      simp only [map_add, mode_add, LinearMap.add_apply]; exact (perp A _).add_mem ha hb)
    (fun p a ha => ?_)
  rcases lt_or_ge p 0 with hp | hp
  · rw [W.positivity p hp, Submodule.mem_bot] at ha
    simp only [ha, map_zero, mode_zero, LinearMap.zero_apply]; exact (perp A _).zero_mem
  obtain ⟨P, rfl⟩ : ∃ P : ℕ, p = (P : ℤ) := ⟨p.toNat, by omega⟩
  exact fun φ hφ => perp_mode_mem_homog A S P ha k hx φ hφ

/-- The annihilator as a weak submodule of `M`. -/
def perpSub (S : WeakModule.Submodule' (contragredientModule A).toWeakModule) :
    WeakModule.Submodule' A.toWeakModule where
  carrier := perp A S.carrier
  act_mem u k _ hx := by rw [WeakModule.act_def]; exact perp_mode_mem A S u k hx

end Perp

/-! ## Submodules of `M'` are graded -/

section Graded

variable (A : OrdVModule W M)

theorem L0_lof (α : ℂ) (g : Module.Dual ℂ (A.weight α)) :
    mode ((contragredientModule A).YM W.conformalVector) 1
        (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (A.weight β)) α g)
      = α • DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (A.weight β)) α g :=
  (contragredientModule A).L0_weight α _ ⟨g, rfl⟩

theorem aeval_L0_mem (S : WeakModule.Submodule' (contragredientModule A).toWeakModule)
    {φ : RestrictedDual A} (hφ : φ ∈ S.carrier) (q : Polynomial ℂ) :
    Polynomial.aeval (mode ((contragredientModule A).YM W.conformalVector) 1) q φ
      ∈ S.carrier := by
  refine Polynomial.induction_on' q (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [map_add, LinearMap.add_apply]; exact S.carrier.add_mem hp hq
  · rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    refine S.carrier.smul_mem a ?_
    induction n with
    | zero => simpa using hφ
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      have := S.act_mem W.conformalVector 1 ih
      rwa [WeakModule.act_def] at this

/-- **Submodules of the contragredient are graded**: the `α`-component of an element of `S`
lies in `S` (eigenvalue isolation for `L₀`). -/
theorem lof_component_mem (S : WeakModule.Submodule' (contragredientModule A).toWeakModule)
    {φ : RestrictedDual A} (hφ : φ ∈ S.carrier) (α : ℂ) :
    DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (A.weight β)) α (cmp A α φ) ∈ S.carrier := by
  classical
  set L := mode ((contragredientModule A).YM W.conformalVector) 1
  set s := (DFinsupp.support φ).erase α
  have hsum : φ = ∑ β ∈ DFinsupp.support φ,
      DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (A.weight β)) β (cmp A β φ) := by
    conv_lhs => rw [← DirectSum.sum_support_of φ]
    rfl
  have hiso : ∀ (β : ℂ) (g : Module.Dual ℂ (A.weight β)),
      Polynomial.aeval L (∏ γ ∈ s, (Polynomial.X - Polynomial.C γ))
        (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (A.weight β)) β g)
      = (∏ γ ∈ s, (β - γ)) • DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (A.weight β)) β g := by
    intro β g
    rw [Module.End.aeval_apply_of_mem_apply_eq_smul (L0_lof A β g), Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    try rfl
  by_cases hα : α ∈ DFinsupp.support φ
  · have hmem := aeval_L0_mem A S hφ (∏ γ ∈ s, (Polynomial.X - Polynomial.C γ))
    rw [hsum] at hmem
    erw [map_sum] at hmem
    rw [Finset.sum_congr rfl (fun β _ => hiso β (cmp A β φ)),
      Finset.sum_eq_single α (fun β hβ hβα => by
        rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hβα, hβ⟩) (sub_self β)]
        exact zero_smul ℂ _)
        (fun h => absurd hα h)] at hmem
    have hc : (∏ γ ∈ s, (α - γ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun γ hγ => sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase hγ))
    have := S.carrier.smul_mem (∏ γ ∈ s, (α - γ))⁻¹ hmem
    erw [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    exact this
  · have h0 : cmp A α φ = 0 := DFinsupp.notMem_support_iff.mp hα
    rw [h0, map_zero]; exact S.carrier.zero_mem

end Graded

/-! ## Irreducibility -/

/-- **The contragredient of an irreducible lowest-weight module is irreducible**
(FHL Prop. 5.3.2). -/
theorem contragredient_isIrreducible (A : OrdVModule W M) {h : ℂ} (hreal : A.weight h ≠ ⊥)
    (hirr : A.IsIrreducible) : (contragredientModule A).IsIrreducible := by
  classical
  haveI : ∀ α, FiniteDimensional ℂ (A.weight α) := A.finrank
  refine ⟨?_, fun S => ?_⟩
  · -- nontrivial: a nonzero functional on the (nonzero) lowest weight space
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hreal
    obtain ⟨g, hg⟩ : ∃ g : Module.Dual ℂ (A.weight h), g ⟨x, hx⟩ ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have := (Module.forall_dual_apply_eq_zero_iff ℂ (⟨x, hx⟩ : A.weight h)).mp hcon
      exact hx0 (congrArg Subtype.val this)
    refine ⟨⟨DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (A.weight β)) h g, 0, fun h0 => ?_⟩⟩
    have := congrArg (cmp A h) h0
    erw [DirectSum.component.lof_self, map_zero] at this
    exact hg (by rw [this]; rfl)
  rcases hirr.2 (perpSub A S) with hbot | htop
  · -- `S^⊥ = 0`: then `S = M'`
    right
    rw [eq_top_iff]
    rintro φ -
    rw [← DirectSum.sum_support_of φ]
    refine S.carrier.sum_mem fun α _ => ?_
    rw [← DirectSum.lof_eq_of ℂ]
    change DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (A.weight β)) α (cmp A α φ) ∈ S.carrier
    set Sα : Submodule ℂ (Module.Dual ℂ (A.weight α)) :=
      S.carrier.comap (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (A.weight β)) α)
    have hco : Sα.dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Submodule.mem_dualCoannihilator] at hx
      have hperp : (x : M) ∈ perp A S.carrier := by
        intro ψ hψ
        rw [dualPairing_of_mem A x.2]
        exact hx _ (lof_component_mem A S hψ α)
      have : (x : M) ∈ (perpSub A S).carrier := hperp
      rw [hbot, Submodule.mem_bot] at this
      exact (Submodule.mem_bot ℂ).mpr (Subtype.ext this)
    have htop' : Sα = ⊤ := by
      rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Sα), hco,
        Submodule.dualAnnihilator_bot]
    have : cmp A α φ ∈ Sα := by rw [htop']; exact Submodule.mem_top
    exact this
  · -- `S^⊥ = M`: then `S = 0`
    left
    rw [eq_bot_iff]
    intro φ hφ
    rw [Submodule.mem_bot]
    refine eq_zero_of_dualPairing A fun x => ?_
    have : x ∈ (perpSub A S).carrier := by rw [htop]; exact Submodule.mem_top
    exact this φ hφ

/-- The contragredient of a lowest-weight module, bundled. -/
noncomputable def contraLW (P : LWModule W) : LWModule W where
  carrier := RestrictedDual P.isMod
  isMod := contragredientModule P.isMod
  h := P.h
  isLow := isLowestWeight_contragredientModule P.isMod P.isLow
  realized := by
    classical
    haveI : ∀ α, FiniteDimensional ℂ (P.isMod.weight α) := P.isMod.finrank
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.realized
    obtain ⟨g, hg⟩ : ∃ g : Module.Dual ℂ (P.isMod.weight P.h), g ⟨x, hx⟩ ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have := (Module.forall_dual_apply_eq_zero_iff ℂ (⟨x, hx⟩ : P.isMod.weight P.h)).mp hcon
      exact hx0 (congrArg Subtype.val this)
    intro hbot
    have hmem : DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (P.isMod.weight β)) P.h g
        ∈ (contragredientModule P.isMod).weight P.h := ⟨g, rfl⟩
    rw [hbot] at hmem
    erw [Submodule.mem_bot] at hmem
    have := congrArg (cmp P.isMod P.h) hmem
    erw [DirectSum.component.lof_self, map_zero] at this
    exact hg (by rw [this]; rfl)

theorem contraLW_isIrreducibleLW {P : LWModule W} (hP : P.IsIrreducibleLW) :
    (contraLW P).IsIrreducibleLW :=
  contragredient_isIrreducible P.isMod P.realized hP

/-- The contragredient `C₂` datum is a case of `ModuleC2Input`. -/
theorem contragredientC2Data_of_moduleC2Input (h2 : ModuleC2Input.{u}) (hV : StronglyRational W) :
    ContragredientC2Data W :=
  fun P hP => h2 𝒱 W hV (contraLW P) (contraLW_isIrreducibleLW hP)

/-- **`HuangODEInput` from `ModuleC2Input` alone** (Abe–Buhl–Dong: irreducible modules of a
`C₂`-cofinite VOA of CFT type are `C₂`-cofinite). -/
theorem huangODEInput_of_moduleC2Input' (h2 : ModuleC2Input.{u}) : HuangODEInput.{u} :=
  huangODEInput_of_C2Inputs h2 fun 𝒱 _ _ W hV => contragredientC2Data_of_moduleC2Input h2 hV

/-- **Products of intertwining operators among irreducible modules of a strongly rational
`V` converge** (absolutely, on each coset, in `|z₁| > |z₂| > 0`), conditional on `ModuleC2Input`
(Abe–Buhl–Dong) alone. -/
theorem summable_prodTerm_of_moduleC2Input (h2 : ModuleC2Input.{u}) (hV : StronglyRational W)
    {P₁ P₂ P₃ P₄ : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    {M₅ : Type u} [AddCommGroup M₅] [Module ℂ M₅] (A₅ : OrdVModule W M₅)
    {Y₁ : IntertwiningModes P₁.carrier M₅ P₄.carrier}
    {Y₂ : IntertwiningModes P₂.carrier P₃.carrier M₅}
    (hY₁ : IsIntertwiningOperator P₁.isMod A₅ P₄.isMod Y₁)
    (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod A₅ Y₂)
    {α₁ α₂ α₃ h₄ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
    {f : P₄.carrier →ₗ[ℂ] ℂ}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : VOA.Huang.MatrixCoeff.SupportedAt P₄.isMod f h₄)
    {ν₀ : ℂ} (hb : VOA.Huang.MatrixCoeff.IsBase Y₂ w₂ w₃ ν₀) {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0)
    (hz : ‖z₂‖ < ‖z₁‖) :
    Summable fun k : ℕ =>
      ‖VOA.Huang.MatrixCoeff.prodCoeff Y₁ Y₂ f w₁ w₂ w₃
          ((α₁ + α₂ + α₃ - h₄ - 2) - ν₀ + k) (ν₀ - k)
        * z₁ ^ (-((α₁ + α₂ + α₃ - h₄ - 2) - ν₀ + k) - 1) * z₂ ^ (-(ν₀ - k) - 1)‖ :=
  summable_prodTerm (huangODEInput_of_moduleC2Input' h2) hV i₁ i₂ i₃ i₄ A₅ hY₁ hY₂ h₁ h₂ h₃ hf hb
    hz₂ hz

/-- **Iterates converge** (on each coset, in `|z₂| > |z₀| > 0`), conditional on
`ModuleC2Input` alone. -/
theorem summable_iterTerm_of_moduleC2Input (h2 : ModuleC2Input.{u}) (hV : StronglyRational W)
    {P₁ P₂ P₃ P₄ : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    {M₅ : Type u} [AddCommGroup M₅] [Module ℂ M₅] (A₅ : OrdVModule W M₅)
    {Y₃ : IntertwiningModes M₅ P₃.carrier P₄.carrier}
    {Y₄ : IntertwiningModes P₁.carrier P₂.carrier M₅}
    (hY₃ : IsIntertwiningOperator A₅ P₃.isMod P₄.isMod Y₃)
    (hY₄ : IsIntertwiningOperator P₁.isMod P₂.isMod A₅ Y₄)
    {α₁ α₂ α₃ h₄ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
    {f : P₄.carrier →ₗ[ℂ] ℂ}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : VOA.Huang.MatrixCoeff.SupportedAt P₄.isMod f h₄)
    {ν₀ : ℂ} (hb : VOA.Huang.MatrixCoeff.IsBase Y₄ w₁ w₂ ν₀) {z₀ z₂ : ℂ} (hz₀ : z₀ ≠ 0)
    (hz : ‖z₀‖ < ‖z₂‖) :
    Summable fun k : ℕ =>
      ‖VOA.Huang.MatrixCoeff.iterCoeff Y₃ Y₄ f w₁ w₂ w₃ (ν₀ - k)
          ((α₁ + α₂ + α₃ - h₄ - 2) - ν₀ + k)
        * z₂ ^ (-((α₁ + α₂ + α₃ - h₄ - 2) - ν₀ + k) - 1) * z₀ ^ (-(ν₀ - k) - 1)‖ :=
  summable_iterTerm (huangODEInput_of_moduleC2Input' h2) hV i₁ i₂ i₃ i₄ A₅ hY₃ hY₄ h₁ h₂ h₃ hf hb
    hz₀ hz

end VOA.Huang.HuangODEContra
