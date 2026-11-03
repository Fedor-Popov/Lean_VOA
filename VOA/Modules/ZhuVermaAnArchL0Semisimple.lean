/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchLumaxSupDisjoint
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# `L₀`-semisimplicity — every submodule of a graded `OrdVModule` is graded (`quot_submodule_graded`)

The maximal-`J` residue `MaxJData` (`ZhuVermaAnArchLumaxSupDisjoint`) is down to two deep DLM
fields: `bottom_regen` (generation-from-bottom) and `quot_submodule_graded` (`L₀`-semisimplicity:
every weak submodule of `M(U)/J` is graded).  This file **proves `quot_submodule_graded`** — in fact
the general `L₀`-semisimplicity of any graded `OrdVModule` — cutting `MaxJData` to the SINGLE deep
field `bottom_regen`.

## The argument (eigenvalue isolation)

A weak submodule `Q` of a `OrdVModule N` is `L₀`-stable (it is closed under every mode, in particular
`L₀ = mode (Y_M ω) 1`).  For `y ∈ Q` with finite weight-support `S` (`DirectSum.decompose`), the
`β`-component is isolated by the operator `∏_{γ∈S\{β}} (L₀ - γ)`: since `L₀` acts as the scalar `δ`
on the weight-`δ` component, this operator kills every component but `β` (each other `δ∈S\{β}` gives
a `(δ-δ)=0` factor) and scales the `β`-component by the nonzero `∏_{γ∈S\{β}}(β-γ)`.  As a polynomial
in `L₀`, it preserves `Q`; hence the `β`-component lies in `Q`.  Every component of `y ∈ Q` is
therefore in `Q`, so `Q = ⨆_α (Q ⊓ N_α)` is graded.  (The submodule lattice is *not* distributive,
so this genuinely uses the `L₀`-eigenvalue structure, not just `⨆_α N_α = ⊤`.)

## What is built (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`OrdVModule.L0op`** — the `L₀` operator `mode (Y_M ω) 1 : End M`; `L0op_weight` (acts as `δ` on
  `N_δ`), `L0op_mem` (`Q` is `L₀`-stable).
* **`OrdVModule.isoOp`** — the isolation operator `∏_{γ∈s} (L₀ - γ)`; `isoOp_weight` (`= ∏(δ-γ)•` on
  `N_δ`), `isoOp_mem` (`Q`-preserving).
* **`OrdVModule.component_mem_of_invariant`** — the crux: for `y ∈ Q`, every weight-component of `y` is
  in `Q`.
* **`OrdVModule.submodule_isGraded`** — **`L₀`-semisimplicity**: every weak submodule of a graded
  `OrdVModule` (with a chosen `Decomposition`) is graded.
* **`MUModuleData.quotSubmoduleGraded`** — `quot_submodule_graded` for `M(U)/J` as a TERM.
* **`MUModuleData.MaxJData.ofRegen`** — the `MaxJData` residue from JUST `bottom_regen` — the single
  deepest DLM field (generation-from-bottom).

## References
Dong–Li–Mason J. Algebra 206 (1998); Dong–Jiang Math. Z. 259 (2008) §4; Gannon §5.3.2, Thm 5.3.4;
`ZhuVermaAnArchLumax` (`MaxJData`, `supBotTrivialGraded`), `ZhuVermaAnArchLumaxSupDisjoint`
(`sup_bottom_disjoint`).
-/

namespace VOA

open scoped BigOperators DirectSum
open VertexOperatorAlgebra

attribute [local instance] Classical.propDecidable

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace OrdVModule

variable {W : VertexOperatorAlgebra 𝒱} {M : Type v} [AddCommGroup M] [Module ℂ M]

/-! ## The `L₀` operator and its basic properties -/

/-- The **`L₀` operator** `mode (Y_M ω) 1 : End M`. -/
noncomputable def L0op (N : OrdVModule W M) : Module.End ℂ M := mode (N.YM W.conformalVector) 1

theorem L0op_weight (N : OrdVModule W M) {δ : ℂ} {x : M} (hx : x ∈ N.weight δ) :
    N.L0op x = δ • x := N.L0_weight δ x hx

/-- `Q` is `L₀`-stable (closed under `L₀ = mode (Y_M ω) 1`, a special mode). -/
theorem L0op_mem (N : OrdVModule W M) (Q : WeakModule.Submodule' N.toWeakModule)
    {x : M} (hx : x ∈ Q.carrier) : N.L0op x ∈ Q.carrier := by
  have h := Q.act_mem W.conformalVector 1 hx
  rw [WeakModule.act_def] at h
  exact h

/-- `Q` is stable under every power `L₀^n`. -/
theorem L0op_pow_mem (N : OrdVModule W M) (Q : WeakModule.Submodule' N.toWeakModule)
    {x : M} (hx : x ∈ Q.carrier) (n : ℕ) : (N.L0op ^ n) x ∈ Q.carrier := by
  induction n with
  | zero => simpa using hx
  | succ n ih => rw [pow_succ', Module.End.mul_apply]; exact N.L0op_mem Q ih

/-! ## The isolation operator `aeval L₀ (∏_{γ∈s} (X - γ))` -/

/-- The **isolation operator** `∏_{γ∈s} (L₀ - γ)` realized as `aeval L₀` of the (commutative) monic
polynomial `∏_{γ∈s} (X - C γ)`. -/
noncomputable def isoOp (N : OrdVModule W M) (s : Finset ℂ) : Module.End ℂ M :=
  Polynomial.aeval N.L0op (∏ γ ∈ s, (Polynomial.X - Polynomial.C γ))

/-- **`isoOp` scales a weight vector** by `∏_{γ∈s}(δ-γ)` (`L₀` acts as `δ` on `N_δ`, so the
polynomial evaluates at `δ`). -/
theorem isoOp_weight (N : OrdVModule W M) (s : Finset ℂ) {δ : ℂ} {x : M} (hx : x ∈ N.weight δ) :
    N.isoOp s x = (∏ γ ∈ s, (δ - γ)) • x := by
  rw [isoOp, Module.End.aeval_apply_of_mem_apply_eq_smul (N.L0op_weight hx), Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

/-- `Q` is stable under `aeval L₀ p` for every polynomial `p` (a polynomial in the `Q`-stable
`L₀`). -/
theorem aeval_L0op_mem (N : OrdVModule W M) (Q : WeakModule.Submodule' N.toWeakModule)
    {x : M} (hx : x ∈ Q.carrier) (p : Polynomial ℂ) :
    Polynomial.aeval N.L0op p x ∈ Q.carrier := by
  refine Polynomial.induction_on' p (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [map_add, LinearMap.add_apply]; exact Q.carrier.add_mem hp hq
  · rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact Q.carrier.smul_mem a (N.L0op_pow_mem Q hx n)

/-- **`isoOp` preserves `Q`** (a polynomial in the `Q`-stable `L₀`). -/
theorem isoOp_mem (N : OrdVModule W M) (Q : WeakModule.Submodule' N.toWeakModule)
    (s : Finset ℂ) {x : M} (hx : x ∈ Q.carrier) : N.isoOp s x ∈ Q.carrier :=
  N.aeval_L0op_mem Q hx _

/-! ## The crux — every weight-component of an element of `Q` lies in `Q` -/

/-- **Eigenvalue isolation.** For `y ∈ Q` and `β` in the weight-support of `y`, the `β`-component
`(decompose N.weight y β)` lies in `Q` — the operator `∏_{γ∈S\{β}}(L₀-γ)` isolates it and preserves
`Q`. -/
theorem component_mem_of_invariant (N : OrdVModule W M) [DirectSum.Decomposition N.weight]
    (Q : WeakModule.Submodule' N.toWeakModule) {y : M} (hy : y ∈ Q.carrier) {β : ℂ}
    (hβ : β ∈ (DirectSum.decompose N.weight y).support) :
    ((DirectSum.decompose N.weight y β : N.weight β) : M) ∈ Q.carrier := by
  classical
  set S := (DirectSum.decompose N.weight y).support with hS
  set s := S.erase β with hs
  have hc : (∏ γ ∈ s, (β - γ)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun γ hγ => ?_
    exact sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase hγ))
  have hkey : N.isoOp s y
      = (∏ γ ∈ s, (β - γ)) • ((DirectSum.decompose N.weight y β : N.weight β) : M) := by
    have e1 : N.isoOp s y
        = ∑ δ ∈ S, N.isoOp s ((DirectSum.decompose N.weight y δ : N.weight δ) : M) := by
      rw [← map_sum]; congr 1; exact (DirectSum.sum_support_decompose N.weight y).symm
    rw [e1, Finset.sum_congr rfl
      (fun δ _ => N.isoOp_weight s (SetLike.coe_mem (DirectSum.decompose N.weight y δ)))]
    rw [Finset.sum_eq_single β (fun δ hδ hδβ => ?_) (fun hβS => absurd hβ hβS)]
    have hδs : δ ∈ s := Finset.mem_erase.mpr ⟨hδβ, hδ⟩
    rw [Finset.prod_eq_zero hδs (sub_self δ), zero_smul]
  have hmem : N.isoOp s y ∈ Q.carrier := N.isoOp_mem Q s hy
  rw [hkey] at hmem
  have hsm := Q.carrier.smul_mem (∏ γ ∈ s, (β - γ))⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at hsm

/-! ## `L₀`-semisimplicity -/

/-- **`L₀`-semisimplicity** — every weak submodule of a graded `OrdVModule` (with a chosen
`Decomposition`) is graded.  Discharges `quot_submodule_graded` for `M(U)/J`. -/
theorem submodule_isGraded (N : OrdVModule W M) [DirectSum.Decomposition N.weight]
    (Q : WeakModule.Submodule' N.toWeakModule) :
    OrdVModule.IsGradedSubmodule N Q := by
  classical
  refine le_antisymm ?_ (iSup_le fun α => inf_le_left)
  intro y hy
  have hsum : (∑ β ∈ (DirectSum.decompose N.weight y).support,
      ((DirectSum.decompose N.weight y β : N.weight β) : M))
        ∈ ⨆ α : ℂ, (Q.carrier ⊓ N.weight α) := by
    refine Submodule.sum_mem _ fun β hβ => ?_
    exact Submodule.mem_iSup_of_mem β ⟨N.component_mem_of_invariant Q hy hβ, SetLike.coe_mem _⟩
  rwa [DirectSum.sum_support_decompose N.weight y] at hsum

end OrdVModule

/-! ## `quot_submodule_graded` for `M(U)/J`, and `MaxJData` from `bottom_regen` alone -/

namespace MUModuleData

variable {W : VertexOperatorAlgebra 𝒱} {U : AMod W} {h : ℂ}

/-- **`quot_submodule_graded`** — every weak submodule of `M(U)/J` is graded (`L₀`-
semisimplicity of the quotient `OrdVModule`). -/
theorem quotSubmoduleGraded (D : MUModuleData W U h) :
    ∀ Q : WeakModule.Submodule'
        (OrdVModule.quotient D.toOrdVModule D.supBotTrivialGraded
          D.supBotTrivialGraded_isGraded).toWeakModule,
      OrdVModule.IsGradedSubmodule
        (OrdVModule.quotient D.toOrdVModule D.supBotTrivialGraded D.supBotTrivialGraded_isGraded) Q := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition
    (OrdVModule.quotient D.toOrdVModule D.supBotTrivialGraded D.supBotTrivialGraded_isGraded).weight
    (OrdVModule.quotient D.toOrdVModule D.supBotTrivialGraded D.supBotTrivialGraded_isGraded).isInternal
  exact fun Q => OrdVModule.submodule_isGraded _ Q

/-- **`MaxJData` from `bottom_regen` alone** — with `sup_bottom_disjoint`
(`supBotTrivialGraded_bottom_disjoint`) and `quot_submodule_graded` (`quotSubmoduleGraded`) both
TERMS, the maximal-`J` residue is the SINGLE deep field `bottom_regen` (generation-from-bottom). -/
def MaxJData.ofRegen (D : MUModuleData W U h)
    (bottom_regen : ∀ Q : WeakModule.Submodule' D.toOrdVModule.toWeakModule,
      OrdVModule.IsGradedSubmodule D.toOrdVModule Q →
        Q.carrier ⊓ D.toOrdVModule.weight h ≠ ⊥ → Q.carrier = ⊤) :
    MaxJData D where
  bottom_regen := bottom_regen
  sup_bottom_disjoint := D.supBotTrivialGraded_bottom_disjoint
  quot_submodule_graded := D.quotSubmoduleGraded

end MUModuleData

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
