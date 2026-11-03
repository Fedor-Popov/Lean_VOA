/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDJCarrierWeak
import VOA.Modules.ZhuVermaAnArchVModQuotGraded
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# C5, layer 1 — `J`, `L = M/J` and irreducibility for a **finrank-free** graded module

`ZhuVermaAnArchDJCarrierWeak` packaged Dong–Jiang's `M(U) = ⨁ₙ A_{n,0}(𝒱) ⊗_{A(𝒱)} U` as a
`GradedLWWeakModule W (DJCarrier W U) h` — the repo's `LWModule` with the single field
`OrdVModule.finrank` deleted, because that field is *false* at the scope the Zhu bijection needs (the
bottom of `M(U)` is `U`, and the gate is instantiated at the regular module `U = A(𝒱)`, which is
infinite-dimensional in general).

This file rebuilds, over that finrank-free object, the whole graded-submodule / maximal-`J` /
irreducible-quotient layer that otherwise exists only over `OrdVModule`
(`ZhuVermaAnArchL0Semisimple`, `ZhuVermaAnArchVModQuotGraded`, `ZhuVermaAnArchLumax`,
`ZhuVermaAnArchGameTwo`).  It is a **build**, not a re-typing exercise, and it lands one statement
strictly stronger than the `OrdVModule` version:

**`maxJ_bottom_disjoint` is a THEOREM here.**  On the `OrdVModule` track the bottom-triviality of the
supremum of all bottom-trivial graded submodules was *carried* as the hypothesis
`MaxJData.sup_bottom_disjoint` ("the genuine finiteness/structure content", `ZhuVermaAnArchLumax`).
It needs no finiteness at all: gradedness of each summand plus uniqueness of the internal
decomposition already force it (§3).

## Contents

### §1 `L₀`-semisimplicity (unconditional)
`IsGradedSub`, `L0op`, `isoOp`, `component_mem_of_invariant`, and
**`submodule_isGraded` — every weak submodule of a graded weak module is graded**.  No finiteness,
no boundedness: only the internal `ℂ`-grading and the `L₀`-eigenvalue property.

### §2 Components of a graded submodule (unconditional)
`component_mem_of_graded`.

### §3 The maximal bottom-trivial graded submodule `J` (unconditional)
`BotTrivialGraded`, `maxJ`, `maxJ_dom`, `maxJ_isGraded`, `maxJ_bottom_disjoint`.

### §4 The graded quotient (unconditional)
`quotWeight`, `quotWeight_isInternal`, `quotWeight_isLow`, `quotWeight_boundedBelow`,
`quotWeight_realized`, and `GradedLWWeakModule.quotient` — a `GradedLWWeakModule` again, *at the
same lowest weight `h`*, provided the divisor meets the bottom trivially.

### §5 Pullbacks of quotient submodules (unconditional)
`comapQuot`, `comapQuot_ge`, `comapQuot_map`, `comapQuot_isGraded`.

### §6 `L = M/J`, its irreducibility, and its bottom
`GeneratedByBottom` and `BottomIrreducible` (two named `Prop`s — the *only* inputs),
`bottom_regen`, `LU`, `LU_graded_simple`, `LU_isIrreducible`, `LU_bottom_equiv`,
`LU_nontrivial`.

## The two carried hypotheses, and why they are the right ones

* **`GeneratedByBottom N`** — a weak submodule containing the bottom `M_h` is everything.  This is
  Dong–Jiang Theorem 4.13's generation sentence; for `M(U)` it is *discharged* by the proved
  `djCarrierWeak_generated_by_bottom` (which carries the independent `regularAMod`
  `BottomProjection` hypothesis).
* **`BottomIrreducible N`** — a nonzero subspace of the bottom `M_h`, stable under every mode that
  keeps it inside `M_h`, is all of `M_h`.  For `M(U)` this is exactly the simplicity of `U` as an
  `A(𝒱)`-module, i.e. the *scope* of the bijection (`AModScope`): the unscoped statement is false.

⚠ **DLM3's own irreducibility argument is NOT used.**  DLM3 Lemma 4.8 / Dong–Jiang Theorem 4.16
prove simplicity of `L(U)` using complete reducibility of `M(U)`, which requires `V` **rational**.
The route here is the general one — the maximal graded submodule meeting the bottom trivially — and
it uses no rationality, no complete reducibility, and no finite-dimensionality.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`) §4, Thm 4.13; Dong–Li–Mason, `q-alg/9612010` §4
(Thm 4.1, Thm 4.2, Lemma 4.8 — the *rational* argument, deliberately not imported); Gannon §5.3.2,
Thm 5.3.4.  Repo: `ZhuVermaAnArchDJCarrierWeak` (`GradedLWWeakModule`),
`ZhuVermaAnArchVModQuot` (`WeakModule.quotient`, `quotient_act_mk`),
`ZhuVermaAnArchL0Semisimple` / `ZhuVermaAnArchLumax` (the `OrdVModule`-typed ancestors of §1–§5).
-/

namespace VOA

open scoped BigOperators DirectSum
open VertexOperatorAlgebra

attribute [local instance] Classical.propDecidable

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace GradedLWWeakModule

variable {W : VertexOperatorAlgebra 𝒱} {M : Type v} [AddCommGroup M] [Module ℂ M] {h : ℂ}

/-! ## §1 Graded submodules and `L₀`-semisimplicity -/

/-- A weak submodule `P` of a graded weak module `N` is **graded** (homogeneous / `L₀`-stable) when
it is the internal sum of its homogeneous parts, `P = ⨆_α (P ⊓ N_α)`.  (The finrank-free mirror of
`OrdVModule.IsGradedSubmodule`.) -/
def IsGradedSub (N : GradedLWWeakModule W M h) (P : WeakModule.Submodule' N.toWeakModule) : Prop :=
  P.carrier = ⨆ α : ℂ, (P.carrier ⊓ N.weight α)

/-- The homogeneous parts always sit inside the submodule; only the converse is content. -/
theorem iSup_inf_le (N : GradedLWWeakModule W M h) (P : WeakModule.Submodule' N.toWeakModule) :
    (⨆ α : ℂ, (P.carrier ⊓ N.weight α)) ≤ P.carrier :=
  iSup_le fun _ => inf_le_left

/-- The **`L₀` operator** `mode (Y_M ω) 1` of a graded weak module. -/
noncomputable def L0op (N : GradedLWWeakModule W M h) : Module.End ℂ M :=
  mode (N.toWeakModule.YM W.conformalVector) 1

/-- On the weight space `M_δ` the operator `L₀` is the scalar `δ`. -/
theorem L0op_weight (N : GradedLWWeakModule W M h) {δ : ℂ} {x : M} (hx : x ∈ N.weight δ) :
    N.L0op x = δ • x := N.L0_weight δ x hx

/-- A weak submodule is `L₀`-stable (`L₀` is one of the modes). -/
theorem L0op_mem (N : GradedLWWeakModule W M h) (Q : WeakModule.Submodule' N.toWeakModule)
    {x : M} (hx : x ∈ Q.carrier) : N.L0op x ∈ Q.carrier := by
  have hq := Q.act_mem W.conformalVector 1 hx
  rwa [WeakModule.act_def] at hq

/-- A weak submodule is stable under every power of `L₀`. -/
theorem L0op_pow_mem (N : GradedLWWeakModule W M h) (Q : WeakModule.Submodule' N.toWeakModule)
    {x : M} (hx : x ∈ Q.carrier) (n : ℕ) : (N.L0op ^ n) x ∈ Q.carrier := by
  induction n with
  | zero => simpa using hx
  | succ n ih => rw [pow_succ', Module.End.mul_apply]; exact N.L0op_mem Q ih

/-- A weak submodule is stable under `aeval L₀ p` for every polynomial `p`. -/
theorem aeval_L0op_mem (N : GradedLWWeakModule W M h) (Q : WeakModule.Submodule' N.toWeakModule)
    {x : M} (hx : x ∈ Q.carrier) (p : Polynomial ℂ) :
    Polynomial.aeval N.L0op p x ∈ Q.carrier := by
  refine Polynomial.induction_on' p (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [map_add, LinearMap.add_apply]; exact Q.carrier.add_mem hp hq
  · rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact Q.carrier.smul_mem a (N.L0op_pow_mem Q hx n)

/-- The **isolation operator** `∏_{γ∈s} (L₀ − γ)`. -/
noncomputable def isoOp (N : GradedLWWeakModule W M h) (s : Finset ℂ) : Module.End ℂ M :=
  Polynomial.aeval N.L0op (∏ γ ∈ s, (Polynomial.X - Polynomial.C γ))

/-- `isoOp s` scales a weight-`δ` vector by `∏_{γ∈s}(δ−γ)`. -/
theorem isoOp_weight (N : GradedLWWeakModule W M h) (s : Finset ℂ) {δ : ℂ} {x : M}
    (hx : x ∈ N.weight δ) : N.isoOp s x = (∏ γ ∈ s, (δ - γ)) • x := by
  rw [isoOp, Module.End.aeval_apply_of_mem_apply_eq_smul (N.L0op_weight hx), Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

/-- `isoOp s` preserves every weak submodule. -/
theorem isoOp_mem (N : GradedLWWeakModule W M h) (Q : WeakModule.Submodule' N.toWeakModule)
    (s : Finset ℂ) {x : M} (hx : x ∈ Q.carrier) : N.isoOp s x ∈ Q.carrier :=
  N.aeval_L0op_mem Q hx _

/-- **Eigenvalue isolation.**  For `y` in a weak submodule `Q` and `β` in the weight-support of `y`,
the `β`-component of `y` again lies in `Q`. -/
theorem component_mem_of_invariant (N : GradedLWWeakModule W M h)
    [DirectSum.Decomposition N.weight] (Q : WeakModule.Submodule' N.toWeakModule) {y : M}
    (hy : y ∈ Q.carrier) {β : ℂ} (hβ : β ∈ (DirectSum.decompose N.weight y).support) :
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

/-- **`L₀`-semisimplicity, finrank-free.**  *Every* weak submodule of a graded weak module is
graded.  Only the internal `ℂ`-grading and the `L₀`-eigenvalue property are used — no
finite-dimensionality, no bounded-belowness. -/
theorem submodule_isGraded (N : GradedLWWeakModule W M h) [DirectSum.Decomposition N.weight]
    (Q : WeakModule.Submodule' N.toWeakModule) : IsGradedSub N Q := by
  classical
  refine le_antisymm ?_ (N.iSup_inf_le Q)
  intro y hy
  have hsum : (∑ β ∈ (DirectSum.decompose N.weight y).support,
      ((DirectSum.decompose N.weight y β : N.weight β) : M))
        ∈ ⨆ α : ℂ, (Q.carrier ⊓ N.weight α) :=
    Submodule.sum_mem _ fun β hβ =>
      Submodule.mem_iSup_of_mem β ⟨N.component_mem_of_invariant Q hy hβ, SetLike.coe_mem _⟩
  rwa [DirectSum.sum_support_decompose N.weight y] at hsum

/-! ## §2 Components of a **graded** submodule -/

/-- **Each weight-component of an element of a graded submodule stays in the submodule.** -/
theorem component_mem_of_graded (N : GradedLWWeakModule W M h)
    [DirectSum.Decomposition N.weight] (P : WeakModule.Submodule' N.toWeakModule)
    (hP : IsGradedSub N P) {y : M} (hy : y ∈ P.carrier) (α : ℂ) :
    ((DirectSum.decompose N.weight y α : N.weight α) : M) ∈ P.carrier := by
  classical
  rw [hP] at hy
  refine Submodule.iSup_induction (fun α : ℂ => P.carrier ⊓ N.weight α) hy
    (motive := fun z => ((DirectSum.decompose N.weight z α : N.weight α) : M) ∈ P.carrier)
    (fun β z hz => ?_) ?_ (fun z w hz hw => ?_)
  · simp only
    rcases eq_or_ne α β with rfl | hαβ
    · rw [DirectSum.decompose_of_mem_same N.weight hz.2]; exact hz.1
    · rw [DirectSum.decompose_of_mem_ne N.weight hz.2 (Ne.symm hαβ)]
      exact Submodule.zero_mem _
  · change ((DirectSum.decompose N.weight (0 : M) α : N.weight α) : M) ∈ P.carrier
    rw [DirectSum.decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]
    exact Submodule.zero_mem _
  · change ((DirectSum.decompose N.weight (z + w) α : N.weight α) : M) ∈ P.carrier
    rw [DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add]
    exact Submodule.add_mem _ hz hw

/-! ## §3 The maximal bottom-trivial graded submodule `J` -/

/-- **A bottom-trivial graded submodule** — the index datum of the supremum `J`. -/
structure BotTrivialGraded (N : GradedLWWeakModule W M h) where
  /-- The underlying weak submodule. -/
  Q : WeakModule.Submodule' N.toWeakModule
  /-- It is graded. -/
  Q_graded : IsGradedSub N Q
  /-- It meets the bottom `M_h` trivially. -/
  Q_disjoint : Q.carrier ⊓ N.weight h = ⊥

/-- **`J` — the maximal bottom-trivial graded submodule**: the supremum of the carriers of all
bottom-trivial graded submodules.  Mode-closure follows from `Submodule.iSup_induction`. -/
noncomputable def maxJ (N : GradedLWWeakModule W M h) :
    WeakModule.Submodule' N.toWeakModule where
  carrier := ⨆ T : BotTrivialGraded N, T.Q.carrier
  act_mem := by
    intro u n x hx
    refine Submodule.iSup_induction (fun T : BotTrivialGraded N => T.Q.carrier) hx
      (motive := fun y => N.toWeakModule.act u n y ∈ ⨆ T : BotTrivialGraded N, T.Q.carrier)
      (fun T y hy => ?_) ?_ (fun y z hy hz => ?_)
    · exact Submodule.mem_iSup_of_mem T (T.Q.act_mem u n hy)
    · simp only [WeakModule.act_zero_right]; exact Submodule.zero_mem _
    · simp only [WeakModule.act_add_right]; exact Submodule.add_mem _ hy hz

@[simp] theorem maxJ_carrier (N : GradedLWWeakModule W M h) :
    (maxJ N).carrier = ⨆ T : BotTrivialGraded N, T.Q.carrier := rfl

/-- Every bottom-trivial graded submodule is contained in `J`. -/
theorem maxJ_dom (N : GradedLWWeakModule W M h) (T : BotTrivialGraded N) :
    T.Q.carrier ≤ (maxJ N).carrier :=
  le_iSup (fun T : BotTrivialGraded N => T.Q.carrier) T

/-- **`J` is graded** (a supremum of graded submodules is graded). -/
theorem maxJ_isGraded (N : GradedLWWeakModule W M h) : IsGradedSub N (maxJ N) := by
  refine le_antisymm ?_ (N.iSup_inf_le (maxJ N))
  rw [maxJ_carrier]
  refine iSup_le fun T => ?_
  rw [T.Q_graded]
  exact iSup_le fun α => le_iSup_of_le α (inf_le_inf_right _ (maxJ_dom N T))

/-- **`J` meets the bottom trivially — a THEOREM, not a hypothesis.**

On the `OrdVModule` track this was carried as `MUModuleData.MaxJData.sup_bottom_disjoint` and described
as "the genuine finiteness/structure content" (`ZhuVermaAnArchLumax`).  It needs no finiteness: for
`x ∈ J ⊓ M_h`, expand `x` as a finite sum of vectors from bottom-trivial graded summands, take the
`h`-component of each (which stays in its summand, by `component_mem_of_graded`), and use that the
`h`-component of `x` is `x` itself. -/
theorem maxJ_bottom_disjoint (N : GradedLWWeakModule W M h) :
    (maxJ N).carrier ⊓ N.weight h = ⊥ := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition N.weight N.isInternal
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxJ, hxh⟩ := Submodule.mem_inf.mp hx
  -- The `h`-component of any element of `J` lies in `⨆_T (Q_T ⊓ M_h)`.
  have key : ∀ y ∈ (maxJ N).carrier,
      ((DirectSum.decompose N.weight y h : N.weight h) : M)
        ∈ ⨆ T : BotTrivialGraded N, (T.Q.carrier ⊓ N.weight h) := by
    intro y hy
    rw [maxJ_carrier] at hy
    refine Submodule.iSup_induction (fun T : BotTrivialGraded N => T.Q.carrier) hy
      (motive := fun z => ((DirectSum.decompose N.weight z h : N.weight h) : M)
        ∈ ⨆ T : BotTrivialGraded N, (T.Q.carrier ⊓ N.weight h))
      (fun T z hz => ?_) ?_ (fun z w hz hw => ?_)
    · exact Submodule.mem_iSup_of_mem T
        ⟨N.component_mem_of_graded T.Q T.Q_graded hz h, SetLike.coe_mem _⟩
    · change ((DirectSum.decompose N.weight (0 : M) h : N.weight h) : M) ∈ _
      rw [DirectSum.decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]
      exact Submodule.zero_mem _
    · change ((DirectSum.decompose N.weight (z + w) h : N.weight h) : M) ∈ _
      rw [DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add]
      exact Submodule.add_mem _ hz hw
  have hxc := key x hxJ
  rw [DirectSum.decompose_of_mem_same N.weight hxh] at hxc
  have hbot : (⨆ T : BotTrivialGraded N, (T.Q.carrier ⊓ N.weight h)) = ⊥ :=
    iSup_eq_bot.mpr fun T => T.Q_disjoint
  rw [hbot] at hxc
  exact hxc

/-! ## §4 The graded quotient by a bottom-trivial graded submodule -/

section Quotient

variable (N : GradedLWWeakModule W M h) (P : WeakModule.Submodule' N.toWeakModule)

/-- The image grading on the quotient: `(M/P)_α = mkQ '' M_α`. -/
noncomputable def quotWeight (α : ℂ) : Submodule ℂ (M ⧸ P.carrier) :=
  (N.weight α).map P.carrier.mkQ

theorem quotWeight_eq_bot_iff (α : ℂ) : quotWeight N P α = ⊥ ↔ N.weight α ≤ P.carrier := by
  rw [quotWeight, eq_bot_iff, Submodule.map_le_iff_le_comap, Submodule.comap_bot,
    Submodule.ker_mkQ]

/-- Disjointness of images through `mkQ`, from a homogeneous-overlap bound. -/
theorem disjoint_map_mkQ (A B : Submodule ℂ M) (hAB : A ⊓ (B ⊔ P.carrier) ≤ P.carrier) :
    Disjoint (A.map P.carrier.mkQ) (B.map P.carrier.mkQ) := by
  rw [disjoint_iff, Submodule.map_inf_eq_map_inf_comap, Submodule.comap_map_eq,
    Submodule.ker_mkQ, eq_bot_iff, Submodule.map_le_iff_le_comap, Submodule.comap_bot,
    Submodule.ker_mkQ]
  exact hAB

/-- The modular core of the independence descent (needs `P` graded). -/
theorem weight_inf_le_of_graded (hP : IsGradedSub N P) (α : ℂ) :
    N.weight α ⊓ ((⨆ β : ℂ, ⨆ (_ : β ≠ α), N.weight β) ⊔ P.carrier) ≤ P.carrier := by
  set B := ⨆ β : ℂ, ⨆ (_ : β ≠ α), N.weight β with hB
  have hindep : iSupIndep N.weight :=
    ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top N.weight).mp N.isInternal).1
  have hdis : Disjoint (N.weight α) B := hindep α
  have hsplit : B ⊔ P.carrier = B ⊔ (P.carrier ⊓ N.weight α) := by
    refine le_antisymm (sup_le le_sup_left ?_) (sup_le_sup_left inf_le_left B)
    conv_lhs => rw [hP]
    refine iSup_le fun γ => ?_
    by_cases hγ : γ = α
    · subst hγ; exact le_sup_right
    · have hγB : N.weight γ ≤ B := by
        rw [hB]; exact le_iSup_of_le γ (le_iSup_of_le hγ le_rfl)
      exact le_trans inf_le_right (le_trans hγB le_sup_left)
  rw [hsplit, ← inf_sup_assoc_of_le B (show P.carrier ⊓ N.weight α ≤ N.weight α from inf_le_right),
    disjoint_iff.mp hdis, bot_sup_eq]
  exact inf_le_left

/-- The image grading of a graded divisor is independent. -/
theorem quotWeight_iSupIndep (hP : IsGradedSub N P) : iSupIndep (quotWeight N P) := by
  intro α
  have hrw : (⨆ β : ℂ, ⨆ (_ : β ≠ α), quotWeight N P β)
      = (⨆ β : ℂ, ⨆ (_ : β ≠ α), N.weight β).map P.carrier.mkQ := by
    rw [Submodule.map_iSup]
    exact iSup_congr fun β => by rw [Submodule.map_iSup]; rfl
  rw [show quotWeight N P α = (N.weight α).map P.carrier.mkQ from rfl, hrw]
  exact disjoint_map_mkQ N P (N.weight α) (⨆ β : ℂ, ⨆ (_ : β ≠ α), N.weight β)
    (weight_inf_le_of_graded N P hP α)

/-- The image grading spans the quotient (`mkQ` is surjective). -/
theorem quotWeight_iSup_eq_top : (⨆ α : ℂ, quotWeight N P α) = ⊤ := by
  have htop : iSup N.weight = ⊤ :=
    ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top N.weight).mp N.isInternal).2
  change (⨆ α : ℂ, (N.weight α).map P.carrier.mkQ) = ⊤
  rw [← Submodule.map_iSup, htop, Submodule.map_top, Submodule.range_mkQ]

/-- The image grading is an internal direct-sum decomposition of `M ⧸ P`. -/
theorem quotWeight_isInternal (hP : IsGradedSub N P) :
    DirectSum.IsInternal (quotWeight N P) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top (quotWeight N P)).mpr
    ⟨quotWeight_iSupIndep N P hP, quotWeight_iSup_eq_top N P⟩

/-- `h` remains a lowest weight of the quotient. -/
theorem quotWeight_isLow (α : ℂ) (hα : quotWeight N P α ≠ ⊥) : ∃ n : ℕ, α = h + n := by
  refine N.isLow α (fun hbot => hα ?_)
  change (N.weight α).map P.carrier.mkQ = ⊥
  rw [hbot, Submodule.map_bot]

/-- The quotient grading is bounded below by the same bound. -/
theorem quotWeight_boundedBelow : ∃ B : ℝ, ∀ α : ℂ, quotWeight N P α ≠ ⊥ → B ≤ α.re := by
  obtain ⟨B, hB⟩ := N.boundedBelow
  refine ⟨B, fun α hα => hB α fun hbot => hα ?_⟩
  change (N.weight α).map P.carrier.mkQ = ⊥
  rw [hbot, Submodule.map_bot]

/-- **The bottom survives the quotient** when the divisor meets it trivially. -/
theorem quotWeight_realized (hdisj : P.carrier ⊓ N.weight h = ⊥) : quotWeight N P h ≠ ⊥ := by
  intro hbot
  have hle : N.weight h ≤ P.carrier := (quotWeight_eq_bot_iff N P h).mp hbot
  refine N.realized ?_
  rw [eq_bot_iff, ← hdisj]
  exact le_inf hle le_rfl

/-- The descended `L₀`-eigenspace property on the quotient. -/
theorem quot_L0_weight (α : ℂ) (y : M ⧸ P.carrier) (hy : y ∈ quotWeight N P α) :
    mode ((WeakModule.quotient N.toWeakModule P).YM W.conformalVector) 1 y = α • y := by
  obtain ⟨x, hx, rfl⟩ := (Submodule.mem_map).mp hy
  rw [Submodule.mkQ_apply]
  have hint : mode ((WeakModule.quotient N.toWeakModule P).YM W.conformalVector) 1
      (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk (mode (N.toWeakModule.YM W.conformalVector) 1 x) :=
    WeakModule.quotient_action_mk N.toWeakModule P W.conformalVector 1 x
  rw [hint, N.L0_weight α x hx, Submodule.Quotient.mk_smul]

/-- **The graded quotient `M ⧸ P` is again a `GradedLWWeakModule` at the same lowest weight `h`**,
for a graded divisor `P` meeting the bottom trivially.  Unconditional; no finiteness anywhere. -/
noncomputable def quotient (hP : IsGradedSub N P) (hdisj : P.carrier ⊓ N.weight h = ⊥) :
    GradedLWWeakModule W (M ⧸ P.carrier) h where
  toWeakModule := WeakModule.quotient N.toWeakModule P
  weight := quotWeight N P
  isInternal := quotWeight_isInternal N P hP
  L0_weight := quot_L0_weight N P
  boundedBelow := quotWeight_boundedBelow N P
  isLow := quotWeight_isLow N P
  realized := quotWeight_realized N P hdisj

@[simp] theorem quotient_weight (hP : IsGradedSub N P) (hdisj : P.carrier ⊓ N.weight h = ⊥)
    (α : ℂ) : (quotient N P hP hdisj).weight α = (N.weight α).map P.carrier.mkQ := rfl

@[simp] theorem quotient_act_mk (hP : IsGradedSub N P) (hdisj : P.carrier ⊓ N.weight h = ⊥)
    (a : 𝒱) (k : ℤ) (x : M) :
    (quotient N P hP hdisj).toWeakModule.act a k (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk (N.toWeakModule.act a k x) :=
  WeakModule.quotient_act_mk N.toWeakModule P a k x

end Quotient

/-! ## §5 Pullbacks of quotient submodules -/

section Comap

variable (N : GradedLWWeakModule W M h) (P : WeakModule.Submodule' N.toWeakModule)
  (hP : IsGradedSub N P) (hdisj : P.carrier ⊓ N.weight h = ⊥)

/-- **The pullback of a quotient weak submodule** along `mkQ`. -/
noncomputable def comapQuot
    (Q : WeakModule.Submodule' (quotient N P hP hdisj).toWeakModule) :
    WeakModule.Submodule' N.toWeakModule where
  carrier := Q.carrier.comap P.carrier.mkQ
  act_mem := by
    intro u n x hx
    simp only [Submodule.mem_comap, Submodule.mkQ_apply] at hx ⊢
    rw [show (Submodule.Quotient.mk (N.toWeakModule.act u n x) : M ⧸ P.carrier)
        = (quotient N P hP hdisj).toWeakModule.act u n (Submodule.Quotient.mk x) from
      (quotient_act_mk N P hP hdisj u n x).symm]
    exact Q.act_mem u n hx

@[simp] theorem comapQuot_carrier
    (Q : WeakModule.Submodule' (quotient N P hP hdisj).toWeakModule) :
    (comapQuot N P hP hdisj Q).carrier = Q.carrier.comap P.carrier.mkQ := rfl

/-- The pullback contains the divisor. -/
theorem comapQuot_ge (Q : WeakModule.Submodule' (quotient N P hP hdisj).toWeakModule) :
    P.carrier ≤ (comapQuot N P hP hdisj Q).carrier := by
  intro x hx
  simp only [comapQuot_carrier, Submodule.mem_comap, Submodule.mkQ_apply]
  rw [(Submodule.Quotient.mk_eq_zero P.carrier).mpr hx]
  exact Submodule.zero_mem _

/-- Pushing the pullback forward recovers the original quotient submodule. -/
theorem comapQuot_map (Q : WeakModule.Submodule' (quotient N P hP hdisj).toWeakModule) :
    (comapQuot N P hP hdisj Q).carrier.map P.carrier.mkQ = Q.carrier :=
  Submodule.map_comap_eq_of_surjective P.carrier.mkQ_surjective Q.carrier

/-- **The pullback of a graded quotient submodule is graded.**  The two `DirectSum.Decomposition`
witnesses are passed *explicitly* (not as instances): the quotient's grading is only definitionally
the one instance search would need at the call sites. -/
theorem comapQuot_isGraded (instN : DirectSum.Decomposition N.weight)
    (instQ : DirectSum.Decomposition (quotient N P hP hdisj).weight)
    (Q : WeakModule.Submodule' (quotient N P hP hdisj).toWeakModule)
    (hQ : IsGradedSub (quotient N P hP hdisj) Q) :
    IsGradedSub N (comapQuot N P hP hdisj Q) := by
  classical
  letI := instN
  letI := instQ
  refine le_antisymm ?_ (N.iSup_inf_le _)
  intro x hx
  have hxQ : (Submodule.Quotient.mk x : M ⧸ P.carrier) ∈ Q.carrier := hx
  set c : ℂ → M := fun β => ((DirectSum.decompose N.weight x β : N.weight β) : M) with hc
  set s : Finset ℂ := (DirectSum.decompose N.weight x).support with hs
  have hcmem : ∀ β, c β ∈ N.weight β := fun β => (DirectSum.decompose N.weight x β).2
  have hdecomp : (∑ β ∈ s, c β) = x := DirectSum.sum_support_decompose N.weight x
  have hcβ_q : ∀ β : ℂ, (Submodule.Quotient.mk (c β) : M ⧸ P.carrier)
      ∈ (quotient N P hP hdisj).weight β := by
    intro β
    rw [quotient_weight]
    exact Submodule.mem_map_of_mem (hcmem β)
  have hmkc : ∀ β : ℂ, (Submodule.Quotient.mk (c β) : M ⧸ P.carrier) ∈ Q.carrier := by
    intro β
    have hcomp : ((DirectSum.decompose (quotient N P hP hdisj).weight
        (Submodule.Quotient.mk x : M ⧸ P.carrier) β :
          (quotient N P hP hdisj).weight β) : M ⧸ P.carrier)
        = Submodule.Quotient.mk (c β) := by
      have hsum : (Submodule.Quotient.mk x : M ⧸ P.carrier)
          = ∑ γ ∈ s, Submodule.Quotient.mk (c γ) := by
        conv_lhs => rw [← hdecomp]
        rw [← Submodule.mkQ_apply, map_sum]
        exact Finset.sum_congr rfl fun γ _ => Submodule.mkQ_apply _ _
      rw [hsum, DirectSum.decompose_sum]
      rw [show (∑ i ∈ s, DirectSum.decompose (quotient N P hP hdisj).weight
            (Submodule.Quotient.mk (c i))) β
          = ∑ i ∈ s, DirectSum.decompose (quotient N P hP hdisj).weight
            (Submodule.Quotient.mk (c i)) β from DFinsupp.finsetSum_apply s _ β]
      rw [AddSubmonoidClass.coe_finsetSum]
      rw [Finset.sum_eq_single β]
      · rw [DirectSum.decompose_of_mem_same _ (hcβ_q β)]
      · intro γ _ hγβ
        rw [DirectSum.decompose_of_mem _ (hcβ_q γ),
          DirectSum.of_eq_of_ne _ _ _ (Ne.symm hγβ), ZeroMemClass.coe_zero]
      · intro hβs
        have hcβ0 : (Submodule.Quotient.mk (c β) : M ⧸ P.carrier) = 0 := by
          have hz : c β = 0 := by
            rw [hc]; simp only
            rw [show DirectSum.decompose N.weight x β = 0 from by
              rw [← DFinsupp.notMem_support_iff]; exact hβs, ZeroMemClass.coe_zero]
          rw [hz, Submodule.Quotient.mk_zero]
        rw [DirectSum.decompose_of_mem _ (hcβ_q β), DirectSum.of_eq_same]
        exact hcβ0
    rw [← hcomp]
    exact component_mem_of_graded (quotient N P hP hdisj) Q hQ hxQ β
  rw [← hdecomp]
  refine Submodule.sum_mem _ fun β _ => ?_
  refine Submodule.mem_iSup_of_mem β (Submodule.mem_inf.mpr ⟨?_, hcmem β⟩)
  simpa only [comapQuot_carrier, Submodule.mem_comap, Submodule.mkQ_apply] using hmkc β

end Comap

/-! ## §6 `L = M/J`, irreducibility, and the bottom -/

section LU

variable (N : GradedLWWeakModule W M h)

/-- **Generation from the bottom** — a weak submodule containing `M_h` is everything.  This is
Dong–Jiang Thm 4.13's generation sentence.  Carried as a named `Prop`, never an axiom. -/
def GeneratedByBottom : Prop :=
  ∀ Q : WeakModule.Submodule' N.toWeakModule, N.weight h ≤ Q.carrier → Q.carrier = ⊤

/-- **Irreducibility of the bottom** — a nonzero subspace of `M_h` that is stable under every mode
which keeps it inside `M_h` is all of `M_h`.  For `M(U)` this is exactly the simplicity of `U` as an
`A(𝒱)`-module: the *scope* of Theorem 5.3.4, false without it.  Carried as a named `Prop`. -/
def BottomIrreducible : Prop :=
  ∀ S : Submodule ℂ M, S ≤ N.weight h → S ≠ ⊥ →
    (∀ (a : 𝒱) (p : ℤ) (x : M), x ∈ S → N.toWeakModule.act a p x ∈ N.weight h →
      N.toWeakModule.act a p x ∈ S) →
    S = N.weight h

variable {N}

/-- **Bottom regeneration.**  Any weak submodule meeting the bottom nontrivially is everything.
(No gradedness of `Q` is needed.) -/
theorem bottom_regen (hgen : GeneratedByBottom N) (hirr : BottomIrreducible N)
    (Q : WeakModule.Submodule' N.toWeakModule) (hQ : Q.carrier ⊓ N.weight h ≠ ⊥) :
    Q.carrier = ⊤ := by
  refine hgen Q ?_
  have hS : Q.carrier ⊓ N.weight h = N.weight h := by
    refine hirr _ inf_le_right hQ ?_
    intro a p x hx hmem
    exact Submodule.mem_inf.mpr ⟨Q.act_mem a p (Submodule.mem_inf.mp hx).1, hmem⟩
  rw [← hS]
  exact inf_le_left

variable (N)

/-- **`L = M / J`** — the quotient by the maximal bottom-trivial graded submodule, again a
`GradedLWWeakModule` at lowest weight `h`.  unconditional. -/
noncomputable def LU : GradedLWWeakModule W (M ⧸ (maxJ N).carrier) h :=
  quotient N (maxJ N) (maxJ_isGraded N) (maxJ_bottom_disjoint N)

@[simp] theorem LU_weight (α : ℂ) : (LU N).weight α = (N.weight α).map (maxJ N).carrier.mkQ := rfl

@[simp] theorem LU_act_mk (a : 𝒱) (k : ℤ) (x : M) :
    (LU N).toWeakModule.act a k (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk (N.toWeakModule.act a k x) :=
  quotient_act_mk N (maxJ N) (maxJ_isGraded N) (maxJ_bottom_disjoint N) a k x

variable {N}

/-- **Graded simplicity of `L`.**  A graded weak submodule of `L` pulls back to a graded submodule
`Q ⊇ J` of `M`; if `Q` is bottom-trivial it is `≤ J` by maximality, so the image is `⊥`; otherwise
`bottom_regen` gives `Q = ⊤`, hence the image is `⊤`. -/
theorem LU_graded_simple (instN : DirectSum.Decomposition N.weight)
    (instL : DirectSum.Decomposition (LU N).weight)
    (hgen : GeneratedByBottom N) (hirr : BottomIrreducible N)
    (Q : WeakModule.Submodule' (LU N).toWeakModule) (hQ : IsGradedSub (LU N) Q) :
    Q.carrier = ⊥ ∨ Q.carrier = ⊤ := by
  set J := maxJ N with hJ
  set Q' := comapQuot N J (maxJ_isGraded N) (maxJ_bottom_disjoint N) Q with hQ'
  have hQ'_graded : IsGradedSub N Q' :=
    comapQuot_isGraded N J (maxJ_isGraded N) (maxJ_bottom_disjoint N) instN instL Q hQ
  have hQ'_ge : J.carrier ≤ Q'.carrier :=
    comapQuot_ge N J (maxJ_isGraded N) (maxJ_bottom_disjoint N) Q
  have hmap : Q'.carrier.map J.carrier.mkQ = Q.carrier :=
    comapQuot_map N J (maxJ_isGraded N) (maxJ_bottom_disjoint N) Q
  by_cases hbt : Q'.carrier ⊓ N.weight h = ⊥
  · left
    have hle : Q'.carrier ≤ J.carrier := maxJ_dom N ⟨Q', hQ'_graded, hbt⟩
    have hQ'eq : Q'.carrier = J.carrier := le_antisymm hle hQ'_ge
    rw [← hmap, hQ'eq, eq_bot_iff, Submodule.map_le_iff_le_comap, Submodule.comap_bot,
      Submodule.ker_mkQ]
  · right
    rw [← hmap, bottom_regen hgen hirr Q' hbt, Submodule.map_top, Submodule.range_mkQ]

/-- `L` is nontrivial: its bottom is nonzero. -/
theorem LU_nontrivial : Nontrivial (M ⧸ (maxJ N).carrier) := by
  have hne : (LU N).weight h ≠ ⊥ := (LU N).realized
  rw [Submodule.ne_bot_iff] at hne
  obtain ⟨y, _, hy0⟩ := hne
  exact ⟨⟨y, 0, hy0⟩⟩

/-- **Irreducibility of a graded weak module**, the finrank-free mirror of
`OrdVModule.IsIrreducible`. -/
def IsIrreducible (N : GradedLWWeakModule W M h) : Prop :=
  Nontrivial M ∧ ∀ Q : WeakModule.Submodule' N.toWeakModule, Q.carrier = ⊥ ∨ Q.carrier = ⊤

/-- **`L = M/J` IS IRREDUCIBLE.**  Every weak submodule of `L` is graded by `L₀`-semisimplicity
(§1, no finiteness), hence `⊥` or `⊤` by `LU_graded_simple`.  Carried inputs: exactly
`GeneratedByBottom N` and `BottomIrreducible N`.

⚠ This is *not* DLM3's Lemma 4.8 argument, which deduces simplicity from complete reducibility of
`M(U)` and is valid only for **rational** `V`.  No rationality, no complete reducibility, no
finite-dimensionality is used here. -/
theorem LU_isIrreducible (hgen : GeneratedByBottom N) (hirr : BottomIrreducible N) :
    IsIrreducible (LU N) := by
  classical
  letI instN := DirectSum.IsInternal.chooseDecomposition N.weight N.isInternal
  letI instL := DirectSum.IsInternal.chooseDecomposition (LU N).weight (LU N).isInternal
  refine ⟨LU_nontrivial, fun Q => ?_⟩
  exact LU_graded_simple instN instL hgen hirr Q (submodule_isGraded (LU N) Q)

variable (N)

/-- **Every bottom-trivial weak submodule is contained in `J`** — no gradedness hypothesis, because
`L₀`-semisimplicity (§1) supplies it.  unconditional. -/
theorem le_maxJ_of_bottom_disjoint [DirectSum.Decomposition N.weight]
    (K : WeakModule.Submodule' N.toWeakModule) (hK : K.carrier ⊓ N.weight h = ⊥) :
    K.carrier ≤ (maxJ N).carrier :=
  maxJ_dom N ⟨K, submodule_isGraded N K, hK⟩

/-- `J` is a proper submodule (it misses the — nonzero — bottom). -/
theorem maxJ_ne_top : (maxJ N).carrier ≠ ⊤ := by
  intro htop
  refine N.realized ?_
  have := maxJ_bottom_disjoint N
  rwa [htop, top_inf_eq] at this

/-- **Uniqueness of the irreducible quotient.**  A bottom-trivial weak submodule `K` that is
*maximal* among proper weak submodules — exactly the situation when `M/K` is irreducible — **is**
`J`.  Hence `M/K = L`: the irreducible quotient of `M` with surviving bottom is unique.
unconditional.

This is the abstract half of "every irreducible lowest-weight module `P` equals `L(P_h)`": given a
surjection `M(P_h) ↠ P` that is injective on the bottom (the universal property of the generalized
Verma module), its kernel is bottom-trivial and maximal, hence is `J(P_h)`, so `P = L(P_h)`. -/
theorem eq_maxJ_of_maximal [DirectSum.Decomposition N.weight]
    (K : WeakModule.Submodule' N.toWeakModule) (hK : K.carrier ⊓ N.weight h = ⊥)
    (hmax : ∀ Q : WeakModule.Submodule' N.toWeakModule, K.carrier ≤ Q.carrier →
      Q.carrier = K.carrier ∨ Q.carrier = ⊤) :
    K.carrier = (maxJ N).carrier := by
  rcases hmax (maxJ N) (le_maxJ_of_bottom_disjoint N K hK) with hcase | hcase
  · exact hcase.symm
  · exact absurd hcase (maxJ_ne_top N)

/-- **The bottom of `L` is the bottom of `M`.**  `mkQ` is injective on `M_h` because
`J ⊓ M_h = ⊥`, and its image is `L_h` by definition of the quotient grading.  unconditional — this
is "`L(U)(0) = U`" once `M_h` has been identified with `U`. -/
noncomputable def LU_bottom_equiv : N.weight h ≃ₗ[ℂ] (LU N).weight h := by
  classical
  set f : N.weight h →ₗ[ℂ] M ⧸ (maxJ N).carrier :=
    (maxJ N).carrier.mkQ.comp (N.weight h).subtype with hf
  have hker : LinearMap.ker f = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz0 : ((z : M)) ∈ (maxJ N).carrier := by
      have : (maxJ N).carrier.mkQ (z : M) = 0 := hz
      exact (Submodule.Quotient.mk_eq_zero _).mp this
    have hmem : (z : M) ∈ (maxJ N).carrier ⊓ N.weight h := Submodule.mem_inf.mpr ⟨hz0, z.2⟩
    rw [maxJ_bottom_disjoint N] at hmem
    exact Submodule.mem_bot _ |>.mpr (Subtype.ext (Submodule.mem_bot _ |>.mp hmem))
  have hrange : LinearMap.range f = (LU N).weight h := by
    rw [LU_weight]
    refine le_antisymm ?_ ?_
    · rintro _ ⟨z, rfl⟩
      exact Submodule.mem_map_of_mem z.2
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  exact (LinearEquiv.ofInjective f (LinearMap.ker_eq_bot.mp hker)).trans
    (LinearEquiv.ofEq _ _ hrange)

@[simp] theorem LU_bottom_equiv_coe (z : N.weight h) :
    ((LU_bottom_equiv N z : (LU N).weight h) : M ⧸ (maxJ N).carrier)
      = Submodule.Quotient.mk (z : M) := rfl

/-- Every bottom vector of `L` is the class of a bottom vector of `M`. -/
theorem LU_bottom_equiv_symm_coe (y : (LU N).weight h) :
    (y : M ⧸ (maxJ N).carrier)
      = Submodule.Quotient.mk ((((LU_bottom_equiv N).symm y : N.weight h)) : M) := by
  rw [← LU_bottom_equiv_coe N ((LU_bottom_equiv N).symm y), LinearEquiv.apply_symm_apply]

/-- Recognising `(LU_bottom_equiv N).symm`: a bottom vector of `L` whose class comes from `z` has
`z` as its preimage. -/
theorem LU_bottom_equiv_symm_eq (z : N.weight h) (y : (LU N).weight h)
    (hy : (y : M ⧸ (maxJ N).carrier) = Submodule.Quotient.mk (z : M)) :
    (LU_bottom_equiv N).symm y = z := by
  have hz : LU_bottom_equiv N z = y := Subtype.ext (by rw [LU_bottom_equiv_coe, ← hy])
  rw [← hz, LinearEquiv.symm_apply_apply]

end LU

end GradedLWWeakModule

end VOA
