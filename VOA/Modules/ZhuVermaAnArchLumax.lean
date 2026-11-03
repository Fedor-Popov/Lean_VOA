/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchHoleF
import VOA.Modules.ZhuVermaAnArchHoleG

/-!
# LUMAX — the maximal bottom-trivial graded `J` of `M(U)` (Gannon Thm 5.3.4)

`Modules.ZhuVermaAnArchHoleF` reduced the per-`U` `L(U) = M(U)/J` datum to the finer input
`MUModuleData.LUMaxData` (Gannon Thm 5.3.4's three genuine ingredients: a graded submodule `J`
meeting the bottom trivially, graded simplicity of the quotient, and weak-submodule-gradedness of
the quotient).  `holeF` then needs, per bottom `U`, a term
`lumax : ∀ U, MUModuleData.LUMaxData (R.mudata U)`.

This file **builds that `lumax`**, following the published argument of Gannon Thm 5.3.4 / Dong–Jiang
§4 (`math/0601626`): the maximal `J` is the **supremum of all bottom-trivial graded submodules** of
`M(U)`, and the irreducible quotient `L(U) = M(U)/J` is graded-simple by maximality of `J` together
with generation-from-bottom.

## The published argument (Gannon Thm 5.3.4, injective half)

Let `M = M(U)` be the generalized-Verma module (a `ℕ`-graded admissible `V`-module, lowest weight
`h`, bottom `M_h`).  Let

  `J := ⨆ { Q | Q a graded submodule with Q ⊓ M_h = ⊥ }`

be the supremum of all bottom-trivial graded submodules.  Then:

* **`J` is graded.**  A supremum of graded submodules is graded (`supBotTrivialGraded_isGraded`):
  gradedness `Q = ⨆_α (Q ⊓ M_α)` is preserved by `⨆`, since `Q_i ⊓ M_α ≤ (⨆_i Q_i) ⊓ M_α`.
* **`J ⊓ M_h = ⊥`** (`bottom_disjoint`).  The supremum of bottom-trivial graded submodules is again
  bottom-trivial — this is the genuine finiteness/structure content of Gannon Thm 5.3.4, carried
  here as the field `MaxJData.sup_bottom_disjoint` (the deep residue, never an axiom).
* **graded simplicity** (`quot_graded_simple`).  A nonzero graded submodule `Q̄` of `M/J` pulls back
  to a graded submodule `Q ⊋ J` of `M`.  If `Q ⊓ M_h = ⊥` then `Q` is bottom-trivial graded, so
  `Q ≤ J` (supremum), contradicting `Q ⊋ J`; hence `Q ⊓ M_h ≠ ⊥`, and by **bottom regeneration**
  (`MaxJData.bottom_regen`: any graded submodule meeting the bottom nontrivially is all of `M(U)` —
  the bottom-`A(𝒱)`-irreducibility + generation-from-bottom content) `Q = ⊤`, so `Q̄ = ⊤`.
* **weak-submodule-gradedness** (`quot_submodule_graded`).  Every weak submodule of `M/J` is graded
  — the standard `ℕ`-graded / finite-piece `L₀`-stability fact, carried as
  `MaxJData.quot_submodule_graded`.

## What is constructed (axiom-clean, no `sorry`, no `pbw`, no `fzRhoMU`/`FZModeDescent`)

* **`MUModuleData.supBotTrivialGraded`** — the carrier-level supremum `J` of all bottom-trivial
  graded submodules, as a `WeakModule.Submodule'` (closure under modes via `Submodule.iSup_induction`).
* **`MUModuleData.supBotTrivialGraded_isGraded`** — `J` is graded (a supremum of graded submodules).
* **`MUModuleData.supBotTrivialGraded_dom`** — every bottom-trivial graded submodule is `≤ J`.
* **`MUModuleData.comapQuotSub`** — the pullback of a quotient weak submodule `Q̄ ⊆ M/J` to a weak
  submodule `Q ⊆ M` containing `J` (via `comap mkQ`, using `quotient_action_mk`).
* **`MUModuleData.MaxJData`** — the genuine per-`U` deep residue of Gannon Thm 5.3.4: the bottom
  regeneration `bottom_regen`, the supremum bottom-disjointness `sup_bottom_disjoint`, and the
  quotient weak-submodule-gradedness `quot_submodule_graded`.  A hypothesis structure, never an axiom.
* **`MUModuleData.MaxJData.toLUMaxData`** — the full `LUMaxData` as a TERM off `MaxJData`, with
  `J := supBotTrivialGraded`, `J_graded` and `quot_graded_simple` **proved**, `bottom_disjoint` and
  `quot_submodule_graded` discharged from the carried residue.
* **`InducedAssignment.MURepFamily.lumax`** — the per-`U` `LUMaxData` feeding `holeF`, assembled from
  a per-`U` `MaxJData` family `maxJ : ∀ U, MaxJData (R.mudata U)`.
* **`InducedAssignment.MURepFamily.holeFofMaxJ`** — `holeF R (R.lumax maxJ) : LUFamily W`, the HOLE-F
  family produced from `R` and the maximal-`J` residue, closing the `lumax` slot.

## The exact remaining inputs (honest residual)

`lumax` is **not** unconditional.  It rests on exactly the per-`U` `MaxJData (R.mudata U)`:

* `bottom_regen` — bottom `A(𝒱)`-irreducibility + generation-from-bottom: any graded submodule of
  `M(U)` meeting the bottom `M(U)_h` nontrivially is all of `M(U)`.  (Gannon Thm 5.3.4 / DJ Thm 4.13
  generation, specialized to the bottom-simple `U`.)
* `sup_bottom_disjoint` — the supremum of all bottom-trivial graded submodules still meets the bottom
  trivially (the finiteness/structure content that the maximal proper graded `J` is itself bottom-
  trivial).
* `quot_submodule_graded` — every weak submodule of `M(U)/J` is graded (the standard `ℕ`-graded
  finite-piece `L₀`-stability fact).

No fresh mathematical reduction is invented: `J = supBotTrivialGraded` is the literal Gannon-5.3.4
maximal `J`, `J_graded` and `quot_graded_simple` are proved from the supremum construction plus the
carried `bottom_regen`, and the two carried structural facts are the genuine Gannon-5.3.4 residue.

## References
Gannon §5.3.1–§5.3.2, Def. 5.3.1, Thm 5.3.4 (injective half); Dong–Jiang, Math. Z. 259 (2008)
(`math/0601626`), §4: Thm 4.13, Prop 4.6; DLM3 §4; Zhu [574]; Frenkel–Zhu.
`ZhuVermaAnArchHoleF` (`MUModuleData.LUMaxData`, `holeF`); `ZhuVermaAnArchHoleG`
(`bottom_generates`, `generatedSub`); `ZhuVermaAnArchGameTwo` (`MUModuleData.LUData`);
`ZhuVermaAnArchVModQuotGraded` (`IsGradedSubmodule`, `quotient`); `ZhuVermaAnArchVModQuot`
(`quotient_action_mk`).
-/

namespace VOA

open scoped BigOperators
open VertexOperatorAlgebra

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace OrdVModule

variable {M : Type v} [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra 𝒱}

/-! ## Weight-components of a graded weak submodule

For an internally `ℂ`-graded `OrdVModule` `N` and a **graded** weak submodule `P = ⨆_α (P ⊓ N_α)`,
every weight-component of an element of `P` is itself in `P`.  This is the uniqueness of the
internal decomposition: writing `y ∈ P` as `∑_α q_α` with `q_α ∈ P ⊓ N_α ⊆ N_α`, the `β`-component
`(decompose N.weight y) β` of `y` equals `q_β ∈ P`. -/

/-- **Each weight-component of an element of a graded submodule stays in the submodule.**
If `P` is graded (`P = ⨆_α (P ⊓ N_α)`) and `y ∈ P`, then for every `α` the homogeneous component
`(DirectSum.decompose N.weight y α : M) ∈ P.carrier`.  The decomposition instance is the one
synthesized from `N.isInternal` (passed explicitly to avoid an instance mismatch). -/
theorem component_mem_of_graded (N : OrdVModule W M)
    [inst : DirectSum.Decomposition N.weight]
    (P : WeakModule.Submodule' N.toWeakModule) (hP : IsGradedSubmodule N P)
    {y : M} (hy : y ∈ P.carrier) (α : ℂ) :
    ((DirectSum.decompose N.weight y α : N.weight α) : M) ∈ P.carrier := by
  classical
  -- `y ∈ P = ⨆_α (P ⊓ N_α)`; expand by `iSup_induction` into a sum of homogeneous `P`-pieces.
  rw [hP] at hy
  refine Submodule.iSup_induction (fun α : ℂ => P.carrier ⊓ N.weight α) hy
    (motive := fun z => ((DirectSum.decompose N.weight z α : N.weight α) : M) ∈ P.carrier)
    (fun β z hz => ?_) ?_ (fun z w hz hw => ?_)
  · -- `z ∈ P ⊓ N_β` is homogeneous of weight `β`: its `α`-component is `z` (if `α=β`) else `0`.
    simp only
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

end OrdVModule

namespace MUModuleData

variable {W : VertexOperatorAlgebra 𝒱} {U : AMod W} {h : ℂ}

/-! ## The supremum of all bottom-trivial graded submodules -/

/-- **A bottom-trivial graded submodule of `M(U)`** — the index data for the supremum `J`: a weak
submodule `Q` that is graded (`IsGradedSubmodule`) and meets the bottom `M(U)_h` trivially. -/
structure BotTrivialGraded (D : MUModuleData W U h) where
  /-- The underlying weak submodule. -/
  Q : WeakModule.Submodule' D.toOrdVModule.toWeakModule
  /-- `Q` is graded (homogeneous / `L₀`-stable). -/
  Q_graded : OrdVModule.IsGradedSubmodule D.toOrdVModule Q
  /-- `Q` meets the bottom weight space trivially. -/
  Q_disjoint : Q.carrier ⊓ D.toOrdVModule.weight h = ⊥

/-- **The maximal bottom-trivial graded submodule `J`** of `M(U)`, as a `WeakModule.Submodule'`:
the supremum (over the index type `BotTrivialGraded D`) of the carriers of all bottom-trivial graded
submodules.  Closure under each mode `u₍ₙ₎` follows from `Submodule.iSup_induction` (each summand is
mode-closed, the action is additive and `0`-preserving).  This is the literal Gannon-Thm-5.3.4
maximal `J`. -/
noncomputable def supBotTrivialGraded (D : MUModuleData W U h) :
    WeakModule.Submodule' D.toOrdVModule.toWeakModule where
  carrier := ⨆ T : BotTrivialGraded D, T.Q.carrier
  act_mem := by
    intro u n x hx
    refine Submodule.iSup_induction (fun T : BotTrivialGraded D => T.Q.carrier) hx
      (motive := fun y => D.toOrdVModule.toWeakModule.act u n y ∈ ⨆ T : BotTrivialGraded D, T.Q.carrier)
      (fun T y hy => ?_) ?_ (fun y z hy hz => ?_)
    · exact Submodule.mem_iSup_of_mem T (T.Q.act_mem u n hy)
    · simp only [WeakModule.act_zero_right]; exact Submodule.zero_mem _
    · simp only [WeakModule.act_add_right]; exact Submodule.add_mem _ hy hz

/-- Every bottom-trivial graded submodule is `≤ J` (the supremum dominates each summand). -/
theorem supBotTrivialGraded_dom (D : MUModuleData W U h) (T : BotTrivialGraded D) :
    T.Q.carrier ≤ (D.supBotTrivialGraded).carrier :=
  le_iSup (fun T : BotTrivialGraded D => T.Q.carrier) T

/-- **`J` is graded.**  A supremum of graded submodules is graded:
`J = ⨆_T Q_T = ⨆_T ⨆_α (Q_T ⊓ M_α) ≤ ⨆_α (J ⊓ M_α)` (since `Q_T ⊓ M_α ≤ J ⊓ M_α`), and the reverse
`⨆_α (J ⊓ M_α) ≤ J` is automatic. -/
theorem supBotTrivialGraded_isGraded (D : MUModuleData W U h) :
    OrdVModule.IsGradedSubmodule D.toOrdVModule D.supBotTrivialGraded := by
  apply le_antisymm
  · -- `J ≤ ⨆_α (J ⊓ M_α)`.
    change (⨆ T : BotTrivialGraded D, T.Q.carrier)
        ≤ ⨆ α : ℂ, ((D.supBotTrivialGraded).carrier ⊓ D.toOrdVModule.weight α)
    refine iSup_le (fun T => ?_)
    -- `Q_T = ⨆_α (Q_T ⊓ M_α)` (graded), each `Q_T ⊓ M_α ≤ J ⊓ M_α`.
    rw [T.Q_graded]
    refine iSup_le (fun α => ?_)
    refine le_iSup_of_le α ?_
    exact inf_le_inf_right _ (D.supBotTrivialGraded_dom T)
  · -- `⨆_α (J ⊓ M_α) ≤ J`.
    exact iSup_le (fun α => inf_le_left)

/-! ## Pulling a quotient weak submodule back to `M(U)`

For graded `J` (here `J := supBotTrivialGraded`), the quotient `M(U)/J` is a graded `OrdVModule`
(`OrdVModule.quotient`).  A weak submodule `Q̄ ⊆ M(U)/J` pulls back to the weak submodule
`Q := comap mkQ Q̄ ⊆ M(U)`, which contains `J` (as `mkQ` kills `J`); closure under modes uses the
intertwining `quotient_action_mk`: `mode (Y_{M/J} a) k ⟦x⟧ = ⟦mode (Y_M a) k x⟧`. -/

/-- **The pullback of a quotient weak submodule to `M(U)`.**  For a graded `J` and a weak submodule
`Q̄ ⊆ M(U)/J`, the comap `comap mkQ Q̄` is a weak submodule of `M(U)`; mode-closure descends from the
intertwining `quotient_action_mk` (the descended action commutes with the projection `mkQ`). -/
noncomputable def comapQuotSub (D : MUModuleData W U h)
    (J : WeakModule.Submodule' D.toOrdVModule.toWeakModule)
    (J_graded : OrdVModule.IsGradedSubmodule D.toOrdVModule J)
    (Q : WeakModule.Submodule' (OrdVModule.quotient D.toOrdVModule J J_graded).toWeakModule) :
    WeakModule.Submodule' D.toOrdVModule.toWeakModule where
  carrier := Q.carrier.comap J.carrier.mkQ
  act_mem := by
    intro u n x hx
    simp only [Submodule.mem_comap, Submodule.mkQ_apply] at hx ⊢
    -- `mkQ (a₍ₙ₎ x) = a₍ₙ₎ (mkQ x)` in the quotient, which is in `Q̄` by `Q̄.act_mem`.
    have hcomm :
        Submodule.Quotient.mk (D.toOrdVModule.toWeakModule.act u n x)
          = (OrdVModule.quotient D.toOrdVModule J J_graded).toWeakModule.act u n
              (Submodule.Quotient.mk x) :=
      (WeakModule.quotient_act_mk D.toOrdVModule.toWeakModule J u n x).symm
    rw [hcomm]
    exact Q.act_mem u n hx

@[simp] theorem comapQuotSub_carrier (D : MUModuleData W U h)
    (J : WeakModule.Submodule' D.toOrdVModule.toWeakModule)
    (J_graded : OrdVModule.IsGradedSubmodule D.toOrdVModule J)
    (Q : WeakModule.Submodule' (OrdVModule.quotient D.toOrdVModule J J_graded).toWeakModule) :
    (D.comapQuotSub J J_graded Q).carrier = Q.carrier.comap J.carrier.mkQ := rfl

/-- The pullback **contains `J`** (`J = ker mkQ ⊆ comap mkQ Q̄`). -/
theorem comapQuotSub_ge (D : MUModuleData W U h)
    (J : WeakModule.Submodule' D.toOrdVModule.toWeakModule)
    (J_graded : OrdVModule.IsGradedSubmodule D.toOrdVModule J)
    (Q : WeakModule.Submodule' (OrdVModule.quotient D.toOrdVModule J J_graded).toWeakModule) :
    J.carrier ≤ (D.comapQuotSub J J_graded Q).carrier := by
  rw [comapQuotSub_carrier]
  intro x hx
  simp only [Submodule.mem_comap, Submodule.mkQ_apply]
  rw [(Submodule.Quotient.mk_eq_zero J.carrier).mpr hx]
  exact Submodule.zero_mem _

/-- **The pullback of a graded quotient submodule is graded.**  For graded `J` and a **graded** weak
submodule `Q̄ ⊆ M(U)/J`, the pullback `comap mkQ Q̄` is graded in `M(U)`.

The `≥` direction is automatic; for `≤`, decompose `x` (with `mkQ x ∈ Q̄`) into its `M(U)`-weight
components `c_α = decompose M.weight x α ∈ M_α`.  Since `mkQ x = ∑_α mkQ c_α` with
`mkQ c_α ∈ (M/J)_α` (the image grading), the `(M/J)`-component of `mkQ x` at `α` is `mkQ c_α`
(`DirectSum.decompose_sum` + `decompose_of_mem`); as `Q̄` is graded, `mkQ c_α ∈ Q̄`
(`component_mem_of_graded`), so `c_α ∈ comap mkQ Q̄ ⊓ M_α`, and `x = ∑_α c_α` lands in the sum. -/
theorem comapQuotSub_isGraded (D : MUModuleData W U h)
    (J : WeakModule.Submodule' D.toOrdVModule.toWeakModule)
    (J_graded : OrdVModule.IsGradedSubmodule D.toOrdVModule J)
    (Q : WeakModule.Submodule' (OrdVModule.quotient D.toOrdVModule J J_graded).toWeakModule)
    (hQ : OrdVModule.IsGradedSubmodule (OrdVModule.quotient D.toOrdVModule J J_graded) Q) :
    OrdVModule.IsGradedSubmodule D.toOrdVModule (D.comapQuotSub J J_graded Q) := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition D.toOrdVModule.weight D.toOrdVModule.isInternal
  letI := DirectSum.IsInternal.chooseDecomposition
    (OrdVModule.quotient D.toOrdVModule J J_graded).weight
    (OrdVModule.quotient D.toOrdVModule J J_graded).isInternal
  apply le_antisymm
  · -- `comap mkQ Q̄ ≤ ⨆_α (comap mkQ Q̄ ⊓ M_α)`.
    intro x hx
    have hxQ : (Submodule.Quotient.mk x : MU W U ⧸ J.carrier) ∈ Q.carrier := hx
    -- `x = ∑_{β ∈ s} c β`, `c β ∈ M_β`.
    set c : ℂ → MU W U :=
      fun β => ((DirectSum.decompose D.toOrdVModule.weight x β : D.toOrdVModule.weight β) : MU W U)
      with hc
    set s : Finset ℂ := (DirectSum.decompose D.toOrdVModule.weight x).support with hs
    have hcmem : ∀ β, c β ∈ D.toOrdVModule.weight β :=
      fun β => (DirectSum.decompose D.toOrdVModule.weight x β).2
    have hdecomp : (∑ β ∈ s, c β) = x := DirectSum.sum_support_decompose D.toOrdVModule.weight x
    -- `mkQ (c β) ∈ (M/J)_β = map mkQ (M_β)` for each `β`.
    have hcβ_q : ∀ β : ℂ, (Submodule.Quotient.mk (c β) : MU W U ⧸ J.carrier)
        ∈ (OrdVModule.quotient D.toOrdVModule J J_graded).weight β := by
      intro β
      rw [OrdVModule.quotient_weight]; exact Submodule.mem_map_of_mem (hcmem β)
    -- Each `mkQ (c β) ∈ Q̄`: it is the `β`-component of `mkQ x ∈ Q̄` (graded).
    have hmkc : ∀ β : ℂ, (Submodule.Quotient.mk (c β) : MU W U ⧸ J.carrier) ∈ Q.carrier := by
      intro β
      -- The `β`-component of `mkQ x = ∑_γ mkQ (c γ)` is `mkQ (c β)`.
      have hcomp : ((DirectSum.decompose (OrdVModule.quotient D.toOrdVModule J J_graded).weight
          (Submodule.Quotient.mk x : MU W U ⧸ J.carrier) β :
            (OrdVModule.quotient D.toOrdVModule J J_graded).weight β) : MU W U ⧸ J.carrier)
          = Submodule.Quotient.mk (c β) := by
        have hsum : (Submodule.Quotient.mk x : MU W U ⧸ J.carrier)
            = ∑ γ ∈ s, Submodule.Quotient.mk (c γ) := by
          conv_lhs => rw [← hdecomp]
          rw [← Submodule.mkQ_apply, map_sum]
          exact Finset.sum_congr rfl (fun γ _ => (Submodule.mkQ_apply _ _))
        rw [hsum, DirectSum.decompose_sum]
        rw [show (∑ i ∈ s, DirectSum.decompose (OrdVModule.quotient D.toOrdVModule J J_graded).weight
              (Submodule.Quotient.mk (c i))) β
            = ∑ i ∈ s, DirectSum.decompose (OrdVModule.quotient D.toOrdVModule J J_graded).weight
              (Submodule.Quotient.mk (c i)) β from DFinsupp.finsetSum_apply s _ β]
        rw [AddSubmonoidClass.coe_finsetSum]
        rw [Finset.sum_eq_single β]
        · rw [DirectSum.decompose_of_mem_same _ (hcβ_q β)]
        · intro γ _ hγβ
          rw [DirectSum.decompose_of_mem _ (hcβ_q γ),
            DirectSum.of_eq_of_ne _ _ _ (Ne.symm hγβ), ZeroMemClass.coe_zero]
        · intro hβs
          -- if `β ∉ s` then `c β = 0`, so `mkQ (c β) = 0` and the single term is `0` too.
          have hcβ0 : (Submodule.Quotient.mk (c β) : MU W U ⧸ J.carrier) = 0 := by
            have : c β = 0 := by
              rw [hc]; simp only
              rw [show DirectSum.decompose D.toOrdVModule.weight x β = 0 from by
                rw [← DFinsupp.notMem_support_iff]; exact hβs, ZeroMemClass.coe_zero]
            rw [this, Submodule.Quotient.mk_zero]
          rw [DirectSum.decompose_of_mem _ (hcβ_q β), DirectSum.of_eq_same]
          exact hcβ0
      -- So `mkQ (c β) = (β-component of mkQ x) ∈ Q̄` (graded).
      rw [← hcomp]
      exact OrdVModule.component_mem_of_graded
        (OrdVModule.quotient D.toOrdVModule J J_graded) Q hQ hxQ β
    -- Hence each `c β ∈ comap mkQ Q̄ ⊓ M_β`, and `x = ∑ c β` lands in the sum.
    rw [← hdecomp]
    refine Submodule.sum_mem _ (fun β _ => ?_)
    refine Submodule.mem_iSup_of_mem β ?_
    refine Submodule.mem_inf.mpr ⟨?_, hcmem β⟩
    rw [comapQuotSub_carrier]; exact hmkc β
  · exact iSup_le (fun α => inf_le_left)

/-! ## `MaxJData` — the genuine Gannon-5.3.4 deep residue, and the full `LUMaxData` as a term -/

/-- **The genuine per-`U` deep residue of Gannon Thm 5.3.4** for the maximal bottom-trivial graded
`J := supBotTrivialGraded`.  Three ingredients, the literal content of the published proof, carried
as hypotheses (never axioms):

* `bottom_regen` — **bottom regeneration** (`A(𝒱)`-bottom-irreducibility + generation-from-bottom):
  any graded submodule of `M(U)` meeting the bottom `M(U)_h` nontrivially is all of `M(U)`.  This is
  Gannon Thm 5.3.4 / DJ Thm 4.13's generation specialized to the bottom-simple `U`.
* `sup_bottom_disjoint` — the supremum of all bottom-trivial graded submodules is itself bottom-
  trivial (`J ⊓ M(U)_h = ⊥`): the finiteness/structure content that the maximal proper graded `J`
  meets the bottom in `0`.
* `quot_submodule_graded` — every **weak** submodule of `M(U)/J` is graded (the standard
  `ℕ`-graded / finite-piece `L₀`-stability fact).

From these the full `LUMaxData` is built as a TERM (`toLUMaxData`): `J := supBotTrivialGraded`,
`J_graded` and `quot_graded_simple` are *proved*, and `bottom_disjoint`/`quot_submodule_graded` are
the carried fields. -/
structure MaxJData (D : MUModuleData W U h) where
  /-- **Bottom regeneration.**  A graded submodule meeting the bottom nontrivially is all of
  `M(U)`. -/
  bottom_regen : ∀ Q : WeakModule.Submodule' D.toOrdVModule.toWeakModule,
    OrdVModule.IsGradedSubmodule D.toOrdVModule Q →
      Q.carrier ⊓ D.toOrdVModule.weight h ≠ ⊥ → Q.carrier = ⊤
  /-- The supremum of all bottom-trivial graded submodules is itself bottom-trivial. -/
  sup_bottom_disjoint : (D.supBotTrivialGraded).carrier ⊓ D.toOrdVModule.weight h = ⊥
  /-- Every weak submodule of the quotient `M(U)/J` is graded. -/
  quot_submodule_graded :
    ∀ Q : WeakModule.Submodule'
        (OrdVModule.quotient D.toOrdVModule D.supBotTrivialGraded
          D.supBotTrivialGraded_isGraded).toWeakModule,
      OrdVModule.IsGradedSubmodule
        (OrdVModule.quotient D.toOrdVModule D.supBotTrivialGraded
          D.supBotTrivialGraded_isGraded) Q

namespace MaxJData

variable {D : MUModuleData W U h}

/-- **Graded simplicity of `M(U)/J` from maximality + bottom regeneration.**  A nonzero graded weak
submodule `Q̄ ⊆ M(U)/J` pulls back (`comapQuotSub`) to a graded submodule `Q ⊇ J` of `M(U)`.  If
`Q ⊓ M(U)_h = ⊥` then `Q` is bottom-trivial graded, so `Q ≤ J = supBotTrivialGraded`, forcing
`Q = J` and `Q̄ = ⊥`; otherwise `bottom_regen` gives `Q = ⊤`, hence `Q̄ = ⊤`.  This is the maximal-`J`
content of Gannon Thm 5.3.4. -/
theorem quot_graded_simple (data : MaxJData D)
    (Q : WeakModule.Submodule'
      (OrdVModule.quotient D.toOrdVModule D.supBotTrivialGraded
        D.supBotTrivialGraded_isGraded).toWeakModule)
    (hQ : OrdVModule.IsGradedSubmodule
      (OrdVModule.quotient D.toOrdVModule D.supBotTrivialGraded
        D.supBotTrivialGraded_isGraded) Q) :
    Q.carrier = ⊥ ∨ Q.carrier = ⊤ := by
  -- The pullback `Q' := comap mkQ Q̄` is a graded submodule of `M(U)` containing `J`.
  have hQ'_graded : OrdVModule.IsGradedSubmodule D.toOrdVModule
      (D.comapQuotSub D.supBotTrivialGraded D.supBotTrivialGraded_isGraded Q) :=
    D.comapQuotSub_isGraded D.supBotTrivialGraded D.supBotTrivialGraded_isGraded Q hQ
  have hQ'_ge : (D.supBotTrivialGraded).carrier ≤
      (D.comapQuotSub D.supBotTrivialGraded D.supBotTrivialGraded_isGraded Q).carrier :=
    D.comapQuotSub_ge D.supBotTrivialGraded D.supBotTrivialGraded_isGraded Q
  -- `map mkQ Q'.carrier = Q̄.carrier` (mkQ surjective).
  have hmap : (D.comapQuotSub D.supBotTrivialGraded D.supBotTrivialGraded_isGraded Q).carrier.map
      (D.supBotTrivialGraded).carrier.mkQ = Q.carrier := by
    rw [comapQuotSub_carrier]
    exact Submodule.map_comap_eq_of_surjective (D.supBotTrivialGraded).carrier.mkQ_surjective
      Q.carrier
  by_cases hbt : (D.comapQuotSub D.supBotTrivialGraded D.supBotTrivialGraded_isGraded Q).carrier
      ⊓ D.toOrdVModule.weight h = ⊥
  · -- `Q'` is bottom-trivial graded, so `Q' ≤ J`, hence `Q' = J` and `Q̄ = map mkQ J = ⊥`.
    left
    have hle : (D.comapQuotSub D.supBotTrivialGraded D.supBotTrivialGraded_isGraded Q).carrier
        ≤ (D.supBotTrivialGraded).carrier :=
      D.supBotTrivialGraded_dom ⟨_, hQ'_graded, hbt⟩
    have hQ'eq : (D.comapQuotSub D.supBotTrivialGraded D.supBotTrivialGraded_isGraded Q).carrier
        = (D.supBotTrivialGraded).carrier := le_antisymm hle hQ'_ge
    rw [← hmap, hQ'eq]
    -- `map mkQ J = ⊥` (`J = ker mkQ`); `map_mkQ_eq_bot_iff` reduces to `J ≤ J`.
    rw [OrdVModule.map_mkQ_eq_bot_iff D.toOrdVModule D.supBotTrivialGraded]
  · -- `Q' ⊓ bottom ≠ ⊥`, so by regeneration `Q' = ⊤`, hence `Q̄ = map mkQ ⊤ = ⊤`.
    right
    have hQ'top : (D.comapQuotSub D.supBotTrivialGraded D.supBotTrivialGraded_isGraded Q).carrier
        = ⊤ := data.bottom_regen _ hQ'_graded hbt
    rw [← hmap, hQ'top, Submodule.map_top, Submodule.range_mkQ]

/-- **`MaxJData → LUMaxData` as a TERM** (Gannon Thm 5.3.4).  The maximal bottom-trivial graded
`J := supBotTrivialGraded` with its proved gradedness, the carried bottom-disjointness, the proved
graded simplicity, and the carried weak-submodule-gradedness.  This is the full per-`U` `LUMaxData`
that `holeF` consumes. -/
noncomputable def toLUMaxData (data : MaxJData D) : MUModuleData.LUMaxData D where
  J := D.supBotTrivialGraded
  J_graded := D.supBotTrivialGraded_isGraded
  bottom_disjoint := data.sup_bottom_disjoint
  quot_submodule_graded := data.quot_submodule_graded
  quot_graded_simple := data.quot_graded_simple

@[simp] theorem toLUMaxData_J (data : MaxJData D) :
    data.toLUMaxData.J = D.supBotTrivialGraded := rfl

end MaxJData

end MUModuleData

/-! ## Assembling the per-`U` `lumax` and the HOLE-F family -/

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

namespace MURepFamily

variable (R : MURepFamily W)

/-- **The per-`U` `LUMaxData` family**, the `lumax` slot of `holeF`, assembled from a per-`U`
maximal-`J` residue `maxJ : ∀ U, MaxJData (R.mudata U)` (Gannon Thm 5.3.4).  Each `LUMaxData` is the
TERM `(maxJ U).toLUMaxData`, with `J := supBotTrivialGraded` and graded simplicity proved. -/
noncomputable def lumax (maxJ : ∀ U : AMod W, MUModuleData.MaxJData (R.mudata U)) :
    ∀ U : AMod W, MUModuleData.LUMaxData (R.mudata U) :=
  fun U => (maxJ U).toLUMaxData

/-- **HOLE F closed via the maximal-`J` residue.**  The per-`U` `L(U) = M(U)/J` family
`F : LUFamily W` produced from the Construction-A representation family `R` (DJ §4) together with
the per-`U` Gannon-5.3.4 maximal-`J` residue `maxJ`.  This is `holeF R (R.lumax maxJ)`, with the
genuine maximal `J := supBotTrivialGraded`. -/
noncomputable def holeFofMaxJ (maxJ : ∀ U : AMod W, MUModuleData.MaxJData (R.mudata U)) :
    LUFamily W :=
  holeF R (R.lumax maxJ)

@[simp] theorem holeFofMaxJ_eq (maxJ : ∀ U : AMod W, MUModuleData.MaxJData (R.mudata U)) :
    R.holeFofMaxJ maxJ = holeF R (R.lumax maxJ) := rfl

/-- `K U = L(U)` is irreducible for the maximal-`J` HOLE-F family (reusing
`holeF_K_isIrreducibleLW`, hence `GameTwo`'s `LU_irreducible`). -/
theorem holeFofMaxJ_K_isIrreducibleLW
    (maxJ : ∀ U : AMod W, MUModuleData.MaxJData (R.mudata U)) (U : AMod W) :
    ((R.holeFofMaxJ maxJ).K U).IsIrreducibleLW :=
  holeF_K_isIrreducibleLW R (R.lumax maxJ) U

end MURepFamily

end InducedAssignment

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
