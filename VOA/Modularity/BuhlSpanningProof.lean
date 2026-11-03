/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.OrderedSpan

/-!
# The graded descent: sorted generator words span the whole module

`Modularity.OrderedSpan.master` gives `Gfil p ≤ ordSpanAll p ⊔ Gfil (p+1)` — sorted generator
words capture everything *modulo one filtration level*.  Since (`Gfil_inf_weight_eq_bot`) the
filtration exhausts each weight space, a **downward induction on the level** inside a fixed
weight space removes the error term entirely.

## Contents

* `wProj` — the weight-`α` projection as an endomorphism of `M`, and the fact that it preserves
  any span of homogeneous vectors (`wProj_mem_span`).
* **`weight_le_ordSpanAll`** — `M_{h+d} ≤ ordSpanAll 0` for every `d`.
* **`ordSpanAll_eq_top`** — `ordSpanAll 0 = ⊤`: the sorted generator words on the bottom
  set span `M`.  This is Karel–Li Thm 3.10 / Cor 3.12 in the repo's normal form.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## The weight projection as an endomorphism -/

/-- The weight-`α` projection of `M`, as an endomorphism. -/
noncomputable def wProj (N : OrdVModule W M) (α : ℂ) : Module.End ℂ M :=
  (N.weight α).subtype.comp (internalProjTo N.isInternal α)

theorem wProj_apply_mem (N : OrdVModule W M) (α : ℂ) (x : M) : wProj N α x ∈ N.weight α :=
  (internalProjTo N.isInternal α x).2

theorem wProj_of_mem (N : OrdVModule W M) {α : ℂ} {x : M} (hx : x ∈ N.weight α) :
    wProj N α x = x :=
  congrArg Subtype.val (internalProjTo_coe N.isInternal α ⟨x, hx⟩)

theorem wProj_of_mem_ne (N : OrdVModule W M) {α β : ℂ} {x : M} (hx : x ∈ N.weight β)
    (hne : α ≠ β) : wProj N α x = 0 := by
  show ((internalProjTo N.isInternal α x : N.weight α) : M) = 0
  rw [internalProjTo_eq_zero_of_ne' N hx hne, Submodule.coe_zero]

/-- The weight projection preserves any span of homogeneous vectors. -/
theorem wProj_mem_span (N : OrdVModule W M) (F : Set M) (hF : ∀ f ∈ F, ∃ β : ℂ, f ∈ N.weight β)
    (α : ℂ) {x : M} (hx : x ∈ Submodule.span ℂ F) : wProj N α x ∈ Submodule.span ℂ F := by
  refine Submodule.span_induction (p := fun x _ => wProj N α x ∈ Submodule.span ℂ F)
    ?_ ?_ ?_ ?_ hx
  · intro f hf
    obtain ⟨β, hβ⟩ := hF f hf
    by_cases hβα : α = β
    · subst hβα; rw [wProj_of_mem N hβ]; exact Submodule.subset_span hf
    · rw [wProj_of_mem_ne N hβ hβα]; exact Submodule.zero_mem _
  · simp only [map_zero]; exact Submodule.zero_mem _
  · intro y z _ _ hy hz; rw [map_add]; exact Submodule.add_mem _ hy hz
  · intro a y _ hy; rw [map_smul]; exact Submodule.smul_mem _ a hy

/-! ## Homogeneity of the two generating sets -/

theorem Gset_homog (N : OrdVModule W M) (B : Set M) (h : ℂ)
    (hB : ∀ w ∈ B, ∃ d₀ : ℕ, w ∈ N.weight (h + d₀)) (p : ℕ) :
    ∀ f ∈ Gset N.toWeakModule B p, ∃ β : ℂ, f ∈ N.weight β := by
  rintro f ⟨l, w, hl, hw, _, rfl⟩
  obtain ⟨d₀, hd₀⟩ := hB w hw
  exact ⟨_, wordAct_mem_weight N hl hd₀⟩

theorem wProj_mem_Gfil (N : OrdVModule W M) (B : Set M) (h : ℂ)
    (hB : ∀ w ∈ B, ∃ d₀ : ℕ, w ∈ N.weight (h + d₀)) (α : ℂ) {q : ℤ} {x : M}
    (hx : x ∈ Gfil N.toWeakModule B q) : wProj N α x ∈ Gfil N.toWeakModule B q :=
  wProj_mem_span N _ (Gset_homog N B h hB q.toNat) α hx

theorem ordSpanAllSet_homog (N : OrdVModule W M) (B : Set M) (h : ℂ)
    (hB : ∀ w ∈ B, ∃ d₀ : ℕ, w ∈ N.weight (h + d₀)) {g : ℕ} {gen : Fin g → 𝒱} {wt : Fin g → ℕ}
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ)) (p : ℕ) :
    ∀ f ∈ {x | ∃ (l : List (Fin g × ℕ)) (w : M), OrdPairs l ∧ p ≤ pairsLevel l ∧ w ∈ B ∧
      x = wordAct N.toWeakModule (genWord gen wt l) w}, ∃ β : ℂ, f ∈ N.weight β := by
  rintro f ⟨l, w, _, _, hw, rfl⟩
  obtain ⟨d₀, hd₀⟩ := hB w hw
  exact ⟨_, wordAct_mem_weight N (genWord_ok hgen l) hd₀⟩

theorem wProj_mem_ordSpanAll (N : OrdVModule W M) (B : Set M) (h : ℂ)
    (hB : ∀ w ∈ B, ∃ d₀ : ℕ, w ∈ N.weight (h + d₀)) {g : ℕ} {gen : Fin g → 𝒱} {wt : Fin g → ℕ}
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ)) (α : ℂ) {p : ℕ} {x : M}
    (hx : x ∈ ordSpanAll N.toWeakModule B gen wt p) :
    wProj N α x ∈ ordSpanAll N.toWeakModule B gen wt p :=
  wProj_mem_span N _ (ordSpanAllSet_homog N B h hB hgen p) α hx

/-! ## The downward induction -/

/-- **Every weight space is spanned by sorted generator words.**

Downward induction on the filtration level inside the fixed weight space `M_{h+d}`: the level
`d+1` piece already misses `M_{h+d}` (`Gfil_inf_weight_eq_bot`), and `master` moves one level at
a time, the error being reabsorbed by the inductive hypothesis after projecting to weight
`h + d`. -/
theorem weight_le_ordSpanAll (N : OrdVModule W M) (B : Set M) (h : ℂ)
    (hB : ∀ w ∈ B, ∃ d₀ : ℕ, w ∈ N.weight (h + d₀)) (hLW : LWGenerated N.toWeakModule B)
    {g : ℕ} {gen : Fin g → 𝒱} {wt : Fin g → ℕ} (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (hdec : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W)
    (d : ℕ) : N.weight (h + d) ≤ ordSpanAll N.toWeakModule B gen wt 0 := by
  have key : ∀ j : ℕ, N.weight (h + d) ⊓ Gfil N.toWeakModule B ((d + 1 - j : ℕ) : ℤ)
      ≤ ordSpanAll N.toWeakModule B gen wt 0 := by
    intro j
    induction j with
    | zero =>
        have hbot : Gfil N.toWeakModule B ((d + 1 - 0 : ℕ) : ℤ) ⊓ N.weight (h + d) = ⊥ :=
          Gfil_inf_weight_eq_bot N B h hB (by omega)
        rw [inf_comm, hbot]
        exact bot_le
    | succ j ih =>
        rcases le_or_gt j d with hj | hj
        · intro x hx
          obtain ⟨hxw, hxG⟩ := hx
          set p : ℕ := d + 1 - (j + 1) with hp
          have hcast : ((d + 1 - j : ℕ) : ℤ) = (p : ℤ) + 1 := by rw [hp]; omega
          have hmaster := master N.toWeakModule B hLW hgen hdec p hxG
          rw [Submodule.mem_sup] at hmaster
          obtain ⟨a, ha, b, hb, hab⟩ := hmaster
          have hxproj : wProj N (h + d) x = x := wProj_of_mem N hxw
          rw [← hxproj, ← hab, map_add]
          refine Submodule.add_mem _ ?_ ?_
          · exact (ordSpanAll_antitone N.toWeakModule B gen wt (Nat.zero_le p))
              (wProj_mem_ordSpanAll N B h hB hgen (h + d) ha)
          · refine ih ⟨wProj_apply_mem N _ _, ?_⟩
            rw [hcast]
            exact wProj_mem_Gfil N B h hB (h + d) hb
        · have heq : (d + 1 - (j + 1) : ℕ) = (d + 1 - j : ℕ) := by omega
          rw [heq]
          exact ih
  have h0 := key (d + 1)
  have hz : (d + 1 - (d + 1) : ℕ) = 0 := by omega
  rw [hz] at h0
  have htop : Gfil N.toWeakModule B ((0 : ℕ) : ℤ) = ⊤ :=
    Gfil_eq_top_of_nonpos hLW (by norm_num)
  rw [htop, inf_top_eq] at h0
  exact h0

/-- **Sorted generator words span the module.**  Karel–Li Thm 3.10/Cor 3.12 in the repo's
normal form: for a lowest-weight generated module with a conformal weight, over a finite
homogeneous generating set of `𝒱` modulo `C₂(𝒱)` and the vacuum, the **sorted** words

  `(gen i₁)₍₋m₁₋₁₎ ⋯ (gen i_r)₍₋m_r₋₁₎ w`,   `(i₁,m₁) ≤ ⋯ ≤ (i_r,m_r)` lexicographically,
  `w ∈ B`,

span all of `M`. -/
theorem ordSpanAll_eq_top (N : OrdVModule W M) (B : Set M) (h : ℂ)
    (hcw : HasConformalWeight N h) (hB : ∀ w ∈ B, ∃ d₀ : ℕ, w ∈ N.weight (h + d₀))
    (hLW : LWGenerated N.toWeakModule B)
    {g : ℕ} {gen : Fin g → 𝒱} {wt : Fin g → ℕ} (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (hdec : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W) :
    ordSpanAll N.toWeakModule B gen wt 0 = ⊤ := by
  refine top_le_iff.mp ?_
  have hsup : (⊤ : Submodule ℂ M) = ⨆ α : ℂ, N.weight α :=
    ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top N.weight).mp N.isInternal).2.symm
  rw [hsup]
  refine iSup_le (fun α => ?_)
  by_cases hα : N.weight α = ⊥
  · rw [hα]; exact bot_le
  · obtain ⟨d, rfl⟩ := hcw.2 α hα
    exact weight_le_ordSpanAll N B h hB hLW hgen hdec d

end VOA
