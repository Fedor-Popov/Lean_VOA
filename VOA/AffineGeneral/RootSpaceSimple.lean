/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.Ideal
import Mathlib.Logic.Relation
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Simplicity from a root-space presentation

An abstract criterion for `LieAlgebra.IsSimple ℂ L`, designed for the weight-one Lie algebra of a
lattice VOA (`𝔥 ⊕ ⨁_α ℂ e^α`) but stated without any VOA.  The data are a finite family of "root
vectors" `e : R → L` and "coroots" `hb : R → L` such that

* `e` and `hb` span `L`, the `hb` commute, and `⁅hb α, e β⁆ = pair α β • e β`;
* the weights separate roots (`sep`) and every `pair α α ≠ 0`;
* `⁅e α, e (neg α)⁆` is a nonzero multiple of `hb α`;
* no nonzero element of `span hb` centralizes every `e β` (`center`);
* the root graph `pair α β ≠ 0` is connected (`conn`).

The proof extracts a single root vector from any nonzero element of an ideal by applying a product
of shifted `ad hb`-operators (`rootProj`), then propagates along the root graph.
-/

namespace VOA.AffineGeneral.RootSpace

open Submodule

noncomputable section

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]
variable {R : Type*}
variable (e hb : R → L) (pair : R → R → ℂ)

/-- The operator `ad (hb γ) - c`. -/
def shiftOp (γ : R) (c : ℂ) : Module.End ℂ L := LieModule.toEnd ℂ L L (hb γ) - c • 1

theorem shiftOp_apply (γ : R) (c : ℂ) (x : L) : shiftOp hb γ c x = ⁅hb γ, x⁆ - c • x := by
  simp [shiftOp]

theorem shiftOp_mem (I : LieIdeal ℂ L) (γ : R) (c : ℂ) {x : L} (hx : x ∈ I) :
    shiftOp hb γ c x ∈ I := by
  rw [shiftOp_apply]
  exact I.sub_mem (I.lie_mem hx) (I.smul_mem c hx)

/-- A product of shift operators. -/
def listOp (l : List (R × ℂ)) : Module.End ℂ L := (l.map fun p => shiftOp hb p.1 p.2).prod

theorem listOp_mem (I : LieIdeal ℂ L) (l : List (R × ℂ)) {x : L} (hx : x ∈ I) :
    listOp hb l x ∈ I := by
  induction l with
  | nil => simpa [listOp] using hx
  | cons p l ih =>
      simp only [listOp, List.map_cons, List.prod_cons, Module.End.mul_apply] at ih ⊢
      exact shiftOp_mem hb I p.1 p.2 ih

variable {e hb pair}

theorem listOp_e (hbe : ∀ α β, ⁅hb α, e β⁆ = pair α β • e β) (l : List (R × ℂ)) (β : R) :
    listOp hb l (e β) = (l.map fun p => pair p.1 β - p.2).prod • e β := by
  induction l with
  | nil => simp [listOp]
  | cons p l ih =>
      simp only [listOp, List.map_cons, List.prod_cons, Module.End.mul_apply] at ih ⊢
      rw [ih, map_smul, shiftOp_apply, hbe, ← sub_smul, smul_smul, mul_comm]

theorem lie_eq_zero_of_mem_span (hhb : ∀ α β, ⁅hb α, hb β⁆ = 0) (γ : R) {y : L}
    (hy : y ∈ span ℂ (Set.range hb)) : ⁅hb γ, y⁆ = 0 := by
  have hle : span ℂ (Set.range hb) ≤ LinearMap.ker (LieModule.toEnd ℂ L L (hb γ)) := by
    rw [span_le]
    rintro _ ⟨β, rfl⟩
    simp [hhb]
  simpa using hle hy

theorem lie_mem_span_e (hbe : ∀ α β, ⁅hb α, e β⁆ = pair α β • e β) (β : R) {y : L}
    (hy : y ∈ span ℂ (Set.range hb)) : ∃ c : ℂ, ⁅y, e β⁆ = c • e β := by
  have hle : span ℂ (Set.range hb) ≤ (ℂ ∙ e β).comap (-(LieModule.toEnd ℂ L L (e β))) := by
    rw [span_le]
    rintro _ ⟨α, rfl⟩
    simp only [SetLike.mem_coe, mem_comap, LinearMap.neg_apply, LieModule.toEnd_apply_apply]
    rw [← lie_skew, neg_neg, hbe]
    exact smul_mem _ _ (mem_span_singleton_self _)
  obtain ⟨c, hc⟩ := mem_span_singleton.mp (hle hy)
  refine ⟨c, ?_⟩
  rw [hc]
  exact (lie_skew _ _).symm

variable (e hb pair)

/-- **Root-space criterion for simplicity.** -/
theorem isSimple_of_roots [Fintype R] [DecidableEq R] [Nonempty R]
    (hspan : span ℂ (Set.range e ∪ Set.range hb) = ⊤)
    (he0 : ∀ β, e β ≠ 0)
    (hbe : ∀ α β, ⁅hb α, e β⁆ = pair α β • e β)
    (hhb : ∀ α β, ⁅hb α, hb β⁆ = 0)
    (hdiag : ∀ α, pair α α ≠ 0)
    (sep : ∀ α β, α ≠ β → ∃ γ, pair γ α ≠ pair γ β)
    (neg : R → R) (hneg : ∀ α, ∃ c : ℂ, c ≠ 0 ∧ ⁅e α, e (neg α)⁆ = c • hb α)
    (center : ∀ y ∈ span ℂ (Set.range hb), (∀ β, ⁅y, e β⁆ = 0) → y = 0)
    (conn : ∀ α β, Relation.ReflTransGen (fun a b => pair a b ≠ 0) α β) :
    LieAlgebra.IsSimple ℂ L where
  eq_bot_or_eq_top I := by
    by_cases hI : I = ⊥
    · exact Or.inl hI
    right
    have hex : ∃ v ∈ I, v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hI
      ext v
      constructor
      · intro hv; exact (LieSubmodule.mem_bot v).mpr (hcon v hv)
      · intro hv; rw [(LieSubmodule.mem_bot v).mp hv]; exact I.zero_mem
    obtain ⟨x, hxI, hx0⟩ := hex
    -- Step 1: some root vector lies in `I`.
    have hroot : ∃ α, e α ∈ I := by
      have hxs : x ∈ span ℂ (Set.range e ∪ Set.range hb) := by rw [hspan]; trivial
      rw [span_union, mem_sup] at hxs
      obtain ⟨u, hu, y, hy, rfl⟩ := hxs
      obtain ⟨a, rfl⟩ := (mem_span_range_iff_exists_fun ℂ).mp hu
      by_cases ha : ∃ α, a α ≠ 0
      · obtain ⟨α, hα⟩ := ha
        choose! g hg using sep
        let l : List (R × ℂ) :=
          (Finset.univ.erase α).toList.map fun β => (g α β, pair (g α β) β)
        let s : R → ℂ := fun β => (l.map fun p => pair p.1 β - p.2).prod
        have hs0 : ∀ β, β ≠ α → s β = 0 := by
          intro β hβ
          apply List.prod_eq_zero
          simp only [l, List.map_map, List.mem_map, Finset.mem_toList, Finset.mem_erase,
            Finset.mem_univ, and_true, Function.comp_apply]
          exact ⟨β, hβ, sub_self _⟩
        have hsα : s α ≠ 0 := by
          apply List.prod_ne_zero
          simp only [l, List.map_map, List.mem_map, Finset.mem_toList, Finset.mem_erase,
            Finset.mem_univ, and_true, Function.comp_apply, not_exists, not_and]
          intro β hβ h
          exact hg α β (Ne.symm hβ) (sub_eq_zero.mp h)
        -- `T = listOp l ∘ ad (hb α)` kills the Cartan part and every `e β`, `β ≠ α`.
        have hT : listOp hb l ⁅hb α, (∑ β, a β • e β) + y⁆ = (s α * pair α α * a α) • e α := by
          rw [lie_add, lie_eq_zero_of_mem_span hhb α hy, add_zero, lie_sum]
          simp only [lie_smul, hbe, smul_smul, map_sum, map_smul, listOp_e hbe]
          rw [Finset.sum_eq_single α]
          · congr 1; simp only [s]; ring
          · intro β _ hβ; rw [show (l.map fun p => pair p.1 β - p.2).prod = 0 from hs0 β hβ]; simp
          · simp
        have hmem := listOp_mem hb I l (I.lie_mem (x := hb α) hxI)
        rw [hT] at hmem
        refine ⟨α, ?_⟩
        have hc : s α * pair α α * a α ≠ 0 := mul_ne_zero (mul_ne_zero hsα (hdiag α)) hα
        have := I.smul_mem (s α * pair α α * a α)⁻¹ hmem
        rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
      · push Not at ha
        simp only [ha, zero_smul, Finset.sum_const_zero, zero_add] at hx0 hxI ⊢
        have : ∃ β, ⁅y, e β⁆ ≠ 0 := by
          by_contra h
          push Not at h
          exact hx0 (center y hy h)
        obtain ⟨β, hβ⟩ := this
        obtain ⟨c, hc⟩ := lie_mem_span_e hbe β hy
        have hc0 : c ≠ 0 := by rintro rfl; rw [zero_smul] at hc; exact hβ hc
        have hmem : ⁅y, e β⁆ ∈ I := by
          rw [← lie_skew]; exact I.neg_mem (I.lie_mem hxI)
        rw [hc] at hmem
        refine ⟨β, ?_⟩
        have := I.smul_mem c⁻¹ hmem
        rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
    -- Step 2: propagate along the root graph.
    obtain ⟨α0, hα0⟩ := hroot
    have hhbmem : ∀ α, e α ∈ I → hb α ∈ I := by
      intro α hα
      obtain ⟨c, hc0, hc⟩ := hneg α
      have h1 : ⁅e α, e (neg α)⁆ ∈ I := by
        rw [← lie_skew]; exact I.neg_mem (I.lie_mem hα)
      rw [hc] at h1
      have := I.smul_mem c⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
    have hstep : ∀ α β, pair α β ≠ 0 → e α ∈ I → e β ∈ I := by
      intro α β hp hα
      have h1 : ⁅hb α, e β⁆ ∈ I := by
        rw [← lie_skew]; exact I.neg_mem (I.lie_mem (hhbmem α hα))
      rw [hbe] at h1
      have := I.smul_mem (pair α β)⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ hp, one_smul] at this
    have hall : ∀ β, e β ∈ I := by
      intro β
      induction conn α0 β with
      | refl => exact hα0
      | tail _ hp ih => exact hstep _ _ hp ih
    rw [eq_top_iff]
    intro v _
    have hv : v ∈ span ℂ (Set.range e ∪ Set.range hb) := by rw [hspan]; trivial
    have hle : span ℂ (Set.range e ∪ Set.range hb) ≤ (I : Submodule ℂ L) := by
      rw [span_le]
      rintro _ (⟨β, rfl⟩ | ⟨β, rfl⟩)
      · exact hall β
      · exact hhbmem β (hall β)
    exact hle hv
  non_abelian := by
    obtain ⟨α⟩ := (inferInstance : Nonempty R)
    intro hab
    have h0 : ⁅hb α, e α⁆ = 0 := hab.trivial _ _
    rw [hbe] at h0
    exact he0 α ((smul_eq_zero.mp h0).resolve_left (hdiag α))

end

end VOA.AffineGeneral.RootSpace
