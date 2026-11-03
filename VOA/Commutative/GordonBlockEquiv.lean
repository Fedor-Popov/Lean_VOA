/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.GordonFiltration
import Mathlib.Logic.Equiv.Basic

/-! # Relabeling original variables and block labels in the Gordon filtration -/

namespace VOA.GordonBlockEquiv

open VOA.GordonFiltration VOA.GordonPartitionOrder

variable {σ σ' τ τ' K : Type*}
variable [Fintype σ] [Fintype σ'] [Fintype τ] [Fintype τ']
variable [DecidableEq σ] [DecidableEq σ'] [DecidableEq τ] [DecidableEq τ']

/-- A block size is the cardinality of its actual fiber. -/
theorem blockSize_eq_card_fiber (f : σ → τ) (j : τ) :
    blockSize f j = Fintype.card {x // f x = j} := by
  simp [blockSize, Fintype.card_subtype]

theorem blockSize_comp_equiv (f : σ' → τ) (e : σ ≃ σ') (j : τ) :
    blockSize (f ∘ e) j = blockSize f j := by
  simp only [blockSize_eq_card_fiber]
  exact Fintype.card_congr (Equiv.subtypeEquiv e (fun _ ↦ Iff.rfl))

theorem blockSize_equiv_comp (f : σ → τ) (e : τ ≃ τ') (j : τ) :
    blockSize (e ∘ f) (e j) = blockSize f j := by
  simp [blockSize, Function.comp_def, e.injective.eq_iff]

theorem rawParts_comp_equiv (f : σ' → τ) (e : σ ≃ σ') :
    rawParts (f ∘ e) = rawParts f := by
  simp only [rawParts]
  congr 1
  funext j
  exact blockSize_comp_equiv f e j

theorem rawParts_equiv_comp (f : σ → τ) (e : τ ≃ τ') :
    rawParts (e ∘ f) = rawParts f := by
  have hu : (Finset.univ : Finset τ').val =
      (Finset.univ : Finset τ).val.map e := by
    simpa using congrArg Finset.val (Finset.map_univ_equiv e).symm
  rw [rawParts, hu, Multiset.map_map]
  change Multiset.map (fun x ↦ blockSize (e ∘ f) (e x)) Finset.univ.val = _
  simp_rw [blockSize_equiv_comp]
  rfl

noncomputable section
variable [CommRing K]

/-- Block evaluations of symmetric polynomials are independent of the chosen
original variables whenever each labeled block has the same size. -/
theorem blockEval_eq_of_blockSize_eq (f g : σ → τ) (F : MvPolynomial σ K)
    (hF : F.IsSymmetric) (hsize : ∀ j, blockSize f j = blockSize g j) :
    blockEval f F = blockEval g F := by
  let ef : ∀ j, {x // f x = j} ≃ {x // g x = j} := fun j ↦
    Fintype.equivOfCardEq (by simpa only [← blockSize_eq_card_fiber] using hsize j)
  let e : Equiv.Perm σ := Equiv.ofFiberEquiv ef
  have he : f = g ∘ e := funext (fun x ↦ (Equiv.ofFiberEquiv_map ef x).symm)
  change MvPolynomial.rename f F = MvPolynomial.rename g F
  rw [he, ← MvPolynomial.rename_rename, hF e]

/-- Membership in the Gordon kernels is preserved by arbitrary simultaneous
relabeling of original variables and block labels. -/
theorem mem_filtration_rename (U : Submodule K (MvPolynomial σ K))
    (f : σ → τ) (g : σ' → τ') (es : σ ≃ σ') (et : τ ≃ τ')
    (hfg : g ∘ es = et ∘ f) (F : MvPolynomial σ K)
    (hmem : F ∈ filtration (τ := τ) U (shape f)) :
    MvPolynomial.rename es F ∈ filtration (τ := τ') ⊤ (shape g) := by
  rw [mem_filtration]
  refine ⟨Submodule.mem_top, ?_⟩
  intro k hk
  let k' : σ → τ := et.symm ∘ k ∘ es
  have hshapeK : rawParts k' = rawParts k := by
    rw [show k' = et.symm ∘ (k ∘ es) from rfl, rawParts_equiv_comp, rawParts_comp_equiv]
  have hshapeF : rawParts f = rawParts g := by
    have ht := congrArg rawParts hfg
    rw [rawParts_comp_equiv, rawParts_equiv_comp] at ht
    exact ht.symm
  have hlt : LexGreater (shape k') (shape f) := by
    simpa only [LexGreater, shape_parts, hshapeK, hshapeF] using hk
  have hz := eval_eq_zero_of_mem_filtration U _ F hmem k' hlt
  have hz' := congrArg (MvPolynomial.rename et) hz
  change MvPolynomial.rename k (MvPolynomial.rename es F) = 0
  simpa [blockEval, MvPolynomial.rename_rename, k', Function.comp_def] using hz'

end
end VOA.GordonBlockEquiv
