/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.GordonCluster
import VOA.Commutative.GordonBlockEquiv

/-! # Gordon multiplicity for every pair in an arbitrary labeled block partition -/

namespace VOA.GordonArbitraryPair

open VOA.GordonFiltration VOA.GordonBlockEquiv VOA.GordonCluster

variable {σ τ K : Type*} [Fintype σ] [Fintype τ] [DecidableEq σ] [DecidableEq τ]

abbrev OtherLabels (u v : τ) := {j : τ // j ≠ u ∧ j ≠ v}
abbrev OtherVariables (f : σ → τ) (u v : τ) := {x : σ // f x ≠ u ∧ f x ≠ v}

/-- Separate two distinguished block labels from all remaining labels. -/
def labelEquiv (u v : τ) (huv : u ≠ v) : Bool ⊕ OtherLabels u v ≃ τ where
  toFun := Sum.elim (fun b ↦ if b then u else v) Subtype.val
  invFun := fun j ↦ if hu : j = u then Sum.inl true else
    if hv : j = v then Sum.inl false else Sum.inr ⟨j, hu, hv⟩
  left_inv := by
    intro j
    rcases j with b | j
    · cases b <;> simp [huv, huv.symm]
    · simp [j.property.1, j.property.2]
  right_inv := by
    intro j
    by_cases hu : j = u
    · subst j; simp
    · by_cases hv : j = v
      · subst j; simp [hu]
      · simp [hu, hv]

@[simp] theorem labelEquiv_true (u v : τ) (huv : u ≠ v) :
    labelEquiv u v huv (Sum.inl true) = u := rfl
@[simp] theorem labelEquiv_false (u v : τ) (huv : u ≠ v) :
    labelEquiv u v huv (Sum.inl false) = v := rfl
@[simp] theorem labelEquiv_other (u v : τ) (huv : u ≠ v) (j : OtherLabels u v) :
    labelEquiv u v huv (Sum.inr j) = j.val := rfl

/-- Restrict the original assignment to variables and labels outside the chosen pair. -/
def restMap (f : σ → τ) (u v : τ) : OtherVariables f u v → OtherLabels u v :=
  fun x ↦ ⟨f x.val, x.property⟩

theorem blockSize_restMap (f : σ → τ) (u v : τ) (j : OtherLabels u v) :
    blockSize (restMap f u v) j = blockSize f j.val := by
  rw [blockSize_eq_card_fiber, blockSize_eq_card_fiber]
  apply Fintype.card_congr
  refine {
    toFun := fun x ↦ ⟨x.val.val, congrArg Subtype.val x.property⟩
    invFun := fun x ↦ ⟨⟨x.val, by simpa only [x.property] using j.property⟩,
      Subtype.ext x.property⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro x; rfl
  · intro x; rfl

/-- Canonical assignment of the chosen pair, followed by the unchanged other blocks. -/
def modelMap (f : σ → τ) (u v : τ) (huv : u ≠ v) :
    Fin (blockSize f u + blockSize f v) ⊕ OtherVariables f u v → τ :=
  labelEquiv u v huv ∘ combinedMap (blockSize f u + blockSize f v)
    (blockSize f u) (restMap f u v)

theorem blockSize_modelMap (f : σ → τ) (u v : τ) (huv : u ≠ v) (j : τ) :
    blockSize (modelMap f u v huv) j = blockSize f j := by
  obtain ⟨j, rfl⟩ := (labelEquiv u v huv).surjective j
  rw [modelMap, blockSize_equiv_comp]
  rcases j with b | j
  · cases b
    · simp [GordonFiltration.blockSize_twoBlockMap_false, Nat.le_add_right]
    · simp [GordonFiltration.blockSize_twoBlockMap_true, Nat.le_add_right]
  · simp [blockSize_restMap]

noncomputable section

/-- Match the original variables with the canonical pair-plus-rest model fiber by fiber. -/
def sourceEquiv (f : σ → τ) (u v : τ) (huv : u ≠ v) :
    σ ≃ Fin (blockSize f u + blockSize f v) ⊕ OtherVariables f u v :=
  Equiv.ofFiberEquiv (f := f) (g := modelMap f u v huv) (fun j ↦ Fintype.equivOfCardEq (by
    simpa only [← blockSize_eq_card_fiber] using (blockSize_modelMap f u v huv j).symm))

theorem sourceEquiv_map (f : σ → τ) (u v : τ) (huv : u ≠ v) (x : σ) :
    modelMap f u v huv (sourceEquiv f u v huv x) = f x := by
  unfold sourceEquiv
  exact Equiv.ofFiberEquiv_map _ x

variable [CommRing K] [Algebra ℚ K] [IsDomain K] [CharZero K]

/-- Multiplicity for an arbitrary pair of blocks, ordered by their cardinalities. -/
theorem difference_pow_dvd_of_size_le (f : σ → τ) (u v : τ) (huv : u ≠ v)
    (hsize : blockSize f v ≤ blockSize f u)
    (U : Submodule K (MvPolynomial σ K)) (F : MvPolynomial σ K) (hF : F.IsSymmetric)
    (hmem : F ∈ filtration (τ := τ) U (shape f)) :
    (MvPolynomial.X u - MvPolynomial.X v) ^ (2 * blockSize f v) ∣ blockEval f F := by
  let es := sourceEquiv f u v huv
  let et := labelEquiv u v huv
  let g := combinedMap (blockSize f u + blockSize f v) (blockSize f u) (restMap f u v)
  have hfg : g ∘ es = et.symm ∘ f := by
    funext x
    apply et.injective
    simpa [g, es, et, modelMap] using sourceEquiv_map f u v huv x
  have hm := mem_filtration_rename U f g es et.symm hfg F hmem
  have hd := difference_pow_dvd_of_mem_filtration hsize (restMap f u v) ⊤
    (MvPolynomial.rename es F) (hF.rename es) hm
  have hout := map_dvd (MvPolynomial.rename et).toRingHom hd
  have heval : MvPolynomial.rename et (blockEval g (MvPolynomial.rename es F)) =
      blockEval f F := by
    simp only [blockEval, MvPolynomial.rename_rename]
    have he : et ∘ g ∘ es = f := by
      funext x
      exact sourceEquiv_map f u v huv x
    rw [he]
  change MvPolynomial.rename et _ ∣
    MvPolynomial.rename et (blockEval g (MvPolynomial.rename es F)) at hout
  rw [heval] at hout
  simpa only [map_pow, map_sub, MvPolynomial.rename_X, labelEquiv_true, labelEquiv_false] using hout

/-- Lemma 4.3 for every distinct pair in an arbitrary labeled finite block partition. -/
theorem difference_pow_two_min_dvd (f : σ → τ) (u v : τ) (huv : u ≠ v)
    (U : Submodule K (MvPolynomial σ K)) (F : MvPolynomial σ K) (hF : F.IsSymmetric)
    (hmem : F ∈ filtration (τ := τ) U (shape f)) :
    (MvPolynomial.X u - MvPolynomial.X v) ^
      (2 * min (blockSize f u) (blockSize f v)) ∣ blockEval f F := by
  by_cases hsize : blockSize f v ≤ blockSize f u
  · simpa only [Nat.min_eq_right hsize] using
      difference_pow_dvd_of_size_le f u v huv hsize U F hF hmem
  · have hrev := difference_pow_dvd_of_size_le f v u huv.symm (by omega) U F hF hmem
    have he : (MvPolynomial.X v - MvPolynomial.X u : MvPolynomial τ K) ^
        (2 * blockSize f u) = (MvPolynomial.X u - MvPolynomial.X v) ^ (2 * blockSize f u) := by
      rw [← neg_sub, neg_pow]
      simp
    rw [he] at hrev
    simpa only [Nat.min_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hsize))] using hrev

end
end VOA.GordonArbitraryPair
