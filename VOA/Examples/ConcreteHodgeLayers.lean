/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.ConcreteHodgeTensor

/-!
# The modified (σ-twisted) form of a graded-unitary VOA, as a positive form on the carrier

Second layer of the concrete Beem–Garner instantiation. Beem–Garner (arXiv 2509.10364,
Definition 2.19 and Corollary 2.24) attach to a graded-unitary VOA the *modified* Hermitian form
`⟨x|y⟩ = ((σ∘ρ) x, y)`, where `σ = (-1)^p` on the `p`-th orthogonal layer of the filtration.
Graded unitarity is exactly the statement that this form is positive definite. Here this is
made literal on the repository's `GradedUnitary` predicate:

* `orthSum P` — the orthogonal sum of sesquilinear forms on a direct sum `⨁ i, V i`, and
  `isPosOn_orthSum`: positive if every summand is.
* `internalForm hI P` — the same, transported along an internal direct-sum decomposition
  `DirectSum.IsInternal L` of a module; `isPosOn_internalForm`, and its values on homogeneous
  vectors (`internalForm_of_mem_same`, `internalForm_of_mem_ne`).
* `layers_isInternal` — under clause (iv) of graded unitarity and reflexivity of the Gram form,
  the layers `L_p = G_p ∩ G_{p-1}^⊥` of one weight space form an internal direct sum.
* `modForm` (at one weight) and `isPosOn_modForm` (**weak GU of one factor at one weight**): the
  layer-orthogonal sum of `(-1)^p h|_{L_p}` is positive definite. `modForm_layer_same` records
  that on `L_p` it is `(-1)^p h`, i.e. `i^{2R} h` with `R = p`.
* `carrierForm` and `isPosOn_carrierForm` (**weak GU of one factor**): summing over conformal
  weights, a positive definite modified form on the whole carrier of a graded-unitary VOA.

Hypotheses: `GradedUnitary B R F` (this is where `hA` enters) and reflexivity of the level-`n`
Gram forms (a consequence of symmetry of the invariant form, `InvariantForm.IsSymmetric`).
Everything is proved outright from these.

**Scope.** The form built here is the layer-orthogonal sum. That it coincides with
`(-1)^p (ρ x, y)` on *all* pairs (not only within one layer) is the statement that distinct layers
are `h`-orthogonal; `modForm_eq_signed_of_orth` proves the coincidence from that orthogonality,
which itself follows from `ρ`-stability of the layers (`layer_h_orth_of_rho_stable`).
-/

namespace VOA.ConcreteHodge

open scoped DirectSum
open VOA.VertexOperatorAlgebra
open Module (finrank)

noncomputable section

universe u v w

/-! ### Orthogonal sums of sesquilinear forms -/

section OrthSum

variable {ι : Type v} [DecidableEq ι] {V : ι → Type w} [∀ i, AddCommGroup (V i)]
  [∀ i, Module ℂ (V i)]

open Classical in
/-- The orthogonal sum `Σ_i P_i (f i, g i)` of sesquilinear forms on `⨁ i, V i`. -/
def orthSumFun (P : ∀ i, SesqForm (V i)) (f g : ⨁ i, V i) : ℂ :=
  ∑ i ∈ f.support ∪ g.support, P i (f i) (g i)

/-- The orthogonal sum may be computed over any finite set containing both supports. -/
theorem orthSumFun_eq (P : ∀ i, SesqForm (V i)) (f g : ⨁ i, V i) (s : Finset ι)
    (hf : ∀ i, f i ≠ 0 → i ∈ s) (hg : ∀ i, g i ≠ 0 → i ∈ s) :
    orthSumFun P f g = ∑ i ∈ s, P i (f i) (g i) := by
  classical
  unfold orthSumFun
  have key : ∀ t : Finset ι, (∀ i, f i ≠ 0 → i ∈ t) → (∀ i, g i ≠ 0 → i ∈ t) →
      ∑ i ∈ t, P i (f i) (g i) = ∑ i ∈ t ∩ (f.support ∪ g.support), P i (f i) (g i) := by
    intro t _ _
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro i _ hi
    simp only [Finset.mem_inter, Finset.mem_union, DFinsupp.mem_support_iff, not_and,
      not_or, not_not] at hi
    have hi' := hi ‹_›
    rw [hi'.1, (P i).zero_left]
  have hU : s ∩ (f.support ∪ g.support) = f.support ∪ g.support := by
    apply Finset.inter_eq_right.mpr
    intro i hi
    rcases Finset.mem_union.mp hi with h | h
    · exact hf i (DFinsupp.mem_support_iff.mp h)
    · exact hg i (DFinsupp.mem_support_iff.mp h)
  rw [key s hf hg, hU]

/-- **The orthogonal sum form** on `⨁ i, V i`. -/
def orthSum (P : ∀ i, SesqForm (V i)) : SesqForm (⨁ i, V i) where
  toFun := orthSumFun P
  add_left f f' g := by
    classical
    let s := f.support ∪ f'.support ∪ g.support
    have hf : ∀ i, f i ≠ 0 → i ∈ s := fun i hi => by simp [s, hi]
    have hf' : ∀ i, f' i ≠ 0 → i ∈ s := fun i hi => by simp [s, hi]
    have hg : ∀ i, g i ≠ 0 → i ∈ s := fun i hi => by simp [s, hi]
    have hff' : ∀ i, (f + f') i ≠ 0 → i ∈ s := fun i hi => by
      by_contra hs
      apply hi
      have h1 : f i = 0 := by by_contra h; exact hs (hf i h)
      have h2 : f' i = 0 := by by_contra h; exact hs (hf' i h)
      simp [h1, h2]
    rw [orthSumFun_eq P _ _ s hff' hg, orthSumFun_eq P _ _ s hf hg,
      orthSumFun_eq P _ _ s hf' hg, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [DirectSum.add_apply, (P i).add_left]
  smul_left z f g := by
    classical
    let s := f.support ∪ g.support
    have hf : ∀ i, f i ≠ 0 → i ∈ s := fun i hi => by simp [s, hi]
    have hg : ∀ i, g i ≠ 0 → i ∈ s := fun i hi => by simp [s, hi]
    have hzf : ∀ i, (z • f) i ≠ 0 → i ∈ s := fun i hi => by
      by_contra hs
      apply hi
      have h1 : f i = 0 := by by_contra h; exact hs (hf i h)
      rw [DirectSum.smul_apply, h1, smul_zero]
    rw [orthSumFun_eq P _ _ s hzf hg, orthSumFun_eq P _ _ s hf hg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [DirectSum.smul_apply, (P i).smul_left]
  add_right f g g' := by
    classical
    let s := f.support ∪ g.support ∪ g'.support
    have hf : ∀ i, f i ≠ 0 → i ∈ s := fun i hi => by simp [s, hi]
    have hg : ∀ i, g i ≠ 0 → i ∈ s := fun i hi => by simp [s, hi]
    have hg' : ∀ i, g' i ≠ 0 → i ∈ s := fun i hi => by simp [s, hi]
    have hgg' : ∀ i, (g + g') i ≠ 0 → i ∈ s := fun i hi => by
      by_contra hs
      apply hi
      have h1 : g i = 0 := by by_contra h; exact hs (hg i h)
      have h2 : g' i = 0 := by by_contra h; exact hs (hg' i h)
      simp [h1, h2]
    rw [orthSumFun_eq P _ _ s hf hgg', orthSumFun_eq P _ _ s hf hg,
      orthSumFun_eq P _ _ s hf hg', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [DirectSum.add_apply, (P i).add_right]
  smul_right z f g := by
    classical
    let s := f.support ∪ g.support
    have hf : ∀ i, f i ≠ 0 → i ∈ s := fun i hi => by simp [s, hi]
    have hg : ∀ i, g i ≠ 0 → i ∈ s := fun i hi => by simp [s, hi]
    have hzg : ∀ i, (z • g) i ≠ 0 → i ∈ s := fun i hi => by
      by_contra hs
      apply hi
      have h1 : g i = 0 := by by_contra h; exact hs (hg i h)
      rw [DirectSum.smul_apply, h1, smul_zero]
    rw [orthSumFun_eq P _ _ s hf hzg, orthSumFun_eq P _ _ s hf hg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [DirectSum.smul_apply, (P i).smul_right]

theorem orthSum_apply (P : ∀ i, SesqForm (V i)) (f g : ⨁ i, V i) (s : Finset ι)
    (hf : ∀ i, f i ≠ 0 → i ∈ s) (hg : ∀ i, g i ≠ 0 → i ∈ s) :
    orthSum P f g = ∑ i ∈ s, P i (f i) (g i) :=
  orthSumFun_eq P f g s hf hg

/-- **Positivity of an orthogonal sum.** -/
theorem isPosOn_orthSum (P : ∀ i, SesqForm (V i)) (hP : ∀ i, IsPosOn (P i) ⊤) :
    IsPosOn (orthSum P) ⊤ := by
  classical
  intro f _ hf
  have hsupp : ∀ i, f i ≠ 0 → i ∈ f.support := fun i hi => DFinsupp.mem_support_iff.mpr hi
  rw [orthSum_apply P f f f.support hsupp hsupp]
  obtain ⟨i0, hi0⟩ : ∃ i, f i ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (DFinsupp.ext h)
  have hterm : ∀ i ∈ f.support, ∃ r : ℝ, 0 < r ∧ P i (f i) (f i) = r := fun i hi =>
    hP i (f i) Submodule.mem_top (DFinsupp.mem_support_iff.mp hi)
  choose r hr0 hr using hterm
  refine ⟨∑ i ∈ f.support.attach, r i.1 i.2, ?_, ?_⟩
  · apply Finset.sum_pos (fun i _ => hr0 i.1 i.2)
    exact ⟨⟨i0, hsupp i0 hi0⟩, Finset.mem_attach _ _⟩
  · rw [Complex.ofReal_sum, ← Finset.sum_attach]
    exact Finset.sum_congr rfl fun i _ => hr i.1 i.2

theorem orthSum_of_same (P : ∀ i, SesqForm (V i)) (i : ι) (a b : V i) :
    orthSum P (DirectSum.of V i a) (DirectSum.of V i b) = P i a b := by
  have hof : ∀ (c : V i) j, (DirectSum.of V i c) j ≠ 0 → j ∈ ({i} : Finset ι) := by
    intro c j hj
    by_contra hji
    apply hj
    rw [DirectSum.of_eq_of_ne]
    simpa using hji
  rw [orthSum_apply P _ _ {i} (hof a) (hof b), Finset.sum_singleton, DirectSum.of_eq_same,
    DirectSum.of_eq_same]

theorem orthSum_of_ne (P : ∀ i, SesqForm (V i)) {i j : ι} (hij : i ≠ j) (a : V i) (b : V j) :
    orthSum P (DirectSum.of V i a) (DirectSum.of V j b) = 0 := by
  have hofi : ∀ k, (DirectSum.of V i a) k ≠ 0 → k ∈ ({i, j} : Finset ι) := by
    intro k hk
    by_contra hki
    apply hk
    rw [DirectSum.of_eq_of_ne]
    intro h; exact hki (by simp [h])
  have hofj : ∀ k, (DirectSum.of V j b) k ≠ 0 → k ∈ ({i, j} : Finset ι) := by
    intro k hk
    by_contra hkj
    apply hk
    rw [DirectSum.of_eq_of_ne]
    intro h; exact hkj (by simp [h])
  rw [orthSum_apply P _ _ {i, j} hofi hofj, Finset.sum_pair hij, DirectSum.of_eq_of_ne _ _ _ hij,
    (P i).zero_right, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hij), (P j).zero_left, add_zero]

end OrthSum

/-! ### Transport along an internal direct sum -/

section Internal

variable {ι : Type v} [DecidableEq ι] {E : Type u} [AddCommGroup E] [Module ℂ E]
  {L : ι → Submodule ℂ E}

/-- The decomposition isomorphism `⨁ i, L i ≃ E` of an internal direct sum. -/
def internalEquiv (hI : DirectSum.IsInternal L) : (⨁ i, L i) ≃ₗ[ℂ] E :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap L) hI

theorem internalEquiv_symm_of_mem (hI : DirectSum.IsInternal L) {i : ι} {x : E} (hx : x ∈ L i) :
    (internalEquiv hI).symm x = DirectSum.of (fun i => L i) i ⟨x, hx⟩ := by
  apply (internalEquiv hI).injective
  rw [LinearEquiv.apply_symm_apply]
  change x = DirectSum.coeLinearMap L (DirectSum.of (fun i => L i) i ⟨x, hx⟩)
  rw [DirectSum.coeLinearMap_of]

/-- The orthogonal sum of forms on the summands of an internal direct sum, as a form on `E`. -/
def internalForm (hI : DirectSum.IsInternal L) (P : ∀ i, SesqForm (L i)) : SesqForm E :=
  (orthSum P).comap (internalEquiv hI).symm.toLinearMap

theorem isPosOn_internalForm (hI : DirectSum.IsInternal L) (P : ∀ i, SesqForm (L i))
    (hP : ∀ i, IsPosOn (P i) ⊤) : IsPosOn (internalForm hI P) ⊤ :=
  (orthSum P).isPosOn_comap (isPosOn_orthSum P hP) _ (internalEquiv hI).symm.injective

theorem internalForm_of_mem_same (hI : DirectSum.IsInternal L) (P : ∀ i, SesqForm (L i))
    {i : ι} {x y : E} (hx : x ∈ L i) (hy : y ∈ L i) :
    internalForm hI P x y = P i ⟨x, hx⟩ ⟨y, hy⟩ := by
  change orthSum P ((internalEquiv hI).symm x) ((internalEquiv hI).symm y) = _
  rw [internalEquiv_symm_of_mem hI hx, internalEquiv_symm_of_mem hI hy, orthSum_of_same]

theorem internalForm_of_mem_ne (hI : DirectSum.IsInternal L) (P : ∀ i, SesqForm (L i))
    {i j : ι} (hij : i ≠ j) {x y : E} (hx : x ∈ L i) (hy : y ∈ L j) :
    internalForm hI P x y = 0 := by
  change orthSum P ((internalEquiv hI).symm x) ((internalEquiv hI).symm y) = _
  rw [internalEquiv_symm_of_mem hI hx, internalEquiv_symm_of_mem hI hy, orthSum_of_ne P hij]

end Internal

/-! ### Independence of a triangular family -/

/-- A family `f : ℕ → Submodule` with `f k ≤ g n` for `k < n` and `f n` disjoint from `g n` is
independent. (Used with `f = layer`, `g = pieceLT`.) -/
theorem iSupIndep_of_disjoint_lower {E : Type u} [AddCommGroup E] [Module ℂ E]
    (f g : ℕ → Submodule ℂ E) (hfg : ∀ k n, k < n → f k ≤ g n)
    (hd : ∀ n, Disjoint (f n) (g n)) : iSupIndep f := by
  classical
  rw [iSupIndep_iff_supIndep]
  intro s
  refine Finset.induction_on_max s (Finset.supIndep_empty f) ?_
  intro a t hlt ih
  refine ih.insert ((hd a).mono_right ?_)
  exact Finset.sup_le fun k hk => hfg k a (hlt k hk)

/-! ### The modified form at one conformal weight -/

section Layers

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

theorem pieceIn_le_pieceLT (F : GradedFlag W) {k p : ℕ} (hkp : k < p) (n : ℤ) :
    F.pieceIn k n ≤ F.pieceLT p n := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [GradedFlag.pieceLT_succ]
  exact F.pieceIn_mono n (by omega)

/-- **The layers of one weight space are an internal direct sum** (clause (iv) of graded
unitarity plus reflexivity of the Gram form). -/
theorem layers_isInternal (F : GradedFlag W) (n : ℤ) {β : LinearMap.BilinForm ℂ (W.grading n)}
    [FiniteDimensional ℂ (W.grading n)] (href : β.IsRefl) (hnd : LayerNondegenerate F n β) :
    DirectSum.IsInternal (fun p : ℕ => F.layer n β p) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · refine iSupIndep_of_disjoint_lower _ (fun p => F.pieceLT p n) ?_ ?_
    · intro k p hkp
      exact (F.layer_le_pieceIn n β k).trans (pieceIn_le_pieceLT F hkp n)
    · intro p
      exact (layerDecomposition F href hnd p).2.symm
  · exact iSup_layer_eq_top F href hnd

/-- The signed form `(-1)^p h` restricted to the layer `L_p`. -/
def layerForm (F : GradedFlag W) (n : ℤ) (β : LinearMap.BilinForm ℂ (W.grading n))
    (h : SesqForm (W.grading n)) (p : ℕ) : SesqForm (F.layer n β p) :=
  (signedForm h p).restrict (F.layer n β p)

theorem isPosOn_layerForm (F : GradedFlag W) (n : ℤ) {β : LinearMap.BilinForm ℂ (W.grading n)}
    {h : SesqForm (W.grading n)} (hpos : LayerPositive F n β h) (p : ℕ) :
    IsPosOn (layerForm F n β h p) ⊤ := by
  intro x _ hx
  have hx' : (x : W.grading n) ≠ 0 := fun h0 => hx (Subtype.ext h0)
  exact hpos p x x.2 hx'

/-- **The modified Hermitian form at weight `n`**: the layer-orthogonal sum of `(-1)^p h`. -/
def modForm (F : GradedFlag W) (n : ℤ) {β : LinearMap.BilinForm ℂ (W.grading n)}
    (h : SesqForm (W.grading n)) [FiniteDimensional ℂ (W.grading n)] (href : β.IsRefl)
    (hnd : LayerNondegenerate F n β) : SesqForm (W.grading n) :=
  internalForm (layers_isInternal F n href hnd) (layerForm F n β h)

/-- **Weak graded unitarity of one factor at one weight.** Graded unitarity at weight `n`
makes the modified form positive definite on the whole weight space. -/
theorem isPosOn_modForm (F : GradedFlag W) (n : ℤ) {β : LinearMap.BilinForm ℂ (W.grading n)}
    {h : SesqForm (W.grading n)} [FiniteDimensional ℂ (W.grading n)] (href : β.IsRefl)
    (hGU : GradedUnitaryAt F n β h) : IsPosOn (modForm F n h href hGU.1) ⊤ :=
  isPosOn_internalForm _ _ (isPosOn_layerForm F n hGU.2)

/-- On one layer the modified form is `(-1)^p h` (that is, `i^{2R} h` with `R = p`). -/
theorem modForm_layer_same (F : GradedFlag W) (n : ℤ) {β : LinearMap.BilinForm ℂ (W.grading n)}
    (h : SesqForm (W.grading n)) [FiniteDimensional ℂ (W.grading n)] (href : β.IsRefl)
    (hnd : LayerNondegenerate F n β) {p : ℕ} {x y : W.grading n} (hx : x ∈ F.layer n β p)
    (hy : y ∈ F.layer n β p) : modForm F n h href hnd x y = (-1 : ℂ) ^ p * h x y :=
  internalForm_of_mem_same _ _ hx hy

/-- Distinct layers are orthogonal for the modified form. -/
theorem modForm_layer_ne (F : GradedFlag W) (n : ℤ) {β : LinearMap.BilinForm ℂ (W.grading n)}
    (h : SesqForm (W.grading n)) [FiniteDimensional ℂ (W.grading n)] (href : β.IsRefl)
    (hnd : LayerNondegenerate F n β) {p q : ℕ} (hpq : p ≠ q) {x y : W.grading n}
    (hx : x ∈ F.layer n β p) (hy : y ∈ F.layer n β q) : modForm F n h href hnd x y = 0 :=
  internalForm_of_mem_ne _ _ hpq hx hy

/-- If distinct layers are `h`-orthogonal, the modified form equals `(-1)^p h` on every pair
with first argument in `L_p`: the `P_eq` identity of `GUData`, with `2R = 2p`. -/
theorem modForm_eq_signed_of_orth (F : GradedFlag W) (n : ℤ)
    {β : LinearMap.BilinForm ℂ (W.grading n)} (h : SesqForm (W.grading n))
    [FiniteDimensional ℂ (W.grading n)] (href : β.IsRefl) (hnd : LayerNondegenerate F n β)
    (horth : ∀ p q, p ≠ q → ∀ x ∈ F.layer n β p, ∀ y ∈ F.layer n β q, h x y = 0)
    {p : ℕ} {x : W.grading n} (hx : x ∈ F.layer n β p) (y : W.grading n) :
    modForm F n h href hnd x y = (-1 : ℂ) ^ p * h x y := by
  have hI := layers_isInternal F n href hnd
  have hy : y ∈ ⨆ q, F.layer n β q := by rw [hI.submodule_iSup_eq_top]; exact Submodule.mem_top
  induction hy using Submodule.iSup_induction' with
  | mem q y hyq =>
      by_cases hpq : p = q
      · subst hpq; exact modForm_layer_same F n h href hnd hx hyq
      · rw [modForm_layer_ne F n h href hnd hpq hx hyq, horth p q hpq x hx y hyq, mul_zero]
  | zero => rw [(modForm F n h href hnd).zero_right, h.zero_right, mul_zero]
  | add y y' _ _ ih ih' =>
      rw [(modForm F n h href hnd).add_right, h.add_right, ih, ih', mul_add]

end Layers

/-! ### The modified form on the whole carrier -/

section Carrier

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- Reflexivity of all level-`n` Gram forms of an invariant form. -/
def GramRefl (B : InvariantForm W) : Prop :=
  ∀ n : ℤ, LinearMap.BilinForm.IsRefl (LiRadical.gradedForm B n)

/-- A symmetric invariant form has reflexive Gram forms. -/
theorem gramRefl_of_isSymmetric (B : InvariantForm W) (hB : B.IsSymmetric) : GramRefl B :=
  fun _ a b hab => by
    rw [LiRadical.gradedForm_apply] at hab ⊢
    rw [hB]; exact hab

/-- The modified form on one weight space, from graded unitarity. -/
def weightModForm (B : InvariantForm W) (R : RealStructure W) (F : GradedFlag W)
    (hGU : GradedUnitary B R F) (hrefl : GramRefl B) (n : ℤ) : SesqForm (W.grading n) :=
  haveI := W.finrank n
  modForm F n (gradedSesq B R n) (hrefl n) (hGU n).1

theorem isPosOn_weightModForm (B : InvariantForm W) (R : RealStructure W) (F : GradedFlag W)
    (hGU : GradedUnitary B R F) (hrefl : GramRefl B) (n : ℤ) :
    IsPosOn (weightModForm B R F hGU hrefl n) ⊤ :=
  haveI := W.finrank n
  isPosOn_modForm F n (hrefl n) (hGU n)

/-- **The modified form `((σ∘ρ)x, y)` of a graded-unitary VOA on its whole carrier**: the
weight-orthogonal sum of the layer-orthogonal sums of `(-1)^p (ρ x, y)`. -/
def carrierForm (B : InvariantForm W) (R : RealStructure W) (F : GradedFlag W)
    (hGU : GradedUnitary B R F) (hrefl : GramRefl B) : SesqForm 𝒱 :=
  internalForm W.isInternal (weightModForm B R F hGU hrefl)

/-- **Weak graded unitarity of one factor**: the modified form of a graded-unitary VOA is
positive definite on the whole carrier. -/
theorem isPosOn_carrierForm (B : InvariantForm W) (R : RealStructure W) (F : GradedFlag W)
    (hGU : GradedUnitary B R F) (hrefl : GramRefl B) : IsPosOn (carrierForm B R F hGU hrefl) ⊤ :=
  isPosOn_internalForm _ _ (isPosOn_weightModForm B R F hGU hrefl)

/-- Distinct conformal weights are orthogonal for the carrier form. -/
theorem carrierForm_weight_ne (B : InvariantForm W) (R : RealStructure W) (F : GradedFlag W)
    (hGU : GradedUnitary B R F) (hrefl : GramRefl B) {m n : ℤ} (hmn : m ≠ n) {x y : 𝒱}
    (hx : x ∈ W.grading m) (hy : y ∈ W.grading n) : carrierForm B R F hGU hrefl x y = 0 :=
  internalForm_of_mem_ne _ _ hmn hx hy

/-- On one weight space the carrier form is the weight-`n` modified form. -/
theorem carrierForm_weight_same (B : InvariantForm W) (R : RealStructure W) (F : GradedFlag W)
    (hGU : GradedUnitary B R F) (hrefl : GramRefl B) {n : ℤ} {x y : 𝒱}
    (hx : x ∈ W.grading n) (hy : y ∈ W.grading n) :
    carrierForm B R F hGU hrefl x y = weightModForm B R F hGU hrefl n ⟨x, hx⟩ ⟨y, hy⟩ :=
  internalForm_of_mem_same _ _ hx hy

end Carrier

end

end VOA.ConcreteHodge
