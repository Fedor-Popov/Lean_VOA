/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Rigidity of graded-unitary layer signs along a continuous family of Hermitian matrices

Pure linear algebra and topology; nothing VOA-specific.

Let `ι` be a finite index set with a length function `ℓ : ι → ℕ`, and `G` a Hermitian matrix on
`ι`.  The **flag steps** are the coordinate subspaces `{ℓ < r}`; the **layer** `r` consists of the
vectors supported on `{ℓ ≤ r}` that are `G`-orthogonal to the step `{ℓ < r}`.

* `MatrixStepNondeg ℓ G` — every step `{ℓ < r}` has nonzero principal minor;
* `MatrixLayerSign ℓ G r` — `(-1)^r yᴴ G y > 0` for every nonzero layer-`r` vector `y`.

Main results:

* `posDef_rigid` — a continuous family of Hermitian matrices with trivial kernels on a
  preconnected space is positive definite everywhere once it is so at one point;
* `matrixLayerSign_iff_schur` — the layer-`r` sign condition is positive definiteness of
  `(-1)^r` times the Schur complement of the step `{ℓ < r}` in the step `{ℓ ≤ r}`;
* `matrixLayerSign_rigid` — along a continuous family of Hermitian matrices whose steps are all
  nondegenerate, the layer signs cannot change on a preconnected parameter space.
-/

namespace VOA

namespace MatrixRigidity

open Matrix
open scoped ComplexOrder

noncomputable section

/-! ## Positive definiteness is rigid along nonsingular continuous families -/

/-- **Positive definiteness is locally constant along a continuous family of Hermitian
matrices with trivial kernels**, hence constant on a preconnected parameter space. -/
theorem posDef_rigid {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {n : Type*} [Fintype n] [DecidableEq n] (T : X → Matrix n n ℂ) (hT : Continuous T)
    (hH : ∀ t, (T t).IsHermitian) (hker : ∀ t (b : n → ℂ), T t *ᵥ b = 0 → b = 0)
    {t₀ t₁ : X} (h₀ : (T t₀).PosDef) : (T t₁).PosDef := by
  have hdet : ∀ t, (T t).det ≠ 0 := by
    intro t hz
    obtain ⟨v, hv, hmv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
    exact hv (hker t v hmv)
  -- continuity of quadratic forms
  have hq : ∀ x : n → ℂ, Continuous fun t => star x ⬝ᵥ (T t *ᵥ x) := fun x =>
    continuous_const.dotProduct (hT.matrix_mulVec continuous_const)
  set U : Set X := {t | (T t).PosDef} with hU
  have hUeq : U = {t | ∀ x : n → ℂ, 0 ≤ star x ⬝ᵥ (T t *ᵥ x)} := by
    ext t
    simp only [hU, Set.mem_setOf_eq]
    constructor
    · intro h x
      exact (posSemidef_iff_dotProduct_mulVec.mp h.posSemidef).2 x
    · intro h
      have hpsd : (T t).PosSemidef := posSemidef_iff_dotProduct_mulVec.mpr ⟨hH t, h⟩
      exact hpsd.posDef_iff_det_ne_zero.mpr (hdet t)
  have hclosed : IsClosed U := by
    rw [hUeq, Set.setOf_forall]
    exact isClosed_iInter fun x => isClosed_le continuous_const (hq x)
  have hopen : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have hK : IsCompact (Metric.sphere (0 : n → ℂ) 1) := isCompact_sphere 0 1
    have hF : Continuous fun p : X × (n → ℂ) => star p.2 ⬝ᵥ (T p.1 *ᵥ p.2) :=
      (continuous_snd.star).dotProduct ((hT.comp continuous_fst).matrix_mulVec continuous_snd)
    have hev : ∀ᶠ s in nhds t, ∀ x ∈ Metric.sphere (0 : n → ℂ) 1,
        0 < (star x ⬝ᵥ (T s *ᵥ x)).re := by
      apply hK.eventually_forall_of_forall_eventually
      intro x hx
      have hx0 : x ≠ 0 := by
        intro h; rw [h, mem_sphere_zero_iff_norm, norm_zero] at hx; exact zero_ne_one hx
      have hpos : 0 < (star x ⬝ᵥ (T t *ᵥ x)).re :=
        (Complex.pos_iff.mp (ht.dotProduct_mulVec_pos hx0)).1
      exact (Complex.continuous_re.comp hF).continuousAt.eventually
        (lt_mem_nhds hpos)
    filter_upwards [hev] with s hs
    refine posDef_iff_dotProduct_mulVec.mpr ⟨hH s, fun y hy => ?_⟩
    have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy
    set c : ℂ := ((‖y‖⁻¹ : ℝ) : ℂ) with hc
    have hxs : c • y ∈ Metric.sphere (0 : n → ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, hc, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hny), inv_mul_cancel₀ hny.ne']
    have hpos := hs _ hxs
    have hscale : star (c • y) ⬝ᵥ (T s *ᵥ (c • y)) =
        ((‖y‖⁻¹ ^ 2 : ℝ) : ℂ) * (star y ⬝ᵥ (T s *ᵥ y)) := by
      rw [mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
        hc, Complex.star_def, Complex.conj_ofReal]
      push_cast
      ring
    rw [hscale, Complex.re_ofReal_mul] at hpos
    have hre : 0 < (star y ⬝ᵥ (T s *ᵥ y)).re :=
      pos_of_mul_pos_right hpos (by positivity)
    have him : (star y ⬝ᵥ (T s *ᵥ y)).im = 0 := by
      simpa using (hH s).im_star_dotProduct_mulVec_self y
    exact Complex.pos_iff.mpr ⟨hre, him.symm⟩
  have hclopen : IsClopen U := ⟨hclosed, hopen⟩
  have hne : U.Nonempty := ⟨t₀, h₀⟩
  have huniv := hclopen.eq_univ hne
  have : t₁ ∈ U := by rw [huniv]; trivial
  exact this

/-! ## Steps, layers and the Schur complement -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (ℓ : ι → ℕ)

/-- The principal submatrix on the step `{ℓ < r}`. -/
def stepMatrix (G : Matrix ι ι ℂ) (r : ℕ) : Matrix {i // ℓ i < r} {i // ℓ i < r} ℂ :=
  G.submatrix Subtype.val Subtype.val

/-- Every flag step carries a nondegenerate principal minor. -/
def MatrixStepNondeg (G : Matrix ι ι ℂ) : Prop :=
  ∀ r : ℕ, (stepMatrix ℓ G r).det ≠ 0

/-- The graded-unitary layer sign at length `r`. -/
def MatrixLayerSign (G : Matrix ι ι ℂ) (r : ℕ) : Prop :=
  ∀ y : ι → ℂ, (∀ i, r < ℓ i → y i = 0) → (∀ i, ℓ i < r → (G *ᵥ y) i = 0) → y ≠ 0 →
    0 < (-1 : ℂ) ^ r * (star y ⬝ᵥ (G *ᵥ y))

variable {ℓ}

/-- A sum over a subtype is the full sum when the summand vanishes off the subtype. -/
theorem sum_subtype_of_vanish (p : ι → Prop) [DecidablePred p] (f : ι → ℂ)
    (h : ∀ i, ¬ p i → f i = 0) : ∑ j : {i // p i}, f j = ∑ i, f i := by
  rw [← Fintype.sum_subtype_add_sum_subtype p f]
  have h0 : ∑ j : {i // ¬ p i}, f j = 0 := Finset.sum_eq_zero (fun j _ => h j.1 j.2)
  rw [h0, add_zero]

/-- Splitting a sum supported on `{ℓ ≤ r}` into the step `{ℓ < r}` and the top `{ℓ = r}`. -/
theorem sum_split (r : ℕ) (f : ι → ℂ) (hf : ∀ i, r < ℓ i → f i = 0) :
    ∑ i, f i = ∑ j : {i // ℓ i < r}, f j + ∑ j : {i // ℓ i = r}, f j := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun i => ℓ i < r)) (by simp) f,
    ← Finset.sum_subtype (Finset.univ.filter (fun i => ℓ i = r)) (by simp) f,
    ← Finset.sum_union (by
      rw [Finset.disjoint_left]
      intro i h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      omega)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hi
  exact hf i (by omega)

/-! ### The Schur complement of a step -/

section Schur

variable (ℓ) (G : Matrix ι ι ℂ) (r : ℕ)

/-- The block from the top `{ℓ = r}` to the step `{ℓ < r}`. -/
def blkLE : Matrix {i // ℓ i < r} {i // ℓ i = r} ℂ := G.submatrix Subtype.val Subtype.val

/-- The block from the step `{ℓ < r}` to the top `{ℓ = r}`. -/
def blkEL : Matrix {i // ℓ i = r} {i // ℓ i < r} ℂ := G.submatrix Subtype.val Subtype.val

/-- The diagonal top block. -/
def blkEE : Matrix {i // ℓ i = r} {i // ℓ i = r} ℂ := G.submatrix Subtype.val Subtype.val

/-- **The Schur complement** of the step `{ℓ < r}` inside `{ℓ ≤ r}`. -/
def schur : Matrix {i // ℓ i = r} {i // ℓ i = r} ℂ :=
  blkEE ℓ G r - blkEL ℓ G r * (stepMatrix ℓ G r)⁻¹ * blkLE ℓ G r

/-- The lower part of the layer vector with prescribed top coordinates. -/
def lowerPart (b : {i // ℓ i = r} → ℂ) : {i // ℓ i < r} → ℂ :=
  -(((stepMatrix ℓ G r)⁻¹ * blkLE ℓ G r) *ᵥ b)

/-- The layer vector with prescribed top coordinates. -/
def extend (b : {i // ℓ i = r} → ℂ) : ι → ℂ := fun i =>
  if h : ℓ i = r then b ⟨i, h⟩ else if h' : ℓ i < r then lowerPart ℓ G r b ⟨i, h'⟩ else 0

variable {ℓ G r}

theorem extend_eq (b : {i // ℓ i = r} → ℂ) {i : ι} (h : ℓ i = r) :
    extend ℓ G r b i = b ⟨i, h⟩ := by
  simp [extend, h]

theorem extend_lt (b : {i // ℓ i = r} → ℂ) {i : ι} (h : ℓ i < r) :
    extend ℓ G r b i = lowerPart ℓ G r b ⟨i, h⟩ := by
  simp [extend, h, Nat.ne_of_lt h]

theorem extend_gt (b : {i // ℓ i = r} → ℂ) {i : ι} (h : r < ℓ i) : extend ℓ G r b i = 0 := by
  simp [extend, Nat.ne_of_gt h, Nat.not_lt_of_gt h]

theorem mulVec_extend (b : {i // ℓ i = r} → ℂ) (i : ι) :
    (G *ᵥ extend ℓ G r b) i =
      (∑ j : {i // ℓ i < r}, G i j * lowerPart ℓ G r b j) + ∑ j : {i // ℓ i = r}, G i j * b j := by
  rw [mulVec, dotProduct, sum_split r _ (fun j hj => by rw [extend_gt b hj, mul_zero])]
  congr 1
  · exact Finset.sum_congr rfl fun j _ => by rw [extend_lt b j.2]
  · exact Finset.sum_congr rfl fun j _ => by rw [extend_eq b j.2]

variable (hdet : (stepMatrix ℓ G r).det ≠ 0)
include hdet

theorem mulVec_extend_lt (b : {i // ℓ i = r} → ℂ) {i : ι} (h : ℓ i < r) :
    (G *ᵥ extend ℓ G r b) i = 0 := by
  rw [mulVec_extend]
  have h1 : (∑ j : {i // ℓ i < r}, G i j * lowerPart ℓ G r b j) =
      (stepMatrix ℓ G r *ᵥ lowerPart ℓ G r b) ⟨i, h⟩ := rfl
  have h2 : (∑ j : {i // ℓ i = r}, G i j * b j) = (blkLE ℓ G r *ᵥ b) ⟨i, h⟩ := rfl
  rw [h1, h2, lowerPart, mulVec_neg, mulVec_mulVec, ← Matrix.mul_assoc,
    mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mul]
  simp

theorem mulVec_extend_eq (b : {i // ℓ i = r} → ℂ) {i : ι} (h : ℓ i = r) :
    (G *ᵥ extend ℓ G r b) i = (schur ℓ G r *ᵥ b) ⟨i, h⟩ := by
  rw [mulVec_extend]
  have h1 : (∑ j : {i // ℓ i < r}, G i j * lowerPart ℓ G r b j) =
      (blkEL ℓ G r *ᵥ lowerPart ℓ G r b) ⟨i, h⟩ := rfl
  have h2 : (∑ j : {i // ℓ i = r}, G i j * b j) = (blkEE ℓ G r *ᵥ b) ⟨i, h⟩ := rfl
  rw [h1, h2, schur, lowerPart, sub_mulVec, mulVec_neg, mulVec_mulVec, ← Matrix.mul_assoc]
  simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply]
  ring

omit hdet in
theorem quad_extend_aux (b : {i // ℓ i = r} → ℂ)
    (hlo : ∀ i, ℓ i < r → (G *ᵥ extend ℓ G r b) i = 0)
    (heq : ∀ i (h : ℓ i = r), (G *ᵥ extend ℓ G r b) i = (schur ℓ G r *ᵥ b) ⟨i, h⟩) :
    star (extend ℓ G r b) ⬝ᵥ (G *ᵥ extend ℓ G r b) = star b ⬝ᵥ (schur ℓ G r *ᵥ b) := by
  rw [dotProduct, sum_split (ℓ := ℓ) r _ (fun j hj => by
    simp only [Pi.star_apply, extend_gt b hj, star_zero, zero_mul])]
  have h0 : ∑ j : {i // ℓ i < r},
      star (extend ℓ G r b) j * (G *ᵥ extend ℓ G r b) j = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [hlo j j.2, mul_zero]
  rw [h0, zero_add, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.star_apply, Pi.star_apply, extend_eq b j.2, heq j j.2]

theorem quad_extend (b : {i // ℓ i = r} → ℂ) :
    star (extend ℓ G r b) ⬝ᵥ (G *ᵥ extend ℓ G r b) = star b ⬝ᵥ (schur ℓ G r *ᵥ b) :=
  quad_extend_aux b (fun i h => mulVec_extend_lt hdet b h)
    (fun i h => mulVec_extend_eq hdet b h)

/-- Every layer vector is the extension of its top coordinates. -/
theorem eq_extend_of_layer (y : ι → ℂ) (hsupp : ∀ i, r < ℓ i → y i = 0)
    (horth : ∀ i, ℓ i < r → (G *ᵥ y) i = 0) :
    y = extend ℓ G r (fun j : {i // ℓ i = r} => y j) := by
  set b : {i // ℓ i = r} → ℂ := fun j => y j
  set a : {i // ℓ i < r} → ℂ := fun j => y j
  have hsys : stepMatrix ℓ G r *ᵥ a = -(blkLE ℓ G r *ᵥ b) := by
    funext i
    have h := horth i.1 i.2
    rw [mulVec, dotProduct, sum_split r _ (fun j hj => by rw [hsupp j hj, mul_zero])] at h
    have h1 : (∑ j : {i // ℓ i < r}, G i j * y j) = (stepMatrix ℓ G r *ᵥ a) i := rfl
    have h2 : (∑ j : {i // ℓ i = r}, G i j * y j) = (blkLE ℓ G r *ᵥ b) i := rfl
    rw [h1, h2] at h
    simp only [Pi.neg_apply]
    linear_combination h
  have ha : a = lowerPart ℓ G r b := by
    have := congrArg (fun v => (stepMatrix ℓ G r)⁻¹ *ᵥ v) hsys
    simp only [mulVec_mulVec, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), one_mulVec] at this
    rw [this, lowerPart, mulVec_neg, mulVec_mulVec]
  funext i
  by_cases h1 : ℓ i = r
  · rw [extend_eq _ h1]
  · by_cases h2 : ℓ i < r
    · rw [extend_lt _ h2, ← ha]
    · rw [extend_gt _ (by omega), hsupp i (by omega)]

omit hdet in
/-- With `G` Hermitian and the step nondegenerate, the Schur complement is Hermitian. -/
theorem schur_isHermitian (hG : G.IsHermitian) : (schur ℓ G r).IsHermitian := by
  have hEL : blkEL ℓ G r = (blkLE ℓ G r)ᴴ := by
    ext i j
    simp only [blkEL, blkLE, submatrix_apply, conjTranspose_apply]
    rw [← hG.apply j.1 i.1]
    simp
  have hM : (stepMatrix ℓ G r).IsHermitian := by
    unfold stepMatrix
    exact hG.submatrix _
  have hEE : (blkEE ℓ G r).IsHermitian := by
    unfold blkEE
    exact hG.submatrix _
  rw [schur, hEL]
  exact hEE.sub (isHermitian_conjTranspose_mul_mul _ hM.inv)

/-- The Schur complement has trivial kernel once the next step is nondegenerate. -/
theorem schur_ker (hnext : (stepMatrix ℓ G (r + 1)).det ≠ 0) (b : {i // ℓ i = r} → ℂ)
    (hb : schur ℓ G r *ᵥ b = 0) : b = 0 := by
  set y := extend ℓ G r b
  have hy : ∀ i, ℓ i < r + 1 → (G *ᵥ y) i = 0 := by
    intro i hi
    by_cases h : ℓ i = r
    · rw [mulVec_extend_eq hdet b h, hb]; rfl
    · exact mulVec_extend_lt hdet b (by omega)
  set z : {i // ℓ i < r + 1} → ℂ := fun j => y j
  have hz : stepMatrix ℓ G (r + 1) *ᵥ z = 0 := by
    funext i
    change ∑ j : {i // ℓ i < r + 1}, G i j * y j = 0
    rw [sum_subtype_of_vanish (fun j => ℓ j < r + 1) (fun j => G i j * y j) (fun j hj => by
      simp only
      rw [show y j = 0 from extend_gt b (by omega), mul_zero])]
    exact hy i.1 i.2
  have hz0 := Matrix.eq_zero_of_mulVec_eq_zero hnext hz
  funext j
  have := congrFun hz0 ⟨j.1, by have := j.2; omega⟩
  simp only [z, y, Pi.zero_apply] at this
  rw [extend_eq b j.2] at this
  simpa using this

/-- **The layer sign is positive definiteness of the signed Schur complement.** -/
theorem matrixLayerSign_iff_schur (hG : G.IsHermitian) :
    MatrixLayerSign ℓ G r ↔ ((-1 : ℂ) ^ r • schur ℓ G r).PosDef := by
  have hT : ((-1 : ℂ) ^ r • schur ℓ G r).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_smul, (schur_isHermitian (r := r) hG).eq]
    simp
  constructor
  · intro hL
    refine posDef_iff_dotProduct_mulVec.mpr ⟨hT, fun b hb => ?_⟩
    have hne : extend ℓ G r b ≠ 0 := by
      intro h
      apply hb
      funext j
      have := congrFun h j.1
      rw [extend_eq b j.2] at this
      simpa using this
    have := hL (extend ℓ G r b) (fun i hi => extend_gt b hi)
      (fun i hi => mulVec_extend_lt hdet b hi) hne
    rw [quad_extend hdet] at this
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact this
  · intro hP y hsupp horth hy
    have hyext := eq_extend_of_layer hdet y hsupp horth
    set b : {i // ℓ i = r} → ℂ := fun j => y j
    have hb : b ≠ 0 := by
      intro h
      apply hy
      rw [hyext, h]
      funext i
      by_cases h1 : ℓ i = r
      · rw [extend_eq _ h1]; rfl
      · by_cases h2 : ℓ i < r
        · rw [extend_lt _ h2, lowerPart, mulVec_zero, neg_zero]; rfl
        · rw [extend_gt _ (by omega)]; rfl
    have := hP.dotProduct_mulVec_pos hb
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul] at this
    rw [hyext, quad_extend hdet]
    exact this

end Schur

/-! ### Rigidity of the layer signs -/

/-- **Layer signs are rigid along continuous families with nondegenerate steps.**
If `H` is a continuous family of Hermitian matrices on a preconnected space, every flag step is
nondegenerate at every parameter, and the layer-`r` sign holds at one parameter, then it holds
at every parameter. -/
theorem matrixLayerSign_rigid {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (H : X → Matrix ι ι ℂ) (hc : Continuous H) (hH : ∀ t, (H t).IsHermitian)
    (hnd : ∀ t, MatrixStepNondeg ℓ (H t)) (r : ℕ) {t₀ t₁ : X}
    (h₀ : MatrixLayerSign ℓ (H t₀) r) : MatrixLayerSign ℓ (H t₁) r := by
  rw [matrixLayerSign_iff_schur (hnd t₁ r) (hH t₁)]
  rw [matrixLayerSign_iff_schur (hnd t₀ r) (hH t₀)] at h₀
  have hstep : Continuous fun t => stepMatrix ℓ (H t) r := hc.matrix_submatrix _ _
  have hinv : Continuous fun t => (stepMatrix ℓ (H t) r)⁻¹ := by
    have h1 : (fun t => (stepMatrix ℓ (H t) r)⁻¹) =
        fun t => ((stepMatrix ℓ (H t) r).det)⁻¹ • (stepMatrix ℓ (H t) r).adjugate := by
      funext t
      rw [inv_def, Ring.inverse_eq_inv']
    rw [h1]
    exact (hstep.matrix_det.inv₀ (fun t => hnd t r)).smul hstep.matrix_adjugate
  have hS : Continuous fun t => (-1 : ℂ) ^ r • schur ℓ (H t) r := by
    refine continuous_const.smul ?_
    unfold schur blkEE blkEL blkLE
    exact (hc.matrix_submatrix _ _).sub
      (((hc.matrix_submatrix _ _).matrix_mul hinv).matrix_mul (hc.matrix_submatrix _ _))
  refine posDef_rigid (fun t => (-1 : ℂ) ^ r • schur ℓ (H t) r) hS (fun t => ?_)
    (fun t b hb => ?_) h₀
  · unfold IsHermitian
    rw [conjTranspose_smul, (schur_isHermitian (r := r) (hH t)).eq]
    simp
  · rw [smul_mulVec] at hb
    have hb' : schur ℓ (H t) r *ᵥ b = 0 := by
      have hu : IsUnit ((-1 : ℂ) ^ r) := (isUnit_neg_one (α := ℂ)).pow r
      exact (smul_eq_zero.mp hb).resolve_left hu.ne_zero
    exact schur_ker (hnd t r) (hnd t (r + 1)) b hb'

end

end MatrixRigidity

end VOA
