/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.ConcreteGoodDerived
import VOA.Examples.ConcreteHodgeLayers
import VOA.Core.SuperVertexAlgebra

/-!
# Interpreted gradings: projections, restriction, tensor products, factor layers

Generic layer of the *interpreted* Beem–Garner geometry. The bigrading `deg` used by
`GoodGeometry` must be the actual `R`-grading coming from the factors. This file supplies the
generic machinery, all proved outright:

* **Projections of an internal family** (`iproj`): `iproj_of_mem_same`, `iproj_of_mem_ne`,
  `iproj_mem`, `iproj_comm_of_preserves` (an operator preserving every piece commutes with every
  projection), `iproj_comm_iproj` (projections of two compatible internal families commute).
* **Stable submodules** (`ProjStable`): kernels of piece-preserving operators, infima, and
  weight spaces of a second internal grading containing the pieces are stable; the restricted
  family of a stable submodule spans it (`iSup_comap_eq_top_of_stable`), and sup-membership
  descends (`mem_sup_comap_of_stable`).
* **Tensor gradings** (`tensorDeg`): for gradings indexed by an additive group, the tensor grading
  `⨆_b dV b ⊗ dW (a - b)` is orthogonal for the product form (`tensorDeg_orth`), spans
  (`tensorDeg_span`), and is compatible with additive gradings of the factors (`tensorDeg_le`).
* **The layer grading of a graded-unitary VOA** (`layerDeg`): index `((2p, 0), m)` for the
  `p`-th orthogonal layer of weight `m`. Orthogonal for `carrierForm` (`layerDeg_orth`), spanning
  (`layerDeg_span`), inside weight `m` (`layerDeg_le_gradingC`), ghost number `0`.
* **The trivial grading of a unitary VOA** (`trivialDeg`): everything at `R = 0`.

Index convention: `((2R, gh), weight) : (ℤ × ℤ) × ℂ`.
-/

namespace VOA.ConcreteHodge

open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open scoped TensorProduct DirectSum

noncomputable section

universe u v w

/-! ### Projections of an internal family -/

section Proj

variable {ι : Type v} [DecidableEq ι] {E : Type u} [AddCommGroup E] [Module ℂ E]
  {L : ι → Submodule ℂ E}

/-- The projection onto the `i`-th summand of an internal direct sum. -/
def iproj (hI : DirectSum.IsInternal L) (i : ι) : E →ₗ[ℂ] E :=
  (L i).subtype ∘ₗ DirectSum.component ℂ ι (fun i => L i) i ∘ₗ
    (internalEquiv hI).symm.toLinearMap

theorem iproj_of_mem_same (hI : DirectSum.IsInternal L) {i : ι} {x : E} (hx : x ∈ L i) :
    iproj hI i x = x := by
  simp only [iproj, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [internalEquiv_symm_of_mem hI hx, ← DirectSum.lof_eq_of ℂ, DirectSum.component.of]
  simp

theorem iproj_of_mem_ne (hI : DirectSum.IsInternal L) {i j : ι} (hij : j ≠ i) {x : E}
    (hx : x ∈ L j) : iproj hI i x = 0 := by
  simp only [iproj, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [internalEquiv_symm_of_mem hI hx, ← DirectSum.lof_eq_of ℂ, DirectSum.component.of]
  simp [hij]

theorem iproj_mem (hI : DirectSum.IsInternal L) (i : ι) (x : E) : iproj hI i x ∈ L i := by
  simp only [iproj, LinearMap.coe_comp, Function.comp_apply]
  exact Submodule.coe_mem _

/-- Two linear maps agreeing on every summand agree. -/
theorem linearMap_ext_internal (hI : DirectSum.IsInternal L) {F : Type w} [AddCommGroup F]
    [Module ℂ F] {T T' : E →ₗ[ℂ] F} (h : ∀ i, ∀ x ∈ L i, T x = T' x) : T = T' := by
  ext x
  have hx : x ∈ iSup L := by rw [hI.submodule_iSup_eq_top]; exact Submodule.mem_top
  exact Submodule.iSup_induction L (motive := fun x => T x = T' x) hx h (by simp)
    (fun x x' hx hx' => by beta_reduce at hx hx' ⊢; rw [map_add, map_add, hx, hx'])

/-- An operator preserving every summand commutes with every projection. -/
theorem iproj_comm_of_preserves (hI : DirectSum.IsInternal L) (T : E →ₗ[ℂ] E)
    (hT : ∀ i, ∀ x ∈ L i, T x ∈ L i) (i : ι) :
    (iproj hI i).comp T = T.comp (iproj hI i) := by
  apply linearMap_ext_internal hI
  intro j x hx
  simp only [LinearMap.coe_comp, Function.comp_apply]
  by_cases hji : j = i
  · subst hji
    rw [iproj_of_mem_same hI (hT j x hx), iproj_of_mem_same hI hx]
  · rw [iproj_of_mem_ne hI hji (hT j x hx), iproj_of_mem_ne hI hji hx, map_zero]

/-- An operator mapping each summand `i` into the summand `σ i`, for injective `σ`, intertwines
the projections. -/
theorem iproj_comm_of_shift (hI : DirectSum.IsInternal L) (T : E →ₗ[ℂ] E) (σ : ι → ι)
    (hσ : Function.Injective σ) (hT : ∀ i, ∀ x ∈ L i, T x ∈ L (σ i)) (i : ι) :
    (iproj hI (σ i)).comp T = T.comp (iproj hI i) := by
  apply linearMap_ext_internal hI
  intro j x hx
  simp only [LinearMap.coe_comp, Function.comp_apply]
  by_cases hji : j = i
  · subst hji
    rw [iproj_of_mem_same hI (hT j x hx), iproj_of_mem_same hI hx]
  · rw [iproj_of_mem_ne hI (fun h => hji (hσ h)) (hT j x hx), iproj_of_mem_ne hI hji hx,
      map_zero]

/-- The sum of the projections over the support recovers the vector. -/
theorem sum_iproj (hI : DirectSum.IsInternal L) (x : E) :
    ∃ s : Finset ι, ∑ i ∈ s, iproj hI i x = x := by
  classical
  let f := (internalEquiv hI).symm x
  refine ⟨f.support, ?_⟩
  have hx : x = DirectSum.coeLinearMap L f := by
    change x = internalEquiv hI f
    simp [f]
  have hcomp : ∀ i, iproj hI i x = (f i : E) := fun i => rfl
  simp_rw [hcomp]
  conv_rhs => rw [hx, ← DirectSum.sum_support_of f, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [DirectSum.coeLinearMap_of]

end Proj

/-! ### Stable submodules and restricted gradings -/

section Stable

variable {ι : Type v} [DecidableEq ι] {E : Type u} [AddCommGroup E] [Module ℂ E]
  {L : ι → Submodule ℂ E}

/-- A submodule closed under all projections of an internal family. -/
def ProjStable (hI : DirectSum.IsInternal L) (S : Submodule ℂ E) : Prop :=
  ∀ i, ∀ x ∈ S, iproj hI i x ∈ S

theorem projStable_inf (hI : DirectSum.IsInternal L) {S S' : Submodule ℂ E}
    (h : ProjStable hI S) (h' : ProjStable hI S') : ProjStable hI (S ⊓ S') :=
  fun i x hx => ⟨h i x hx.1, h' i x hx.2⟩

theorem projStable_iInf (hI : DirectSum.IsInternal L) {κ : Sort w} {S : κ → Submodule ℂ E}
    (h : ∀ k, ProjStable hI (S k)) : ProjStable hI (⨅ k, S k) := by
  intro i x hx
  rw [Submodule.mem_iInf] at hx ⊢
  exact fun k => h k i x (hx k)

/-- The kernel of a piece-preserving operator is stable. -/
theorem projStable_ker (hI : DirectSum.IsInternal L) (T : E →ₗ[ℂ] E)
    (hT : ∀ i, ∀ x ∈ L i, T x ∈ L i) : ProjStable hI (LinearMap.ker T) := by
  intro i x hx
  rw [LinearMap.mem_ker] at hx ⊢
  have := LinearMap.congr_fun (iproj_comm_of_preserves hI T hT i) x
  simp only [LinearMap.coe_comp, Function.comp_apply, hx, map_zero] at this
  exact this.symm

/-- The kernel of an operator shifting the pieces along an injective `σ` is stable. -/
theorem projStable_ker_shift (hI : DirectSum.IsInternal L) (T : E →ₗ[ℂ] E) (σ : ι → ι)
    (hσ : Function.Injective σ) (hT : ∀ i, ∀ x ∈ L i, T x ∈ L (σ i)) :
    ProjStable hI (LinearMap.ker T) := by
  intro i x hx
  rw [LinearMap.mem_ker] at hx ⊢
  have := LinearMap.congr_fun (iproj_comm_of_shift hI T σ hσ hT i) x
  simp only [LinearMap.coe_comp, Function.comp_apply, hx, map_zero] at this
  exact this.symm

/-- A weight space of a second internal family is stable, if every piece lies in one weight
space. -/
theorem projStable_weight (hI : DirectSum.IsInternal L) {κ : Type w} [DecidableEq κ]
    {W : κ → Submodule ℂ E} (hW : DirectSum.IsInternal W) (wt : ι → κ)
    (hle : ∀ i, L i ≤ W (wt i)) (k : κ) : ProjStable hI (W k) := by
  intro i x hx
  -- the projections commute
  have hcomm : (iproj hI i).comp (iproj hW k) = (iproj hW k).comp (iproj hI i) := by
    apply linearMap_ext_internal hI
    intro j y hy
    simp only [LinearMap.coe_comp, Function.comp_apply]
    by_cases hk : wt j = k
    · rw [iproj_of_mem_same hW (hk ▸ hle j hy)]
      by_cases hji : j = i
      · subst hji; rw [iproj_of_mem_same hI hy, iproj_of_mem_same hW (hk ▸ hle j hy)]
      · rw [iproj_of_mem_ne hI hji hy, map_zero]
    · rw [iproj_of_mem_ne hW hk (hle j hy), map_zero]
      by_cases hji : j = i
      · subst hji; rw [iproj_of_mem_same hI hy, iproj_of_mem_ne hW hk (hle j hy)]
      · rw [iproj_of_mem_ne hI hji hy, map_zero]
  have hx' : iproj hW k x = x := iproj_of_mem_same hW hx
  have := LinearMap.congr_fun hcomm x
  simp only [LinearMap.coe_comp, Function.comp_apply, hx'] at this
  rw [this]
  exact iproj_mem hW k _

/-- Components of a vector of a stable submodule, for an index whose weight differs from a
weight space containing the vector, vanish. -/
theorem iproj_eq_zero_of_weight (hI : DirectSum.IsInternal L) {κ : Type w} [DecidableEq κ]
    {W : κ → Submodule ℂ E} (hW : DirectSum.IsInternal W) (wt : ι → κ)
    (hle : ∀ i, L i ≤ W (wt i)) {k : κ} {x : E} (hx : x ∈ W k) {i : ι} (hi : wt i ≠ k) :
    iproj hI i x = 0 := by
  have h1 : iproj hI i x ∈ W k := projStable_weight hI hW wt hle k i x hx
  have h2 : iproj hI i x ∈ W (wt i) := hle i (iproj_mem hI i x)
  have hd := hW.submodule_iSupIndep.pairwiseDisjoint hi
  exact (Submodule.disjoint_def.mp hd) _ h2 h1

/-- **The restricted family of a stable submodule spans it.** -/
theorem iSup_comap_eq_top_of_stable (hI : DirectSum.IsInternal L) {S : Submodule ℂ E}
    (hS : ProjStable hI S) : (⨆ i, (L i).comap S.subtype) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  obtain ⟨s, hs⟩ := sum_iproj hI x
  have hmem : ∀ i, (⟨iproj hI i x, hS i x hx⟩ : S) ∈ ⨆ i, (L i).comap S.subtype :=
    fun i => Submodule.mem_iSup_of_mem i (iproj_mem hI i x)
  have hsum : (⟨x, hx⟩ : S) = ∑ i ∈ s, (⟨iproj hI i x, hS i x hx⟩ : S) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact hs.symm
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ => hmem i

/-- **Sup-membership descends to a stable submodule.** -/
theorem mem_sup_comap_of_stable (hI : DirectSum.IsInternal L) {S : Submodule ℂ E}
    (hS : ProjStable hI S) {a b : ι} (hab : a ≠ b) (y : S) (hy : (y : E) ∈ L a ⊔ L b) :
    y ∈ (L a).comap S.subtype ⊔ (L b).comap S.subtype := by
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hy
  have hpa : iproj hI a (y : E) = u := by
    rw [← huv, map_add, iproj_of_mem_same hI hu, iproj_of_mem_ne hI (Ne.symm hab) hv, add_zero]
  have hpb : iproj hI b (y : E) = v := by
    rw [← huv, map_add, iproj_of_mem_same hI hv, iproj_of_mem_ne hI hab hu, zero_add]
  have huS : u ∈ S := hpa ▸ hS a y y.2
  have hvS : v ∈ S := hpb ▸ hS b y y.2
  refine Submodule.mem_sup.mpr ⟨⟨u, huS⟩, hu, ⟨v, hvS⟩, hv, ?_⟩
  apply Subtype.ext
  simp only [Submodule.coe_add]
  exact huv

end Stable

/-! ### Orthogonality on spans -/

section OrthSpan

variable {E : Type u} [AddCommGroup E] [Module ℂ E]

theorem sesq_span_left (P : SesqForm E) {s : Set E} {y : E} (h : ∀ x ∈ s, P x y = 0) :
    ∀ x ∈ Submodule.span ℂ s, P x y = 0 := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact P.zero_left y
  | add x x' _ _ h1 h2 => rw [P.add_left, h1, h2, add_zero]
  | smul c x _ h1 => rw [P.smul_left, h1, mul_zero]

theorem sesq_span_right (P : SesqForm E) {s : Set E} {x : E} (h : ∀ y ∈ s, P x y = 0) :
    ∀ y ∈ Submodule.span ℂ s, P x y = 0 := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy => exact h y hy
  | zero => exact P.zero_right x
  | add y y' _ _ h1 h2 => rw [P.add_right, h1, h2, add_zero]
  | smul c y _ h1 => rw [P.smul_right, h1, mul_zero]

theorem sesq_iSup_left' {ι : Sort v} (P : SesqForm E) (L : ι → Submodule ℂ E) {y : E}
    (h : ∀ i, ∀ x ∈ L i, P x y = 0) : ∀ x ∈ iSup L, P x y = 0 := by
  intro x hx
  exact Submodule.iSup_induction L (motive := fun x => P x y = 0) hx h (P.zero_left y)
    (fun x x' h h' => by beta_reduce at h h' ⊢; rw [P.add_left, h, h', add_zero])

theorem sesq_iSup_right' {ι : Sort v} (P : SesqForm E) (L : ι → Submodule ℂ E) {x : E}
    (h : ∀ i, ∀ y ∈ L i, P x y = 0) : ∀ y ∈ iSup L, P x y = 0 := by
  intro y hy
  exact Submodule.iSup_induction L (motive := fun y => P x y = 0) hy h (P.zero_right x)
    (fun y y' h h' => by beta_reduce at h h' ⊢; rw [P.add_right, h, h', add_zero])

end OrthSpan

/-! ### Tensor gradings -/

section Tensor

variable {ι : Type w} [AddCommGroup ι]
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : Type v} [AddCommGroup W] [Module ℂ W]

/-- **The tensor grading** `(dV ⊗ dW)(a) = ⨆_b dV b ⊗ dW (a - b)`. -/
def tensorDeg (dV : ι → Submodule ℂ V) (dW : ι → Submodule ℂ W) (a : ι) :
    Submodule ℂ (V ⊗[ℂ] W) :=
  ⨆ b : ι, Submodule.map₂ (TensorProduct.mk ℂ V W) (dV b) (dW (a - b))

theorem tmul_mem_tensorDeg (dV : ι → Submodule ℂ V) (dW : ι → Submodule ℂ W) {b c : ι}
    {x : V} {y : W} (hx : x ∈ dV b) (hy : y ∈ dW c) : x ⊗ₜ[ℂ] y ∈ tensorDeg dV dW (b + c) := by
  apply Submodule.mem_iSup_of_mem b
  have : b + c - b = c := by abel
  rw [this]
  exact Submodule.apply_mem_map₂ _ hx hy

/-- Orthogonality of the tensor grading for the product form. -/
theorem tensorDeg_orth (PV : SesqForm V) (PW : SesqForm W) (dV : ι → Submodule ℂ V)
    (dW : ι → Submodule ℂ W)
    (hV : ∀ a b, a ≠ b → ∀ x ∈ dV a, ∀ y ∈ dV b, PV x y = 0)
    (hW : ∀ a b, a ≠ b → ∀ x ∈ dW a, ∀ y ∈ dW b, PW x y = 0) :
    ∀ a a', a ≠ a' → ∀ x ∈ tensorDeg dV dW a, ∀ y ∈ tensorDeg dV dW a',
      PV.tensor PW x y = 0 := by
  intro a a' haa' x hx y hy
  refine sesq_iSup_left' _ _ (fun b x hx => ?_) x hx
  refine sesq_iSup_right' _ _ (fun b' y hy => ?_) y hy
  rw [Submodule.map₂_eq_span_image2] at hx hy
  refine sesq_span_left _ (fun x hx => ?_) x hx
  refine sesq_span_right _ (fun y hy => ?_) y hy
  obtain ⟨v, hv, w, hw, rfl⟩ := hx
  obtain ⟨v', hv', w', hw', rfl⟩ := hy
  simp only [TensorProduct.mk_apply, SesqForm.tensor_tmul]
  by_cases hb : b = b'
  · subst hb
    have : a - b ≠ a' - b := fun h => haa' (by simpa using h)
    rw [hW _ _ this w hw w' hw', mul_zero]
  · rw [hV _ _ hb v hv v' hv', zero_mul]

/-- The tensor grading spans. -/
theorem tensorDeg_span (dV : ι → Submodule ℂ V) (dW : ι → Submodule ℂ W) (hV : iSup dV = ⊤)
    (hW : iSup dW = ⊤) : iSup (tensorDeg dV dW) = ⊤ := by
  rw [eq_top_iff, ← TensorProduct.span_tmul_eq_top, Submodule.span_le]
  rintro _ ⟨x, y, rfl⟩
  have hx : x ∈ iSup dV := hV ▸ Submodule.mem_top
  have hy : y ∈ iSup dW := hW ▸ Submodule.mem_top
  refine Submodule.iSup_induction dV (motive := fun x => x ⊗ₜ[ℂ] y ∈ iSup (tensorDeg dV dW))
    hx ?_ (by simp) (fun x x' h h' => by
      beta_reduce at h h' ⊢; rw [TensorProduct.add_tmul]; exact Submodule.add_mem _ h h')
  intro b x hx
  refine Submodule.iSup_induction dW (motive := fun y => x ⊗ₜ[ℂ] y ∈ iSup (tensorDeg dV dW))
    hy ?_ (by simp) (fun y y' h h' => by
      beta_reduce at h h' ⊢; rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ h h')
  intro c y hy
  exact Submodule.mem_iSup_of_mem (b + c) (tmul_mem_tensorDeg dV dW hx hy)

/-- **Compatibility with additive gradings**: if the factor pieces sit in additive gradings `FV`,
`FW` along `φ`, and pure tensors of those land in `FT`, then the tensor pieces sit in `FT`. -/
theorem tensorDeg_le {κ : Type*} [AddCommGroup κ] (φ : ι →+ κ) (dV : ι → Submodule ℂ V)
    (dW : ι → Submodule ℂ W) (FV : κ → Submodule ℂ V) (FW : κ → Submodule ℂ W)
    (FT : κ → Submodule ℂ (V ⊗[ℂ] W))
    (hT : ∀ k k' x y, x ∈ FV k → y ∈ FW k' → x ⊗ₜ[ℂ] y ∈ FT (k + k'))
    (hdV : ∀ i, dV i ≤ FV (φ i)) (hdW : ∀ i, dW i ≤ FW (φ i)) (a : ι) :
    tensorDeg dV dW a ≤ FT (φ a) := by
  refine iSup_le fun b => ?_
  rw [Submodule.map₂_le]
  intro x hx y hy
  have h := hT _ _ x y (hdV b hx) (hdW (a - b) hy)
  rw [← map_add, add_sub_cancel] at h
  exact h

end Tensor

/-! ### Factor gradings -/

section Factors

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- The index `((2p, 0), m)` of the `p`-th layer at weight `m`. -/
abbrev layerIndex (p : ℕ) (m : ℤ) : (ℤ × ℤ) × ℂ := ((2 * (p : ℤ), 0), (m : ℂ))

/-- **The layer grading of a graded-unitary VOA**: `R = p` on the `p`-th orthogonal layer. -/
def layerDeg (B : InvariantForm W) (F : GradedFlag W) (i : (ℤ × ℤ) × ℂ) : Submodule ℂ 𝒱 :=
  ⨆ (m : ℤ) (p : ℕ) (_ : layerIndex p m = i),
    (F.layer m (LiRadical.gradedForm B m) p).map (W.grading m).subtype

theorem layerIndex_injective {p p' : ℕ} {m m' : ℤ} (h : layerIndex p m = layerIndex p' m') :
    p = p' ∧ m = m' := by
  simp only [layerIndex, Prod.mk.injEq, and_true] at h
  exact ⟨by omega, by exact_mod_cast h.2⟩

theorem layerDeg_orth (B : InvariantForm W) (R : RealStructure W) (F : GradedFlag W)
    (hGU : GradedUnitary B R F) (hrefl : GramRefl B) :
    ∀ a b, a ≠ b → ∀ x ∈ layerDeg B F a, ∀ y ∈ layerDeg B F b,
      carrierForm B R F hGU hrefl x y = 0 := by
  intro a b hab x hx y hy
  refine sesq_iSup_left' _ _ (fun m x hx => ?_) x hx
  refine sesq_iSup_left' _ _ (fun p x hx => ?_) x hx
  refine sesq_iSup_left' _ _ (fun ha x hx => ?_) x hx
  refine sesq_iSup_right' _ _ (fun m' y hy => ?_) y hy
  refine sesq_iSup_right' _ _ (fun p' y hy => ?_) y hy
  refine sesq_iSup_right' _ _ (fun hb y hy => ?_) y hy
  obtain ⟨x, hxl, rfl⟩ := Submodule.mem_map.mp hx
  obtain ⟨y, hyl, rfl⟩ := Submodule.mem_map.mp hy
  by_cases hm : m = m'
  · subst hm
    have hp : p ≠ p' := by
      rintro rfl; exact hab (ha.symm.trans hb)
    change carrierForm B R F hGU hrefl (x : 𝒱) (y : 𝒱) = 0
    rw [carrierForm_weight_same B R F hGU hrefl x.2 y.2]
    haveI := W.finrank m
    exact modForm_layer_ne F m _ (hrefl m) (hGU m).1 hp hxl hyl
  · exact carrierForm_weight_ne B R F hGU hrefl hm x.2 y.2

theorem layerDeg_span (B : InvariantForm W) (R : RealStructure W) (F : GradedFlag W)
    (hGU : GradedUnitary B R F) (hrefl : GramRefl B) : iSup (layerDeg B F) = ⊤ := by
  rw [eq_top_iff, ← W.isInternal.submodule_iSup_eq_top]
  refine iSup_le fun m => ?_
  intro x hx
  haveI := W.finrank m
  have hxm : (⟨x, hx⟩ : W.grading m) ∈ ⨆ p, F.layer m (LiRadical.gradedForm B m) p := by
    rw [iSup_layer_eq_top F (hrefl m) (hGU m).1]; exact Submodule.mem_top
  have hmap : x ∈ (⨆ p, F.layer m (LiRadical.gradedForm B m) p).map (W.grading m).subtype :=
    ⟨⟨x, hx⟩, hxm, rfl⟩
  rw [Submodule.map_iSup] at hmap
  refine (iSup_le fun p => ?_ : _ ≤ iSup (layerDeg B F)) hmap
  refine le_trans ?_ (le_iSup _ (layerIndex p m))
  exact le_iSup₂_of_le m p (le_iSup_of_le rfl le_rfl)

theorem layerDeg_le_gradingC (B : InvariantForm W) (F : GradedFlag W) (i : (ℤ × ℤ) × ℂ) :
    layerDeg B F i ≤ W.toPreVertexAlgebra.gradingC i.2 := by
  refine iSup_le fun m => iSup_le fun p => iSup_le fun h => ?_
  subst h
  rw [show (layerIndex p m).2 = (m : ℂ) from rfl, PreVertexAlgebra.gradingC_intCast]
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem layerDeg_ghost (B : InvariantForm W) (F : GradedFlag W) (i : (ℤ × ℤ) × ℂ)
    (hi : i.1.2 ≠ 0) : layerDeg B F i = ⊥ := by
  rw [eq_bot_iff]
  refine iSup_le fun m => iSup_le fun p => iSup_le fun h => ?_
  subst h
  exact absurd rfl hi

/-- **The trivial grading of a unitary VOA**: everything at `R = 0`, ghost number `0`. -/
def trivialDeg (W : VertexOperatorAlgebra 𝒱) (i : (ℤ × ℤ) × ℂ) : Submodule ℂ 𝒱 :=
  if i.1 = (0, 0) then W.toPreVertexAlgebra.gradingC i.2 else ⊥

theorem trivialDeg_le_gradingC (i : (ℤ × ℤ) × ℂ) :
    trivialDeg W i ≤ W.toPreVertexAlgebra.gradingC i.2 := by
  unfold trivialDeg; split_ifs <;> simp

theorem trivialDeg_ghost (i : (ℤ × ℤ) × ℂ) (hi : i.1.2 ≠ 0) : trivialDeg W i = ⊥ := by
  unfold trivialDeg
  rw [if_neg]
  intro h; exact hi (by rw [h])

theorem trivialDeg_span : iSup (trivialDeg W) = ⊤ := by
  rw [eq_top_iff, ← (W.toPreVertexAlgebra.toSuper).isInternal.submodule_iSup_eq_top]
  refine iSup_le fun h => le_trans ?_ (le_iSup _ ((0, 0), h))
  change W.toPreVertexAlgebra.gradingC h ≤ trivialDeg W ((0, 0), h)
  simp [trivialDeg]

theorem trivialDeg_orth (PW : SesqForm 𝒱)
    (hPW : ∀ h h' : ℂ, h ≠ h' → ∀ x ∈ W.toPreVertexAlgebra.gradingC h,
      ∀ y ∈ W.toPreVertexAlgebra.gradingC h', PW x y = 0) :
    ∀ a b, a ≠ b → ∀ x ∈ trivialDeg W a, ∀ y ∈ trivialDeg W b, PW x y = 0 := by
  rintro ⟨a1, a2⟩ ⟨b1, b2⟩ hab x hx y hy
  unfold trivialDeg at hx hy
  split_ifs at hx hy with h1 h2
  · subst h1; subst h2
    have : a2 ≠ b2 := fun h => hab (by rw [h])
    exact hPW a2 b2 this x hx y hy
  · simp only [Submodule.mem_bot] at hy; rw [hy, PW.zero_right]
  · simp only [Submodule.mem_bot] at hx; rw [hx, PW.zero_left]
  · simp only [Submodule.mem_bot] at hx; rw [hx, PW.zero_left]

end Factors

end

end VOA.ConcreteHodge
