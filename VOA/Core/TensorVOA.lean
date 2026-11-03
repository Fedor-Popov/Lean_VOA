/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Core.SuperVertexAlgebra
import VOA.Core.DongSuperNeg
import VOA.Core.SuperReconstruction
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# The tensor product of two vertex superalgebras

Given super vertex algebras `V` on `A` and `W` on `B`, this file constructs a
`SuperVertexAlgebra` structure on `A ⊗[ℂ] B` with

  `Y(u ⊗ v, z)(u' ⊗ v') = (-1)^{|v||u'|} (Y(u,z)u') ⊗ (Y(v,z)v')`,

the Koszul sign arising when the second factor's field passes the first factor's state.

## The shape of the construction

The point is to keep `Y` *manifestly linear* in `u ⊗ v` while carrying a sign that depends on
the **parity** of the second leg.  The device is the fermion-number involution `θ_B = (-1)^F`
of `B` (`ParityGrading.parityInvol`) together with the operator `Θ = θ_A ⊗ 1` on `A ⊗ B`
(`kappaTen V W 1`):

* `rawCoeff V W a b s` is the *sign-free* coefficient
  `(x ⊗ y) ↦ ∑ᶠ m, (a₍ₘ₎x) ⊗ (b₍ₛ₋ₘ₎y)`, an honest `ℂ`-linear endomorphism of `A ⊗ B`
  (the sum is finite because both `Y`s are lower truncated), bilinear in `(a,b)`;
* `tenY V W := 2⁻¹ • ( (·∘(1+Θ)) ∘ rawY + (·∘(1-Θ)) ∘ rawY ∘ (1 ⊗ θ_B) )`.

For `b` of parity `q` this collapses to `rawCoeff V W a b s ∘ (κ_q ⊗ 1)` with `κ_q = (-1)^{qF}`
on `A` (`tenY_tmul_parity`) — exactly the Koszul-signed formula — but the *definition* is a
composition of linear maps, so linearity is free.

## Locality

Locality comes from **Dong's lemma**, not by hand.  The two families

* `lftF V W a n = (a₍ₙ₎) ⊗ 1`,
* `rgtF V W q b n = κ_q ⊗ (b₍ₙ₎)`,

are pairwise `Localε`: `lftF`–`lftF` inherits `V`'s locality, `rgtF`–`rgtF` inherits `W`'s, and
`lftF`–`rgtF` *commute on the nose up to the Koszul sign* (`lftF_mul_rgtF_comm`) because they
act on different legs.  Since they commute exactly, the same-variable normal product `nprodε`
of `lftF` and `rgtF` **is** their plain product, i.e. is `tenY (a ⊗ b)`
(`tenY_tmul_eq_nprodε`).  Two applications of `dong_negε` then give locality of
`tenY (a ⊗ b)` against `tenY (a' ⊗ b')`, and a span argument extends it to the whole parity
components.

## The gradings

Both gradings are **convolutions**:

* `tenGrading V W h = ⨆_{h₁} (V.grading h₁) ⊗ (W.grading (h - h₁))`,
* `tenParity V W p = ⨆_{p₁} (V.parity p₁) ⊗ (W.parity (p - p₁))`.

`grading_mode`, `parity_mode`, `vacuum_mem`, `vacuum_parity` are proved for these.

## What is proved, and what is assumed

Everything except three purely *linear-algebraic* facts about the convolution families is
proved here; those three are collected in `TensorGradingHyp`:

* `DirectSum.IsInternal (tenGrading V W)`,
* `∀ h, FiniteDimensional ℂ (tenGrading V W h)`,
* `DirectSum.IsInternal (tenParity V W)`.

One further hypothesis is genuinely needed and is named `ParityCompatible`: the parity
involution must preserve the weight spaces (the algebra is *bi*graded).  The
`SuperVertexAlgebra` axioms deliberately keep the two gradings independent, so this has to be
asked for; it holds in every example.  See the closing note.

## Main definitions

* `rawCoeff`, `rawY` — the sign-free tensor coefficient and its linear packaging.
* `tenY` — the tensor-product state–field correspondence.
* `tenGrading`, `tenParity` — the convolution gradings.
* `tensorSVA` — the `SuperVertexAlgebra` structure on `A ⊗[ℂ] B`.

## References
* Frenkel–Huang–Lepowsky, *On axiomatic approaches to vertex operator algebras*, §3;
  Kac, *Vertex Algebras for Beginners*, §4.3;  Lepowsky–Li, §3.12.
-/

namespace VOA

namespace TensorVA

open Module (End)
open scoped TensorProduct

variable {A B C D : Type*}
variable [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
variable [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D]

/-! ## §0  Generic helpers

Small, entirely general facts: post-composition with a linear map commutes with the locality
operator `(z₁-z₂)^N`, `IsField` is closed under the linear operations, and an algebraically
defined sum of members of a submodule is a member. -/

/-- Post-composing a two-variable formal distribution with a linear map commutes with
multiplication by `(z₁ - z₂)^N`. -/
theorem mulBySubPow_congrMap (Ψ : C →ₗ[ℂ] D) (N : ℕ) (f : FormalDist₂ C) :
    mulBySubPow N (fun m n => Ψ (f m n)) = fun m n => Ψ (mulBySubPow N f m n) := by
  induction N with
  | zero =>
    apply FormalDist₂.ext; intro m n
    simp only [mulBySubPow_zero, LinearMap.id_coe, id_eq]
  | succ k ih =>
    apply FormalDist₂.ext; intro m n
    simp only [mulBySubPow_succ, LinearMap.comp_apply, mulBySub_apply, ih, map_sub]

/-- **Transfer of `ε`-locality along a linear map of operator algebras.**  If the twisted
commutator of `a'` and `b'` is the image of that of `a` and `b` under a linear `Ψ`, then
`ε`-locality transfers.  Every locality statement about the two lifted families of fields
below is an instance. -/
theorem localε_transfer {ε : ℂ} (Ψ : End ℂ C →ₗ[ℂ] End ℂ D)
    {a b : FormalDist (End ℂ C)} {a' b' : FormalDist (End ℂ D)}
    (h : ∀ m n : ℤ, bracketDistε ε a' b' m n = Ψ (bracketDistε ε a b m n))
    (hl : Localε ε a b) : Localε ε a' b' := by
  obtain ⟨N, hN⟩ := hl
  refine ⟨N, ?_⟩
  have he : bracketDistε ε a' b' = fun m n => Ψ (bracketDistε ε a b m n) := by
    apply FormalDist₂.ext; exact h
  rw [he, mulBySubPow_congrMap Ψ N, hN]
  apply FormalDist₂.ext; intro m n
  exact map_zero Ψ

/-- The zero distribution is a field. -/
theorem isField_zero : IsField (0 : FormalDist (End ℂ C)) := fun _ => ⟨0, fun _ _ => rfl⟩

/-- Fields are closed under addition. -/
theorem isField_add {f g : FormalDist (End ℂ C)} (hf : IsField f) (hg : IsField g) :
    IsField (f + g) := by
  intro x
  obtain ⟨N₁, h₁⟩ := hf x
  obtain ⟨N₂, h₂⟩ := hg x
  refine ⟨min N₁ N₂, fun n hn => ?_⟩
  have hval : (f + g) n x = f n x + g n x := rfl
  rw [hval, h₁ n (by omega), h₂ n (by omega), add_zero]

/-- Fields are closed under scaling. -/
theorem isField_smulF (c : ℂ) {f : FormalDist (End ℂ C)} (hf : IsField f) : IsField (c • f) := by
  intro x
  obtain ⟨N, h⟩ := hf x
  refine ⟨N, fun n hn => ?_⟩
  have hval : (c • f) n x = c • f n x := rfl
  rw [hval, h n hn, smul_zero]

/-- Fields are closed under post-composition with a fixed operator. -/
theorem isField_postComp (P : End ℂ C) {f : FormalDist (End ℂ C)} (hf : IsField f) :
    IsField (fun s => f s * P) := by
  intro x
  obtain ⟨N, h⟩ := hf (P x)
  refine ⟨N, fun n hn => ?_⟩
  have hval : (fun s => f s * P) n x = f n (P x) := rfl
  rw [hval, h n hn]

/-- An algebraically-defined sum of members of a submodule lies in the submodule. -/
theorem finsum_mem_sub {ι : Type*} (P : Submodule ℂ C) (f : ι → C) (hf : ∀ i, f i ∈ P) :
    (∑ᶠ i, f i) ∈ P :=
  finsum_induction (fun x => x ∈ P) P.zero_mem (fun _ _ hx hy => P.add_mem hx hy) hf

/-- Induction over a tensor product: a predicate closed under the module operations and holding
on pure tensors holds everywhere. -/
theorem tmul_induction {motive : A ⊗[ℂ] B → Prop} (hz : motive 0)
    (hadd : ∀ x y, motive x → motive y → motive (x + y))
    (hsmul : ∀ (c : ℂ) x, motive x → motive (c • x))
    (htmul : ∀ (a : A) (b : B), motive (a ⊗ₜ[ℂ] b)) (u : A ⊗[ℂ] B) : motive u := by
  have key : ∀ w ∈ Submodule.span ℂ {t : A ⊗[ℂ] B | ∃ a b, a ⊗ₜ[ℂ] b = t}, motive w := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx => obtain ⟨a, b, rfl⟩ := hx; exact htmul a b
    | zero => exact hz
    | add x y _ _ hx hy => exact hadd x y hx hy
    | smul c x _ hx => exact hsmul c x hx
  exact key u (by rw [TensorProduct.span_tmul_eq_top]; trivial)

/-! ## §1  Coefficient-index reformulations of the axioms

The `SuperVertexAlgebra` axioms are phrased in terms of `mode`; the tensor construction is
naturally phrased in terms of the *coefficient* index (`Y u j` is the `z^j` coefficient, and
`mode (Y u) n = Y u (-n-1)`).  These five lemmas do the translation once and for all. -/

/-- Regularity in coefficient form: `Y(u,z)` is a field. -/
theorem isField_superY (V : SuperVertexAlgebra A) (a : A) : IsField (V.Y a) := by
  intro x
  obtain ⟨N, hN⟩ := V.regularity a x
  refine ⟨-N, fun j hj => ?_⟩
  have h := hN (-j - 1) (by omega)
  rw [mode_apply] at h
  have e1 : (-(-j - 1) - 1 : ℤ) = j := by ring
  rwa [e1] at h

/-- VA3 in coefficient form: the `z⁰` coefficient creates. -/
theorem Ycoeff_vacuum (V : SuperVertexAlgebra A) (a : A) : V.Y a 0 V.vacuum = a := by
  have h := (V.creation a).1
  rw [mode_apply] at h
  have e1 : (-(-1 : ℤ) - 1 : ℤ) = 0 := by ring
  rwa [e1] at h

/-- VA3 in coefficient form: strictly negative coefficients kill the vacuum. -/
theorem Ycoeff_vacuum_neg (V : SuperVertexAlgebra A) (a : A) {j : ℤ} (hj : j < 0) :
    V.Y a j V.vacuum = 0 := by
  have h := (V.creation a).2 (-j - 1) (by omega)
  rw [mode_apply] at h
  have e1 : (-(-j - 1) - 1 : ℤ) = j := by ring
  rwa [e1] at h

/-- VA1 in coefficient form: weights add and shift by the coefficient index. -/
theorem Ycoeff_grading (V : SuperVertexAlgebra A) {h k : ℂ} {a x : A} (ha : a ∈ V.grading h)
    (hx : x ∈ V.grading k) (j : ℤ) : V.Y a j x ∈ V.grading (h + k + j) := by
  have hmem := V.grading_mode a ha x hx (-j - 1)
  rw [mode_apply] at hmem
  have e1 : (-(-j - 1) - 1 : ℤ) = j := by ring
  rw [e1] at hmem
  have e2 : h + k - (((-j - 1 : ℤ)) : ℂ) - 1 = h + k + (j : ℂ) := by push_cast; ring
  rwa [e2] at hmem

/-- VA1′ in coefficient form: parities add. -/
theorem Ycoeff_parity (V : SuperVertexAlgebra A) {p q : ZMod 2} {a x : A} (ha : a ∈ V.parity p)
    (hx : x ∈ V.parity q) (j : ℤ) : V.Y a j x ∈ V.parity (p + q) := by
  have hmem := V.parity_mode a ha x hx (-j - 1)
  rw [mode_apply] at hmem
  have e1 : (-(-j - 1) - 1 : ℤ) = j := by ring
  rwa [e1] at hmem

/-! ## §2  The parity involution of a super vertex algebra -/

/-- The parity grading underlying a super vertex algebra. -/
def parGr (V : SuperVertexAlgebra A) : ParityGrading A := ⟨V.parity, V.parity_isInternal⟩

@[simp] theorem parGr_parity (V : SuperVertexAlgebra A) (p : ZMod 2) :
    (parGr V).parity p = V.parity p := rfl

/-- `(-1)^{0·F} = 1`. -/
theorem koszulOp_zero (P : ParityGrading A) : P.koszulOp 0 = LinearMap.id := by
  change (if (0 : ZMod 2) = 0 then LinearMap.id else P.parityInvol) = LinearMap.id
  rw [if_pos rfl]

/-- `(-1)^{1·F} = (-1)^F`. -/
theorem koszulOp_one (P : ParityGrading A) : P.koszulOp 1 = P.parityInvol := by
  change (if (1 : ZMod 2) = 0 then LinearMap.id else P.parityInvol) = P.parityInvol
  rw [if_neg (by decide)]

/-- The Koszul operators commute with each other (each is `1` or `(-1)^F`). -/
theorem koszulOp_comm_apply (P : ParityGrading A) (r r' : ZMod 2) (x : A) :
    P.koszulOp r (P.koszulOp r' x) = P.koszulOp r' (P.koszulOp r x) := by
  rcases zmod2_cases r with hr | hr <;> rcases zmod2_cases r' with hr' | hr' <;>
    subst hr <;> subst hr' <;>
    simp only [koszulOp_zero, koszulOp_one, LinearMap.id_coe, id_eq]

/-- **Compatibility of the two gradings.**  The parity involution preserves each weight space —
i.e. the algebra is genuinely *bi*graded.  The `SuperVertexAlgebra` axioms keep the two
gradings independent, so this must be assumed; it holds in every example. -/
def ParityCompatible (V : SuperVertexAlgebra A) : Prop :=
  ∀ (h : ℂ) (u : A), u ∈ V.grading h → (parGr V).parityInvol u ∈ V.grading h

/-- A Koszul operator always preserves the parity spaces (it acts there by a scalar). -/
theorem koszulOp_mem_parity (V : SuperVertexAlgebra A) (q : ZMod 2) {r : ZMod 2} {u : A}
    (hu : u ∈ V.parity r) : (parGr V).koszulOp q u ∈ V.parity r := by
  rw [(parGr V).koszulOp_homog q (show u ∈ (parGr V).parity r from hu)]
  exact Submodule.smul_mem _ _ hu

/-- The involution always preserves the parity spaces. -/
theorem parityInvol_mem_parity (V : SuperVertexAlgebra A) {r : ZMod 2} {u : A}
    (hu : u ∈ V.parity r) : (parGr V).parityInvol u ∈ V.parity r := by
  rw [(parGr V).parityInvol_homog (show u ∈ (parGr V).parity r from hu)]
  exact Submodule.smul_mem _ _ hu

/-! ## §3  The sign-free tensor coefficient `rawCoeff`

`rawCoeff V W a b s` is the `z^s`-coefficient of the *naive* product `Y_A(a,z) ⊗ Y_B(b,z)`,
with no Koszul sign at all.  It is an honest linear endomorphism of `A ⊗ B`, bilinear in
`(a,b)`. -/

/-- The antidiagonal defining `rawCoeff` has finite support: `a₍ₘ₎x` dies for `m ≪ 0` and
`b₍ₛ₋ₘ₎y` dies for `m ≫ 0`.  Both bounds are uniform because `x` and `y` are fixed. -/
theorem raw_support (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (a : A) (b : B)
    (s : ℤ) (x : A) (y : B) :
    (Function.support (fun m : ℤ => (V.Y a m x) ⊗ₜ[ℂ] (W.Y b (s - m) y))).Finite := by
  obtain ⟨N₁, hN₁⟩ := isField_superY V a x
  obtain ⟨N₂, hN₂⟩ := isField_superY W b y
  refine Set.Finite.subset (Set.finite_Icc N₁ (s - N₂)) ?_
  intro m hm
  rw [Function.mem_support] at hm
  rw [Set.mem_Icc]
  constructor
  · by_contra hc
    exact hm (by rw [hN₁ m (by omega), TensorProduct.zero_tmul])
  · by_contra hc
    exact hm (by rw [hN₂ (s - m) (by omega), TensorProduct.tmul_zero])

/-- The bilinear form underlying `rawCoeff`. -/
noncomputable def rawBil (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (a : A) (b : B)
    (s : ℤ) : A →ₗ[ℂ] B →ₗ[ℂ] A ⊗[ℂ] B where
  toFun x :=
    { toFun := fun y => ∑ᶠ m : ℤ, (V.Y a m x) ⊗ₜ[ℂ] (W.Y b (s - m) y)
      map_add' := fun y y' => by
        rw [← finsum_add_distrib (raw_support V W a b s x y) (raw_support V W a b s x y')]
        refine finsum_congr fun m => ?_
        rw [map_add, TensorProduct.tmul_add]
      map_smul' := fun c y => by
        rw [RingHom.id_apply, smul_finsum' c (raw_support V W a b s x y)]
        refine finsum_congr fun m => ?_
        rw [map_smul, TensorProduct.tmul_smul] }
  map_add' x x' := by
    apply LinearMap.ext; intro y
    change (∑ᶠ m : ℤ, (V.Y a m (x + x')) ⊗ₜ[ℂ] (W.Y b (s - m) y))
        = (∑ᶠ m : ℤ, (V.Y a m x) ⊗ₜ[ℂ] (W.Y b (s - m) y))
          + (∑ᶠ m : ℤ, (V.Y a m x') ⊗ₜ[ℂ] (W.Y b (s - m) y))
    rw [← finsum_add_distrib (raw_support V W a b s x y) (raw_support V W a b s x' y)]
    refine finsum_congr fun m => ?_
    rw [map_add, TensorProduct.add_tmul]
  map_smul' c x := by
    apply LinearMap.ext; intro y
    change (∑ᶠ m : ℤ, (V.Y a m (c • x)) ⊗ₜ[ℂ] (W.Y b (s - m) y))
        = c • (∑ᶠ m : ℤ, (V.Y a m x) ⊗ₜ[ℂ] (W.Y b (s - m) y))
    rw [smul_finsum' c (raw_support V W a b s x y)]
    refine finsum_congr fun m => ?_
    rw [map_smul, TensorProduct.smul_tmul']

/-- The **sign-free tensor coefficient**: the `z^s` coefficient of `Y_A(a,z) ⊗ Y_B(b,z)`. -/
noncomputable def rawCoeff (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (a : A) (b : B)
    (s : ℤ) : A ⊗[ℂ] B →ₗ[ℂ] A ⊗[ℂ] B :=
  TensorProduct.lift (rawBil V W a b s)

@[simp] theorem rawCoeff_tmul (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (a : A)
    (b : B) (s : ℤ) (x : A) (y : B) :
    rawCoeff V W a b s (x ⊗ₜ[ℂ] y) = ∑ᶠ m : ℤ, (V.Y a m x) ⊗ₜ[ℂ] (W.Y b (s - m) y) :=
  TensorProduct.lift.tmul x y

theorem rawCoeff_add_left (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (a a' : A)
    (b : B) (s : ℤ) : rawCoeff V W (a + a') b s = rawCoeff V W a b s + rawCoeff V W a' b s := by
  apply TensorProduct.ext'
  intro x y
  rw [LinearMap.add_apply, rawCoeff_tmul, rawCoeff_tmul, rawCoeff_tmul,
    ← finsum_add_distrib (raw_support V W a b s x y) (raw_support V W a' b s x y)]
  refine finsum_congr fun m => ?_
  have hY : V.Y (a + a') m = V.Y a m + V.Y a' m := by rw [map_add]; rfl
  rw [hY]
  change (V.Y a m x + V.Y a' m x) ⊗ₜ[ℂ] (W.Y b (s - m) y)
      = (V.Y a m x) ⊗ₜ[ℂ] (W.Y b (s - m) y) + (V.Y a' m x) ⊗ₜ[ℂ] (W.Y b (s - m) y)
  rw [TensorProduct.add_tmul]

theorem rawCoeff_smul_left (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (c : ℂ) (a : A)
    (b : B) (s : ℤ) : rawCoeff V W (c • a) b s = c • rawCoeff V W a b s := by
  apply TensorProduct.ext'
  intro x y
  rw [LinearMap.smul_apply, rawCoeff_tmul, rawCoeff_tmul,
    smul_finsum' c (raw_support V W a b s x y)]
  refine finsum_congr fun m => ?_
  have hY : V.Y (c • a) m = c • V.Y a m := by rw [map_smul]; rfl
  rw [hY]
  change (c • V.Y a m x) ⊗ₜ[ℂ] (W.Y b (s - m) y) = c • ((V.Y a m x) ⊗ₜ[ℂ] (W.Y b (s - m) y))
  rw [TensorProduct.smul_tmul']

theorem rawCoeff_add_right (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (a : A)
    (b b' : B) (s : ℤ) :
    rawCoeff V W a (b + b') s = rawCoeff V W a b s + rawCoeff V W a b' s := by
  apply TensorProduct.ext'
  intro x y
  rw [LinearMap.add_apply, rawCoeff_tmul, rawCoeff_tmul, rawCoeff_tmul,
    ← finsum_add_distrib (raw_support V W a b s x y) (raw_support V W a b' s x y)]
  refine finsum_congr fun m => ?_
  have hY : W.Y (b + b') (s - m) = W.Y b (s - m) + W.Y b' (s - m) := by rw [map_add]; rfl
  rw [hY]
  change (V.Y a m x) ⊗ₜ[ℂ] (W.Y b (s - m) y + W.Y b' (s - m) y)
      = (V.Y a m x) ⊗ₜ[ℂ] (W.Y b (s - m) y) + (V.Y a m x) ⊗ₜ[ℂ] (W.Y b' (s - m) y)
  rw [TensorProduct.tmul_add]

theorem rawCoeff_smul_right (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (c : ℂ) (a : A)
    (b : B) (s : ℤ) : rawCoeff V W a (c • b) s = c • rawCoeff V W a b s := by
  apply TensorProduct.ext'
  intro x y
  rw [LinearMap.smul_apply, rawCoeff_tmul, rawCoeff_tmul,
    smul_finsum' c (raw_support V W a b s x y)]
  refine finsum_congr fun m => ?_
  have hY : W.Y (c • b) (s - m) = c • W.Y b (s - m) := by rw [map_smul]; rfl
  rw [hY]
  change (V.Y a m x) ⊗ₜ[ℂ] (c • W.Y b (s - m) y) = c • ((V.Y a m x) ⊗ₜ[ℂ] (W.Y b (s - m) y))
  rw [TensorProduct.tmul_smul]

/-- `rawCoeff` as a bilinear map into the formal distributions. -/
noncomputable def rawFld (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) :
    A →ₗ[ℂ] B →ₗ[ℂ] FormalDist (End ℂ (A ⊗[ℂ] B)) where
  toFun a :=
    { toFun := fun b => fun s => rawCoeff V W a b s
      map_add' := fun b b' => by
        funext s
        change rawCoeff V W a (b + b') s = rawCoeff V W a b s + rawCoeff V W a b' s
        rw [rawCoeff_add_right]
      map_smul' := fun c b => by
        funext s
        change rawCoeff V W a (c • b) s = c • rawCoeff V W a b s
        rw [rawCoeff_smul_right] }
  map_add' a a' := by
    apply LinearMap.ext; intro b
    funext s
    change rawCoeff V W (a + a') b s = rawCoeff V W a b s + rawCoeff V W a' b s
    rw [rawCoeff_add_left]
  map_smul' c a := by
    apply LinearMap.ext; intro b
    funext s
    change rawCoeff V W (c • a) b s = c • rawCoeff V W a b s
    rw [rawCoeff_smul_left]

/-- The sign-free tensor operator, as a linear map on `A ⊗ B`. -/
noncomputable def rawY (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) :
    A ⊗[ℂ] B →ₗ[ℂ] FormalDist (End ℂ (A ⊗[ℂ] B)) :=
  TensorProduct.lift (rawFld V W)

theorem rawY_tmul (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (a : A) (b : B) :
    rawY V W (a ⊗ₜ[ℂ] b) = fun s => rawCoeff V W a b s :=
  TensorProduct.lift.tmul a b

/-- `rawCoeff V W a b` is a field. -/
theorem isField_rawCoeff (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (a : A) (b : B) :
    IsField (fun s => rawCoeff V W a b s) := by
  intro z
  refine tmul_induction (motive := fun z => ∃ N : ℤ, ∀ n : ℤ, n < N → rawCoeff V W a b n z = 0)
    ⟨0, fun n _ => map_zero _⟩ ?_ ?_ ?_ z
  · rintro w w' ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
    exact ⟨min N₁ N₂, fun n hn => by rw [map_add, h₁ n (by omega), h₂ n (by omega), add_zero]⟩
  · rintro c w ⟨N, h⟩
    exact ⟨N, fun n hn => by rw [map_smul, h n hn, smul_zero]⟩
  · intro x y
    obtain ⟨N₁, hN₁⟩ := isField_superY V a x
    obtain ⟨N₂, hN₂⟩ := isField_superY W b y
    refine ⟨N₁ + N₂, fun n hn => ?_⟩
    rw [rawCoeff_tmul]
    refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
    by_cases hm : m < N₁
    · rw [hN₁ m hm, TensorProduct.zero_tmul]
    · rw [hN₂ (n - m) (by omega), TensorProduct.tmul_zero]

/-! ## §4  The tensor-product vertex operator -/

/-- The Koszul dressing operator `κ_q ⊗ 1` on `A ⊗ B`. -/
noncomputable def kappaTen (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (q : ZMod 2) :
    End ℂ (A ⊗[ℂ] B) :=
  TensorProduct.map ((parGr V).koszulOp q) (LinearMap.id : B →ₗ[ℂ] B)

@[simp] theorem kappaTen_tmul (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (q : ZMod 2)
    (x : A) (y : B) : kappaTen V W q (x ⊗ₜ[ℂ] y) = ((parGr V).koszulOp q x) ⊗ₜ[ℂ] y := by
  simp only [kappaTen, TensorProduct.map_tmul, LinearMap.id_coe, id_eq]

theorem kappaTen_zero (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) :
    kappaTen V W 0 = (LinearMap.id : A ⊗[ℂ] B →ₗ[ℂ] A ⊗[ℂ] B) := by
  change TensorProduct.map ((parGr V).koszulOp 0) (LinearMap.id : B →ₗ[ℂ] B) = LinearMap.id
  rw [koszulOp_zero, TensorProduct.map_id]

/-- Right-composition with a fixed operator, as a linear map on formal distributions. -/
noncomputable def postCompHom (P : End ℂ C) :
    FormalDist (End ℂ C) →ₗ[ℂ] FormalDist (End ℂ C) where
  toFun f := fun s => f s * P
  map_add' f g := by funext s; exact add_mul (f s) (g s) P
  map_smul' c f := by funext s; exact smul_mul_assoc c (f s) P

@[simp] theorem postCompHom_apply (P : End ℂ C) (f : FormalDist (End ℂ C)) (s : ℤ) :
    postCompHom P f s = f s * P := rfl

/-- **The tensor-product state–field correspondence.**  Manifestly linear: the Koszul sign
enters through the involution `θ_B` of the second factor and the operator `Θ = θ_A ⊗ 1` of the
first, both fixed linear maps. -/
noncomputable def tenY (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) :
    A ⊗[ℂ] B →ₗ[ℂ] FormalDist (End ℂ (A ⊗[ℂ] B)) :=
  (2⁻¹ : ℂ) •
    ((postCompHom (1 + kappaTen V W 1)).comp (rawY V W)
      + (postCompHom (1 - kappaTen V W 1)).comp
          ((rawY V W).comp
            (TensorProduct.map (LinearMap.id : A →ₗ[ℂ] A) ((parGr W).parityInvol))))

theorem tenY_tmul_eq (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (a : A) (b : B) :
    tenY V W (a ⊗ₜ[ℂ] b)
      = (2⁻¹ : ℂ) • ((fun s => rawCoeff V W a b s * (1 + kappaTen V W 1))
          + (fun s => rawCoeff V W a ((parGr W).parityInvol b) s * (1 - kappaTen V W 1))) := by
  change ((2⁻¹ : ℂ) •
      ((postCompHom (1 + kappaTen V W 1)).comp (rawY V W)
        + (postCompHom (1 - kappaTen V W 1)).comp
            ((rawY V W).comp
              (TensorProduct.map (LinearMap.id : A →ₗ[ℂ] A) ((parGr W).parityInvol)))))
        (a ⊗ₜ[ℂ] b) = _
  rw [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_coe, id_eq, rawY_tmul, rawY_tmul]
  rfl

theorem tenY_tmul_apply (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (a : A) (b : B)
    (s : ℤ) (z : A ⊗[ℂ] B) :
    tenY V W (a ⊗ₜ[ℂ] b) s z
      = (2⁻¹ : ℂ) • (rawCoeff V W a b s (z + kappaTen V W 1 z)
          + rawCoeff V W a ((parGr W).parityInvol b) s (z - kappaTen V W 1 z)) := by
  have e1 : ((1 : End ℂ (A ⊗[ℂ] B)) + kappaTen V W 1) z = z + kappaTen V W 1 z := by
    rw [LinearMap.add_apply]; rfl
  have e2 : ((1 : End ℂ (A ⊗[ℂ] B)) - kappaTen V W 1) z = z - kappaTen V W 1 z := by
    rw [LinearMap.sub_apply]; rfl
  rw [tenY_tmul_eq]
  change ((2⁻¹ : ℂ) • ((rawCoeff V W a b s * (1 + kappaTen V W 1))
      + (rawCoeff V W a ((parGr W).parityInvol b) s * (1 - kappaTen V W 1)))) z = _
  rw [LinearMap.smul_apply, LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply,
    e1, e2]

/-- **The Koszul-signed formula.**  For a parity-homogeneous second leg, `tenY` really is
`Y_A(a,z) ⊗ Y_B(b,z)` dressed by the Koszul operator `(-1)^{|b|F_A} ⊗ 1`. -/
theorem tenY_tmul_parity (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (a : A)
    {q : ZMod 2} {b : B} (hb : b ∈ W.parity q) (s : ℤ) (z : A ⊗[ℂ] B) :
    tenY V W (a ⊗ₜ[ℂ] b) s z = rawCoeff V W a b s (kappaTen V W q z) := by
  have hθb : (parGr W).parityInvol b = parSign q • b :=
    (parGr W).parityInvol_homog (show b ∈ (parGr W).parity q from hb)
  rw [tenY_tmul_apply, hθb, rawCoeff_smul_right]
  rcases zmod2_cases q with hq | hq <;> subst hq
  · rw [kappaTen_zero]
    simp only [parSign_zero, one_smul, LinearMap.id_coe, id_eq, LinearMap.smul_apply, map_add,
      map_sub]
    module
  · simp only [parSign_one, LinearMap.smul_apply, map_add, map_sub]
    module

/-! ## §5  The two lifted families of fields

`lftF` acts through the first leg only; `rgtF` acts through the second leg, dressed by the
Koszul operator on the first.  They commute *exactly* up to the Koszul sign, which is what
makes the normal-ordered product of the two equal to their plain product — and hence what lets
Dong's lemma deliver the locality of `tenY`. -/

/-- The left leg's field `a₍ₙ₎ ⊗ 1`. -/
noncomputable def lftF (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (a : A) :
    FormalDist (End ℂ (A ⊗[ℂ] B)) :=
  fun m => TensorProduct.map (V.Y a m) (LinearMap.id : B →ₗ[ℂ] B)

/-- The right leg's field `κ_q ⊗ b₍ₙ₎`. -/
noncomputable def rgtF (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (q : ZMod 2)
    (b : B) : FormalDist (End ℂ (A ⊗[ℂ] B)) :=
  fun n => TensorProduct.map ((parGr V).koszulOp q) (W.Y b n)

@[simp] theorem lftF_tmul (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (a : A) (m : ℤ)
    (x : A) (y : B) : lftF V W a m (x ⊗ₜ[ℂ] y) = (V.Y a m x) ⊗ₜ[ℂ] y := by
  simp only [lftF, TensorProduct.map_tmul, LinearMap.id_coe, id_eq]

@[simp] theorem rgtF_tmul (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (q : ZMod 2)
    (b : B) (n : ℤ) (x : A) (y : B) :
    rgtF V W q b n (x ⊗ₜ[ℂ] y) = ((parGr V).koszulOp q x) ⊗ₜ[ℂ] (W.Y b n y) := by
  simp only [rgtF, TensorProduct.map_tmul]

theorem isField_lftF (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (a : A) :
    IsField (lftF V W a) := by
  intro z
  refine tmul_induction (motive := fun z => ∃ N : ℤ, ∀ n : ℤ, n < N → lftF V W a n z = 0)
    ⟨0, fun n _ => map_zero _⟩ ?_ ?_ ?_ z
  · rintro w w' ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
    exact ⟨min N₁ N₂, fun n hn => by rw [map_add, h₁ n (by omega), h₂ n (by omega), add_zero]⟩
  · rintro c w ⟨N, h⟩
    exact ⟨N, fun n hn => by rw [map_smul, h n hn, smul_zero]⟩
  · intro x y
    obtain ⟨N, hN⟩ := isField_superY V a x
    exact ⟨N, fun n hn => by rw [lftF_tmul, hN n hn, TensorProduct.zero_tmul]⟩

theorem isField_rgtF (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (q : ZMod 2) (b : B) :
    IsField (rgtF V W q b) := by
  intro z
  refine tmul_induction (motive := fun z => ∃ N : ℤ, ∀ n : ℤ, n < N → rgtF V W q b n z = 0)
    ⟨0, fun n _ => map_zero _⟩ ?_ ?_ ?_ z
  · rintro w w' ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
    exact ⟨min N₁ N₂, fun n hn => by rw [map_add, h₁ n (by omega), h₂ n (by omega), add_zero]⟩
  · rintro c w ⟨N, h⟩
    exact ⟨N, fun n hn => by rw [map_smul, h n hn, smul_zero]⟩
  · intro x y
    obtain ⟨N, hN⟩ := isField_superY W b y
    exact ⟨N, fun n hn => by rw [rgtF_tmul, hN n hn, TensorProduct.tmul_zero]⟩

/-- `f ↦ f ⊗ 1`, as a linear map of operator algebras. -/
noncomputable def mapLeftHom (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) :
    End ℂ A →ₗ[ℂ] End ℂ (A ⊗[ℂ] B) where
  toFun f := TensorProduct.map f (LinearMap.id : B →ₗ[ℂ] B)
  map_add' f g := by
    apply TensorProduct.ext'; intro x y
    simp only [TensorProduct.map_tmul, LinearMap.add_apply, LinearMap.id_coe, id_eq,
      TensorProduct.add_tmul]
  map_smul' c f := by
    apply TensorProduct.ext'; intro x y
    simp only [RingHom.id_apply, TensorProduct.map_tmul, LinearMap.smul_apply, LinearMap.id_coe,
      id_eq, TensorProduct.smul_tmul']

theorem mapLeftHom_apply (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (f : End ℂ A) :
    mapLeftHom V W f = TensorProduct.map f (LinearMap.id : B →ₗ[ℂ] B) := rfl

theorem mapLeftHom_mul (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (f g : End ℂ A) :
    mapLeftHom V W (f * g) = mapLeftHom V W f * mapLeftHom V W g := by
  apply TensorProduct.ext'; intro x y
  simp only [mapLeftHom_apply, TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
    Module.End.mul_apply]

/-- `g ↦ μ ⊗ g`, as a linear map of operator algebras (for a fixed `μ` on the first leg). -/
noncomputable def mapRightHom (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B)
    (μ : End ℂ A) : End ℂ B →ₗ[ℂ] End ℂ (A ⊗[ℂ] B) where
  toFun g := TensorProduct.map μ g
  map_add' g g' := by
    apply TensorProduct.ext'; intro x y
    simp only [TensorProduct.map_tmul, LinearMap.add_apply, TensorProduct.tmul_add]
  map_smul' c g := by
    apply TensorProduct.ext'; intro x y
    simp only [RingHom.id_apply, TensorProduct.map_tmul, LinearMap.smul_apply,
      TensorProduct.tmul_smul]

theorem mapRightHom_apply (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (μ : End ℂ A)
    (g : End ℂ B) : mapRightHom V W μ g = TensorProduct.map μ g := rfl

/-! ### The three pairwise localities -/

/-- Left-leg fields inherit `V`'s locality. -/
theorem localε_lftF (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) {p p' : ZMod 2}
    {a a' : A} (ha : a ∈ V.parity p) (ha' : a' ∈ V.parity p') :
    Localε (koszul p p') (lftF V W a) (lftF V W a') := by
  refine localε_transfer (mapLeftHom V W) ?_ (V.locality a ha a' ha')
  intro m n
  rw [bracketDistε_apply, bracketDistε_apply, map_sub, map_smul, mapLeftHom_mul, mapLeftHom_mul]
  rfl

/-- Right-leg fields inherit `W`'s locality; the two Koszul dressings commute. -/
theorem localε_rgtF (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (r r' : ZMod 2)
    {q q' : ZMod 2} {b b' : B} (hb : b ∈ W.parity q) (hb' : b' ∈ W.parity q') :
    Localε (koszul q q') (rgtF V W r b) (rgtF V W r' b') := by
  refine localε_transfer
    (mapRightHom V W ((parGr V).koszulOp r * (parGr V).koszulOp r')) ?_ (W.locality b hb b' hb')
  intro m n
  have e1 : rgtF V W r b m * rgtF V W r' b' n
      = mapRightHom V W ((parGr V).koszulOp r * (parGr V).koszulOp r') (W.Y b m * W.Y b' n) := by
    apply TensorProduct.ext'; intro x y
    simp only [Module.End.mul_apply, rgtF_tmul, mapRightHom_apply, TensorProduct.map_tmul]
  have e2 : rgtF V W r' b' n * rgtF V W r b m
      = mapRightHom V W ((parGr V).koszulOp r * (parGr V).koszulOp r') (W.Y b' n * W.Y b m) := by
    apply TensorProduct.ext'; intro x y
    simp only [Module.End.mul_apply, rgtF_tmul, mapRightHom_apply, TensorProduct.map_tmul]
    rw [koszulOp_comm_apply]
  rw [bracketDistε_apply, bracketDistε_apply, e1, e2, map_sub, map_smul]

/-- **The two legs commute on the nose, up to the Koszul sign.**  This is the exact
(anti)commutation that makes the tensor construction work: no locality bound is needed. -/
theorem lftF_mul_rgtF_comm (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) {p : ZMod 2}
    {a : A} (ha : a ∈ V.parity p) (q : ZMod 2) (b : B) (m n : ℤ) :
    lftF V W a m * rgtF V W q b n = koszul p q • (rgtF V W q b n * lftF V W a m) := by
  have key : ∀ (r : ZMod 2) (w : A), w ∈ V.parity r →
      V.Y a m ((parGr V).koszulOp q w) = koszul p q • ((parGr V).koszulOp q (V.Y a m w)) := by
    intro r w hw
    rw [(parGr V).koszulOp_homog q (show w ∈ (parGr V).parity r from hw), map_smul,
      (parGr V).koszulOp_homog q
        (show V.Y a m w ∈ (parGr V).parity (p + r) from Ycoeff_parity V ha hw m),
      smul_smul]
    congr 1
    rw [koszul_add_right, koszul_comm q p, ← mul_assoc, koszul_mul_self, one_mul]
  apply TensorProduct.ext'; intro x y
  have hx : V.Y a m ((parGr V).koszulOp q x)
      = koszul p q • ((parGr V).koszulOp q (V.Y a m x)) := by
    obtain ⟨x₀, hx₀, x₁, hx₁, hsum⟩ := (parGr V).exists_parity_decomp x
    rw [← hsum]
    simp only [map_add, smul_add]
    rw [key 0 x₀ hx₀, key 1 x₁ hx₁]
  simp only [Module.End.mul_apply, LinearMap.smul_apply, lftF_tmul, rgtF_tmul]
  rw [hx, TensorProduct.smul_tmul']

/-- Consequently the two legs are `ε`-local with vanishing bracket. -/
theorem localε_lftF_rgtF (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) {p : ZMod 2}
    {a : A} (ha : a ∈ V.parity p) (q : ZMod 2) (b : B) :
    Localε (koszul p q) (lftF V W a) (rgtF V W q b) := by
  refine localε_of_bracketDistε_eq_zero ?_
  apply FormalDist₂.ext; intro m n
  rw [bracketDistε_apply, lftF_mul_rgtF_comm V W ha q b m n]
  exact sub_self _

/-! ### `tenY` on a homogeneous pure tensor is the normal-ordered product -/

/-- Because the two legs commute exactly up to the Koszul sign, the super normal ordering of
`lftF` against `rgtF` is their plain product. -/
theorem normalOrderedε_lftF_rgtF (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B)
    {p : ZMod 2} {a : A} (ha : a ∈ V.parity p) (q : ZMod 2) (b : B) (m n : ℤ) :
    normalOrderedε (koszul p q) (lftF V W a) (rgtF V W q b) m n
      = lftF V W a m * rgtF V W q b n := by
  rw [normalOrderedε_apply]
  split_ifs with h
  · rfl
  · exact (lftF_mul_rgtF_comm V W ha q b m n).symm

/-- **`tenY` on a homogeneous pure tensor is `:lftF · rgtF:`.**  This is what puts the tensor
vertex operator inside the reach of Dong's lemma. -/
theorem tenY_tmul_eq_nprodε (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) {p q : ZMod 2}
    {a : A} {b : B} (ha : a ∈ V.parity p) (hb : b ∈ W.parity q) :
    tenY V W (a ⊗ₜ[ℂ] b)
      = nprodε (koszul p q) (isField_lftF V W a) (isField_rgtF V W q b) := by
  funext s
  apply TensorProduct.ext'
  intro x y
  rw [nprodε_apply, tenY_tmul_parity V W a hb s, kappaTen_tmul, rawCoeff_tmul]
  refine finsum_congr fun m => ?_
  rw [normalOrderedε_lftF_rgtF V W ha q b m (s - m)]
  simp only [Module.End.mul_apply, rgtF_tmul, lftF_tmul]

/-! ## §6  The convolution gradings -/

/-- The image of `P ⊗ Q` inside `A ⊗ B`. -/
def tenSub (P : Submodule ℂ A) (Q : Submodule ℂ B) : Submodule ℂ (A ⊗[ℂ] B) :=
  Submodule.span ℂ {t : A ⊗[ℂ] B | ∃ a ∈ P, ∃ b ∈ Q, a ⊗ₜ[ℂ] b = t}

theorem tmul_mem_tenSub {P : Submodule ℂ A} {Q : Submodule ℂ B} {a : A} {b : B} (ha : a ∈ P)
    (hb : b ∈ Q) : a ⊗ₜ[ℂ] b ∈ tenSub P Q :=
  Submodule.subset_span ⟨a, ha, b, hb, rfl⟩

theorem tenSub_induction {P : Submodule ℂ A} {Q : Submodule ℂ B} {motive : A ⊗[ℂ] B → Prop}
    (hz : motive 0) (hadd : ∀ x y, motive x → motive y → motive (x + y))
    (hsmul : ∀ (c : ℂ) x, motive x → motive (c • x))
    (htmul : ∀ a ∈ P, ∀ b ∈ Q, motive (a ⊗ₜ[ℂ] b)) {u : A ⊗[ℂ] B} (hu : u ∈ tenSub P Q) :
    motive u := by
  have hu' : u ∈ Submodule.span ℂ {t : A ⊗[ℂ] B | ∃ a ∈ P, ∃ b ∈ Q, a ⊗ₜ[ℂ] b = t} := hu
  clear hu
  induction hu' using Submodule.span_induction with
  | mem x hx => obtain ⟨a, ha, b, hb, rfl⟩ := hx; exact htmul a ha b hb
  | zero => exact hz
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul c x _ hx => exact hsmul c x hx

/-- **The convolution weight grading** `(V ⊗ W)_h = ⨆_{h₁+h₂=h} V_{h₁} ⊗ W_{h₂}`. -/
def tenGrading (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (h : ℂ) :
    Submodule ℂ (A ⊗[ℂ] B) :=
  ⨆ h₁ : ℂ, tenSub (V.grading h₁) (W.grading (h - h₁))

/-- **The convolution parity grading** `(V ⊗ W)_p = ⨆_{p₁+p₂=p} V_{p₁} ⊗ W_{p₂}`. -/
def tenParity (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (p : ZMod 2) :
    Submodule ℂ (A ⊗[ℂ] B) :=
  ⨆ p₁ : ZMod 2, tenSub (V.parity p₁) (W.parity (p - p₁))

theorem tmul_mem_tenGrading (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) {h h₁ : ℂ}
    {a : A} {b : B} (ha : a ∈ V.grading h₁) (hb : b ∈ W.grading (h - h₁)) :
    a ⊗ₜ[ℂ] b ∈ tenGrading V W h :=
  Submodule.mem_iSup_of_mem h₁ (tmul_mem_tenSub ha hb)

theorem tmul_mem_tenParity (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) {p p₁ : ZMod 2}
    {a : A} {b : B} (ha : a ∈ V.parity p₁) (hb : b ∈ W.parity (p - p₁)) :
    a ⊗ₜ[ℂ] b ∈ tenParity V W p :=
  Submodule.mem_iSup_of_mem p₁ (tmul_mem_tenSub ha hb)

theorem tenGrading_induction (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) {h : ℂ}
    {motive : A ⊗[ℂ] B → Prop} (hz : motive 0)
    (hadd : ∀ x y, motive x → motive y → motive (x + y))
    (hsmul : ∀ (c : ℂ) x, motive x → motive (c • x))
    (htmul : ∀ (h₁ : ℂ), ∀ a ∈ V.grading h₁, ∀ b ∈ W.grading (h - h₁), motive (a ⊗ₜ[ℂ] b))
    {u : A ⊗[ℂ] B} (hu : u ∈ tenGrading V W h) : motive u := by
  have hu' : u ∈ ⨆ h₁ : ℂ, tenSub (V.grading h₁) (W.grading (h - h₁)) := hu
  refine Submodule.iSup_induction' (motive := fun x _ => motive x) _ ?_ hz
    (fun x y _ _ hx hy => hadd x y hx hy) hu'
  intro h₁ x hx
  exact tenSub_induction hz hadd hsmul (htmul h₁) hx

theorem tenParity_induction (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) {p : ZMod 2}
    {motive : A ⊗[ℂ] B → Prop} (hz : motive 0)
    (hadd : ∀ x y, motive x → motive y → motive (x + y))
    (hsmul : ∀ (c : ℂ) x, motive x → motive (c • x))
    (htmul : ∀ (p₁ : ZMod 2), ∀ a ∈ V.parity p₁, ∀ b ∈ W.parity (p - p₁), motive (a ⊗ₜ[ℂ] b))
    {u : A ⊗[ℂ] B} (hu : u ∈ tenParity V W p) : motive u := by
  have hu' : u ∈ ⨆ p₁ : ZMod 2, tenSub (V.parity p₁) (W.parity (p - p₁)) := hu
  refine Submodule.iSup_induction' (motive := fun x _ => motive x) _ ?_ hz
    (fun x y _ _ hx hy => hadd x y hx hy) hu'
  intro p₁ x hx
  exact tenSub_induction hz hadd hsmul (htmul p₁) hx

/-! ## §7  The grading axioms -/

theorem rawCoeff_tmul_mem_tenGrading (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B)
    {h₁ h₂ k₁ k₂ : ℂ} {a x : A} {b y : B} (ha : a ∈ V.grading h₁) (hb : b ∈ W.grading h₂)
    (hx : x ∈ V.grading k₁) (hy : y ∈ W.grading k₂) (s : ℤ) :
    rawCoeff V W a b s (x ⊗ₜ[ℂ] y) ∈ tenGrading V W (h₁ + h₂ + k₁ + k₂ + s) := by
  rw [rawCoeff_tmul]
  refine finsum_mem_sub _ _ fun m => ?_
  have g1 : V.Y a m x ∈ V.grading (h₁ + k₁ + (m : ℂ)) := Ycoeff_grading V ha hx m
  have g2 : W.Y b (s - m) y ∈ W.grading (h₂ + k₂ + (((s - m : ℤ)) : ℂ)) :=
    Ycoeff_grading W hb hy (s - m)
  have he : h₂ + k₂ + (((s - m : ℤ)) : ℂ)
      = (h₁ + h₂ + k₁ + k₂ + (s : ℂ)) - (h₁ + k₁ + (m : ℂ)) := by push_cast; ring
  rw [he] at g2
  exact tmul_mem_tenGrading V W g1 g2

theorem rawCoeff_tmul_mem_tenParity (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B)
    {p₁ p₂ r₁ r₂ : ZMod 2} {a x : A} {b y : B} (ha : a ∈ V.parity p₁) (hb : b ∈ W.parity p₂)
    (hx : x ∈ V.parity r₁) (hy : y ∈ W.parity r₂) (s : ℤ) :
    rawCoeff V W a b s (x ⊗ₜ[ℂ] y) ∈ tenParity V W (p₁ + p₂ + r₁ + r₂) := by
  rw [rawCoeff_tmul]
  refine finsum_mem_sub _ _ fun m => ?_
  have g1 : V.Y a m x ∈ V.parity (p₁ + r₁) := Ycoeff_parity V ha hx m
  have g2 : W.Y b (s - m) y ∈ W.parity (p₂ + r₂) := Ycoeff_parity W hb hy (s - m)
  have he : p₂ + r₂ = (p₁ + p₂ + r₁ + r₂) - (p₁ + r₁) := by ring
  rw [he] at g2
  exact tmul_mem_tenParity V W g1 g2

/-- **VA1 for the tensor product.** -/
theorem tenY_mem_tenGrading (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B)
    (hV : ParityCompatible V) (hW : ParityCompatible W) {h k : ℂ} {u : A ⊗[ℂ] B}
    (hu : u ∈ tenGrading V W h) (s : ℤ) :
    ∀ v ∈ tenGrading V W k, tenY V W u s v ∈ tenGrading V W (h + k + s) := by
  refine tenGrading_induction V W (h := h)
    (motive := fun w => ∀ v ∈ tenGrading V W k,
      tenY V W w s v ∈ tenGrading V W (h + k + (s : ℂ))) ?_ ?_ ?_ ?_ hu
  · intro v _
    rw [map_zero]
    exact Submodule.zero_mem _
  · intro x y hx hy v hv
    rw [map_add]
    exact Submodule.add_mem _ (hx v hv) (hy v hv)
  · intro c x hx v hv
    rw [map_smul]
    exact Submodule.smul_mem _ _ (hx v hv)
  · intro h₁ a ha b hb v hv
    refine tenGrading_induction V W (h := k)
      (motive := fun w => tenY V W (a ⊗ₜ[ℂ] b) s w ∈ tenGrading V W (h + k + (s : ℂ)))
      ?_ ?_ ?_ ?_ hv
    · change tenY V W (a ⊗ₜ[ℂ] b) s (0 : A ⊗[ℂ] B) ∈ tenGrading V W (h + k + (s : ℂ))
      rw [map_zero]; exact Submodule.zero_mem _
    · intro x y hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
    · intro c x hx; rw [map_smul]; exact Submodule.smul_mem _ _ hx
    · intro k₁ x hx y hy
      have hθb : (parGr W).parityInvol b ∈ W.grading (h - h₁) := hW _ b hb
      have hθx : (parGr V).parityInvol x ∈ V.grading k₁ := hV _ x hx
      have hκ : kappaTen V W 1 (x ⊗ₜ[ℂ] y) = ((parGr V).parityInvol x) ⊗ₜ[ℂ] y := by
        rw [kappaTen_tmul, koszulOp_one]
      have he : h₁ + (h - h₁) + k₁ + (k - k₁) + (s : ℂ) = h + k + (s : ℂ) := by ring
      rw [tenY_tmul_apply, hκ, map_add, map_sub, ← he]
      refine Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_)
        (Submodule.sub_mem _ ?_ ?_))
      · exact rawCoeff_tmul_mem_tenGrading V W ha hb hx hy s
      · exact rawCoeff_tmul_mem_tenGrading V W ha hb hθx hy s
      · exact rawCoeff_tmul_mem_tenGrading V W ha hθb hx hy s
      · exact rawCoeff_tmul_mem_tenGrading V W ha hθb hθx hy s

/-- **VA1′ for the tensor product.** -/
theorem tenY_mem_tenParity (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) {p p' : ZMod 2}
    {u : A ⊗[ℂ] B} (hu : u ∈ tenParity V W p) (s : ℤ) :
    ∀ v ∈ tenParity V W p', tenY V W u s v ∈ tenParity V W (p + p') := by
  refine tenParity_induction V W (p := p)
    (motive := fun w => ∀ v ∈ tenParity V W p',
      tenY V W w s v ∈ tenParity V W (p + p')) ?_ ?_ ?_ ?_ hu
  · intro v _
    rw [map_zero]
    exact Submodule.zero_mem _
  · intro x y hx hy v hv
    rw [map_add]
    exact Submodule.add_mem _ (hx v hv) (hy v hv)
  · intro c x hx v hv
    rw [map_smul]
    exact Submodule.smul_mem _ _ (hx v hv)
  · intro p₁ a ha b hb v hv
    refine tenParity_induction V W (p := p')
      (motive := fun w => tenY V W (a ⊗ₜ[ℂ] b) s w ∈ tenParity V W (p + p')) ?_ ?_ ?_ ?_ hv
    · change tenY V W (a ⊗ₜ[ℂ] b) s (0 : A ⊗[ℂ] B) ∈ tenParity V W (p + p')
      rw [map_zero]; exact Submodule.zero_mem _
    · intro x y hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
    · intro c x hx; rw [map_smul]; exact Submodule.smul_mem _ _ hx
    · intro r₁ x hx y hy
      have hθb : (parGr W).parityInvol b ∈ W.parity (p - p₁) := parityInvol_mem_parity W hb
      have hθx : (parGr V).parityInvol x ∈ V.parity r₁ := parityInvol_mem_parity V hx
      have hκ : kappaTen V W 1 (x ⊗ₜ[ℂ] y) = ((parGr V).parityInvol x) ⊗ₜ[ℂ] y := by
        rw [kappaTen_tmul, koszulOp_one]
      have he : p₁ + (p - p₁) + r₁ + (p' - r₁) = p + p' := by ring
      rw [tenY_tmul_apply, hκ, map_add, map_sub, ← he]
      refine Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_)
        (Submodule.sub_mem _ ?_ ?_))
      · exact rawCoeff_tmul_mem_tenParity V W ha hb hx hy s
      · exact rawCoeff_tmul_mem_tenParity V W ha hb hθx hy s
      · exact rawCoeff_tmul_mem_tenParity V W ha hθb hx hy s
      · exact rawCoeff_tmul_mem_tenParity V W ha hθb hθx hy s

/-! ## §8  Vacuum, creation and regularity -/

/-- The tensor vacuum is fixed by the dressing operator. -/
theorem kappaTen_vacuum (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (q : ZMod 2) :
    kappaTen V W q (V.vacuum ⊗ₜ[ℂ] W.vacuum) = V.vacuum ⊗ₜ[ℂ] W.vacuum := by
  rw [kappaTen_tmul, (parGr V).koszulOp_homog q
    (show V.vacuum ∈ (parGr V).parity 0 from V.vacuum_parity), koszul_zero_right, one_smul]

/-- **VA2 for the tensor product**: `Y(𝟙 ⊗ 𝟙, z) = id`. -/
theorem tenY_vacuum (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) :
    tenY V W (V.vacuum ⊗ₜ[ℂ] W.vacuum) = (1 : (End ℂ (A ⊗[ℂ] B))⟦z^±⟧) := by
  have hV1 : ∀ m : ℤ, V.Y V.vacuum m = (if m = 0 then (1 : End ℂ A) else 0) := by
    intro m; rw [V.vacuum_Y]; exact FormalDist.one_apply m
  have hW1 : ∀ m : ℤ, W.Y W.vacuum m = (if m = 0 then (1 : End ℂ B) else 0) := by
    intro m; rw [W.vacuum_Y]; exact FormalDist.one_apply m
  funext s
  apply TensorProduct.ext'
  intro x y
  rw [tenY_tmul_parity V W V.vacuum W.vacuum_parity s, kappaTen_zero, LinearMap.id_coe, id_eq,
    rawCoeff_tmul]
  have hsingle : (∑ᶠ m : ℤ, (V.Y V.vacuum m x) ⊗ₜ[ℂ] (W.Y W.vacuum (s - m) y))
      = x ⊗ₜ[ℂ] (W.Y W.vacuum s y) := by
    refine (finsum_eq_single _ 0 fun m hm => ?_).trans ?_
    · change (V.Y V.vacuum m x) ⊗ₜ[ℂ] (W.Y W.vacuum (s - m) y) = 0
      rw [hV1 m, if_neg hm]
      show ((0 : End ℂ A) x) ⊗ₜ[ℂ] (W.Y W.vacuum (s - m) y) = 0
      rw [LinearMap.zero_apply, TensorProduct.zero_tmul]
    · change (V.Y V.vacuum 0 x) ⊗ₜ[ℂ] (W.Y W.vacuum (s - 0) y) = x ⊗ₜ[ℂ] (W.Y W.vacuum s y)
      rw [hV1 0, if_pos rfl, sub_zero]
      show ((1 : End ℂ A) x) ⊗ₜ[ℂ] (W.Y W.vacuum s y) = x ⊗ₜ[ℂ] (W.Y W.vacuum s y)
      rw [Module.End.one_apply]
  rw [hsingle, hW1 s]
  change x ⊗ₜ[ℂ] ((if s = 0 then (1 : End ℂ B) else 0) y)
      = ((1 : (End ℂ (A ⊗[ℂ] B))⟦z^±⟧) s) (x ⊗ₜ[ℂ] y)
  rw [FormalDist.one_apply]
  by_cases hs : s = 0
  · rw [if_pos hs, if_pos hs, Module.End.one_apply, Module.End.one_apply]
  · rw [if_neg hs, if_neg hs, LinearMap.zero_apply, LinearMap.zero_apply,
      TensorProduct.tmul_zero]

/-- On the vacuum, `tenY` is the sign-free coefficient (the dressing acts trivially). -/
theorem tenY_tmul_vacuum (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (a : A) (b : B)
    (s : ℤ) :
    tenY V W (a ⊗ₜ[ℂ] b) s (V.vacuum ⊗ₜ[ℂ] W.vacuum)
      = rawCoeff V W a b s (V.vacuum ⊗ₜ[ℂ] W.vacuum) := by
  have hΘ : kappaTen V W 1 (V.vacuum ⊗ₜ[ℂ] W.vacuum) = V.vacuum ⊗ₜ[ℂ] W.vacuum :=
    kappaTen_vacuum V W 1
  rw [tenY_tmul_apply, hΘ, sub_self, map_zero, add_zero]
  have h2 : (V.vacuum ⊗ₜ[ℂ] W.vacuum) + (V.vacuum ⊗ₜ[ℂ] W.vacuum)
      = (2 : ℂ) • (V.vacuum ⊗ₜ[ℂ] W.vacuum) := by rw [two_smul]
  rw [h2, map_smul, smul_smul, show (2⁻¹ * 2 : ℂ) = 1 by norm_num, one_smul]

/-- **VA3 for the tensor product.** -/
theorem tenY_creation (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (u : A ⊗[ℂ] B) :
    tenY V W u 0 (V.vacuum ⊗ₜ[ℂ] W.vacuum) = u
      ∧ ∀ j : ℤ, j < 0 → tenY V W u j (V.vacuum ⊗ₜ[ℂ] W.vacuum) = 0 := by
  refine tmul_induction
    (motive := fun u => tenY V W u 0 (V.vacuum ⊗ₜ[ℂ] W.vacuum) = u
      ∧ ∀ j : ℤ, j < 0 → tenY V W u j (V.vacuum ⊗ₜ[ℂ] W.vacuum) = 0)
    ⟨by rw [map_zero]; rfl, fun j _ => by rw [map_zero]; rfl⟩ ?_ ?_ ?_ u
  · rintro w w' ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
    refine ⟨?_, fun j hj => ?_⟩
    · rw [map_add]
      change tenY V W w 0 (V.vacuum ⊗ₜ[ℂ] W.vacuum) + tenY V W w' 0 (V.vacuum ⊗ₜ[ℂ] W.vacuum)
          = w + w'
      rw [h₁, h₂]
    · rw [map_add]
      change tenY V W w j (V.vacuum ⊗ₜ[ℂ] W.vacuum) + tenY V W w' j (V.vacuum ⊗ₜ[ℂ] W.vacuum) = 0
      rw [h₁' j hj, h₂' j hj, add_zero]
  · rintro c w ⟨h₁, h₁'⟩
    refine ⟨?_, fun j hj => ?_⟩
    · rw [map_smul]
      change c • tenY V W w 0 (V.vacuum ⊗ₜ[ℂ] W.vacuum) = c • w
      rw [h₁]
    · rw [map_smul]
      change c • tenY V W w j (V.vacuum ⊗ₜ[ℂ] W.vacuum) = 0
      rw [h₁' j hj, smul_zero]
  · intro a b
    constructor
    · rw [tenY_tmul_vacuum, rawCoeff_tmul]
      refine (finsum_eq_single _ 0 fun m hm => ?_).trans ?_
      · change (V.Y a m V.vacuum) ⊗ₜ[ℂ] (W.Y b (0 - m) W.vacuum) = 0
        rcases lt_or_ge m 0 with hlt | hge
        · rw [Ycoeff_vacuum_neg V a hlt, TensorProduct.zero_tmul]
        · have hm0 : 0 < m := lt_of_le_of_ne hge (Ne.symm hm)
          rw [Ycoeff_vacuum_neg W b (show (0 : ℤ) - m < 0 by omega), TensorProduct.tmul_zero]
      · change (V.Y a 0 V.vacuum) ⊗ₜ[ℂ] (W.Y b (0 - 0) W.vacuum) = a ⊗ₜ[ℂ] b
        rw [Ycoeff_vacuum V a, sub_zero, Ycoeff_vacuum W b]
    · intro j hj
      rw [tenY_tmul_vacuum, rawCoeff_tmul]
      refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
      rcases lt_or_ge m 0 with hlt | hge
      · rw [Ycoeff_vacuum_neg V a hlt, TensorProduct.zero_tmul]
      · rw [Ycoeff_vacuum_neg W b (show j - m < 0 by omega), TensorProduct.tmul_zero]

/-- **VA5 for the tensor product**: every `tenY u` is a field. -/
theorem isField_tenY (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (u : A ⊗[ℂ] B) :
    IsField (tenY V W u) := by
  refine tmul_induction (motive := fun w => IsField (tenY V W w)) ?_ ?_ ?_ ?_ u
  · change IsField (tenY V W (0 : A ⊗[ℂ] B))
    rw [map_zero]; exact isField_zero
  · intro w w' hw hw'; rw [map_add]; exact isField_add hw hw'
  · intro c w hw; rw [map_smul]; exact isField_smulF c hw
  · intro a b
    rw [tenY_tmul_eq]
    exact isField_smulF _ (isField_add (isField_postComp _ (isField_rawCoeff V W a b))
      (isField_postComp _ (isField_rawCoeff V W a ((parGr W).parityInvol b))))

/-! ## §9  Locality -/

/-- `ε`-locality on the right is preserved by addition (by symmetry). -/
theorem Localε_add_right {ε : ℂ} (hε2 : ε * ε = 1) {a b c : FormalDist (End ℂ C)}
    (h1 : Localε ε a b) (h2 : Localε ε a c) : Localε ε a (b + c) :=
  Localε.symm hε2 (Localε.add_left (Localε.symm hε2 h1) (Localε.symm hε2 h2))

/-- **Locality of `tenY` on homogeneous pure tensors**, by two applications of Dong's lemma. -/
theorem localε_tenY_tmul (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B)
    {p₁ q₁ p₂ q₂ : ZMod 2} {a a' : A} {b b' : B} (ha : a ∈ V.parity p₁) (hb : b ∈ W.parity q₁)
    (ha' : a' ∈ V.parity p₂) (hb' : b' ∈ W.parity q₂) :
    Localε (koszul (p₁ + q₁) (p₂ + q₂)) (tenY V W (a ⊗ₜ[ℂ] b)) (tenY V W (a' ⊗ₜ[ℂ] b')) := by
  have hfA : IsField (lftF V W a) := isField_lftF V W a
  have hfB : IsField (rgtF V W q₁ b) := isField_rgtF V W q₁ b
  have hfA' : IsField (lftF V W a') := isField_lftF V W a'
  have hfB' : IsField (rgtF V W q₂ b') := isField_rgtF V W q₂ b'
  -- the pairwise localities among the four lifted fields
  have l_ab : Localε (koszul p₁ q₁) (lftF V W a) (rgtF V W q₁ b) := localε_lftF_rgtF V W ha q₁ b
  have l_a'b' : Localε (koszul p₂ q₂) (lftF V W a') (rgtF V W q₂ b') :=
    localε_lftF_rgtF V W ha' q₂ b'
  have l_aa' : Localε (koszul p₁ p₂) (lftF V W a) (lftF V W a') := localε_lftF V W ha ha'
  have l_bb' : Localε (koszul q₁ q₂) (rgtF V W q₁ b) (rgtF V W q₂ b') :=
    localε_rgtF V W q₁ q₂ hb hb'
  have l_ab' : Localε (koszul p₁ q₂) (lftF V W a) (rgtF V W q₂ b') :=
    localε_lftF_rgtF V W ha q₂ b'
  have l_a'b : Localε (koszul p₂ q₁) (lftF V W a') (rgtF V W q₁ b) :=
    localε_lftF_rgtF V W ha' q₁ b
  have l_ba' : Localε (koszul q₁ p₂) (rgtF V W q₁ b) (lftF V W a') := by
    have hsym := Localε.symm (koszul_mul_self p₂ q₁) l_a'b
    rwa [koszul_comm p₂ q₁] at hsym
  -- round one
  have r1 : Localε (koszul p₁ p₂ * koszul q₁ p₂)
      (nprodε (koszul p₁ q₁) hfA hfB) (lftF V W a') :=
    dong_negε (koszul_mul_self p₁ q₁) hfA hfB l_ab l_aa' l_ba'
  have r2 : Localε (koszul p₁ q₂ * koszul q₁ q₂)
      (nprodε (koszul p₁ q₁) hfA hfB) (rgtF V W q₂ b') :=
    dong_negε (koszul_mul_self p₁ q₁) hfA hfB l_ab l_ab' l_bb'
  rw [← koszul_add_left p₁ q₁ p₂] at r1
  rw [← koszul_add_left p₁ q₁ q₂] at r2
  have r1' : Localε (koszul p₂ (p₁ + q₁)) (lftF V W a') (nprodε (koszul p₁ q₁) hfA hfB) := by
    have hsym := Localε.symm (koszul_mul_self (p₁ + q₁) p₂) r1
    rwa [koszul_comm (p₁ + q₁) p₂] at hsym
  have r2' : Localε (koszul q₂ (p₁ + q₁)) (rgtF V W q₂ b') (nprodε (koszul p₁ q₁) hfA hfB) := by
    have hsym := Localε.symm (koszul_mul_self (p₁ + q₁) q₂) r2
    rwa [koszul_comm (p₁ + q₁) q₂] at hsym
  -- round two
  have r3 : Localε (koszul p₂ (p₁ + q₁) * koszul q₂ (p₁ + q₁))
      (nprodε (koszul p₂ q₂) hfA' hfB') (nprodε (koszul p₁ q₁) hfA hfB) :=
    dong_negε (koszul_mul_self p₂ q₂) hfA' hfB' l_a'b' r1' r2'
  rw [← koszul_add_left p₂ q₂ (p₁ + q₁)] at r3
  have r4 : Localε (koszul (p₂ + q₂) (p₁ + q₁)) (nprodε (koszul p₁ q₁) hfA hfB)
      (nprodε (koszul p₂ q₂) hfA' hfB') :=
    Localε.symm (koszul_mul_self (p₂ + q₂) (p₁ + q₁)) r3
  rw [koszul_comm (p₂ + q₂) (p₁ + q₁)] at r4
  rw [tenY_tmul_eq_nprodε V W ha hb, tenY_tmul_eq_nprodε V W ha' hb']
  exact r4

/-- **VA4 for the tensor product.** -/
theorem localε_tenY (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) {p p' : ZMod 2}
    {u : A ⊗[ℂ] B} (hu : u ∈ tenParity V W p) :
    ∀ v ∈ tenParity V W p', Localε (koszul p p') (tenY V W u) (tenY V W v) := by
  refine tenParity_induction V W (p := p)
    (motive := fun w => ∀ v ∈ tenParity V W p',
      Localε (koszul p p') (tenY V W w) (tenY V W v)) ?_ ?_ ?_ ?_ hu
  · intro v _
    rw [map_zero]
    exact Localε.zero_left _ _
  · intro x y hx hy v hv
    rw [map_add]
    exact Localε.add_left (hx v hv) (hy v hv)
  · intro c x hx v hv
    rw [map_smul]
    exact Localε.smul_left _ c (hx v hv)
  · intro p₁ a ha b hb v hv
    refine tenParity_induction V W (p := p')
      (motive := fun w => Localε (koszul p p') (tenY V W (a ⊗ₜ[ℂ] b)) (tenY V W w))
      ?_ ?_ ?_ ?_ hv
    · change Localε (koszul p p') (tenY V W (a ⊗ₜ[ℂ] b)) (tenY V W (0 : A ⊗[ℂ] B))
      rw [map_zero]; exact localε_zero_right _ _
    · intro x y hx hy
      rw [map_add]
      exact Localε_add_right (koszul_mul_self _ _) hx hy
    · intro c x hx
      rw [map_smul]
      exact Localε.smul_right (koszul_mul_self _ _) c hx
    · intro p'₁ a' ha' b' hb'
      have hloc := localε_tenY_tmul V W ha hb ha' hb'
      have e1 : p₁ + (p - p₁) = p := by ring
      have e2 : p'₁ + (p' - p'₁) = p' := by ring
      rw [e1, e2] at hloc
      exact hloc

/-! ## §10  The convolution families span, and the parity convolution is internal

The parity case closes completely, by an eigenvalue argument: the total involution
`(-1)^{F_A} ⊗ (-1)^{F_B}` acts on `tenParity V W p` by the scalar `(-1)^p`, so the two
components meet only in `0`.  The weight case is `ℂ`-indexed and has no such separating
operator; only the spanning half is proved here. -/

/-- A submodule of `A ⊗ B` containing all pure tensors of members of two spanning families is
everything. -/
theorem eq_top_of_tmul_mem {ι κ : Type*} {P : ι → Submodule ℂ A} {Q : κ → Submodule ℂ B}
    (hP : (⨆ i, P i) = ⊤) (hQ : (⨆ j, Q j) = ⊤) {S : Submodule ℂ (A ⊗[ℂ] B)}
    (hS : ∀ (i : ι) (j : κ), ∀ x ∈ P i, ∀ y ∈ Q j, x ⊗ₜ[ℂ] y ∈ S) : S = ⊤ := by
  refine le_antisymm le_top fun u _ => ?_
  refine tmul_induction (motive := fun w => w ∈ S) (Submodule.zero_mem _)
    (fun w w' hw hw' => Submodule.add_mem _ hw hw') (fun c w hw => Submodule.smul_mem _ _ hw)
    ?_ u
  intro x y
  have key : ∀ (i : ι), ∀ x' ∈ P i, x' ⊗ₜ[ℂ] y ∈ S := by
    intro i x' hx'
    have hcomap : (⊤ : Submodule ℂ B) ≤ Submodule.comap (TensorProduct.mk ℂ A B x') S := by
      rw [← hQ]
      refine iSup_le fun j => fun y' hy' => ?_
      exact hS i j x' hx' y' hy'
    have hmem : y ∈ Submodule.comap (TensorProduct.mk ℂ A B x') S := hcomap trivial
    rwa [Submodule.mem_comap, TensorProduct.mk_apply] at hmem
  have hcomapA : (⊤ : Submodule ℂ A) ≤ Submodule.comap ((TensorProduct.mk ℂ A B).flip y) S := by
    rw [← hP]
    exact iSup_le fun i => fun x' hx' => key i x' hx'
  have hfin : x ∈ Submodule.comap ((TensorProduct.mk ℂ A B).flip y) S := hcomapA trivial
  rwa [Submodule.mem_comap, LinearMap.flip_apply, TensorProduct.mk_apply] at hfin

/-- The convolution weight grading spans `A ⊗ B`. -/
theorem tenGrading_iSup_eq_top (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) :
    (⨆ h : ℂ, tenGrading V W h) = ⊤ := by
  refine eq_top_of_tmul_mem (P := V.grading) (Q := W.grading)
    ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).1 V.isInternal).2
    ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).1 W.isInternal).2 ?_
  intro h₁ h₂ x hx y hy
  refine Submodule.mem_iSup_of_mem (h₁ + h₂) (tmul_mem_tenGrading V W hx ?_)
  rw [show h₁ + h₂ - h₁ = h₂ from by ring]
  exact hy

/-- The convolution parity grading spans `A ⊗ B`. -/
theorem tenParity_iSup_eq_top (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) :
    (⨆ p : ZMod 2, tenParity V W p) = ⊤ := by
  refine eq_top_of_tmul_mem (P := V.parity) (Q := W.parity)
    ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).1 V.parity_isInternal).2
    ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).1 W.parity_isInternal).2 ?_
  intro p₁ p₂ x hx y hy
  refine Submodule.mem_iSup_of_mem (p₁ + p₂) (tmul_mem_tenParity V W hx ?_)
  rw [show p₁ + p₂ - p₁ = p₂ from by ring]
  exact hy

/-- The total fermion-number involution `(-1)^{F_A} ⊗ (-1)^{F_B}` of `A ⊗ B`. -/
noncomputable def totInvol (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) :
    End ℂ (A ⊗[ℂ] B) :=
  TensorProduct.map ((parGr V).parityInvol) ((parGr W).parityInvol)

/-- On the `p`-th convolution parity component the total involution is the scalar `(-1)^p`. -/
theorem totInvol_tenParity (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) (p : ZMod 2)
    {u : A ⊗[ℂ] B} (hu : u ∈ tenParity V W p) : totInvol V W u = parSign p • u := by
  refine tenParity_induction V W (p := p)
    (motive := fun w => totInvol V W w = parSign p • w) ?_ ?_ ?_ ?_ hu
  · change totInvol V W (0 : A ⊗[ℂ] B) = parSign p • (0 : A ⊗[ℂ] B)
    rw [map_zero, smul_zero]
  · intro x y hx hy
    change totInvol V W (x + y) = parSign p • (x + y)
    rw [map_add, hx, hy, smul_add]
  · intro c x hx
    change totInvol V W (c • x) = parSign p • (c • x)
    rw [map_smul, hx, smul_comm]
  · intro p₁ a ha b hb
    change totInvol V W (a ⊗ₜ[ℂ] b) = parSign p • (a ⊗ₜ[ℂ] b)
    have hmap : totInvol V W (a ⊗ₜ[ℂ] b)
        = ((parGr V).parityInvol a) ⊗ₜ[ℂ] ((parGr W).parityInvol b) := by
      change TensorProduct.map ((parGr V).parityInvol) ((parGr W).parityInvol) (a ⊗ₜ[ℂ] b) = _
      rw [TensorProduct.map_tmul]
    rw [hmap, (parGr V).parityInvol_homog (show a ∈ (parGr V).parity p₁ from ha),
      (parGr W).parityInvol_homog (show b ∈ (parGr W).parity (p - p₁) from hb),
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_smul, ← parSign_add,
      show (p - p₁) + p₁ = p from by ring, TensorProduct.smul_tmul']

/-- The two convolution parity components meet only in `0`. -/
theorem tenParity_disjoint (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) :
    Disjoint (tenParity V W 0) (tenParity V W 1) := by
  rw [Submodule.disjoint_def]
  intro u h0 h1
  have e0 : totInvol V W u = u := by
    rw [totInvol_tenParity V W 0 h0, parSign_zero, one_smul]
  have e1 : totInvol V W u = -u := by
    rw [totInvol_tenParity V W 1 h1, parSign_one, neg_one_smul]
  have huu : u = -u := e0.symm.trans e1
  have hc : u + u = -u + u := congrArg (fun w => w + u) huu
  have hzero : u + u = 0 := by rw [hc]; simp
  have h2 : (2 : ℂ) • u = 0 := by rw [two_smul]; exact hzero
  have hrec : u = (2 : ℂ)⁻¹ • ((2 : ℂ) • u) := by rw [smul_smul]; norm_num
  rw [hrec, h2, smul_zero]

/-- **The convolution parity grading is an internal direct sum.** -/
theorem tenParity_isInternal (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) :
    DirectSum.IsInternal (tenParity V W) := by
  have hne : ∀ r : ZMod 2, (r + 1 : ZMod 2) ≠ r := by decide
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, tenParity_iSup_eq_top V W⟩
  rw [iSupIndep_def]
  intro p
  have hcollapse : (⨆ (q : ZMod 2) (_ : q ≠ p), tenParity V W q) = tenParity V W (p + 1) := by
    refine le_antisymm (iSup₂_le fun q hq => ?_) ?_
    · exact le_of_eq (congrArg (tenParity V W) (zmod_two_ne p q hq))
    · exact le_iSup₂ (f := fun (q : ZMod 2) (_ : q ≠ p) => tenParity V W q) (p + 1) (hne p)
  rw [hcollapse]
  rcases zmod2_cases p with hp | hp <;> subst hp
  · rw [show (0 : ZMod 2) + 1 = 1 from by decide]
    exact tenParity_disjoint V W
  · rw [show (1 : ZMod 2) + 1 = 0 from by decide]
    exact (tenParity_disjoint V W).symm

/-! ## §11  Assembly -/

/-- The two purely linear-algebraic facts about the convolution **weight** grading that this
file does not prove.  (Its spanning half is `tenGrading_iSup_eq_top`, and the whole parity
statement is `tenParity_isInternal`; only these two remain.)  See the closing note. -/
structure TensorGradingHyp (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B) : Prop where
  /-- The convolution weight components are independent. -/
  iSupIndep : iSupIndep (tenGrading V W)
  /-- Each convolution weight space is finite-dimensional. -/
  finrank : ∀ h : ℂ, FiniteDimensional ℂ (tenGrading V W h)

/-- **The tensor product of two vertex superalgebras.**

`Y(u ⊗ v, z)(u' ⊗ v') = (-1)^{|v||u'|}(Y(u,z)u') ⊗ (Y(v,z)v')`, with the convolution weight and
parity gradings and the vacuum `𝟙 ⊗ 𝟙`.  All of VA1–VA5 (and VA1′) are proved; the hypotheses
are the two bigrading-compatibility conditions and the three linear-algebraic facts of
`TensorGradingHyp`. -/
noncomputable def tensorSVA (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B)
    (hV : ParityCompatible V) (hW : ParityCompatible W) (hg : TensorGradingHyp V W) :
    SuperVertexAlgebra (A ⊗[ℂ] B) where
  grading := tenGrading V W
  isInternal := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨hg.iSupIndep, tenGrading_iSup_eq_top V W⟩
  finrank := hg.finrank
  parity := tenParity V W
  parity_isInternal := tenParity_isInternal V W
  Y := tenY V W
  vacuum := V.vacuum ⊗ₜ[ℂ] W.vacuum
  vacuum_mem := by
    refine tmul_mem_tenGrading V W (h₁ := 0) V.vacuum_mem ?_
    rw [sub_zero]
    exact W.vacuum_mem
  vacuum_parity := by
    refine tmul_mem_tenParity V W (p₁ := 0) V.vacuum_parity ?_
    rw [sub_zero]
    exact W.vacuum_parity
  grading_mode := by
    intro h k u hu v hv n
    have hmem := tenY_mem_tenGrading V W hV hW hu (-n - 1) v hv
    rw [mode_apply]
    have e2 : h + k + (((-n - 1 : ℤ)) : ℂ) = h + k - (n : ℂ) - 1 := by push_cast; ring
    rwa [e2] at hmem
  parity_mode := by
    intro p q u hu v hv n
    have hmem := tenY_mem_tenParity V W hu (-n - 1) v hv
    rw [mode_apply]
    exact hmem
  vacuum_Y := tenY_vacuum V W
  creation := by
    intro u
    obtain ⟨h1, h2⟩ := tenY_creation V W u
    refine ⟨?_, fun n hn => ?_⟩
    · rw [mode_apply]
      have e1 : (-(-1 : ℤ) - 1 : ℤ) = 0 := by ring
      rw [e1]
      exact h1
    · rw [mode_apply]
      exact h2 (-n - 1) (by omega)
  locality := by
    intro p q u hu v hv
    exact localε_tenY V W hu v hv
  regularity := by
    intro u v
    obtain ⟨N, hN⟩ := isField_tenY V W u v
    refine ⟨-N, fun n hn => ?_⟩
    rw [mode_apply]
    exact hN (-n - 1) (by omega)

/-!
## What is missing

1. **`TensorGradingHyp.iSupIndep`** — independence of the convolution *weight* components.
   (Spanning is proved: `tenGrading_iSup_eq_top`; and the whole parity statement is proved:
   `tenParity_isInternal`, by the eigenvalue argument for `totInvol`.)  Over the field `ℂ` every
   module is flat, so each `tenSub (V.grading h₁) (W.grading h₂)` really is a copy of
   `V_{h₁} ⊗ W_{h₂}`, and `A ⊗ B = ⨁_{(h₁,h₂)} V_{h₁} ⊗ W_{h₂}` follows from
   `TensorProduct.directSum` together with the two `isInternal` hypotheses; grouping the summands
   along `(h₁,h₂) ↦ h₁ + h₂` then gives independence for `tenGrading`.  The `ℂ`-indexed weight
   case admits no separating operator analogous to `totInvol`, which is why it is left open here.

2. **`TensorGradingHyp.finrank`** is **not** a consequence of the axioms: it needs each `h` to
   admit only finitely many splittings `h = h₁ + h₂` with `V_{h₁} ≠ 0 ≠ W_{h₂}`, which a
   bounded-below grading with discrete weight support supplies.  A concrete instantiation should
   discharge `TensorGradingHyp` from `BoundedBelow`.

3. **The conformal layer.**  `ω = ω ⊗ 𝟙 + 𝟙 ⊗ ω` and the additivity of central charges are not
   built here; they need the `SuperNearVOA` / `SuperVertexOperatorAlgebra` layer on top of what
   is proved above.  Nothing here obstructs it: `tenY_tmul_parity` gives the Koszul-signed
   formula for the modes of `ω ⊗ 𝟙` and `𝟙 ⊗ ω` in closed form, and `lftF_mul_rgtF_comm`
   already says the two Virasoro fields commute exactly.
-/

end TensorVA

end VOA
