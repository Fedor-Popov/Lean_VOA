/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import Mathlib

/-!
# Twisted intertwiners out of a cyclic module  (Moonshine step M8g twisted half: linear algebra)

Pure linear algebra, used for the triality `σ` on the twisted sectors of `V♮`
(`TrialityTwSigma.lean`).

Let a set of "letters" `A` act on `M` by `ρ u n : M →ₗ M` and on `N` by `τ u n : N →ₗ N`
(`n : ℤ`, the mode index), and let `g : A → A` (the automorphism `σ` on `V₀⁺`).  A linear map
`Φ : M → N` is a **`g`-twisted intertwiner on `X ≤ M`** for the letters `S ⊆ A` if

  `Φ (ρ u n x) = τ (g u) n (Φ x)`   for `u ∈ S`, `n ∈ ℤ`, `x ∈ X`   (`IsTwInt`).

## Main results
* `eqOn_of_cyclic` — **uniqueness**: if `X = span{ρ u n x₀ | u ∈ S}` (single-mode
  cyclicity, the form of `cyclic_V3` / `cyclic_TPframe`), a twisted intertwiner on `X` is
  determined by `Φ x₀`.
* `IsTwInt.comp` — composition (twists compose); `eqOn_id_of_cyclic` — an untwisted
  self-intertwiner fixing `x₀` is the identity on `X`; `comp_eqOn_id` — **involutivity
  criterion**: if `Φ` is `g`-twisted, `Ψ` is `g'`-twisted, `g' ∘ g = id` on `S`, and
  `Ψ (Φ x₀) = x₀`, then `Ψ ∘ Φ = id` on `X`.
* Words: `wordAct ρ w` (iterated modes), `twWord g w`, the evaluation maps `evW`.
* `exists_twInt_iff` — **existence ⇔ annihilator compatibility**: a `g`-twisted intertwiner
  with `Φ x₀ = y₀` exists iff every linear relation among the word vectors `ρ_w x₀` also holds
  among the twisted word vectors `τ_{g(w)} y₀` (`ker evW ρ x₀ ≤ ker evW τ∘g y₀`).  This is the
  device that *defines* `σ` on a sector once its well-definedness is proved.
* `annCompat_of_gram` — the compatibility follows from matching Gram matrices of word vectors
  against a form that is nondegenerate on the target span (the "two-point data" reduction).

## Status
`sorry`-free; no axioms beyond `[propext, Classical.choice, Quot.sound]`.  Lattice-free and
VOA-free: these are reductions, not the existence of `σ` (which remains open; see
`TrialityTwSigma.lean`).
-/

namespace VOA.Moonshine.TrialityTw

open Submodule

variable {A : Type*} {M N P : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
  [AddCommGroup P] [Module ℂ P]

/-! ## §1  Twisted intertwiners -/

/-- `Φ` is a **`g`-twisted intertwiner on `X`** for the letters `S`:
`Φ (ρ u n x) = τ (g u) n (Φ x)` for `u ∈ S`, `n ∈ ℤ`, `x ∈ X`. -/
def IsTwInt (ρ : A → ℤ → M →ₗ[ℂ] M) (τ : A → ℤ → N →ₗ[ℂ] N) (g : A → A) (S : Set A)
    (X : Submodule ℂ M) (Φ : M →ₗ[ℂ] N) : Prop :=
  ∀ u ∈ S, ∀ (n : ℤ), ∀ x ∈ X, Φ (ρ u n x) = τ (g u) n (Φ x)

variable {ρ : A → ℤ → M →ₗ[ℂ] M} {τ : A → ℤ → N →ₗ[ℂ] N} {π : A → ℤ → P →ₗ[ℂ] P}
  {g g' : A → A} {S S' : Set A} {X : Submodule ℂ M} {Y : Submodule ℂ N}

/-- **Uniqueness from a cyclic vector.**  Two `g`-twisted intertwiners on a single-mode
cyclic `X = span{ρ u n x₀}` that agree on `x₀` agree on all of `X`. -/
theorem eqOn_of_cyclic {x₀ : M} (hx₀ : x₀ ∈ X)
    (hcyc : span ℂ {y | ∃ u ∈ S, ∃ n : ℤ, y = ρ u n x₀} = X) {Φ Ψ : M →ₗ[ℂ] N}
    (hΦ : IsTwInt ρ τ g S X Φ) (hΨ : IsTwInt ρ τ g S X Ψ) (h : Φ x₀ = Ψ x₀) :
    ∀ x ∈ X, Φ x = Ψ x := by
  intro x hx
  rw [← hcyc] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, n, rfl⟩ := hy
    rw [hΦ u hu n x₀ hx₀, hΨ u hu n x₀ hx₀, h]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
  | smul c a _ ha => rw [map_smul, map_smul, ha]

/-- Twisted intertwiners compose; the twists compose. -/
theorem IsTwInt.comp {Φ : M →ₗ[ℂ] N} {Ψ : N →ₗ[ℂ] P} (hΦ : IsTwInt ρ τ g S X Φ)
    (hΨ : IsTwInt τ π g' S' Y Ψ) (hmap : ∀ x ∈ X, Φ x ∈ Y) (hS : ∀ u ∈ S, g u ∈ S') :
    IsTwInt ρ π (g' ∘ g) S X (Ψ ∘ₗ Φ) := by
  intro u hu n x hx
  simp only [LinearMap.comp_apply, Function.comp_apply]
  rw [hΦ u hu n x hx, hΨ (g u) (hS u hu) n (Φ x) (hmap x hx)]

/-- The identity is an untwisted intertwiner (for any `g` that fixes the letters). -/
theorem isTwInt_id (hg : ∀ u ∈ S, g u = u) : IsTwInt ρ ρ g S X LinearMap.id := by
  intro u hu n x _
  simp [hg u hu]

/-- An untwisted self-intertwiner of a cyclic `X` fixing `x₀` is the identity on `X`. -/
theorem eqOn_id_of_cyclic {x₀ : M} (hx₀ : x₀ ∈ X)
    (hcyc : span ℂ {y | ∃ u ∈ S, ∃ n : ℤ, y = ρ u n x₀} = X) (hg : ∀ u ∈ S, g u = u)
    {Θ : M →ₗ[ℂ] M} (hΘ : IsTwInt ρ ρ g S X Θ) (h : Θ x₀ = x₀) : ∀ x ∈ X, Θ x = x :=
  fun x hx => eqOn_of_cyclic hx₀ hcyc hΘ (isTwInt_id hg) h x hx

/-- **Involutivity criterion.**  If `Φ : X → Y` is `g`-twisted, `Ψ` is `g'`-twisted on `Y`,
`g' ∘ g = id` on the letters, and `Ψ (Φ x₀) = x₀`, then `Ψ ∘ Φ = id` on `X`. -/
theorem comp_eqOn_id {Φ : M →ₗ[ℂ] N} {Ψ : N →ₗ[ℂ] M} {x₀ : M} (hx₀ : x₀ ∈ X)
    (hcyc : span ℂ {y | ∃ u ∈ S, ∃ n : ℤ, y = ρ u n x₀} = X)
    (hΦ : IsTwInt ρ τ g S X Φ) (hΨ : IsTwInt τ ρ g' S' Y Ψ) (hmap : ∀ x ∈ X, Φ x ∈ Y)
    (hS : ∀ u ∈ S, g u ∈ S') (hgg : ∀ u ∈ S, g' (g u) = u) (h : Ψ (Φ x₀) = x₀) :
    ∀ x ∈ X, Ψ (Φ x) = x :=
  eqOn_id_of_cyclic (g := g' ∘ g) hx₀ hcyc hgg (hΦ.comp hΨ hmap hS) h

/-! ## §2  Words and the existence criterion -/

/-- Iterated modes along a word `w = [(u₁,n₁), …, (u_k,n_k)]`: `ρ u₁ n₁ ∘ ⋯ ∘ ρ u_k n_k`. -/
def wordAct (ρ : A → ℤ → M →ₗ[ℂ] M) : List (A × ℤ) → M →ₗ[ℂ] M
  | [] => LinearMap.id
  | p :: w => ρ p.1 p.2 ∘ₗ wordAct ρ w

@[simp] theorem wordAct_nil : wordAct ρ [] = LinearMap.id := rfl

@[simp] theorem wordAct_cons (p : A × ℤ) (w : List (A × ℤ)) :
    wordAct ρ (p :: w) = ρ p.1 p.2 ∘ₗ wordAct ρ w := rfl

/-- Twist every letter of a word by `g`. -/
def twWord (g : A → A) (w : List (A × ℤ)) : List (A × ℤ) := w.map fun p => (g p.1, p.2)

@[simp] theorem twWord_cons (p : A × ℤ) (w : List (A × ℤ)) :
    twWord g (p :: w) = (g p.1, p.2) :: twWord g w := rfl

/-- Words all of whose letters lie in `S`. -/
def Words (S : Set A) : Type _ := {w : List (A × ℤ) // ∀ p ∈ w, p.1 ∈ S}

/-- The empty word. -/
def Words.nil (S : Set A) : Words S := ⟨[], by simp⟩

/-- Prepend a letter of `S`. -/
def Words.cons {u : A} (hu : u ∈ S) (n : ℤ) (w : Words S) : Words S :=
  ⟨(u, n) :: w.1, by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hu
    · exact w.2 p hp⟩

/-- Evaluation of formal combinations of words on a vector: `f ↦ ∑ f(w) • ρ_w x₀`. -/
noncomputable def evW (ρ : A → ℤ → M →ₗ[ℂ] M) (S : Set A) (x₀ : M) : (Words S →₀ ℂ) →ₗ[ℂ] M :=
  Finsupp.linearCombination ℂ fun w : Words S => wordAct ρ w.1 x₀

/-- The twisted evaluation `f ↦ ∑ f(w) • τ_{g(w)} y₀`. -/
noncomputable def evTw (τ : A → ℤ → N →ₗ[ℂ] N) (g : A → A) (S : Set A) (y₀ : N) :
    (Words S →₀ ℂ) →ₗ[ℂ] N :=
  Finsupp.linearCombination ℂ fun w : Words S => wordAct τ (twWord g w.1) y₀

/-- **Annihilator compatibility** of `(x₀, y₀)`: every linear relation among the word vectors
`ρ_w x₀` also holds among the twisted word vectors `τ_{g(w)} y₀`. -/
def AnnCompat (ρ : A → ℤ → M →ₗ[ℂ] M) (τ : A → ℤ → N →ₗ[ℂ] N) (g : A → A) (S : Set A)
    (x₀ : M) (y₀ : N) : Prop :=
  LinearMap.ker (evW ρ S x₀) ≤ LinearMap.ker (evTw τ g S y₀)

theorem evW_mapDomain_cons {u : A} (hu : u ∈ S) (n : ℤ) (x₀ : M) (f : Words S →₀ ℂ) :
    evW ρ S x₀ (Finsupp.mapDomain (Words.cons hu n) f) = ρ u n (evW ρ S x₀ f) := by
  simp only [evW, Finsupp.linearCombination_mapDomain]
  rw [Finsupp.apply_linearCombination]
  rfl

theorem evTw_mapDomain_cons {u : A} (hu : u ∈ S) (n : ℤ) (y₀ : N) (f : Words S →₀ ℂ) :
    evTw τ g S y₀ (Finsupp.mapDomain (Words.cons hu n) f) = τ (g u) n (evTw τ g S y₀ f) := by
  simp only [evTw, Finsupp.linearCombination_mapDomain]
  rw [Finsupp.apply_linearCombination]
  rfl

/-- Word vectors stay in a stable subspace. -/
theorem wordAct_mem (hstab : ∀ u ∈ S, ∀ (n : ℤ), ∀ x ∈ X, ρ u n x ∈ X) {x₀ : M} (hx₀ : x₀ ∈ X)
    (w : Words S) : wordAct ρ w.1 x₀ ∈ X := by
  obtain ⟨w, hw⟩ := w
  induction w with
  | nil => simpa using hx₀
  | cons p w ih =>
    simp only [wordAct_cons, LinearMap.comp_apply]
    exact hstab p.1 (hw p (by simp)) p.2 _ (ih fun q hq => hw q (by simp [hq]))

/-- The range of `evW` is `X` (stability plus single-mode cyclicity). -/
theorem range_evW (hstab : ∀ u ∈ S, ∀ (n : ℤ), ∀ x ∈ X, ρ u n x ∈ X) {x₀ : M} (hx₀ : x₀ ∈ X)
    (hcyc : span ℂ {y | ∃ u ∈ S, ∃ n : ℤ, y = ρ u n x₀} = X) :
    LinearMap.range (evW ρ S x₀) = X := by
  refine le_antisymm ?_ ?_
  · rw [evW, Finsupp.range_linearCombination, span_le]
    rintro _ ⟨w, rfl⟩
    exact wordAct_mem hstab hx₀ w
  · rw [← hcyc, span_le]
    rintro _ ⟨u, hu, n, rfl⟩
    refine ⟨Finsupp.single (Words.cons hu n (Words.nil S)) 1, ?_⟩
    simp [evW, Words.cons, Words.nil]

/-- A twisted intertwiner transports word vectors to twisted word vectors. -/
theorem IsTwInt.wordAct {Φ : M →ₗ[ℂ] N} (hΦ : IsTwInt ρ τ g S X Φ)
    (hstab : ∀ u ∈ S, ∀ (n : ℤ), ∀ x ∈ X, ρ u n x ∈ X) {x₀ : M} (hx₀ : x₀ ∈ X) (w : Words S) :
    Φ (wordAct ρ w.1 x₀) = wordAct τ (twWord g w.1) (Φ x₀) := by
  obtain ⟨w, hw⟩ := w
  induction w with
  | nil => simp [twWord]
  | cons p w ih =>
    have hw' : ∀ q ∈ w, q.1 ∈ S := fun q hq => hw q (by simp [hq])
    simp only [wordAct_cons, LinearMap.comp_apply, twWord_cons]
    rw [hΦ p.1 (hw p (by simp)) p.2 _ (wordAct_mem hstab hx₀ ⟨w, hw'⟩), ih hw']

theorem IsTwInt.comp_evW {Φ : M →ₗ[ℂ] N} (hΦ : IsTwInt ρ τ g S X Φ)
    (hstab : ∀ u ∈ S, ∀ (n : ℤ), ∀ x ∈ X, ρ u n x ∈ X) {x₀ : M} (hx₀ : x₀ ∈ X) :
    Φ ∘ₗ evW ρ S x₀ = evTw τ g S (Φ x₀) := by
  apply Finsupp.lhom_ext'
  intro w
  apply LinearMap.ext_ring
  simp [evW, evTw, hΦ.wordAct hstab hx₀ w]

/-- **Existence ⇔ annihilator compatibility.**  On a stable, single-mode cyclic `X`, a
`g`-twisted intertwiner with `Φ x₀ = y₀` exists iff `(x₀, y₀)` is annihilator-compatible. -/
theorem exists_twInt_iff (hstab : ∀ u ∈ S, ∀ (n : ℤ), ∀ x ∈ X, ρ u n x ∈ X) {x₀ : M}
    (hx₀ : x₀ ∈ X) (hcyc : span ℂ {y | ∃ u ∈ S, ∃ n : ℤ, y = ρ u n x₀} = X) (y₀ : N) :
    (∃ Φ : M →ₗ[ℂ] N, IsTwInt ρ τ g S X Φ ∧ Φ x₀ = y₀) ↔ AnnCompat ρ τ g S x₀ y₀ := by
  constructor
  · rintro ⟨Φ, hΦ, rfl⟩ f hf
    rw [LinearMap.mem_ker] at hf ⊢
    rw [← hΦ.comp_evW hstab hx₀, LinearMap.comp_apply, hf, map_zero]
  · intro hc
    set e₁ := evW ρ S x₀
    set e₂ := evTw τ g S y₀
    -- `Φ₀ : range e₁ → N`, `e₁ f ↦ e₂ f`
    let Φ₀ : LinearMap.range e₁ →ₗ[ℂ] N :=
      ((LinearMap.ker e₁).liftQ e₂ hc).comp e₁.quotKerEquivRange.symm.toLinearMap
    have hΦ₀ : ∀ f, Φ₀ ⟨e₁ f, LinearMap.mem_range_self e₁ f⟩ = e₂ f := by
      intro f
      simp only [Φ₀, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [LinearMap.quotKerEquivRange_symm_apply_image]
      rfl
    obtain ⟨Φ, hΦ⟩ := LinearMap.exists_extend Φ₀
    have hev : ∀ f, Φ (e₁ f) = e₂ f := by
      intro f
      have := LinearMap.congr_fun hΦ ⟨e₁ f, LinearMap.mem_range_self e₁ f⟩
      simpa [hΦ₀] using this
    have hrange := range_evW hstab hx₀ hcyc
    refine ⟨Φ, ?_, ?_⟩
    · intro u hu n x hx
      rw [← hrange] at hx
      obtain ⟨f, rfl⟩ := hx
      rw [← evW_mapDomain_cons hu n x₀ f, hev, hev, evTw_mapDomain_cons hu n y₀ f]
    · have := hev (Finsupp.single (Words.nil S) 1)
      simpa [e₁, e₂, evW, evTw, Words.nil, twWord] using this

/-- Bilinear expansion: matching Gram matrices of word vectors give matching Gram matrices of
all formal combinations. -/
theorem gram_evW (B₁ : M →ₗ[ℂ] M →ₗ[ℂ] ℂ) (B₂ : N →ₗ[ℂ] N →ₗ[ℂ] ℂ) {x₀ : M} {y₀ : N}
    (hgram : ∀ w w' : Words S, B₁ (wordAct ρ w'.1 x₀) (wordAct ρ w.1 x₀)
      = B₂ (wordAct τ (twWord g w'.1) y₀) (wordAct τ (twWord g w.1) y₀))
    (f f' : Words S →₀ ℂ) :
    B₂ (evTw τ g S y₀ f') (evTw τ g S y₀ f) = B₁ (evW ρ S x₀ f') (evW ρ S x₀ f) := by
  induction f' using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | single w' c =>
    simp only [evTw, evW, Finsupp.linearCombination_single, map_smul, LinearMap.smul_apply]
    congr 1
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single w d => simp [Finsupp.linearCombination_single, hgram w w']

/-- **Gram-matrix criterion for compatibility.**  If the Gram matrix of the word vectors
`ρ_w x₀` under `B₁` equals that of the twisted word vectors `τ_{g(w)} y₀` under `B₂`, and `B₂`
is nondegenerate on their span, then `(x₀, y₀)` is annihilator-compatible. -/
theorem annCompat_of_gram (B₁ : M →ₗ[ℂ] M →ₗ[ℂ] ℂ) (B₂ : N →ₗ[ℂ] N →ₗ[ℂ] ℂ) {x₀ : M} {y₀ : N}
    (hgram : ∀ w w' : Words S, B₁ (wordAct ρ w'.1 x₀) (wordAct ρ w.1 x₀)
      = B₂ (wordAct τ (twWord g w'.1) y₀) (wordAct τ (twWord g w.1) y₀))
    (hnd : ∀ y ∈ LinearMap.range (evTw τ g S y₀),
      (∀ y' ∈ LinearMap.range (evTw τ g S y₀), B₂ y' y = 0) → y = 0) :
    AnnCompat ρ τ g S x₀ y₀ := by
  intro f hf
  rw [LinearMap.mem_ker] at hf ⊢
  apply hnd _ (LinearMap.mem_range_self _ f)
  rintro _ ⟨f', rfl⟩
  rw [gram_evW B₁ B₂ hgram f f', hf, map_zero]

end VOA.Moonshine.TrialityTw
