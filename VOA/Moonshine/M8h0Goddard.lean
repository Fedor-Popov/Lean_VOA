/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Foundations.FormalDist3
import VOA.Core.Goddard
import Mathlib.Tactic.NoncommRing

/-!
# M8h-0a: a two-variable Goddard lemma

The one-variable Goddard argument (`goddard_zero`, `Reconstruction.field_eq_zero_of_vacuum`)
kills a **field** `A(z)` that annihilates the vacuum and is local with a family of creating
fields.  For the twisted × twisted block of `V♮` the object to kill is a **two-variable**
distribution `B(z₁, z₂)` — e.g. `B = (z₁ − z₂)ᴺ [a(z₁), b(z₂)]` — and the relevant locality
is the three-variable statement

  `(w − z₁)^{M₁} (w − z₂)^{M₂} [A(w), B(z₁, z₂)] = 0`.

## Main results

* `brk3 A F` — the three-variable bracket `[A(w), F(z₁,z₂)]` (`w` is the first variable).
* `goddard₂` — if `B` kills `vac`, `A(w) vac ∈ V[[w]]`, and
  `(w−z₁)^{M₁}(w−z₂)^{M₂}[A(w), B(z₁,z₂)] = 0`, then `B(z₁,z₂) A(w) vac = 0` coefficientwise;
  in particular `B` kills every `A_p vac`.
* `loc3_mulBySubPow_bracketDist` — if `A` is `Local` with `a` and with `b`, then for every
  `N` the distribution `B = (z₁−z₂)ᴺ [a(z₁), b(z₂)]` satisfies the three-variable locality with
  `A`, i.e. the hypothesis of `goddard₂`.

## Proof idea
Evaluate the locality on `vac`: since `B` kills `vac`, `(w−z₁)^{M₁}(w−z₂)^{M₂} G = 0` for
`G(w,z₁,z₂) := B(z₁,z₂)A(w)vac`.  `G` is lower-truncated in `w`, and multiplication by
`w − zᵢ` is injective on such distributions (`eq_zero_of_mulBySub₁₂_of_bdd`: the lowest
`w`-coefficient is reproduced up to a shift).  The three-variable locality of a commutator is
the Leibniz rule `[A, ab] = [A, a]b + a[A, b]`.

## Status
`sorry`-free; generic (any `ℂ`-module `V`), no hypotheses beyond those displayed.
-/

namespace VOA.Moonshine.M8h0

open Module (End)

universe u

/-! ## Cancellation in the first variable of a three-variable distribution -/

section Cancel

variable {𝒲 : Type u} [AddCommGroup 𝒲] [Module ℂ 𝒲]

/-- Lower truncation in the first variable. -/
def BddBelow₁₃ (D : FormalDist₃ 𝒲) : Prop := ∃ B : ℤ, ∀ p m n, p < B → D p m n = 0

theorem BddBelow₁₃.mulBySub₁₂ {D : FormalDist₃ 𝒲} (h : BddBelow₁₃ D) :
    BddBelow₁₃ (mulBySub₁₂ D) := by
  obtain ⟨B, hB⟩ := h
  exact ⟨B, fun p m n hp => by rw [mulBySub₁₂_apply, hB _ _ _ (by omega), hB _ _ _ hp, sub_zero]⟩

theorem BddBelow₁₃.mulBySub₁₃ {D : FormalDist₃ 𝒲} (h : BddBelow₁₃ D) :
    BddBelow₁₃ (mulBySub₁₃ D) := by
  obtain ⟨B, hB⟩ := h
  exact ⟨B, fun p m n hp => by rw [mulBySub₁₃_apply, hB _ _ _ (by omega), hB _ _ _ hp, sub_zero]⟩

theorem BddBelow₁₃.mulBySub₁₃Pow {D : FormalDist₃ 𝒲} (h : BddBelow₁₃ D) (M : ℕ) :
    BddBelow₁₃ (mulBySub₁₃Pow M D) := by
  induction M with
  | zero => simpa using h
  | succ M ih => rw [mulBySub₁₃Pow_succ, LinearMap.comp_apply]; exact ih.mulBySub₁₃

theorem BddBelow₁₃.mulBySub₁₂Pow {D : FormalDist₃ 𝒲} (h : BddBelow₁₃ D) (M : ℕ) :
    BddBelow₁₃ (mulBySub₁₂Pow M D) := by
  induction M with
  | zero => simpa using h
  | succ M ih => rw [mulBySub₁₂Pow_succ, LinearMap.comp_apply]; exact ih.mulBySub₁₂

omit [Module ℂ 𝒲] in
/-- Generic first-variable cancellation: if `D(p−1,·)` determines `D(p,·)` up to a shift and
`D` is lower-truncated in `p`, then `D = 0`. -/
theorem eq_zero_of_shift {D : FormalDist₃ 𝒲} (σ : ℤ → ℤ → ℤ × ℤ)
    (hrec : ∀ p m n, D p m n = D (p - 1) (σ m n).1 (σ m n).2) (h : BddBelow₁₃ D) : D = 0 := by
  obtain ⟨B, hB⟩ := h
  have key : ∀ k : ℕ, ∀ m n, D (B + k) m n = 0 := by
    intro k
    induction k with
    | zero => intro m n; rw [hrec]; exact hB _ _ _ (by omega)
    | succ k ih =>
      intro m n
      rw [hrec, show B + ((k + 1 : ℕ) : ℤ) - 1 = B + k by push_cast; ring]
      exact ih _ _
  ext p m n
  by_cases hp : p < B
  · exact hB _ _ _ hp
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, p = B + k := ⟨(p - B).toNat, by omega⟩
    rw [hk]; exact key k m n

theorem eq_zero_of_mulBySub₁₂ {D : FormalDist₃ 𝒲} (h0 : mulBySub₁₂ D = 0) (h : BddBelow₁₃ D) :
    D = 0 := by
  refine eq_zero_of_shift (fun m n => (m + 1, n)) (fun p m n => ?_) h
  have := congrFun (congrFun (congrFun h0 p) (m + 1)) n
  rw [mulBySub₁₂_apply, add_sub_cancel_right] at this
  exact (sub_eq_zero.mp this).symm

theorem eq_zero_of_mulBySub₁₃ {D : FormalDist₃ 𝒲} (h0 : mulBySub₁₃ D = 0) (h : BddBelow₁₃ D) :
    D = 0 := by
  refine eq_zero_of_shift (fun m n => (m, n + 1)) (fun p m n => ?_) h
  have := congrFun (congrFun (congrFun h0 p) m) (n + 1)
  rw [mulBySub₁₃_apply, add_sub_cancel_right] at this
  exact (sub_eq_zero.mp this).symm

theorem eq_zero_of_mulBySub₁₂Pow {D : FormalDist₃ 𝒲} (M : ℕ) (h0 : mulBySub₁₂Pow M D = 0)
    (h : BddBelow₁₃ D) : D = 0 := by
  induction M with
  | zero => simpa using h0
  | succ M ih =>
    rw [mulBySub₁₂Pow_succ, LinearMap.comp_apply] at h0
    exact ih (eq_zero_of_mulBySub₁₂ h0 (h.mulBySub₁₂Pow M))

theorem eq_zero_of_mulBySub₁₃Pow {D : FormalDist₃ 𝒲} (M : ℕ) (h0 : mulBySub₁₃Pow M D = 0)
    (h : BddBelow₁₃ D) : D = 0 := by
  induction M with
  | zero => simpa using h0
  | succ M ih =>
    rw [mulBySub₁₃Pow_succ, LinearMap.comp_apply] at h0
    exact ih (eq_zero_of_mulBySub₁₃ h0 (h.mulBySub₁₃Pow M))

/-! ## Commutation of the difference operators -/

theorem mulBySub₁₂Pow_eq_npow (N : ℕ) :
    (mulBySub₁₂Pow N : FormalDist₃ 𝒲 →ₗ[ℂ] _) = mulBySub₁₂ ^ N := by
  induction N with
  | zero => rfl
  | succ k ih => rw [mulBySub₁₂Pow_succ, ih, pow_succ']; rfl

theorem commute_12_13 : Commute (mulBySub₁₂ : FormalDist₃ 𝒲 →ₗ[ℂ] _) mulBySub₁₃ := by
  change mulBySub₁₂ * mulBySub₁₃ = mulBySub₁₃ * mulBySub₁₂
  ext f m n p
  change mulBySub₁₂ (mulBySub₁₃ f) m n p = mulBySub₁₃ (mulBySub₁₂ f) m n p
  simp only [mulBySub₁₂_apply, mulBySub₁₃_apply]
  abel

theorem commute_12_23 : Commute (mulBySub₁₂ : FormalDist₃ 𝒲 →ₗ[ℂ] _) mulBySub₂₃ := by
  change mulBySub₁₂ * mulBySub₂₃ = mulBySub₂₃ * mulBySub₁₂
  ext f m n p
  change mulBySub₁₂ (mulBySub₂₃ f) m n p = mulBySub₂₃ (mulBySub₁₂ f) m n p
  simp only [mulBySub₁₂_apply, mulBySub₂₃_apply]
  abel

theorem commute_13_23 : Commute (mulBySub₁₃ : FormalDist₃ 𝒲 →ₗ[ℂ] _) mulBySub₂₃ := by
  change mulBySub₁₃ * mulBySub₂₃ = mulBySub₂₃ * mulBySub₁₃
  ext f m n p
  change mulBySub₁₃ (mulBySub₂₃ f) m n p = mulBySub₂₃ (mulBySub₁₃ f) m n p
  simp only [mulBySub₁₃_apply, mulBySub₂₃_apply]
  abel

theorem pow12_pow13_comm (M₁ M₂ : ℕ) (f : FormalDist₃ 𝒲) :
    mulBySub₁₂Pow M₁ (mulBySub₁₃Pow M₂ f) = mulBySub₁₃Pow M₂ (mulBySub₁₂Pow M₁ f) := by
  rw [mulBySub₁₂Pow_eq_npow, mulBySub₁₃Pow_eq_npow, ← Module.End.mul_apply,
    (commute_12_13.pow_pow M₁ M₂).eq, Module.End.mul_apply]

theorem pow12_pow23_comm (M₁ N : ℕ) (f : FormalDist₃ 𝒲) :
    mulBySub₁₂Pow M₁ (mulBySub₂₃Pow N f) = mulBySub₂₃Pow N (mulBySub₁₂Pow M₁ f) := by
  rw [mulBySub₁₂Pow_eq_npow, mulBySub₂₃Pow_eq_npow, ← Module.End.mul_apply,
    (commute_12_23.pow_pow M₁ N).eq, Module.End.mul_apply]

theorem pow13_pow23_comm (M₂ N : ℕ) (f : FormalDist₃ 𝒲) :
    mulBySub₁₃Pow M₂ (mulBySub₂₃Pow N f) = mulBySub₂₃Pow N (mulBySub₁₃Pow M₂ f) := by
  rw [mulBySub₁₃Pow_eq_npow, mulBySub₂₃Pow_eq_npow, ← Module.End.mul_apply,
    (commute_13_23.pow_pow M₂ N).eq, Module.End.mul_apply]

/-! ## Coefficientwise linear maps commute with the difference operators -/

variable {𝒲' : Type*} [AddCommGroup 𝒲'] [Module ℂ 𝒲']

theorem map12 (Φ : ℤ → 𝒲 →ₗ[ℂ] 𝒲') (M : ℕ) (G : FormalDist₂ 𝒲) :
    mulBySub₁₂Pow M ((fun p m n => Φ n (G p m)) : FormalDist₃ 𝒲')
      = fun p m n => Φ n (mulBySubPow M G p m) := by
  induction M with
  | zero => rfl
  | succ M ih =>
    rw [mulBySub₁₂Pow_succ, LinearMap.comp_apply, ih, mulBySubPow_succ]
    ext p m n
    simp only [mulBySub₁₂_apply, LinearMap.comp_apply, mulBySub_apply, map_sub]

theorem map13 (Φ : ℤ → 𝒲 →ₗ[ℂ] 𝒲') (M : ℕ) (G : FormalDist₂ 𝒲) :
    mulBySub₁₃Pow M ((fun p m n => Φ m (G p n)) : FormalDist₃ 𝒲')
      = fun p m n => Φ m (mulBySubPow M G p n) := by
  induction M with
  | zero => rfl
  | succ M ih =>
    rw [mulBySub₁₃Pow_succ, LinearMap.comp_apply, ih, mulBySubPow_succ]
    ext p m n
    simp only [mulBySub₁₃_apply, LinearMap.comp_apply, mulBySub_apply, map_sub]

/-- Evaluation of a three-variable distribution through a linear map. -/
def map3 (f : 𝒲 →ₗ[ℂ] 𝒲') (D : FormalDist₃ 𝒲) : FormalDist₃ 𝒲' := fun p m n => f (D p m n)

theorem map3_12 (f : 𝒲 →ₗ[ℂ] 𝒲') (M : ℕ) (D : FormalDist₃ 𝒲) :
    map3 f (mulBySub₁₂Pow M D) = mulBySub₁₂Pow M (map3 f D) := by
  induction M with
  | zero => rfl
  | succ M ih =>
    change map3 f (mulBySub₁₂ (mulBySub₁₂Pow M D)) = mulBySub₁₂ (mulBySub₁₂Pow M (map3 f D))
    rw [← ih]
    ext p m n
    simp only [map3, mulBySub₁₂_apply, map_sub]

theorem map3_13 (f : 𝒲 →ₗ[ℂ] 𝒲') (M : ℕ) (D : FormalDist₃ 𝒲) :
    map3 f (mulBySub₁₃Pow M D) = mulBySub₁₃Pow M (map3 f D) := by
  induction M with
  | zero => rfl
  | succ M ih =>
    change map3 f (mulBySub₁₃ (mulBySub₁₃Pow M D)) = mulBySub₁₃ (mulBySub₁₃Pow M (map3 f D))
    rw [← ih]
    ext p m n
    simp only [map3, mulBySub₁₃_apply, map_sub]

end Cancel

/-! ## The three-variable bracket and the two-variable Goddard lemma -/

section Goddard

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- `[A(w), F(z₁,z₂)]`, with `w` the first variable. -/
def brk3 (A : FormalDist (End ℂ V)) (F : FormalDist₂ (End ℂ V)) : FormalDist₃ (End ℂ V) :=
  fun p m n => A p * F m n - F m n * A p

/-- **M8h-0a: the two-variable Goddard lemma.**  Let `B(z₁,z₂)` annihilate `vac`, let `A(w)`
create from `vac` only non-negative powers of `w`, and let
`(w−z₁)^{M₁}(w−z₂)^{M₂}[A(w), B(z₁,z₂)] = 0`.  Then `B(z₁,z₂) A(w) vac = 0`. -/
theorem goddard₂ (vac : V) (A : FormalDist (End ℂ V)) (B : FormalDist₂ (End ℂ V)) (M₁ M₂ : ℕ)
    (hloc : mulBySub₁₂Pow M₁ (mulBySub₁₃Pow M₂ (brk3 A B)) = 0)
    (hneg : ∀ p : ℤ, p < 0 → A p vac = 0) (hvac : ∀ m n, B m n vac = 0) (p m n : ℤ) :
    B m n (A p vac) = 0 := by
  set ev : End ℂ V →ₗ[ℂ] V := LinearMap.applyₗ vac
  set G : FormalDist₃ V := fun p m n => B m n (A p vac) with hG
  have hmap : map3 ev (brk3 A B) = -G := by
    ext p m n
    simp only [map3, brk3, ev, LinearMap.applyₗ_apply_apply, LinearMap.sub_apply,
      Module.End.mul_apply, hvac, map_zero, zero_sub, hG]
    rfl
  have h0 : mulBySub₁₂Pow M₁ (mulBySub₁₃Pow M₂ G) = 0 := by
    have := congrArg (map3 ev) hloc
    rw [map3_12, map3_13, hmap, map_neg, map_neg] at this
    have hz : map3 ev (0 : FormalDist₃ (End ℂ V)) = 0 := by
      ext p m n; simp [map3]; rfl
    rw [hz] at this
    exact neg_eq_zero.mp this
  have hb : BddBelow₁₃ G := ⟨0, fun p m n hp => by
    change B m n (A p vac) = 0
    rw [hneg p hp, map_zero]⟩
  have h1 := eq_zero_of_mulBySub₁₂Pow M₁ h0 (hb.mulBySub₁₃Pow M₂)
  have h2 := eq_zero_of_mulBySub₁₃Pow M₂ h1 hb
  exact congrFun (congrFun (congrFun h2 p) m) n

/-! ## Three-variable locality of a commutator -/

/-- `G(w,z₁) c(z₂)`. -/
def mulR12 (G : FormalDist₂ (End ℂ V)) (c : FormalDist (End ℂ V)) : FormalDist₃ (End ℂ V) :=
  fun p m n => G p m * c n
/-- `c(z₂) G(w,z₁)`. -/
def mulL12 (c : FormalDist (End ℂ V)) (G : FormalDist₂ (End ℂ V)) : FormalDist₃ (End ℂ V) :=
  fun p m n => c n * G p m
/-- `G(w,z₂) a(z₁)`. -/
def mulR13 (G : FormalDist₂ (End ℂ V)) (a : FormalDist (End ℂ V)) : FormalDist₃ (End ℂ V) :=
  fun p m n => G p n * a m
/-- `a(z₁) G(w,z₂)`. -/
def mulL13 (a : FormalDist (End ℂ V)) (G : FormalDist₂ (End ℂ V)) : FormalDist₃ (End ℂ V) :=
  fun p m n => a m * G p n

theorem pow12_mulR12 (M : ℕ) (G : FormalDist₂ (End ℂ V)) (c : FormalDist (End ℂ V)) :
    mulBySub₁₂Pow M (mulR12 G c) = mulR12 (mulBySubPow M G) c :=
  map12 (fun n => LinearMap.mulRight ℂ (c n)) M G

theorem pow12_mulL12 (M : ℕ) (G : FormalDist₂ (End ℂ V)) (c : FormalDist (End ℂ V)) :
    mulBySub₁₂Pow M (mulL12 c G) = mulL12 c (mulBySubPow M G) :=
  map12 (fun n => LinearMap.mulLeft ℂ (c n)) M G

theorem pow13_mulR13 (M : ℕ) (G : FormalDist₂ (End ℂ V)) (a : FormalDist (End ℂ V)) :
    mulBySub₁₃Pow M (mulR13 G a) = mulR13 (mulBySubPow M G) a :=
  map13 (fun m => LinearMap.mulRight ℂ (a m)) M G

theorem pow13_mulL13 (M : ℕ) (G : FormalDist₂ (End ℂ V)) (a : FormalDist (End ℂ V)) :
    mulBySub₁₃Pow M (mulL13 a G) = mulL13 a (mulBySubPow M G) :=
  map13 (fun m => LinearMap.mulLeft ℂ (a m)) M G

theorem mulR12_zero (c : FormalDist (End ℂ V)) : mulR12 0 c = 0 := by
  ext p m n x; change ((0 : End ℂ V) * c n) x = 0; simp
theorem mulL12_zero (c : FormalDist (End ℂ V)) : mulL12 c 0 = 0 := by
  ext p m n x; change (c n * (0 : End ℂ V)) x = 0; simp
theorem mulR13_zero (a : FormalDist (End ℂ V)) : mulR13 0 a = 0 := by
  ext p m n x; change ((0 : End ℂ V) * a m) x = 0; simp
theorem mulL13_zero (a : FormalDist (End ℂ V)) : mulL13 a 0 = 0 := by
  ext p m n x; change (a m * (0 : End ℂ V)) x = 0; simp

/-- `a(z₁) b(z₂)`. -/
def prod2 (a b : FormalDist (End ℂ V)) : FormalDist₂ (End ℂ V) := fun m n => a m * b n
/-- `b(z₂) a(z₁)`. -/
def prod2' (a b : FormalDist (End ℂ V)) : FormalDist₂ (End ℂ V) := fun m n => b n * a m

theorem brk3_prod (A a b : FormalDist (End ℂ V)) :
    brk3 A (prod2 a b) = mulR12 (bracketDist A a) b + mulL13 a (bracketDist A b) := by
  ext p m n x
  change (A p * (a m * b n) - a m * b n * A p) x
    = ((A p * a m - a m * A p) * b n) x + (a m * (A p * b n - b n * A p)) x
  rw [← LinearMap.add_apply]
  congr 1
  noncomm_ring

theorem brk3_prod' (A a b : FormalDist (End ℂ V)) :
    brk3 A (prod2' a b) = mulR13 (bracketDist A b) a + mulL12 b (bracketDist A a) := by
  ext p m n x
  change (A p * (b n * a m) - b n * a m * A p) x
    = ((A p * b n - b n * A p) * a m) x + (b n * (A p * a m - a m * A p)) x
  rw [← LinearMap.add_apply]
  congr 1
  noncomm_ring

/-- Three-variable locality of a product `a(z₁)b(z₂)` with `A(w)`. -/
theorem loc3_prod {A a b : FormalDist (End ℂ V)} {M₁ M₂ : ℕ}
    (ha : mulBySubPow M₁ (bracketDist A a) = 0) (hb : mulBySubPow M₂ (bracketDist A b) = 0) :
    mulBySub₁₂Pow M₁ (mulBySub₁₃Pow M₂ (brk3 A (prod2 a b))) = 0 := by
  rw [brk3_prod, map_add, map_add, pow13_mulL13, hb, mulL13_zero, map_zero, add_zero,
    pow12_pow13_comm, pow12_mulR12, ha, mulR12_zero, map_zero]

theorem loc3_prod' {A a b : FormalDist (End ℂ V)} {M₁ M₂ : ℕ}
    (ha : mulBySubPow M₁ (bracketDist A a) = 0) (hb : mulBySubPow M₂ (bracketDist A b) = 0) :
    mulBySub₁₂Pow M₁ (mulBySub₁₃Pow M₂ (brk3 A (prod2' a b))) = 0 := by
  rw [brk3_prod', map_add, map_add, pow13_mulR13, hb, mulR13_zero, map_zero, zero_add,
    pow12_pow13_comm, pow12_mulL12, ha, mulL12_zero, map_zero]

theorem brk3_mulBySub (A : FormalDist (End ℂ V)) (F : FormalDist₂ (End ℂ V)) :
    brk3 A (mulBySub F) = mulBySub₂₃ (brk3 A F) := by
  ext p m n x
  simp only [brk3, mulBySub_apply, mulBySub₂₃_apply, mul_sub, sub_mul, LinearMap.sub_apply]
  abel

theorem brk3_mulBySubPow (A : FormalDist (End ℂ V)) (N : ℕ) (F : FormalDist₂ (End ℂ V)) :
    brk3 A (mulBySubPow N F) = mulBySub₂₃Pow N (brk3 A F) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [mulBySubPow_succ, LinearMap.comp_apply, brk3_mulBySub, ih, mulBySub₂₃Pow_succ,
      LinearMap.comp_apply]

theorem brk3_sub (A : FormalDist (End ℂ V)) (F F' : FormalDist₂ (End ℂ V)) :
    brk3 A (F - F') = brk3 A F - brk3 A F' := by
  ext p m n x
  simp only [brk3]
  change (A p * (F m n - F' m n) - (F m n - F' m n) * A p) x
    = (A p * F m n - F m n * A p) x - (A p * F' m n - F' m n * A p) x
  rw [← LinearMap.sub_apply]
  congr 1
  noncomm_ring

/-- **The hypothesis of `goddard₂` for `(z₁−z₂)ᴺ[a(z₁), b(z₂)]`**: if `A` is local with `a`
and with `b`, the three-variable locality holds for every `N`. -/
theorem loc3_mulBySubPow_bracketDist {A a b : FormalDist (End ℂ V)} (ha : Local A a)
    (hb : Local A b) (N : ℕ) :
    ∃ M₁ M₂ : ℕ, mulBySub₁₂Pow M₁ (mulBySub₁₃Pow M₂
      (brk3 A (mulBySubPow N (bracketDist a b)))) = 0 := by
  obtain ⟨M₁, h₁⟩ := ha
  obtain ⟨M₂, h₂⟩ := hb
  refine ⟨M₁, M₂, ?_⟩
  have hsplit : bracketDist a b = prod2 a b - prod2' a b := rfl
  rw [brk3_mulBySubPow, pow13_pow23_comm, pow12_pow23_comm, hsplit, brk3_sub, map_sub, map_sub,
    loc3_prod h₁ h₂, loc3_prod' h₁ h₂, sub_zero, map_zero]

end Goddard

end VOA.Moonshine.M8h0
