/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Core.Dong
import VOA.Core.Reconstruction
import VOA.Core.Identities
import VOA.Foundations.Locality

/-!
# Generic field operations: `nprod`-closure and the identity field

The closure of fields under the same-variable normal-ordered product, and the identity field
`idField = id·z⁰` with its locality and unit laws.  Nothing here is specific to any example:
`V` is an arbitrary `ℂ`-vector space, exactly as in `Core.Dong`.

These were originally proved inside `Examples/HeisenbergVertex.lean`, where they were the first
consumer, and are hoisted here unchanged (same names, same `VOA` namespace) so that the
module-side constructions can use them without an `Examples` dependency.  Li's local systems of
weak vertex operators need exactly this closure together with Dong's lemma.
-/

namespace VOA

open scoped BigOperators
open Module (End)

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-! ## §0  Generic locality infrastructure: derivative and swap preserve locality -/

/-- The `∂_{z₁}` of a two-variable distribution: `(∂₁G)(s,t) = (s+1)·G(s+1,t)`. -/
def d1 (G : FormalDist₂ (End ℂ V)) : FormalDist₂ (End ℂ V) := fun s t => (s + 1) • G (s + 1) t

/-- The `∂_{z₂}` of a two-variable distribution: `(∂₂G)(s,t) = (t+1)·G(s,t+1)`. -/
def d2 (G : FormalDist₂ (End ℂ V)) : FormalDist₂ (End ℂ V) := fun s t => (t + 1) • G s (t + 1)

theorem d1_zero : d1 (0 : FormalDist₂ (End ℂ V)) = 0 := by
  apply FormalDist₂.ext; intro s t
  show (s + 1) • (0 : FormalDist₂ (End ℂ V)) (s + 1) t = (0 : FormalDist₂ (End ℂ V)) s t
  show (s + 1) • (0 : End ℂ V) = (0 : End ℂ V); rw [smul_zero]

theorem d2_zero : d2 (0 : FormalDist₂ (End ℂ V)) = 0 := by
  apply FormalDist₂.ext; intro s t
  show (t + 1) • (0 : FormalDist₂ (End ℂ V)) s (t + 1) = (0 : FormalDist₂ (End ℂ V)) s t
  show (t + 1) • (0 : End ℂ V) = (0 : End ℂ V); rw [smul_zero]

/-- The commutator `[∂₁, (z₁-z₂)·] = id`: `(z₁-z₂)·(∂₁G) = ∂₁((z₁-z₂)·G) - G`. -/
theorem mulBySub_d1 (G : FormalDist₂ (End ℂ V)) : mulBySub (d1 G) = d1 (mulBySub G) - G := by
  apply FormalDist₂.ext; intro s t
  rw [mulBySub_apply]
  show (d1 G) (s - 1) t - (d1 G) s (t - 1) = (s + 1) • (mulBySub G) (s + 1) t - G s t
  rw [mulBySub_apply]
  show (s - 1 + 1) • G ((s - 1) + 1) t - (s + 1) • G (s + 1) (t - 1)
     = (s + 1) • (G ((s + 1) - 1) t - G (s + 1) (t - 1)) - G s t
  rw [show (s + 1) - 1 = s by ring, show s - 1 + 1 = s by ring]
  module

/-- The commutator `[∂₂, (z₁-z₂)·] = -id`: `(z₁-z₂)·(∂₂G) = ∂₂((z₁-z₂)·G) + G`. -/
theorem mulBySub_d2 (G : FormalDist₂ (End ℂ V)) : mulBySub (d2 G) = d2 (mulBySub G) + G := by
  apply FormalDist₂.ext; intro s t
  rw [mulBySub_apply]
  show (d2 G) (s - 1) t - (d2 G) s (t - 1) = (t + 1) • (mulBySub G) s (t + 1) + G s t
  rw [mulBySub_apply]
  show (t + 1) • G (s - 1) (t + 1) - (t - 1 + 1) • G s ((t - 1) + 1)
     = (t + 1) • (G (s - 1) (t + 1) - G s ((t + 1) - 1)) + G s t
  rw [show (t + 1) - 1 = t by ring, show t - 1 + 1 = t by ring]
  module

/-- If `(z₁-z₂)ᴺ G = 0` then `(z₁-z₂)ᴺ⁺¹ (∂₁G) = 0`: differentiating in `z₁` costs one extra
locality power.  (Gannon-style: `∂₁(z₁-z₂)ᴺG = 0`, multiply by `(z₁-z₂)` and peel.) -/
theorem mulBySubPow_succ_d1_of_zero : ∀ (N : ℕ) (G : FormalDist₂ (End ℂ V)),
    mulBySubPow N G = 0 → mulBySubPow (N + 1) (d1 G) = 0 := by
  intro N; induction N with
  | zero => intro G hG; rw [mulBySubPow_zero] at hG
            have hz : G = 0 := by simpa using hG
            rw [hz, d1_zero, map_zero]
  | succ p ih =>
    intro G hG
    rw [mulBySubPow_succ', mulBySub_d1, map_sub]
    have h1 : mulBySubPow p (mulBySub G) = 0 := by rw [← mulBySubPow_succ']; exact hG
    rw [ih (mulBySub G) h1, hG, sub_zero]

/-- If `(z₁-z₂)ᴺ G = 0` then `(z₁-z₂)ᴺ⁺¹ (∂₂G) = 0`. -/
theorem mulBySubPow_succ_d2_of_zero : ∀ (N : ℕ) (G : FormalDist₂ (End ℂ V)),
    mulBySubPow N G = 0 → mulBySubPow (N + 1) (d2 G) = 0 := by
  intro N; induction N with
  | zero => intro G hG; rw [mulBySubPow_zero] at hG
            have hz : G = 0 := by simpa using hG
            rw [hz, d2_zero, map_zero]
  | succ p ih =>
    intro G hG
    rw [mulBySubPow_succ', mulBySub_d2, map_add]
    have h1 : mulBySubPow p (mulBySub G) = 0 := by rw [← mulBySubPow_succ']; exact hG
    rw [ih (mulBySub G) h1, hG, add_zero]

/-- The bracket with `∂a` on the left is `∂₁` of the bracket: `[∂a(z₁),b(z₂)] = ∂₁[a,b]`. -/
theorem bracketDist_deriv_left (a b : FormalDist (End ℂ V)) :
    bracketDist (deriv a) b = d1 (bracketDist a b) := by
  apply FormalDist₂.ext; intro m n
  show (deriv a) m * b n - b n * (deriv a) m = (m + 1) • bracketDist a b (m + 1) n
  rw [deriv_apply, bracketDist_apply, smul_sub, smul_mul_assoc, mul_smul_comm]

/-- The bracket with `∂b` on the right is `∂₂` of the bracket: `[a(z₁),∂b(z₂)] = ∂₂[a,b]`. -/
theorem bracketDist_deriv_right (a b : FormalDist (End ℂ V)) :
    bracketDist a (deriv b) = d2 (bracketDist a b) := by
  apply FormalDist₂.ext; intro m n
  show a m * (deriv b) n - (deriv b) n * a m = (n + 1) • bracketDist a b m (n + 1)
  rw [deriv_apply, bracketDist_apply, smul_sub, mul_smul_comm, smul_mul_assoc]

/-- **Locality is preserved by `∂_z` on the left**: `Local a b → Local (∂a) b`. -/
theorem Local.derivL {a b : FormalDist (End ℂ V)} (h : Local a b) : Local (deriv a) b := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N + 1, by rw [bracketDist_deriv_left]; exact mulBySubPow_succ_d1_of_zero N _ hN⟩

/-- **Locality is preserved by `∂_z` on the right**: `Local a b → Local a (∂b)`. -/
theorem Local.derivR {a b : FormalDist (End ℂ V)} (h : Local a b) : Local a (deriv b) := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N + 1, by rw [bracketDist_deriv_right]; exact mulBySubPow_succ_d2_of_zero N _ hN⟩

/-- Iterating: `Local a b → Local (∂^[i] a) b`. -/
theorem Local.deriv_iterate_left {a b : FormalDist (End ℂ V)} (h : Local a b) (i : ℕ) :
    Local ((deriv^[i]) a) b := by
  induction i with
  | zero => simpa using h
  | succ p ih => rw [Function.iterate_succ', Function.comp_apply]; exact ih.derivL

/-- Iterating: `Local a b → Local a (∂^[j] b)`. -/
theorem Local.deriv_iterate_right {a b : FormalDist (End ℂ V)} (h : Local a b) (j : ℕ) :
    Local a ((deriv^[j]) b) := by
  induction j with
  | zero => simpa using h
  | succ p ih => rw [Function.iterate_succ', Function.comp_apply]; exact ih.derivR

/-- Swap of the two variables of a two-variable distribution. -/
def swap₂ (G : FormalDist₂ (End ℂ V)) : FormalDist₂ (End ℂ V) := fun m n => G n m

theorem swap₂_zero : swap₂ (0 : FormalDist₂ (End ℂ V)) = 0 := rfl

theorem mulBySub_swap (G : FormalDist₂ (End ℂ V)) :
    mulBySub (swap₂ G) = - swap₂ (mulBySub G) := by
  apply FormalDist₂.ext; intro m n
  show G n (m - 1) - G (n - 1) m = -((mulBySub G) n m)
  rw [mulBySub_apply]; abel

theorem mulBySubPow_swap_eq_zero : ∀ (N : ℕ) (G : FormalDist₂ (End ℂ V)),
    mulBySubPow N G = 0 → mulBySubPow N (swap₂ G) = 0 := by
  intro N; induction N with
  | zero => intro G hG; rw [mulBySubPow_zero] at hG
            have hz : G = 0 := by simpa using hG
            rw [mulBySubPow_zero, hz, swap₂_zero]; rfl
  | succ p ih =>
    intro G hG
    rw [mulBySubPow_succ', mulBySub_swap, map_neg]
    have h1 : mulBySubPow p (mulBySub G) = 0 := by rw [← mulBySubPow_succ']; exact hG
    rw [ih (mulBySub G) h1, neg_zero]

theorem swap₂_bracketDist (a b : FormalDist (End ℂ V)) :
    swap₂ (bracketDist a b) = - bracketDist b a := by
  apply FormalDist₂.ext; intro m n
  show (bracketDist a b) n m = (- bracketDist b a) m n
  rw [bracketDist_apply]
  show a n * b m - b m * a n = -(bracketDist b a m n)
  rw [bracketDist_apply]; abel

/-- **Mutual locality is symmetric**: `Local a b → Local b a`. -/
theorem Local.symm {a b : FormalDist (End ℂ V)} (h : Local a b) : Local b a := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  have hs := mulBySubPow_swap_eq_zero N (bracketDist a b) hN
  rw [swap₂_bracketDist, map_neg, neg_eq_zero] at hs
  exact hs

/-! ## §1  `IsField (nprod a b)`: the normal-ordered product of two fields is a field

The same-variable normal-ordered product `:a(z)b(z):` of two lower-truncated fields is again
lower-truncated, hence a field — exactly the closure needed to iterate `nprod`.  The proof
uses that for fixed `x` the diagonal support in `m` is finite and, on the negative-`m` side,
`s`-independent, so a single lower bound `B` makes every summand vanish for `s < B`. -/

/-- **The normal-ordered product of two fields is a field** (Gannon 5.1.6b).  For each vector
`x`, the truncation bound is `min B Bb` where `Bb` truncates `b` and `B = min_{m∈[min Ba 0,0]}
(Bb(a m x) + m)` handles the finitely many `s`-independent negative modes. -/
theorem IsField.nprod {a b : FormalDist (End ℂ V)} (ha : IsField a) (hb : IsField b) :
    IsField (nprod ha hb) := by
  intro x
  classical
  obtain ⟨Ba, hBa⟩ := ha x
  obtain ⟨Bb, hBb⟩ := hb x
  set S0 : Finset ℤ := Finset.Icc (min Ba 0) 0 with hS0
  have hS0ne : S0.Nonempty := by rw [hS0, Finset.nonempty_Icc]; exact min_le_right _ _
  let Bbm : ℤ → ℤ := fun m => Classical.choose (hb (a m x))
  have hBbm : ∀ m : ℤ, ∀ j : ℤ, j < Bbm m → b j (a m x) = 0 :=
    fun m => Classical.choose_spec (hb (a m x))
  set B : ℤ := S0.inf' hS0ne (fun m => Bbm m + m) with hB
  refine ⟨min B Bb, fun n hn => ?_⟩
  rw [nprod_apply]
  apply finsum_eq_zero_of_forall_eq_zero
  intro m
  rw [normalOrdered_apply]
  by_cases h0 : 0 ≤ m
  · rw [if_pos h0]
    show a m (b (n - m) x) = 0
    have hbz : b (n - m) x = 0 := hBb (n - m) (by
      have : n < Bb := lt_of_lt_of_le hn (min_le_right _ _); omega)
    rw [hbz, map_zero]
  · rw [if_neg h0]
    show b (n - m) (a m x) = 0
    by_cases hmem : m ∈ S0
    · apply hBbm m (n - m)
      have hle : B ≤ Bbm m + m := Finset.inf'_le (fun m => Bbm m + m) hmem
      have hnB : n < B := lt_of_lt_of_le hn (min_le_left _ _)
      omega
    · rw [hS0, Finset.mem_Icc, not_and_or] at hmem
      have hlt : m < min Ba 0 := by
        rcases hmem with h | h
        · exact lt_of_not_ge h
        · exact absurd (lt_of_not_ge h) (by omega)
      have haz : a m x = 0 := hBa m (lt_of_lt_of_le hlt (min_le_left _ _))
      rw [haz, map_zero]

/-! ## §2  The identity field `Y(1,z) = id·z⁰` -/

/-- The **identity field** `Y(1,z) = id`: the constant distribution `id·z⁰`, with coefficient
`id` at `z`-power `0` and `0` elsewhere (Gannon VA2). -/
noncomputable def idField : FormalDist (End ℂ V) := fun j => if j = 0 then LinearMap.id else 0

@[simp] theorem idField_apply (j : ℤ) :
    (idField : FormalDist (End ℂ V)) j = if j = 0 then LinearMap.id else 0 := rfl

theorem idField_isField : IsField (idField : FormalDist (End ℂ V)) := by
  intro x; exact ⟨0, fun n hn => by
    rw [idField_apply, if_neg (by omega)]; rfl⟩

/-- The identity field commutes with every distribution (`id` is central): `[1(z₁),b(z₂)] = 0`. -/
theorem bracketDist_idField_left (b : FormalDist (End ℂ V)) :
    bracketDist (idField : FormalDist (End ℂ V)) b = 0 := by
  apply FormalDist₂.ext; intro m n
  rw [bracketDist_apply, idField_apply]
  show (if m = 0 then LinearMap.id else 0 : End ℂ V) * b n
      - b n * (if m = 0 then LinearMap.id else 0) = (0 : FormalDist₂ (End ℂ V)) m n
  by_cases h : m = 0
  · rw [if_pos h, show (LinearMap.id : End ℂ V) = 1 from rfl, one_mul, mul_one, sub_self]; rfl
  · rw [if_neg h, zero_mul, mul_zero, sub_zero]; rfl

theorem Local_idField_left (b : FormalDist (End ℂ V)) :
    Local (idField : FormalDist (End ℂ V)) b :=
  local_of_bracketDist_eq_zero (bracketDist_idField_left b)

theorem Local_idField_right (b : FormalDist (End ℂ V)) :
    Local b (idField : FormalDist (End ℂ V)) :=
  (Local_idField_left b).symm

/-- `:a(z) 1: = a(z)`: the normal-ordered product with the identity field is the identity
operation on fields.  (Only the `m = s` summand survives, since `1(z)` lives at `z⁰`.) -/
theorem nprod_idField {a : FormalDist (End ℂ V)} (ha : IsField a) :
    nprod ha (idField_isField) = a := by
  funext s
  apply LinearMap.ext; intro x
  rw [nprod_apply, finsum_eq_single _ s]
  · rw [normalOrdered_apply]
    have hid : (idField : FormalDist (End ℂ V)) (s - s) = LinearMap.id := by
      rw [idField_apply, if_pos (by ring)]
    by_cases h : 0 ≤ s
    · rw [if_pos h, hid]; rfl
    · rw [if_neg h, hid]; rfl
  · intro m hm
    rw [normalOrdered_apply]
    have hid : (idField : FormalDist (End ℂ V)) (s - m) = 0 := by
      rw [idField_apply, if_neg (by omega)]
    by_cases h : 0 ≤ m
    · rw [if_pos h, hid]; simp
    · rw [if_neg h, hid]; simp

end VOA
