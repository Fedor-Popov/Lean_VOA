/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import Mathlib

/-!
# Local independence of products of evaluation forms

Let `P_l` be the space of polynomials `f(s) = Σ_{j ≤ l} u_j s^j`; its coordinate ring is
`ℂ[u_0, …, u_l] ⊆ ℂ[u_j]`. For a point `t` we have the linear forms

  `ev_l(t) = f(t) = Σ_j t^j u_j`,   `evd_l(t) = f'(t) = Σ_j j t^{j-1} u_j`.

A *configuration* is a list of points `t_i` (pairwise distinct), each of multiplicity one or two.
A point of multiplicity two carries the four local forms `1, β ev, γ ev + δ evd, β² ev²` (of
degrees `0, 1, 1, 2`); a point of multiplicity one carries `1, β ev` (degrees `0, 1`).  With
`M = Σ mult` and `l = M - k`, the products of local forms of total degree `k` are linearly
independent in `ℂ[u_0, …, u_l]`.

* `local_indep` — the independence theorem, by induction on `M`: the substitution
  `f = (s - t_p) h` (`psi0`) removes the local forms vanishing at `t_p`, and the remaining
  terms are divisible by `ev(t_p)`.

This is the generic-fibre statement used for the jet-ring lower bound (the fibre of the jet image
at distinct points is a tensor product of local four-dimensional spaces).  Everything is proved
outright.
-/

namespace VOA.JetProduct

open MvPolynomial
open scoped BigOperators

noncomputable section

/-- The coordinate ring of the polynomials `f(s) = Σ u_j s^j`. -/
abbrev UPoly : Type := MvPolynomial ℕ ℂ

/-- The evaluation form `f ↦ f(t)` on polynomials of degree `≤ l`. -/
def ev (l : ℕ) (t : ℂ) : UPoly := ∑ j ∈ Finset.range (l + 1), C (t ^ j) * X j

/-- The derivative-evaluation form `f ↦ f'(t)` on polynomials of degree `≤ l`. -/
def evd (l : ℕ) (t : ℂ) : UPoly :=
  ∑ j ∈ Finset.range (l + 1), C ((j : ℂ) * t ^ (j - 1)) * X j

/-- The substitution `f = (s - t₀) h` with `deg h ≤ l - 1`: the new variables are the
coefficients of `h`. -/
def psi0 (l : ℕ) (t₀ : ℂ) : UPoly →ₐ[ℂ] UPoly :=
  aeval fun j => (if 1 ≤ j ∧ j ≤ l then X (j - 1) else 0) - C t₀ * (if j < l then X j else 0)

theorem psi0_X (l : ℕ) (t₀ : ℂ) (j : ℕ) :
    psi0 l t₀ (X j) = (if 1 ≤ j ∧ j ≤ l then X (j - 1) else 0) -
      C t₀ * (if j < l then X j else 0) := by
  simp [psi0]

/-- Splitting `Σ_{j ≤ m+1} a_j ψ(X_j)` into the shifted and the scaled parts. -/
theorem psi0_sum (m : ℕ) (t₀ : ℂ) (a : ℕ → ℂ) :
    psi0 (m + 1) t₀ (∑ j ∈ Finset.range (m + 2), C (a j) * X j) =
      ∑ i ∈ Finset.range (m + 1), C (a (i + 1) - t₀ * a i) * X i := by
  rw [map_sum]
  simp only [map_mul, algHom_C, algebraMap_eq, psi0_X, mul_sub]
  rw [Finset.sum_sub_distrib]
  have hA : ∑ j ∈ Finset.range (m + 2),
      C (a j) * (if 1 ≤ j ∧ j ≤ m + 1 then X (j - 1) else (0 : UPoly)) =
      ∑ i ∈ Finset.range (m + 1), C (a (i + 1)) * X i := by
    rw [Finset.sum_range_succ']
    simp only [show ¬ (1 ≤ 0 ∧ 0 ≤ m + 1) by omega, if_false, mul_zero, add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < m + 1 := Finset.mem_range.mp hi
    rw [if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel]
  have hB : ∑ j ∈ Finset.range (m + 2),
      C (a j) * (C t₀ * (if j < m + 1 then X j else (0 : UPoly))) =
      ∑ i ∈ Finset.range (m + 1), C (t₀ * a i) * X i := by
    rw [Finset.sum_range_succ]
    simp only [lt_irrefl, if_false, mul_zero, add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < m + 1 := Finset.mem_range.mp hi
    rw [if_pos hi', map_mul]; ring
  rw [hA, hB, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sub]; ring

theorem psi0_ev (m : ℕ) (t₀ t : ℂ) : psi0 (m + 1) t₀ (ev (m + 1) t) = C (t - t₀) * ev m t := by
  rw [ev, psi0_sum, ev, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_assoc, ← map_mul]
  congr 2
  ring

theorem psi0_evd (m : ℕ) (t₀ t : ℂ) :
    psi0 (m + 1) t₀ (evd (m + 1) t) = ev m t + C (t - t₀) * evd m t := by
  rw [evd, psi0_sum, ev, evd, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [show ∀ a b c : ℂ, C a * X i + C b * (C c * X i) = (C (a + b * c) : UPoly) * X i from
    fun a b c => by rw [map_add, map_mul]; ring]
  congr 2
  rcases i with _ | i
  · simp
  · simp only [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right]
    ring

/-- `ev` is a nonzero polynomial (its `u_0` coefficient is `1`). -/
theorem ev_ne_zero (l : ℕ) (t : ℂ) : ev l t ≠ 0 := by
  intro h
  have h2 := congrArg (MvPolynomial.eval (fun j : ℕ => if j = 0 then (1 : ℂ) else 0)) h
  rw [ev, map_sum, map_zero, Finset.sum_eq_single 0] at h2
  · simp at h2
  · intro b _ hb; simp [hb]
  · intro h0; simp at h0

/-! ### Configurations -/

/-- A point of a configuration: position `t`, local coefficients `β, γ, δ`, and multiplicity
two (`two = true`) or one. -/
structure Pt where
  t : ℂ
  β : ℂ
  γ : ℂ
  δ : ℂ
  two : Bool

/-- The multiplicity of a point. -/
def Pt.mult (p : Pt) : ℕ := if p.two then 2 else 1

/-- Degrees of the four local types `1, ev, ev', ev²`. -/
def tdeg (x : Fin 4) : ℕ := ![0, 1, 1, 2] x

/-- The local types allowed at a point. -/
def Pt.allowed (p : Pt) (x : Fin 4) : Prop := p.two = true ∨ x.val ≤ 1

instance (p : Pt) : DecidablePred p.allowed := fun x => by
  unfold Pt.allowed; infer_instance

/-- The local forms at a point. -/
def loc (l : ℕ) (p : Pt) (x : Fin 4) : UPoly :=
  ![1, C p.β * ev l p.t, C p.γ * ev l p.t + C p.δ * evd l p.t, C (p.β ^ 2) * ev l p.t ^ 2] x

/-- The total multiplicity. -/
def totalMult (P : List Pt) : ℕ := (P.map Pt.mult).sum

/-- The valid type assignments of total degree `k`. -/
def validSet : List Pt → ℕ → Finset (List (Fin 4))
  | [], k => if k = 0 then {[]} else ∅
  | p :: P, k => Finset.univ.biUnion fun x =>
      if p.allowed x ∧ tdeg x ≤ k then (validSet P (k - tdeg x)).image (List.cons x) else ∅

/-- The product of local forms attached to an assignment. -/
def F (l : ℕ) : List Pt → List (Fin 4) → UPoly
  | p :: P, x :: g => loc l p x * F l P g
  | _, _ => 1

/-- The transformed point after the substitution `f = (s - t₀) h`. -/
def Pt.tr (t₀ : ℂ) (q : Pt) : Pt :=
  { t := q.t, β := q.β * (q.t - t₀), γ := q.γ * (q.t - t₀) + q.δ, δ := q.δ * (q.t - t₀),
    two := q.two }

/-- Admissible configurations: distinct positions, nonzero `β, δ`. -/
def Good (P : List Pt) : Prop :=
  P.Pairwise (fun p q => p.t ≠ q.t) ∧ ∀ p ∈ P, p.β ≠ 0 ∧ p.δ ≠ 0

@[simp] theorem totalMult_nil : totalMult [] = 0 := rfl
@[simp] theorem totalMult_cons (p : Pt) (P : List Pt) :
    totalMult (p :: P) = p.mult + totalMult P := by simp [totalMult]

@[simp] theorem F_cons (l : ℕ) (p : Pt) (P : List Pt) (x : Fin 4) (g : List (Fin 4)) :
    F l (p :: P) (x :: g) = loc l p x * F l P g := rfl

theorem tdeg_le_mult (p : Pt) (x : Fin 4) (hx : p.allowed x) : tdeg x ≤ p.mult := by
  unfold Pt.mult
  rcases hx with h | h <;> fin_cases x <;> split_ifs <;> simp_all [tdeg]

theorem mem_validSet_cons (p : Pt) (P : List Pt) (k : ℕ) (g : List (Fin 4)) :
    g ∈ validSet (p :: P) k ↔ ∃ x g', g = x :: g' ∧ p.allowed x ∧ tdeg x ≤ k ∧
      g' ∈ validSet P (k - tdeg x) := by
  simp only [validSet, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx⟩
    split_ifs at hx with h
    · obtain ⟨g', hg', rfl⟩ := Finset.mem_image.mp hx
      exact ⟨x, g', rfl, h.1, h.2, hg'⟩
    · simp at hx
  · rintro ⟨x, g', rfl, h1, h2, hg'⟩
    exact ⟨x, by rw [if_pos ⟨h1, h2⟩]; exact Finset.mem_image_of_mem _ hg'⟩

theorem le_of_mem_validSet : ∀ (P : List Pt) (k : ℕ) (g : List (Fin 4)),
    g ∈ validSet P k → k ≤ totalMult P
  | [], k, g, h => by
    simp only [validSet] at h
    split_ifs at h with hk
    · simp [hk]
    · simp at h
  | p :: P, k, g, h => by
    obtain ⟨x, g', rfl, h1, h2, hg'⟩ := (mem_validSet_cons p P k g).mp h
    have := le_of_mem_validSet P _ g' hg'
    have := tdeg_le_mult p x h1
    simp only [totalMult_cons]
    omega

theorem sum_validSet_cons {M : Type*} [AddCommMonoid M] (p : Pt) (P : List Pt) (k : ℕ)
    (f : List (Fin 4) → M) :
    ∑ g ∈ validSet (p :: P) k, f g = ∑ x : Fin 4,
      if p.allowed x ∧ tdeg x ≤ k then ∑ g' ∈ validSet P (k - tdeg x), f (x :: g') else 0 := by
  rw [validSet, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro x _
    split_ifs
    · rw [Finset.sum_image]
      intro a _ b _ h
      exact List.cons_injective h
    · simp
  · intro x _ y _ hxy
    simp only [Function.onFun]
    split_ifs <;> try simp only [Finset.disjoint_empty_left, Finset.disjoint_empty_right]
    rw [Finset.disjoint_left]
    intro g hx hy
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hy
    exact hxy (List.cons_eq_cons.mp hb).1.symm

theorem validSet_map_tr (t₀ : ℂ) : ∀ (P : List Pt) (k : ℕ),
    validSet (P.map (Pt.tr t₀)) k = validSet P k
  | [], k => rfl
  | p :: P, k => by
    simp only [List.map_cons, validSet, validSet_map_tr t₀ P]
    rfl

theorem psi0_loc (m : ℕ) (t₀ : ℂ) (q : Pt) (x : Fin 4) :
    psi0 (m + 1) t₀ (loc (m + 1) q x) = loc m (q.tr t₀) x := by
  fin_cases x <;> simp [loc, Pt.tr, psi0_ev, psi0_evd] <;> ring

theorem psi0_F (m : ℕ) (t₀ : ℂ) : ∀ (P : List Pt) (g : List (Fin 4)), g.length = P.length →
    psi0 (m + 1) t₀ (F (m + 1) P g) = F m (P.map (Pt.tr t₀)) g
  | [], [], _ => by simp [F]
  | p :: P, x :: g, h => by
    simp only [F_cons, map_mul, psi0_loc, List.map_cons]
    rw [psi0_F m t₀ P g (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem length_of_mem_validSet : ∀ (P : List Pt) (k : ℕ) (g : List (Fin 4)),
    g ∈ validSet P k → g.length = P.length
  | [], k, g, h => by
    simp only [validSet] at h
    split_ifs at h
    · simp at h; simp [h]
    · simp at h
  | p :: P, k, g, h => by
    obtain ⟨x, g', rfl, _, _, hg'⟩ := (mem_validSet_cons p P k g).mp h
    simp [length_of_mem_validSet P _ g' hg']


/-! ### The relation for a cons configuration -/

/-- A multiplicity-one point. -/
def Pt.one (t β : ℂ) : Pt := { t := t, β := β, γ := 0, δ := 1, two := false }

@[simp] theorem Pt.one_two (t β : ℂ) : (Pt.one t β).two = false := rfl
@[simp] theorem Pt.one_mult (t β : ℂ) : (Pt.one t β).mult = 1 := rfl

theorem loc_zero (l : ℕ) (p : Pt) : loc l p 0 = 1 := rfl

/-- The relation of a cons configuration, split by the type at the head. -/
theorem sum_cons_expand (l : ℕ) (p : Pt) (P : List Pt) (k : ℕ) (c : List (Fin 4) → ℂ) :
    ∑ g ∈ validSet (p :: P) k, c g • F l (p :: P) g =
      ∑ g' ∈ validSet P k, c (0 :: g') • F l P g' +
      (if 1 ≤ k then ∑ g' ∈ validSet P (k - 1), c (1 :: g') • (loc l p 1 * F l P g') else 0) +
      (if p.two = true ∧ 1 ≤ k then
        ∑ g' ∈ validSet P (k - 1), c (2 :: g') • (loc l p 2 * F l P g') else 0) +
      (if p.two = true ∧ 2 ≤ k then
        ∑ g' ∈ validSet P (k - 2), c (3 :: g') • (loc l p 3 * F l P g') else 0) := by
  rw [sum_validSet_cons, Fin.sum_univ_four]
  simp only [F_cons, loc_zero, one_mul]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_
  · simp [Pt.allowed, tdeg]
  · by_cases h : 1 ≤ k
    · simp [Pt.allowed, tdeg, h]
    · simp [Pt.allowed, tdeg, h]
  · by_cases h : 1 ≤ k
    · by_cases h2 : p.two = true
      · simp [Pt.allowed, tdeg, h, h2]
      · simp [Pt.allowed, tdeg, h2]
    · simp [Pt.allowed, tdeg, h]
  · by_cases h : 2 ≤ k
    · by_cases h2 : p.two = true
      · simp [Pt.allowed, tdeg, h, h2]
      · simp [Pt.allowed, tdeg, h2]
    · simp [Pt.allowed, tdeg, h]


theorem loc_tr_self_one (m : ℕ) (p : Pt) : loc m (p.tr p.t) 1 = 0 := by
  simp [loc, Pt.tr]

theorem loc_tr_self_two (m : ℕ) (p : Pt) : loc m (p.tr p.t) 2 = C p.δ * ev m p.t := by
  simp [loc, Pt.tr]

theorem loc_tr_self_three (m : ℕ) (p : Pt) : loc m (p.tr p.t) 3 = 0 := by
  simp [loc, Pt.tr]

theorem loc_one_one (l : ℕ) (t β : ℂ) : loc l (Pt.one t β) 1 = C β * ev l t := rfl

theorem loc_three (l : ℕ) (p : Pt) : loc l p 3 = (C p.β * ev l p.t) * (C p.β * ev l p.t) := by
  simp only [loc, Matrix.cons_val]
  rw [map_pow]; ring

/-- The substitution applied to a relation sum over a fixed valid set. -/
theorem psi0_sum_valid (m : ℕ) (t₀ : ℂ) (P : List Pt) (j : ℕ) (d : List (Fin 4) → ℂ)
    (A : UPoly) :
    psi0 (m + 1) t₀ (∑ g' ∈ validSet P j, d g' • (A * F (m + 1) P g')) =
      ∑ g' ∈ validSet P j, d g' • (psi0 (m + 1) t₀ A * F m (P.map (Pt.tr t₀)) g') := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro g' hg'
  rw [map_smul, map_mul, psi0_F m t₀ P g' (length_of_mem_validSet P j g' hg')]

theorem good_tail {p : Pt} {P : List Pt} (h : Good (p :: P)) : Good P :=
  ⟨(List.pairwise_cons.mp h.1).2, fun q hq => h.2 q (List.mem_cons_of_mem _ hq)⟩

theorem good_map_tr {p : Pt} {P : List Pt} (h : Good (p :: P)) :
    Good (P.map (Pt.tr p.t)) := by
  obtain ⟨h1, h2⟩ := h
  rw [List.pairwise_cons] at h1
  refine ⟨?_, ?_⟩
  · rw [List.pairwise_map]
    exact h1.2.imp (fun hab => hab)
  · intro q hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    have hne : q'.t - p.t ≠ 0 := sub_ne_zero.mpr (fun h => h1.1 q' hq' h.symm)
    have hb := h2 q' (List.mem_cons_of_mem _ hq')
    exact ⟨mul_ne_zero hb.1 hne, mul_ne_zero hb.2 hne⟩

theorem good_one_map_tr {p : Pt} {P : List Pt} (h : Good (p :: P)) (b : ℂ) (hb : b ≠ 0) :
    Good (Pt.one p.t b :: P.map (Pt.tr p.t)) := by
  have hm := good_map_tr h
  obtain ⟨h1, h2⟩ := h
  rw [List.pairwise_cons] at h1
  refine ⟨List.pairwise_cons.mpr ⟨?_, hm.1⟩, ?_⟩
  · intro q hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    exact h1.1 q' hq'
  · intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨hb, one_ne_zero⟩
    · exact hm.2 q hq

theorem good_one {p : Pt} {P : List Pt} (h : Good (p :: P)) :
    Good (Pt.one p.t p.β :: P) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [List.pairwise_cons] at h1 ⊢
    exact ⟨fun q hq => h1.1 q hq, h1.2⟩
  · intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨(h2 p (List.mem_cons_self)).1, one_ne_zero⟩
    · exact h2 q (List.mem_cons_of_mem _ hq)


theorem totalMult_map_tr (t₀ : ℂ) : ∀ P : List Pt, totalMult (P.map (Pt.tr t₀)) = totalMult P
  | [] => rfl
  | p :: P => by
    simp only [List.map_cons, totalMult_cons, totalMult_map_tr t₀ P]
    rfl

theorem one_le_mult (p : Pt) : 1 ≤ p.mult := by unfold Pt.mult; split_ifs <;> omega

theorem mult_of_two {p : Pt} (h : p.two = true) : p.mult = 2 := by simp [Pt.mult, h]
theorem mult_of_not_two {p : Pt} (h : ¬ p.two = true) : p.mult = 1 := by simp [Pt.mult, h]

theorem sum_smul_mul_left (S : Finset (List (Fin 4))) (d : List (Fin 4) → ℂ)
    (A : UPoly) (G : List (Fin 4) → UPoly) :
    ∑ g ∈ S, d g • (A * G g) = A * ∑ g ∈ S, d g • G g := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [mul_smul_comm]

/-- The coefficient function of the head-reduced relation. -/
def recoef (c : List (Fin 4) → ℂ) (a b : Fin 4) : List (Fin 4) → ℂ
  | x :: g => if x = 0 then c (a :: g) else if x = 1 then c (b :: g) else 0
  | [] => 0

@[simp] theorem recoef_zero (c : List (Fin 4) → ℂ) (a b : Fin 4) (g : List (Fin 4)) :
    recoef c a b (0 :: g) = c (a :: g) := by simp [recoef]

@[simp] theorem recoef_one (c : List (Fin 4) → ℂ) (a b : Fin 4) (g : List (Fin 4)) :
    recoef c a b (1 :: g) = c (b :: g) := by simp [recoef]

/-- **Local independence**: for an admissible configuration of total multiplicity `n`, the
products of local forms of total degree `k` are linearly independent on polynomials of degree
`≤ n - k`. -/
theorem local_indep : ∀ (n : ℕ) (P : List Pt), totalMult P = n → Good P →
    ∀ (k : ℕ) (c : List (Fin 4) → ℂ),
      ∑ g ∈ validSet P k, c g • F (n - k) P g = 0 → ∀ g ∈ validSet P k, c g = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hn hP k c hrel g hg
  match P, hn, hP, hrel, hg with
  | [], hn, hP, hrel, hg =>
    simp only [validSet] at hg hrel
    split_ifs at hg hrel with hk
    · rw [Finset.mem_singleton] at hg
      subst hg
      simpa [F] using hrel
    · simp at hg
  | p :: P, hn, hP, hrel, hg =>
    simp only [totalMult_cons] at hn
    rw [sum_cons_expand] at hrel
    have hm1 := one_le_mult p
    have hβ : p.β ≠ 0 := (hP.2 p List.mem_cons_self).1
    have hδ : p.δ ≠ 0 := (hP.2 p List.mem_cons_self).2
    -- Step 1: the types not vanishing at the head point.
    have step1 : (∀ g' ∈ validSet P k, c (0 :: g') = 0) ∧
        (p.two = true → 1 ≤ k → ∀ g' ∈ validSet P (k - 1), c (2 :: g') = 0) := by
      by_cases hl : n - k = 0
      · refine ⟨fun g' hg' => ?_, fun h2 hk g' hg' => ?_⟩
        · have := le_of_mem_validSet P k g' hg'
          omega
        · have := le_of_mem_validSet P _ g' hg'
          have := mult_of_two h2
          omega
      · obtain ⟨m, hm⟩ : ∃ m, n - k = m + 1 := ⟨n - k - 1, by omega⟩
        have hψ := congrArg (psi0 (m + 1) p.t) hrel
        rw [hm] at hψ
        simp only [map_add, map_zero, apply_ite (psi0 (m + 1) p.t)] at hψ
        have e0 : psi0 (m + 1) p.t (∑ g' ∈ validSet P k, c (0 :: g') • F (m + 1) P g') =
            ∑ g' ∈ validSet P k, c (0 :: g') • F m (P.map (Pt.tr p.t)) g' := by
          have := psi0_sum_valid m p.t P k (fun g' => c (0 :: g')) 1
          simpa only [one_mul, map_one] using this
        rw [e0, psi0_sum_valid, psi0_sum_valid, psi0_sum_valid, psi0_loc, psi0_loc, psi0_loc,
          loc_tr_self_one, loc_tr_self_three, loc_tr_self_two] at hψ
        simp only [zero_mul, smul_zero, Finset.sum_const_zero, ite_self, add_zero] at hψ
        by_cases h2 : p.two = true
        · -- reduce to the multiplicity-one head point `(p.t, δ)`
          have hQ := good_one_map_tr hP p.δ hδ
          have hmult : totalMult (Pt.one p.t p.δ :: P.map (Pt.tr p.t)) = n - 1 := by
            rw [totalMult_cons, totalMult_map_tr, Pt.one_mult, ← hn, mult_of_two h2]; omega
          have hrel' : ∑ g ∈ validSet (Pt.one p.t p.δ :: P.map (Pt.tr p.t)) k,
              recoef c 0 2 g • F (n - 1 - k) (Pt.one p.t p.δ :: P.map (Pt.tr p.t)) g = 0 := by
            rw [sum_cons_expand, show n - 1 - k = m by omega]
            simp only [recoef_zero, recoef_one, Pt.one_two, Bool.false_eq_true, false_and,
              if_false, add_zero, validSet_map_tr, loc_one_one]
            simpa only [h2, true_and] using hψ
          have hc := ih (n - 1) (by omega) _ hmult hQ k _ hrel'
          refine ⟨fun g' hg' => ?_, fun _ hk g' hg' => ?_⟩
          · have := hc (0 :: g') ((mem_validSet_cons _ _ _ _).mpr ⟨0, g', rfl, Or.inr (by simp),
              by simp [tdeg], by simpa [tdeg, validSet_map_tr] using hg'⟩)
            simpa using this
          · have := hc (1 :: g') ((mem_validSet_cons _ _ _ _).mpr ⟨1, g', rfl, Or.inr (by simp),
              by simpa [tdeg] using hk, by simpa [tdeg, validSet_map_tr] using hg'⟩)
            simpa using this
        · have hmult : totalMult (P.map (Pt.tr p.t)) = n - 1 := by
            rw [totalMult_map_tr, ← hn, mult_of_not_two h2]; omega
          have hrel' : ∑ g ∈ validSet (P.map (Pt.tr p.t)) k,
              (fun g' => c (0 :: g')) g • F (n - 1 - k) (P.map (Pt.tr p.t)) g = 0 := by
            rw [show n - 1 - k = m by omega, validSet_map_tr]
            simpa only [h2, Bool.false_eq_true, false_and, if_false, add_zero] using hψ
          have hc := ih (n - 1) (by omega) _ hmult (good_map_tr hP) k _ hrel'
          refine ⟨fun g' hg' => ?_, fun h => absurd h h2⟩
          exact hc g' (by rwa [validSet_map_tr])
    obtain ⟨hA0, hA2⟩ := step1
    -- Step 2: the types vanishing at the head point are divisible by `ev(t_p)`.
    set E : UPoly := C p.β * ev (n - k) p.t with hE
    have hEne : E ≠ 0 := mul_ne_zero (by simpa using hβ) (ev_ne_zero _ _)
    have h0 : ∑ g' ∈ validSet P k, c (0 :: g') • F (n - k) P g' = 0 :=
      Finset.sum_eq_zero fun g' hg' => by rw [hA0 g' hg', zero_smul]
    have h2' : (if p.two = true ∧ 1 ≤ k then
        ∑ g' ∈ validSet P (k - 1), c (2 :: g') • (loc (n - k) p 2 * F (n - k) P g')
        else 0) = 0 := by
      split_ifs with h
      · exact Finset.sum_eq_zero fun g' hg' => by rw [hA2 h.1 h.2 g' hg', zero_smul]
      · rfl
    rw [h0, h2', zero_add, add_zero] at hrel
    have step2 : 1 ≤ k → (∀ g' ∈ validSet P (k - 1), c (1 :: g') = 0) ∧
        (p.two = true → 2 ≤ k → ∀ g' ∈ validSet P (k - 2), c (3 :: g') = 0) := by
      intro hk
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hloc1 : loc (n - (k' + 1)) p 1 = E := rfl
      rw [if_pos hk, hloc1, loc_three, ← hE, sum_smul_mul_left] at hrel
      simp only [mul_assoc] at hrel
      have hS : ∑ g' ∈ validSet P (k' + 1 - 1), c (1 :: g') • F (n - (k' + 1)) P g' +
          (if p.two = true ∧ 2 ≤ k' + 1 then
            ∑ g' ∈ validSet P (k' + 1 - 2), c (3 :: g') • (E * F (n - (k' + 1)) P g')
            else 0) = 0 := by
        have : E * (∑ g' ∈ validSet P (k' + 1 - 1), c (1 :: g') • F (n - (k' + 1)) P g' +
            (if p.two = true ∧ 2 ≤ k' + 1 then
              ∑ g' ∈ validSet P (k' + 1 - 2), c (3 :: g') • (E * F (n - (k' + 1)) P g')
              else 0)) = 0 := by
          rw [mul_add, mul_ite, mul_zero]
          refine Eq.trans ?_ hrel
          congr 1
          split_ifs
          · exact (sum_smul_mul_left _ _ E _).symm
          · rfl
        exact (mul_eq_zero.mp this).resolve_left hEne
      simp only [Nat.add_sub_cancel] at hS
      by_cases h2 : p.two = true
      · have hQ := good_one hP
        have hmult : totalMult (Pt.one p.t p.β :: P) = n - 1 := by
          rw [totalMult_cons, Pt.one_mult, ← hn, mult_of_two h2]; omega
        have hrel' : ∑ g ∈ validSet (Pt.one p.t p.β :: P) k',
            recoef c 1 3 g • F (n - 1 - k') (Pt.one p.t p.β :: P) g = 0 := by
          rw [sum_cons_expand, show n - 1 - k' = n - (k' + 1) by omega]
          simp only [recoef_zero, recoef_one, Pt.one_two, Bool.false_eq_true, false_and,
            if_false, add_zero, loc_one_one]
          rw [← hE]
          simpa only [h2, true_and, show (2 ≤ k' + 1) = (1 ≤ k') from propext (by omega),
            show k' + 1 - 2 = k' - 1 by omega] using hS
        have hc := ih (n - 1) (by omega) _ hmult hQ k' _ hrel'
        refine ⟨fun g' hg' => ?_, fun _ hk2 g' hg' => ?_⟩
        · have := hc (0 :: g') ((mem_validSet_cons _ _ _ _).mpr ⟨0, g', rfl, Or.inr (by simp),
            by simp [tdeg], by simpa [tdeg] using hg'⟩)
          simpa using this
        · have := hc (1 :: g') ((mem_validSet_cons _ _ _ _).mpr ⟨1, g', rfl, Or.inr (by simp),
            by simp [tdeg]; omega, by simpa [tdeg, show k' + 1 - 2 = k' - 1 by omega] using hg'⟩)
          simpa using this
      · have hmult : totalMult P = n - 1 := by rw [← hn, mult_of_not_two h2]; omega
        have hrel' : ∑ g ∈ validSet P k', (fun g' => c (1 :: g')) g •
            F (n - 1 - k') P g = 0 := by
          rw [show n - 1 - k' = n - (k' + 1) by omega]
          simpa only [h2, Bool.false_eq_true, false_and, if_false, add_zero] using hS
        have hc := ih (n - 1) (by omega) _ hmult (good_tail hP) k' _ hrel'
        exact ⟨fun g' hg' => hc g' (by simpa using hg'), fun h => absurd h h2⟩
    -- Conclusion.
    obtain ⟨x, g', rfl, hxa, hxk, hg'⟩ := (mem_validSet_cons p P k g).mp hg
    fin_cases x
    · simpa [tdeg] using hA0 g' (by simpa [tdeg] using hg')
    · have hk : 1 ≤ k := by simpa [tdeg] using hxk
      exact (step2 hk).1 g' (by simpa [tdeg] using hg')
    · have h2 : p.two = true := by
        rcases hxa with h | h
        · exact h
        · simp at h
      have hk : 1 ≤ k := by simpa [tdeg] using hxk
      exact hA2 h2 hk g' (by simpa [tdeg] using hg')
    · have h2 : p.two = true := by
        rcases hxa with h | h
        · exact h
        · simp at h
      have hk : 2 ≤ k := by simpa [tdeg] using hxk
      exact (step2 (by omega)).2 h2 hk g' (by simpa [tdeg] using hg')


end

end VOA.JetProduct
