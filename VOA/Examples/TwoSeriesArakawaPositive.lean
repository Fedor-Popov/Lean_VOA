/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesArakawaEndpoint

/-!
# Positive Virasoro modes on the Whittaker slice

The slice map `W₁ = ψ ∘ W₀ : V^k(sl₂) → Vir^c` intertwines the creation Sugawara modes with the
creation Virasoro modes.  Here we find **lifts of the annihilation modes** `L₀, L₁, L₂`: explicit
operators in the (current) enveloping algebra,

* `Q₀ = L₀ + ½ h₀`,
* `Q₁ = L₁ + h₁ + k f₀ + ½ f₀ h₀`,
* `Q₂ = L₂ + 3/2 h₂ + 3k f₁ + 7k/4 f₀² + ½ f₀ h₁ + f₁ h₀ + ½ f₀² h₀`

(`L_n` the Sugawara modes), with

  `W₁ ∘ Q_i = L_i ∘ W₁`   (`i = 0, 1, 2`),

where for `i = 2` the Virasoro central charge must be the Drinfeld–Sokolov value
`c = cDS k = 1 - 6 (k+1)² / (k+2)`.  (For `i = 0, 1` any `c` works.)

The proof has two halves.

* **Normalisation** (`Q0_whitIdeal`, `Q1_whitIdeal`, `Q2_whitIdeal`): each `Q_i` maps the Whittaker
  ideal `Σ (x - χ(x)) V` into itself.  The correction terms are exactly what is needed: e.g.
  `[Q₁, f_{-1} + 1] = -(f_{-1} + 1) f₀` and `[Q₁, h_{-1}] = (f_{-1} + 1)(h₀ + 2k)`.
* **Sugawara words** (`W1_Q*_sugWord`): on `L_{-n₁-2} ⋯ L_{-n_b-2} |0⟩` the identity follows by
  induction from the commutators `[Q_i, L_{-N}] ≡ (i+N) Q_{i-N}` modulo the Whittaker ideal; for
  `(i, N) = (2, 2)` the Sugawara central term `c_sug / 2 = 3k / (2(k+2))` and the corrections
  combine to `c_DS / 2` (`cSug_sub_cDS`).

Since Sugawara words and the Whittaker ideal together span `V^k`, the identities hold everywhere
(`W1_Q0`, `W1_Q1`, `W1_Q2`).

Everything here is proved; no new axiom.
-/

namespace VOA.TwoSeries.SliceMap

open VOA.AffineVOA VOA.AffineVOA.SugawaraCov VOA.AffineVOA.Strong MvPolynomial
open VOA.VirModule VOA.TwoSeries.DSSlice VOA.VirSimple VOA.LeeYangCharacter
open scoped BigOperators

noncomputable section

variable (c k : ℂ) (hk : k + 2 ≠ 0)

/-- The Drinfeld–Sokolov central charge `1 - 6 (k+1)² / (k+2)`. -/
def cDS (k : ℂ) : ℂ := 1 - 6 * (k + 1) ^ 2 / (k + 2)

/-! ## §1  Rules for the ungraded slice map -/

theorem W1_fOne (y : WakModule k) : W1 c k hk (J k 1 (-1) y) = -W1 c k hk y := by
  simp only [W1, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [W0_J_fOne, map_neg]

theorem W1_f_le {μ : ℤ} (hμ : μ ≤ -2) (y : WakModule k) : W1 c k hk (J k 1 μ y) = 0 := by
  simp only [W1, LinearMap.comp_apply, LinearEquiv.coe_coe]
  have h := W0_J_fHigh k hk (-μ - 2).toNat y
  rw [show -(((-μ - 2).toNat : ℕ) : ℤ) - 2 = μ by omega] at h
  rw [h, map_zero]

theorem W1_h_le {μ : ℤ} (hμ : μ ≤ -1) (y : WakModule k) : W1 c k hk (J k 2 μ y) = 0 := by
  have h := W1_h c k hk (-μ - 1).toNat y
  rwa [show -(((-μ - 1).toNat : ℕ) : ℤ) - 1 = μ by omega] at h

theorem W1_whit {y : WakModule k} (hy : y ∈ whitIdeal k) : W1 c k hk y = 0 := by
  simp only [W1, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [W0_whitIdeal k hk hy, map_zero]

theorem W1_vac : W1 c k hk (vacuumA k) = vacVec c := by
  simp only [W1, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [W0_vacuum, psi_one]

theorem whit_f_le {μ : ℤ} (hμ : μ ≤ -2) (v : WakModule k) : J k 1 μ v ∈ whitIdeal k := by
  have h := fHigh_mem k (-μ - 2).toNat v
  rwa [show -(((-μ - 2).toNat : ℕ) : ℤ) - 2 = μ by omega] at h

theorem whit_h_le {μ : ℤ} (hμ : μ ≤ -1) (v : WakModule k) : J k 2 μ v ∈ whitIdeal k := by
  have h := h_mem k (-μ - 1).toNat v
  rwa [show -(((-μ - 1).toNat : ℕ) : ℤ) - 1 = μ by omega] at h

/-! ## §2  More current commutators -/

/-- `[h_μ, h_ν] = 2 μ k δ_{μ+ν,0}`. -/
theorem h_h_comm (μ ν : ℤ) (y : WakModule k) :
    J k 2 μ (J k 2 ν y) = J k 2 ν (J k 2 μ y) +
      (if μ + ν = 0 then ((μ : ℂ) * k * 2) • y else 0) := by
  rw [J_comm_apply, Fin.sum_univ_three]
  split_ifs <;> simp [fabc, kappa]

/-- Commuting a current mode past a Sugawara mode: `J_ν L_n = L_n J_ν + ν J_{n+ν}`. -/
theorem J_Lm (n : ℤ) (a : Fin 3) (ν : ℤ) (y : WakModule k) :
    J k a ν (Lm k hk n y) = Lm k hk n (J k a ν y) + (ν : ℂ) • J k a (n + ν) y := by
  rw [Lm_J]
  push_cast
  module

/-! ## §3  The lifts -/

/-- `Q₀ = L₀ + ½ h₀`. -/
def Q0 (y : WakModule k) : WakModule k := Lm k hk 0 y + (1 / 2 : ℂ) • J k 2 0 y

/-- `Q₁ = L₁ + h₁ + k f₀ + ½ f₀ h₀`. -/
def Q1 (y : WakModule k) : WakModule k :=
  Lm k hk 1 y + J k 2 1 y + k • J k 1 0 y + (1 / 2 : ℂ) • J k 1 0 (J k 2 0 y)

/-- `Q₂ = L₂ + 3/2 h₂ + 3k f₁ + 7k/4 f₀² + ½ f₀ h₁ + f₁ h₀ + ½ f₀² h₀`. -/
def Q2 (y : WakModule k) : WakModule k :=
  Lm k hk 2 y + (3 / 2 : ℂ) • J k 2 2 y + (3 * k) • J k 1 1 y +
    (7 * k / 4) • J k 1 0 (J k 1 0 y) + (1 / 2 : ℂ) • J k 1 0 (J k 2 1 y) +
    J k 1 1 (J k 2 0 y) + (1 / 2 : ℂ) • J k 1 0 (J k 1 0 (J k 2 0 y))

theorem Q0_add (x y : WakModule k) : Q0 k hk (x + y) = Q0 k hk x + Q0 k hk y := by
  simp only [Q0, map_add]; module

theorem Q0_smul (r : ℂ) (x : WakModule k) : Q0 k hk (r • x) = r • Q0 k hk x := by
  simp only [Q0, map_smul]; module

theorem Q1_add (x y : WakModule k) : Q1 k hk (x + y) = Q1 k hk x + Q1 k hk y := by
  simp only [Q1, map_add]; module

theorem Q1_smul (r : ℂ) (x : WakModule k) : Q1 k hk (r • x) = r • Q1 k hk x := by
  simp only [Q1, map_smul]; module

theorem Q2_add (x y : WakModule k) : Q2 k hk (x + y) = Q2 k hk x + Q2 k hk y := by
  simp only [Q2, map_add]; module

theorem Q2_smul (r : ℂ) (x : WakModule k) : Q2 k hk (r • x) = r • Q2 k hk x := by
  simp only [Q2, map_smul]; module

/-- The lifts as linear maps. -/
def Q0L : WakModule k →ₗ[ℂ] WakModule k where
  toFun := Q0 k hk
  map_add' := Q0_add k hk
  map_smul' := Q0_smul k hk

def Q1L : WakModule k →ₗ[ℂ] WakModule k where
  toFun := Q1 k hk
  map_add' := Q1_add k hk
  map_smul' := Q1_smul k hk

def Q2L : WakModule k →ₗ[ℂ] WakModule k where
  toFun := Q2 k hk
  map_add' := Q2_add k hk
  map_smul' := Q2_smul k hk

/-! ## §4  Commutators with `f`- and `h`-modes -/

theorem Q0_f (μ : ℤ) (v : WakModule k) :
    Q0 k hk (J k 1 μ v) = J k 1 μ (Q0 k hk v) + (-(μ : ℂ) - 1) • J k 1 μ v := by
  simp only [Q0, map_add, map_smul]
  rw [Lm_J, h_f_comm]
  push_cast
  simp only [zero_add]
  module

theorem Q0_h (μ : ℤ) (v : WakModule k) :
    Q0 k hk (J k 2 μ v) = J k 2 μ (Q0 k hk v) + (-(μ : ℂ)) • J k 2 μ v := by
  simp only [Q0, map_add, map_smul]
  rw [Lm_J, h0_h_comm]
  push_cast
  simp only [zero_add]
  module

theorem Q1_f (μ : ℤ) (v : WakModule k) :
    Q1 k hk (J k 1 μ v) = J k 1 μ (Q1 k hk v) + (-(μ : ℂ) - 2) • J k 1 (1 + μ) v -
      J k 1 μ (J k 1 0 v) := by
  simp only [Q1, map_add, map_smul]
  rw [Lm_J, h_f_comm, f_f_comm, h_f_comm k 0, map_add, map_smul, f_f_comm k 0 μ (J k 2 0 v),
    f_f_comm k 0 (0 + μ)]
  push_cast
  simp only [zero_add]
  module

theorem Q1_h (μ : ℤ) (v : WakModule k) :
    Q1 k hk (J k 2 μ v) = J k 2 μ (Q1 k hk v) + (-(μ : ℂ)) • J k 2 (1 + μ) v +
      (if 1 + μ = 0 then (2 * k) • v else 0) + (2 * k) • J k 1 μ v + J k 1 μ (J k 2 0 v) := by
  simp only [Q1, map_add, map_smul]
  rw [Lm_J, h_h_comm, f_h_comm, h0_h_comm, f_h_comm k 0 μ (J k 2 0 v)]
  push_cast
  simp only [zero_add]
  split_ifs <;> module

theorem Q2_f (μ : ℤ) (v : WakModule k) :
    Q2 k hk (J k 1 μ v) = J k 1 μ (Q2 k hk v) + (-(μ : ℂ) - 3) • J k 1 (2 + μ) v -
      J k 1 (1 + μ) (J k 1 0 v) - (2 : ℂ) • J k 1 μ (J k 1 1 v) -
      J k 1 μ (J k 1 0 (J k 1 0 v)) := by
  have ff0 : ∀ x, J k 1 0 (J k 1 μ x) = J k 1 μ (J k 1 0 x) := fun x => f_f_comm k 0 μ x
  have a1 : Lm k hk 2 (J k 1 μ v) = J k 1 μ (Lm k hk 2 v) + ((-μ : ℤ) : ℂ) • J k 1 (2 + μ) v :=
    Lm_J k hk 2 1 μ v
  have a2 := h_f_comm k 2 μ v
  have a3 := f_f_comm k 1 μ v
  have a4 : J k 1 0 (J k 1 0 (J k 1 μ v)) = J k 1 μ (J k 1 0 (J k 1 0 v)) := by
    rw [ff0, ff0]
  have a5 : J k 1 0 (J k 2 1 (J k 1 μ v)) =
      J k 1 μ (J k 1 0 (J k 2 1 v)) + (-2 : ℂ) • J k 1 (1 + μ) (J k 1 0 v) := by
    rw [h_f_comm k 1 μ v, map_add, map_smul, ff0, f_f_comm k 0 (1 + μ)]
  have a6 : J k 1 1 (J k 2 0 (J k 1 μ v)) =
      J k 1 μ (J k 1 1 (J k 2 0 v)) + (-2 : ℂ) • J k 1 μ (J k 1 1 v) := by
    rw [h_f_comm k 0 μ v, map_add, map_smul, f_f_comm k 1 μ, zero_add, f_f_comm k 1 μ]
  have a7 : J k 1 0 (J k 1 0 (J k 2 0 (J k 1 μ v))) =
      J k 1 μ (J k 1 0 (J k 1 0 (J k 2 0 v))) + (-2 : ℂ) • J k 1 μ (J k 1 0 (J k 1 0 v)) := by
    rw [h_f_comm k 0 μ v, zero_add]
    simp only [map_add, map_smul, ff0]
  simp only [Q2]
  rw [a1, a2, a3, a4, a5, a6, a7]
  simp only [map_add, map_smul]
  push_cast
  module

theorem Q2_h (μ : ℤ) (v : WakModule k) :
    Q2 k hk (J k 2 μ v) = J k 2 μ (Q2 k hk v) + (-(μ : ℂ)) • J k 2 (2 + μ) v +
      (if 2 + μ = 0 then (6 * k) • v else 0) + (6 * k) • J k 1 (1 + μ) v +
      (7 * k) • J k 1 μ (J k 1 0 v) + J k 1 μ (J k 2 1 v) +
      (if 1 + μ = 0 then k • J k 1 0 v else 0) + (2 : ℂ) • J k 1 (1 + μ) (J k 2 0 v) +
      (2 : ℂ) • J k 1 μ (J k 1 0 (J k 2 0 v)) := by
  have fh0 : ∀ x, J k 1 0 (J k 2 μ x) = J k 2 μ (J k 1 0 x) + (2 : ℂ) • J k 1 μ x := by
    intro x; rw [f_h_comm, zero_add]
  have ff0 : ∀ x, J k 1 0 (J k 1 μ x) = J k 1 μ (J k 1 0 x) := fun x => f_f_comm k 0 μ x
  have a1 : Lm k hk 2 (J k 2 μ v) = J k 2 μ (Lm k hk 2 v) + ((-μ : ℤ) : ℂ) • J k 2 (2 + μ) v :=
    Lm_J k hk 2 2 μ v
  have a2 : J k 2 2 (J k 2 μ v) = J k 2 μ (J k 2 2 v) +
      (if 2 + μ = 0 then ((4 * k : ℂ)) • v else 0) := by
    rw [h_h_comm]; split_ifs <;> simp; ring_nf
  have a3 := f_h_comm k 1 μ v
  have a4 : J k 1 0 (J k 1 0 (J k 2 μ v)) = J k 2 μ (J k 1 0 (J k 1 0 v)) +
      (4 : ℂ) • J k 1 μ (J k 1 0 v) := by
    rw [fh0, map_add, map_smul, fh0, ff0]; module
  have a5 : J k 1 0 (J k 2 1 (J k 2 μ v)) = J k 2 μ (J k 1 0 (J k 2 1 v)) +
      (2 : ℂ) • J k 1 μ (J k 2 1 v) + (if 1 + μ = 0 then (2 * k) • J k 1 0 v else 0) := by
    rw [h_h_comm k 1 μ v, map_add, fh0]
    split_ifs
    · rw [map_smul]; module
    · rw [map_zero, add_zero]
  have a6 : J k 1 1 (J k 2 0 (J k 2 μ v)) = J k 2 μ (J k 1 1 (J k 2 0 v)) +
      (2 : ℂ) • J k 1 (1 + μ) (J k 2 0 v) := by
    rw [h0_h_comm, f_h_comm]
  have a7 : J k 1 0 (J k 1 0 (J k 2 0 (J k 2 μ v))) = J k 2 μ (J k 1 0 (J k 1 0 (J k 2 0 v))) +
      (4 : ℂ) • J k 1 μ (J k 1 0 (J k 2 0 v)) := by
    rw [h0_h_comm, fh0, map_add, map_smul, fh0, ff0]; module
  simp only [Q2]
  rw [a1, a2, a3, a4, a5, a6, a7]
  simp only [map_add, map_smul]
  push_cast
  split_ifs <;> module

/-! ## §5  The lifts normalise the Whittaker ideal -/

theorem Q0_whitIdeal {y : WakModule k} (hy : y ∈ whitIdeal k) : Q0 k hk y ∈ whitIdeal k := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
      rcases hx with (⟨v, rfl⟩ | ⟨d, v, rfl⟩) | ⟨d, v, rfl⟩
      · rw [Q0_add, Q0_f]
        have h := fOne_mem k (Q0 k hk v)
        convert h using 1
        push_cast; module
      · rw [Q0_f]
        exact Submodule.add_mem _ (fHigh_mem k _ _) (Submodule.smul_mem _ _ (fHigh_mem k _ _))
      · rw [Q0_h]
        exact Submodule.add_mem _ (h_mem k _ _) (Submodule.smul_mem _ _ (h_mem k _ _))
  | zero => simp only [Q0, map_zero, smul_zero, add_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Q0_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Q0_smul]; exact Submodule.smul_mem _ _ hx

theorem Q1_whitIdeal {y : WakModule k} (hy : y ∈ whitIdeal k) : Q1 k hk y ∈ whitIdeal k := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
      rcases hx with (⟨v, rfl⟩ | ⟨d, v, rfl⟩) | ⟨d, v, rfl⟩
      · rw [Q1_add, Q1_f]
        have h := Submodule.sub_mem _ (fOne_mem k (Q1 k hk v)) (fOne_mem k (J k 1 0 v))
        convert h using 1
        rw [show (1 : ℤ) + -1 = 0 by norm_num]
        push_cast; module
      · rw [Q1_f]
        refine Submodule.sub_mem _ (Submodule.add_mem _ (fHigh_mem k _ _) ?_) (fHigh_mem k _ _)
        rcases d with _ | d
        · simp
        · exact Submodule.smul_mem _ _ (whit_f_le k (by push_cast; omega) v)
      · rw [Q1_h]
        rcases d with _ | d
        · rw [if_pos (by norm_num)]
          have h1 := fOne_mem k (J k 2 0 v)
          have h2 := Submodule.smul_mem _ (2 * k) (fOne_mem k v)
          have h3 := h_mem k 0 (Q1 k hk v)
          have := Submodule.add_mem _ (Submodule.add_mem _ h3 h1) h2
          convert this using 1
          rw [show (1 : ℤ) + (-((0 : ℕ) : ℤ) - 1) = 0 by norm_num,
            show (-((0 : ℕ) : ℤ) - 1) = -1 by norm_num]
          push_cast; module
        · rw [if_neg (by push_cast; omega), add_zero]
          refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (h_mem k _ _)
            (Submodule.smul_mem _ _ (whit_h_le k (by push_cast; omega) v)))
            (Submodule.smul_mem _ _ (whit_f_le k (by push_cast; omega) v)))
            (whit_f_le k (by push_cast; omega) _)
  | zero => simp only [Q1, map_zero, smul_zero, add_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Q1_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Q1_smul]; exact Submodule.smul_mem _ _ hx

theorem Q2_whitIdeal {y : WakModule k} (hy : y ∈ whitIdeal k) : Q2 k hk y ∈ whitIdeal k := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
      rcases hx with (⟨v, rfl⟩ | ⟨d, v, rfl⟩) | ⟨d, v, rfl⟩
      · rw [Q2_add, Q2_f]
        have h1 := fOne_mem k (Q2 k hk v)
        have h2 := fOne_mem k (J k 1 1 v)
        have h3 := fOne_mem k (J k 1 0 (J k 1 0 v))
        have := Submodule.sub_mem _ (Submodule.sub_mem _ h1 (Submodule.smul_mem _ (2 : ℂ) h2)) h3
        convert this using 1
        rw [show (2 : ℤ) + -1 = 1 by norm_num, show (1 : ℤ) + -1 = 0 by norm_num]
        push_cast; module
      · rw [Q2_f]
        have hf1 := fHigh_mem k d (Q2 k hk v)
        have hf2 := fHigh_mem k d (J k 1 1 v)
        have hf3 := fHigh_mem k d (J k 1 0 (J k 1 0 v))
        rcases d with _ | _ | d
        · -- `μ = -2`: the two edge terms combine to `-(f_{-1} + 1) f₀ v`
          have h4 := fOne_mem k (J k 1 0 v)
          have := Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _ hf1 h4)
            (Submodule.smul_mem _ (2 : ℂ) hf2)) hf3
          convert this using 1
          rw [show (2 : ℤ) + (-((0 : ℕ) : ℤ) - 2) = 0 by norm_num,
            show (1 : ℤ) + (-((0 : ℕ) : ℤ) - 2) = -1 by norm_num]
          push_cast; module
        · have h4 := fHigh_mem k 0 (J k 1 0 v)
          have := Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _ hf1 h4)
            (Submodule.smul_mem _ (2 : ℂ) hf2)) hf3
          convert this using 1
          rw [show (1 : ℤ) + (-((0 + 1 : ℕ) : ℤ) - 2) = -((0 : ℕ) : ℤ) - 2 by norm_num]
          push_cast; module
        · refine Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _
            (Submodule.add_mem _ hf1 (Submodule.smul_mem _ _ (whit_f_le k (by push_cast; omega) v)))
            (whit_f_le k (by push_cast; omega) _)) (Submodule.smul_mem _ _ hf2)) hf3
      · rw [Q2_h]
        have hh1 := h_mem k d (Q2 k hk v)
        rcases d with _ | _ | d
        · -- `μ = -1`
          rw [if_neg (by norm_num), if_pos (by norm_num), add_zero]
          have g1 := fOne_mem k (J k 2 1 v)
          have g2 := Submodule.smul_mem _ (7 * k) (fOne_mem k (J k 1 0 v))
          have g3 := Submodule.smul_mem _ (2 : ℂ) (fOne_mem k (J k 1 0 (J k 2 0 v)))
          have := Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ hh1 g1) g2) g3
          convert this using 1
          rw [show (1 : ℤ) + (-((0 : ℕ) : ℤ) - 1) = 0 by norm_num,
            show (2 : ℤ) + (-((0 : ℕ) : ℤ) - 1) = 1 by norm_num,
            show (-((0 : ℕ) : ℤ) - 1) = -1 by norm_num]
          push_cast; module
        · -- `μ = -2`
          rw [if_pos (by norm_num), if_neg (by norm_num), add_zero]
          have g1 := Submodule.smul_mem _ (2 : ℂ) (fOne_mem k (J k 2 0 v))
          have g2 := Submodule.smul_mem _ (6 * k) (fOne_mem k v)
          have g3 := Submodule.smul_mem _ (7 * k) (fHigh_mem k 0 (J k 1 0 v))
          have g4 := fHigh_mem k 0 (J k 2 1 v)
          have g5 := Submodule.smul_mem _ (2 : ℂ) (fHigh_mem k 0 (J k 1 0 (J k 2 0 v)))
          have := Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
            (Submodule.add_mem _ (Submodule.add_mem _ hh1 g1) g2) g3) g4) g5
          convert this using 1
          rw [show (2 : ℤ) + (-((0 + 1 : ℕ) : ℤ) - 1) = 0 by norm_num,
            show (1 : ℤ) + (-((0 + 1 : ℕ) : ℤ) - 1) = -1 by norm_num,
            show (-((0 + 1 : ℕ) : ℤ) - 1) = -((0 : ℕ) : ℤ) - 2 by norm_num]
          push_cast; module
        · rw [if_neg (by push_cast; omega), if_neg (by push_cast; omega), add_zero, add_zero]
          refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
            (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ hh1
            (Submodule.smul_mem _ _ (whit_h_le k (by push_cast; omega) v)))
            (Submodule.smul_mem _ _ (whit_f_le k (by push_cast; omega) v)))
            (Submodule.smul_mem _ _ (whit_f_le k (by push_cast; omega) _)))
            (whit_f_le k (by push_cast; omega) _))
            (Submodule.smul_mem _ _ (whit_f_le k (by push_cast; omega) _)))
            (Submodule.smul_mem _ _ (whit_f_le k (by push_cast; omega) _))
  | zero => simp only [Q2, map_zero, smul_zero, add_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Q2_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Q2_smul]; exact Submodule.smul_mem _ _ hx

end

end VOA.TwoSeries.SliceMap
