/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.PlusC2Degree

/-!
# The excess filtration of a lattice VOA

For a Fock monomial `x^s` (`x_{(i,a)} = h_a(−i−1)`) put `wt s = Σ (i+1)·s(i,a)` (conformal weight)
and `deg s = Σ s(i,a)` (polynomial degree), and call `wt s − deg s ≥ 0` its **excess**.  The excess
is `0` exactly for the monomials in the `h(−1)`'s alone.  Filter `V_L` charge by charge:
`ExFil e γ = span{x^s ⊗ e^γ : wt s − deg s ≥ e}`.

## Main results

* `oscN_mem_ExF` — the oscillator `h_a(n)` lowers the excess by at most `n + 1`.
* `word_smul_mem_ExFil` — for a creation word `u = h(−k₁−1)⋯h(−k_r−1)𝟙` (charge `0`) of weight
  `w` and length `r`, the mode `u₍N₎` maps `ExFil e γ` into `ExFil (e + (w − r) − N − 1) γ`.
  In particular **every `u₍N₎v` with `N ≤ −2` has excess `≥ 1`** (`word_smul_le_neg_two_mem_ExFil`),
  i.e. has no component along `h(−1)^w`.
-/

set_option linter.style.longLine false

namespace VOA.Classification.COne

open VOA VOA.LatGen VOA.IntegralLattice HeisenbergN MvPolynomial

namespace PlusC2

variable (L : IntegralLattice) (hEven : L.Even) (hPos : L.PosDef)

/-! ## §1  Weight, degree, excess of a monomial -/

/-- The conformal weight `Σ (i+1)·s(i,a)` of the monomial `x^s`. -/
def monoWt (s : (ℕ × Fin (rank L)) →₀ ℕ) : ℕ := s.sum fun v k => (v.1 + 1) * k

/-- The polynomial degree `Σ s(i,a)` of the monomial `x^s`. -/
def monoDeg (s : (ℕ × Fin (rank L)) →₀ ℕ) : ℕ := s.sum fun _ k => k

theorem monoWt_add (s t : (ℕ × Fin (rank L)) →₀ ℕ) : monoWt L (s + t) = monoWt L s + monoWt L t :=
  Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)

theorem monoDeg_add (s t : (ℕ × Fin (rank L)) →₀ ℕ) : monoDeg L (s + t) = monoDeg L s + monoDeg L t :=
  Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

theorem monoWt_single (v : ℕ × Fin (rank L)) (k : ℕ) : monoWt L (Finsupp.single v k) = (v.1 + 1) * k :=
  Finsupp.sum_single_index (by simp)

theorem monoDeg_single (v : ℕ × Fin (rank L)) (k : ℕ) : monoDeg L (Finsupp.single v k) = k :=
  Finsupp.sum_single_index rfl

/-- The excess filtration of the Fock space: `span{x^s : wt s − deg s ≥ e}`. -/
noncomputable def ExF (e : ℤ) : Submodule ℂ (FockN (rank L)) :=
  Submodule.span ℂ {p | ∃ s : (ℕ × Fin (rank L)) →₀ ℕ,
    e ≤ (monoWt L s : ℤ) - monoDeg L s ∧ p = monomial s 1}

/-- `ExFil e γ = ExF e ⊗ e^γ`. -/
noncomputable def ExFil (e : ℤ) (γ : L.carrier) : Submodule ℂ (LatModuleGen L) :=
  (ExF L e).map (stateMap L γ)

theorem ExF_anti {e e' : ℤ} (h : e' ≤ e) : ExF L e ≤ ExF L e' := by
  apply Submodule.span_mono
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨s, h.trans hs, rfl⟩

theorem ExFil_anti {e e' : ℤ} (h : e' ≤ e) (γ : L.carrier) : ExFil L e γ ≤ ExFil L e' γ :=
  Submodule.map_mono (ExF_anti L h)

theorem monomial_mem_ExF (s : (ℕ × Fin (rank L)) →₀ ℕ) (c : ℂ) {e : ℤ}
    (h : e ≤ (monoWt L s : ℤ) - monoDeg L s) : monomial s c ∈ ExF L e := by
  have : monomial s c = c • monomial s (1 : ℂ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, h, rfl⟩)

/-- Every Fock state has excess `≥ 0`. -/
theorem monoDeg_le_monoWt (s : (ℕ × Fin (rank L)) →₀ ℕ) : monoDeg L s ≤ monoWt L s := by
  unfold monoDeg monoWt Finsupp.sum
  exact Finset.sum_le_sum fun v _ => Nat.le_mul_of_pos_left _ (Nat.succ_pos _)

theorem ExF_zero : ExF L 0 = ⊤ := by
  refine eq_top_iff.mpr fun p _ => ?_
  rw [p.as_sum]
  refine Submodule.sum_mem _ fun s _ => monomial_mem_ExF L s _ ?_
  have := monoDeg_le_monoWt L s
  omega

/-- Multiplication by `x_{(i,a)}` raises the excess by `i`. -/
theorem X_mul_mem_ExF (v : ℕ × Fin (rank L)) {e : ℤ} {p : FockN (rank L)} (hp : p ∈ ExF L e) :
    X v * p ∈ ExF L (e + v.1) := by
  refine Submodule.span_induction (p := fun p _ => X v * p ∈ ExF L (e + v.1)) ?_ ?_ ?_ ?_ hp
  · rintro _ ⟨s, hs, rfl⟩
    rw [X, monomial_mul, one_mul]
    refine monomial_mem_ExF L _ _ ?_
    rw [monoWt_add, monoDeg_add, monoWt_single, monoDeg_single]
    push_cast
    linarith
  · simp only [mul_zero, Submodule.zero_mem]
  · intro x y _ _ hx hy; rw [mul_add]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx; rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

/-- The partial derivative `∂/∂x_{(i,a)}` lowers the excess by `i`. -/
theorem pderiv_mem_ExF (v : ℕ × Fin (rank L)) {e : ℤ} {p : FockN (rank L)} (hp : p ∈ ExF L e) :
    pderiv v p ∈ ExF L (e - v.1) := by
  refine Submodule.span_induction (p := fun p _ => pderiv v p ∈ ExF L (e - v.1)) ?_ ?_ ?_ ?_ hp
  · rintro _ ⟨s, hs, rfl⟩
    rw [pderiv_monomial]
    by_cases hsv : s v = 0
    · rw [hsv, Nat.cast_zero, mul_zero, monomial_zero]; exact Submodule.zero_mem _
    · refine monomial_mem_ExF L _ _ ?_
      have hle : Finsupp.single v 1 ≤ s := by
        intro w
        rw [Finsupp.single_apply]
        split_ifs with h
        · subst h; omega
        · exact Nat.zero_le _
      have hs' : s = (s - Finsupp.single v 1) + Finsupp.single v 1 := (tsub_add_cancel_of_le hle).symm
      have hW := congrArg (monoWt L) hs'
      have hD := congrArg (monoDeg L) hs'
      rw [monoWt_add, monoWt_single] at hW
      rw [monoDeg_add, monoDeg_single] at hD
      have hW' : (monoWt L s : ℤ) = monoWt L (s - Finsupp.single v 1) + (v.1 + 1) := by
        rw [hW]; push_cast; ring
      have hD' : (monoDeg L s : ℤ) = monoDeg L (s - Finsupp.single v 1) + 1 := by
        rw [hD]; push_cast; ring
      rw [hW', hD'] at hs
      linarith
  · simp only [map_zero, Submodule.zero_mem]
  · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx; rw [(pderiv v).map_smul]; exact Submodule.smul_mem _ _ hx

/-! ## §2  The boson modes -/

/-- The oscillator `h_a(n)` lowers the excess by at most `n + 1`. -/
theorem oscN_mem_ExF (a : Fin (rank L)) (n : ℤ) {e : ℤ} {p : FockN (rank L)} (hp : p ∈ ExF L e) :
    oscN (rank L) 1 a n p ∈ ExF L (e - n - 1) := by
  rcases lt_trichotomy n 0 with hn | hn | hn
  · rw [oscN_neg _ _ _ hn, mulXN_apply]
    have := X_mul_mem_ExF L ((-n - 1).toNat, a) hp
    refine ExF_anti L ?_ this
    simp only
    omega
  · subst hn; rw [oscN_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
  · rw [oscN_pos _ _ _ hn]
    simp only [LinearMap.smul_apply, pderivLMN_apply]
    refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
    have := pderiv_mem_ExF L ((n - 1).toNat, a) hp
    refine ExF_anti L ?_ this
    simp only
    omega

/-- The boson modes on the excess filtration: `h₍ₙ₎` lowers the excess by at most `n + 1`. -/
theorem smul_bosonState_mem_ExFil (a : Fin (rank L)) (n : ℤ) {e : ℤ} {γ : L.carrier}
    {x : LatModuleGen L} (hx : x ∈ ExFil L e γ) :
    (latticeVOAGen L hEven hPos).smul (bosonState L a) n x ∈ ExFil L (e - n - 1) γ := by
  obtain ⟨p, hp, rfl⟩ := hx
  rw [stateMap_apply, smul_bosonState_latStateGen]
  refine Submodule.add_mem _ ⟨_, oscN_mem_ExF L a n hp, rfl⟩ ?_
  by_cases h0 : n = 0
  · rw [if_pos h0]
    refine Submodule.smul_mem _ _ ⟨p, ExF_anti L (by omega) hp, rfl⟩
  · rw [if_neg h0]; exact Submodule.zero_mem _

/-! ## §3  Creation words -/

/-- The conformal weight `Σ (kᵢ + 1)` of the creation word `h(−k₁−1)⋯h(−k_r−1)𝟙`. -/
def wordWtL : List (ℕ × Fin (rank L)) → ℕ
  | [] => 0
  | (k, _) :: rest => k + 1 + wordWtL rest

/-- **Excess bound for the modes of a creation word** (charge `0`, weight `w`, length `r`):
`u₍N₎` maps `ExFil e γ` into `ExFil (e + (w − r) − N − 1) γ`. -/
theorem word_smul_mem_ExFil : ∀ (l : List (ℕ × Fin (rank L))) (N e : ℤ) (γ : L.carrier)
    (x : LatModuleGen L), x ∈ ExFil L e γ →
    (latticeVOAGen L hEven hPos).smul (wordStateLatGen L l 0) N x ∈
      ExFil L (e + ((wordWtL L l : ℤ) - l.length) - N - 1) γ
  | [], N, e, γ, x, hx => by
    rw [word_nil L hEven hPos, PreVertexAlgebra.smul_vacuum_left]
    split_ifs with hN
    · refine ExFil_anti L ?_ γ hx
      simp [wordWtL]; omega
    · exact Submodule.zero_mem _
  | (k, a) :: rest, N, e, γ, x, hx => by
    set W := latticeVOAGen L hEven hPos
    set H := bosonState L a
    set u' := wordStateLatGen L rest 0
    have IH := fun N' e' x' (hx' : x' ∈ ExFil L e' γ) => word_smul_mem_ExFil rest N' e' γ x' hx'
    rw [word_cons L hEven hPos, VertexOperatorAlgebra.mode_iterate W H u' (-(k : ℤ) - 1) N x]
    have hlen : (((k, a) :: rest).length : ℤ) = rest.length + 1 := by simp
    have hwt : (wordWtL L ((k, a) :: rest) : ℤ) = k + 1 + wordWtL L rest := by
      simp [wordWtL]
    refine finsum_mem_submodule_pd _ _ fun i => Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
    · have h1 := IH (N + i) e x hx
      have h2 := smul_bosonState_mem_ExFil L hEven hPos a (-(k : ℤ) - 1 - i) h1
      refine ExFil_anti L ?_ γ h2
      rw [hlen, hwt]; omega
    · refine Submodule.smul_mem _ _ ?_
      have h0 := smul_bosonState_mem_ExFil L hEven hPos a (i : ℤ) hx
      have h1 := IH (-(k : ℤ) - 1 + N - i) _ _ h0
      refine ExFil_anti L ?_ γ h1
      rw [hlen, hwt]; omega

/-- A creation word has weight at least its length. -/
theorem length_le_wordWt : ∀ l : List (ℕ × Fin (rank L)), l.length ≤ wordWtL L l
  | [] => le_rfl
  | (k, _) :: rest => by
    have := length_le_wordWt rest
    simp [wordWtL]; omega

/-- **Every `u₍N₎x` with `N ≤ −2` raises the excess by at least one.** -/
theorem word_smul_le_neg_two_mem_ExFil (l : List (ℕ × Fin (rank L))) {N : ℤ} (hN : N ≤ -2)
    {e : ℤ} {γ : L.carrier} {x : LatModuleGen L} (hx : x ∈ ExFil L e γ) :
    (latticeVOAGen L hEven hPos).smul (wordStateLatGen L l 0) N x ∈ ExFil L (e + 1) γ := by
  have h := word_smul_mem_ExFil L hEven hPos l N e γ x hx
  refine ExFil_anti L ?_ γ h
  have := length_le_wordWt L l
  omega

end PlusC2

end VOA.Classification.COne
