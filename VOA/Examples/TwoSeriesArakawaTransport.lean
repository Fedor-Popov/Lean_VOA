/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesArakawaSugawara
import VOA.Examples.LeeYangCharacterSpanning

/-!
# Exact transport rules of the slice map

The graded slice map `Wslice : V^k(sl₂) → (ℤ →₀ Vir^c)` of `TwoSeriesSliceMap` satisfies, besides
the Whittaker relations for `f`, the following **exact** rules, for every vector:

* `Wslice_h` — `W ∘ h_{-j-1} = 0`;
* `Wslice_Lm` — `W ∘ L_n = L_n ∘ W` for every creation Sugawara mode `n ≤ -1`, **including**
  `n = -1` (`phi_Lop_neg_one`: `φ` intertwines `L_{-1}` with the derivation `Lt (-1)`).

Consequently the preimage of the maximal ideal,
`sliceMaxPreimage = {y | ∀ a, W(y)_a ∈ maxIdeal(Vir^c)}`, is stable under `f_{-j-1}`, `h_{-j-1}`,
`L_{-j-1}`, and is **`f_{-1}`-saturated** (`f_{-1} y ∈ Z → y ∈ Z`) — the four closure properties
used by the slice-closure argument of `TwoSeriesArakawaClosure`.

Everything here is proved; no new axiom.
-/

namespace VOA.TwoSeries.SliceMap

open VOA.AffineVOA VOA.AffineVOA.SugawaraCov VOA.AffineVOA.Strong MvPolynomial
open VOA.VirModule VOA.TwoSeries.DSSlice VOA.VirSimple VOA.LeeYangCharacter
open scoped BigOperators

noncomputable section

variable (c k : ℂ) (hk : k + 2 ≠ 0)

/-! ## §1  `φ` intertwines `L_{-1}` -/

theorem phi_Lop_neg_one_negWordVir (w : List ℕ) :
    phi c k hk (Lop c (-1) (negWordVir c w)) = Lt k hk (-1) (phi c k hk (negWordVir c w)) := by
  induction w with
  | nil =>
      rw [negWordVir_nil, Lop_vacuum c le_rfl, map_zero, phi_vac, Lt_one_neg_one]
  | cons n w ih =>
      have hb := congrArg (fun T : Module.End ℂ (VirUniv c) => T (negWordVir c w))
        (Lop_bracket c (-1) (-(n : ℤ) - 2))
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
        LinearMap.smul_apply] at hb
      rw [if_neg (by omega), zero_smul, add_zero, sub_eq_iff_eq_add] at hb
      have e1 : phi c k hk (Lop c (-(n : ℤ) - 2) (Lop c (-1) (negWordVir c w))) =
          Lt k hk (-(n : ℤ) - 2) (Lt k hk (-1) (phi c k hk (negWordVir c w))) := by
        rw [phi_Lop, ih]
      have e2 := phi_Lop c k hk (n + 1) (negWordVir c w)
      have e3 := phi_Lop c k hk n (negWordVir c w)
      have hc := Lt_comm k hk (m := -1) (n := -(n : ℤ) - 2) le_rfl (by omega)
        (phi c k hk (negWordVir c w))
      rw [show (-1 : ℤ) + (-(n : ℤ) - 2) = -((n + 1 : ℕ) : ℤ) - 2 by push_cast; ring] at hb hc
      rw [negWordVir_cons, hb, map_add, map_smul, e1, e2, e3, hc, add_comm]

/-- `φ ∘ L_{-1} = Lt(-1) ∘ φ`. -/
theorem phi_Lop_neg_one (v : VirUniv c) :
    phi c k hk (Lop c (-1) v) = Lt k hk (-1) (phi c k hk v) := by
  have h : (phi c k hk).comp (Lop c (-1)) = (Lt k hk (-1)).comp (phi c k hk) := by
    apply LinearMap.ext_on_range (v := negWordVir c)
    · have := negSpanVir_eq_top c
      rwa [negSpanVir] at this
    · intro w
      exact phi_Lop_neg_one_negWordVir c k hk w
  exact LinearMap.congr_fun h v

theorem psi_Lt_neg_one (P : EPoly) :
    psi c k hk (Lt k hk (-1) P) = Lop c (-1) (psi c k hk P) := by
  apply phi_injective c k hk
  rw [phi_psi, phi_Lop_neg_one, phi_psi]

/-! ## §2  The ungraded and graded transport rules -/

/-- `W₁ ∘ L_n = L_n ∘ W₁` for every creation mode `n ≤ -1`. -/
theorem W1_Lm {n : ℤ} (hn : n ≤ -1) (y : WakModule k) :
    W1 c k hk (Lm k hk n y) = Lop c n (W1 c k hk y) := by
  simp only [W1, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [W0_Lm k hk hn]
  rcases (show n = -1 ∨ ∃ j : ℕ, n = -(j : ℤ) - 2 by
    rcases eq_or_lt_of_le hn with h | h
    · exact Or.inl h
    · exact Or.inr ⟨(-n - 2).toNat, by omega⟩) with h | ⟨j, rfl⟩
  · subst h; exact psi_Lt_neg_one c k hk _
  · exact psi_Lt c k hk j _

/-- `W₁ ∘ h_{-j-1} = 0`. -/
theorem W1_h (j : ℕ) (y : WakModule k) : W1 c k hk (J k 2 (-(j : ℤ) - 1) y) = 0 := by
  simp only [W1, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [W0_J_h k hk j, map_zero]

/-- The creation Sugawara modes preserve the charge grading. -/
theorem Lm_KC_charge {n : ℤ} (hn : n ≤ -1) {p : ℕ} {q : ℤ} {y : WakModule k}
    (hy : y ∈ KC k p q) : ∃ p', Lm k hk n y ∈ KC k p' q := by
  rcases eq_or_lt_of_le hn with h | h
  · subst h; exact ⟨p, Lm_neg_one_KC k hk hy⟩
  · refine ⟨p + 2, ?_⟩
    have := Lm_KC k hk (-n - 2).toNat hy
    rwa [show -(((-n - 2).toNat : ℕ) : ℤ) - 2 = n by omega] at this

/-- **Exact Sugawara transport of the graded slice map**, `n ≤ -1`. -/
theorem Wslice_Lm {n : ℤ} (hn : n ≤ -1) (y : WakModule k) (a : ℤ) :
    Wslice c k hk (Lm k hk n y) a = Lop c n (Wslice c k hk y a) := by
  have h : (Finsupp.lapply a).comp ((Wslice c k hk).comp (Lm k hk n)) =
      (Lop c n).comp ((Finsupp.lapply a).comp (Wslice c k hk)) := by
    apply LinearMap.ext_on_range (rword_span_eq_top k)
    intro l
    have hl := rword_mem_KC_self k l
    obtain ⟨p', hp'⟩ := Lm_KC_charge k hk hn hl
    simp only [LinearMap.comp_apply, Finsupp.lapply_apply]
    rw [Wslice_KC c k hk hp', Wslice_KC c k hk hl, W1_Lm c k hk hn, Finsupp.single_apply,
      Finsupp.single_apply]
    split_ifs <;> simp
  exact LinearMap.congr_fun h y

/-- **The graded slice map kills `h`-led vectors.** -/
theorem Wslice_h (j : ℕ) (y : WakModule k) : Wslice c k hk (J k 2 (-(j : ℤ) - 1) y) = 0 := by
  have h : (Wslice c k hk).comp (J k 2 (-(j : ℤ) - 1)) = 0 := by
    apply LinearMap.ext_on_range (rword_span_eq_top k)
    intro l
    rw [LinearMap.comp_apply, LinearMap.zero_apply]
    have hw : J k 2 (-(j : ℤ) - 1) (rword k l) = rword k (toLex (1, j) :: l) := by
      rw [rword_cons]
      simp only [col_toLex, dep_toLex, rankColor]
    rw [hw, Wslice, chargeLift_rword, ← hw]
    have h0 := W1_h c k hk j (rword k l)
    rw [show W1 c k hk (J k 2 (-(j : ℤ) - 1) (rword k l)) = 0 from h0, Finsupp.single_zero]
  exact LinearMap.congr_fun h y

/-! ## §3  The preimage of the maximal ideal -/

/-- The vectors whose every graded slice component lies in the maximal ideal of `Vir^c`. -/
def sliceMaxPreimage : Submodule ℂ (WakModule k) where
  carrier := {y | ∀ a, Wslice c k hk y a ∈ maxIdealVir c}
  add_mem' := by
    intro x y hx hy a
    rw [map_add, Finsupp.add_apply]
    exact Submodule.add_mem _ (hx a) (hy a)
  zero_mem' := by
    intro a
    rw [map_zero, Finsupp.zero_apply]
    exact Submodule.zero_mem _
  smul_mem' := by
    intro r x hx a
    rw [map_smul, Finsupp.smul_apply]
    exact Submodule.smul_mem _ r (hx a)

theorem mem_sliceMaxPreimage {y : WakModule k} :
    y ∈ sliceMaxPreimage c k hk ↔ ∀ a, Wslice c k hk y a ∈ maxIdealVir c := Iff.rfl

end

end VOA.TwoSeries.SliceMap
