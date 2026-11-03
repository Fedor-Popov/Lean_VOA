/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesArakawaTransport

/-!
# The slice closure of the bottom of a singular vector

Call a subspace `Z ⊆ V^k(sl₂)` **slice-closed** (`SliceClosed`) if it is stable under the creation
modes `f_{-j-1}`, `h_{-j-1}` and the creation Sugawara modes `L_{-j-1}`, and is
`f_{-1}`-saturated: `f_{-1} y ∈ Z → y ∈ Z`.  These are exactly the operations under which the
preimage of `maxIdeal(Vir^c)` under the slice map is stable (`TwoSeriesArakawaTransport`), even
though that map does **not** intertwine the `e`-modes or the zero modes.

The point of this file: let `s` be positive-current-singular with `e₀ s = 0`, `h₀ s = 2 s`,
`f₀³ s = 0`, and let `t₀ = f₀² s` be the bottom (lowest charge) vector of its horizontal
triplet.  Then the smallest slice-closed subspace containing `t₀` is **automatically** stable
under every `e`-creation mode and every zero mode, contains `s`, and therefore contains the whole
nonpositive-current span `U(ŝl₂_{≤0}) s`.

The mechanism is the Sugawara formula on singular vectors (`TwoSeriesArakawaSugawara`): for a
singular `t`,

  `L_{-m-2} t ≡ 2 c₀ (e_{-m-2} f₀ t + f_{-1} e_{-m-1} t)`

modulo the slice-closure of lower `e`-descendants of `t`, so `f_{-1}`-saturation produces
`e_{-m-1} t` from `e_{-m-2} f₀ t`; the induction runs down the `f₀`-string `f₀² s, f₀ s, s`.

## Results

* `sliceClosure`, `sliceClosure_closed`, `sliceClosure_le` — the inductive closure;
* `e_step` — the Sugawara step;
* `sliceClosure_e_mem`, `sliceClosure_zero_mem` — `e`-mode and zero-mode stability;
* `nonpositiveCurrentSpan_le_sliceClosure` — `U(ŝl₂_{≤0}) s ⊆ sliceClosure (f₀² s)`.

Everything here is proved; no new axiom.
-/

namespace VOA.TwoSeries.SliceMap

open VOA.AffineVOA VOA.AffineVOA.SugawaraCov VOA.AffineVOA.Strong
open VOA.AffineSl2BoundaryC2
open scoped BigOperators

noncomputable section

variable (k : ℂ) (hk : k + 2 ≠ 0)

/-! ## §1  Slice-closed subspaces -/

/-- The closure properties of the slice preimage of the Virasoro maximal ideal. -/
structure SliceClosed (Z : Submodule ℂ (WakModule k)) : Prop where
  f_mem : ∀ y ∈ Z, ∀ j : ℕ, J k 1 (-(j : ℤ) - 1) y ∈ Z
  h_mem : ∀ y ∈ Z, ∀ j : ℕ, J k 2 (-(j : ℤ) - 1) y ∈ Z
  L_mem : ∀ y ∈ Z, ∀ j : ℕ, Lm k hk (-(j : ℤ) - 1) y ∈ Z
  div_mem : ∀ y, J k 1 (-1) y ∈ Z → y ∈ Z

variable {k hk}

namespace SliceClosed

variable {Z : Submodule ℂ (WakModule k)} (hZ : SliceClosed k hk Z)
include hZ

theorem f_neg {μ : ℤ} (hμ : μ ≤ -1) {y : WakModule k} (hy : y ∈ Z) : J k 1 μ y ∈ Z := by
  have h := hZ.f_mem y hy (-μ - 1).toNat
  rwa [show -(((-μ - 1).toNat : ℕ) : ℤ) - 1 = μ by omega] at h

theorem h_neg {μ : ℤ} (hμ : μ ≤ -1) {y : WakModule k} (hy : y ∈ Z) : J k 2 μ y ∈ Z := by
  have h := hZ.h_mem y hy (-μ - 1).toNat
  rwa [show -(((-μ - 1).toNat : ℕ) : ℤ) - 1 = μ by omega] at h

theorem L_neg {μ : ℤ} (hμ : μ ≤ -1) {y : WakModule k} (hy : y ∈ Z) : Lm k hk μ y ∈ Z := by
  have h := hZ.L_mem y hy (-μ - 1).toNat
  rwa [show -(((-μ - 1).toNat : ℕ) : ℤ) - 1 = μ by omega] at h

end SliceClosed

variable (k hk)

/-- **The slice closure** of a vector: the smallest slice-closed subspace containing it. -/
def sliceClosure (t : WakModule k) : Submodule ℂ (WakModule k) :=
  sInf {Z | t ∈ Z ∧ SliceClosed k hk Z}

variable {k hk}

theorem mem_sliceClosure_self (t : WakModule k) : t ∈ sliceClosure k hk t :=
  Submodule.mem_sInf.mpr fun _ hZ => hZ.1

theorem sliceClosure_le {t : WakModule k} {Z : Submodule ℂ (WakModule k)} (ht : t ∈ Z)
    (hZ : SliceClosed k hk Z) : sliceClosure k hk t ≤ Z :=
  sInf_le ⟨ht, hZ⟩

theorem sliceClosure_closed (t : WakModule k) : SliceClosed k hk (sliceClosure k hk t) where
  f_mem y hy j := Submodule.mem_sInf.mpr fun Z hZ =>
    hZ.2.f_mem y (Submodule.mem_sInf.mp hy Z hZ) j
  h_mem y hy j := Submodule.mem_sInf.mpr fun Z hZ =>
    hZ.2.h_mem y (Submodule.mem_sInf.mp hy Z hZ) j
  L_mem y hy j := Submodule.mem_sInf.mpr fun Z hZ =>
    hZ.2.L_mem y (Submodule.mem_sInf.mp hy Z hZ) j
  div_mem y hy := Submodule.mem_sInf.mpr fun Z hZ =>
    hZ.2.div_mem y (Submodule.mem_sInf.mp hy Z hZ)

/-! ## §2  The Sugawara step -/

theorem c0_ne_zero (hk : k + 2 ≠ 0) : c0 k ≠ 0 := by
  rw [c0, dualCoxeter]
  exact inv_ne_zero (mul_ne_zero two_ne_zero hk)

/-- `L_{-1}` on a singular vector. -/
theorem Lm_neg_one_singP (t : WakModule k) (ht : SingP k t) :
    Lm k hk (-1) t = c0 k • ((2 : ℂ) • J k 0 (-1) (J k 1 0 t) + (2 : ℂ) • J k 1 (-1) (J k 0 0 t) +
      J k 2 (-1) (J k 2 0 t)) := by
  have h := Lm_singP_expand k hk t ht 0
  simp only [zero_add, Finset.sum_range_one, Nat.cast_zero, neg_zero, zero_sub, sub_zero] at h
  rw [h]
  congr 1
  module

/-- Membership from a `c₀`-multiple. -/
theorem mem_of_c0_smul_mem (hk : k + 2 ≠ 0) {Z : Submodule ℂ (WakModule k)} {x : WakModule k}
    (hx : c0 k • x ∈ Z) : x ∈ Z := by
  have h := Z.smul_mem (c0 k)⁻¹ hx
  rwa [smul_smul, inv_mul_cancel₀ (c0_ne_zero hk), one_smul] at h

/-- **The Sugawara step.**  For a singular `t` in a slice-closed `Z` whose zero-mode images
`e₀ t`, `h₀ t` lie in `Z`, whose lower `e`-descendants `e_{-i-1} t` (`i < m`) lie in `Z`, and with
`e_{-m-2} f₀ t ∈ Z`: also `e_{-m-1} t ∈ Z`. -/
theorem e_step {Z : Submodule ℂ (WakModule k)} (hZ : SliceClosed k hk Z) (t : WakModule k)
    (hS : SingP k t) (ht : t ∈ Z) (he0 : J k 0 0 t ∈ Z) (hh0 : J k 2 0 t ∈ Z) (m : ℕ)
    (IH : ∀ i < m, J k 0 (-(i : ℤ) - 1) t ∈ Z)
    (hmain : J k 0 (-(m : ℤ) - 2) (J k 1 0 t) ∈ Z) :
    J k 0 (-(m : ℤ) - 1) t ∈ Z := by
  apply hZ.div_mem
  set F := J k 1 (-1) (J k 0 (-(m : ℤ) - 1) t) with hF
  have hL := Lm_singP_expand k hk t hS (m + 1)
  have hLZ : Lm k hk (-((m + 1 : ℕ) : ℤ) - 1) t ∈ Z := hZ.L_mem t ht (m + 1)
  rw [hL] at hLZ
  have hsum := mem_of_c0_smul_mem hk hLZ
  -- the three Casimir blocks
  set A := J k 1 (-((m + 1 : ℕ) : ℤ) - 1) (J k 0 0 t) +
    ∑ p ∈ Finset.range (m + 1 + 1),
      J k 0 (-(p : ℤ) - 1) (J k 1 ((p : ℤ) - ((m + 1 : ℕ) : ℤ)) t) with hA
  set B := J k 0 (-((m + 1 : ℕ) : ℤ) - 1) (J k 1 0 t) +
    ∑ p ∈ Finset.range (m + 1 + 1),
      J k 1 (-(p : ℤ) - 1) (J k 0 ((p : ℤ) - ((m + 1 : ℕ) : ℤ)) t) with hB
  set C := J k 2 (-((m + 1 : ℕ) : ℤ) - 1) (J k 2 0 t) +
    ∑ p ∈ Finset.range (m + 1 + 1),
      J k 2 (-(p : ℤ) - 1) (J k 2 ((p : ℤ) - ((m + 1 : ℕ) : ℤ)) t) with hC
  have hmain' : J k 0 (-((m + 1 : ℕ) : ℤ) - 1) (J k 1 0 t) ∈ Z := by
    rw [show -((m + 1 : ℕ) : ℤ) - 1 = -(m : ℤ) - 2 by push_cast; ring]; exact hmain
  -- `A - F ∈ Z`
  have hAF : A - F ∈ Z := by
    rw [hA, Finset.sum_range_succ, Finset.sum_range_succ]
    have hlast : J k 0 (-((m + 1 : ℕ) : ℤ) - 1) (J k 1 (((m + 1 : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ)) t)
        ∈ Z := by rw [sub_self]; exact hmain'
    have hmid : J k 0 (-(m : ℤ) - 1) (J k 1 ((m : ℤ) - ((m + 1 : ℕ) : ℤ)) t) - F ∈ Z := by
      rw [e_f_comm k _ _ (by push_cast; omega), hF,
        show (m : ℤ) - ((m + 1 : ℕ) : ℤ) = -1 by push_cast; ring, add_sub_cancel_left]
      exact hZ.h_neg (by omega) ht
    have hrest : ∑ p ∈ Finset.range m,
        J k 0 (-(p : ℤ) - 1) (J k 1 ((p : ℤ) - ((m + 1 : ℕ) : ℤ)) t) ∈ Z := by
      refine Submodule.sum_mem _ fun p hp => ?_
      have hpm := Finset.mem_range.mp hp
      rw [e_f_comm k _ _ (by push_cast; omega)]
      exact Submodule.add_mem _ (hZ.f_neg (by push_cast; omega) (IH p hpm))
        (hZ.h_neg (by push_cast; omega) ht)
    have h1 : J k 1 (-((m + 1 : ℕ) : ℤ) - 1) (J k 0 0 t) ∈ Z := hZ.f_neg (by omega) he0
    have := Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ h1 hrest) hmid) hlast
    convert this using 1
    abel
  -- `B - F ∈ Z`
  have hBF : B - F ∈ Z := by
    rw [hB, Finset.sum_range_succ, Finset.sum_range_succ']
    have hlast : J k 1 (-((m + 1 : ℕ) : ℤ) - 1) (J k 0 (((m + 1 : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ)) t)
        ∈ Z := by rw [sub_self]; exact hZ.f_neg (by omega) he0
    have hfirst : J k 1 (-((0 : ℕ) : ℤ) - 1) (J k 0 (((0 : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ)) t) = F := by
      rw [hF, show -((0 : ℕ) : ℤ) - 1 = -1 by norm_num,
        show ((0 : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ) = -(m : ℤ) - 1 by push_cast; ring]
    have hrest : ∑ p ∈ Finset.range m,
        J k 1 (-((p + 1 : ℕ) : ℤ) - 1) (J k 0 (((p + 1 : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ)) t) ∈ Z := by
      refine Submodule.sum_mem _ fun p hp => ?_
      have hpm := Finset.mem_range.mp hp
      refine hZ.f_neg (by push_cast; omega) ?_
      have h := IH (m - p - 1) (by omega)
      rwa [show -((m - p - 1 : ℕ) : ℤ) - 1 = ((p + 1 : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ) by
        push_cast [Nat.sub_sub, Nat.cast_sub (show p + 1 ≤ m by omega)]; ring] at h
    rw [hfirst]
    have := Submodule.add_mem _ (Submodule.add_mem _ hmain' hrest) hlast
    convert this using 1
    abel
  -- `C ∈ Z`
  have hCZ : C ∈ Z := by
    rw [hC]
    refine Submodule.add_mem _ (hZ.h_neg (by omega) hh0) (Submodule.sum_mem _ fun p hp => ?_)
    have hpm := Finset.mem_range.mp hp
    refine hZ.h_neg (by omega) ?_
    by_cases hpe : p = m + 1
    · subst hpe; rw [sub_self]; exact hh0
    · exact hZ.h_neg (by push_cast; omega) ht
  -- conclude
  have hfinal : (2 : ℂ) • F ∈ Z := by
    have h := Submodule.sub_mem _ hsum
      (Submodule.add_mem _ (Submodule.add_mem _ hAF hBF) (Submodule.smul_mem _ (1 / 2 : ℂ) hCZ))
    convert h using 1
    module
  have h := Z.smul_mem (1 / 2 : ℂ) hfinal
  rwa [smul_smul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul] at h

/-! ## §3  The good subspace: `e`-modes and zero modes -/

/-- `[e₀, f₀] = h₀`. -/
theorem e0_f0_comm (y : WakModule k) :
    J k 0 0 (J k 1 0 y) = J k 1 0 (J k 0 0 y) + J k 2 0 y := by
  rw [J_comm_apply, Fin.sum_univ_three]
  simp [fabc]

theorem fin3_cases (a : Fin 3) : a = 0 ∨ a = 1 ∨ a = 2 := by
  fin_cases a <;> simp

/-- The vectors of `Z` all of whose `e`-creation and zero-mode images lie in `Z`. -/
def goodSub (Z : Submodule ℂ (WakModule k)) : Submodule ℂ (WakModule k) where
  carrier := {y | y ∈ Z ∧ (∀ m : ℕ, J k 0 (-(m : ℤ) - 1) y ∈ Z) ∧ ∀ a : Fin 3, J k a 0 y ∈ Z}
  add_mem' := by
    rintro x y ⟨hx, hxe, hx0⟩ ⟨hy, hye, hy0⟩
    refine ⟨Z.add_mem hx hy, fun m => ?_, fun a => ?_⟩
    · rw [map_add]; exact Z.add_mem (hxe m) (hye m)
    · rw [map_add]; exact Z.add_mem (hx0 a) (hy0 a)
  zero_mem' := ⟨Z.zero_mem, fun m => by rw [map_zero]; exact Z.zero_mem,
    fun a => by rw [map_zero]; exact Z.zero_mem⟩
  smul_mem' := by
    rintro r x ⟨hx, hxe, hx0⟩
    refine ⟨Z.smul_mem r hx, fun m => ?_, fun a => ?_⟩
    · rw [map_smul]; exact Z.smul_mem r (hxe m)
    · rw [map_smul]; exact Z.smul_mem r (hx0 a)

theorem goodSub_closed {Z : Submodule ℂ (WakModule k)} (hZ : SliceClosed k hk Z) :
    SliceClosed k hk (goodSub (k := k) Z) where
  f_mem := by
    rintro y ⟨hy, hye, hy0⟩ j
    refine ⟨hZ.f_mem y hy j, fun m => ?_, fun a => ?_⟩
    · rw [e_f_comm k _ _ (by omega)]
      exact Z.add_mem (hZ.f_mem _ (hye m) j) (hZ.h_neg (by omega) hy)
    · rcases fin3_cases a with rfl | rfl | rfl
      · rw [e_f_comm k _ _ (by omega)]
        exact Z.add_mem (hZ.f_mem _ (hy0 0) j) (hZ.h_neg (by omega) hy)
      · rw [f_f_comm]; exact hZ.f_mem _ (hy0 1) j
      · rw [h_f_comm]
        exact Z.add_mem (hZ.f_mem _ (hy0 2) j) (Z.smul_mem _ (hZ.f_neg (by omega) hy))
  h_mem := by
    rintro y ⟨hy, hye, hy0⟩ j
    refine ⟨hZ.h_mem y hy j, fun m => ?_, fun a => ?_⟩
    · rw [e_h_comm]
      refine Z.add_mem (hZ.h_mem _ (hye m) j) (Z.smul_mem _ ?_)
      have h := hye (m + j + 1)
      rwa [show -((m + j + 1 : ℕ) : ℤ) - 1 = -(m : ℤ) - 1 + (-(j : ℤ) - 1) by push_cast; ring] at h
    · rcases fin3_cases a with rfl | rfl | rfl
      · rw [e_h_comm]
        refine Z.add_mem (hZ.h_mem _ (hy0 0) j) (Z.smul_mem _ ?_)
        rw [zero_add]; exact hye j
      · rw [f_h_comm]
        exact Z.add_mem (hZ.h_mem _ (hy0 1) j) (Z.smul_mem _ (hZ.f_neg (by omega) hy))
      · rw [h0_h_comm]; exact hZ.h_mem _ (hy0 2) j
  L_mem := by
    rintro y ⟨hy, hye, hy0⟩ j
    refine ⟨hZ.L_mem y hy j, fun m => ?_, fun a => ?_⟩
    · have hc := Lm_J k hk (-(j : ℤ) - 1) 0 (-(m : ℤ) - 1) y
      rw [eq_sub_of_add_eq hc.symm]
      refine Z.sub_mem (hZ.L_mem _ (hye m) j) (Z.smul_mem _ ?_)
      have h := hye (m + j + 1)
      rwa [show -((m + j + 1 : ℕ) : ℤ) - 1 = -(j : ℤ) - 1 + (-(m : ℤ) - 1) by push_cast; ring] at h
    · have hc := Lm_J k hk (-(j : ℤ) - 1) a 0 y
      rw [eq_sub_of_add_eq hc.symm]
      simp only [neg_zero, Int.cast_zero, zero_smul, sub_zero]
      exact hZ.L_mem _ (hy0 a) j
  div_mem := by
    rintro y ⟨hy, hye, hy0⟩
    have hyZ : y ∈ Z := hZ.div_mem y hy
    refine ⟨hyZ, fun m => ?_, fun a => ?_⟩
    · apply hZ.div_mem
      have hc := e_f_comm k (-(m : ℤ) - 1) (-1) (by omega) y
      rw [eq_sub_of_add_eq hc.symm]
      exact Z.sub_mem (hye m) (hZ.h_neg (by omega) hyZ)
    · apply hZ.div_mem
      rcases fin3_cases a with rfl | rfl | rfl
      · have hc := e_f_comm k 0 (-1) (by omega) y
        rw [eq_sub_of_add_eq hc.symm]
        exact Z.sub_mem (hy0 0) (hZ.h_neg (by omega) hyZ)
      · rw [← f_f_comm]; exact hy0 1
      · have hc := h_f_comm k 0 (-1) y
        rw [eq_sub_of_add_eq hc.symm]
        exact Z.sub_mem (hy0 2) (Z.smul_mem _ hy)

/-! ## §4  The horizontal triplet of a singular vector -/

section Triplet

variable (s : WakModule k) (hS : SingP k s) (he : J k 0 0 s = 0) (hh : J k 2 0 s = (2 : ℂ) • s)
  (hf3 : J k 1 0 (J k 1 0 (J k 1 0 s)) = 0)

include hS he hh hf3

/-- **The slice closure of the bottom vector `f₀² s` contains `U(ŝl₂_{≤0}) s`.** -/
theorem nonpositiveCurrentSpan_le_sliceClosure :
    AffineSl2BoundaryC2.nonpositiveCurrentSpan k s ≤
      sliceClosure k hk (J k 1 0 (J k 1 0 s)) := by
  set t₁ := J k 1 0 s with ht₁
  set t₀ := J k 1 0 t₁ with ht₀
  set Cl := sliceClosure k hk t₀ with hCl
  have hC : SliceClosed k hk Cl := sliceClosure_closed t₀
  have ht₀C : t₀ ∈ Cl := mem_sliceClosure_self t₀
  -- singularity of the triplet
  have hS₁ : SingP k t₁ := hS.zeroMode 1
  have hS₀ : SingP k t₀ := hS₁.zeroMode 1
  -- the `sl₂` relations
  have he₁ : J k 0 0 t₁ = (2 : ℂ) • s := by
    rw [ht₁, e0_f0_comm, he, map_zero, zero_add, hh]
  have hh₁ : J k 2 0 t₁ = 0 := by
    rw [ht₁, h_f_comm, hh, map_smul, add_zero]; module
  have he₀ : J k 0 0 t₀ = (2 : ℂ) • t₁ := by
    rw [ht₀, e0_f0_comm, he₁, hh₁, add_zero, map_smul]
  have hh₀ : J k 2 0 t₀ = (-2 : ℂ) • t₀ := by
    rw [ht₀, h_f_comm, hh₁, map_zero, zero_add, add_zero]
  have hf₀ : J k 1 0 t₀ = 0 := hf3
  -- step 1: `f₀ s ∈ Cl`
  have ht₁C : t₁ ∈ Cl := by
    apply hC.div_mem
    have hL := hC.L_mem t₀ ht₀C 0
    rw [show -((0 : ℕ) : ℤ) - 1 = -1 by norm_num, Lm_neg_one_singP (hk := hk) t₀ hS₀, hf₀, he₀,
      hh₀, map_zero, map_smul, map_smul, smul_zero, zero_add] at hL
    have h1 := mem_of_c0_smul_mem hk hL
    have h2 : J k 2 (-1) t₀ ∈ Cl := hC.h_neg (by norm_num) ht₀C
    have h3 := Cl.sub_mem h1 (Cl.smul_mem (-2 : ℂ) h2)
    have h4 := Cl.smul_mem (1 / 4 : ℂ) h3
    convert h4 using 1
    module
  -- step 2: all `e`-descendants of `t₀`
  have he0C : J k 0 0 t₀ ∈ Cl := by rw [he₀]; exact Cl.smul_mem _ ht₁C
  have hh0C : J k 2 0 t₀ ∈ Cl := by rw [hh₀]; exact Cl.smul_mem _ ht₀C
  have hEt₀ : ∀ m : ℕ, J k 0 (-(m : ℤ) - 1) t₀ ∈ Cl := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m IH =>
      exact e_step hC t₀ hS₀ ht₀C he0C hh0C m IH (by rw [hf₀, map_zero]; exact Cl.zero_mem)
  -- step 3: the good subspace contains the closure
  have hgood : Cl ≤ goodSub (k := k) Cl := by
    refine sliceClosure_le ⟨ht₀C, hEt₀, fun a => ?_⟩ (goodSub_closed hC)
    rcases fin3_cases a with rfl | rfl | rfl
    · exact he0C
    · rw [hf₀]; exact Cl.zero_mem
    · exact hh0C
  have hE : ∀ y ∈ Cl, ∀ m : ℕ, J k 0 (-(m : ℤ) - 1) y ∈ Cl := fun y hy => (hgood hy).2.1
  have hZ0 : ∀ y ∈ Cl, ∀ a : Fin 3, J k a 0 y ∈ Cl := fun y hy => (hgood hy).2.2
  -- step 4: `s ∈ Cl`
  have hsC : s ∈ Cl := by
    apply hC.div_mem
    have hL := hC.L_mem t₁ ht₁C 0
    rw [show -((0 : ℕ) : ℤ) - 1 = -1 by norm_num, Lm_neg_one_singP (hk := hk) t₁ hS₁, he₁, hh₁,
      map_zero, add_zero, map_smul] at hL
    have h1 := mem_of_c0_smul_mem hk hL
    have h2 : J k 0 (-1) t₀ ∈ Cl := by
      have := hE t₀ ht₀C 0
      rwa [show -((0 : ℕ) : ℤ) - 1 = -1 by norm_num] at this
    have h3 := Cl.sub_mem h1 (Cl.smul_mem (2 : ℂ) h2)
    have h4 := Cl.smul_mem (1 / 4 : ℂ) h3
    convert h4 using 1
    rw [← ht₀]
    module
  -- step 5: nonpositive current words
  rw [AffineSl2BoundaryC2.nonpositiveCurrentSpan, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  induction l with
  | nil => exact hsC
  | cons am l ih =>
      obtain ⟨a, μ⟩ := am
      have hμ : μ ≤ 0 := hl (a, μ) (List.mem_cons_self ..)
      have hrest := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      rw [AffineSl2BoundaryC2.currentWord_cons]
      rcases eq_or_lt_of_le hμ with h0 | hneg
      · subst h0; exact hZ0 _ hrest a
      · rcases fin3_cases a with rfl | rfl | rfl
        · have h := hE _ hrest (-μ - 1).toNat
          rwa [show -(((-μ - 1).toNat : ℕ) : ℤ) - 1 = μ by omega] at h
        · exact hC.f_neg (by omega) hrest
        · exact hC.h_neg (by omega) hrest

end Triplet

end

end VOA.TwoSeries.SliceMap
