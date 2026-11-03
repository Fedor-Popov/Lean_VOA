/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesHighReduce
import VOA.Examples.TwoSeriesBoxFusion

/-!
# Affine GU ⇒ GU of `M(2, 2n+3)` through the model route

The membership bound `ModelSocleMembership n r` needs, for every `N < r`, the inclusion of the
membership space `vMem (R_n) r d (2N)` in the box (`BoxCount` is proved for every `n`, `r`:
`boxCount_all`).  This file gets that inclusion **directly from the model ring**, bypassing the
test ring and its jet ideal `(J + x̃)ⁿ`:

* slots with `T`-degree `k = r - N ≤ n`: the test-ring results (`boxInclusion_low`,
  `boxInclusion_degN`), since `vMem ⊆ testSp`;
* slots with `N ≤ 1` (any `k`): `TwoSeriesHighReduce` + the Euler cases `jetPoincare_zero`,
  `jetPoincare_one` — **new: every slot with `N ≤ 1` and `k > n`**;
* slots with `N ≥ 2`, `k > n`: the named input `JetPoincareHigh n` (the jet-ideal Poincaré lemma in
  those slots, a statement purely about `ℂ[T_j]` and the jet ideal of `Tⁿ`).

Main results:

* `vMem_le_box_zero`, `vMem_le_box_one` — `vMem ⊆ box` in every slot with `N ≤ 1`;
* `vMem_le_box_of_le` — `vMem ⊆ box` in every slot with `r - N ≤ n`;
* `modelSocleMembership_of_le` — **`ModelSocleMembership n r` for every `r ≤ n + 2`**,
  unconditionally (this covers `BoxInclusion n (n + 1)` and `BoxInclusion n (n + 2)`-type slots);
* `JetPoincareHigh n` — the remaining input; `modelSocleMembership_of_jetPoincare`;
* `twoSeries_gradedUnitary_of_strictModel_jetPoincare` — **Affine GU ⇒ GU of `M(2, 2n+3)`**,
  conditional only on `hA`, detection `det` and `JetPoincareHigh n`.

Everything is proved outright.
-/

namespace VOA.TwoSeries.StrictModel

open MvPolynomial

noncomputable section

namespace HighEndpoint

open HighJet HighReduce

/-- `vMem ⊆ box` in every slot with `N = 0`. -/
theorem vMem_le_box_zero {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (d : ℤ) :
    vMem (Rn n) (tn n) (0 + k) d (2 * 0) ≤ boxW (tn n) 0 k (d - ((0 + k : ℕ) : ℤ)) :=
  vMem_le_box_of_jetPoincare hn hk d fun E _ => jetPoincare_zero n k E

/-- `vMem ⊆ box` in every slot with `N = 1`. -/
theorem vMem_le_box_one {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (d : ℤ) :
    vMem (Rn n) (tn n) (1 + k) d (2 * 1) ≤ boxW (tn n) 1 k (d - ((1 + k : ℕ) : ℤ)) :=
  vMem_le_box_of_jetPoincare hn hk d fun E _ => jetPoincare_one n k E

/-- `vMem ⊆ box` in every slot of `T`-degree `r - N ≤ n` (the test-ring results). -/
theorem vMem_le_box_of_le {n r N : ℕ} (hn : 1 ≤ n) (d : ℤ) (hN : N < r) (hk : r - N ≤ n) :
    vMem (Rn n) (tn n) r d (2 * N) ≤ boxW (tn n) N (r - N) (d - r) := by
  intro τ hτ
  have h : τ ∈ tMonW (Rn n) (tn n) (r - N) (d - r) ⊓ testSp n r N :=
    ⟨vMem_le_tMonW (Rn n) (tn n) hN.le d hτ, vMem_le_testSp n r d N hτ⟩
  rcases Nat.lt_or_ge (r - N) n with hlt | hge
  · exact InclLow.boxInclusion_low d N hN hlt h
  · exact LiftDegN.boxInclusion_degN hn d N (le_antisymm hk hge) hN h

/-- **The remaining input**: the jet-ideal Poincaré lemma in the slots with `N ≥ 2` and `T`-degree
`k > n`. -/
def JetPoincareHigh (n : ℕ) : Prop :=
  ∀ N k E : ℕ, 2 ≤ N → n < k → JetPoincare n N k E

/-- `vMem ⊆ box` in one slot, from the box inclusion of the slot. -/
theorem rank_vMem_le {n r : ℕ} (hn : 1 ≤ n) {d : ℤ} {N : ℕ} (hN : N < r)
    (h : vMem (Rn n) (tn n) r d (2 * N) ≤ boxW (tn n) N (r - N) (d - r)) :
    Module.rank ℂ ↥(vMem (Rn n) (tn n) r d (2 * N)) ≤ socleCount n r d N :=
  (Submodule.rank_mono h).trans (boxCount_all n hn r d N hN)

/-- `vMem ⊆ box` in every slot, given the input in the slots with `N ≥ 2`, `k > n`. -/
theorem vMem_le_box {n r N : ℕ} (hn : 1 ≤ n) (d : ℤ) (hN : N < r)
    (hJP : 2 ≤ N → n < r - N → ∀ E : ℕ, JetPoincare n N (r - N) E) :
    vMem (Rn n) (tn n) r d (2 * N) ≤ boxW (tn n) N (r - N) (d - r) := by
  rcases Nat.lt_or_ge n (r - N) with hlt | hge
  · obtain ⟨k, hk, rfl⟩ : ∃ k, 1 ≤ k ∧ r = N + k := ⟨r - N, by omega, by omega⟩
    rw [show N + k - N = k by omega]
    rcases Nat.lt_or_ge N 2 with hN2 | hN2
    · interval_cases N
      · exact vMem_le_box_zero hn hk d
      · exact vMem_le_box_one hn hk d
    · refine vMem_le_box_of_jetPoincare hn hk d fun E _ => ?_
      have := hJP hN2 (by omega) E
      rwa [show N + k - N = k by omega] at this
  · exact vMem_le_box_of_le hn d hN hge

/-- **`ModelSocleMembership n r` for every `r ≤ n + 2`**, unconditionally. -/
theorem modelSocleMembership_of_le {n r : ℕ} (hn : 1 ≤ n) (hr : r ≤ n + 2) :
    ModelSocleMembership n r :=
  modelSocleMembership_of_below hn fun d N hN =>
    rank_vMem_le hn hN (vMem_le_box hn d hN fun h2 hk => absurd hk (by omega))

/-- **`ModelSocleMembership n r` for every `r`** from the jet-ideal Poincaré lemma in the slots
with `N ≥ 2`, `k > n`. -/
theorem modelSocleMembership_of_jetPoincare {n : ℕ} (hn : 1 ≤ n) (h : JetPoincareHigh n)
    (r : ℕ) : ModelSocleMembership n r :=
  modelSocleMembership_of_below hn fun d N hN =>
    rank_vMem_le hn hN (vMem_le_box hn d hN fun h2 hk E => h N (r - N) E h2 hk)

end HighEndpoint

open HighEndpoint

/-- **Affine GU ⇒ GU of `M(2, 2n+3)`**, `#print axioms`-clean, conditional only on `hA`,
detection `det` and the jet-ideal Poincaré lemma `JetPoincareHigh n` in the slots `N ≥ 2`,
`k > n` (a statement purely about `ℂ[T_j]` and the jet ideal of `Tⁿ`). -/
theorem twoSeries_gradedUnitary_of_strictModel_jetPoincare (n : ℕ) (hn : 1 ≤ n)
    (hA : GradedUnitary (affineForm (twoSeriesLevels n)) (affineRealStructure (twoSeriesLevels n))
      (affineFlag (twoSeriesLevels n)))
    (det : TwoSeriesModelDetects n) (h : JetPoincareHigh n) :
    VirGradedUnitarity.VirGradedUnitary (twoSeriesLevels n).c
      (targetRealStructure (twoSeriesLevels n)) :=
  twoSeries_gradedUnitary_of_strictModel_membership n hn hA det
    (modelSocleMembership_of_jetPoincare hn h)

end

end VOA.TwoSeries.StrictModel
