/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.InvariantFormDiagonal

/-!
# FHL full invariance, reduced to the pure `p`-recursion residual `PStep`

Building on `Core.InvariantFormDiagonal` (which reduced the would-be general-`B` full invariance
`InvariantForm.IsFullyInvariant` to the matching-mode identity `DiagonalFHL`), this file discharges
the *entire `q`-direction* and isolates that route in a single predicate `PStep` — closure of the
pure `p`-recursion `(p+wt−q)·D(p,q,a,b) = D(p+1,q,L₋₁a,b)` within one grade `q`.

* **`matchDiff_rec`** (★) — the matching-mode recursion
  `(p+wt−q)·D(p,q,a,b) = D(p+1,q,L₋₁a,b) − D(p,q−1,a,L₁b)` (`fhlDiff_recursion` at the matching
  mode, where all three terms land at *their* matching modes).
* **`matchDiff_vacuum_lt`** — a genuine *closed* sub-case: the matching-mode obstruction vanishes
  for `a = 𝟙` and every `q < wt` (`L₋₁𝟙 = 0` kills one branch; upward induction on `q`).
* **`PStep`** / **`diagAt_of_pstep`** — the `q`-direction is fully discharged by strong induction:
  `PStep B` (the pure `p`-recursion residual at each grade) gives `DiagAt B wt q` for every `wt, q`.
* **`isFullyInvariant_of_pstep`** — full `IsFullyInvariant` from `PStep B` alone.

## Status
**Delimited by a conditional obstruction.** The recursion results are axiom-clean.
`Core.InvariantFormDelimitation.general_pstep_not_a_theorem` rules out a uniform proof of
`PStep B` only under `hqp` and an explicitly supplied nonsymmetric grade-one invariant-form
witness; it does not construct that witness.  Canonical-form FHL is complete in
`Core.InvariantFormFHL2`; `PStep` remains the interface of this historical reduction.

## References
* Gannon §5.1.3, eq. (5.1.11a); Frenkel–Huang–Lepowsky [199]; Li [380].
-/

namespace VOA.VertexOperatorAlgebra

open scoped BigOperators
open Classical

variable {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- `L₋₁ = ω₍₀₎`, so `L₋₁ 𝒱ₖ ⊆ 𝒱_{k+1}` (since `ω ∈ 𝒱₂`, VA1: `ω₍₀₎𝒱ₖ ⊆ 𝒱_{2+k-0-1}`). -/
theorem L_neg_one_raise (W : VertexOperatorAlgebra 𝒱) {k : ℤ} {x : 𝒱} (hx : x ∈ W.grading k) :
    W.L (-1) x ∈ W.grading (k + 1) := by
  have heq : W.L (-1) x = W.smul W.conformalVector 0 x := by
    rw [L_def, PreVertexAlgebra.smul_def, show ((-1 : ℤ) + 1) = 0 by ring]
  rw [heq]
  have h := W.smul_mem_grading W.conformal_mem hx 0
  rwa [show (2 + k - 0 - 1 : ℤ) = k + 1 by ring] at h

/-- Abbreviation for the obstruction at the matching mode (homogeneous data). -/
noncomputable def matchDiff (B : InvariantForm W) (wt p q : ℤ) (u a b : 𝒱) : ℂ :=
  fhlDiff B u a b wt (p + wt - q - 1)

/-- The matching-mode recursion (★):
`(p+wt−q)·D(p,q,a,b) = D(p+1,q,L₋₁a,b) − D(p,q−1,a,L₁b)`. -/
theorem matchDiff_rec (B : InvariantForm W) {wt p q : ℤ} (hwt : 0 ≤ wt) {u a b : 𝒱}
    (hu : u ∈ W.grading wt) (_ha : a ∈ W.grading p) (_hb : b ∈ W.grading q) :
    ((p + wt - q : ℤ) : ℂ) • matchDiff B wt p q u a b
      = matchDiff B wt (p + 1) q u (W.L (-1) a) b
        - matchDiff B wt p (q - 1) u a (W.L 1 b) := by
  have hrec := fhlDiff_recursion B hwt hu a b (p + wt - q)
  rw [show (p + wt - q - 1 : ℤ) = p + wt - q - 1 by ring] at hrec
  simp only [matchDiff]
  rw [show (p + 1 + wt - q - 1 : ℤ) = p + wt - q by ring]
  rw [show (p + wt - (q - 1) - 1 : ℤ) = p + wt - q by ring]
  rw [← hrec]

/-- `fhlDiff` vanishes when `a = 0`. -/
theorem fhlDiff_zero_left (B : InvariantForm W) (u b : 𝒱) (wt n : ℤ) :
    fhlDiff B u 0 b wt n = 0 := by
  rw [fhlDiff, PreVertexAlgebra.smul_zero_right, map_zero, LinearMap.zero_apply,
    fhlRHS_zero_left, sub_zero]

/-- `fhlDiff` vanishes when `b = 0`. -/
theorem fhlDiff_zero_right (B : InvariantForm W) (u a : 𝒱) (wt n : ℤ) :
    fhlDiff B u a 0 wt n = 0 := by
  rw [fhlDiff, map_zero, fhlRHS_zero_right, sub_zero]

/-- `matchDiff` vanishes when `b` lies in a negative grade (then `b = 0`). -/
theorem matchDiff_eq_zero_of_neg_q (B : InvariantForm W) {wt p q : ℤ} (hq : q < 0) {u a b : 𝒱}
    (hb : b ∈ W.grading q) : matchDiff B wt p q u a b = 0 := by
  rw [eq_zero_of_mem_neg_grading W hq hb, matchDiff, fhlDiff_zero_right]

/-- The clean `a = 𝟙` matching-mode recursion: `(wt−q)·D(0,q,𝟙,b) = −D(0,q−1,𝟙,L₁b)`. -/
theorem matchDiff_vacuum_rec (B : InvariantForm W) {wt q : ℤ} (hwt : 0 ≤ wt) {u : 𝒱}
    (hu : u ∈ W.grading wt) {b : 𝒱} (hb : b ∈ W.grading q) :
    ((wt - q : ℤ) : ℂ) • matchDiff B wt 0 q u W.vacuum b
      = - matchDiff B wt 0 (q - 1) u W.vacuum (W.L 1 b) := by
  have hrec := matchDiff_rec B hwt (u := u) (a := W.vacuum) (b := b)
    hu W.vacuum_mem hb
  rw [show (0 + wt - q : ℤ) = wt - q by ring] at hrec
  rw [W.L_neg_one_vacuum] at hrec
  rw [show matchDiff B wt (0 + 1) q u (0 : 𝒱) b = 0 from by
        rw [matchDiff, fhlDiff_zero_left]] at hrec
  rw [hrec, zero_sub]

/-- **`a = 𝟙` diagonal, below the weight.**  For `u ∈ 𝒱_wt`, `b ∈ 𝒱_q` with `q < wt`, the
matching-mode obstruction with `a = 𝟙` vanishes.  Upward strong induction on `q.toNat` (base `q = 0`:
`L₁b = 0`; step: `wt − q ≠ 0`). -/
theorem matchDiff_vacuum_lt (B : InvariantForm W) {wt : ℤ} (hwt : 0 ≤ wt) {u : 𝒱}
    (hu : u ∈ W.grading wt) :
    ∀ (q : ℤ), q < wt → ∀ b : 𝒱, b ∈ W.grading q → matchDiff B wt 0 q u W.vacuum b = 0 := by
  have key : ∀ N : ℕ, ∀ q : ℤ, q.toNat ≤ N → q < wt → ∀ b : 𝒱, b ∈ W.grading q →
      matchDiff B wt 0 q u W.vacuum b = 0 := by
    intro N
    induction N with
    | zero =>
        intro q hqN hqwt b hb
        rcases lt_or_ge q 0 with hqneg | hq0
        · exact matchDiff_eq_zero_of_neg_q B hqneg hb
        · have hq : q = 0 := by omega
          subst hq
          have hrec := matchDiff_vacuum_rec B hwt hu hb
          rw [show (wt - 0 : ℤ) = wt by ring] at hrec
          have hL1 : W.L 1 b = 0 := by
            have hmem := L_one_lower W hb
            rw [show (0 - 1 : ℤ) = -1 by ring] at hmem
            exact eq_zero_of_mem_neg_grading W (by norm_num) hmem
          rw [hL1] at hrec
          rw [show matchDiff B wt 0 (0 - 1) u W.vacuum 0 = 0 from by
                rw [matchDiff, fhlDiff_zero_right], neg_zero] at hrec
          have hwtne : (wt : ℂ) ≠ 0 := by
            have : (0 : ℤ) < wt := hqwt
            exact_mod_cast (by omega : wt ≠ 0)
          rcases smul_eq_zero.mp hrec with h | h
          · exact absurd h hwtne
          · exact h
    | succ M ih =>
        intro q hqN hqwt b hb
        rcases lt_or_ge q 0 with hqneg | hq0
        · exact matchDiff_eq_zero_of_neg_q B hqneg hb
        rcases Nat.lt_or_ge q.toNat (M + 1) with hlt | hge
        · exact ih q (by omega) hqwt b hb
        · have hrec := matchDiff_vacuum_rec B hwt hu hb
          have hL1mem : W.L 1 b ∈ W.grading (q - 1) := L_one_lower W hb
          have hsub : matchDiff B wt 0 (q - 1) u W.vacuum (W.L 1 b) = 0 :=
            ih (q - 1) (by omega) (by omega) (W.L 1 b) hL1mem
          rw [hsub, neg_zero] at hrec
          have hwtne : ((wt - q : ℤ) : ℂ) ≠ 0 := by
            have : q < wt := hqwt
            exact_mod_cast (by omega : (wt - q : ℤ) ≠ 0)
          rcases smul_eq_zero.mp hrec with h | h
          · exact absurd h hwtne
          · exact h
  intro q hqwt b hb
  exact key q.toNat q le_rfl hqwt b hb

/-- The matching-mode diagonal at a fixed weight `wt` and target grade `q`, over all source grades
`p` and all homogeneous data. -/
def DiagAt (B : InvariantForm W) (wt q : ℤ) : Prop :=
  ∀ (p : ℤ) (u a b : 𝒱), u ∈ W.grading wt → a ∈ W.grading p → b ∈ W.grading q →
    matchDiff B wt p q u a b = 0

/-- The **pure `p`-recursion residual**: at a fixed weight `wt` and grade `q ≥ 0`, *given* the
diagonal at every lower grade `q' < q` (which removes the `L₁b` branch of (★)), the diagonal holds
at `q`.  This isolates the entire remaining content of FHL into closing the `p`-recursion
`(p+wt−q)·D(p,q,a,b) = D(p+1,q,L₋₁a,b)` within a single grade `q`. -/
def PStep (B : InvariantForm W) : Prop :=
  ∀ (wt q : ℤ), 0 ≤ wt → 0 ≤ q → (∀ q' : ℤ, q' < q → DiagAt B wt q') → DiagAt B wt q

/-- **`DiagAt` below the floor is automatic.**  For `q < 0`, `b ∈ 𝒱_q = 0`. -/
theorem diagAt_of_neg (B : InvariantForm W) {wt q : ℤ} (hq : q < 0) : DiagAt B wt q := by
  intro p u a b _ _ hb
  exact matchDiff_eq_zero_of_neg_q B hq hb

/-- **The upward-`q` reduction.**  `PStep B` discharges the whole `q`-direction:
`DiagAt B wt q` holds for every `wt ≥ 0` and every `q`, by strong induction on `q.toNat`. -/
theorem diagAt_of_pstep (B : InvariantForm W) (hP : PStep B) {wt : ℤ} (hwt : 0 ≤ wt) :
    ∀ q : ℤ, DiagAt B wt q := by
  have key : ∀ N : ℕ, ∀ q : ℤ, q.toNat ≤ N → DiagAt B wt q := by
    intro N
    induction N with
    | zero =>
        intro q hqN
        rcases lt_or_ge q 0 with hqneg | hq0
        · exact diagAt_of_neg B hqneg
        · have hq : q = 0 := by omega
          subst hq
          exact hP wt 0 hwt le_rfl (fun q' hq' => diagAt_of_neg B (by omega))
    | succ M ih =>
        intro q hqN
        rcases lt_or_ge q 0 with hqneg | hq0
        · exact diagAt_of_neg B hqneg
        · refine hP wt q hwt hq0 (fun q' hq' => ?_)
          rcases lt_or_ge q' 0 with hq'neg | hq'0
          · exact diagAt_of_neg B hq'neg
          · exact ih q' (by omega)
  intro q
  exact key q.toNat q le_rfl

/-- **Full `DiagonalFHL` from the `p`-recursion residual `PStep`.** -/
theorem diagonalFHL_of_pstep (B : InvariantForm W) (hP : PStep B) : DiagonalFHL B := by
  intro wt p q u a b hu ha hb
  rcases lt_or_ge wt 0 with hwt | hwt
  · have hu0 : u = 0 := eq_zero_of_mem_neg_grading W hwt hu
    subst hu0
    rw [PreVertexAlgebra.smul_zero_left, map_zero, LinearMap.zero_apply,
      fhlRHS, Finset.sum_eq_zero (fun j _ => by
        rw [map_zero, PreVertexAlgebra.smul_zero_left, map_zero, smul_zero]), smul_zero]
  · have hdiag := diagAt_of_pstep B hP hwt q p u a b hu ha hb
    rw [matchDiff, fhlDiff, sub_eq_zero] at hdiag
    exact hdiag

/-- **Conditional main result: full FHL full-invariance from the `p`-recursion residual.**  Chaining
`diagonalFHL_of_pstep` with the already-built `isFullyInvariant_of_diagonal`, the entire
Frenkel–Huang–Lepowsky full-invariance theorem `IsFullyInvariant` follows from `PStep B`. -/
theorem isFullyInvariant_of_pstep (B : InvariantForm W) (hP : PStep B) :
    B.IsFullyInvariant :=
  isFullyInvariant_of_diagonal B (diagonalFHL_of_pstep B hP)

end VOA.VertexOperatorAlgebra
