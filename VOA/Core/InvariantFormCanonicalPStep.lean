/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.InvariantFormCanonicalVir
import VOA.Core.LieAlgebraV1

/-!
# Canonical-form FHL: the native covariance machinery, reducing `CanDiagonal` to one resonant slice

The full `canBilin`-native replication of the `Core.InvariantFormDiagonal`/`PStep` machinery — built
on `canBilin_Lneg1_adj` (the proved `n=−1` adjointness under `L₁𝒱₁=0`) in place of `B.virasoro_adj`,
so it is NOT circular through `DiagonalFHL`/`canForm`:

* **`canBilin_mode_lower`** / **`canBilin_L1_term`** / **`canInner_recursion`** / **`canDiff_recursion`**
  — the `L₋₁`-covariance recursion for the canonical obstruction.
* **`matchDiff_rec`** — the matching-mode recursion `(p+wt−q)·D = D(p+1,L₋₁a) − D(p,q−1,L₁b)`.
* **`canDiagonal_of_pstep`** / **`canDiagonal_holds_of_pstep`** — the `q`-direction is fully discharged
  by downward induction, reducing `CanDiagonal` to the single resonant residual **`CanPStep`** (the
  pure-`p`-recursion closure within a grade).
* **`adjPair_transpose`** (the Li lever `vacCoord_smul_symm` applied to every `adjPair` summand) and
  **`canRHS_wt1`** — the staged tools for the final two-point computation.

## Status
**The residual is bypassed in `Core.InvariantFormFHL2`.**  The residual named below is discharged, under the
standing hypotheses `hne : 𝟙 ≠ 0` and `hqp : L₁𝒱₁ = 0`, by `canDiagonal_unconditional : CanDiagonal hne`
and `canVirasoroAdj_of_diagonal`; the resulting form is `canonicalInvariantForm`.  `FHL2` reaches `CanDiagonal` directly
(sl₂ decomposition `qpDecomp` + matching
`canBilin_qp_qp_adj`), so `CanPStep` is not needed there and is not itself proved.  The text below
describes this file's own reduction, an intermediate step.
Axiom-free reduction; bottoms out at the residual `CanPStep` (→ Li 1994; bypassed, see above).
Axiom-clean for the native covariance machinery, the `q`-direction discharge, and the levers. The
residual `CanPStep` (a hypothesis, not an axiom) is the genuine irreducible Li Prop 2.6 core:
the resonant/creation-mode two-point `vacCoord` identity, where the covariance recursion is singular
(coefficient vanishes) and `vacCoord_smul_symm` + the `e^{zL₁}` tower must supply the independent
equation. Provable under `L₁𝒱₁=0` (Li's theorem), the multi-page two-point computation.

## References
* Gannon §5.1.3, eqs. (5.1.11)–(5.1.12); Frenkel–Huang–Lepowsky [199]; Li [380].
-/


open VOA VOA.VertexOperatorAlgebra
open scoped BigOperators
open Classical
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

namespace VOA

/-! ## Native `L₋₁`-covariance recursion for `canBilin` (replicating `Core.InvariantFormDiagonal`,
using `canBilin_Lneg1_adj` in place of `B.virasoro_adj (-1)`). -/

/-- **Form-level `L₋₁`-covariance recursion** for `canBilin` (the LHS mode-lowering), under `hqp`:
`n·canBilin(u₍ₙ₋₁₎a, b) = canBilin(u₍ₙ₎(L₋₁a), b) − canBilin(u₍ₙ₎a, L₁b)`. -/
theorem canBilin_mode_lower (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) (u a b : V) (n : ℤ) :
    (n : ℂ) • canBilin W hne (W.smul u (n - 1) a) b
      = canBilin W hne (W.smul u n (W.L (-1) a)) b
        - canBilin W hne (W.smul u n a) (W.L 1 b) := by
  have h := smul_mode_lower W u a n
  apply_fun (fun x => canBilin W hne x b) at h
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, ← smul_eq_mul] at h
  rw [map_sub, LinearMap.sub_apply] at h
  rw [h]
  congr 1
  rw [canBilin_Lneg1_adj hne hqp (W.smul u n a) b]

/-- **Form-level per-term `L₁`-covariance** for `canBilin`, under `hqp`:
`canBilin(L₋₁a, v₍s₎b) − canBilin(a, v₍s₎(L₁b)) = (2w−s−2)·canBilin(a, v₍s+1₎b) + canBilin(a, (L₁v)₍s₎b)`. -/
theorem canBilin_L1_term (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {w : ℤ} {v : V} (hv : v ∈ W.grading w)
    (s : ℤ) (a b : V) :
    canBilin W hne (W.L (-1) a) (W.smul v s b) - canBilin W hne a (W.smul v s (W.L 1 b))
      = (2 * w - s - 2 : ℂ) • canBilin W hne a (W.smul v (s + 1) b)
          + canBilin W hne a (W.smul (W.L 1 v) s b) := by
  have hbr := L1_bracket_smul W hv s b
  apply_fun (fun x => canBilin W hne a x) at hbr
  rw [map_sub, map_add, map_smul, smul_eq_mul, ← smul_eq_mul] at hbr
  rw [← canBilin_Lneg1_adj hne hqp a (W.smul v s b)] at hbr
  exact hbr

/-- The `canRHS` inner sum `S(a,b,n) = ∑_{j≤wt} (1/j!) canBilin(a, (L₁ʲu)₍2wt−n−2−j₎ b)`
(so `canRHS = (−1)^wt • canInner`). -/
noncomputable def canInner (hne : W.vacuum ≠ 0) (u a b : V) (wt n : ℤ) : ℂ :=
  ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) •
    canBilin W hne a (W.smul (((W.L 1) ^ j) u) (2 * wt - n - 2 - (j : ℤ)) b)

/-- `canRHS = (−1)^wt • canInner`. -/
theorem canRHS_eq_inner (hne : W.vacuum ≠ 0) (u a b : V) (wt n : ℤ) :
    canRHS hne u a b wt n = (-1 : ℂ) ^ wt • canInner hne u a b wt n := rfl

/-- **The FHL covariance recursion for the inner sum** for `canBilin`, under `hqp`. For `u ∈ 𝒱_wt`,
`n·S(a,b,n−1) = S(L₋₁a,b,n) − S(a,L₁b,n)`. -/
theorem canInner_recursion (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {wt : ℤ} (hwt : 0 ≤ wt) {u : V}
    (hu : u ∈ W.grading wt) (a b : V) (n : ℤ) :
    (n : ℂ) • canInner hne u a b wt (n - 1)
      = canInner hne u (W.L (-1) a) b wt n - canInner hne u a (W.L 1 b) wt n := by
  set K := wt.toNat with hK
  have hvmem : ∀ j : ℕ, ((W.L 1) ^ j) u ∈ W.grading (wt - (j : ℤ)) := fun j => L_one_pow_mem W hu j
  have hLv : ∀ j : ℕ, W.L 1 (((W.L 1) ^ j) u) = ((W.L 1) ^ (j + 1)) u := by
    intro j; rw [pow_succ']; rfl
  have hvtop : ((W.L 1) ^ (K + 1)) u = 0 := by
    apply L_one_pow_eq_zero W hu
    rw [hK]; omega
  set P : ℕ → ℂ := fun j => canBilin W hne a (W.smul (((W.L 1) ^ j) u) (2 * wt - (n - 1) - 2 - (j : ℤ)) b)
    with hP
  rw [canInner]
  rw [canInner, canInner, ← Finset.sum_sub_distrib]
  have hterm : ∀ j ∈ Finset.range (K + 1),
      ((j.factorial : ℂ)⁻¹) • canBilin W hne (W.L (-1) a)
          (W.smul (((W.L 1) ^ j) u) (2 * wt - n - 2 - (j : ℤ)) b)
        - ((j.factorial : ℂ)⁻¹) • canBilin W hne a
          (W.smul (((W.L 1) ^ j) u) (2 * wt - n - 2 - (j : ℤ)) (W.L 1 b))
        = ((j.factorial : ℂ)⁻¹) • ((((n : ℂ) - j)) • P j)
          + ((j.factorial : ℂ)⁻¹) • canBilin W hne a
              (W.smul (((W.L 1) ^ (j + 1)) u) (2 * wt - n - 2 - (j : ℤ)) b) := by
    intro j _
    rw [← smul_sub]
    rw [canBilin_L1_term hne hqp (hvmem j) (2 * wt - n - 2 - (j : ℤ)) a b]
    rw [hLv j, smul_add]
    congr 1
    rw [hP]
    have hcoeff : (2 * ((wt - (j : ℤ) : ℤ) : ℂ) - ((2 * wt - n - 2 - (j : ℤ) : ℤ) : ℂ) - 2)
        = ((n : ℂ) - j) := by push_cast; ring
    have hidx : (2 * wt - n - 2 - (j : ℤ) + 1 : ℤ) = (2 * wt - (n - 1) - 2 - (j : ℤ)) := by ring
    rw [hcoeff, hidx]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  have hQP : ∀ j : ℕ, canBilin W hne a (W.smul (((W.L 1) ^ (j + 1)) u) (2 * wt - n - 2 - (j : ℤ)) b)
      = P (j + 1) := by
    intro j; rw [hP]; congr 2; push_cast; ring
  rw [show (∑ j ∈ Finset.range (K + 1), ((j.factorial : ℂ)⁻¹) • canBilin W hne a
            (W.smul (((W.L 1) ^ (j + 1)) u) (2 * wt - n - 2 - (j : ℤ)) b))
        = ∑ j ∈ Finset.range (K + 1), ((j.factorial : ℂ)⁻¹) • P (j + 1)
      from Finset.sum_congr rfl (fun j _ => by rw [hQP j])]
  rw [hP, Finset.smul_sum]
  have hPtop : P (K + 1) = 0 := by rw [hP]; simp only [hvtop, W.smul_zero_left, map_zero]
  have hshift : (∑ j ∈ Finset.range (K + 1), ((j.factorial : ℂ)⁻¹) • P (j + 1))
      = ∑ j ∈ Finset.range (K + 1), ((j : ℂ) * (j.factorial : ℂ)⁻¹) • P j := by
    rw [Finset.sum_range_succ' (fun j => ((j : ℂ) * (j.factorial : ℂ)⁻¹) • P j) K]
    simp only [Nat.cast_zero, zero_mul, zero_smul, add_zero]
    rw [Finset.sum_range_succ (fun j => ((j.factorial : ℂ)⁻¹) • P (j + 1)) K, hPtop, smul_zero,
      add_zero]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    rw [Nat.factorial_succ]
    push_cast
    rw [mul_inv]
    field_simp
  rw [hshift, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [smul_smul]
  rw [show ((j.factorial : ℂ)⁻¹) • (((n : ℂ) - j) • P j)
        = (((j.factorial : ℂ)⁻¹ * ((n : ℂ) - j))) • P j by rw [smul_smul]]
  rw [← add_smul]
  congr 1
  field_simp
  ring

/-- The `canBilin` obstruction at weight `wt`: `canDiff = canBilin(u₍ₙ₎a, b) − canRHS`. -/
noncomputable def canDiff (hne : W.vacuum ≠ 0) (u a b : V) (wt n : ℤ) : ℂ :=
  canBilin W hne (W.smul u n a) b - canRHS hne u a b wt n

/-- **The `L₋₁`-covariance recursion for the obstruction `canDiff`** under `hqp`. -/
theorem canDiff_recursion (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {wt : ℤ} (hwt : 0 ≤ wt) {u : V}
    (hu : u ∈ W.grading wt) (a b : V) (n : ℤ) :
    (n : ℂ) • canDiff hne u a b wt (n - 1)
      = canDiff hne u (W.L (-1) a) b wt n - canDiff hne u a (W.L 1 b) wt n := by
  simp only [canDiff]
  rw [smul_sub, canBilin_mode_lower hne hqp u a b n]
  have hcan := canInner_recursion hne hqp hwt hu a b n
  rw [canRHS_eq_inner, canRHS_eq_inner, canRHS_eq_inner]
  rw [smul_comm ((n : ℂ)) ((-1 : ℂ) ^ wt), hcan, smul_sub]
  ring

/-- Abbreviation for the obstruction at the matching mode (homogeneous data). -/
noncomputable def matchDiff (hne : W.vacuum ≠ 0) (wt p q : ℤ) (u a b : V) : ℂ :=
  canDiff hne u a b wt (p + wt - q - 1)

/-- The matching-mode recursion (★) for `canBilin`:
`(p+wt−q)·D(p,q,a,b) = D(p+1,q,L₋₁a,b) − D(p,q−1,a,L₁b)`. -/
theorem matchDiff_rec (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {wt p q : ℤ} (hwt : 0 ≤ wt) {u a b : V}
    (hu : u ∈ W.grading wt) (_ha : a ∈ W.grading p) (_hb : b ∈ W.grading q) :
    ((p + wt - q : ℤ) : ℂ) • matchDiff hne wt p q u a b
      = matchDiff hne wt (p + 1) q u (W.L (-1) a) b
        - matchDiff hne wt p (q - 1) u a (W.L 1 b) := by
  have hrec := canDiff_recursion hne hqp hwt hu a b (p + wt - q)
  rw [show (p + wt - q - 1 : ℤ) = p + wt - q - 1 by ring] at hrec
  simp only [matchDiff]
  rw [show (p + 1 + wt - q - 1 : ℤ) = p + wt - q by ring]
  rw [show (p + wt - (q - 1) - 1 : ℤ) = p + wt - q by ring]
  rw [← hrec]

/-! ## STEP 1: the weight-1 current adjunction `canBilin(u₍ₙ₎a, b) = − canBilin(a, u₍−n₎b)`. -/

/-- For `u ∈ 𝒱₁` (so `L₁u = 0` by `hqp`), the `canRHS` at `wt = 1` collapses to its single `j = 0`
term: `canRHS u a b 1 n = − canBilin(a, u₍−n₎ b)`. -/
theorem canRHS_wt1 (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {u : V} (hu : u ∈ W.grading 1) (a b : V) (n : ℤ) :
    canRHS hne u a b 1 n = - canBilin W hne a (W.smul u (-n) b) := by
  rw [canRHS, show ((1 : ℤ).toNat + 1) = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
  rw [pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    Nat.cast_zero, sub_zero]
  rw [pow_one, hqp u hu, PreVertexAlgebra.smul_zero_left, map_zero, smul_zero, add_zero]
  rw [show (2 * (1 : ℤ) - n - 2) = -n by ring, zpow_one, neg_one_smul]

/-! ### Vanishing helpers for `matchDiff`/`canDiff`. -/

theorem canDiff_zero_left (hne : W.vacuum ≠ 0) (u b : V) (wt n : ℤ) :
    canDiff hne u 0 b wt n = 0 := by
  rw [canDiff, PreVertexAlgebra.smul_zero_right, map_zero, LinearMap.zero_apply,
    canRHS_zero_left, sub_zero]

theorem canDiff_zero_right (hne : W.vacuum ≠ 0) (u a : V) (wt n : ℤ) :
    canDiff hne u a 0 wt n = 0 := by
  rw [canDiff, map_zero, canRHS_zero_right, sub_zero]

theorem matchDiff_eq_zero_of_neg_q (hne : W.vacuum ≠ 0) {wt p q : ℤ} (hq : q < 0) {u a b : V}
    (hb : b ∈ W.grading q) : matchDiff hne wt p q u a b = 0 := by
  rw [eq_zero_of_mem_neg_grading W hq hb, matchDiff, canDiff_zero_right]

/-! ### The transposed (lever) form of `canBilin` on grade-matched vectors. -/

/-- **The lever-transposed form of `adjPair` on grade-matched vectors.**  For `a ∈ 𝒱_p`, `w ∈ 𝒱_p`,
applying `vacCoord_smul_symm` to each summand of `adjPair p a w` swaps `(L₁ʲa)` and `w`:
`adjPair p a w = (-1)^p ∑_{j≤p} (1/j!) sgn(j-2p) vacCoord(w₍2p-1-j₎(L₁ʲa))`. -/
theorem adjPair_transpose (hne : W.vacuum ≠ 0) {p : ℤ} {a w : V}
    (ha : a ∈ W.grading p) (hw : w ∈ W.grading p) :
    adjPair W hne p a w
      = (-1 : ℂ) ^ p • ∑ j ∈ Finset.range (p.toNat + 1), ((j.factorial : ℂ)⁻¹) •
          ((sgn (((j : ℤ)) - 2 * p)) • vacCoord W hne (W.smul w (2 * p - 1 - (j : ℤ)) (((W.L 1) ^ j) a))) := by
  rw [adjPair]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hLa : ((W.L 1) ^ j) a ∈ W.grading (p - (j : ℤ)) := L_one_pow_mem W ha j
  rw [vacCoord_smul_symm hne hLa hw (2 * p - 1 - (j : ℤ))]
  rw [show (-(2 * p - 1 - (j : ℤ)) - 1 : ℤ) = (j : ℤ) - 2 * p by ring]

/-! ## The `q`-direction reduction of `CanDiagonal` to the resonant per-grade closure `canPStep`. -/

/-- The matching-mode diagonal at a fixed weight `wt` and target grade `q`. -/
def CanDiagAt (hne : W.vacuum ≠ 0) (wt q : ℤ) : Prop :=
  ∀ (p : ℤ) (u a b : V), u ∈ W.grading wt → a ∈ W.grading p → b ∈ W.grading q →
    matchDiff hne wt p q u a b = 0

/-- The **pure `p`-recursion residual** for `canBilin`: at a fixed weight `wt` and grade `q ≥ 0`,
*given* the diagonal at every lower grade `q' < q`, the diagonal holds at `q`.  This is the precise
remaining content (the resonant `p`-recursion closure within a single grade — the Li Prop 2.6
two-point computation), to be discharged by the lever `vacCoord_smul_symm`/`adjPair_transpose`. -/
def CanPStep (hne : W.vacuum ≠ 0) : Prop :=
  ∀ (wt q : ℤ), 0 ≤ wt → 0 ≤ q → (∀ q' : ℤ, q' < q → CanDiagAt hne wt q') → CanDiagAt hne wt q

/-- `CanDiagAt` below the floor is automatic. -/
theorem canDiagAt_of_neg (hne : W.vacuum ≠ 0) {wt q : ℤ} (hq : q < 0) : CanDiagAt hne wt q := by
  intro p u a b _ _ hb
  exact matchDiff_eq_zero_of_neg_q hne hq hb

/-- **The upward-`q` reduction.** `CanPStep` discharges the whole `q`-direction. -/
theorem canDiagAt_of_pstep (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) (hP : CanPStep hne) {wt : ℤ} (hwt : 0 ≤ wt) :
    ∀ q : ℤ, CanDiagAt hne wt q := by
  have key : ∀ N : ℕ, ∀ q : ℤ, q.toNat ≤ N → CanDiagAt hne wt q := by
    intro N
    induction N with
    | zero =>
        intro q hqN
        rcases lt_or_ge q 0 with hqneg | hq0
        · exact canDiagAt_of_neg hne hqneg
        · have hq : q = 0 := by omega
          subst hq
          exact hP wt 0 hwt le_rfl (fun q' hq' => canDiagAt_of_neg hne (by omega))
    | succ M ih =>
        intro q hqN
        rcases lt_or_ge q 0 with hqneg | hq0
        · exact canDiagAt_of_neg hne hqneg
        · refine hP wt q hwt hq0 (fun q' hq' => ?_)
          rcases lt_or_ge q' 0 with hq'neg | hq'0
          · exact canDiagAt_of_neg hne hq'neg
          · exact ih q' (by omega)
  intro q
  exact key q.toNat q le_rfl

/-- **Full `CanDiagonal` from the `p`-recursion residual `CanPStep`.** -/
theorem canDiagonal_of_pstep (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) (hP : CanPStep hne) :
    CanDiagonal hne := by
  intro wt p q u a b hu ha hb
  rcases lt_or_ge wt 0 with hwt | hwt
  · have hu0 : u = 0 := eq_zero_of_mem_neg_grading W hwt hu
    subst hu0
    rw [PreVertexAlgebra.smul_zero_left, map_zero, LinearMap.zero_apply,
      canRHS, Finset.sum_eq_zero (fun j _ => by
        rw [map_zero, PreVertexAlgebra.smul_zero_left, map_zero, smul_zero]), smul_zero]
  · have hdiag := canDiagAt_of_pstep hne hqp hP hwt q p u a b hu ha hb
    rw [matchDiff, canDiff, sub_eq_zero] at hdiag
    exact hdiag

/-- **`canDiagonal_holds`, reduced to the resonant per-grade residual `CanPStep`.**
The whole `q`-direction is discharged by the native `L₋₁`-covariance recursion (`matchDiff_rec`),
isolating the entire remaining content into `CanPStep` (the resonant `p`-recursion closure within a
grade — the genuine Li Prop 2.6 two-point computation). -/
theorem canDiagonal_holds_of_pstep (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) (hP : CanPStep hne) :
    CanDiagonal hne :=
  canDiagonal_of_pstep hne hqp hP


/-! ## The weight-1 current zero-mode skew-adjointness (the affine FHL fragment, `n=0`).

For a weight-1 current `u ∈ 𝒱₁` (so `L₁u=0` by `hqp`), the charge `o(u)=u₍₀₎` is **skew-adjoint** for
the canonical form: `canBilin(u₍₀₎a, b) = − canBilin(a, u₍₀₎b)` (`canBilin_wt1_zero_mode_adj`). This is
the clean `n=0` slice of the weight-1 current skew-adjointness (`canBilin(u₍ₙ₎a,b) = −canBilin(a,u₍−n₎b)`):
at the zero mode the two FHL obstructions both trivialise — the bracket `[L₁,u₍₀₎]=0·u₍₁₎=0` and the
zero-mode derivation `(u₍₀₎X)₍ₘ₎b = u₍₀₎(X₍ₘ₎b) − X₍ₘ₎(u₍₀₎b)` with `vacCoord(u₍₀₎·)|_{𝒱₀}=0`. The
general-`n` case is the Li Prop 2.6 two-point computation (the matching-mode `vacCoord` identity,
not proved in this file).
Also banks the second-slot recursion `canBilin_mode_lower_right` and the combined `Dform_rec`. -/

/-- The obstruction `D(n,a,b) := canBilin(u₍ₙ₎a, b) + canBilin(a, u₍₋ₙ₎b)`. -/
noncomputable def Dform (hne : W.vacuum ≠ 0) (u : V) (n : ℤ) (a b : V) : ℂ :=
  canBilin W hne (W.smul u n a) b + canBilin W hne a (W.smul u (-n) b)

/-! ## Bilinearity of `Dform` in `a` and `b` (for fixed `u, n`). -/

theorem Dform_add_left (hne : W.vacuum ≠ 0) (u : V) (n : ℤ) (a₁ a₂ b : V) :
    Dform hne u n (a₁ + a₂) b = Dform hne u n a₁ b + Dform hne u n a₂ b := by
  simp only [Dform, PreVertexAlgebra.smul_add_right, map_add, LinearMap.add_apply]
  ring


theorem Dform_zero_left (hne : W.vacuum ≠ 0) (u : V) (n : ℤ) (b : V) :
    Dform hne u n 0 b = 0 := by
  simp only [Dform, PreVertexAlgebra.smul_zero_right, map_zero, LinearMap.zero_apply, add_zero]

theorem Dform_add_right (hne : W.vacuum ≠ 0) (u : V) (n : ℤ) (a b₁ b₂ : V) :
    Dform hne u n a (b₁ + b₂) = Dform hne u n a b₁ + Dform hne u n a b₂ := by
  simp only [Dform, PreVertexAlgebra.smul_add_right, map_add]
  ring

theorem Dform_zero_right (hne : W.vacuum ≠ 0) (u : V) (n : ℤ) (a : V) :
    Dform hne u n a 0 = 0 := by
  simp only [Dform, PreVertexAlgebra.smul_zero_right, map_zero, add_zero]

/-! ## The two matched covariance recursions, lowering the mode `n → n−1`.

(I) [= `canBilin_mode_lower`, first slot]:
    `n • canBilin(u₍ₙ₋₁₎a, b) = canBilin(u₍ₙ₎(L₋₁a), b) − canBilin(u₍ₙ₎a, L₁b)`.
(II) [second slot, derived here from `L1_bracket_smul` + `canBilin_Lneg1_adj`]:
    `n • canBilin(a, u₍₋₍ₙ₋₁₎₎b) = canBilin(L₋₁a, u₍₋ₙ₎b) − canBilin(a, u₍₋ₙ₎(L₁b))`.
-/

/-- **Recursion (II)** — the second-slot mode-lowering, for `u ∈ 𝒱₁` (so `L₁u=0`).
`n • canBilin(a, u₍₋₍ₙ₋₁₎₎b) = canBilin(L₋₁a, u₍₋ₙ₎b) − canBilin(a, u₍₋ₙ₎(L₁b))`. -/
theorem canBilin_mode_lower_right (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {u : V} (hu : u ∈ W.grading 1) (a b : V) (n : ℤ) :
    (n : ℂ) • canBilin W hne a (W.smul u (-(n - 1)) b)
      = canBilin W hne (W.L (-1) a) (W.smul u (-n) b)
        - canBilin W hne a (W.smul u (-n) (W.L 1 b)) := by
  -- `L1_bracket_smul` at v=u (w=1), s=-n, b:  L1(u₍₋ₙ₎b) - u₍₋ₙ₎(L1 b) = (2-(-n)-2)•u₍₋ₙ₊₁₎b + (L1 u)₍₋ₙ₎b
  have hbr := W.L1_bracket_smul hu (-n) b
  rw [hqp u hu, PreVertexAlgebra.smul_zero_left, add_zero] at hbr
  -- hbr : L1(u₍₋ₙ₎b) - u₍₋ₙ₎(L1 b) = (2*1 - (-n) - 2) • u₍₋ₙ₊₁₎b
  -- coefficient 2*1 - (-n) - 2 = n
  have hcoeff : (2 * ((1 : ℤ) : ℂ) - ((-n : ℤ) : ℂ) - 2) = (n : ℂ) := by push_cast; ring
  rw [hcoeff] at hbr
  -- so  n • u₍₋ₙ₊₁₎b = L1(u₍₋ₙ₎b) - u₍₋ₙ₎(L1 b);  note -n+1 = -(n-1)
  have hidx : (-n + 1 : ℤ) = -(n - 1) := by ring
  rw [hidx] at hbr
  -- pair with canBilin(a, ·)
  have hpair : (n : ℂ) • canBilin W hne a (W.smul u (-(n - 1)) b)
      = canBilin W hne a (W.L 1 (W.smul u (-n) b)) - canBilin W hne a (W.smul u (-n) (W.L 1 b)) := by
    rw [← map_sub]
    have := congrArg (fun x => canBilin W hne a x) hbr.symm
    simp only at this
    rw [map_smul] at this
    rw [this]
  rw [hpair]
  congr 1
  -- canBilin(a, L1(u₍₋ₙ₎b)) = canBilin(L₋₁a, u₍₋ₙ₎b)
  rw [← canBilin_Lneg1_adj hne hqp a (W.smul u (-n) b)]

/-- **The combined `Dform` covariance recursion** (valid for ALL `a, b`), for `u ∈ 𝒱₁`:
`n • Dform(n−1, a, b) = Dform(n, L₋₁a, b) − Dform(n, a, L₁b)`. -/
theorem Dform_rec (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {u : V} (hu : u ∈ W.grading 1) (a b : V) (n : ℤ) :
    (n : ℂ) • Dform hne u (n - 1) a b
      = Dform hne u n (W.L (-1) a) b - Dform hne u n a (W.L 1 b) := by
  have hI := canBilin_mode_lower hne hqp u a b n
  have hII := canBilin_mode_lower_right hne hqp hu a b n
  simp only [Dform, smul_add]
  -- LHS = n•canBilin(u₍ₙ₋₁₎a,b) + n•canBilin(a, u₍₋₍ₙ₋₁₎₎b)
  rw [hI, hII]
  ring

/-! ## The `n = 0` BASE CASE — the zero mode `u₍₀₎` of a weight-1 current is skew-adjoint.

This is the cleanest case (the zero mode preserves grading), proved DIRECTLY via:
  • `L₁(u₍₀₎x) = u₍₀₎(L₁x)`  (the V1 bracket `[L₁,u₍₀₎] = 0·u₍₁₎ = 0`), hence `L₁ⁱ(u₍₀₎a)=u₍₀₎(L₁ⁱa)`,
  • the zero-mode derivation `(u₍₀₎v)₍ₘ₎w = u₍₀₎(v₍ₘ₎w) − v₍ₘ₎(u₍₀₎w)` (`zeroMode_isDerivation`),
  • `vacCoord(u₍₀₎X) = 0` for `X ∈ 𝒱₀` (since `X = c𝟙` and `u₍₀₎𝟙 = 0`).
-/

/-- For `u ∈ 𝒱₁` (so `L₁u=0`): `L₁(u₍₀₎a) = u₍₀₎(L₁a)` (the `m=0` bracket has no `u₍₁₎` term). -/
theorem L1_u0 (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    {u : V} (hu : u ∈ W.grading 1) (a : V) :
    W.L 1 (W.smul u 0 a) = W.smul u 0 (W.L 1 a) := by
  have hbr := W.L1_bracket_smul hu 0 a
  rw [hqp u hu, PreVertexAlgebra.smul_zero_left, add_zero,
    show (2 * ((1:ℤ):ℂ) - ((0:ℤ):ℂ) - 2) = (0:ℂ) by push_cast; ring, zero_smul] at hbr
  -- hbr : L₁(u₍₀₎a) − u₍₀₎(L₁a) = 0
  linear_combination (norm := module) hbr

/-- Iterated: `L₁ⁱ(u₍₀₎a) = u₍₀₎(L₁ⁱa)`. -/
theorem L1pow_u0 (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    {u : V} (hu : u ∈ W.grading 1) (a : V) (i : ℕ) :
    (W.L 1 ^ i) (W.smul u 0 a) = W.smul u 0 ((W.L 1 ^ i) a) := by
  induction i generalizing a with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih a, L1_u0 hqp hu, ← Module.End.mul_apply, ← pow_succ']

/-- `vacCoord(u₍₀₎X) = 0` for `X ∈ 𝒱₀` (so `X = c·𝟙`, and `u₍₀₎𝟙 = 0`). -/
theorem vacCoord_u0_grade0 (hne : W.vacuum ≠ 0) {u : V} {X : V} (hX : X ∈ W.grading 0) :
    vacCoord W hne (W.smul u 0 X) = 0 := by
  rw [W.vacuum_grade, Submodule.mem_span_singleton] at hX
  obtain ⟨c, rfl⟩ := hX
  rw [PreVertexAlgebra.smul_smul_right, PreVertexAlgebra.smul_vacuum_zero, smul_zero, map_zero]

/-- **The key term-wise identity for the zero mode.** For `u ∈ 𝒱₁`, `a ∈ 𝒱_q`, `b ∈ 𝒱_q`, every
summand of `adjPair q (u₍₀₎a) b` equals minus the corresponding summand of `adjPair q a (u₍₀₎b)`:
  `vacCoord((L₁ⁱ(u₍₀₎a))₍2q-1-i₎b) = − vacCoord((L₁ⁱa)₍2q-1-i₎(u₍₀₎b))`.
Proof: `L₁ⁱ(u₍₀₎a) = u₍₀₎(L₁ⁱa)`; the derivation `(u₍₀₎X)₍ₘ₎b = u₍₀₎(X₍ₘ₎b) − X₍ₘ₎(u₍₀₎b)`
with `X = L₁ⁱa`; and `vacCoord(u₍₀₎(X₍ₘ₎b)) = 0` since `X₍ₘ₎b ∈ 𝒱₀`. -/
theorem u0_summand (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {u : V} (hu : u ∈ W.grading 1)
    {q : ℤ} {a : V} (ha : a ∈ W.grading q) {b : V} (hb : b ∈ W.grading q) (i : ℕ) :
    vacCoord W hne (W.smul ((W.L 1 ^ i) (W.smul u 0 a)) (2 * q - 1 - (i : ℤ)) b)
      = - vacCoord W hne (W.smul ((W.L 1 ^ i) a) (2 * q - 1 - (i : ℤ)) (W.smul u 0 b)) := by
  rw [L1pow_u0 hqp hu a i]
  -- (u₍₀₎(L₁ⁱa))₍ₘ₎b = u₍₀₎((L₁ⁱa)₍ₘ₎b) − (L₁ⁱa)₍ₘ₎(u₍₀₎b)
  set m : ℤ := 2 * q - 1 - (i : ℤ)
  set X : V := (W.L 1 ^ i) a with hX
  have hderiv := W.zeroMode_isDerivation u X b m
  -- hderiv : u₍₀₎(X₍ₘ₎b) − X₍ₘ₎(u₍₀₎b) = (u₍₀₎X)₍ₘ₎b
  have hkey : W.smul (W.smul u 0 X) m b
      = W.smul u 0 (W.smul X m b) - W.smul X m (W.smul u 0 b) := hderiv.symm
  rw [hkey, map_sub]
  -- vacCoord(u₍₀₎(X₍ₘ₎b)) = 0 since X₍ₘ₎b ∈ 𝒱₀
  have hXmem : X ∈ W.grading (q - (i : ℤ)) := by rw [hX]; exact L_one_pow_mem W ha i
  have hXmb : W.smul X m b ∈ W.grading 0 := by
    have h := W.smul_mem_grading hXmem hb m
    rwa [show (q - (i : ℤ) + q - m - 1 : ℤ) = 0 by rw [show m = 2 * q - 1 - (i:ℤ) from rfl]; ring] at h
  rw [vacCoord_u0_grade0 hne hXmb, zero_sub]

/-- **The `n=0` base case, homogeneous-diagonal.** For `u ∈ 𝒱₁`, `a, b ∈ 𝒱_q`:
`canBilin(u₍₀₎a, b) = − canBilin(a, u₍₀₎b)`.  Sum `u0_summand` over `i`. -/
theorem n0_diag (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {u : V} (hu : u ∈ W.grading 1)
    {q : ℤ} {a : V} (ha : a ∈ W.grading q) {b : V} (hb : b ∈ W.grading q) :
    canBilin W hne (W.smul u 0 a) b = - canBilin W hne a (W.smul u 0 b) := by
  -- u₍₀₎a ∈ 𝒱_q, u₍₀₎b ∈ 𝒱_q
  have hu0a : W.smul u 0 a ∈ W.grading q := by
    have h := W.smul_mem_grading hu ha 0
    rwa [show (1 + q - 0 - 1 : ℤ) = q by ring] at h
  rw [canBilin_homog W hne hu0a b, canBilin_homog W hne ha (W.smul u 0 b)]
  rw [neg_neg]
  -- goal: -adjPair q (u₀a) b = adjPair q a (u₀b)
  rw [adjPair, adjPair]
  -- rewrite each LHS summand by u0_summand
  have hsum : (∑ i ∈ Finset.range (q.toNat + 1), ((i.factorial : ℂ)⁻¹) •
        vacCoord W hne (W.smul ((W.L 1 ^ i) (W.smul u 0 a)) (2 * q - 1 - (i : ℤ)) b))
      = - ∑ i ∈ Finset.range (q.toNat + 1), ((i.factorial : ℂ)⁻¹) •
        vacCoord W hne (W.smul ((W.L 1 ^ i) a) (2 * q - 1 - (i : ℤ)) (W.smul u 0 b)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [u0_summand hne hqp hu ha hb i, smul_neg]
  rw [hsum, smul_neg, neg_neg]

/-! ## Off-diagonal reduction: away from the matching mode `n = p−q` the target is trivial. -/

/-- Off the matching mode `n ≠ p−q`, both sides of the target vanish (`canBilin_offdiag`). -/
theorem target_offdiag (hne : W.vacuum ≠ 0)
    {u : V} (hu : u ∈ W.grading 1) {a : V} {p : ℤ} (ha : a ∈ W.grading p)
    {b : V} {q : ℤ} (hb : b ∈ W.grading q) (n : ℤ) (hn : n ≠ p - q) :
    canBilin W hne (W.smul u n a) b = - canBilin W hne a (W.smul u (-n) b) := by
  have hmemL : W.smul u n a ∈ W.grading (1 + p - n - 1) := W.smul_mem_grading hu ha n
  have hmemR : W.smul u (-n) b ∈ W.grading (1 + q - (-n) - 1) := W.smul_mem_grading hu hb (-n)
  rw [canBilin_offdiag hne hmemL hb (by omega : 1 + p - n - 1 ≠ q),
      canBilin_offdiag hne ha hmemR (by omega : p ≠ 1 + q - (-n) - 1), neg_zero]

/-! ## The `n = 0` skew-adjointness on ALL of `V` (lift `n0_diag` by bilinearity + offdiag). -/

/-- **`n = 0` zero-mode skew-adjointness for ALL `a, b`** (not just homogeneous).
`canBilin(u₍₀₎a, b) = − canBilin(a, u₍₀₎b)` for every weight-1 current `u`. -/
theorem canBilin_wt1_zero_mode_adj (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {u : V} (hu : u ∈ W.grading 1) (a b : V) :
    canBilin W hne (W.smul u 0 a) b = - canBilin W hne a (W.smul u 0 b) := by
  -- reduce `a` to homogeneous via the internal direct sum
  have hatop : a ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading (motive := fun a =>
      ∀ b : V, canBilin W hne (W.smul u 0 a) b = - canBilin W hne a (W.smul u 0 b)) hatop ?_ ?_ ?_ b
  · intro p a ha b
    -- reduce `b` to homogeneous
    have hbtop : b ∈ ⨆ i, W.grading i := by
      rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
    refine Submodule.iSup_induction W.grading (motive := fun b =>
        canBilin W hne (W.smul u 0 a) b = - canBilin W hne a (W.smul u 0 b)) hbtop ?_ ?_ ?_
    · intro q b hb
      rcases eq_or_ne p q with hpq | hpq
      · subst hpq; exact n0_diag hne hqp hu ha hb
      · -- off-diagonal in grade: both sides vanish (n=0, but p≠q means p-0 ≠ q)
        exact target_offdiag hne hu ha hb 0 (by omega : (0:ℤ) ≠ p - q)
    · show canBilin W hne (W.smul u 0 a) 0 = - canBilin W hne a (W.smul u 0 0)
      rw [PreVertexAlgebra.smul_zero_right, map_zero, map_zero, neg_zero]
    · intro b₁ b₂ h₁ h₂
      show canBilin W hne (W.smul u 0 a) (b₁ + b₂) = - canBilin W hne a (W.smul u 0 (b₁ + b₂))
      rw [PreVertexAlgebra.smul_add_right, map_add, map_add, h₁, h₂, neg_add]
  · intro b
    show canBilin W hne (W.smul u 0 0) b = - canBilin W hne 0 (W.smul u 0 b)
    simp
  · intro a₁ a₂ h₁ h₂ b
    show canBilin W hne (W.smul u 0 (a₁ + a₂)) b = - canBilin W hne (a₁ + a₂) (W.smul u 0 b)
    rw [PreVertexAlgebra.smul_add_right, map_add, LinearMap.add_apply, map_add, LinearMap.add_apply,
      h₁ b, h₂ b, neg_add]


/-! ## The weight-1 current skew-adjointness, all modes, grade-0 first slot (`Route A` grind).

Extends the `n=0` charge skew-adjointness to **all modes** `n` of a weight-1 current, with the first
argument a vacuum descendant (`a ∈ 𝒱₀`): `canBilin(u₍ₙ₎(c·𝟙), b) = − canBilin(c·𝟙, u₍−n₎b)`
(`canBilin_wt1_grade0_left_adj`). The two FHL obstructions are controlled here because the `e^{zL₁}`
tower on `a = c·𝟙` is trivial; the genuine remaining core is general `a ∈ 𝒱ₚ` (`p>0`), the full tower —
the Li Prop 2.6 two-point computation (not proved in this file). Provides the engines `L1pow_smul_neg1`, `vacCoord_u1_L1pow`,
`canBilin_Lneg1pow_adj` for that computation. -/
/-! ## Step 0: `matchDiff` at `wt = 1` IS `Dform` (homogeneous), and `Dform` vanishes off-grade. -/

/-- At `wt = 1`, for `u ∈ 𝒱₁`, `matchDiff 1 p q u a b = Dform hne u (p-q) a b`. -/
theorem matchDiff_wt1_eq_Dform (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {u : V} (hu : u ∈ W.grading 1)
    {p q : ℤ} (a b : V) :
    matchDiff hne 1 p q u a b = Dform hne u (p - q) a b := by
  rw [matchDiff, canDiff, canRHS_wt1 hne hqp hu, Dform,
    show (p + 1 - q - 1 : ℤ) = p - q by ring, sub_neg_eq_add]

/-! ## Step 1: the `L₁`-tower on the creation mode `u₍₋₁₎a` (for `u ∈ 𝒱₁`).

For `u ∈ 𝒱₁` (so `L₁u=0`), `L₁(u₍ₛ₎x) = u₍ₛ₎(L₁x) − s·u₍ₛ₊₁₎x` (the `L1_bracket_smul` tower with
`(L₁u)=0`).  At `s=−1`:  `L₁(u₍₋₁₎x) = u₍₋₁₎(L₁x) + u₍₀₎x`.  At `s=0`: `L₁(u₍₀₎x) = u₍₀₎(L₁x)`.
Iterating gives the closed form
  `L₁ᵏ(u₍₋₁₎a) = u₍₋₁₎(L₁ᵏa) + k·u₍₀₎(L₁^{k-1}a)`. -/

/-- `L₁(u₍₋₁₎x) = u₍₋₁₎(L₁x) + u₍₀₎x` for `u ∈ 𝒱₁`. -/
theorem L1_smul_neg1 (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    {u : V} (hu : u ∈ W.grading 1) (x : V) :
    W.L 1 (W.smul u (-1) x) = W.smul u (-1) (W.L 1 x) + W.smul u 0 x := by
  have hbr := W.L1_bracket_smul hu (-1) x
  rw [hqp u hu, PreVertexAlgebra.smul_zero_left, add_zero,
    show (2 * ((1:ℤ):ℂ) - ((-1:ℤ):ℂ) - 2) = (1:ℂ) by push_cast; ring, one_smul,
    show ((-1:ℤ) + 1) = 0 by ring] at hbr
  -- hbr : L₁(u₍₋₁₎x) − u₍₋₁₎(L₁x) = u₍₀₎x
  linear_combination (norm := module) hbr

/-- The closed `L₁`-tower on the creation mode:
`L₁ᵏ(u₍₋₁₎a) = u₍₋₁₎(L₁ᵏa) + k·u₍₀₎(L₁^{k-1}a)`.  (At `k=0` the second term has coefficient 0.) -/
theorem L1pow_smul_neg1 (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    {u : V} (hu : u ∈ W.grading 1) (a : V) (k : ℕ) :
    (W.L 1 ^ k) (W.smul u (-1) a)
      = W.smul u (-1) ((W.L 1 ^ k) a) + (k : ℂ) • W.smul u 0 ((W.L 1 ^ (k-1)) a) := by
  induction k with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_add, L1_smul_neg1 hqp hu, map_smul]
    -- L₁(u₍₋₁₎(L₁ᵐa)) = u₍₋₁₎(L₁^{m+1}a) + u₍₀₎(L₁ᵐa)
    -- L₁(u₍₀₎(L₁^{m-1}a)) = u₍₀₎(L₁(L₁^{m-1}a))   (since L₁ commutes with u₀)
    rw [L1_u0 hqp hu]
    -- now: u₍₋₁₎(L₁(L₁ᵐa)) + u₍₀₎(L₁ᵐa) + m•(u₍₀₎(L₁(L₁^{m-1}a)))
    have hpow : W.L 1 ((W.L 1 ^ m) a) = (W.L 1 ^ (m+1)) a := by
      rw [← Module.End.mul_apply, ← pow_succ']
    rw [hpow]
    -- handle m•(u₀(L₁(L₁^{m-1}a))) : for m≥1, L₁(L₁^{m-1}a)=L₁ᵐa; for m=0 the coefficient is 0
    have hcoeff : (m : ℂ) • W.smul u 0 (W.L 1 ((W.L 1 ^ (m-1)) a))
        = (m : ℂ) • W.smul u 0 ((W.L 1 ^ m) a) := by
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm; simp
      · congr 2
        rw [← Module.End.mul_apply, ← pow_succ', show m - 1 + 1 = m by omega]
    rw [hcoeff, show (m + 1 - 1) = m by omega]
    push_cast
    rw [show (W.L 1 * W.L 1 ^ m) = (W.L 1 ^ (m+1)) from (pow_succ' (W.L 1) m).symm]
    -- u₍₋₁₎(L₁^{m+1}a) + u₍₀₎(L₁ᵐa) + m•u₍₀₎(L₁ᵐa) = u₍₋₁₎(L₁^{m+1}a) + (m+1)•u₍₀₎(L₁ᵐa)
    rw [add_smul, one_smul]
    abel

/-! ## Step 2: `canBilin` against a grade-1 vector reads off the `u₍₁₎` mode (`u ∈ 𝒱₁`).

For `u ∈ 𝒱₁` and `b ∈ 𝒱₁`, `canBilin(u, b) = vacCoord(u₍₁₎b)`: the `adjPair 1`-sum has only its
`j = 0` term survive (`j = 1` is `(L₁u)₍₀₎b = 0` since `L₁u = 0`). -/
/-- `canBilin(𝟙, X) = − vacCoord(X)` for any `X` (the `a = 𝟙` row of the canonical form). -/
theorem canBilin_vacuum_left (hne : W.vacuum ≠ 0) (X : V) :
    canBilin W hne W.vacuum X = - vacCoord W hne X := by
  rw [canBilin_homog W hne W.vacuum_mem, adjPair, show ((0:ℤ).toNat + 1) = 1 from rfl,
    Finset.sum_range_one, pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one,
    inv_one, one_smul, Nat.cast_zero, zpow_zero, show (2 * (0:ℤ) - 1 - 0) = -1 by ring,
    PreVertexAlgebra.smul_vacuum_left, if_pos rfl, one_smul]

theorem canBilin_wt1_grade1 (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {u : V} (hu : u ∈ W.grading 1) (b : V) :
    canBilin W hne u b = vacCoord W hne (W.smul u 1 b) := by
  rw [canBilin_homog W hne hu, adjPair, show ((1:ℤ).toNat + 1) = 2 from rfl,
    Finset.sum_range_succ, Finset.sum_range_one]
  rw [pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    Nat.cast_zero, sub_zero, show (2 * (1:ℤ) - 1) = 1 by ring]
  rw [pow_one, hqp u hu, PreVertexAlgebra.smul_zero_left, map_zero, smul_zero, add_zero]
  rw [zpow_one, neg_one_smul, neg_neg]

/-! ## Step 3: the RESONANT matching-mode identity at target grade `q = 1` (mode `n = −1`).

The creation mode `u₍₋₁₎` of a weight-1 current is skew-adjoint on `𝒱₀ × 𝒱₁`:
  `canBilin(u₍₋₁₎a, b) = − canBilin(a, u₍₁₎b)`  for `u ∈ 𝒱₁`, `a ∈ 𝒱₀`, `b ∈ 𝒱₁`.
This is the first genuinely-new matching mode beyond the banked `n = 0`.  It is the unique resonant
point of the weight-1 `q = 1` grade (`p = q−1 = 0`), where the `L₁`-tower truncates after one step
and the troublesome inner modes `u₍ᵢ₎b` (`i ≥ 2`) land in negative grade hence vanish. -/
theorem canBilin_wt1_neg1_resonant (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {u : V} (hu : u ∈ W.grading 1)
    {a : V} (ha : a ∈ W.grading 0) {b : V} (_hb : b ∈ W.grading 1) :
    canBilin W hne (W.smul u (-1) a) b = - canBilin W hne a (W.smul u 1 b) := by
  -- a = c • 𝟙
  rw [W.vacuum_grade, Submodule.mem_span_singleton] at ha
  obtain ⟨c, rfl⟩ := ha
  -- u₍₋₁₎(c•𝟙) = c • (u₍₋₁₎𝟙) = c • u
  rw [PreVertexAlgebra.smul_smul_right, W.smul_vacuum_neg_one]
  -- LHS = c • canBilin(u, b)
  rw [map_smul, LinearMap.smul_apply]
  -- RHS: canBilin(c•𝟙, u₍₁₎b) = c • canBilin(𝟙, u₍₁₎b)
  rw [map_smul, LinearMap.smul_apply]
  -- canBilin(u, b) = vacCoord(u₍₁₎b)
  rw [canBilin_wt1_grade1 hne hqp hu b]
  -- canBilin(𝟙, X) = − vacCoord(X)   for any X
  rw [canBilin_vacuum_left hne (W.smul u 1 b)]
  -- c • vacCoord(u₁b) = − (c • (− vacCoord(u₁b)))
  rw [smul_neg, neg_neg]

/-! ## Step 3b: the `vacCoord` mode-raising telescope (`u ∈ 𝒱₁`).

`L₁(u₍ₛ₎c) = u₍ₛ₎(L₁c) − s·u₍ₛ₊₁₎c` and `vacCoord(L₁·) = 0` (under `L₁𝒱₁=0`) give the mode-raising
relation `vacCoord(u₍ₛ₎(L₁c)) = s·vacCoord(u₍ₛ₊₁₎c)`.  Iterating:
  `vacCoord(u₍ₛ₎(L₁ᵐc)) = (s)(s+1)…(s+m−1)·vacCoord(u₍ₛ₊ₘ₎c)`.
At `s = 1`:  `vacCoord(u₍₁₎(L₁ᵐc)) = m!·vacCoord(u₍ₘ₊₁₎c)`. -/

/-- `vacCoord(u₍ₛ₎(L₁c)) = s·vacCoord(u₍ₛ₊₁₎c)` for `u ∈ 𝒱₁`, under `L₁𝒱₁=0`. -/
theorem vacCoord_u_L1_shift (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {u : V} (hu : u ∈ W.grading 1) (s : ℤ) (c : V) :
    vacCoord W hne (W.smul u s (W.L 1 c)) = (s : ℂ) • vacCoord W hne (W.smul u (s+1) c) := by
  have hbr := W.L1_bracket_smul hu s c
  rw [hqp u hu, PreVertexAlgebra.smul_zero_left, add_zero] at hbr
  -- hbr : L₁(u₍ₛ₎c) − u₍ₛ₎(L₁c) = (2·1 − s − 2)·u₍ₛ₊₁₎c = (−s)·u₍ₛ₊₁₎c
  rw [show (2 * ((1:ℤ):ℂ) - (s:ℂ) - 2) = (-(s:ℂ)) by push_cast; ring] at hbr
  -- so u₍ₛ₎(L₁c) = L₁(u₍ₛ₎c) + s·u₍ₛ₊₁₎c
  have heq : W.smul u s (W.L 1 c) = W.L 1 (W.smul u s c) + (s : ℂ) • W.smul u (s+1) c := by
    have h2 : W.smul u s (W.L 1 c)
        = W.L 1 (W.smul u s c) - (-(s:ℂ)) • W.smul u (s+1) c := by
      rw [← hbr]; abel
    rw [h2, neg_smul, sub_neg_eq_add]
  rw [heq, map_add, vacCoord_L1_eq_zero hne hqp, zero_add, map_smul]

/-- Iterated: `vacCoord(u₍ₛ₎(L₁ᵐc)) = (∏_{t<m}(s+t))·vacCoord(u₍ₛ₊ₘ₎c)`.  We only need the `s=1`
specialization `vacCoord(u₍₁₎(L₁ᵐc)) = m!·vacCoord(u₍ₘ₊₁₎c)`, proved directly by induction. -/
theorem vacCoord_u1_L1pow (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {u : V} (hu : u ∈ W.grading 1) (m : ℕ) (c : V) :
    vacCoord W hne (W.smul u 1 ((W.L 1 ^ m) c))
      = (m.factorial : ℂ) • vacCoord W hne (W.smul u (m + 1 : ℤ) c) := by
  -- prove the general-`s` statement, then set s = 1
  suffices h : ∀ (s : ℤ) (c : V), vacCoord W hne (W.smul u s ((W.L 1 ^ m) c))
      = (∏ t ∈ Finset.range m, (s + (t : ℤ) : ℂ)) • vacCoord W hne (W.smul u (s + m : ℤ) c) by
    have := h 1 c
    rw [Finset.prod_congr rfl (fun t _ => by push_cast; ring : ∀ t ∈ Finset.range m,
        ((1 : ℤ) + (t : ℤ) : ℂ) = ((t : ℂ) + 1))] at this
    rw [this]
    congr 1
    · -- ∏_{t<m} (t+1) = m!
      rw [show (∏ t ∈ Finset.range m, ((t : ℂ) + 1)) = ((∏ t ∈ Finset.range m, (t + 1 : ℕ) : ℕ) : ℂ)
          by push_cast; rfl]
      congr 1
      rw [Finset.prod_range_add_one_eq_factorial]
    · rw [show ((1 : ℤ) + (m : ℤ)) = ((m : ℤ) + 1) by ring]
  intro s c
  induction m generalizing s c with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, vacCoord_u_L1_shift hne hqp hu s, ih (s+1)]
    rw [Finset.prod_range_succ' (fun t => (s + (t : ℤ) : ℂ)) k]
    rw [smul_smul]
    congr 1
    · rw [Finset.prod_congr rfl (fun t _ => by push_cast; ring : ∀ t ∈ Finset.range k,
        (((s + 1 : ℤ)) + (t : ℤ) : ℂ) = (s + ((t : ℤ) + 1)))]
      push_cast; ring
    · congr 2
      push_cast
      ring

/-! ## Step 3c: iterated `L₋₁`-adjunction and the `vacCoord` vanishing for non-positive `u`-modes. -/

/-- Iterated `L₋₁`-adjunction: `canBilin(L₋₁ᵐ u, b) = canBilin(u, L₁ᵐ b)`, under `L₁𝒱₁=0`. -/
theorem canBilin_Lneg1pow_adj (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) (u : V) (m : ℕ) (b : V) :
    canBilin W hne ((W.L (-1) ^ m) u) b = canBilin W hne u ((W.L 1 ^ m) b) := by
  induction m generalizing b with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, canBilin_Lneg1_adj hne hqp, ih]
    rw [show (W.L 1 ^ k) (W.L 1 b) = (W.L 1 ^ (k+1)) b by
      rw [← Module.End.mul_apply, ← pow_succ]]

/-- `vacCoord(u₍ₘ₎b) = 0` for `m ≤ 0`, `u ∈ 𝒱₁`: the grade-0 part of `u₍ₘ₎b` comes from the
grade-`m` part of `b`, which is `0` for `m < 0` (positivity), and from the grade-`0` part for `m=0`
where `u₍₀₎(c𝟙)=0` (creation).  Stated and proved by reduction to homogeneous `b`. -/
theorem vacCoord_u_nonpos_eq_zero (hne : W.vacuum ≠ 0) {u : V} (hu : u ∈ W.grading 1)
    {m : ℤ} (hm : m ≤ 0) (b : V) :
    vacCoord W hne (W.smul u m b) = 0 := by
  have hbtop : b ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading (motive := fun b =>
      vacCoord W hne (W.smul u m b) = 0) hbtop ?_ ?_ ?_
  · intro q b hb
    have hmem : W.smul u m b ∈ W.grading (1 + q - m - 1) := W.smul_mem_grading hu hb m
    rcases eq_or_ne (1 + q - m - 1) 0 with h0 | h0
    · -- grade 0: need q = m; since m ≤ 0, q ≤ 0. If q < 0, b = 0. If q = 0 then m = 0.
      rcases lt_or_ge q 0 with hq | hq
      · rw [eq_zero_of_mem_neg_grading W hq hb, PreVertexAlgebra.smul_zero_right, map_zero]
      · -- q ≥ 0 and 1+q-m-1 = 0 ⟹ q = m ≤ 0 ⟹ q = 0, m = 0
        have hqm : q = m := by omega
        have hq0 : q = 0 := by omega
        have hm0 : m = 0 := by omega
        subst hq0; subst hm0
        -- b ∈ 𝒱₀ ⟹ b = c𝟙 ⟹ u₍₀₎b = 0
        rw [W.vacuum_grade, Submodule.mem_span_singleton] at hb
        obtain ⟨c, rfl⟩ := hb
        rw [PreVertexAlgebra.smul_smul_right, PreVertexAlgebra.smul_vacuum_zero, smul_zero, map_zero]
    · exact vacCoord_of_mem_ne W hne h0 hmem
  · show vacCoord W hne (W.smul u m 0) = 0
    rw [PreVertexAlgebra.smul_zero_right, map_zero]
  · intro b₁ b₂ h₁ h₂
    show vacCoord W hne (W.smul u m (b₁ + b₂)) = 0
    rw [PreVertexAlgebra.smul_add_right, map_add, h₁, h₂, add_zero]

/-! ## Step 4: assemble — full weight-1 skew-adjointness on `𝒱₀ × 𝒱₁` (ALL modes `n`).

Combine the resonant point (`n = −1`, the matching mode for `a ∈ 𝒱₀`, `b ∈ 𝒱₁`) with the
off-grade vanishing (`target_offdiag`, every `n ≠ p − q = 0 − 1 = −1`).  Hence the weight-1
current is skew-adjoint at EVERY mode on `𝒱₀ × 𝒱₁` — a strict generalization of the banked
`n = 0` zero-mode case (it includes the creation mode `n = −1`). -/
theorem Dform_wt1_grade01_zero (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {u : V} (hu : u ∈ W.grading 1)
    {a : V} (ha : a ∈ W.grading 0) {b : V} (hb : b ∈ W.grading 1) (n : ℤ) :
    canBilin W hne (W.smul u n a) b = - canBilin W hne a (W.smul u (-n) b) := by
  rcases eq_or_ne n (-1) with hn | hn
  · subst hn
    rw [show (-(-1) : ℤ) = 1 by ring]
    exact canBilin_wt1_neg1_resonant hne hqp hu ha hb
  · -- off the matching mode n = p − q = 0 − 1 = −1
    exact target_offdiag hne hu ha hb n (by omega : n ≠ (0 : ℤ) - 1)

/-! ## Step 5: THE GENUINE PARTIAL — general `n` at `wt = 1`, first argument `a ∈ 𝒱₀`.

The weight-1 current `u ∈ 𝒱₁` is skew-adjoint at **every** mode `n ∈ ℤ` when the first argument is a
grade-0 vacuum descendant `a = c·𝟙`:
  `canBilin(u₍ₙ₎(c𝟙), b) = − canBilin(c𝟙, u₍₋ₙ₎b)`  for ALL `n` and ALL `b`.

This is a strict generalization of the banked `n = 0` zero-mode case in the **mode** direction (all
`n`, in particular all the creation modes `n ≤ −1`), at the cost of restricting the first slot to
`𝒱₀`.  Proof: both sides reduce to `c·vacCoord(u₍₋ₙ₎b)`.
* For `n ≥ 0`: `u₍ₙ₎𝟙 = 0` (creation), so LHS `= 0`; and the RHS `vacCoord(u₍₋ₙ₎b) = 0` since
  `−n ≤ 0` (`vacCoord_u_nonpos_eq_zero`).
* For `n ≤ −1` (set `m = −n−1 ≥ 0`): `u₍ₙ₎𝟙 = Tᵐu/m! = L₋₁ᵐu/m!` (`creation_pow`), so
  LHS `= (c/m!)·canBilin(L₋₁ᵐu, b) = (c/m!)·canBilin(u, L₁ᵐb)` (iterated `L₋₁`-adjunction)
  `= (c/m!)·vacCoord(u₍₁₎(L₁ᵐb))` (the grade-1 row) `= (c/m!)·m!·vacCoord(u₍ₘ₊₁₎b)`
  (the `vacCoord` telescope) `= c·vacCoord(u₍₋ₙ₎b)`, matching the RHS. -/
theorem canBilin_wt1_grade0_left_adj (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {u : V} (hu : u ∈ W.grading 1)
    (c : ℂ) (n : ℤ) (b : V) :
    canBilin W hne (W.smul u n (c • W.vacuum)) b
      = - canBilin W hne (c • W.vacuum) (W.smul u (-n) b) := by
  -- RHS: canBilin(c•𝟙, u₍₋ₙ₎b) = c • canBilin(𝟙, u₍₋ₙ₎b) = c • (− vacCoord(u₍₋ₙ₎b))
  rw [show canBilin W hne (c • W.vacuum) (W.smul u (-n) b)
        = c • canBilin W hne W.vacuum (W.smul u (-n) b) by rw [map_smul, LinearMap.smul_apply]]
  rw [canBilin_vacuum_left hne (W.smul u (-n) b), smul_neg, neg_neg]
  -- LHS: u₍ₙ₎(c•𝟙) = c•(u₍ₙ₎𝟙), so canBilin(u₍ₙ₎(c•𝟙), b) = c • canBilin(u₍ₙ₎𝟙, b)
  rw [PreVertexAlgebra.smul_smul_right, map_smul, LinearMap.smul_apply]
  congr 1
  -- canBilin(u₍ₙ₎𝟙, b) = vacCoord(u₍₋ₙ₎b)
  rcases lt_or_ge n 0 with hn | hn
  · -- n ≤ −1, set m = −n−1 ≥ 0, so n = −m−1 and u₍ₙ₎𝟙 = (1/m!)·L₋₁ᵐu (creation_pow)
    obtain ⟨m, hm⟩ : ∃ m : ℕ, n = -(m : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
    subst hm
    rw [show (-(-(m : ℤ) - 1)) = ((m : ℤ) + 1) by ring]
    rw [creation_pow W u m, T_eq_Lneg1, map_smul, LinearMap.smul_apply]
    -- canBilin((1/m!)·L₋₁ᵐu, b) = (1/m!) • canBilin(L₋₁ᵐu, b)
    rw [canBilin_Lneg1pow_adj hne hqp u m b]
    -- = (1/m!) • canBilin(u, L₁ᵐb) = (1/m!) • vacCoord(u₍₁₎(L₁ᵐb))
    rw [canBilin_wt1_grade1 hne hqp hu]
    rw [vacCoord_u1_L1pow hne hqp hu m b]
    -- (1/m!) • (m! • vacCoord(u₍ₘ₊₁₎b)) = vacCoord(u₍ₘ₊₁₎b); and −(−m−1) = m+1
    rw [smul_smul, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero m), one_smul]
  · -- n ≥ 0: u₍ₙ₎𝟙 = 0, and vacCoord(u₍₋ₙ₎b) = 0 since −n ≤ 0
    rw [W.toPreVertexAlgebra.smul_vacuum_nonneg u hn, map_zero, LinearMap.zero_apply]
    rw [vacCoord_u_nonpos_eq_zero hne hu (by omega : -n ≤ 0) b]



/-! ###############################################################################################
  Weight-1 FHL diagonal on every QUASI-PRIMARY state `a` (`L₁a = 0`), all modes `n`.

  GOAL `canBilin_wt1_quasiprimary_adj`:
    `canBilin(u₍ₙ₎a, b) = − canBilin(a, u₍−n₎b)`  for `u ∈ 𝒱₁` (`L₁u=0`), `a` quasi-primary.

  Result (this file, axiom-free, no `sorry`):
  * `L1_smul_qp` / `L1pow_smul_qp` — the genuinely-new reusable `e^{zL₁}`-tower COLLAPSE engine for a
    quasi-primary `a` and a weight-1 current `u`.
  * `canBilin_wt1_quasiprimary_adj_of_match` — the FULL target, reduced (by `b`-linearity, the
    off-grade vanishing `target_offdiag`, and the matching-mode core) to the SINGLE homogeneous
    resonant identity `QPMatch` at the matching mode `n = p − q`.
  * `qp_match_lhs_expand` / `qp_match_rhs_expand` — the two sides of `QPMatch` expanded to explicit
    `vacCoord` forms (so the remaining equation is fully pinned, below).

  REMAINING OBSTRUCTION = `QPMatch` = the genuine Li Prop 2.6 two-point computation (the project's
  flagged irreducible `CanPStep` core, here sharpened to the quasi-primary slice). By the two
  `*_expand` lemmas it is the explicit equation, with `n := p − q`:

    `−(−1)^q · ∑_{k=0}^{q} (1/k!)·(∏_{l<k}(−(n+l)))·vacCoord( (u₍n+k₎a)₍2q−1−k₎ b )`
        `=  (−1)^p · vacCoord( a₍2p−1₎(u₍−n₎b) )`.

  The single missing ingredient is the two-point reassociation of `(u₍n+k₎a)₍2q−1−k₎b` via the
  all-integer Borcherds iterate `mode_iterate`, whose `u`-first family `u₍·₎(a₍·₎b)` (finite by
  `vacCoord_u_nonpos_eq_zero`) sums to `0`, and whose `a`-first family `a₍·₎(u₍·₎b)` (finite by
  positivity, `u₍i₎b = 0` for `i > q`) telescopes to the single RHS term.  Consistency: at `q = p`
  (`n = 0`) `QPMatch` IS the banked `canBilin_wt1_zero_mode_adj`; for `q < 0` it is vacuous.
  ############################################################################################### -/

/-! ## Engine: the `L₁`-tower COLLAPSE (quasi-primary `a`, weight-1 current `u`). -/

/-- One-step collapse: `L₁(u₍ₘ₎a) = −m·u₍ₘ₊₁₎a`. -/
theorem L1_smul_qp (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    {u : V} (hu : u ∈ W.grading 1) {a : V} (hqpa : W.L 1 a = 0) (m : ℤ) :
    W.L 1 (W.smul u m a) = (-(m : ℂ)) • W.smul u (m + 1) a := by
  have hbr := W.L1_bracket_smul hu m a
  rw [hqp u hu, PreVertexAlgebra.smul_zero_left, add_zero, hqpa, PreVertexAlgebra.smul_zero_right,
    sub_zero, show (2 * ((1:ℤ):ℂ) - (m:ℂ) - 2) = (-(m:ℂ)) by push_cast; ring] at hbr
  exact hbr

/-- Iterated collapse: `L₁ᵏ(u₍ₙ₎a) = (∏_{l<k}(−(n+l)))·u₍ₙ₊ₖ₎a`. -/
theorem L1pow_smul_qp (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    {u : V} (hu : u ∈ W.grading 1) {a : V} (hqpa : W.L 1 a = 0) (n : ℤ) (k : ℕ) :
    (W.L 1 ^ k) (W.smul u n a)
      = (∏ l ∈ Finset.range k, (-((n : ℂ) + (l : ℤ)))) • W.smul u (n + k) a := by
  induction k with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, L1_smul_qp hqp hu hqpa,
      Finset.prod_range_succ, smul_smul,
      show (n + (m : ℤ) + 1) = (n + ((m : ℕ) + 1 : ℕ)) by push_cast; ring]
    congr 2
    push_cast; ring

/-! ## The matching-mode resonant identity `QPMatch` (the precise obstruction). -/

/-- `QPMatch` : the weight-1 quasi-primary diagonal AT the matching mode `n = p − q`. -/
def QPMatch (hne : W.vacuum ≠ 0) (u : V) : Prop :=
  ∀ {a : V} {p : ℤ}, a ∈ W.grading p → W.L 1 a = 0 → ∀ {b : V} {q : ℤ}, b ∈ W.grading q →
    canBilin W hne (W.smul u (p - q) a) b = - canBilin W hne a (W.smul u (-(p - q)) b)

/-- Verified LHS expansion of `QPMatch` (collapse engine on `adjPair q (u₍ₙ₎a) b`). -/
theorem qp_match_lhs_expand (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {u : V} (hu : u ∈ W.grading 1)
    {a : V} {p : ℤ} (ha : a ∈ W.grading p) (hqpa : W.L 1 a = 0)
    {b : V} {q : ℤ} (_hb : b ∈ W.grading q) :
    canBilin W hne (W.smul u (p - q) a) b
      = -((-1:ℂ)^q • ∑ k ∈ Finset.range (q.toNat + 1), ((k.factorial:ℂ)⁻¹) •
          ((∏ l ∈ Finset.range k, (-(((p - q : ℤ):ℂ) + (l:ℤ)))) •
            vacCoord W hne (W.smul (W.smul u ((p-q) + k) a) (2*q - 1 - (k:ℤ)) b))) := by
  have huna : W.smul u (p - q) a ∈ W.grading q := by
    have h := W.smul_mem_grading hu ha (p - q)
    rwa [show (1 + p - (p - q) - 1 : ℤ) = q by ring] at h
  rw [canBilin_homog W hne huna b, adjPair]
  congr 2
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [L1pow_smul_qp hqp hu hqpa (p - q) k, PreVertexAlgebra.smul_smul_left, map_smul]

/-- Verified RHS expansion of `QPMatch` (`L₁a=0` collapses `adjPair p a ·` to its `j=0` term). -/
theorem qp_match_rhs_expand (hne : W.vacuum ≠ 0)
    {a : V} {p : ℤ} (ha : a ∈ W.grading p) (hqpa : W.L 1 a = 0) {b : V} {q : ℤ} :
    - canBilin W hne a (W.smul u (-(p - q)) b)
      = (-1:ℂ)^p • vacCoord W hne (W.smul a (2*p - 1) (W.smul u (-(p-q)) b)) := by
  rw [canBilin_homog W hne ha, adjPair]
  rw [Finset.sum_eq_single 0]
  · rw [pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
      Nat.cast_zero, sub_zero, neg_neg]
  · intro j _ hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [pow_succ, Module.End.mul_apply, hqpa, map_zero, PreVertexAlgebra.smul_zero_left, map_zero,
      smul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-! ## Banked infrastructure toward `QPMatch`: finiteness of the `mode_iterate` body.

The remaining content of `QPMatch` is the two-point reassociation of `(u₍ℓ₎a)₍N₎b` via the
all-integer Borcherds iterate `mode_iterate` (an `∑ᶠ`).  To push the linear `vacCoord` through that
`∑ᶠ` (`map_finsum`) one needs the body's support finite; that is supplied here from the two
`smul_eventually_zero` bounds (`a₍N+i₎b = 0` and `u₍i₎b = 0` for large `i`). -/
theorem mode_iterate_body_support_finite
    {u : V} {a : V} {b : V} (ℓ N : ℤ) :
    (Function.support (fun i : ℕ => ((-1:ℂ)^i * gBinom ℓ i) •
      (W.smul u (ℓ - i) (W.smul a (N + i) b)
        - ((-1:ℂ)^ℓ) • W.smul a (ℓ + N - i) (W.smul u i b)))).Finite := by
  obtain ⟨Nab, hNab⟩ := W.toPreVertexAlgebra.smul_eventually_zero a b
  obtain ⟨Nub, hNub⟩ := W.toPreVertexAlgebra.smul_eventually_zero u b
  apply Set.Finite.subset (Set.finite_Iio ((max (Nab - N) Nub).toNat))
  intro i hi
  rw [Function.mem_support] at hi
  by_contra hc
  rw [Set.mem_Iio, not_lt] at hc
  apply hi
  have hge : (max (Nab - N) Nub : ℤ) ≤ (i : ℤ) := by
    rcases le_or_gt 0 (max (Nab - N) Nub) with h0 | h0
    · rw [← Int.toNat_of_nonneg h0]; exact_mod_cast hc
    · omega
  rw [hNab (N + i) (by omega), hNub i (by omega)]
  simp

/-! ## The full target, reduced axiom-free to `QPMatch`. -/

/-- **The weight-1 FHL diagonal on every quasi-primary `a`, all modes** — reduced to the
matching-mode resonant identity `QPMatch u` by `b`-linearity and off-grade vanishing. -/
theorem canBilin_wt1_quasiprimary_adj_of_match (hne : W.vacuum ≠ 0)
    {u : V} (hu : u ∈ W.grading 1) (hmatch : QPMatch hne u)
    {a : V} {p : ℤ} (ha : a ∈ W.grading p) (hqpa : W.L 1 a = 0) (n : ℤ) (b : V) :
    canBilin W hne (W.smul u n a) b = - canBilin W hne a (W.smul u (-n) b) := by
  have hbtop : b ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading (motive := fun b =>
      canBilin W hne (W.smul u n a) b = - canBilin W hne a (W.smul u (-n) b)) hbtop ?_ ?_ ?_
  · intro q b hb
    rcases eq_or_ne n (p - q) with hn | hn
    · subst hn; exact hmatch ha hqpa hb
    · exact target_offdiag hne hu ha hb n hn
  · show canBilin W hne (W.smul u n a) 0 = - canBilin W hne a (W.smul u (-n) 0)
    rw [PreVertexAlgebra.smul_zero_right, map_zero, map_zero, neg_zero]
  · intro b₁ b₂ h₁ h₂
    show canBilin W hne (W.smul u n a) (b₁ + b₂) = - canBilin W hne a (W.smul u (-n) (b₁ + b₂))
    rw [PreVertexAlgebra.smul_add_right, map_add, map_add, h₁, h₂, neg_add]

end VOA
