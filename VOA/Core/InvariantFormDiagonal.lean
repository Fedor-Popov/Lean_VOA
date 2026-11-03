/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.InvariantFormFHL
import VOA.Core.Borcherds

/-!
# FHL full invariance, sharpened to the single matching-mode diagonal identity

Building on `Core.InvariantFormFHL` (the skew-route adjoint identity `form_smul_skew`, the base
cases, and `isFullyInvariant_of_propagation`), this file reduces the would-be **general-`B`
full-invariance** statement `InvariantForm.IsFullyInvariant` (Gannon 5.1.11a) all the way down to a
single, sharply-localized residual — the **matching-mode diagonal identity** `DiagonalFHL`.

The genuine FHL covariance is proved on *both* sides of the mode-adjoint identity:

* **`L0_mode_comm` / `L1_mode_comm`** — the Virasoro-on-modes commutators
  `[L₀,u₍ₘ₎] = (L₋₁u)₍ₘ₊₁₎+(L₀u)₍ₘ₎`, `[L₁,u₍ₘ₎] = (L₋₁u)₍ₘ₊₂₎+2(L₀u)₍ₘ₊₁₎+(L₁u)₍ₘ₎` (off
  `commBound`/`mode_commutator`, the head-term `gBinom` collapse `finN_gBinom_collapse`).
* **`form_mode_lower`** — the LHS `(u₍ₙ₋₁₎a|b)` obeys an `L₋₁`-covariance recursion (off `L_comm_mode`
  + `virasoro_adj`).
* **`fhlInner_recursion`** — the FHL `e^{zL₁}(−z⁻²)^{L₀}` sum obeys the *same* `L₋₁`-covariance
  recursion (off `L1_bracket_smul`/`form_L1_term` + the mode-shift `smul_Lneg1_shift`).
* **`fhlDiff_recursion`** — hence the obstruction `D := (u₍ₙ₎a|b) − fhlRHS` obeys the homogeneous
  recursion; with the **off-diagonal vanishing** (`lhs_offdiag`/`fhlRHS_offdiag`, by
  `orthogonal_of_ne`) and bilinearity, `residual_of_diagonal` collapses the whole residual to the
  one non-orthogonal mode per homogeneous pair.

* **`isFullyInvariant_of_diagonal`** — full `IsFullyInvariant` from `DiagonalFHL B` alone.

## Status
**Delimited by a conditional obstruction.** Every reduction above is axiom-clean.
`Core.InvariantFormDelimitation.general_diagonalFHL_not_a_theorem` rules out a uniform
`DiagonalFHL B` only under `hqp` and an explicitly supplied nonsymmetric grade-one invariant-form
witness; it does not construct that witness.  The canonical form follows a different, completed
route through `Core.InvariantFormFHL2`.

## References
* Gannon §5.1.3, eq. (5.1.11a); Frenkel–Huang–Lepowsky [199]; Li [380].
-/

namespace VOA.VertexOperatorAlgebra

open scoped BigOperators
open Classical

variable {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- Collapse a `Fin N` sum of `gBinom (K:ℤ) j • g j` (nat top index `K`), where additionally
`g j = 0` for `K < j < N` (the high-mode OPE-vanishing), to the finite `Finset.range (K+1)` sum.
Both obstructions kill the tail: `gBinom (K:ℤ) j = 0` for `j > K`, and `g j = 0` is assumed for
the `[K+1, N)` window.  Robust to `N` smaller OR larger than `K+1`. -/
theorem finN_gBinom_collapse {M : Type*} [AddCommGroup M] [Module ℂ M] (K : ℕ) (N : ℕ)
    (g : ℕ → M) (hg : ∀ j, N ≤ j → g j = 0) :
    (∑ j : Fin N, gBinom (K : ℤ) (j : ℕ) • g (j : ℕ))
      = ∑ j ∈ Finset.range (K + 1), gBinom (K : ℤ) j • g j := by
  rw [Fin.sum_univ_eq_sum_range (fun j => gBinom (K : ℤ) j • g j) N]
  rcases Nat.lt_or_ge N (K + 1) with hNK | hNK
  · rw [← Finset.sum_range_add_sum_Ico _ (le_of_lt hNK)]
    have hzero : ∑ j ∈ Finset.Ico N (K + 1), gBinom (K : ℤ) j • g j = 0 := by
      refine Finset.sum_eq_zero (fun j hj => ?_)
      rw [Finset.mem_Ico] at hj
      rw [hg j hj.1, smul_zero]
    rw [hzero, add_zero]
  · rw [← Finset.sum_range_add_sum_Ico _ hNK]
    have hzero : ∑ j ∈ Finset.Ico (K + 1) N, gBinom (K : ℤ) j • g j = 0 := by
      refine Finset.sum_eq_zero (fun j hj => ?_)
      rw [Finset.mem_Ico] at hj
      rw [gBinom_natCast_eq_zero (by omega : K < j), zero_smul]
    rw [hzero, add_zero]

/-- **`[L₀, u₍ₘ₎]` Virasoro mode commutator** (operator form):
`[L₀, u₍ₘ₎] = (L₋₁u)₍ₘ₊₁₎ + (L₀u)₍ₘ₎`.  Here `u₍ₘ₎ = mode (W.Y u) m`. -/
theorem L0_mode_comm (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) (m : ℤ) :
    ⁅W.L 0, mode (W.Y u) m⁆
      = mode (W.Y (W.L (-1) u)) (m + 1) + mode (W.Y (W.L 0 u)) m := by
  obtain ⟨N, hzero, hcomm⟩ := commBound W W.conformalVector u 1 m
  have hL0 : W.L 0 = mode (W.Y W.conformalVector) 1 := by rw [L_def]; norm_num
  rw [hL0, hcomm]
  rw [show (gBinom (1 : ℤ)) = gBinom ((1 : ℕ) : ℤ) from by norm_num]
  rw [finN_gBinom_collapse 1 N
    (fun j => mode (W.Y (W.smul W.conformalVector (j : ℤ) u)) (1 + m - (j : ℤ)))
    (fun j hj => by simp only [hzero j hj, map_zero, mode_zero])]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  rw [gBinom_natCast_eq_choose (Nat.zero_le 1), gBinom_natCast_eq_choose (le_refl 1)]
  simp only [Nat.choose_self, Nat.cast_one, one_smul, Nat.cast_zero, Nat.choose_zero_right]
  have e0 : W.smul W.conformalVector (0 : ℤ) u = W.L (-1) u := by
    rw [PreVertexAlgebra.smul_def, L_def, show ((-1 : ℤ) + 1) = 0 by ring]
  have e1 : W.smul W.conformalVector (1 : ℤ) u = W.L 0 u := by
    rw [PreVertexAlgebra.smul_def, L_def, show ((0 : ℤ) + 1) = 1 by ring]
  rw [e0, e1, show (1 + m - (0 : ℤ)) = m + 1 by ring,
    show (1 + m - (1 : ℤ)) = m by ring, ← hL0]

/-- **`[L₁, u₍ₘ₎]` Virasoro mode commutator** (operator form):
`[L₁, u₍ₘ₎] = (L₋₁u)₍ₘ₊₂₎ + 2(L₀u)₍ₘ₊₁₎ + (L₁u)₍ₘ₎`. -/
theorem L1_mode_comm (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) (m : ℤ) :
    ⁅W.L 1, mode (W.Y u) m⁆
      = mode (W.Y (W.L (-1) u)) (m + 2) + (2 : ℂ) • mode (W.Y (W.L 0 u)) (m + 1)
          + mode (W.Y (W.L 1 u)) m := by
  obtain ⟨N, hzero, hcomm⟩ := commBound W W.conformalVector u 2 m
  have hL1 : W.L 1 = mode (W.Y W.conformalVector) 2 := by rw [L_def]; norm_num
  rw [hL1, hcomm]
  rw [show (gBinom (2 : ℤ)) = gBinom ((2 : ℕ) : ℤ) from by norm_num]
  rw [finN_gBinom_collapse 2 N
    (fun j => mode (W.Y (W.smul W.conformalVector (j : ℤ) u)) (2 + m - (j : ℤ)))
    (fun j hj => by simp only [hzero j hj, map_zero, mode_zero])]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  rw [gBinom_natCast_eq_choose (Nat.zero_le 2), gBinom_natCast_eq_choose (by norm_num : 1 ≤ 2),
    gBinom_natCast_eq_choose (le_refl 2)]
  simp only [Nat.choose_self, Nat.choose_zero_right, Nat.cast_one, one_smul,
    Nat.cast_zero, Nat.cast_ofNat]
  rw [show (Nat.choose 2 1 : ℂ) = 2 by norm_num]
  have e0 : W.smul W.conformalVector (0 : ℤ) u = W.L (-1) u := by
    rw [PreVertexAlgebra.smul_def, L_def, show ((-1 : ℤ) + 1) = 0 by ring]
  have e1 : W.smul W.conformalVector (1 : ℤ) u = W.L 0 u := by
    rw [PreVertexAlgebra.smul_def, L_def, show ((0 : ℤ) + 1) = 1 by ring]
  have e2 : W.smul W.conformalVector (2 : ℤ) u = W.L 1 u := by
    rw [PreVertexAlgebra.smul_def, L_def, show ((1 : ℤ) + 1) = 2 by ring]
  rw [e0, e1, e2, show (2 + m - (0 : ℤ)) = m + 2 by ring,
    show (2 + m - (1 : ℤ)) = m + 1 by ring, show (2 + m - (2 : ℤ)) = m by ring, ← hL1]

/-! ## The skew-transposed reformulation of `FullyInvariantAt` -/

/-- The **skew-route RHS** of the mode-adjoint identity (the value of `(u₍ₙ₎a|b)`, by
`form_smul_skew`). -/
noncomputable def skewRHS (B : InvariantForm W) (u a b : 𝒱) (n : ℤ) : ℂ :=
  ∑ᶠ j : ℕ, ((j.factorial : ℂ)⁻¹) • (sgn (-n - 1 - j)) •
    B.form (W.smul a (n + j) u) ((W.L 1 ^ j) b)

/-- The **FHL RHS** of the mode-adjoint identity (the target value at weight `wt`). -/
noncomputable def fhlRHS (B : InvariantForm W) (u a b : 𝒱) (wt n : ℤ) : ℂ :=
  (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) •
    B.form a (W.smul (((W.L 1) ^ j) u) (2 * wt - n - 2 - (j : ℤ)) b)

/-- **The skew-transposed reduction of `FullyInvariantAt`.**  Because `form_smul_skew` gives
`(u₍ₙ₎a|b) = skewRHS`, the per-weight FHL body `FullyInvariantAt B wt` is logically equivalent to
the pure residual identity `skewRHS = fhlRHS` for all `u ∈ 𝒱_wt`, `n, a, b`.  Fully axiom-free. -/
theorem fullyInvariantAt_iff_skew_eq_fhl (B : InvariantForm W) (wt : ℤ) :
    FullyInvariantAt B wt ↔
      ∀ (u : 𝒱), u ∈ W.grading wt → ∀ (n : ℤ) (a b : 𝒱),
        skewRHS B u a b n = fhlRHS B u a b wt n := by
  constructor
  · intro hFI u hu n a b
    rw [skewRHS, ← form_smul_skew B u a b n, fhlRHS, hFI u hu n a b]
  · intro hres u hu n a b
    rw [form_smul_skew B u a b n]
    have := hres u hu n a b
    rw [skewRHS, fhlRHS] at this
    rw [this]

/-! ## `L₋₁`-covariance recursion for the LHS (mode-lowering in `n`) -/

/-- The mode-lowering recursion as an operator identity:
`n • u₍ₙ₋₁₎ a = u₍ₙ₎ (L₋₁ a) − L₋₁ (u₍ₙ₎ a)`. -/
theorem smul_mode_lower (W : VertexOperatorAlgebra 𝒱) (u a : 𝒱) (n : ℤ) :
    (n : ℂ) • W.smul u (n - 1) a
      = W.smul u n (W.L (-1) a) - W.L (-1) (W.smul u n a) := by
  have h := L_comm_mode W u n
  have h2 := DFunLike.congr_fun h a
  rw [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply, LinearMap.smul_apply] at h2
  rw [← PreVertexAlgebra.smul_def, ← PreVertexAlgebra.smul_def, ← PreVertexAlgebra.smul_def] at h2
  rw [← Int.cast_smul_eq_zsmul ℂ (-n), Int.cast_neg] at h2
  rw [show (n : ℂ) • W.smul u (n - 1) a = -((-(n : ℂ)) • W.smul u (n - 1) a) by
        rw [neg_smul, neg_neg], ← h2]
  abel

/-- **Form-level `L₋₁`-covariance recursion** (the LHS mode-lowering):
`n·(u₍ₙ₋₁₎a|b) = (u₍ₙ₎(L₋₁a)|b) − (u₍ₙ₎a|L₁b)`.  Pairs `smul_mode_lower` against `b` and uses
`virasoro_adj` to move `L₋₁` to `L₁` on the other slot.  Unconditional. -/
theorem form_mode_lower (B : InvariantForm W) (u a b : 𝒱) (n : ℤ) :
    (n : ℂ) • B.form (W.smul u (n - 1) a) b
      = B.form (W.smul u n (W.L (-1) a)) b - B.form (W.smul u n a) (W.L 1 b) := by
  have h := smul_mode_lower W u a n
  apply_fun (fun x => B.form x b) at h
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, ← smul_eq_mul] at h
  rw [map_sub, LinearMap.sub_apply] at h
  rw [h]
  congr 1
  have hadj := B.virasoro_adj (-1) (W.smul u n a) b
  rw [show (-(-1) : ℤ) = 1 by ring] at hadj
  rw [hadj]

/-! ## The residual reduction: full FHL from the single skew=FHL identity -/

/-- The **residual FHL identity**: at every weight, the skew-route adjoint sum equals the FHL
`e^{zL₁}(−z⁻²)^{L₀}` adjoint sum.  This is the precise, fully-stripped remaining content of FHL
(`form_smul_skew` having discharged the LHS `(u₍ₙ₎a|b)`). -/
def ResidualFHL (B : InvariantForm W) : Prop :=
  ∀ (wt : ℤ) (u : 𝒱), u ∈ W.grading wt → ∀ (n : ℤ) (a b : 𝒱),
    skewRHS B u a b n = fhlRHS B u a b wt n

/-- **Full FHL from the residual identity.**  `ResidualFHL B` (the skew = FHL adjoint-sum identity
at every weight) discharges the propagation hypothesis, hence — through the already-built
`isFullyInvariant_of_propagation` — the full `IsFullyInvariant`.  Axiom-free. -/
theorem isFullyInvariant_of_residual (B : InvariantForm W) (hres : ResidualFHL B) :
    B.IsFullyInvariant := by
  apply isFullyInvariant_of_propagation B
  intro m _ih
  rw [fullyInvariantAt_iff_skew_eq_fhl B ((m : ℤ) + 1)]
  intro u hu n a b
  exact hres ((m : ℤ) + 1) u hu n a b

/-! ## The `fhlRHS` satisfies the SAME `L₋₁`-covariance recursion -/

/-- **Mode-shift identity** `(L₋₁v)₍s₎w = −s·v₍s−1₎w` (translation/VOA3, via `mode_Y_T`). -/
theorem smul_Lneg1_shift (W : VertexOperatorAlgebra 𝒱) (v w : 𝒱) (s : ℤ) :
    W.smul (W.L (-1) v) s w = (-s : ℂ) • W.smul v (s - 1) w := by
  rw [PreVertexAlgebra.smul_def, ← T_eq_Lneg1, mode_Y_T]
  rw [← Int.cast_smul_eq_zsmul ℂ (-s), Int.cast_neg, LinearMap.smul_apply,
    PreVertexAlgebra.smul_def]

/-- The **`L₁`-bracket on a homogeneous mode**, as a `smul` identity acted on `b`:
`L₁(v₍s₎b) − v₍s₎(L₁b) = (2w − s − 2)·v₍s+1₎b + (L₁v)₍s₎b` for `v ∈ 𝒱_w`. -/
theorem L1_bracket_smul (W : VertexOperatorAlgebra 𝒱) {w : ℤ} {v : 𝒱} (hv : v ∈ W.grading w)
    (s : ℤ) (b : 𝒱) :
    W.L 1 (W.smul v s b) - W.smul v s (W.L 1 b)
      = (2 * w - s - 2 : ℂ) • W.smul v (s + 1) b + W.smul (W.L 1 v) s b := by
  have hcomm := L1_mode_comm W v s
  have h2 := DFunLike.congr_fun hcomm b
  rw [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply] at h2
  rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.smul_apply] at h2
  rw [← PreVertexAlgebra.smul_def, ← PreVertexAlgebra.smul_def, ← PreVertexAlgebra.smul_def,
    ← PreVertexAlgebra.smul_def] at h2
  rw [h2]
  rw [W.L_zero_grading v hv]
  rw [smul_Lneg1_shift W v b (s + 2), show (s + 2 - 1 : ℤ) = s + 1 by ring]
  rw [PreVertexAlgebra.smul_smul_left]
  rw [← PreVertexAlgebra.smul_def]
  push_cast
  module

/-- **Form-level per-term `L₁`-covariance.**  Pairing `L1_bracket_smul` (acting on `b`) against
`(a|·)` and using `virasoro_adj`:
`(L₋₁a | v₍s₎b) − (a | v₍s₎(L₁b)) = (2w−s−2)·(a | v₍s+1₎b) + (a | (L₁v)₍s₎b)`. -/
theorem form_L1_term (B : InvariantForm W) {w : ℤ} {v : 𝒱} (hv : v ∈ W.grading w)
    (s : ℤ) (a b : 𝒱) :
    B.form (W.L (-1) a) (W.smul v s b) - B.form a (W.smul v s (W.L 1 b))
      = (2 * w - s - 2 : ℂ) • B.form a (W.smul v (s + 1) b)
          + B.form a (W.smul (W.L 1 v) s b) := by
  have hbr := L1_bracket_smul W hv s b
  apply_fun (fun x => B.form a x) at hbr
  rw [map_sub, map_add, map_smul, smul_eq_mul, ← smul_eq_mul] at hbr
  have hadj := B.virasoro_adj (-1) a (W.smul v s b)
  rw [show (-(-1) : ℤ) = 1 by ring] at hadj
  rw [← hadj] at hbr
  exact hbr

/-- The FHL inner sum `S(a,b,n) = ∑_{j≤wt} (1/j!) (a | (L₁ʲu)₍2wt−n−2−j₎ b)` (so
`fhlRHS = (−1)^wt • S`). -/
noncomputable def fhlInner (B : InvariantForm W) (u a b : 𝒱) (wt n : ℤ) : ℂ :=
  ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) •
    B.form a (W.smul (((W.L 1) ^ j) u) (2 * wt - n - 2 - (j : ℤ)) b)

/-- **The genuine FHL covariance recursion for the inner sum.**  For `u ∈ 𝒱_wt`,
`n·S(a,b,n−1) = S(L₋₁a,b,n) − S(a,L₁b,n)` — the same `L₋₁`-covariance the LHS obeys
(`form_mode_lower`). -/
theorem fhlInner_recursion (B : InvariantForm W) {wt : ℤ} (hwt : 0 ≤ wt) {u : 𝒱}
    (hu : u ∈ W.grading wt) (a b : 𝒱) (n : ℤ) :
    (n : ℂ) • fhlInner B u a b wt (n - 1)
      = fhlInner B u (W.L (-1) a) b wt n - fhlInner B u a (W.L 1 b) wt n := by
  set K := wt.toNat with hK
  have hvmem : ∀ j : ℕ, ((W.L 1) ^ j) u ∈ W.grading (wt - (j : ℤ)) := fun j => L_one_pow_mem W hu j
  have hLv : ∀ j : ℕ, W.L 1 (((W.L 1) ^ j) u) = ((W.L 1) ^ (j + 1)) u := by
    intro j; rw [pow_succ']; rfl
  have hvtop : ((W.L 1) ^ (K + 1)) u = 0 := by
    apply L_one_pow_eq_zero W hu
    rw [hK]; omega
  set P : ℕ → ℂ := fun j => B.form a (W.smul (((W.L 1) ^ j) u) (2 * wt - (n - 1) - 2 - (j : ℤ)) b)
    with hP
  rw [fhlInner]
  rw [fhlInner, fhlInner, ← Finset.sum_sub_distrib]
  have hterm : ∀ j ∈ Finset.range (K + 1),
      ((j.factorial : ℂ)⁻¹) • B.form (W.L (-1) a)
          (W.smul (((W.L 1) ^ j) u) (2 * wt - n - 2 - (j : ℤ)) b)
        - ((j.factorial : ℂ)⁻¹) • B.form a
          (W.smul (((W.L 1) ^ j) u) (2 * wt - n - 2 - (j : ℤ)) (W.L 1 b))
        = ((j.factorial : ℂ)⁻¹) • ((((n : ℂ) - j)) • P j)
          + ((j.factorial : ℂ)⁻¹) • B.form a
              (W.smul (((W.L 1) ^ (j + 1)) u) (2 * wt - n - 2 - (j : ℤ)) b) := by
    intro j _
    rw [← smul_sub]
    rw [form_L1_term B (hvmem j) (2 * wt - n - 2 - (j : ℤ)) a b]
    rw [hLv j, smul_add]
    congr 1
    rw [hP]
    have hcoeff : (2 * ((wt - (j : ℤ) : ℤ) : ℂ) - ((2 * wt - n - 2 - (j : ℤ) : ℤ) : ℂ) - 2)
        = ((n : ℂ) - j) := by push_cast; ring
    have hidx : (2 * wt - n - 2 - (j : ℤ) + 1 : ℤ) = (2 * wt - (n - 1) - 2 - (j : ℤ)) := by ring
    rw [hcoeff, hidx]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  have hQP : ∀ j : ℕ, B.form a (W.smul (((W.L 1) ^ (j + 1)) u) (2 * wt - n - 2 - (j : ℤ)) b)
      = P (j + 1) := by
    intro j; rw [hP]; congr 2; push_cast; ring
  rw [show (∑ j ∈ Finset.range (K + 1), ((j.factorial : ℂ)⁻¹) • B.form a
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

/-! ## Off-diagonal vanishing (grading) — the matching-mode reduction -/

/-- `fhlRHS` vanishes off the matching mode for homogeneous `a, b`: every FHL summand
`(a | (L₁ʲu)₍2wt−n−2−j₎ b)` is `0` by `orthogonal_of_ne` unless `n = p + wt − q − 1`. -/
theorem fhlRHS_offdiag (B : InvariantForm W) {wt p q : ℤ} {u a b : 𝒱}
    (hu : u ∈ W.grading wt) (ha : a ∈ W.grading p) (hb : b ∈ W.grading q)
    (n : ℤ) (hn : n ≠ p + wt - q - 1) :
    fhlRHS B u a b wt n = 0 := by
  rw [fhlRHS]
  rw [Finset.sum_eq_zero, smul_zero]
  intro j _
  have hvj : ((W.L 1) ^ j) u ∈ W.grading (wt - (j : ℤ)) := L_one_pow_mem W hu j
  have hmem : W.smul (((W.L 1) ^ j) u) (2 * wt - n - 2 - (j : ℤ)) b
      ∈ W.grading (n + q + 1 - wt) := by
    have h := W.smul_mem_grading hvj hb (2 * wt - n - 2 - (j : ℤ))
    rwa [show (wt - (j : ℤ) + q - (2 * wt - n - 2 - (j : ℤ)) - 1 : ℤ) = n + q + 1 - wt by ring] at h
  rw [B.orthogonal_of_ne (by omega : p ≠ n + q + 1 - wt) ha hmem, smul_zero]

/-- The true value `(u₍ₙ₎a|b)` vanishes off the matching mode for homogeneous `a, b`
(by `orthogonal_of_ne`). -/
theorem lhs_offdiag (B : InvariantForm W) {wt p q : ℤ} {u a b : 𝒱}
    (hu : u ∈ W.grading wt) (ha : a ∈ W.grading p) (hb : b ∈ W.grading q)
    (n : ℤ) (hn : n ≠ p + wt - q - 1) :
    B.form (W.smul u n a) b = 0 := by
  have hmem : W.smul u n a ∈ W.grading (wt + p - n - 1) := by
    have h := W.smul_mem_grading hu ha n
    rwa [show (wt + p - n - 1 : ℤ) = wt + p - n - 1 by ring] at h
  exact B.orthogonal_of_ne (by omega : wt + p - n - 1 ≠ q) hmem hb

/-! ## The difference `D` and its `L₋₁`-covariance recursion (the residual content) -/

/-- The FHL obstruction at weight `wt`. -/
noncomputable def fhlDiff (B : InvariantForm W) (u a b : 𝒱) (wt n : ℤ) : ℂ :=
  B.form (W.smul u n a) b - fhlRHS B u a b wt n

/-- **`fhlRHS = (−1)^wt • fhlInner`** (unfolding). -/
theorem fhlRHS_eq_inner (B : InvariantForm W) (u a b : 𝒱) (wt n : ℤ) :
    fhlRHS B u a b wt n = (-1 : ℂ) ^ wt • fhlInner B u a b wt n := rfl

/-- **The `L₋₁`-covariance recursion for the obstruction `D`.**  Both the true value
(`form_mode_lower`) and `fhlRHS` (`fhlInner_recursion`, scaled by `(−1)^wt`) obey
`n·F(a,b,n−1) = F(L₋₁a,b,n) − F(a,L₁b,n)`; hence so does `D`. -/
theorem fhlDiff_recursion (B : InvariantForm W) {wt : ℤ} (hwt : 0 ≤ wt) {u : 𝒱}
    (hu : u ∈ W.grading wt) (a b : 𝒱) (n : ℤ) :
    (n : ℂ) • fhlDiff B u a b wt (n - 1)
      = fhlDiff B u (W.L (-1) a) b wt n - fhlDiff B u a (W.L 1 b) wt n := by
  simp only [fhlDiff]
  rw [smul_sub, form_mode_lower B u a b n]
  have hfhl := fhlInner_recursion B hwt hu a b n
  rw [fhlRHS_eq_inner, fhlRHS_eq_inner, fhlRHS_eq_inner]
  rw [smul_comm ((n : ℂ)) ((-1 : ℂ) ^ wt), hfhl, smul_sub]
  ring

/-! ## Reduction of `ResidualFHL` to the matching-mode diagonal identity -/

/-- The **matching-mode diagonal identity**: for homogeneous `a ∈ 𝒱_p`, `b ∈ 𝒱_q`, the residual
holds at the one non-orthogonal mode `n = p + wt − q − 1`. -/
def DiagonalFHL (B : InvariantForm W) : Prop :=
  ∀ (wt p q : ℤ) (u a b : 𝒱), u ∈ W.grading wt → a ∈ W.grading p → b ∈ W.grading q →
    B.form (W.smul u (p + wt - q - 1) a) b = fhlRHS B u a b wt (p + wt - q - 1)

/-- `fhlRHS` is additive in `b`. -/
theorem fhlRHS_add_right (B : InvariantForm W) (u a b₁ b₂ : 𝒱) (wt n : ℤ) :
    fhlRHS B u a (b₁ + b₂) wt n = fhlRHS B u a b₁ wt n + fhlRHS B u a b₂ wt n := by
  rw [fhlRHS, fhlRHS, fhlRHS, ← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [W.smul_add_right, map_add, ← smul_add]

/-- `fhlRHS` vanishes when `b = 0`. -/
theorem fhlRHS_zero_right (B : InvariantForm W) (u a : 𝒱) (wt n : ℤ) :
    fhlRHS B u a 0 wt n = 0 := by
  rw [fhlRHS, Finset.sum_eq_zero (fun j _ => ?_), smul_zero]
  rw [PreVertexAlgebra.smul_def, map_zero, map_zero, smul_zero]

/-- `fhlRHS` is additive in `a`. -/
theorem fhlRHS_add_left (B : InvariantForm W) (u a₁ a₂ b : 𝒱) (wt n : ℤ) :
    fhlRHS B u (a₁ + a₂) b wt n = fhlRHS B u a₁ b wt n + fhlRHS B u a₂ b wt n := by
  rw [fhlRHS, fhlRHS, fhlRHS, ← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_add, LinearMap.add_apply, ← smul_add]

/-- `fhlRHS` vanishes when `a = 0`. -/
theorem fhlRHS_zero_left (B : InvariantForm W) (u b : 𝒱) (wt n : ℤ) :
    fhlRHS B u 0 b wt n = 0 := by
  rw [fhlRHS, Finset.sum_eq_zero (fun j _ => by rw [map_zero, LinearMap.zero_apply, smul_zero]),
    smul_zero]

/-- **`ResidualFHL` from the diagonal identity** (off-diagonal vanishing does the rest). -/
theorem residual_of_diagonal (B : InvariantForm W) (hdiag : DiagonalFHL B) : ResidualFHL B := by
  intro wt u hu n a b
  rw [skewRHS, ← form_smul_skew B u a b n]
  have hatop : a ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading (motive := fun a =>
      ∀ b : 𝒱, B.form (W.smul u n a) b = fhlRHS B u a b wt n) hatop ?_ ?_ ?_ b
  · intro p a ha b
    have hbtop : b ∈ ⨆ i, W.grading i := by
      rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
    refine Submodule.iSup_induction W.grading (motive := fun b =>
        B.form (W.smul u n a) b = fhlRHS B u a b wt n) hbtop ?_ ?_ ?_
    · intro q b hb
      by_cases hn : n = p + wt - q - 1
      · subst hn; exact hdiag wt p q u a b hu ha hb
      · rw [lhs_offdiag B hu ha hb n hn, fhlRHS_offdiag B hu ha hb n hn]
    · show B.form (W.smul u n a) 0 = fhlRHS B u a 0 wt n
      rw [map_zero, fhlRHS_zero_right]
    · intro b₁ b₂ hb₁ hb₂
      show B.form (W.smul u n a) (b₁ + b₂) = fhlRHS B u a (b₁ + b₂) wt n
      rw [map_add, hb₁, hb₂, fhlRHS_add_right]
  · intro b
    show B.form (W.smul u n 0) b = fhlRHS B u 0 b wt n
    rw [PreVertexAlgebra.smul_def, map_zero, map_zero, LinearMap.zero_apply, fhlRHS_zero_left]
  · intro a₁ a₂ ha₁ ha₂ b
    show B.form (W.smul u n (a₁ + a₂)) b = fhlRHS B u (a₁ + a₂) b wt n
    rw [W.smul_add_right, map_add, LinearMap.add_apply, ha₁ b, ha₂ b, fhlRHS_add_left]

/-- **Full FHL from the matching-mode diagonal identity.**  Chaining `residual_of_diagonal`
(off-diagonal vanishing) and `isFullyInvariant_of_residual` (`form_smul_skew` + the weight
reduction), the entire FHL theorem `IsFullyInvariant` reduces to the single hypothesis
`DiagonalFHL B`. -/
theorem isFullyInvariant_of_diagonal (B : InvariantForm W) (hdiag : DiagonalFHL B) :
    B.IsFullyInvariant :=
  isFullyInvariant_of_residual B (residual_of_diagonal B hdiag)

end VOA.VertexOperatorAlgebra
