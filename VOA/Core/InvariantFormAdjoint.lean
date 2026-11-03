/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.InvariantFormCanonical

/-!
# The adjoint vertex operator `Y*` mode calculus (FHL infrastructure)

The Frenkel–Huang–Lepowsky / Li adjoint-mode infrastructure: the FHL adjoint mode operator
`adjMode u wt n` (the RHS of `IsFullyInvariant`), its vacuum normalisation and `ℂ`-linearity, the
canonical-form adjunction bridge `adjMode_eq_fullInvariant_rhs`, the sl₂-conjugation covariance of
`Y` in mode form (`L0_smul_comm`, `L1_smul_comm`), and the genuine new `e^{zL₁}` operator iterate
`L1_pow_mul` (the Hadamard/binomial `L₁ᵏ∘M = ∑ⱼ C(k,j)(ad L₁ʲM)∘L₁^{k−j}`) with its mode form
`L1_pow_smul`. This is the operator-side scaffolding the canonical-form invariance proof consumes.

## Status
Axiom-clean for the `Y*` mode calculus, the sl₂ conjugation, and the `e^{zL₁}` iterate.
-/

namespace VOA.VertexOperatorAlgebra

open scoped BigOperators
open Classical

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}


/-! ## The FHL adjoint mode operator `adjMode` -/

/-- The **FHL adjoint mode operator** `Y*` (Gannon 5.1.11a / Frenkel–Huang–Lepowsky).
For a state `u` of conformal weight `wt`,
`adjMode u wt n := (-1)^{wt} • ∑_{j ≤ wt} (1/j!) • (L₁ʲu)₍2wt−n−2−j₎(·)`,
the explicit mode content of `Y(e^{zL₁}(−z⁻²)^{L₀}u, z⁻¹)`.  By the canonical-form full
invariance `IsFullyInvariant`, this is the operator for which `(u₍ₙ₎a|b) = (a|adjMode u wt n b)`. -/
noncomputable def adjMode (W : VertexOperatorAlgebra V) (u : V) (wt n : ℤ) (b : V) : V :=
  (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) •
      W.smul (((W.L 1) ^ j) u) (2 * wt - n - 2 - (j : ℤ)) b

/-- Unfolding of `adjMode`. -/
theorem adjMode_def (W : VertexOperatorAlgebra V) (u : V) (wt n : ℤ) (b : V) :
    adjMode W u wt n b
      = (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) •
          W.smul (((W.L 1) ^ j) u) (2 * wt - n - 2 - (j : ℤ)) b := rfl

/-! ## (1) Vacuum normalization -/

/-- **(1) Vacuum normalization.** For `u = 𝟙` (weight `0`), the `adjMode` sum collapses to its
single `j = 0` term: `adjMode 𝟙 0 n b = 𝟙₍₋n−2₎ b = δ_{n,−1} b`.  Concretely the operator is the
*unit-field* mode `mode(Y 𝟙)(…) = δ`, so the FHL adjoint of `Y(𝟙,z) = id` is again the identity. -/
theorem adjMode_vacuum (W : VertexOperatorAlgebra V) (n : ℤ) (b : V) :
    adjMode W W.vacuum 0 n b = W.smul W.vacuum (-n - 2) b := by
  rw [adjMode_def]
  -- weight 0: range (0.toNat + 1) = range 1 = {0}, single term j = 0
  simp only [Int.toNat_zero, zero_add, Finset.range_one, Finset.sum_singleton,
    pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    Nat.cast_zero]
  -- exponent: 2*0 - n - 2 - 0 = -n - 2; sign (-1)^0 = 1
  rw [show (2 * (0 : ℤ) - n - 2 - 0) = -n - 2 by ring]
  simp

/-- **(1′) Vacuum normalization, the `δ_{n,−1}` form.** `adjMode 𝟙 0 n b = if n = −1 then b else 0`
— the mode of the unit field `Y(𝟙,z)=id`.  So the FHL-adjoint of the vacuum field is the
identity field, as it must be. -/
theorem adjMode_vacuum_delta (W : VertexOperatorAlgebra V) (n : ℤ) (b : V) :
    adjMode W W.vacuum 0 n b = if n = -1 then b else 0 := by
  rw [adjMode_vacuum, PreVertexAlgebra.smul_vacuum_left]
  by_cases h : n = -1
  · rw [if_pos h, if_pos (show (-n - 2 : ℤ) = -1 by omega)]
  · rw [if_neg h, if_neg (show ¬ (-n - 2 : ℤ) = -1 by omega)]

/-! ## (2) ℂ-linearity of `adjMode` in `u` (at fixed `wt`) -/

/-- **(2a) Additivity** of `adjMode` in the state `u` (fixed `wt`, `n`, `b`). -/
theorem adjMode_add_left (W : VertexOperatorAlgebra V) (u₁ u₂ : V) (wt n : ℤ) (b : V) :
    adjMode W (u₁ + u₂) wt n b = adjMode W u₁ wt n b + adjMode W u₂ wt n b := by
  simp only [adjMode_def]
  rw [← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_add, PreVertexAlgebra.smul_add_left, smul_add]

/-- **(2b) ℂ-homogeneity** of `adjMode` in the state `u`. -/
theorem adjMode_smul_left (W : VertexOperatorAlgebra V) (c : ℂ) (u : V) (wt n : ℤ) (b : V) :
    adjMode W (c • u) wt n b = c • adjMode W u wt n b := by
  simp only [adjMode_def]
  have hsum : ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) •
        W.smul (((W.L 1) ^ j) (c • u)) (2 * wt - n - 2 - (j : ℤ)) b
      = c • ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) •
          W.smul (((W.L 1) ^ j) u) (2 * wt - n - 2 - (j : ℤ)) b := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul, PreVertexAlgebra.smul_smul_left, smul_comm c]
  rw [hsum, smul_comm]

/-- **(2c) Vanishing on `0`**: `adjMode 0 wt n b = 0`. -/
theorem adjMode_zero_left (W : VertexOperatorAlgebra V) (wt n : ℤ) (b : V) :
    adjMode W 0 wt n b = 0 := by
  simp only [adjMode_def, map_zero, PreVertexAlgebra.smul_zero_left, smul_zero,
    Finset.sum_const_zero]

/-- **(2c′)** `adjMode … wt n` bundled as an additive hom in `u`. -/
noncomputable def adjModeAddHom (W : VertexOperatorAlgebra V) (wt n : ℤ) (b : V) : V →+ V where
  toFun u := adjMode W u wt n b
  map_zero' := adjMode_zero_left W wt n b
  map_add' u₁ u₂ := adjMode_add_left W u₁ u₂ wt n b

/-- **(2d) `adjMode … wt n` as a ℂ-linear map in the state `u`** (fixed weight `wt`, mode `n`,
second argument `b`).  This is the linearity FHL needs to extend the adjoint relation from a basis
of homogeneous states to all of `𝒱_{wt}`. -/
noncomputable def adjModeₗ (W : VertexOperatorAlgebra V) (wt n : ℤ) (b : V) : V →ₗ[ℂ] V where
  toFun u := adjMode W u wt n b
  map_add' u₁ u₂ := adjMode_add_left W u₁ u₂ wt n b
  map_smul' c u := adjMode_smul_left W c u wt n b

@[simp] theorem adjModeₗ_apply (W : VertexOperatorAlgebra V) (wt n : ℤ) (b u : V) :
    adjModeₗ W wt n b u = adjMode W u wt n b := rfl

/-! ## The bridge to `IsFullyInvariant` (the canonical-form adjunction) -/

/-- **The adjoint bridge.** `adjMode` is *exactly* the RHS operator of `IsFullyInvariant`.  Hence
for the canonical/normalized invariant form `B` (any `B` with `B.IsFullyInvariant`),
`(u₍ₙ₎a|b) = (a|adjMode u wt n b)` for homogeneous `u` of weight `wt`.  This is the FHL adjunction
for the canonical form — the *only* form for which it can hold (`Core.InvariantFormTranspose`). -/
theorem adjMode_eq_fullInvariant_rhs (B : InvariantForm W) (hB : B.IsFullyInvariant)
    {wt : ℤ} (u : V) (hu : u ∈ W.grading wt) (n : ℤ) (a b : V) :
    B.form (W.smul u n a) b = B.form a (adjMode W u wt n b) := by
  rw [hB wt u hu n a b, adjMode_def, map_smul, map_sum]
  refine congrArg (fun s : ℂ => (-1 : ℂ) ^ wt • s) (Finset.sum_congr rfl (fun j _ => ?_))
  rw [map_smul]

/-! ## (3) SL₂ conjugation covariance of `Y` in mode form -/

/-! ### (3a) The `L₀`-conjugation `z₀^{L₀}Y(u,z)z₀^{−L₀} = Y(z₀^{L₀}u, z₀z)` -/

/-- **(3a) `L₀`-conjugation covariance**, in its infinitesimal mode form: for homogeneous `u ∈ 𝒱_wt`
and `x ∈ 𝒱_k`, the mode `u₍ₘ₎` carries grade `wt + k − m − 1`, so `L₀` acts on `u₍ₘ₎x` by that
weight.  Equivalently, `[L₀, u₍ₘ₎] = (wt − m − 1)·u₍ₘ₎` on `𝒱_wt`.  This is the (diagonalized) mode
content of `z₀^{L₀}Y(u,z)z₀^{−L₀} = Y(z₀^{L₀}u, z₀z)`: `L₀` shifts the mode index by the conformal
weight. -/
theorem L0_smul_comm (W : VertexOperatorAlgebra V) {wt k : ℤ} {u : V} (hu : u ∈ W.grading wt)
    {x : V} (hx : x ∈ W.grading k) (m : ℤ) :
    W.L 0 (W.smul u m x) = ((wt + k - m - 1 : ℤ) : ℂ) • W.smul u m x := by
  have hmem : W.smul u m x ∈ W.grading (wt + k - m - 1) := W.smul_mem_grading hu hx m
  exact W.L_zero_grading _ hmem

/-- **(3a′) The pure `[L₀, u₍ₘ₎]` commutator on homogeneous states.** With `x ∈ 𝒱_k`,
`L₀(u₍ₘ₎x) − u₍ₘ₎(L₀x) = (wt − m − 1)·u₍ₘ₎x`.  This is the `z₀`-derivative of the `L₀`-conjugation
covariance, separated from the grading of `x`. -/
theorem L0_smul_bracket (W : VertexOperatorAlgebra V) {wt k : ℤ} {u : V} (hu : u ∈ W.grading wt)
    {x : V} (hx : x ∈ W.grading k) (m : ℤ) :
    W.L 0 (W.smul u m x) - W.smul u m (W.L 0 x) = ((wt - m - 1 : ℤ) : ℂ) • W.smul u m x := by
  rw [L0_smul_comm W hu hx m, W.L_zero_grading x hx, PreVertexAlgebra.smul_smul_right]
  rw [← sub_smul]
  congr 1
  push_cast
  ring

/-! ### (3b) The `[L₁, u₍ₘ₎]` bracket in `smul` form (the hard new ingredient) -/

/-- **(3b) The `[L₁, u₍ₘ₎]` Virasoro mode commutator, in `smul` form.**
`L₁(u₍ₘ₎x) − u₍ₘ₎(L₁x) = (L₋₁u)₍ₘ₊₂₎x + 2(L₀u)₍ₘ₊₁₎x + (L₁u)₍ₘ₎x`.
This is the operator commutator `L1_mode_comm` applied to `x` and rewritten through `smul`. -/
theorem L1_smul_comm (W : VertexOperatorAlgebra V) (u : V) (m : ℤ) (x : V) :
    W.L 1 (W.smul u m x) - W.smul u m (W.L 1 x)
      = W.smul (W.L (-1) u) (m + 2) x + (2 : ℂ) • W.smul (W.L 0 u) (m + 1) x
          + W.smul (W.L 1 u) m x := by
  have h := L1_mode_comm W u m
  rw [Ring.lie_def] at h
  have happ := congrArg (fun (T : Module.End ℂ V) => T x) h
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply] at happ
  -- happ : W.L 1 (mode (W.Y u) m x) - mode (W.Y u) m (W.L 1 x)
  --        = mode (W.Y (L(-1)u)) (m+2) x + 2 • mode (W.Y (L0 u)) (m+1) x + mode (W.Y (L1 u)) m x
  simpa only [← PreVertexAlgebra.smul_def] using happ

/-! ### The `e^{zL₁}`-conjugation operator iterate (Hadamard / Leibniz form)

The `e^{zL₁}`-conjugation `e^{zL₁}M e^{−zL₁} = ∑_k (z^k/k!) (ad L₁)^k M` is governed, term by term,
by the **binomial operator iterate** below: `L₁ᵏ ∘ M = ∑_{j≤k} C(k,j) (adL₁^j M) ∘ L₁^{k−j}`, where
`adL₁ M = [L₁, M]`.  It is a pure `End`-identity (no VOA needed), proved by induction on `k` from the
single-step Leibniz rule `L₁ ∘ M = M ∘ L₁ + [L₁, M]`.  Specialising `M = u₍ₘ₎` and feeding the
single bracket `L1_smul_comm` ( = `adL₁(u₍ₘ₎)` in tower form) turns it into the genuine `e^{zL₁}Y(u,z)`
mode conjugation. -/

/-- `adL₁ M := ⁅L₁, M⁆`, the inner derivation by `L₁` (the `z`-derivative of conjugation). -/
noncomputable def adL1 (W : VertexOperatorAlgebra V) (M : Module.End ℂ V) : Module.End ℂ V :=
  ⁅W.L 1, M⁆

/-- One-step Leibniz: `L₁ ∘ M = M ∘ L₁ + adL₁ M`. -/
theorem L1_mul_eq (W : VertexOperatorAlgebra V) (M : Module.End ℂ V) :
    W.L 1 * M = M * W.L 1 + adL1 W M := by
  rw [adL1, Ring.lie_def]; abel

/-- **The binomial operator iterate (Hadamard lemma, polynomial part).**
`L₁ᵏ ∘ M = ∑_{j∈range(k+1)} C(k,j) • (adL₁^j M) ∘ L₁^{k−j}`.
Proved by induction on `k` using the single-step Leibniz rule `L1_mul_eq` and Pascal's identity
(`Finset.sum_range_choose_mul_pow`-style reindex).  This is the algebraic skeleton of
`e^{zL₁}M e^{−zL₁} = ∑ (z^k/k!) adL₁^k M`. -/
theorem L1_pow_mul (W : VertexOperatorAlgebra V) (M : Module.End ℂ V) (k : ℕ) :
    (W.L 1) ^ k * M
      = ∑ j ∈ Finset.range (k + 1),
          (k.choose j : ℂ) • ((adL1 W)^[j] M * (W.L 1) ^ (k - j)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc, ih, Finset.mul_sum]
    -- Expand each summand `L₁ * (C(k,j) • adL1^j M ∘ L₁^{k-j})` via the Leibniz rule into two
    -- pieces, with all right-powers written as `L₁^{(k+1)-j}` (valid since `j ≤ k`).
    have hterm : ∀ j ∈ Finset.range (k + 1),
        W.L 1 * ((k.choose j : ℂ) • ((adL1 W)^[j] M * (W.L 1) ^ (k - j)))
          = (k.choose j : ℂ) • ((adL1 W)^[j] M * (W.L 1) ^ (k + 1 - j))
            + (k.choose j : ℂ) • ((adL1 W)^[j + 1] M * (W.L 1) ^ (k - j)) := by
      intro j hj
      rw [Finset.mem_range, Nat.lt_succ_iff] at hj
      rw [mul_smul_comm, ← mul_assoc, L1_mul_eq W ((adL1 W)^[j] M), add_mul, smul_add]
      congr 2
      · rw [mul_assoc, ← pow_succ', show k + 1 - j = (k - j) + 1 from by omega]
      · rw [Function.iterate_succ_apply']
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    -- the canonical target term `T j := adL1^j M ∘ L₁^{(k+1)-j}`
    set T : ℕ → Module.End ℂ V := fun j => (adL1 W)^[j] M * (W.L 1) ^ (k + 1 - j) with hT
    -- LHS first sum `S_A = ∑_{j≤k} C(k,j) • T j`; second `S_B = ∑_{j≤k} C(k,j) • T (j+1)`.
    have hS_A : ∑ j ∈ Finset.range (k + 1),
          (k.choose j : ℂ) • ((adL1 W)^[j] M * (W.L 1) ^ (k + 1 - j))
        = ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) • T j := rfl
    have hS_B : ∑ j ∈ Finset.range (k + 1),
          (k.choose j : ℂ) • ((adL1 W)^[j + 1] M * (W.L 1) ^ (k - j))
        = ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) • T (j + 1) := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_range, Nat.lt_succ_iff] at hj
      rw [hT]; simp only [show k + 1 - (j + 1) = k - j from by omega]
    rw [hS_A, hS_B]
    -- expand the target via `sum_range_succ'` (peel the `j=0` term, reindex the rest as `j+1`)
    rw [Finset.sum_range_succ' (fun j => (Nat.choose (k + 1) j : ℂ) • T j) (k + 1)]
    -- Pascal on each reindexed term: `C(k+1, j+1) = C(k,j) + C(k,j+1)`
    have hpascal : ∀ j ∈ Finset.range (k + 1),
        (Nat.choose (k + 1) (j + 1) : ℂ) • T (j + 1)
          = (k.choose j : ℂ) • T (j + 1) + (k.choose (j + 1) : ℂ) • T (j + 1) := by
      intro j _
      rw [← add_smul, ← Nat.cast_add, Nat.choose_succ_succ k j]
    rw [Finset.sum_congr rfl hpascal, Finset.sum_add_distrib]
    -- reassemble: S_A = (C(k,0)•T 0) + ∑_{j≤k-1} C(k,j+1)•T(j+1) ; the `j=0` boundary terms match
    rw [Finset.sum_range_succ' (fun j => (k.choose j : ℂ) • T j) k]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_smul]
    -- pad `∑_{range k} C(k,x+1)•T(x+1)` to `∑_{range (k+1)}` (top term `C(k,k+1)=0`)
    have hpad : ∑ x ∈ Finset.range k, (k.choose (x + 1) : ℂ) • T (x + 1)
        = ∑ x ∈ Finset.range (k + 1), (k.choose (x + 1) : ℂ) • T (x + 1) := by
      rw [Finset.sum_range_succ]
      simp only [Nat.choose_succ_self, Nat.cast_zero, zero_smul, add_zero]
    rw [hpad]
    abel

/-- **The `e^{zL₁}`-conjugation in mode form (applied to a vector).**
`L₁ᵏ(u₍ₘ₎x) = ∑_{j≤k} C(k,j)·(adL₁ʲ u₍ₘ₎)(L₁^{k−j} x)`.  This is `L1_pow_mul` evaluated at `x`
with `M = u₍ₘ₎`: the polynomial (term-by-term) content of `e^{zL₁}Y(u,z)e^{−zL₁}`. -/
theorem L1_pow_smul (W : VertexOperatorAlgebra V) (u : V) (m : ℤ) (x : V) (k : ℕ) :
    ((W.L 1) ^ k) (W.smul u m x)
      = ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) •
          ((adL1 W)^[j] (mode (W.Y u) m)) (((W.L 1) ^ (k - j)) x) := by
  have hmul := L1_pow_mul W (mode (W.Y u) m) k
  have happ := congrArg (fun (S : Module.End ℂ V) => S x) hmul
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply] at happ
  rw [PreVertexAlgebra.smul_def]
  exact happ

/-- **The single-step `adL₁(u₍ₘ₎)` in tower form** (the `m ↦ m+2,m+1,m` Virasoro tower):
`adL₁(u₍ₘ₎) = (L₋₁u)₍ₘ₊₂₎ + 2(L₀u)₍ₘ₊₁₎ + (L₁u)₍ₘ₎` as an endomorphism.  This is the operator
version of `L1_smul_comm`; iterating it inside `L1_pow_smul` produces the full `e^{zL₁}`-tower. -/
theorem adL1_mode (W : VertexOperatorAlgebra V) (u : V) (m : ℤ) :
    adL1 W (mode (W.Y u) m)
      = mode (W.Y (W.L (-1) u)) (m + 2) + (2 : ℂ) • mode (W.Y (W.L 0 u)) (m + 1)
          + mode (W.Y (W.L 1 u)) m := by
  rw [adL1]; exact L1_mode_comm W u m

/-! ### Termination: the `e^{zL₁}` tower is finite on the bounded-below grading

For homogeneous `u ∈ 𝒱_wt` the `L₁`-tower `L₁ʲu` vanishes for `j > wt` (`L_one_pow_eq_zero`), so the
`adjMode` sum (range `wt.toNat + 1`) already captures every nonzero term — this is what makes
`adjMode` (hence the FHL adjoint `Y*`) a *finite* operator and the `e^{zL₁}` conjugation polynomial.
-/

/-- **Tower termination.** For `u ∈ 𝒱_wt` with `0 ≤ wt`, the `adjMode` sum may be freely extended
beyond `wt`: every term with `j > wt.toNat` is `0`, since `L₁ʲu = 0` there. -/
theorem adjMode_tower_terminates (W : VertexOperatorAlgebra V) {wt : ℤ} (hwt : 0 ≤ wt) {u : V}
    (hu : u ∈ W.grading wt) {j : ℕ} (hj : wt.toNat < j) :
    ((W.L 1) ^ j) u = 0 :=
  L_one_pow_eq_zero W hu (by
    have : (wt.toNat : ℤ) = wt := Int.toNat_of_nonneg hwt
    omega)


end VOA.VertexOperatorAlgebra
