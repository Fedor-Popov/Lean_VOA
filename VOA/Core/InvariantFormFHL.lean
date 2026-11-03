/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.InvariantFormSymmetry
import VOA.Core.SkewSymmetry

/-!
# Toward FHL full invariance — the skew-route adjoint identity and the weight reduction

Genuine, axiom-free bricks toward the would-be **general-`B` full-invariance** statement
suggested by Gannon 5.1.11a: an invariant bilinear form `B` (a
`Core.BilinearForm.InvariantForm`, carrying only the
Virasoro-adjointness `(Lₙa|b)=(a|L₋ₙb)`) would satisfy the *full* mode adjointness
`InvariantForm.IsFullyInvariant` — `(u₍ₙ₎a|b) = (−1)^{wt} ∑_{j≤wt}(1/j!)(a|(L₁ʲu)₍2wt−n−2−j₎b)`.
Under `hqp` and an explicitly supplied nonsymmetric grade-one invariant-form witness, the
universal statement is ruled out by `Core.InvariantFormDelimitation`.  That witness is not
constructed in the repository.  The valid FHL/Li theorem for the constructed canonical form is
proved separately.

* **`form_smul_skew`** — the **skew-route adjoint identity**: applying the functional `x ↦ (x|b)`
  to the skew-symmetry mode formula (`Core.SkewSymmetry.skew_mode`, Gannon 5.1.8) and using
  `virasoro_adj` (so `(L₋₁)ʲ ⊣ (L₁)ʲ`, `form_Lneg1_pow`), every invariant form obeys
  `(u₍ₙ₎a|b) = ∑ⱼ (1/j!) sgn(−n−1−j) (a₍n+j₎u | L₁ʲb)`. Unconditional, axiom-clean.
* **`isFullyInvariant_wt0`** — full invariance proved outright for `u ∈ 𝒱₀ = ℂ𝟙` (`wt = 0`).
* **`FullyInvariantAt` / `isFullyInvariant_iff_forall`** — the per-weight body of
  `IsFullyInvariant` (`Iff.rfl`).
* **`isFullyInvariant_of_propagation`** — the honest **reduction**: full `IsFullyInvariant` follows
  from a single weight-propagation hypothesis `hstep` ("`FullyInvariantAt` for all `k ≤ m` ⟹ for
  `m+1`"); the `wt < 0` (`fullyInvariantAt_neg`) and `wt = 0` (`fullyInvariantAt_zero`) layers are
  discharged here and strong induction closes the rest. `hstep` is a **hypothesis** (the textbook
  reconstruction/Borcherds propagation), never an `axiom`.

## Status
**Delimited by a conditional obstruction.** The reductions in this file are axiom-clean.
`Core.InvariantFormDelimitation.general_fullyInvariant_not_a_theorem` proves that their universal
general-`B` target fails under `hqp` and an explicit nonsymmetric grade-one invariant-form witness;
it does not construct that witness.  The genuine canonical-form result is complete in
`Core.InvariantFormFHL2` (`canonicalInvariantForm_isFullyInvariant`).

## References
* Gannon §5.1.3, eq. (5.1.11a); Frenkel–Huang–Lepowsky [199]; Li [380].
-/

namespace VOA.VertexOperatorAlgebra

open scoped BigOperators
open Classical

variable {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- Helper: `(L₋₁)ʲ` is adjoint to `(L₁)ʲ` for an invariant form. -/
theorem form_Lneg1_pow (B : InvariantForm W) (x b : 𝒱) (j : ℕ) :
    B.form ((W.L (-1) ^ j) x) b = B.form x ((W.L 1 ^ j) b) := by
  induction j generalizing x b with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    -- B.form (L₋₁ ((L₋₁)^k x)) b = B.form ((L₋₁)^k x) (L₁ b)   via virasoro_adj at n = -1
    have hadj := B.virasoro_adj (-1) ((W.L (-1) ^ k) x) b
    rw [show (-(-1) : ℤ) = 1 by ring] at hadj
    rw [hadj, ih x (W.L 1 b), pow_succ, Module.End.mul_apply]

/-- The skew summand `j ↦ (j!⁻¹)·sgn(-n-1-j)·Tʲ((Y a)(-n-1-j) u)` has finite support:
it vanishes once `W.smul a (n+j) u = 0`, which holds for `j` large by regularity. -/
theorem skew_summand_finite (W : VertexOperatorAlgebra 𝒱) (u a : 𝒱) (n : ℤ) :
    Function.HasFiniteSupport
      (fun j : ℕ => ((j.factorial : ℂ)⁻¹) • (sgn (-n - 1 - j)) •
        ((W.toPreVertexAlgebra.T ^ j) ((W.Y a) (-n - 1 - j) u))) := by
  obtain ⟨N, hN⟩ := W.toPreVertexAlgebra.smul_eventually_zero a u
  apply Set.Finite.subset (Set.finite_Iio (max 0 (N - n)).toNat)
  intro j hj
  simp only [Function.mem_support, ne_eq] at hj
  rw [Set.mem_Iio]
  by_contra hge
  rw [not_lt] at hge
  -- j ≥ (max 0 (N-n)).toNat, so n + j ≥ N, so the smul vanishes
  apply hj
  have hzero : (W.Y a) (-n - 1 - j) u = 0 := by
    rw [Y_apply_eq_smul, show (-(-n - 1 - (j : ℤ)) - 1 : ℤ) = n + j by ring]
    apply hN
    have : (N - n : ℤ) ≤ (j : ℤ) := by
      have h1 : ((max 0 (N - n)).toNat : ℤ) ≤ (j : ℤ) := by exact_mod_cast hge
      have h2 : (N - n : ℤ) ≤ ((max 0 (N - n)).toNat : ℤ) := by
        rw [Int.toNat_of_nonneg (le_max_left 0 _)]; exact le_max_right 0 _
      omega
    omega
  rw [hzero, map_zero, smul_zero, smul_zero]

/-! ## The skew-route adjoint identity -/

/-- **The skew-route adjoint identity.**  Applying the functional `x ↦ (x|b)` to the
skew-symmetry mode formula gives, for any invariant form `B`,
`(u₍ₙ₎a | b) = ∑ⱼ (1/j!) sgn(-n-1-j) (a₍n+j₎u | L₁ʲ b)`. Unconditional. -/
theorem form_smul_skew (B : InvariantForm W) (u a b : 𝒱) (n : ℤ) :
    B.form (W.smul u n a) b
      = ∑ᶠ j : ℕ, ((j.factorial : ℂ)⁻¹) • (sgn (-n - 1 - j)) •
          B.form (W.smul a (n + j) u) ((W.L 1 ^ j) b) := by
  -- apply the linear functional `x ↦ (x | b)` to the skew mode formula
  have hskew := skew_mode W u a n
  apply_fun (fun x => B.form x b) at hskew
  rw [hskew]
  -- push the functional through the finsum
  rw [show (B.form (∑ᶠ j : ℕ, ((j.factorial : ℂ)⁻¹) • (sgn (-n - 1 - j)) •
        ((W.toPreVertexAlgebra.T ^ j) ((W.Y a) (-n - 1 - j) u)))) b
      = (LinearMap.flip B.form b : 𝒱 →ₗ[ℂ] ℂ)
          (∑ᶠ j : ℕ, ((j.factorial : ℂ)⁻¹) • (sgn (-n - 1 - j)) •
            ((W.toPreVertexAlgebra.T ^ j) ((W.Y a) (-n - 1 - j) u))) from rfl,
      map_finsum (LinearMap.flip B.form b) (skew_summand_finite W u a n)]
  -- now simplify each summand
  refine finsum_congr fun j => ?_
  simp only [LinearMap.flip_apply, map_smul, smul_eq_mul]
  -- B.form ((j!⁻¹)•sgn•(Tʲ x)) b  →  (j!⁻¹)•sgn•(B.form (Tʲ x) b)
  -- now rewrite Tʲ = (L₋₁)ʲ, use the adjoint helper, and Y_apply_eq_smul
  congr 1
  congr 1
  rw [T_eq_Lneg1, form_Lneg1_pow B ((W.Y a) (-n - 1 - j) u) b,
      Y_apply_eq_smul, show (-(-n - 1 - (j : ℤ)) - 1 : ℤ) = n + j by ring]

/-! ## The `wt = 0` base case of `IsFullyInvariant` -/

/-- **Full-invariance base case, weight 0.**  For `u ∈ 𝒱₀ = ℂ·𝟙`, the explicit mode content of
full invariance holds: `(u₍ₙ₎a | b) = (-1)⁰ ∑_{j<1} (1/j!) (a | (L₁ʲu)₍-n-2-j₎ b)`.
Both sides reduce to `c·δ_{n,-1}·(a|b)` when `u = c·𝟙`. -/
theorem isFullyInvariant_wt0 (B : InvariantForm W) (u : 𝒱) (hu : u ∈ W.grading 0)
    (n : ℤ) (a b : 𝒱) :
    B.form (W.smul u n a) b
      = (-1 : ℂ) ^ (0 : ℤ) • ∑ j ∈ Finset.range 1, ((j.factorial : ℂ)⁻¹) •
          B.form a (W.smul (((W.L 1) ^ j) u) (2 * 0 - n - 2 - (j : ℤ)) b) := by
  -- u = c • 𝟙
  rw [W.vacuum_grade, Submodule.mem_span_singleton] at hu
  obtain ⟨c, hc⟩ := hu
  subst hc
  -- LHS:  (c𝟙)₍ₙ₎a = c • 𝟙₍ₙ₎a = c • (if n=-1 then a else 0)
  rw [PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_vacuum_left,
    map_smul, LinearMap.smul_apply, smul_eq_mul]
  -- RHS: collapse the singleton sum (j = 0), L₁⁰ = id
  rw [Finset.sum_range_one, pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one,
    inv_one, one_smul, zpow_zero, one_smul, Nat.cast_zero,
    show (2 * (0 : ℤ) - n - 2 - 0) = -n - 2 by ring,
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_vacuum_left, map_smul, smul_eq_mul]
  -- both sides: c * (if … then (a|b) else 0); align the index conditions n = -1  ↔  -n-2 = -1
  by_cases hn : n = -1
  · subst hn; norm_num
  · rw [if_neg hn, if_neg (by omega : ¬ (-n - 2 = -1))]
    simp

/-! ## Honest reduction of full FHL to a single weight-propagation step

The full theorem `IsFullyInvariant` quantifies the mode identity over every weight `wt`.
We provide an **axiom-free reduction**: the per-weight statement `FullyInvariantAt B wt`,
proved outright for `wt < 0` (where `u = 0`) and `wt = 0` (above), and a clean derivation
of the FULL `IsFullyInvariant` from an isolated **propagation hypothesis** `hstep`
("weight `k ≤ m` ⟹ weight `m+1`").  No `sorry`/`axiom`: the residual mathematical content of FHL
is exactly `hstep`, and everything else is discharged. -/

/-- The full-invariance mode identity at a *fixed* weight `wt` (the body of `IsFullyInvariant`
specialised to one `wt`). -/
def FullyInvariantAt (B : InvariantForm W) (wt : ℤ) : Prop :=
  ∀ (u : 𝒱), u ∈ W.grading wt → ∀ (n : ℤ) (a b : 𝒱),
    B.form (W.smul u n a) b
      = (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) •
          B.form a (W.smul (((W.L 1) ^ j) u) (2 * wt - n - 2 - (j : ℤ)) b)

/-- `IsFullyInvariant` is exactly "`FullyInvariantAt` at every weight". -/
theorem isFullyInvariant_iff_forall (B : InvariantForm W) :
    B.IsFullyInvariant ↔ ∀ wt : ℤ, FullyInvariantAt B wt := Iff.rfl

/-- **Base case below grade 0.**  For `wt < 0`, `𝒱_{wt} = 0`, so `u = 0` and both sides
vanish: `FullyInvariantAt B wt` holds vacuously. -/
theorem fullyInvariantAt_neg (B : InvariantForm W) {wt : ℤ} (hwt : wt < 0) :
    FullyInvariantAt B wt := by
  intro u hu n a b
  have hu0 : u = 0 := eq_zero_of_mem_neg_grading W hwt hu
  subst hu0
  rw [PreVertexAlgebra.smul_zero_left, map_zero, LinearMap.zero_apply,
    show wt.toNat = 0 by omega]
  simp

/-- **Base case at grade 0** (`isFullyInvariant_wt0`, repackaged): `FullyInvariantAt B 0`. -/
theorem fullyInvariantAt_zero (B : InvariantForm W) : FullyInvariantAt B 0 := by
  intro u hu n a b
  have h := isFullyInvariant_wt0 B u hu n a b
  rwa [show ((0:ℤ).toNat + 1) = 1 from rfl]

/-- **The FHL weight reduction.**  Given a single **weight-propagation step** `hstep` —
"`FullyInvariantAt B k` for all `k ≤ m` ⟹ `FullyInvariantAt B (m+1)`", for every `m ≥ 0` —
the FULL FHL theorem `IsFullyInvariant` follows.  The negative and grade-0 layers are
discharged here (`fullyInvariantAt_neg`, `fullyInvariantAt_zero`); strong induction on the
weight closes the rest.  This isolates the entire remaining content of FHL into `hstep`
(the textbook reconstruction/Borcherds propagation), with no axioms or `sorry`. -/
theorem isFullyInvariant_of_propagation (B : InvariantForm W)
    (hstep : ∀ m : ℕ, (∀ k : ℤ, k ≤ (m : ℤ) → FullyInvariantAt B k) →
        FullyInvariantAt B ((m : ℤ) + 1)) :
    B.IsFullyInvariant := by
  rw [isFullyInvariant_iff_forall]
  -- first establish `FullyInvariantAt B wt` for all `wt ≥ 0` by strong induction on `wt.toNat`
  have hnonneg : ∀ N : ℕ, ∀ k : ℤ, k ≤ (N : ℤ) → FullyInvariantAt B k := by
    intro N
    induction N with
    | zero =>
        intro k hk
        rcases lt_or_eq_of_le hk with h | h
        · exact fullyInvariantAt_neg B (by exact_mod_cast h)
        · rw [h]; exact fullyInvariantAt_zero B
    | succ M ih =>
        intro k hk
        rcases lt_or_eq_of_le hk with h | h
        · exact ih k (by push_cast at h; omega)
        · rw [show k = ((M : ℤ) + 1) by push_cast at h; omega]
          exact hstep M ih
  -- now conclude for every weight
  intro wt
  rcases lt_or_ge wt 0 with hwt | hwt
  · exact fullyInvariantAt_neg B hwt
  · exact hnonneg wt.toNat wt (by rw [Int.toNat_of_nonneg hwt])

end VOA.VertexOperatorAlgebra
