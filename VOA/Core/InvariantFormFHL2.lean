/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.QuasiPrimaryDecomp
import VOA.Core.InvariantFormQPMatchGen
import VOA.Core.InvariantFormCanonicalFHL

/-!
# Canonical-form FHL: `CanDiagonal` discharged, the `Core/BilinearForm` main results for the canonical form

The Frenkel–Huang–Lepowsky / Li (1994) invariant-form theorem, assembled axiom-free under the standing
hypotheses `hne : 𝟙 ≠ 0` and `hqp : L₁𝒱₁ = 0`.  The two genuine inputs are proved:
`qpDecomp` (`Core.QuasiPrimaryDecomp`, the sl₂ quasi-primary decomposition) and `canBilin_qp_qp_adj`
(`Core.InvariantFormQPMatchGen`, the general-weight matching identity, Li Prop 2.6).  This file feeds
them into the assembly `canDiagonal_holds` to get **`canDiagonal_unconditional : CanDiagonal hne`**, then
derives the canonical-form full invariance (`canFormFHL`/`CanVirasoroAdj`, via `L₁ω = 0`) and the
5.1.11b/5.1.12b main results (no hypotheses beyond `hne`, `hqp`) for the unit-normalised
`canonicalInvariantForm`.  The raw Li/FHL construction is retained as `gannonCanFormFHL` with
vacuum norm `-1`; the public form is its negative and has vacuum norm `+1`.

## References
* Gannon §5.1.3, eqs. (5.1.11)–(5.1.12); Frenkel–Huang–Lepowsky [199]; Li [380].
-/

set_option linter.style.longLine false
set_option maxHeartbeats 1600000

open VOA VOA.VertexOperatorAlgebra
open scoped BigOperators
open Classical
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
namespace VOA

/-- (I) sl₂ decomposition, as a named Prop.  Proved under `L₁𝒱₁ = 0` by `qpDecomp`
(`Core.QuasiPrimaryDecomp`). -/
def DecompHyp (W : VertexOperatorAlgebra V) : Prop :=
  ∀ {p : ℤ}, 1 ≤ p → ∀ {a : V}, a ∈ W.grading p →
    ∃ a₀ c : V, a₀ ∈ W.grading p ∧ W.L 1 a₀ = 0 ∧ c ∈ W.grading (p - 1) ∧ a = a₀ + W.L (-1) c

/-- (II) general-weight quasi-primary matching, all modes, as a named Prop.  Proved under
`L₁𝒱₁ = 0` by `canBilin_qp_qp_adj` (`Core.InvariantFormQPMatchGen`). -/
def MatchHyp (W : VertexOperatorAlgebra V) (hne : W.vacuum ≠ 0) : Prop :=
  ∀ {w : ℤ} {u : V}, u ∈ W.grading w → W.L 1 u = 0 →
    ∀ {p : ℤ} {a : V}, a ∈ W.grading p → W.L 1 a = 0 → ∀ (n : ℤ) (b : V),
      canBilin W hne (W.smul u n a) b = (-1:ℂ)^w • canBilin W hne a (W.smul u (2*w - n - 2) b)

/-! ## Translation mode helper: `(L₋₁X)₍s₎b = -s•X₍s-1₎b` (this is `smul_Lneg1_shift`). -/

/-! ## `canRHS` u-additivity (linear in the `u`-slot). -/

theorem canRHS_add_u (hne : W.vacuum ≠ 0) (u₁ u₂ a b : V) (wt n : ℤ) :
    canRHS hne (u₁ + u₂) a b wt n = canRHS hne u₁ a b wt n + canRHS hne u₂ a b wt n := by
  rw [canRHS, canRHS, canRHS, ← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_add (((W.L 1) ^ j)), PreVertexAlgebra.smul_add_left, map_add, ← smul_add]

/-! ## The qp-collapse of `canRHS` for a quasi-primary `u`.

For `u ∈ 𝒱_w` with `L₁u = 0` and `0 ≤ w`, every `j ≥ 1` term of `canRHS` carries `(L₁ʲu) = 0`,
leaving the single `j = 0` term: `canRHS u a b w n = (-1)^w • canBilin(a, u₍2w-n-2₎b)`. -/
theorem canRHS_qp_collapse (hne : W.vacuum ≠ 0) {w : ℤ} {u : V} (_hu : u ∈ W.grading w) (hqpu : W.L 1 u = 0)
    (_hw : 0 ≤ w) (a b : V) (n : ℤ) :
    canRHS hne u a b w n = (-1:ℂ)^w • canBilin W hne a (W.smul u (2*w - n - 2) b) := by
  rw [canRHS]
  congr 1
  rw [Finset.sum_eq_single 0]
  · rw [pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
      Nat.cast_zero, sub_zero]
  · intro j _ hj0
    -- j ≥ 1 : (L₁^j) u = L₁^(j-1)(L₁ u) = 0
    have hjpos : 1 ≤ j := by omega
    have hz : ((W.L 1) ^ j) u = 0 := by
      obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      rw [pow_succ, Module.End.mul_apply, hqpu, map_zero]
    rw [hz, PreVertexAlgebra.smul_zero_left, map_zero, smul_zero]
  · intro hcontra
    exact absurd (Finset.mem_range.mpr (by omega : 0 < w.toNat + 1)) hcontra

/-! ## STEP A — the a-tower lift for a quasi-primary `u`.

For quasi-primary `u ∈ 𝒱_w` (`L₁u = 0`), we prove
  `Pᵤ(a) : ∀ n b, canBilin(u₍n₎a, b) = (-1)^w • canBilin(a, u₍2w-n-2₎b)`
for ALL `a`.  Base case (homogeneous quasi-primary `a`) is `hMatch`; the L₋₁-closure step lifts it
through the sl₂ decomposition. -/

/-- The per-`u` statement `Pᵤ(a)`. -/
def StepA_P (hne : W.vacuum ≠ 0) {w : ℤ} (u : V) (a : V) : Prop :=
  ∀ (n : ℤ) (b : V),
    canBilin W hne (W.smul u n a) b = (-1:ℂ)^w • canBilin W hne a (W.smul u (2*w - n - 2) b)

/-- **The L₋₁-closure step.**  Assume `Pᵤ(a)` for ALL modes; then `Pᵤ(L₋₁a)`. -/
theorem stepA_Lneg1_closure (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    {w : ℤ} {u : V} (_hu : u ∈ W.grading w) (hqpu : W.L 1 u = 0)
    (a : V) (hPa : StepA_P (W := W) hne (w := w) u a) :
    StepA_P (W := W) hne (w := w) u (W.L (-1) a) := by
  intro n b
  -- LHS via canBilin_mode_lower:
  --   n • canBilin(u₍ₙ₋₁₎a, b) = canBilin(u₍ₙ₎(L₋₁a), b) − canBilin(u₍ₙ₎a, L₁b)
  -- so canBilin(u₍ₙ₎(L₋₁a), b) = n • canBilin(u₍ₙ₋₁₎a, b) + canBilin(u₍ₙ₎a, L₁b)
  have hlower := canBilin_mode_lower hne hqp u a b n
  have hLHS : canBilin W hne (W.smul u n (W.L (-1) a)) b
      = (n : ℂ) • canBilin W hne (W.smul u (n - 1) a) b
        + canBilin W hne (W.smul u n a) (W.L 1 b) := by
    rw [hlower]; abel
  rw [hLHS]
  -- apply Pᵤ(a) at (n-1, b) and at (n, L₁b):
  rw [hPa (n - 1) b, hPa n (W.L 1 b)]
  -- now LHS = n•(-1)^w•canBilin(a, u₍2w-(n-1)-2₎b) + (-1)^w•canBilin(a, u₍2w-n-2₎(L₁b))
  --        = n•(-1)^w•canBilin(a, u₍2w-n-1₎b) + (-1)^w•canBilin(a, u₍2w-n-2₎(L₁b))
  -- RHS via canBilin_Lneg1_adj: canBilin(L₋₁a, X) = canBilin(a, L₁X), at X = u₍2w-n-2₎b
  rw [show (2 * w - (n - 1) - 2 : ℤ) = 2 * w - n - 1 by ring]
  rw [canBilin_Lneg1_adj hne hqp a (W.smul u (2*w - n - 2) b)]
  -- L1_bracket_smul with L₁u=0 :
  --   L₁(u₍s₎b) − u₍s₎(L₁b) = (2w-s-2)•u₍s+1₎b + (L₁u)₍s₎b
  -- at s = 2w-n-2: L₁(u₍2w-n-2₎b) = u₍2w-n-2₎(L₁b) + n•u₍2w-n-1₎b
  have hbr := W.L1_bracket_smul _hu (2*w - n - 2) b
  rw [hqpu, PreVertexAlgebra.smul_zero_left, add_zero] at hbr
  have hcoeff : (2 * (w : ℂ) - ((2*w - n - 2 : ℤ) : ℂ) - 2) = (n : ℂ) := by push_cast; ring
  rw [hcoeff] at hbr
  have hidx : (2*w - n - 2 + 1 : ℤ) = 2*w - n - 1 := by ring
  rw [hidx] at hbr
  -- hbr : L₁(u₍2w-n-2₎b) − u₍2w-n-2₎(L₁b) = n•u₍2w-n-1₎b
  -- so L₁(u₍2w-n-2₎b) = u₍2w-n-2₎(L₁b) + n•u₍2w-n-1₎b
  have hL1 : W.L 1 (W.smul u (2*w - n - 2) b)
      = W.smul u (2*w - n - 2) (W.L 1 b) + (n : ℂ) • W.smul u (2*w - n - 1) b := by
    rw [← hbr]; abel
  rw [hL1, map_add, map_smul]
  -- now both sides:  n•(-1)^w•A + (-1)^w•B  =  (-1)^w•(B + n•A)
  module

/-! ## STEP A, homogeneous core: `Pᵤ(a)` for homogeneous `a`, by strong induction on grade. -/

theorem stepA_homog (hne : W.vacuum ≠ 0) (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    (hDecomp : DecompHyp W) (hMatch : MatchHyp W hne)
    {w : ℤ} {u : V} (hu : u ∈ W.grading w) (hqpu : W.L 1 u = 0) (_hw : 0 ≤ w) :
    ∀ (N : ℕ) {p : ℤ}, p.toNat ≤ N → ∀ {a : V}, a ∈ W.grading p → @StepA_P V _ _ W hne w u a := by
  intro N
  induction N with
  | zero =>
      intro p hpN a ha
      -- p.toNat ≤ 0 means p ≤ 0
      rcases lt_or_ge p 1 with hp1 | hp1
      · -- p ≤ 0
        rcases lt_or_ge p 0 with hpneg | hp0
        · -- p < 0 : a = 0
          have ha0 : a = 0 := eq_zero_of_mem_neg_grading W hpneg ha
          subst ha0
          intro n b
          simp
        · -- p = 0 : a ∈ ℂ𝟙, quasi-primary (L₁ of grade 0 lands in grade -1 = 0)
          have hp0' : p = 0 := by omega
          subst hp0'
          have hqpa : W.L 1 a = 0 := by
            have := L_one_lower W ha
            exact eq_zero_of_mem_neg_grading W (by norm_num) this
          intro n b
          exact hMatch hu hqpu ha hqpa n b
      · -- p ≥ 1 but p.toNat ≤ 0 — impossible
        omega
  | succ M ih =>
      intro p hpN a ha
      rcases lt_or_ge p 1 with hp1 | hp1
      · -- p ≤ 0 : same base treatment as N=0
        rcases lt_or_ge p 0 with hpneg | hp0
        · have ha0 : a = 0 := eq_zero_of_mem_neg_grading W hpneg ha
          subst ha0
          intro n b; simp
        · have hp0' : p = 0 := by omega
          subst hp0'
          have hqpa : W.L 1 a = 0 := by
            have := L_one_lower W ha
            exact eq_zero_of_mem_neg_grading W (by norm_num) this
          intro n b
          exact hMatch hu hqpu ha hqpa n b
      · -- p ≥ 1 : decompose a = a₀ + L₋₁c
        obtain ⟨a₀, c, ha₀mem, ha₀qp, hcmem, haeq⟩ := hDecomp hp1 ha
        subst haeq
        -- Pᵤ(a₀) from hMatch (a₀ quasi-primary in grade p)
        have hPa0 : @StepA_P V _ _ W hne w u a₀ := by
          intro n b
          exact hMatch hu hqpu ha₀mem ha₀qp n b
        -- Pᵤ(c) from IH (c ∈ grade (p-1), (p-1).toNat ≤ M)
        have hPc : @StepA_P V _ _ W hne w u c := by
          apply ih (p := p - 1) (by omega) hcmem
        -- Pᵤ(L₋₁c) by the closure step
        have hPLc : @StepA_P V _ _ W hne w u (W.L (-1) c) :=
          stepA_Lneg1_closure hne hqp hu hqpu c hPc
        -- Pᵤ(a₀ + L₋₁c) by additivity in a
        intro n b
        show canBilin W hne (W.smul u n (a₀ + W.L (-1) c)) b
          = (-1:ℂ)^w • canBilin W hne (a₀ + W.L (-1) c) (W.smul u (2*w - n - 2) b)
        rw [PreVertexAlgebra.smul_add_right, map_add, LinearMap.add_apply,
            map_add, LinearMap.add_apply, smul_add, hPa0 n b, hPLc n b]

/-- **STEP A lifted to all `a`.** For quasi-primary `u ∈ 𝒱_w` (`L₁u=0`, `0 ≤ w`), `Pᵤ(a)` holds
for every `a`. -/
theorem stepA_all (hne : W.vacuum ≠ 0) (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    (hDecomp : DecompHyp W) (hMatch : MatchHyp W hne)
    {w : ℤ} {u : V} (hu : u ∈ W.grading w) (hqpu : W.L 1 u = 0) (hw : 0 ≤ w) (a : V) :
    @StepA_P V _ _ W hne w u a := by
  intro n b
  have hatop : a ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading (motive := fun a =>
      canBilin W hne (W.smul u n a) b = (-1:ℂ)^w • canBilin W hne a (W.smul u (2*w - n - 2) b))
      hatop ?_ ?_ ?_
  · intro p a ha
    exact stepA_homog hne hqp hDecomp hMatch hu hqpu hw p.toNat le_rfl ha n b
  · show canBilin W hne (W.smul u n 0) b = (-1:ℂ)^w • canBilin W hne 0 (W.smul u (2*w - n - 2) b)
    simp
  · intro a₁ a₂ h₁ h₂
    show canBilin W hne (W.smul u n (a₁ + a₂)) b
      = (-1:ℂ)^w • canBilin W hne (a₁ + a₂) (W.smul u (2*w - n - 2) b)
    rw [PreVertexAlgebra.smul_add_right, map_add, LinearMap.add_apply,
        map_add, LinearMap.add_apply, smul_add, h₁, h₂]

/-- **STEP A as `CanFullyInvariantAt`-for-this-`u`.**  For quasi-primary `u ∈ 𝒱_w` (`L₁u=0`,
`0 ≤ w`), `canBilin(u₍n₎a, b) = canRHS u a b w n` for all `n, a, b`. -/
theorem stepA_fullyInvariant (hne : W.vacuum ≠ 0) (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    (hDecomp : DecompHyp W) (hMatch : MatchHyp W hne)
    {w : ℤ} {u : V} (hu : u ∈ W.grading w) (hqpu : W.L 1 u = 0) (hw : 0 ≤ w)
    (n : ℤ) (a b : V) :
    canBilin W hne (W.smul u n a) b = canRHS hne u a b w n := by
  rw [stepA_all hne hqp hDecomp hMatch hu hqpu hw a n b,
      canRHS_qp_collapse hne hu hqpu hw a b n]

/-! ## STEP B — the u-tower induction on `wt`.

`CanFullyInvariantAt hne wt` for all `wt`, by strong induction on `wt.toNat`.
Decompose `u = u₀ + L₋₁c` with `u₀` quasi-primary in grade `wt`, `c ∈ grade (wt-1)`.
Then `canBilin(·₍n₎a, b)` and `canRHS · a b wt n` are both additive in the `u`-slot:
- `u₀` (quasi-primary): STEP A.
- `L₋₁c`: translation mode `(L₋₁c)₍n₎ = -n•c₍n-1₎` on the LHS, IH at `wt-1` on `c`, and the
  `canRHS` sl₂ tower on the RHS, matched by reindexing the `j`-sum. -/

/-! ### The `canRHS` for `L₋₁c` matches the `L₋₁`-mode LHS via the sl₂ tower.

We show directly that for `c ∈ 𝒱_{wt-1}` and `0 ≤ wt`,
  `canRHS (L₋₁c) a b wt n = -n • canRHS c a b (wt-1) (n-1)`,
*given* the IH `canBilin(c₍m₎a',b') = canRHS c a' b' (wt-1) m` (used to keep things as `canBilin`s).
Actually we keep the comparison purely at the `canBilin` tower level using `L1pow_Lneg1`,
`smul_Lneg1_shift`, and `canBilin_Lneg1_adj`, mirroring `canBilin_vir_adj_n1`'s telescoping but in
the `u`-slot. -/

/-- **The STEP B telescoping** (pure `ℂ`).  For `F : ℕ → ℂ` with `F (K+1) = 0`:
`∑_{j≤K+1} (1/j!)[-(2cc-nn-j)·F j + j(2cc-j+1)·F(j-1)] = nn·∑_{j≤K} (1/j!)·F j`. -/
theorem stepB_telescope (K : ℕ) (cc nn : ℂ) (F : ℕ → ℂ) (hF : F (K + 1) = 0) :
    (∑ j ∈ Finset.range (K + 1 + 1), ((j.factorial : ℂ)⁻¹) *
        (-(2 * cc - nn - (j : ℂ)) * F j + ((j : ℂ) * (2 * cc - (j : ℂ) + 1)) * F (j - 1)))
      = nn * ∑ j ∈ Finset.range (K + 1), ((j.factorial : ℂ)⁻¹) * F j := by
  -- split the sum
  rw [show (∑ j ∈ Finset.range (K + 1 + 1), ((j.factorial : ℂ)⁻¹) *
          (-(2 * cc - nn - (j : ℂ)) * F j + ((j : ℂ) * (2 * cc - (j : ℂ) + 1)) * F (j - 1)))
        = (∑ j ∈ Finset.range (K + 1 + 1), ((j.factorial : ℂ)⁻¹) * (-(2 * cc - nn - (j : ℂ)) * F j))
          + (∑ j ∈ Finset.range (K + 1 + 1),
              ((j.factorial : ℂ)⁻¹) * (((j : ℂ) * (2 * cc - (j : ℂ) + 1)) * F (j - 1))) from by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun j _ => by ring)]
  -- second sum: reindex j = i+1 (j=0 term vanishes), giving ∑_{i≤K} (1/i!)(2cc - i)·F i
  rw [Finset.sum_range_succ' (fun j => ((j.factorial : ℂ)⁻¹) *
        (((j : ℂ) * (2 * cc - (j : ℂ) + 1)) * F (j - 1))) (K + 1)]
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
  have hreidx : ∀ i ∈ Finset.range (K + 1),
      (((i + 1).factorial : ℂ)⁻¹) *
          ((((i + 1 : ℕ) : ℂ)) * (2 * cc - ((i + 1 : ℕ) : ℂ) + 1) * F ((i + 1) - 1))
        = ((i.factorial : ℂ)⁻¹) * ((2 * cc - (i : ℂ)) * F i) := by
    intro i _
    rw [Nat.factorial_succ, Nat.cast_mul]
    have hfac : ((i.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
    have hi1 : ((i : ℂ) + 1) ≠ 0 := by
      have : ((i + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
      push_cast at this; exact this
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl hreidx]
  -- first sum: top term j=K+1 has F(K+1)=0, drop it
  rw [Finset.sum_range_succ (fun j => ((j.factorial : ℂ)⁻¹) *
        (-(2 * cc - nn - (j : ℂ)) * F j)) (K + 1), hF, mul_zero, mul_zero, add_zero]
  -- combine the two ∑_{j≤K} sums and factor out nn
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- **STEP B for the `L₋₁c` piece.**  For `c ∈ 𝒱_{wt-1}` with `0 ≤ wt`, the LHS translation-mode
identity and the `canRHS` sl₂ tower agree, *given* the IH at weight `wt-1` (as
`CanFullyInvariantAt hne (wt-1)`). -/
theorem stepB_Lneg1c (hne : W.vacuum ≠ 0)
    {wt : ℤ} (hwt : 0 ≤ wt) {c : V} (hc : c ∈ W.grading (wt - 1))
    (hIH : CanFullyInvariantAt hne (wt - 1)) (n : ℤ) (a b : V) :
    canBilin W hne (W.smul (W.L (-1) c) n a) b = canRHS hne (W.L (-1) c) a b wt n := by
  -- LHS: (L₋₁c)₍n₎a = -n • c₍n-1₎a  (translation mode)
  rw [W.smul_Lneg1_shift c a n, map_smul, LinearMap.smul_apply, smul_eq_mul]
  -- now LHS = (-n) • canBilin(c₍n-1₎a, b)
  -- apply IH: canBilin(c₍n-1₎a, b) = canRHS c a b (wt-1) (n-1)
  rw [hIH c hc (n - 1) a b]
  -- RHS: canRHS (L₋₁c) a b wt n.  Expand both canRHS and compare term by term.
  rw [canRHS, canRHS]
  -- set k := (wt-1).toNat ; wt.toNat = k+1 since wt ≥ 1 (else c = 0 path handled below)
  rcases eq_or_lt_of_le hwt with hwt0 | hwt1
  · -- wt = 0 : then wt-1 = -1 < 0, c = 0
    have hc0 : c = 0 := eq_zero_of_mem_neg_grading W (by omega) hc
    subst hc0
    simp
  · -- wt ≥ 1
    have hwtn : (0:ℤ) ≤ wt - 1 := by omega
    set K : ℕ := (wt - 1).toNat with hK
    have hKwt : wt.toNat = K + 1 := by rw [hK]; omega
    have hKval : ((K : ℤ)) = wt - 1 := by rw [hK]; omega
    rw [hKwt]
    -- LHS:  (-n) • ((-1)^(wt-1) • ∑_{j≤K} (1/j!) canBilin(a, (L₁ʲc)₍2(wt-1)-(n-1)-2-j₎b))
    -- RHS:  (-1)^wt • ∑_{j≤K+1} (1/j!) canBilin(a, (L₁ʲ(L₋₁c))₍2wt-n-2-j₎b)
    -- Use the sl₂ tower L1pow_Lneg1 on each (L₁ʲ(L₋₁c)) in the RHS.
    -- We compute the RHS sum and show it equals (-n)•(-1)^(wt-1)•(LHS-inner).
    -- Define F j := canBilin(a, (L₁ʲc)₍2(wt-1)-(n-1)-2-j₎b)   [the LHS inner summand]
    -- and the RHS summand expands via L1pow_Lneg1 into two pieces.
    -- We instead transform the RHS directly.
    -- First rewrite the sign: (-1)^wt = -(-1)^(wt-1).
    have hsign : (-1:ℂ)^wt = -((-1:ℂ)^(wt-1)) := by
      rw [show wt = (wt - 1) + 1 by ring, zpow_add₀ (by norm_num : (-1:ℂ) ≠ 0), zpow_one]
      ring
    rw [hsign]
    -- Move scalars: LHS = (-n) • ((-1)^(wt-1) • sL),  RHS = (-(-1)^(wt-1)) • sR.
    -- Define the diagonal atom F i := canBilin(a, (L₁ⁱc)₍2kk - n - 1 - i₎ b)  [kk = wt-1].
    -- Both sums reduce to F: sL = ∑_{j≤K} (1/j!) F j; sR-summand = (1/j!)[-(2kk-n-j)F j + j(2kk-j+1)F(j-1)].
    -- Then `stepB_telescope` gives sR = n • sL, and `module` closes.
    set kk : ℤ := wt - 1 with hkk
    set F : ℕ → ℂ := fun i =>
      canBilin W hne a (W.smul ((W.L 1 ^ i) c) (2 * kk - n - 1 - (i : ℤ)) b) with hF
    set sL : ℂ := ∑ j ∈ Finset.range (K + 1), ((j.factorial : ℂ)⁻¹) •
        canBilin W hne a (W.smul ((W.L 1 ^ j) c) (2 * (wt - 1) - (n - 1) - 2 - (j : ℤ)) b)
      with hsL
    set sR : ℂ := ∑ j ∈ Finset.range (K + 1 + 1), ((j.factorial : ℂ)⁻¹) •
        canBilin W hne a (W.smul ((W.L 1 ^ j) (W.L (-1) c)) (2 * wt - n - 2 - (j : ℤ)) b)
      with hsR
    show (-n : ℂ) • ((-1:ℂ)^(wt-1) • sL) = (-((-1:ℂ)^(wt-1))) • sR
    -- sL = ∑_{j≤K} (1/j!) • F j  (the LHS index 2(wt-1)-(n-1)-2-j = 2kk-n-1-j).
    have hsL_F : sL = ∑ j ∈ Finset.range (K + 1), ((j.factorial : ℂ)⁻¹) * F j := by
      rw [hsL]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hF]; simp only [smul_eq_mul]
      rw [show (2 * (wt - 1) - (n - 1) - 2 - (j:ℤ)) = 2 * kk - n - 1 - (j:ℤ) by rw [hkk]; ring]
    -- sR-summand expansion via the sl₂ tower.
    have hsR_F : sR = ∑ j ∈ Finset.range (K + 1 + 1), ((j.factorial : ℂ)⁻¹) *
        (-(2 * (kk:ℂ) - (n:ℂ) - (j:ℂ)) * F j
          + ((j:ℂ) * (2 * (kk:ℂ) - (j:ℂ) + 1)) * F (j - 1)) := by
      rw [hsR]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      -- the sl₂ tower on (L₁ʲ(L₋₁c)) at the RHS index, evaluated inside canBilin(a, ·)
      have hpiece1 : canBilin W hne a (W.smul (W.L (-1) ((W.L 1 ^ j) c)) (2 * kk - n - (j:ℤ)) b)
          = -(2 * (kk:ℂ) - (n:ℂ) - (j:ℂ)) * F j := by
        rw [W.smul_Lneg1_shift ((W.L 1 ^ j) c) b (2 * kk - n - (j:ℤ)), map_smul, smul_eq_mul, hF]
        simp only
        rw [show (2 * kk - n - (j:ℤ) - 1) = 2 * kk - n - 1 - (j:ℤ) by ring]
        push_cast; ring
      have hpiece2 : canBilin W hne a
            (W.smul (((j:ℂ) * (2 * (kk:ℂ) - (j:ℂ) + 1)) • (W.L 1 ^ (j-1)) c) (2 * kk - n - (j:ℤ)) b)
          = ((j:ℂ) * (2 * (kk:ℂ) - (j:ℂ) + 1)) * F (j - 1) := by
        rw [PreVertexAlgebra.smul_smul_left, map_smul, smul_eq_mul, hF]
        simp only
        rcases Nat.eq_zero_or_pos j with hj0 | hjpos
        · subst hj0; simp
        · rw [show (2 * kk - n - (j:ℤ)) = 2 * kk - n - 1 - (((j-1 : ℕ)):ℤ) by
                rw [Nat.cast_sub hjpos]; push_cast; ring]
      rw [L1pow_Lneg1 hc j]
      rw [show (2 * wt - n - 2 - (j:ℤ)) = 2 * kk - n - (j:ℤ) by rw [hkk]; ring]
      rw [PreVertexAlgebra.smul_add_left, map_add, smul_eq_mul, mul_add, hpiece1, hpiece2]
      ring
    have hFvanish : F (K + 1) = 0 := by
      rw [hF]; simp only
      have hz : ((W.L 1) ^ (K + 1)) c = 0 :=
        L_one_pow_eq_zero W hc (by simp only [Nat.cast_add, Nat.cast_one, hKval]; omega)
      rw [hz, PreVertexAlgebra.smul_zero_left, map_zero]
    have hkey : sR = (n : ℂ) • sL := by
      rw [hsR_F, hsL_F, smul_eq_mul]
      exact stepB_telescope K (kk:ℂ) (n:ℂ) F hFvanish
    rw [hkey]
    module

/-! ### STEP B main: `CanFullyInvariantAt hne wt` for every `wt`, by strong induction on `wt.toNat`. -/

theorem stepB_fullyInvariant (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    (hDecomp : DecompHyp W) (hMatch : MatchHyp W hne) :
    ∀ (wt : ℤ), CanFullyInvariantAt hne wt := by
  have key : ∀ (N : ℕ) (wt : ℤ), wt.toNat ≤ N → CanFullyInvariantAt hne wt := by
    intro N
    induction N with
    | zero =>
        intro wt hwtN
        rcases lt_or_ge wt 0 with hwt | hwt
        · exact canFullyInvariantAt_neg hne hwt
        · have hwt0 : wt = 0 := by omega
          subst hwt0
          exact canFullyInvariantAt_zero hne
    | succ M ih =>
        intro wt hwtN
        rcases lt_or_ge wt 0 with hwt | hwt
        · exact canFullyInvariantAt_neg hne hwt
        · rcases eq_or_lt_of_le hwt with hwt0 | hwt1
          · subst hwt0; exact canFullyInvariantAt_zero hne
          · -- wt ≥ 1 : decompose u = u₀ + L₋₁c
            intro u hu n a b
            obtain ⟨u₀, c, hu₀mem, hu₀qp, hcmem, hueq⟩ := hDecomp (by omega : (1:ℤ) ≤ wt) hu
            subst hueq
            -- additivity in the u-slot for both sides
            rw [PreVertexAlgebra.smul_add_left, map_add, LinearMap.add_apply, canRHS_add_u]
            congr 1
            · -- u₀ (quasi-primary) : STEP A
              exact stepA_fullyInvariant hne hqp hDecomp hMatch hu₀mem hu₀qp (by omega) n a b
            · -- L₋₁c : STEP B Lneg1c, with IH at wt-1
              have hIH : CanFullyInvariantAt hne (wt - 1) := ih (wt - 1) (by omega)
              exact stepB_Lneg1c hne (by omega) hcmem hIH n a b
  intro wt
  exact key wt.toNat wt le_rfl

/-! ## TARGET: `canDiagonal_holds`. -/

/-- **`CanDiagonal hne`**, from the two FHL hypotheses.  `CanFullyInvariantAt hne wt` (proved for all
`wt`) at the matching mode `n = p + wt - q - 1` for homogeneous `a, b` IS the diagonal. -/
theorem canDiagonal_holds (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    (hDecomp : DecompHyp W) (hMatch : MatchHyp W hne) :
    CanDiagonal hne := by
  intro wt p q u a b hu _ha _hb
  exact stepB_fullyInvariant hne hqp hDecomp hMatch wt u hu (p + wt - q - 1) a b



/-! ## Discharge: `CanDiagonal` unconditionally (under `hqp`, `hne`). -/

/-- **`CanDiagonal hne`** (under `hqp : L₁𝒱₁=0` only).  The two FHL hypotheses of
`canDiagonal_holds` are discharged by `qpDecomp` (sl₂ decomposition) and `canBilin_qp_qp_adj`
(general-weight matching). -/
theorem canDiagonal_unconditional (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) : CanDiagonal hne :=
  canDiagonal_holds hne hqp (fun {_p} hp {_a} ha => qpDecomp W hqp hp ha)
    (fun {_w} {_u} hu hqpu {_p} {_a} ha hqpa n b => canBilin_qp_qp_adj hne hqp hu hqpu ha hqpa n b)


/-! ## `L₁ω = 0` (ω is quasi-primary): from `ω = L₋₂𝟙`, the Virasoro bracket `[L₁,L₋₂]=3L₋₁`,
and `L₋₁𝟙 = L₁𝟙 = 0`. -/
theorem L1_conformal_zero (W : VertexOperatorAlgebra V) :
    W.L 1 W.conformalVector = 0 := by
  -- ω = L₋₂ 𝟙
  have hω : W.conformalVector = W.L (-2) W.vacuum := by
    rw [L_def, show (-2 + 1 : ℤ) = -1 by ring, ← PreVertexAlgebra.smul_def, W.smul_vacuum_neg_one]
  -- L₁𝟙 = 0  (creation, mode 2 ≥ 0)
  have hL1vac : W.L 1 W.vacuum = 0 := by
    rw [L_def, show (1 + 1 : ℤ) = 2 by ring, ← PreVertexAlgebra.smul_def,
      W.toPreVertexAlgebra.smul_vacuum_nonneg W.conformalVector (by norm_num : (0:ℤ) ≤ 2)]
  -- L₋₁𝟙 = 0
  have hLm1vac : W.L (-1) W.vacuum = 0 := L_neg_one_vacuum W
  -- L₁(L₋₂𝟙) = [L₁,L₋₂]𝟙 + L₋₂(L₁𝟙)
  have hbr := W.L_virasoro 1 (-2)
  rw [show (1 + (-2) : ℤ) = -1 by ring, if_neg (by norm_num : ¬ (-1 : ℤ) = 0), add_zero] at hbr
  -- hbr : ⁅L 1, L (-2)⁆ = (1-(-2)) • L (-1) = 3 • L (-1)
  rw [hω]
  have hcomm : W.L 1 (W.L (-2) W.vacuum)
      = (⁅W.L 1, W.L (-2)⁆ : Module.End ℂ V) W.vacuum + W.L (-2) (W.L 1 W.vacuum) := by
    rw [LieRing.of_associative_ring_bracket]
    simp only [LinearMap.sub_apply, Module.End.mul_apply]
    abel
  rw [hcomm, hbr, hL1vac, map_zero, add_zero, LinearMap.smul_apply, hLm1vac, smul_zero]

/-! ## `CanDiagonal ⟹ CanVirasoroAdj` (the `u = ω` slice; `L₁ω = 0` collapses the sum). -/
theorem canVirasoroAdj_of_diagonal (hne : W.vacuum ≠ 0) (hdiag : CanDiagonal hne) :
    CanVirasoroAdj W hne := by
  intro k a b
  -- L k a = ω₍k+1₎ a
  have hLk : W.L k a = W.smul W.conformalVector (k + 1) a := by rw [L_def, PreVertexAlgebra.smul_def]
  have hLmk : W.smul W.conformalVector (1 - k) b = W.L (-k) b := by
    rw [L_def, PreVertexAlgebra.smul_def, show (-k + 1 : ℤ) = 1 - k by ring]
  rw [hLk]
  have hfull := canBilin_fullyInvariant_of_diagonal hne hdiag 2 W.conformalVector
    W.conformal_mem (k + 1) a b
  rw [hfull, show ((2 : ℤ).toNat + 1) = 3 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  -- j = 1 and j = 2 terms vanish (L₁ω = 0)
  have hL1ω : (W.L 1 ^ 1) W.conformalVector = 0 := by rw [pow_one]; exact L1_conformal_zero W
  have hL2ω : (W.L 1 ^ 2) W.conformalVector = 0 := by
    rw [pow_two, Module.End.mul_apply, L1_conformal_zero W, map_zero]
  rw [show ((1:ℕ) : ℤ) = 1 by rfl] at *
  simp only [hL1ω, hL2ω, PreVertexAlgebra.smul_zero_left, map_zero, smul_zero, add_zero]
  -- j = 0 term: (-1)^2 • (1/0!) • canBilin a (ω₍2*2-(k+1)-2-0₎ b) = canBilin a (L (-k) b)
  rw [pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    Nat.cast_zero, show (2 * 2 - (k + 1) - 2 - (0:ℤ)) = 1 - k by ring, hLmk]
  norm_num

/-! ## The `Core/BilinearForm` main results for the canonical form, under `hne`, `hqp` only. -/

/-- The raw Li/FHL form, with Gannon vacuum norm `-1`, given `CanDiagonal` (which the sections above supply
under `L₁𝒱₁=0`). -/
noncomputable def gannonCanFormFHL (hne : W.vacuum ≠ 0)
    (hdiag : CanDiagonal hne) : InvariantForm W :=
  canForm hne (canVirasoroAdj_of_diagonal hne hdiag)

/-- The raw Gannon-normalised form is fully invariant. -/
theorem gannonCanFormFHL_isFullyInvariant (hne : W.vacuum ≠ 0) (hdiag : CanDiagonal hne) :
    (gannonCanFormFHL hne hdiag).IsFullyInvariant := by
  intro wt u hu n a b
  show canBilin W hne (W.smul u n a) b
      = (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) •
          canBilin W hne a (W.smul (((W.L 1) ^ j) u) (2 * wt - n - 2 - (j : ℤ)) b)
  exact canBilin_fullyInvariant_of_diagonal hne hdiag wt u hu n a b

/-- The raw Li/FHL form has Gannon vacuum norm `-1`. -/
theorem gannonCanFormFHL_gannonNormalized (hne : W.vacuum ≠ 0) (hdiag : CanDiagonal hne) :
    (gannonCanFormFHL hne hdiag).GannonNormalized := canBilin_vacuum hne

/-- The public canonical form GIVEN `CanDiagonal`: the negative of the raw Gannon form, hence
vacuum norm `+1`. -/
noncomputable def canFormFHL (hne : W.vacuum ≠ 0) (hdiag : CanDiagonal hne) : InvariantForm W :=
  InvariantForm.neg (gannonCanFormFHL hne hdiag)

@[simp] theorem canFormFHL_form_apply (hne : W.vacuum ≠ 0) (hdiag : CanDiagonal hne)
    (a b : V) : (canFormFHL hne hdiag).form a b = -canBilin W hne a b := by
  rw [canFormFHL, InvariantForm.neg_form_apply]
  rfl

theorem canFormFHL_isFullyInvariant (hne : W.vacuum ≠ 0) (hdiag : CanDiagonal hne) :
    (canFormFHL hne hdiag).IsFullyInvariant :=
  (gannonCanFormFHL_isFullyInvariant hne hdiag).neg

theorem canFormFHL_normalized (hne : W.vacuum ≠ 0) (hdiag : CanDiagonal hne) :
    (canFormFHL hne hdiag).Normalized :=
  (gannonCanFormFHL_gannonNormalized hne hdiag).neg

/-- **Uniqueness (5.1.11b), unconditional for the canonical form.** Any fully-invariant
normalised form equals the canonical one. -/
theorem invariantForm_unique_canonical (hne : W.vacuum ≠ 0) (hdiag : CanDiagonal hne)
    {B : InvariantForm W} (hB : B.IsFullyInvariant) (hn : B.Normalized) :
    B.form = (canFormFHL hne hdiag).form :=
  InvariantForm.invariantForm_unique hB (canFormFHL_isFullyInvariant hne hdiag) hn
    (canFormFHL_normalized hne hdiag)

/-- **Nondegeneracy (5.1.11b), unconditional for the canonical form** on a simple VOA. -/
theorem invariantForm_nondegenerate_canonical (hne : W.vacuum ≠ 0) (hdiag : CanDiagonal hne)
    (hsimple : W.IsSimple) :
    InvariantForm.leftRadical (canFormFHL hne hdiag) = ⊥ :=
  InvariantForm.invariantForm_nondegenerate hsimple (canFormFHL_isFullyInvariant hne hdiag)
    (canFormFHL_normalized hne hdiag)

/-- **`𝒱₁`-evaluation, unconditional for the unit-normalised canonical form**:
`u₍₁₎v = -(u|v)·𝟙`. -/
theorem eval_oneMode_grading1_canonical (hne : W.vacuum ≠ 0) (hdiag : CanDiagonal hne)
    {u v : V} (hu : u ∈ W.grading 1) (hv : v ∈ W.grading 1) :
    W.smul u 1 v = -(canFormFHL hne hdiag).form u v • W.vacuum :=
  InvariantForm.eval_oneMode_grading1 (canFormFHL_isFullyInvariant hne hdiag)
    (canFormFHL_normalized hne hdiag) hu hv


/-! ## The canonical invariant form: fully invariant (under `hne`, `hqp` only) and
unit-normalised. -/

/-- The canonical invariant form as a genuine fully-invariant normalised `InvariantForm`, under the
standing hypotheses `hne` and `hqp` (no `CanDiagonal`/`IsFullyInvariant` hypothesis — they are proved). -/
noncomputable def canonicalInvariantForm (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) : InvariantForm W :=
  canFormFHL hne (canDiagonal_unconditional hne hqp)

theorem canonicalInvariantForm_isFullyInvariant (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) :
    (canonicalInvariantForm hne hqp).IsFullyInvariant :=
  canFormFHL_isFullyInvariant hne (canDiagonal_unconditional hne hqp)

theorem canonicalInvariantForm_normalized (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) :
    (canonicalInvariantForm hne hqp).Normalized :=
  canFormFHL_normalized hne (canDiagonal_unconditional hne hqp)

/-- **Uniqueness** (under `hne`, `hqp` only). Every fully-invariant unit-normalised form equals the
canonical one. -/
theorem invariantForm_unique_FHL (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {B : InvariantForm W}
    (hB : B.IsFullyInvariant) (hn : B.Normalized) :
    B.form = (canonicalInvariantForm hne hqp).form :=
  invariantForm_unique_canonical hne (canDiagonal_unconditional hne hqp) hB hn

/-- **Nondegeneracy** (simple VOA; under `hne`, `hqp` only). -/
theorem invariantForm_nondegenerate_FHL (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) (hsimple : W.IsSimple) :
    InvariantForm.leftRadical (canonicalInvariantForm hne hqp) = ⊥ :=
  invariantForm_nondegenerate_canonical hne (canDiagonal_unconditional hne hqp) hsimple

/-- **`𝒱₁`-evaluation** (under `hne`, `hqp` only) for the unit-normalised form:
`u₍₁₎v = -(u|v)·𝟙`. -/
theorem eval_oneMode_grading1_FHL (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {u v : V}
    (hu : u ∈ W.grading 1) (hv : v ∈ W.grading 1) :
    W.smul u 1 v = -(canonicalInvariantForm hne hqp).form u v • W.vacuum :=
  eval_oneMode_grading1_canonical hne (canDiagonal_unconditional hne hqp) hu hv

end VOA
