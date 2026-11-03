/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.InvariantFormCanonicalFHL

/-!
# The `n = −1` Virasoro adjointness of the canonical form, under quasi-primarity `L₁𝒱₁ = 0`

The single identity `virSlice_vacuum` proved necessary-and-sufficient for the canonical form's
invariance — `canBilin(L₋₁a, b) = canBilin(a, L₁b)` — **proved** under Gannon's standing
hypothesis `L₁𝒱₁ = 0` (5.1.11b / quasi-primarity), via the genuine Li mechanism.

* **`vacCoord_mode_shift`** — `vacCoord(u₍ₘ₎(L₋₁c)) = m·vacCoord(u₍ₘ₋₁₎c)`.
* **`vacCoord_L1_eq_zero`** — under `L₁𝒱₁=0`, `vacCoord(L₁b) = 0` (the obstruction-killer).
* **`L1pow_Lneg1`** — the sl₂ tower `L₁ʲL₋₁a = L₋₁L₁ʲa + j(2k−j+1)L₁^{j−1}a`.
* **`canBilin_Lneg1_adj`** (homogeneous core `canBilin_vir_adj_n1`) — `canBilin(L₋₁a, b) =
  canBilin(a, L₁b)` for all `a, b` (the `n=−1` Virasoro adjointness `CanVirasoroAdj (-1)`), proved
  under the quasi-primarity hypothesis.
* **`canDiagonal_wt_le_zero`** — the matching-mode diagonal at every `wt ≤ 0`, unconditional.

## Status
**The residual is discharged in `Core.InvariantFormFHL2`.**  The residual named below is discharged, under the
standing hypotheses `hne : 𝟙 ≠ 0` and `hqp : L₁𝒱₁ = 0`, by `canDiagonal_unconditional : CanDiagonal hne`
and `canVirasoroAdj_of_diagonal`; the resulting form is `canonicalInvariantForm`.  The text below
describes this file's own reduction, an intermediate step.
Axiom-free reduction; bottoms out at the residual `CanDiagonal` (the `wt ≥ 1`
matching-mode diagonal / Li Prop 2.6) (→ Li 1994; discharged, see above).
Axiom-clean (the `n=−1` Virasoro adjointness, the levers, the `wt ≤ 0` diagonal — all under the
explicit `L₁𝒱₁=0` hypothesis where required). The remaining content of full canonical-form FHL in this file is
the `wt ≥ 1` matching-mode diagonal (the Li Prop 2.6 two-point computation): the path is
`canBilin_Lneg1_adj ⟹` a canBilin-native `form_smul_skew` `⟹` the `ResidualFHL` (`skewRHS = canRHS`).

## References
* Gannon §5.1.3, eqs. (5.1.11)–(5.1.12); Frenkel–Huang–Lepowsky [199]; Li [380].
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators
open Classical

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-! ## Levers -/

/-- `vacCoord` mode-shift: `vacCoord(u₍ₘ₎(L₋₁c)) = m·vacCoord(u₍ₘ₋₁₎c)` for homogeneous `u, c`. -/
theorem vacCoord_mode_shift (hne : W.vacuum ≠ 0) {pu pc : ℤ} {u c : V}
    (hu : u ∈ W.grading pu) (hc : c ∈ W.grading pc) (m : ℤ) :
    vacCoord W hne (W.smul u m (W.L (-1) c)) = (m : ℂ) • vacCoord W hne (W.smul u (m-1) c) := by
  have hderiv := W.L_neg_one_deriv u c m
  have heq : W.smul u m (W.L (-1) c) = W.L (-1) (W.smul u m c) - W.smul (W.L (-1) u) m c := by
    rw [← hderiv]; abel
  rw [heq, map_sub]
  have humc : W.smul u m c ∈ W.grading (pu + pc - m - 1) := W.smul_mem_grading hu hc m
  rw [vacCoord_Lneg1_homog hne humc, zero_sub]
  rw [W.smul_Lneg1_shift u c m, map_smul]
  rw [neg_smul, neg_neg]

/-- **The obstruction-killer.** Under Gannon's quasi-primarity hypothesis `L₁𝒱₁ = 0`,
`vacCoord(L₁b) = 0` for every `b`: the grade-0 part of `L₁b` is `L₁` of the grade-1 part of `b`. -/
theorem vacCoord_L1_eq_zero (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) (b : V) :
    vacCoord W hne (W.L 1 b) = 0 := by
  have hbtop : b ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading (motive := fun b =>
      vacCoord W hne (W.L 1 b) = 0) hbtop ?_ ?_ ?_
  · intro q b hb
    have hL1 : W.L 1 b ∈ W.grading (q - 1) := L_one_lower W hb
    rcases eq_or_ne (q - 1) 0 with hq | hq
    · have hq1 : q = 1 := by omega
      subst hq1; rw [hqp b hb, map_zero]
    · exact vacCoord_of_mem_ne W hne hq hL1
  · show vacCoord W hne (W.L 1 0) = 0
    rw [map_zero, map_zero]
  · intro b₁ b₂ hb₁ hb₂
    show vacCoord W hne (W.L 1 (b₁ + b₂)) = 0
    rw [map_add, map_add, hb₁, hb₂, add_zero]

/-! ## `𝔰𝔩₂` tower -/

/-- `L₁(L₋₁x) = L₋₁(L₁x) + 2 L₀x` (from `[L₁,L₋₁] = 2L₀`). -/
theorem L1_Lneg1_apply (x : V) :
    W.L 1 (W.L (-1) x) = W.L (-1) (W.L 1 x) + (2:ℂ) • W.L 0 x := by
  have h := W.L_one_L_neg_one
  rw [LieRing.of_associative_ring_bracket] at h
  have h2 := DFunLike.congr_fun h x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h2
  rw [← h2]; abel

private theorem nsmul_L1_pred (a : V) (n : ℕ) (c : ℂ) :
    ((n:ℂ) * c) • W.L 1 ((W.L 1 ^ (n-1)) a) = ((n:ℂ) * c) • ((W.L 1 ^ n) a) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · congr 1
    rw [← Module.End.mul_apply, ← pow_succ', show n - 1 + 1 = n by omega]

/-- **The `𝔰𝔩₂` tower** on a weight-`k` vector: `L₁ʲ(L₋₁a) = L₋₁(L₁ʲa) + j(2k-j+1)·L₁^{j-1}a`. -/
theorem L1pow_Lneg1 {k : ℤ} {a : V} (ha : a ∈ W.grading k) (j : ℕ) :
    (W.L 1 ^ j) (W.L (-1) a)
      = W.L (-1) ((W.L 1 ^ j) a)
        + ((j : ℂ) * (2 * (k:ℂ) - j + 1)) • ((W.L 1 ^ (j-1)) a) := by
  induction j with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    rw [map_add, L1_Lneg1_apply]
    have hmem : (W.L 1 ^ n) a ∈ W.grading (k - n) := L_one_pow_mem W ha n
    rw [W.L_zero_grading _ hmem, map_smul, smul_smul]
    have hpow2 : W.L 1 ((W.L 1 ^ n) a) = (W.L 1 ^ (n+1)) a := by
      rw [← Module.End.mul_apply, ← pow_succ']
    rw [hpow2, show (n+1) - 1 = n by omega]
    rw [nsmul_L1_pred a n (2 * (k:ℂ) - n + 1)]
    rw [← pow_succ' (W.L 1) n]
    rw [add_assoc, ← add_smul]
    congr 2
    rw [Int.cast_sub, Int.cast_natCast]
    push_cast; ring

/-! ## Per-`j` summand identities (`F(i) := vacCoord((L₁ⁱa)₍2k−i₎b)`) -/

/-- LHS summand: `vacCoord((L₁ʲL₋₁a)₍2k+1−j₎b) = −(2k+1−j)F(j) + j(2k−j+1)F(j−1)`.
Pure `𝔰𝔩₂`-tower + `L₋₁` mode-shift (no hypothesis). -/
theorem lhs_summand (hne : W.vacuum ≠ 0)
    {k : ℤ} {a : V} (ha : a ∈ W.grading k) (b : V) (j : ℕ) :
    vacCoord W hne (W.smul ((W.L 1 ^ j) (W.L (-1) a)) (2*k+1-j) b)
      = -(2*(k:ℂ)+1-j) * vacCoord W hne (W.smul ((W.L 1 ^ j) a) (2*k-j) b)
        + ((j:ℂ)*(2*(k:ℂ)-j+1)) * vacCoord W hne (W.smul ((W.L 1 ^ (j-1)) a) (2*k-(j-1)) b) := by
  rw [L1pow_Lneg1 ha j]
  rw [PreVertexAlgebra.smul_add_left, map_add]
  congr 1
  · rw [W.smul_Lneg1_shift, map_smul]
    rw [show (2*k+1-(j:ℤ)-1) = 2*k-(j:ℤ) by ring]
    push_cast; ring
  · rw [PreVertexAlgebra.smul_smul_left, map_smul]
    rw [show (2*k+1-(j:ℤ)) = 2*k-((j:ℤ)-1) by ring]
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj; simp
    · rw [show ((j:ℤ)-1) = ((j-1 : ℕ):ℤ) by omega]
      ring

/-- RHS summand: `vacCoord((L₁ʲa)₍2k−1−j₎(L₁b)) = (j+1)F(j) − F(j+1)` under `L₁𝒱₁=0`.
The obstruction `vacCoord(L₁(…))` is killed by `vacCoord_L1_eq_zero`. -/
theorem rhs_summand (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    {k : ℤ} {a : V} (ha : a ∈ W.grading k) (b : V) (j : ℕ) :
    vacCoord W hne (W.smul ((W.L 1 ^ j) a) (2*k-1-j) (W.L 1 b))
      = ((j:ℂ)+1) * vacCoord W hne (W.smul ((W.L 1 ^ j) a) (2*k-j) b)
        - vacCoord W hne (W.smul ((W.L 1 ^ (j+1)) a) (2*k-(j+1)) b) := by
  have hmem : (W.L 1 ^ j) a ∈ W.grading (k - j) := L_one_pow_mem W ha j
  have hbr := W.L1_bracket_smul hmem (2*k-1-(j:ℤ)) b
  push_cast at hbr
  have heq : W.smul ((W.L 1 ^ j) a) (2*k-1-(j:ℤ)) (W.L 1 b)
      = W.L 1 (W.smul ((W.L 1 ^ j) a) (2*k-1-(j:ℤ)) b)
        - ((2 * ((k:ℂ) - j) - (2 * (k:ℂ) - 1 - j) - 2) • W.smul ((W.L 1 ^ j) a) (2*k-1-(j:ℤ)+1) b
        + W.smul (W.L 1 ((W.L 1 ^ j) a)) (2*k-1-(j:ℤ)) b) := by
    rw [← hbr]; abel
  rw [heq, map_sub, map_add, map_smul]
  rw [vacCoord_L1_eq_zero hne hqp]
  rw [show (2 * ((k:ℂ) - j) - (2 * (k:ℂ) - 1 - j) - 2) = (-(j:ℂ)-1) by ring]
  rw [show W.L 1 ((W.L 1 ^ j) a) = (W.L 1 ^ (j+1)) a by rw [← Module.End.mul_apply, ← pow_succ']]
  rw [show (2*k-1-(j:ℤ)+1) = 2*k-(j:ℤ) by ring, show (2*k-1-(j:ℤ)) = 2*k-((j:ℤ)+1) by ring]
  ring

/-! ## Telescoping (pure `ℂ`) -/

theorem lhs_telescope (M : ℕ) (k : ℂ) (F : ℕ → ℂ) (hF : F M = 0) :
    (∑ j ∈ Finset.range (M+1), ((j.factorial:ℂ)⁻¹) * (-(2*k+1-(j:ℂ)) * F j))
    + (∑ j ∈ Finset.range (M+1), ((j.factorial:ℂ)⁻¹) * (((j:ℂ)*(2*k-(j:ℂ)+1)) * F (j-1)))
      = - ∑ j ∈ Finset.range (M+1), ((j.factorial:ℂ)⁻¹) * F j := by
  rw [Finset.sum_range_succ' (fun j => ((j.factorial:ℂ)⁻¹) * (((j:ℂ)*(2*k-(j:ℂ)+1)) * F (j-1))) M]
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
  have hreidx : ∀ i ∈ Finset.range M,
      (((i+1).factorial:ℂ)⁻¹) * ((((i+1:ℕ):ℂ))*(2*k-((i+1:ℕ):ℂ)+1) * F ((i+1)-1))
        = ((i.factorial:ℂ)⁻¹) * ((2*k-(i:ℂ)) * F i) := by
    intro i _
    rw [Nat.factorial_succ, Nat.cast_mul]
    have hfac : ((i.factorial:ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
    have hi1 : ((i:ℂ)+1) ≠ 0 := by
      have : ((i+1:ℕ):ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
      push_cast at this; exact this
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl hreidx]
  rw [Finset.sum_range_succ (fun j => ((j.factorial:ℂ)⁻¹) * (-(2*k+1-(j:ℂ)) * F j)) M]
  rw [hF, mul_zero, mul_zero, add_zero]
  rw [Finset.sum_range_succ (fun j => ((j.factorial:ℂ)⁻¹) * F j) M, hF, mul_zero, add_zero]
  rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem rhs_telescope (M : ℕ) (F : ℕ → ℂ) (hF : F (M+1) = 0) :
    (∑ j ∈ Finset.range (M+1), ((j.factorial:ℂ)⁻¹) * (((j:ℂ)+1) * F j - F (j+1)))
      = ∑ j ∈ Finset.range (M+1), ((j.factorial:ℂ)⁻¹) * F j := by
  set g : ℕ → ℂ := fun i => ((i.factorial:ℂ)⁻¹) * ((i:ℂ) * F i) with hg
  have hgsucc : ∀ j : ℕ, g (j+1) = (((j+1).factorial:ℂ)⁻¹) * (((j:ℂ)+1) * F (j+1)) := by
    intro j; rw [hg]; simp only; push_cast; ring
  have hterm : ∀ j : ℕ, ((j.factorial:ℂ)⁻¹) * (((j:ℂ)+1) * F j - F (j+1))
      = (g j + ((j.factorial:ℂ)⁻¹) * F j) - g (j+1) := by
    intro j
    rw [hgsucc j, hg]; simp only
    rw [Nat.factorial_succ, Nat.cast_mul]
    have hfac : ((j.factorial:ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    have hj1 : ((j:ℂ)+1) ≠ 0 := by
      have : ((j+1:ℕ):ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
      push_cast at this; exact this
    push_cast; field_simp
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hg0 : g 0 = 0 := by rw [hg]; simp
  have hshift : ∑ j ∈ Finset.range (M+1), g (j+1) = ∑ i ∈ Finset.range (M+2), g i - g 0 := by
    rw [Finset.sum_range_succ' g (M+1)]; ring
  rw [hshift, hg0, sub_zero]
  rw [Finset.sum_range_succ g (M+1)]
  have hgM : g (M+1) = 0 := by rw [hgsucc M, hF, mul_zero, mul_zero]
  rw [hgM, add_zero]
  ring

/-! ## `n = 1` Virasoro adjointness for `canBilin` (under `L₁𝒱₁ = 0`) -/

/-- **`canBilin(L₋₁a, b) = canBilin(a, L₁b)`** for homogeneous `a`, under quasi-primarity.
Both sides equal `−(−1)ᵏ ∑ⱼ (1/j!) vacCoord((L₁ʲa)₍2k−j₎b)` (the diagonal `F`-sum); the `𝔰𝔩₂`
tower + `L₋₁` shift telescopes the LHS, the `L₁`-bracket + obstruction-killer telescopes the RHS. -/
theorem canBilin_vir_adj_n1 (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    {k : ℤ} {a : V} (ha : a ∈ W.grading k) (b : V) :
    canBilin W hne (W.L (-1) a) b = canBilin W hne a (W.L 1 b) := by
  rcases lt_or_ge k 0 with hk | hk
  · have ha0 : a = 0 := eq_zero_of_mem_neg_grading W hk ha
    subst ha0
    simp only [map_zero, LinearMap.zero_apply]
  · set M : ℕ := k.toNat with hM
    have hMk : (M : ℤ) = k := Int.toNat_of_nonneg hk
    set F : ℕ → ℂ := fun i => vacCoord W hne (W.smul ((W.L 1 ^ i) a) (2*k - i) b) with hF
    have haL : W.L (-1) a ∈ W.grading (k + 1) := L_neg_one_raise W ha
    have hFvanish : F (M+1) = 0 := by
      rw [hF]; simp only
      have hz : ((W.L 1) ^ (M+1)) a = 0 := L_one_pow_eq_zero W ha (by rw [← hMk]; push_cast; omega)
      rw [hz, PreVertexAlgebra.smul_zero_left, map_zero]
    -- LHS = -vacCoord(adjMode (L_{-1}a) (k+1) (-1) b)
    rw [canBilin_eq_vacCoord_adjMode hne haL b, adjMode_def, map_smul, map_sum]
    simp only [map_smul]
    rw [show ((k+1).toNat + 1) = M + 2 by rw [hM]; omega]
    -- rewrite each LHS summand
    have hLrw : ∀ j ∈ Finset.range (M+2),
        ((j.factorial:ℂ)⁻¹) • vacCoord W hne (W.smul ((W.L 1 ^ j) (W.L (-1) a))
            (2 * (k+1) - -1 - 2 - (j:ℤ)) b)
          = ((j.factorial:ℂ)⁻¹) * (-(2*(k:ℂ)+1-(j:ℂ)) * F j)
            + ((j.factorial:ℂ)⁻¹) * (((j:ℂ)*(2*(k:ℂ)-(j:ℂ)+1)) * F (j-1)) := by
      intro j _
      rw [show (2 * (k+1) - -1 - 2 - (j:ℤ)) = 2*k+1-(j:ℤ) by ring]
      rw [lhs_summand hne ha b j]
      rw [smul_eq_mul, mul_add]
      simp only [hF]
      congr 2
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj; simp
      · rw [show (2*k-((j:ℤ)-1)) = 2*k-((j-1:ℕ):ℤ) by rw [Nat.cast_sub hj]; push_cast; ring]
    rw [Finset.sum_congr rfl hLrw, Finset.sum_add_distrib]
    rw [lhs_telescope (M+1) (k:ℂ) F hFvanish]
    -- RHS = -vacCoord(adjMode a k (-1) (L1 b))
    rw [canBilin_eq_vacCoord_adjMode hne ha (W.L 1 b), adjMode_def, map_smul, map_sum]
    simp only [map_smul]
    rw [show (k.toNat + 1) = M + 1 by rw [hM]]
    have hRrw : ∀ j ∈ Finset.range (M+1),
        ((j.factorial:ℂ)⁻¹) • vacCoord W hne (W.smul ((W.L 1 ^ j) a)
            (2 * k - -1 - 2 - (j:ℤ)) (W.L 1 b))
          = ((j.factorial:ℂ)⁻¹) * (((j:ℂ)+1) * F j - F (j+1)) := by
      intro j _
      rw [show (2 * k - -1 - 2 - (j:ℤ)) = 2*k-1-(j:ℤ) by ring]
      rw [rhs_summand hne hqp ha b j, smul_eq_mul]
      simp only [hF]
      rw [show (2*k-((j:ℤ)+1)) = 2*k-((j+1:ℕ):ℤ) by push_cast; ring]
    rw [Finset.sum_congr rfl hRrw, rhs_telescope M F hFvanish]
    -- both sides now: −((−1)^(k+1) • S₂) and −((−1)^k • S₁); align powers and ranges.
    rw [zpow_add₀ (by norm_num : (-1:ℂ) ≠ 0), zpow_one]
    -- peel the F(M+1)=0 top term to match ranges (M+2 vs M+1)
    rw [Finset.sum_range_succ (fun j => ((j.factorial:ℂ)⁻¹) * F j) (M+1), hFvanish, mul_zero, add_zero]
    rw [mul_comm ((-1:ℂ)^k) (-1), neg_one_mul, neg_smul, neg_neg, smul_neg]

/-! ## The matching-mode diagonal at the reachable weights -/

/-- **`CanDiagonal` at the unconditional weights `wt ≤ 0`.** For `u ∈ 𝒱_wt` with `wt ≤ 0`
(`u ∈ ℂ𝟙` or `u = 0`) the matching-mode FHL identity holds with no hypothesis — this is the
diagonal slice of the proven `canBilin_fullyInvariant_wt_le_zero`. -/
theorem canDiagonal_wt_le_zero (hne : W.vacuum ≠ 0) {wt : ℤ} (hwt : wt ≤ 0)
    (p q : ℤ) (u a b : V) (hu : u ∈ W.grading wt) :
    canBilin W hne (W.smul u (p + wt - q - 1) a) b
      = canRHS hne u a b wt (p + wt - q - 1) := by
  rw [canRHS]
  exact canBilin_fullyInvariant_wt_le_zero hne hwt u hu (p + wt - q - 1) a b

/-! ## `CanVirasoroAdj` at `n = −1` on all of `V` (the genuine Li lever, banked)

Lifting `canBilin_vir_adj_n1` (homogeneous) to arbitrary `a` by the internal direct-sum
decomposition gives the full `n = −1` Virasoro-adjointness of the canonical form — exactly the
identity `virSlice_vacuum` isolated as the necessary-and-sufficient content of invariance,
proved under the correct Gannon hypothesis `L₁𝒱₁ = 0`. -/

/-- **`canBilin(L₋₁a, b) = canBilin(a, L₁b)` for all `a`** (not just homogeneous), under `L₁𝒱₁=0`.
This is `CanVirasoroAdj` at `n = −1`. -/
theorem canBilin_Lneg1_adj (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) (a b : V) :
    canBilin W hne (W.L (-1) a) b = canBilin W hne a (W.L 1 b) := by
  have hatop : a ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading (motive := fun a =>
      canBilin W hne (W.L (-1) a) b = canBilin W hne a (W.L 1 b)) hatop ?_ ?_ ?_
  · intro k a ha; exact canBilin_vir_adj_n1 hne hqp ha b
  · show canBilin W hne (W.L (-1) 0) b = canBilin W hne 0 (W.L 1 b)
    simp only [map_zero, LinearMap.zero_apply]
  · intro a₁ a₂ h₁ h₂
    show canBilin W hne (W.L (-1) (a₁+a₂)) b = canBilin W hne (a₁+a₂) (W.L 1 b)
    rw [map_add, map_add, LinearMap.add_apply, h₁, h₂, map_add, LinearMap.add_apply]

end VOA
