/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnBimodule
import VOA.Core.InvariantFormDiagonal
import VOA.Core.InvariantFormPStep
import VOA.Core.FLM
import VOA.Foundations.Substitution

/-!
# The Dong–Jiang Prop 5.2 D-weight mechanism, formalized

The level-`0`-vs-level-`n` circle pole-shift is the single keystone of the Zhu bijection.  The
pure-circle tower-witness route walled (no coefficient collapse); the genuine route is Dong–Jiang
Prop 5.2's **D-weight** — the `L(-1)`-integration-by-parts that trades the pole-deficient residues for
off-diagonal residues (∈ `Onm`) plus `anmLgen` `L`-generators (∈ `OnmL`).  This file formalizes the two
engine-verified identities (`certificates/mathematica/poleshift_id.wl`, `certificates/mathematica/dweight_recursion.wl`).

## Contents (axiom-clean, pbw-free)

* **`cbz_absorb`** — the absorption binomial `i·cbz N i = N·cbz (N-1) (i-1)` (via `gBinom_mul_factorial`).
* **`resHom_Lneg1_ibp`** — the **D-weight IBP recursion**:
  `resHom W s p (L(-1)c) w = -(k+s+1)·resHom W s p c w + p·resHom W (s+1) (p+1) c w` (`c ∈ 𝒱_k`,
  `0 ≤ k+s`), from `smul_Lneg1_shift` + `resHom_homogeneous` + `cbz_absorb`.  This is the telescoping
  tool: it raises the pole `p → p+1` while spinning off the `L(-1)`-generator.
* **`resHom_poleShift`** — the **uniform pole-shift** (a):
  `resHom W 0 2 c w = ∑_{r≤n} asgn n r · resHom W r (n+2) c w` (`asgn n r = (-1)^{n-r} C(n,r)`), the
  finite-difference binomial `cbz_fd` (`Core/FLM`) applied per mode.  The `r=0` term is the level-`n`
  circle (∈ `Onm`); the `r≥1` terms are pole-deficient.

## The remaining residual (c) — the D-weight cancellation

`anmCirc W 0 0 c w = resHom W 0 2 c w ∈ Onm W n 0`: telescope the pole-deficient `r≥1` terms of
`resHom_poleShift` via `resHom_Lneg1_ibp` — the alternating `asgn` weights cancel the deficient parts,
leaving off-diagonal residues (∈ `Onm` by `resHom_offdiag_mem_Onm`) and `anmLgen` generators (∈ `OnmL`).
This is the exact remaining induction; `cbz_absorb`, `resHom_Lneg1_ibp`, `resHom_poleShift` (and `cbz_fd`)
are its verified ingredients.  (Note: per-term IBP keeps the pole-deficiency constant — the closure is a
cancellation on the *alternating* `asgn`-sum, DJ Prop 5.2's genuine content, not a term-by-term raise.)

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 5.2 (D-weight); Gannon §5.3.2;
`smul_Lneg1_shift` (`Core/InvariantFormDiagonal`), `cbz_fd` (`Core/FLM`), `resHom_offdiag_mem_Onm`.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The absorption binomial `i·cbz N i = N·cbz (N-1) (i-1)` -/

/-- **Absorption identity** `i·cbz N i = N·cbz (N-1) (i-1)` (all `i N : ℤ`), from
`∏_{j<k}(N-j) = N·∏_{j<k-1}(N-1-j)` (`gBinom_mul_factorial`). -/
theorem cbz_absorb (N i : ℤ) : (i : ℂ) * cbz N i = (N : ℂ) * cbz (N - 1) (i - 1) := by
  rcases lt_or_ge i 0 with hi | hi
  · rw [cbz_apply_neg N hi, cbz_apply_neg (N - 1) (by omega)]; ring
  · lift i to ℕ using hi with j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [cbz_apply_neg (N - 1) (by norm_num)]; simp
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
      have h1 : cbz N ((m + 1 : ℕ) : ℤ) = gBinom N (m + 1) := by
        rw [cbz_apply_nonneg N (by exact_mod_cast Nat.zero_le _)]; norm_num
      have h2 : cbz (N - 1) (((m + 1 : ℕ) : ℤ) - 1) = gBinom (N - 1) m := by
        rw [show ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) by push_cast; ring,
          cbz_apply_nonneg (N - 1) (by exact_mod_cast Nat.zero_le _)]; norm_num
      rw [h1, h2]
      have e1 := gBinom_mul_factorial N (m + 1)
      have e2 := gBinom_mul_factorial (N - 1) m
      have key : (∏ i ∈ Finset.range (m + 1), ((N : ℂ) - i))
          = (N : ℂ) * ∏ i ∈ Finset.range m, ((N : ℂ) - 1 - i) := by
        rw [Finset.prod_range_succ']; simp only [Nat.cast_zero, sub_zero]
        rw [mul_comm]; congr 1; apply Finset.prod_congr rfl; intro k _; push_cast; ring
      have hfac : (((m + 1).factorial : ℕ) : ℂ) = ((m + 1 : ℕ) : ℂ) * (m.factorial : ℂ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hne : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
      have lhs : ((m + 1 : ℕ) : ℂ) * (m.factorial : ℂ) * gBinom N (m + 1)
          = (N : ℂ) * ∏ i ∈ Finset.range m, ((N : ℂ) - 1 - i) := by rw [← hfac, e1, key]
      have rhs : (N : ℂ) * ((m.factorial : ℂ) * gBinom (N - 1) m)
          = (N : ℂ) * ∏ i ∈ Finset.range m, ((N : ℂ) - 1 - i) := by
        rw [e2]; congr 1; apply Finset.prod_congr rfl; intro k _; push_cast; ring
      refine mul_left_cancel₀ hne ?_
      calc (m.factorial : ℂ) * (((m + 1 : ℕ) : ℂ) * gBinom N (m + 1))
          = ((m + 1 : ℕ) : ℂ) * (m.factorial : ℂ) * gBinom N (m + 1) := by ring
        _ = (N : ℂ) * ∏ i ∈ Finset.range m, ((N : ℂ) - 1 - i) := lhs
        _ = (N : ℂ) * ((m.factorial : ℂ) * gBinom (N - 1) m) := rhs.symm
        _ = (m.factorial : ℂ) * ((N : ℂ) * gBinom (N - 1) m) := by ring

/-! ## The D-weight IBP recursion (b) -/

/-- **The D-weight `L(-1)` integration-by-parts recursion** (Dong–Jiang Prop 5.2).  For `c ∈ 𝒱_k` and
`0 ≤ k+s`,
`resHom W s p (L(-1)c) w = -(k+s+1)·resHom W s p c w + p·resHom W (s+1) (p+1) c w`.
Proof: expand all three via `resHom_homogeneous` (`L(-1)c ∈ 𝒱_{k+1}` by `L_neg_one_raise`), rewrite the
`L(-1)`-modes by `smul_Lneg1_shift` (`(L(-1)v)_{(m)} = -m·v_{(m-1)}`), and match coefficients by
`cbz_absorb` (`i·cbz N i = N·cbz (N-1) (i-1)`) after the index shift. -/
theorem resHom_Lneg1_ibp (W : VertexOperatorAlgebra 𝒱) {k : ℤ} {c : 𝒱}
    (hc : c ∈ W.grading k) (w : 𝒱) (s p : ℤ) (hks : 0 ≤ k + s) :
    resHom W s p (W.L (-1) c) w
      = (-(k + s + 1) : ℂ) • resHom W s p c w + (p : ℂ) • resHom W (s + 1) (p + 1) c w := by
  have hLc : W.L (-1) c ∈ W.grading (k + 1) := W.L_neg_one_raise hc
  rw [resHom_homogeneous W s p hLc, resHom_homogeneous W s p hc,
    resHom_homogeneous W (s + 1) (p + 1) hc, Finset.smul_sum, Finset.smul_sum,
    show (k + 1 + s : ℤ) = k + s + 1 from by ring,
    show (k + (s + 1) : ℤ) = k + s + 1 from by ring,
    ← sub_eq_iff_eq_add, ← Finset.sum_sub_distrib]
  have hcoef : ∀ i ∈ Finset.range ((k + s + 1).toNat + 1),
      cbz (k + s + 1) i • W.smul (W.L (-1) c) ((i : ℤ) - p) w
        - (p : ℂ) • (cbz (k + s + 1) i • W.smul c ((i : ℤ) - (p + 1)) w)
      = (-(k + s + 1 : ℂ)) • (cbz (k + s) ((i : ℤ) - 1) • W.smul c ((i : ℤ) - p - 1) w) := by
    intro i _
    rw [W.smul_Lneg1_shift c w ((i : ℤ) - p), smul_smul, smul_smul,
      show ((i : ℤ) - p) - 1 = (i : ℤ) - p - 1 from rfl,
      show (i : ℤ) - (p + 1) = (i : ℤ) - p - 1 from by ring, smul_smul, ← sub_smul]
    congr 1
    have hab := cbz_absorb (k + s + 1) (i : ℤ)
    push_cast at hab ⊢
    ring_nf; ring_nf at hab; linear_combination (-1 : ℂ) * hab
  rw [Finset.sum_congr rfl hcoef, ← Finset.smul_sum, ← Finset.smul_sum]
  congr 1
  rw [show (k + s + 1).toNat + 1 = ((k + s).toNat + 1) + 1 from by omega, Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_sub]
  rw [cbz_apply_neg (k + s) (by norm_num), zero_smul, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  congr 2 <;> push_cast <;> ring

/-! ## The uniform pole-shift (a) -/

/-- **The uniform pole-shift** (Dong–Jiang Prop 5.2, identity (a)).  For `c ∈ 𝒱_M`,
`resHom W 0 2 c w = ∑_{r≤n} asgn n r · resHom W r (n+2) c w` (`asgn n r = (-1)^{n-r} C(n,r)`), i.e.
`anmCirc W 0 0 c w` (the level-`0` circle, pole `2`) written as a uniform alternating combination of the
shifted pole-`(n+2)` residues `resHom W r (n+2) c w`.  This is the finite-difference binomial `cbz_fd`
(`Core/FLM`) applied per mode: matching the coefficient of `c₍i-2₎w` (RHS mode `c₍j-(n+2)₎w`, `j = i+n`)
gives `∑_r asgn n r · cbz (M+r) (i+n) = cbz M i`.  The `r=0` term is the level-`n` circle
`resHom W 0 (n+2) c w = anmCirc W n 0 c w` (∈ `Onm`); the `r≥1` terms are pole-deficient. -/
theorem resHom_poleShift (W : VertexOperatorAlgebra 𝒱) {M : ℕ} {c : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (w : 𝒱) (n : ℕ) :
    resHom W 0 2 c w
      = ∑ r ∈ Finset.range (n + 1), (asgn n r : ℂ) • resHom W (r : ℤ) (n + 2) c w := by
  have hExt : ∀ r ∈ Finset.range (n + 1),
      (asgn n r : ℂ) • resHom W (r : ℤ) (n + 2) c w
        = ∑ j ∈ Finset.range (M + n + 1),
            ((asgn n r : ℂ) * cbz ((M : ℤ) + r) j) • W.smul c ((j : ℤ) - (n + 2)) w := by
    intro r hr
    rw [Finset.mem_range] at hr
    rw [resHom_homogeneous W (r : ℤ) (n + 2) hc, Finset.smul_sum,
      show ((M : ℤ) + (r : ℤ)).toNat + 1 = M + r + 1 from by omega]
    have hsub : Finset.range (M + r + 1) ⊆ Finset.range (M + n + 1) := by
      intro x hx; rw [Finset.mem_range] at hx ⊢; omega
    have hf : ∀ j ∈ Finset.range (M + n + 1), j ∉ Finset.range (M + r + 1) →
        (asgn n r : ℂ) • (cbz ((M : ℤ) + r) j • W.smul c ((j : ℤ) - (n + 2)) w) = 0 := by
      intro j hjt hjs
      simp only [Finset.mem_range, not_lt] at hjt hjs
      rw [cbz_lt (by positivity) (by omega), zero_smul, smul_zero]
    rw [Finset.sum_subset hsub hf]
    apply Finset.sum_congr rfl; intro j _; rw [smul_smul]
  rw [Finset.sum_congr rfl hExt, Finset.sum_comm]
  have hInner : ∀ j ∈ Finset.range (M + n + 1),
      (∑ r ∈ Finset.range (n + 1),
        ((asgn n r : ℂ) * cbz ((M : ℤ) + r) j) • W.smul c ((j : ℤ) - (n + 2)) w)
        = (cbz (M : ℤ) ((j : ℤ) - n)) • W.smul c ((j : ℤ) - (n + 2)) w := by
    intro j _
    rw [← Finset.sum_smul]; congr 1
    rw [← cbz_fd n (M : ℤ) (j : ℤ)]
    apply Finset.sum_congr rfl; intro r _; rw [zsmul_eq_mul]
  rw [Finset.sum_congr rfl hInner, show M + n + 1 = n + (M + 1) from by omega, Finset.sum_range_add]
  have hzero : (∑ j ∈ Finset.range n, cbz (M : ℤ) ((j : ℤ) - n) • W.smul c ((j : ℤ) - (n + 2)) w) = 0 := by
    apply Finset.sum_eq_zero; intro j hj; rw [Finset.mem_range] at hj
    rw [cbz_apply_neg (M : ℤ) (by omega), zero_smul]
  rw [hzero, zero_add, resHom_homogeneous W 0 2 hc,
    show ((M : ℤ) + 0).toNat + 1 = M + 1 from by omega]
  apply Finset.sum_congr rfl
  intro i _
  congr 2 <;> push_cast <;> ring

end VOA

-- Integrity gate.
