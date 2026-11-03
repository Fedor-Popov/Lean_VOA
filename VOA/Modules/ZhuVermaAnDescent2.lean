/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnDescent
import VOA.Modules.ZhuRightIdeal

/-!
# The depth-`n` generalized Vandermonde identity and the descent memberships

This file extends `Modules.ZhuVermaAnDescent` (the keystone `Pres_mem_On` and the
descended actions `An.lAct`/`An.rAct`, parametric in the bundled hypotheses
`LeftDescends`/`RightDescends`) toward discharging those hypotheses.

## The depth-`n` generalized Vandermonde identity (`gen_vandermonde`)

The principal new combinatorial input is the depth-`n` generalization of the Zhu right-ideal
residue identity `ZhuRes.zhu_right_binom` (Zhu Thm 2.1.1), carrying the extra `(1+z)^{n}/z^{2n}`
weighting of the Frenkel–Zhu `n`-th products.  For each fixed FZ summation index `j`, the inner
`p`-sum collapses:

  `∑_p C(K+n,p)·C(M+n, m+3+n+j+s−p)·C(p−(n+j+1), s)`
    `= ∑_{t=0}^{s} (−1)^t · C(n+j+t, t) · C(K+n, s−t) · C(K+M+2n−(s−t), m+3+n+j+t)`.

At `n = 0`, `j = 0` this is exactly `ZhuRes.zhu_right_binom` (`C(t,t) = 1`, top
`K+M−(s−t) = K+M−s+t`).  It is **not** a special case of `zhu_right_binom`: it is proved here from
scratch by the same Vandermonde route, but with the new negative-top peeling lemma `cbz_neg_succ`
(`C(−(r+1), t) = (−1)^t·C(r+t, t)`) replacing `ZhuRes.cbz_neg_one`.

## Status
* **`cbz_neg_succ`** (the negative-top alternating-row lemma) and **`gen_stepA`** (the depth-`n`
generalized peeling) proved, axiom-clean.
* **`gen_vandermonde`** (the depth-`n` Vandermonde identity) proved, axiom-clean.

The four circle-generator memberships (`LeftDescends`/`RightDescends`) collapse (via the keystone
`Pres_mem_On` + this identity, summed over the FZ index `j`) onto `PresOn`-towers; that residue
bookkeeping (the `S_mem_O`-analog at depth `n`) is documented as a precise remaining target at the
file end.

## References
* Gannon §5.3.2, Thm 5.3.4; Zhu Thm 2.1.1; Frenkel–Zhu Lemma 2.1.2; Dong–Li–Mason.
-/

open scoped BigOperators
open Finset

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators
open Classical

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace ZhuRes

/-! ## The negative-top alternating-row lemma `C(−(r+1), t) = (−1)^t·C(r+t, t)`. -/

/-- **`C(−(r+1), t) = (−1)^t · C(r+t, t)`** for `r t : ℕ` (the negative-top binomial as an
alternating shift of the positive one).  At `r = 0` this is `ZhuRes.cbz_neg_one`.  Proved off the
closed form `gBinom_negsucc` (`gBinom(−r−1, t) = (−1)^t (r+t)!/(r!·t!)`) and
`cbz_natCast_eq_choose`. -/
theorem cbz_neg_succ (r t : ℕ) :
    cbz (-((r : ℤ) + 1)) (t : ℤ) = (-1 : ℂ) ^ t * cbz ((r : ℤ) + t) (t : ℤ) := by
  -- LHS: `cbz (-(r+1)) t = gBinom (-(r+1)) t = (-1)^t (r+t)!/(r! t!)`.
  rw [show (-((r : ℤ) + 1)) = (-(r : ℤ) - 1) from by ring,
    cbz_apply_nonneg _ (by positivity), Int.toNat_natCast, gBinom_negsucc r t]
  -- RHS: `cbz (r+t) t = C(r+t, t) = (r+t)!/(r! t!)`.
  rw [show ((r : ℤ) + (t : ℤ)) = ((r + t : ℕ) : ℤ) from by push_cast; ring,
    cbz_natCast_eq_choose (by omega : t ≤ r + t)]
  -- `(r+t).choose t = (r+t)!/(r! t!)` ⟹ both sides equal.
  have hchoose : ((r + t).choose t : ℂ) * ((r.factorial : ℂ) * (t.factorial : ℂ))
      = ((r + t).factorial : ℂ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (by omega : t ≤ r + t)
    rw [show r + t - t = r from by omega] at h
    have := congrArg (Nat.cast (R := ℂ)) h
    push_cast at this ⊢
    linear_combination this
  have hr : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have ht : (t.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  -- `cbz (r+t) t = (r+t).choose t = (r+t)!/(r! t!)`; clear the denominator off `hchoose`.
  rw [div_eq_iff (mul_ne_zero hr ht)]
  linear_combination (-(-1 : ℂ) ^ t) * hchoose

/-! ## (A′) The depth-`n` generalized peeling
`C(p−(n+j+1), s) = ∑_{t≤s} (−1)^t·C(n+j+t, t)·C(p, s−t)` (Vandermonde with the negative top
`−(n+j+1)`, off `cbz_neg_succ`). The `n = j = 0` case is `ZhuRes.stepA`. -/
theorem gen_stepA (n j : ℕ) (p : ℤ) (s : ℕ) :
    cbz (p - ((n : ℤ) + j + 1)) (s : ℤ)
      = ∑ t ∈ Finset.range (s + 1),
          (-1 : ℂ) ^ t * cbz ((n : ℤ) + j + t) (t : ℤ) * cbz p ((s : ℤ) - (t : ℤ)) := by
  have hv := vandermonde_range (-((n : ℤ) + (j : ℤ) + 1)) p (s : ℤ) (N := s + 1)
    (by push_cast; omega)
  rw [show (-((n : ℤ) + (j : ℤ) + 1) + p) = p - ((n : ℤ) + j + 1) from by ring] at hv
  rw [← hv]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  have hcnj : cbz (-((n : ℤ) + (j : ℤ) + 1)) (t : ℤ)
      = (-1 : ℂ) ^ t * cbz ((n : ℤ) + j + t) (t : ℤ) := by
    have h := cbz_neg_succ (n + j) t
    rw [show (-((((n + j : ℕ)) : ℤ) + 1)) = -((n : ℤ) + (j : ℤ) + 1) from by push_cast; ring,
      show (((n + j : ℕ)) : ℤ) + (t : ℤ) = (n : ℤ) + j + t from by push_cast; ring] at h
    exact h
  rw [hcnj, mul_assoc]

/-! ## The depth-`n` generalized Vandermonde identity (`gen_vandermonde`).

For each fixed Frenkel–Zhu index `j`, the inner `p`-sum of the commutator family of
`leftProd W n a (circ W n c d)` collapses:

  `∑_p C(K+n,p)·C(M+n, m−p+3n+3+j+s)·C(p−(n+j+1), s)`
    `= ∑_{t=0}^{s} (−1)^t · C(n+j+t, t) · C(K+n, s−t) · C(K+M+2n−(s−t), m+3n+3+j+t)`.

Same Vandermonde route as `ZhuRes.zhu_right_binom` (`gen_stepA` + `stepB` + `stepC`), generalized
to depth `n`; the `n = j = 0` case is exactly `zhu_right_binom` (`C(t,t)=1`,
`C(K+M−(s−t), m+3+t)`).  The RHS top `C(K+M+2n−(s−t), …)` with `Ws := K+M−s−1` reads
`C(Ws+2n+1+t, m+3n+3+j+t)`, the mode-coefficient feeding the depth-`n` keystone `Pres_mem_On`. -/
theorem gen_vandermonde (K M n j s : ℕ) (m : ℤ) :
    ∑ p ∈ Finset.range (K + n + 1),
        cbz ((K : ℤ) + n) (p : ℤ)
          * cbz ((M : ℤ) + n) (m - (p : ℤ) + 3 * n + 3 + j + s)
          * cbz ((p : ℤ) - ((n : ℤ) + j + 1)) (s : ℤ)
      = ∑ t ∈ Finset.range (s + 1),
        (-1 : ℂ) ^ t * cbz ((n : ℤ) + j + t) (t : ℤ) * cbz ((K : ℤ) + n) ((s : ℤ) - (t : ℤ))
          * cbz ((K : ℤ) + M + 2 * n - ((s : ℤ) - (t : ℤ))) (m + 3 * n + 3 + j + t) := by
  -- Expand `C(p-(n+j+1), s)` by `gen_stepA`, then swap the order of summation.
  rw [show (∑ p ∈ Finset.range (K + n + 1),
            cbz ((K : ℤ) + n) (p : ℤ)
              * cbz ((M : ℤ) + n) (m - (p : ℤ) + 3 * n + 3 + j + s)
              * cbz ((p : ℤ) - ((n : ℤ) + j + 1)) (s : ℤ))
        = ∑ p ∈ Finset.range (K + n + 1), ∑ t ∈ Finset.range (s + 1),
            ((-1 : ℂ) ^ t * cbz ((n : ℤ) + j + t) (t : ℤ))
              * (cbz ((K : ℤ) + n) (p : ℤ) * cbz (p : ℤ) ((s : ℤ) - (t : ℤ)))
              * cbz ((M : ℤ) + n) (m - (p : ℤ) + 3 * n + 3 + j + s) from
      Finset.sum_congr rfl fun p _ => by
        rw [gen_stepA n j (p : ℤ) s, Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun t ht => ?_
  -- Factor out the `t`-only scalars and the `cbz (K+n) (s-t)` via the trinomial revision `stepB`.
  rw [show (∑ p ∈ Finset.range (K + n + 1),
            ((-1 : ℂ) ^ t * cbz ((n : ℤ) + j + t) (t : ℤ))
              * (cbz ((K : ℤ) + n) (p : ℤ) * cbz (p : ℤ) ((s : ℤ) - (t : ℤ)))
              * cbz ((M : ℤ) + n) (m - (p : ℤ) + 3 * n + 3 + j + s))
        = ((-1 : ℂ) ^ t * cbz ((n : ℤ) + j + t) (t : ℤ) * cbz ((K : ℤ) + n) ((s : ℤ) - (t : ℤ)))
            * ∑ p ∈ Finset.range (K + n + 1),
                cbz (((K + n : ℕ) : ℤ) - ((s : ℤ) - (t : ℤ))) ((p : ℤ) - ((s : ℤ) - (t : ℤ)))
                  * cbz ((M : ℤ) + n) ((m + 3 * n + 3 + j + s) - (p : ℤ)) from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [show ((K : ℤ) + n) = ((K + n : ℕ) : ℤ) from by push_cast; ring,
        stepB (K + n) (p : ℤ) ((s : ℤ) - (t : ℤ))]
      rw [show (m - (p : ℤ) + 3 * n + 3 + j + s) = (m + 3 * n + 3 + j + s) - (p : ℤ) from by ring]
      ring]
  -- Collapse the inner `p`-sum by the shifted Vandermonde `stepC` (when `s - t ≤ K+n`).
  rcases le_or_gt ((s : ℤ) - (t : ℤ)) ((K + n : ℕ) : ℤ) with hstK | hstK
  · rw [stepC (((K + n : ℕ) : ℤ) - ((s : ℤ) - (t : ℤ))) ((M : ℤ) + n) (m + 3 * n + 3 + j + s)
          ((s : ℤ) - (t : ℤ)) (N := K + n + 1) (by omega)
          (by have := Finset.mem_range.mp ht; omega)
          (by push_cast at hstK ⊢; omega)]
    rw [show (((K + n : ℕ) : ℤ) - ((s : ℤ) - (t : ℤ))) + ((M : ℤ) + n)
          = (K : ℤ) + M + 2 * n - ((s : ℤ) - (t : ℤ)) from by push_cast; ring,
      show (m + 3 * n + 3 + j + s) - ((s : ℤ) - (t : ℤ)) = m + 3 * n + 3 + j + t from by ring]
  · -- `s - t > K + n`: then `cbz (K+n) (s-t) = 0`, both sides vanish.
    rw [show ((K : ℤ) + n) = ((K + n : ℕ) : ℤ) from by push_cast; ring,
      cbz_lt (by positivity) hstK]
    ring

end ZhuRes

/-! ## The `c`-first family of the right-slot `leftProd` membership lands in `O_n(𝒱)`.

For homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, expanding `leftProd W n a (circ W n c d)` via
`leftProd_homogeneous` + `circ_homogeneous` and splitting each `a₍α₎(c₍β₎e)` by `ZhuHR.mode_split`
into the `c`-first term `c₍β₎(a₍α₎e)` plus the commutator, the `c`-first family is a finite
ℂ-combination of circle products `circ W n c (a₍p−n−j−1₎d)`, hence in `O_n(𝒱)`.  (The commutator
family is the depth-`n` analog of `ZhuHR.commutator_family_mem_O`, collapsing through
`gen_vandermonde` + the keystone `Pres_mem_On`; see the remaining-targets note at the file end.) -/
theorem leftProd_circ_first_family_mem_On (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M : ℕ}
    {c : 𝒱} (hc : c ∈ W.grading (M : ℤ)) (Krange : ℕ) (a d : 𝒱) :
    (∑ j ∈ Finset.range (n + 1),
        ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) •
          ∑ p ∈ Finset.range (Krange + 1),
            cbz (M + (n : ℤ)) p •
              ∑ i ∈ Finset.range ((M + (n : ℤ)).toNat + 1),
                cbz (M + (n : ℤ)) i •
                  W.smul c ((i : ℤ) - 2 * (n : ℤ) - 2)
                    (W.smul a ((p : ℤ) - (n : ℤ) - (j : ℤ) - 1) d))
      ∈ On W n := by
  -- Each inner `i`-sum is `circ W n c (a₍p−n−j−1₎d)` (by `circ_homogeneous`, `c` homogeneous),
  -- hence in `O_n(𝒱)`; the membership is then closed by `Submodule.{sum,smul}_mem`.
  apply Submodule.sum_mem; intro j _
  apply Submodule.smul_mem
  apply Submodule.sum_mem; intro p _
  apply Submodule.smul_mem
  rw [← circ_homogeneous W n hc (W.smul a ((p : ℤ) - (n : ℤ) - (j : ℤ) - 1) d)]
  exact circ_mem_On W n c _

/-!
## The four descent memberships: PRECISE remaining targets (NOT `sorry`)

With the depth-`n` generalized Vandermonde `gen_vandermonde` proved, the reduction of the four
circle-generator memberships (the fields of `LeftDescends`/`RightDescends`) is fully pinned
down.  The status of each piece:

### Right-slot, `leftProd W n a (circ W n c d) ∈ On W n` (membership 1)
For homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, expand by `leftProd_homogeneous` + `circ_homogeneous` and
split each `a₍α₎(c₍β₎d)` via `ZhuHR.mode_split` into
* the **`c`-first family** — `∑_j (-1)^j C(j+n,n) ∑_p C(K+n,p)·circ W n c (a₍p−n−j−1₎d)`, which is
  in `O_n(𝒱)` by **`leftProd_circ_first_family_mem_On` (proved above)**;
* the **commutator family** `∑_{p,i,j} (…)·⁅a₍α₎, c₍β₎⁆d`, expanded by
  `ZhuHR.mode_commutator_uniform` into `∑_s (…)·(a₍ₛ₎c)₍α+β−s₎d` with `w_s := a₍ₛ₎c ∈ 𝒱_{K+M−s−1}`.

The commutator family's coefficient of `(w_s)₍μ₎d`, after the inner `i`-reindex to the mode value
`μ` (`ZhuHR.inner_reindex`), is `∑_t (-1)^t C(K+n, s−t)·J(t,μ)` with the inner FZ `j`-sum
  `J(t,μ) = ∑_{j=0}^{n} (-1)^j C(j+n,n)·C(n+j+t, t)·C(Ws+2n+1+t, μ+3n+3+j+t)`,  `Ws := K+M−s−1`,
**exactly via `gen_vandermonde`** (verified end-to-end against the raw double sum).

### The single remaining combinatorial target `gen_jsum`
`J(t,μ)` decomposes (numerically `Ws`- and `M`-independently) into the depth-`n` keystone towers:
  `J(t,μ) = ∑_{e=0}^{n} ν(n,t,e)·C(Ws+n+(n+1+t+e), μ+2n+2+(n+1+t+e))`,
i.e. `∑ᶠ_μ J(t,μ)·(w_s)₍μ₎d = ∑_{e=0}^{n} ν(n,t,e)·PresOn W Ws n (n+1+t+e) w_s d ∈ O_n(𝒱)` by the
keystone `Pres_mem_On`.  At `n = 0` this is `J(t,μ) = C(Ws+1+t, μ+3+t)` (a single tower, `ν=1`),
recovering `ZhuHR.S_mem_O`.  The coefficients `ν(n,t,e)` are a `₃F₂`-type family with no elementary
product form (`ν(n,0,0)=C(2n+1,n)`, `ν(n,0,n)=(-1)^n C(2n,n)`); discharging `gen_jsum` is the one
genuine combinatorial step still open.

### Membership 2 (`rightProd W n (circ W n c d) a ∈ On W n`)
Here the circle product sits in the *decomposed* (left) slot, so the reduction runs through the
bilinear `rightProd_homogeneous` on the homogeneous pieces of `circ W n c d` with the right-product
coefficients `C(L+j, i)` (binomial shift `s = j`), again collapsing onto `Pres_mem_On` towers via
the `s = j` instance of `gen_vandermonde`/`gen_jsum`.

### Left-slot generators (memberships 3, 4: `O(𝒱) *ₙ 𝒱 ⊆ O_n`, `𝒱 *ₙ O(𝒱) ⊆ O_n`)
For an `O(𝒱)`-generator `g = (L₋₁u + L₀u)*v`, `leftProd W n g b` (resp. `rightProd W n x g`) reduces
by the same residue route; the FZ alternating `j`-sum together with `gen_vandermonde` collapses the
generator residue onto `Pres_mem_On` towers, modulo the same `gen_jsum` coefficient identity.

Discharging `gen_jsum` packages the four into `LeftDescends`/`RightDescends`, yielding the
unconditional descended bimodule actions `An.lAct W n (leftDescends_holds W n)` /
`An.rAct W n (rightDescends_holds W n)` of `Modules.ZhuVermaAnDescent`, with the `n = 0` anchors
`An.lAct_zero_mk`/`An.rAct_zero_mk` tying the bottom rung to the Zhu product.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.ZhuRes.cbz_neg_succ
  #print axioms VOA.ZhuRes.gen_stepA
  #print axioms VOA.ZhuRes.gen_vandermonde
  #print axioms VOA.leftProd_circ_first_family_mem_On
-/
