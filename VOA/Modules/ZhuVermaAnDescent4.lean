/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnDescent3

/-!
# The four descent memberships and the unconditional `A_n(𝒱)` bimodule

This file completes the Frenkel–Zhu bimodule descent.  It is the depth-`n` lift of the `n = 0`
two-sided-ideal bookkeeping of `Modules.ZhuRightIdeal` (`mode_split`, `mode_commutator_uniform`,
`inner_reindex`, `S_mem_O`, `commutator_family_mem_O`, `right_ideal_core`), now with the extra
`(1+z)^{n}/z^{2n}` weighting.  All combinatorial inputs are already proved and proved:

* the depth-`n` generalized Vandermonde `ZhuRes.gen_vandermonde`
  (`Modules.ZhuVermaAnDescent3`);
* the keystone coefficient identity `ZhuRes.gen_jsum`
  (`∑ⱼ (-1)ʲ C(j+n,n) C(n+j+t,t) C(Ws+2n+1+t, μ+3n+3+j+t)
       = ∑ₑ ν(n,t,e) C(Ws+n+(n+1+t+e), μ+2n+2+(n+1+t+e))`);
* the keystone higher-pole residue membership `Pres_mem_On`
  (`∑ᵢ C(M+n+d,i) a₍ᵢ₋₂ₙ₋₂₋d₎ b ∈ Oₙ`).

## What is proved (the commutator-family reduction, end-to-end)

* `PresOn_eq_finsum` — `PresOn` in the mode-value finsum form (depth-`n` lift of
   `ZhuHR.Pres_eq_finsum`); `mode_split_gen`; `inner_reindexN`.
* **`coeffSn_eq_coeffPn`** — the depth-`n` coefficient collapse (combining `gen_vandermonde` per FZ
   index `j` with `gen_jsum`); the `n = 0` instance is `ZhuHR.coeffS_eq_coeffP`.
* **`Sn_eq_finsum`** / **`PresOnCombo_eq_finsum`** — the two finsum-collapse halves
   (lifts of `ZhuHR.S_eq_finsum` / `PresCombo_eq_finsum`).
* **`Sn_mem_On`** — the per-commutator-index term `S_s ∈ Oₙ` (lift of `ZhuHR.S_mem_O`).
* **`leftProd_circ_commutator_family_mem_On`** — the commutator family of
   `leftProd W n a (circ W n c d) ∈ Oₙ` (lift of `ZhuHR.commutator_family_mem_O`).
* **`leftProd_circ_mem_On_homog`** / **`leftProd_circ_mem_On`** — **MEMBERSHIP 1**
   (`leftProd W n a (circ W n c d) ∈ Oₙ`, homogeneous then arbitrary `a c d`), via the `c`-first
   family (`leftProd_circ_first_family_mem_On`) + the commutator family.  This is the unique
   *commutator-style* circle-generator membership (the homogeneous factor `a` is in the outer
   applied-mode position; the circle product is in the inner slot).
* **`leftProd_On_mem_On`** — the `LeftDescends.on_mem` field `𝒱 *ₙ Oₙ ⊆ Oₙ`, unconditionally
   (via `leftProd_On_of_gen` + membership 1).  **One bimodule descent direction is discharged.**

## Precise remaining targets (NOT `sorry`, NOT axiomatized — see the note at the file end)

The other three circle-generator memberships are *associator/iterate-style*, not commutator-style:
each puts the circle product (or an `O(𝒱)`-generator) in the **first** `rightProd`/`leftProd` slot
(or an `O(𝒱)`-generator `g` in a slot), so after the bilinear `*_homogeneous` collapse the residue
acts on an *iterated* mode `(c₍β₎d)₍γ₎a` / `(u₍β₎v)₍γ₎b` rather than a single commutator
`⁅a₍α₎,c₍β₎⁆`.  Discharging them is the depth-`n` lift of the *associator* machinery
(`ZhuUCore.u_core`/`ZhuVCore.v_core`/`ZhuAssociator.associator_core`), a separate development; the
provided combinatorial inputs (`gen_jsum`/`gen_vandermonde`) are exactly the commutator-family
identities and feed membership 1.  See the file-end note.

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

/-- `circ W n 0 d = 0` (from additivity in the left factor). -/
@[simp] theorem circ_zero_left (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (d : 𝒱) :
    circ W n 0 d = 0 := by
  have h := circ_smul_left W n 0 0 d
  rwa [zero_smul, zero_smul] at h

/-! ## A general mode-split (arbitrary modes), the depth-`n` analog of `ZhuHR.mode_split`. -/

/-- `u₍α₎(a₍β₎b) = a₍β₎(u₍α₎b) + ⁅u₍α₎, a₍β₎⁆ b` for arbitrary integer modes `α β`. -/
theorem mode_split_gen (W : VertexOperatorAlgebra 𝒱) (u a b : 𝒱) (α β : ℤ) :
    W.smul u α (W.smul a β b)
      = W.smul a β (W.smul u α b)
        + ⁅mode (W.Y u) α, mode (W.Y a) β⁆ b := by
  rw [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply]
  simp only [PreVertexAlgebra.smul_def, mode_apply]
  abel

/-! ## `PresOn` in the mode-value finsum form (depth-`n` lift of `ZhuHR.Pres_eq_finsum`). -/

/-- `PresOn W M n d w b` in the mode-value finsum form (`m = r - 2n - 2 - d`):
`∑ᶠ m, C(M+n+d, m+2n+2+d) • w₍ₘ₎b`. -/
theorem PresOn_eq_finsum (W : VertexOperatorAlgebra 𝒱) (M n d : ℕ) (w b : 𝒱) :
    PresOn W M n d w b
      = ∑ᶠ m : ℤ, cbz ((M : ℤ) + n + d) (m + 2 * n + 2 + d) • W.smul w m b := by
  unfold PresOn
  rw [show (∑ r ∈ Finset.range (M + n + d + 1),
            cbz ((M : ℤ) + n + d) (r : ℤ)
              • W.smul w ((r : ℤ) - 2 * (n : ℤ) - 2 - d) b)
        = ∑ r ∈ Finset.range (M + n + d + 1),
            cbz ((M : ℤ) + n + d) (r : ℤ)
              • W.smul w ((r : ℤ) + (-(2 * (n : ℤ)) - 2 - d)) b from
      Finset.sum_congr rfl fun r _ => by
        rw [show (r : ℤ) - 2 * (n : ℤ) - 2 - d = (r : ℤ) + (-(2 * (n : ℤ)) - 2 - d) from by ring]]
  rw [ZhuHR.rangeSmul_eq_finsumZ (fun q : ℤ => cbz ((M : ℤ) + n + d) q)
      (fun q => W.smul w q b) (-(2 * (n : ℤ)) - 2 - d)
      (fun q hq => cbz_apply_neg _ hq)
      (fun q hq => cbz_lt (by positivity) (by push_cast at hq ⊢; omega))]
  rw [← finsum_comp_equiv (Equiv.addRight (-(2 * (n : ℤ)) - 2 - (d : ℤ)))
      (f := fun m : ℤ => cbz ((M : ℤ) + n + d) (m + 2 * n + 2 + d) • W.smul w m b)]
  refine finsum_congr fun q => ?_
  simp only [Equiv.coe_addRight]
  rw [show (q + (-(2 * (n : ℤ)) - 2 - (d : ℤ))) + 2 * n + 2 + d = q from by ring]

/-! ## The depth-`n` inner reindex (mode-value collapse, lift of `ZhuHR.inner_reindex`).

For homogeneous `c ∈ 𝒱_M`, the inner `i`-sum `∑_i C(M+n,i) • w₍p+i-3n-3-j-s₎b` over `range(M+n+1)`
collapses to the mode-value finsum `∑ᶠ m, C(M+n, m+3n+3+j+s-p) • w₍ₘ₎b`. -/
theorem inner_reindexN (W : VertexOperatorAlgebra 𝒱) (M n : ℕ) (w b : 𝒱) (j s p : ℤ) :
    (∑ i ∈ Finset.range (M + n + 1),
        cbz ((M : ℤ) + n) (i : ℤ) • W.smul w (p + (i : ℤ) - 3 * n - 3 - j - s) b)
      = ∑ᶠ m : ℤ, cbz ((M : ℤ) + n) (m + 3 * n + 3 + j + s - p) • W.smul w m b := by
  rw [show (∑ i ∈ Finset.range (M + n + 1),
            cbz ((M : ℤ) + n) (i : ℤ) • W.smul w (p + (i : ℤ) - 3 * n - 3 - j - s) b)
        = ∑ i ∈ Finset.range (M + n + 1),
            cbz ((M : ℤ) + n) (i : ℤ) • W.smul w ((i : ℤ) + (p - 3 * n - 3 - j - s)) b from
      Finset.sum_congr rfl fun i _ => by
        rw [show p + (i : ℤ) - 3 * n - 3 - j - s = (i : ℤ) + (p - 3 * n - 3 - j - s) from by ring]]
  rw [ZhuHR.rangeSmul_eq_finsumZ (fun q : ℤ => cbz ((M : ℤ) + n) q) (fun q => W.smul w q b)
      (p - 3 * n - 3 - j - s)
      (fun q hq => cbz_apply_neg _ hq)
      (fun q hq => cbz_lt (by positivity) (by push_cast at hq ⊢; omega))]
  rw [← finsum_comp_equiv (Equiv.addRight (p - 3 * (n : ℤ) - 3 - j - s))
      (f := fun m : ℤ => cbz ((M : ℤ) + n) (m + 3 * n + 3 + j + s - p) • W.smul w m b)]
  refine finsum_congr fun q => ?_
  simp only [Equiv.coe_addRight]
  rw [show (q + (p - 3 * (n : ℤ) - 3 - j - s)) + 3 * n + 3 + j + s - p = q from by ring]

/-! ## The two coefficient families and their `gen_jsum`/`gen_vandermonde` equality. -/

/-- The per-commutator-index scalar coefficient of `w₍ₘ₎d` in `S_s` (LHS, the raw FZ double sum
collapsed via `inner_reindexN`): for fixed `s`, summed over the FZ index `j` and the inner residue
index `p`. -/
noncomputable def coeffSn (K M n s : ℕ) (m : ℤ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1),
    ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ))
      * ∑ p ∈ Finset.range (K + n + 1),
          cbz ((K : ℤ) + n) (p : ℤ)
            * cbz ((M : ℤ) + n) (m + 3 * n + 3 + j + s - p)
            * cbz ((p : ℤ) - ((n : ℤ) + j + 1)) (s : ℤ)

/-- The `Pres_mem_On`-tower coefficient of `w₍ₘ₎d` (RHS, the `ν`-weighted tower family of
`gen_jsum`): for fixed `s`, summed over `t ≤ s` and the descent index `e ≤ n`, with `Ws := K+M-s-1`
(so the top reads `C(Ws+n+(n+1+t+e), m+2n+2+(n+1+t+e))`). -/
noncomputable def coeffPn (K M n s : ℕ) (m : ℤ) : ℂ :=
  ∑ t ∈ Finset.range (s + 1),
    ((-1 : ℂ) ^ t * cbz ((K : ℤ) + n) ((s : ℤ) - (t : ℤ)))
      * ∑ e ∈ Finset.range (n + 1),
          ZhuRes.nu n t e
            * cbz (((K : ℤ) + M - s - 1) + n + ((n : ℤ) + 1 + t + e))
                (m + 2 * n + 2 + ((n : ℤ) + 1 + t + e))

/-- **`coeffSn = coeffPn`.**  The depth-`n` collapse of the commutator-index coefficient onto the
`ν`-tower family: combine the inner `p`-sum collapse `ZhuRes.gen_vandermonde` (per FZ index `j`)
with the keystone `j`-sum identity `ZhuRes.gen_jsum`.  At `n = 0` this is `ZhuHR.coeffS_eq_coeffP`
(`= ZhuRes.zhu_right_binom`). -/
theorem coeffSn_eq_coeffPn (K M n s : ℕ) (m : ℤ) :
    coeffSn K M n s m = coeffPn K M n s m := by
  -- Step 1: collapse each inner `p`-sum by `gen_vandermonde`.
  rw [coeffSn]
  rw [show (∑ j ∈ Finset.range (n + 1),
            ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ))
              * ∑ p ∈ Finset.range (K + n + 1),
                  cbz ((K : ℤ) + n) (p : ℤ)
                    * cbz ((M : ℤ) + n) (m + 3 * n + 3 + j + s - p)
                    * cbz ((p : ℤ) - ((n : ℤ) + j + 1)) (s : ℤ))
        = ∑ j ∈ Finset.range (n + 1),
            ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ))
              * ∑ t ∈ Finset.range (s + 1),
                  (-1 : ℂ) ^ t * cbz ((n : ℤ) + j + t) (t : ℤ)
                    * cbz ((K : ℤ) + n) ((s : ℤ) - (t : ℤ))
                    * cbz ((K : ℤ) + M + 2 * n - ((s : ℤ) - (t : ℤ))) (m + 3 * n + 3 + j + t) from
      Finset.sum_congr rfl fun j _ => by
        congr 1
        rw [← ZhuRes.gen_vandermonde K M n j s m]
        refine Finset.sum_congr rfl fun p _ => by
          rw [show m + 3 * n + 3 + j + s - (p : ℤ) = m - (p : ℤ) + 3 * n + 3 + j + s from by ring]]
  -- Step 2: distribute the `j`-scalar across the `t`-sum, then swap `∑_j ∑_t ↦ ∑_t ∑_j`.
  rw [show (∑ j ∈ Finset.range (n + 1),
            ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ))
              * ∑ t ∈ Finset.range (s + 1),
                  (-1 : ℂ) ^ t * cbz ((n : ℤ) + j + t) (t : ℤ)
                    * cbz ((K : ℤ) + n) ((s : ℤ) - (t : ℤ))
                    * cbz ((K : ℤ) + M + 2 * n - ((s : ℤ) - (t : ℤ))) (m + 3 * n + 3 + j + t))
        = ∑ j ∈ Finset.range (n + 1), ∑ t ∈ Finset.range (s + 1),
            ((-1 : ℂ) ^ t * cbz ((K : ℤ) + n) ((s : ℤ) - (t : ℤ)))
              * (((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ) * cbz ((n : ℤ) + j + t) (t : ℤ))
                  * cbz ((K : ℤ) + M + 2 * n - ((s : ℤ) - (t : ℤ))) (m + 3 * n + 3 + j + t)) from
      Finset.sum_congr rfl fun j _ => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring,
    Finset.sum_comm]
  -- Step 3: per `t`, factor out `(-1)^t C(K+n,s-t)` and collapse the `j`-sum by `gen_jsum`.
  rw [coeffPn]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.mul_sum]
  rw [show (∑ j ∈ Finset.range (n + 1),
            ((-1 : ℂ) ^ t * cbz ((K : ℤ) + n) ((s : ℤ) - (t : ℤ)))
              * (((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ) * cbz ((n : ℤ) + j + t) (t : ℤ))
                  * cbz ((K : ℤ) + M + 2 * n - ((s : ℤ) - (t : ℤ))) (m + 3 * n + 3 + j + t)))
        = ((-1 : ℂ) ^ t * cbz ((K : ℤ) + n) ((s : ℤ) - (t : ℤ)))
            * ∑ j ∈ Finset.range (n + 1),
                ((-1 : ℂ) ^ j * (Nat.choose (j + n) n : ℂ) * (Nat.choose (n + j + t) t : ℂ))
                  * cbz (((K : ℤ) + M - s - 1) + 2 * n + 1 + t)
                      (m + 3 * n + 3 + (j : ℤ) + t) from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hc1 : cbz ((j : ℤ) + n) (n : ℤ) = (Nat.choose (j + n) n : ℂ) := by
        rw [show ((j : ℤ) + n) = ((j + n : ℕ) : ℤ) from by push_cast; ring,
          cbz_natCast_eq_choose (by omega : n ≤ j + n)]
      have hc2 : cbz ((n : ℤ) + j + t) (t : ℤ) = (Nat.choose (n + j + t) t : ℂ) := by
        rw [show ((n : ℤ) + j + t) = ((n + j + t : ℕ) : ℤ) from by push_cast; ring,
          show (t : ℤ) = ((t : ℕ) : ℤ) from rfl,
          cbz_natCast_eq_choose (by omega : t ≤ n + j + t)]
      have hidx : cbz ((K : ℤ) + M + 2 * n - ((s : ℤ) - (t : ℤ))) (m + 3 * n + 3 + j + t)
          = cbz (((K : ℤ) + M - s - 1) + 2 * n + 1 + t) (m + 3 * n + 3 + (j : ℤ) + t) := by
        rw [show (K : ℤ) + M + 2 * n - ((s : ℤ) - (t : ℤ))
              = ((K : ℤ) + M - s - 1) + 2 * n + 1 + t from by ring]
      rw [hc1, hc2, hidx]]
  rw [ZhuRes.gen_jsum n t ((K : ℤ) + M - s - 1) m, Finset.mul_sum]

/-! ## Finite-support of the per-`m` scalars (so the finite-sum / finsum swaps are valid). -/

/-- For fixed `j p`, the scalar `m ↦ cbz (M+n) (m+3n+3+j+s-p)` has finite support. -/
theorem cbzN_shift_support_fin (M n : ℕ) (j s p : ℤ) :
    (Function.support (fun m : ℤ => cbz ((M : ℤ) + n) (m + 3 * n + 3 + j + s - p))).Finite := by
  refine Set.Finite.subset (ZhuHR.cbz_shift_support_fin (d := (M : ℤ) + n) (by positivity)
    (3 * n + 3 + j + s - p)) ?_
  intro m hm
  rw [Function.mem_support] at hm ⊢
  intro h; apply hm
  rwa [show m + 3 * (n : ℤ) + 3 + j + s - p = m + (3 * (n : ℤ) + 3 + j + s - p) from by ring]

/-- The `m`-support of the (scaled) inner `p`-sum scalar (the bracket of `coeffSn`, per FZ index
`j`, with an arbitrary leading scalar `c0`) is finite. -/
theorem coeffSn_inner_support_fin (W : VertexOperatorAlgebra 𝒱) (K M n : ℕ) (w d : 𝒱)
    (c0 : ℂ) (j s : ℤ) :
    Function.HasFiniteSupport
      (fun m : ℤ =>
        (c0 * ∑ p ∈ Finset.range (K + n + 1),
            cbz ((K : ℤ) + n) (p : ℤ)
              * cbz ((M : ℤ) + n) (m + 3 * n + 3 + j + s - p)
              * cbz ((p : ℤ) - ((n : ℤ) + j + 1)) (s : ℤ))
          • W.smul w m d) := by
  refine ZhuHR.smul_support_of_scalar W w d _ (Set.Finite.subset
    ((Finset.range (K + n + 1)).finite_toSet.biUnion
      (fun p _ => cbzN_shift_support_fin M n j s (p : ℤ))) ?_)
  intro m hm
  rw [Function.mem_support] at hm
  simp only [Set.mem_iUnion, Finset.mem_coe, Finset.mem_range, exists_prop]
  by_contra hcon
  push_neg at hcon
  apply hm
  rw [show (c0 * ∑ p ∈ Finset.range (K + n + 1),
            cbz ((K : ℤ) + n) (p : ℤ)
              * cbz ((M : ℤ) + n) (m + 3 * n + 3 + j + s - p)
              * cbz ((p : ℤ) - ((n : ℤ) + j + 1)) (s : ℤ))
        = c0 * ∑ p ∈ Finset.range (K + n + 1),
            cbz ((M : ℤ) + n) (m + 3 * n + 3 + j + s - p)
              * (cbz ((K : ℤ) + n) (p : ℤ) * cbz ((p : ℤ) - ((n : ℤ) + j + 1)) (s : ℤ)) from by
      congr 1; refine Finset.sum_congr rfl fun p _ => by ring]
  rw [Finset.sum_eq_zero fun p hp => ?_, mul_zero]
  have hz : cbz ((M : ℤ) + n) (m + 3 * n + 3 + j + s - p) = 0 := by
    have := hcon p (Finset.mem_range.mp hp)
    rwa [Function.mem_support, not_not] at this
  rw [hz, zero_mul]

/-! ## The depth-`n` `S_s` collapse (lift of `ZhuHR.S_eq_finsum`).

For homogeneous `c ∈ 𝒱_M`, `w := a₍ₛ₎c`, the per-commutator-index term `S_s` (the raw FZ
double/triple sum) collapses to the single mode-value finsum `∑ᶠ m, coeffSn K M n s m • w₍ₘ₎d`. -/
theorem Sn_eq_finsum (W : VertexOperatorAlgebra 𝒱) (K M n s : ℕ) (w d : 𝒱) :
    (∑ j ∈ Finset.range (n + 1),
        ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) •
          ∑ p ∈ Finset.range (K + n + 1),
            cbz ((K : ℤ) + n) (p : ℤ) •
              ∑ i ∈ Finset.range (M + n + 1),
                (cbz ((M : ℤ) + n) (i : ℤ) * cbz ((p : ℤ) - ((n : ℤ) + j + 1)) (s : ℤ))
                  • W.smul w ((p : ℤ) + (i : ℤ) - 3 * n - 3 - j - s) d)
      = ∑ᶠ m : ℤ, coeffSn K M n s m • W.smul w m d := by
  -- (a) collapse each inner `i`-sum via `inner_reindexN` (after pulling the `(p-(n+j+1),s)` scalar).
  have hinner : ∀ (j : ℤ) (p : ℤ),
      (∑ i ∈ Finset.range (M + n + 1),
          (cbz ((M : ℤ) + n) (i : ℤ) * cbz ((p : ℤ) - ((n : ℤ) + j + 1)) (s : ℤ))
            • W.smul w ((p : ℤ) + (i : ℤ) - 3 * n - 3 - j - s) d)
        = ∑ᶠ m : ℤ,
            (cbz ((M : ℤ) + n) (m + 3 * n + 3 + j + s - p)
                * cbz ((p : ℤ) - ((n : ℤ) + j + 1)) (s : ℤ))
              • W.smul w m d := by
    intro j p
    rw [show (∑ i ∈ Finset.range (M + n + 1),
              (cbz ((M : ℤ) + n) (i : ℤ) * cbz ((p : ℤ) - ((n : ℤ) + j + 1)) (s : ℤ))
                • W.smul w ((p : ℤ) + (i : ℤ) - 3 * n - 3 - j - s) d)
          = cbz ((p : ℤ) - ((n : ℤ) + j + 1)) (s : ℤ)
              • ∑ i ∈ Finset.range (M + n + 1),
                  cbz ((M : ℤ) + n) (i : ℤ)
                    • W.smul w ((p : ℤ) + (i : ℤ) - 3 * n - 3 - j - s) d from by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, mul_comm]]
    rw [inner_reindexN W M n w d j s p]
    rw [smul_finsum' (cbz ((p : ℤ) - ((n : ℤ) + j + 1)) (s : ℤ))
        (ZhuHR.smul_support_of_scalar W w d _ (cbzN_shift_support_fin M n j s p))]
    refine finsum_congr fun m => ?_
    rw [smul_smul, mul_comm]
  -- (b) rewrite the LHS using (a), then pull the finite `j,p`-scalars into the finsums.
  rw [show (∑ j ∈ Finset.range (n + 1),
            ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) •
              ∑ p ∈ Finset.range (K + n + 1),
                cbz ((K : ℤ) + n) (p : ℤ) •
                  ∑ i ∈ Finset.range (M + n + 1),
                    (cbz ((M : ℤ) + n) (i : ℤ) * cbz ((p : ℤ) - ((n : ℤ) + j + 1)) (s : ℤ))
                      • W.smul w ((p : ℤ) + (i : ℤ) - 3 * n - 3 - j - s) d)
        = ∑ j ∈ Finset.range (n + 1), ∑ p ∈ Finset.range (K + n + 1),
            ∑ᶠ m : ℤ,
              (((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) * cbz ((K : ℤ) + n) (p : ℤ)
                * (cbz ((M : ℤ) + n) (m + 3 * n + 3 + j + s - p)
                    * cbz ((p : ℤ) - ((n : ℤ) + j + 1)) (s : ℤ)))
                • W.smul w m d from
      Finset.sum_congr rfl fun j _ => by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hinner (j : ℤ) (p : ℤ)]
        -- pull `(-1)^j C(j+n,n)` and `C(K+n,p)` into the finsum
        have hfin : Function.HasFiniteSupport
            (fun m : ℤ =>
              (cbz ((M : ℤ) + n) (m + 3 * n + 3 + j + s - p)
                  * cbz ((p : ℤ) - ((n : ℤ) + j + 1)) (s : ℤ))
                • W.smul w m d) :=
          ZhuHR.smul_support_of_scalar W w d _
            (Set.Finite.subset (cbzN_shift_support_fin M n j s p)
              (fun m hm => by
                rw [Function.mem_support] at hm ⊢
                intro h; apply hm
                rw [h, zero_mul]))
        rw [smul_smul, smul_finsum'
            (((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) * cbz ((K : ℤ) + n) (p : ℤ)) hfin]
        refine finsum_congr fun m => ?_
        rw [smul_smul, mul_assoc]]
  -- (c) swap `∑_p ∑ᶠ m` then `∑_j ∑ᶠ m`, and assemble into `coeffSn`.
  rw [show (∑ j ∈ Finset.range (n + 1), ∑ p ∈ Finset.range (K + n + 1),
            ∑ᶠ m : ℤ,
              (((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) * cbz ((K : ℤ) + n) (p : ℤ)
                * (cbz ((M : ℤ) + n) (m + 3 * n + 3 + j + s - p)
                    * cbz ((p : ℤ) - ((n : ℤ) + j + 1)) (s : ℤ)))
                • W.smul w m d)
        = ∑ j ∈ Finset.range (n + 1),
            ∑ᶠ m : ℤ,
              (((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ))
                * ∑ p ∈ Finset.range (K + n + 1),
                    cbz ((K : ℤ) + n) (p : ℤ)
                      * cbz ((M : ℤ) + n) (m + 3 * n + 3 + j + s - p)
                      * cbz ((p : ℤ) - ((n : ℤ) + j + 1)) (s : ℤ))
                • W.smul w m d from
      Finset.sum_congr rfl fun j _ => by
        rw [← finsum_sum_comm (Finset.range (K + n + 1))
            (fun m p => (((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) * cbz ((K : ℤ) + n) (p : ℤ)
                * (cbz ((M : ℤ) + n) (m + 3 * n + 3 + j + s - p)
                    * cbz ((p : ℤ) - ((n : ℤ) + j + 1)) (s : ℤ)))
              • W.smul w m d)
            (fun p _ => ZhuHR.smul_support_of_scalar W w d _
              (Set.Finite.subset (cbzN_shift_support_fin M n j s p)
                (fun m hm => by
                  rw [Function.mem_support] at hm ⊢
                  intro h; apply hm
                  rw [h, zero_mul, mul_zero])))]
        refine finsum_congr fun m => ?_
        rw [Finset.mul_sum, Finset.sum_smul]
        refine Finset.sum_congr rfl fun p _ => by congr 1; ring]
  rw [← finsum_sum_comm (Finset.range (n + 1))
      (fun m j => (((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ))
          * ∑ p ∈ Finset.range (K + n + 1),
              cbz ((K : ℤ) + n) (p : ℤ)
                * cbz ((M : ℤ) + n) (m + 3 * n + 3 + j + s - p)
                * cbz ((p : ℤ) - ((n : ℤ) + j + 1)) (s : ℤ))
        • W.smul w m d)
      (fun j _ => coeffSn_inner_support_fin W K M n w d
        ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) j s)]
  refine finsum_congr fun m => ?_
  rw [coeffSn, Finset.sum_smul]

/-! ## The depth-`n` `Pres`-combination collapse (lift of `ZhuHR.PresCombo_eq_finsum`).

For `Ws : ℕ` with `(Ws:ℤ) = K+M-s-1`, the `ν`-weighted `PresOn`-tower combination (summed over the
`gen_jsum` indices `t ≤ s`, `e ≤ n`) collapses to the single mode-value finsum
`∑ᶠ m, coeffPn K M n s m • w₍ₘ₎d`. -/
theorem PresOnCombo_eq_finsum (W : VertexOperatorAlgebra 𝒱) (K M n s Ws : ℕ) (w d : 𝒱)
    (hWs : (Ws : ℤ) = (K : ℤ) + (M : ℤ) - (s : ℤ) - 1) :
    (∑ t ∈ Finset.range (s + 1),
        ((-1 : ℂ) ^ t * cbz ((K : ℤ) + n) ((s : ℤ) - (t : ℤ))) •
          ∑ e ∈ Finset.range (n + 1),
            ZhuRes.nu n t e • PresOn W Ws n (n + 1 + t + e) w d)
      = ∑ᶠ m : ℤ, coeffPn K M n s m • W.smul w m d := by
  rw [show (∑ t ∈ Finset.range (s + 1),
            ((-1 : ℂ) ^ t * cbz ((K : ℤ) + n) ((s : ℤ) - (t : ℤ))) •
              ∑ e ∈ Finset.range (n + 1),
                ZhuRes.nu n t e • PresOn W Ws n (n + 1 + t + e) w d)
        = ∑ t ∈ Finset.range (s + 1),
            ∑ᶠ m : ℤ,
              (((-1 : ℂ) ^ t * cbz ((K : ℤ) + n) ((s : ℤ) - (t : ℤ)))
                * ∑ e ∈ Finset.range (n + 1),
                    ZhuRes.nu n t e
                      * cbz ((Ws : ℤ) + n + ((n : ℤ) + 1 + t + e))
                          (m + 2 * n + 2 + ((n : ℤ) + 1 + t + e)))
                • W.smul w m d from
      Finset.sum_congr rfl fun t _ => by
        -- expand each `PresOn` into its mode-value finsum, pull `ν` in, sum over `e`, then pull
        -- the `t`-scalar in.
        rw [show (∑ e ∈ Finset.range (n + 1), ZhuRes.nu n t e • PresOn W Ws n (n + 1 + t + e) w d)
              = ∑ e ∈ Finset.range (n + 1),
                  ∑ᶠ m : ℤ,
                    (ZhuRes.nu n t e
                      * cbz ((Ws : ℤ) + n + ((n + 1 + t + e : ℕ) : ℤ))
                          (m + 2 * n + 2 + ((n + 1 + t + e : ℕ) : ℤ)))
                      • W.smul w m d from
            Finset.sum_congr rfl fun e _ => by
              rw [PresOn_eq_finsum W Ws n (n + 1 + t + e) w d]
              have hfin : Function.HasFiniteSupport
                  (fun m : ℤ =>
                    cbz ((Ws : ℤ) + n + ((n + 1 + t + e : ℕ) : ℤ))
                        (m + 2 * n + 2 + ((n + 1 + t + e : ℕ) : ℤ)) • W.smul w m d) :=
                ZhuHR.smul_support_of_scalar W w d _
                  (Set.Finite.subset
                    (ZhuHR.cbz_shift_support_fin
                      (d := (Ws : ℤ) + n + ((n + 1 + t + e : ℕ) : ℤ)) (by positivity)
                      (2 * n + 2 + ((n + 1 + t + e : ℕ) : ℤ)))
                    (fun m hm => by
                      rw [Function.mem_support] at hm ⊢
                      intro h; apply hm
                      rwa [show m + 2 * (n : ℤ) + 2 + ((n + 1 + t + e : ℕ) : ℤ)
                              = m + (2 * (n : ℤ) + 2 + ((n + 1 + t + e : ℕ) : ℤ)) from by ring]))
              rw [smul_finsum' (ZhuRes.nu n t e) hfin]
              refine finsum_congr fun m => ?_
              rw [smul_smul]]
        -- collapse the `e`-sum past `∑ᶠ m` (factored form), then pull the `t`-scalar in.
        rw [show (∑ e ∈ Finset.range (n + 1),
                  ∑ᶠ m : ℤ,
                    (ZhuRes.nu n t e
                      * cbz ((Ws : ℤ) + n + ((n + 1 + t + e : ℕ) : ℤ))
                          (m + 2 * n + 2 + ((n + 1 + t + e : ℕ) : ℤ)))
                      • W.smul w m d)
              = ∑ e ∈ Finset.range (n + 1),
                  ∑ᶠ m : ℤ,
                    (ZhuRes.nu n t e
                      * cbz ((Ws : ℤ) + n + ((n : ℤ) + 1 + t + e))
                          (m + 2 * n + 2 + ((n : ℤ) + 1 + t + e)))
                      • W.smul w m d from
            Finset.sum_congr rfl fun e _ => by
              rw [show ((n + 1 + t + e : ℕ) : ℤ) = (n : ℤ) + 1 + t + e from by push_cast; ring]]
        rw [← finsum_sum_comm (Finset.range (n + 1))
            (fun m e => (ZhuRes.nu n t e
                * cbz ((Ws : ℤ) + n + ((n : ℤ) + 1 + t + e))
                    (m + 2 * n + 2 + ((n : ℤ) + 1 + t + e)))
              • W.smul w m d)
            (fun e _ => ZhuHR.smul_support_of_scalar W w d _
              (Set.Finite.subset
                (ZhuHR.cbz_shift_support_fin
                  (d := (Ws : ℤ) + n + ((n : ℤ) + 1 + t + (e : ℤ))) (by positivity)
                  (2 * n + 2 + ((n : ℤ) + 1 + t + (e : ℤ))))
                (fun m hm => by
                  rw [Function.mem_support] at hm ⊢
                  intro h; apply hm
                  rw [show m + 2 * (n : ℤ) + 2 + ((n : ℤ) + 1 + t + (e : ℤ))
                        = m + (2 * (n : ℤ) + 2 + ((n : ℤ) + 1 + t + (e : ℤ))) from by ring]
                  rw [h, mul_zero])))]
        -- now the finsum body is `∑_e (...)•w`; factor to `(∑_e ...)•w`.
        rw [show (∑ᶠ m : ℤ, ∑ e ∈ Finset.range (n + 1),
                    (ZhuRes.nu n t e
                      * cbz ((Ws : ℤ) + n + ((n : ℤ) + 1 + t + e))
                          (m + 2 * n + 2 + ((n : ℤ) + 1 + t + e)))
                      • W.smul w m d)
              = ∑ᶠ m : ℤ,
                  (∑ e ∈ Finset.range (n + 1),
                      ZhuRes.nu n t e
                        * cbz ((Ws : ℤ) + n + ((n : ℤ) + 1 + t + e))
                            (m + 2 * n + 2 + ((n : ℤ) + 1 + t + e)))
                    • W.smul w m d from
            finsum_congr fun m => (Finset.sum_smul ..).symm]
        have hfin2 : Function.HasFiniteSupport
            (fun m : ℤ =>
              (∑ e ∈ Finset.range (n + 1),
                  ZhuRes.nu n t e
                    * cbz ((Ws : ℤ) + n + ((n : ℤ) + 1 + t + e))
                        (m + 2 * n + 2 + ((n : ℤ) + 1 + t + e)))
                • W.smul w m d) := by
          refine ZhuHR.smul_support_of_scalar W w d _ (Set.Finite.subset
            ((Finset.range (n + 1)).finite_toSet.biUnion
              (fun e _ => ZhuHR.cbz_shift_support_fin
                (d := (Ws : ℤ) + n + ((n : ℤ) + 1 + t + (e : ℤ))) (by positivity)
                (2 * n + 2 + ((n : ℤ) + 1 + t + (e : ℤ))))) ?_)
          intro m hm
          rw [Function.mem_support] at hm
          simp only [Set.mem_iUnion, Finset.mem_coe, Finset.mem_range, exists_prop]
          by_contra hcon
          push_neg at hcon
          apply hm
          refine Finset.sum_eq_zero fun e he => ?_
          have hz : cbz ((Ws : ℤ) + n + ((n : ℤ) + 1 + t + (e : ℤ)))
              (m + 2 * n + 2 + ((n : ℤ) + 1 + t + (e : ℤ))) = 0 := by
            have hsup := hcon e (Finset.mem_range.mp he)
            rw [Function.mem_support, not_not] at hsup
            rw [show m + 2 * (n : ℤ) + 2 + ((n : ℤ) + 1 + t + (e : ℤ))
                  = m + (2 * (n : ℤ) + 2 + ((n : ℤ) + 1 + t + (e : ℤ))) from by ring]
            exact hsup
          rw [hz, mul_zero]
        rw [smul_finsum' ((-1 : ℂ) ^ t * cbz ((K : ℤ) + n) ((s : ℤ) - (t : ℤ))) hfin2]
        refine finsum_congr fun m => ?_
        rw [smul_smul]]
  -- swap `∑_t ∑ᶠ m ↦ ∑ᶠ m ∑_t`, then assemble into `coeffPn`.
  rw [← finsum_sum_comm (Finset.range (s + 1))
      (fun m t => (((-1 : ℂ) ^ t * cbz ((K : ℤ) + n) ((s : ℤ) - (t : ℤ)))
          * ∑ e ∈ Finset.range (n + 1),
              ZhuRes.nu n t e
                * cbz ((Ws : ℤ) + n + ((n : ℤ) + 1 + t + e))
                    (m + 2 * n + 2 + ((n : ℤ) + 1 + t + e)))
        • W.smul w m d)
      (fun t _ => by
        refine ZhuHR.smul_support_of_scalar W w d _ (Set.Finite.subset
          ((Finset.range (n + 1)).finite_toSet.biUnion
            (fun e _ => ZhuHR.cbz_shift_support_fin
              (d := (Ws : ℤ) + n + ((n : ℤ) + 1 + t + (e : ℤ))) (by positivity)
              (2 * n + 2 + ((n : ℤ) + 1 + t + (e : ℤ))))) ?_)
        intro m hm
        rw [Function.mem_support] at hm
        simp only [Set.mem_iUnion, Finset.mem_coe, Finset.mem_range, exists_prop]
        by_contra hcon
        push_neg at hcon
        apply hm
        rw [Finset.sum_eq_zero fun e he => ?_, mul_zero]
        have hz : cbz ((Ws : ℤ) + n + ((n : ℤ) + 1 + t + (e : ℤ)))
            (m + 2 * n + 2 + ((n : ℤ) + 1 + t + (e : ℤ))) = 0 := by
          have hsup := hcon e (Finset.mem_range.mp he)
          rw [Function.mem_support, not_not] at hsup
          rw [show m + 2 * (n : ℤ) + 2 + ((n : ℤ) + 1 + t + (e : ℤ))
                = m + (2 * (n : ℤ) + 2 + ((n : ℤ) + 1 + t + (e : ℤ))) from by ring]
          exact hsup
        rw [hz, mul_zero])]
  refine finsum_congr fun m => ?_
  rw [coeffPn, Finset.sum_smul]
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  rw [show (K : ℤ) + M - s - 1 = (Ws : ℤ) from hWs.symm]

/-! ## The depth-`n` `S_s ∈ Oₙ` (lift of `ZhuHR.S_mem_O`). -/

/-- **The per-commutator-index term lies in `Oₙ`.**  For homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`,
`w := a₍ₛ₎c ∈ 𝒱_{K+M-s-1}`, the raw FZ commutator-family term `S_s` lies in `Oₙ(𝒱)`: it collapses
(via `Sn_eq_finsum` + `coeffSn_eq_coeffPn` + `PresOnCombo_eq_finsum`) onto the `ν`-weighted
`PresOn`-tower combination, each tower `∈ Oₙ` by the keystone `Pres_mem_On`.  At `n = 0` this is
`ZhuHR.S_mem_O`. -/
theorem Sn_mem_On (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ} {a c : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) (s : ℕ) :
    (∑ j ∈ Finset.range (n + 1),
        ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) •
          ∑ p ∈ Finset.range (K + n + 1),
            cbz ((K : ℤ) + n) (p : ℤ) •
              ∑ i ∈ Finset.range (M + n + 1),
                (cbz ((M : ℤ) + n) (i : ℤ) * cbz ((p : ℤ) - ((n : ℤ) + j + 1)) (s : ℤ))
                  • W.smul (W.smul a (s : ℤ) c)
                      ((p : ℤ) + (i : ℤ) - 3 * n - 3 - j - s) d) ∈ On W n := by
  set w := W.smul a (s : ℤ) c with hw
  have hwmem : w ∈ W.grading ((K : ℤ) + (M : ℤ) - (s : ℤ) - 1) := W.smul_mem_grading ha hc (s : ℤ)
  rw [Sn_eq_finsum W K M n s w d]
  rcases lt_or_ge ((K : ℤ) + (M : ℤ) - (s : ℤ) - 1) 0 with hneg | hpos
  · -- `w ∈ 𝒱_{<0} = ⊥`, so `w = 0` and the finsum is `0`.
    rw [W.positivity _ hneg, Submodule.mem_bot] at hwmem
    rw [show (∑ᶠ m : ℤ, coeffSn K M n s m • W.smul w m d) = 0 from by
      refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
      rw [hwmem, PreVertexAlgebra.smul_zero_left, smul_zero]]
    exact (On W n).zero_mem
  · -- `Ws := K+M-s-1 : ℕ`; rewrite the finsum as the `PresOn`-combination, in `Oₙ`.
    obtain ⟨Ws, hWs⟩ : ∃ Ws : ℕ, (Ws : ℤ) = (K : ℤ) + (M : ℤ) - (s : ℤ) - 1 :=
      ⟨((K : ℤ) + (M : ℤ) - (s : ℤ) - 1).toNat, by omega⟩
    have hwmem' : w ∈ W.grading (Ws : ℤ) := by rwa [hWs]
    rw [show (∑ᶠ m : ℤ, coeffSn K M n s m • W.smul w m d)
          = ∑ᶠ m : ℤ, coeffPn K M n s m • W.smul w m d from
        finsum_congr fun m => by rw [coeffSn_eq_coeffPn],
      ← PresOnCombo_eq_finsum W K M n s Ws w d hWs]
    apply Submodule.sum_mem
    intro t _
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro e _
    exact Submodule.smul_mem _ _ (Pres_mem_On W n hwmem' d (n + 1 + t + e))

/-! ## The commutator family of the right-slot `leftProd` membership lies in `Oₙ`. -/

/-- **The commutator family lies in `Oₙ`** (depth-`n` lift of `ZhuHR.commutator_family_mem_O`).
For homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, the commutator part of `leftProd W n a (circ W n c d)` —
`∑_j (-1)^j C(j+n,n) ∑_p C(K+n,p) ∑_i C(M+n,i) • ⁅a₍p-n-j-1₎, c₍i-2n-2₎⁆ d` — lies in `Oₙ(𝒱)`.
Expand each bracket via `mode_commutator_uniform`, merge the locality `s`-sum into each summand,
pull `∑_s` outermost (each fixed-`s` slice is `Sn_mem_On`). -/
theorem leftProd_circ_commutator_family_mem_On (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ}
    {a c : 𝒱} (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) :
    (∑ j ∈ Finset.range (n + 1),
        ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) •
          ∑ p ∈ Finset.range (K + n + 1),
            cbz ((K : ℤ) + n) (p : ℤ) •
              ∑ i ∈ Finset.range (M + n + 1),
                cbz ((M : ℤ) + n) (i : ℤ)
                  • ⁅mode (W.Y a) ((p : ℤ) - (n : ℤ) - (j : ℤ) - 1),
                      mode (W.Y c) ((i : ℤ) - 2 * (n : ℤ) - 2)⁆ d) ∈ On W n := by
  obtain ⟨N, hN⟩ := ZhuHR.mode_commutator_uniform W a c
  -- expand each bracket, merge the `s`-sum into each `(j,p,i)` summand, then pull `∑_s` outermost.
  rw [show (∑ j ∈ Finset.range (n + 1),
            ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) •
              ∑ p ∈ Finset.range (K + n + 1),
                cbz ((K : ℤ) + n) (p : ℤ) •
                  ∑ i ∈ Finset.range (M + n + 1),
                    cbz ((M : ℤ) + n) (i : ℤ)
                      • ⁅mode (W.Y a) ((p : ℤ) - (n : ℤ) - (j : ℤ) - 1),
                          mode (W.Y c) ((i : ℤ) - 2 * (n : ℤ) - 2)⁆ d)
        = ∑ s ∈ Finset.range N,
            ∑ j ∈ Finset.range (n + 1),
              ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) •
                ∑ p ∈ Finset.range (K + n + 1),
                  cbz ((K : ℤ) + n) (p : ℤ) •
                    ∑ i ∈ Finset.range (M + n + 1),
                      (cbz ((M : ℤ) + n) (i : ℤ)
                          * cbz ((p : ℤ) - ((n : ℤ) + j + 1)) (s : ℤ))
                        • W.smul (W.smul a (s : ℤ) c)
                            ((p : ℤ) + (i : ℤ) - 3 * n - 3 - j - s) d from ?_]
  · apply Submodule.sum_mem
    intro s _
    exact Sn_mem_On W n ha hc d s
  · -- the reindexing identity: merge `∑_s` into each `(j,p,i)`-summand, then pull it outermost.
    rw [show (∑ j ∈ Finset.range (n + 1),
              ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) •
                ∑ p ∈ Finset.range (K + n + 1),
                  cbz ((K : ℤ) + n) (p : ℤ) •
                    ∑ i ∈ Finset.range (M + n + 1),
                      cbz ((M : ℤ) + n) (i : ℤ)
                        • ⁅mode (W.Y a) ((p : ℤ) - (n : ℤ) - (j : ℤ) - 1),
                            mode (W.Y c) ((i : ℤ) - 2 * (n : ℤ) - 2)⁆ d)
          = ∑ j ∈ Finset.range (n + 1),
              ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) •
                ∑ p ∈ Finset.range (K + n + 1),
                  cbz ((K : ℤ) + n) (p : ℤ) •
                    ∑ i ∈ Finset.range (M + n + 1), ∑ s ∈ Finset.range N,
                      (cbz ((M : ℤ) + n) (i : ℤ)
                          * cbz ((p : ℤ) - ((n : ℤ) + j + 1)) (s : ℤ))
                        • W.smul (W.smul a (s : ℤ) c)
                            ((p : ℤ) + (i : ℤ) - 3 * n - 3 - j - s) d from
        Finset.sum_congr rfl fun j _ => by
          congr 1
          refine Finset.sum_congr rfl fun p _ => by
            congr 1
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hN ((p : ℤ) - (n : ℤ) - (j : ℤ) - 1) ((i : ℤ) - 2 * (n : ℤ) - 2) d,
              Finset.smul_sum]
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [smul_smul,
              show ((p : ℤ) - (n : ℤ) - (j : ℤ) - 1) + ((i : ℤ) - 2 * (n : ℤ) - 2) - (s : ℤ)
                = (p : ℤ) + (i : ℤ) - 3 * n - 3 - j - s from by ring,
              show (p : ℤ) - ((n : ℤ) + j + 1) = (p : ℤ) - (n : ℤ) - (j : ℤ) - 1 from by ring]]
    -- pull `∑_s` outermost: per `j`, swap (i,s), distribute `c2_p` and swap (p,s); then swap (j,s).
    rw [show (∑ j ∈ Finset.range (n + 1),
              ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) •
                ∑ p ∈ Finset.range (K + n + 1),
                  cbz ((K : ℤ) + n) (p : ℤ) •
                    ∑ i ∈ Finset.range (M + n + 1), ∑ s ∈ Finset.range N,
                      (cbz ((M : ℤ) + n) (i : ℤ)
                          * cbz ((p : ℤ) - ((n : ℤ) + j + 1)) (s : ℤ))
                        • W.smul (W.smul a (s : ℤ) c)
                            ((p : ℤ) + (i : ℤ) - 3 * n - 3 - j - s) d)
          = ∑ j ∈ Finset.range (n + 1),
              ∑ s ∈ Finset.range N,
                ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) •
                  ∑ p ∈ Finset.range (K + n + 1),
                    cbz ((K : ℤ) + n) (p : ℤ) •
                      ∑ i ∈ Finset.range (M + n + 1),
                        (cbz ((M : ℤ) + n) (i : ℤ)
                            * cbz ((p : ℤ) - ((n : ℤ) + j + 1)) (s : ℤ))
                          • W.smul (W.smul a (s : ℤ) c)
                              ((p : ℤ) + (i : ℤ) - 3 * n - 3 - j - s) d from
        Finset.sum_congr rfl fun j _ => by
          rw [show (∑ p ∈ Finset.range (K + n + 1),
                    cbz ((K : ℤ) + n) (p : ℤ) •
                      ∑ i ∈ Finset.range (M + n + 1), ∑ s ∈ Finset.range N,
                        (cbz ((M : ℤ) + n) (i : ℤ)
                            * cbz ((p : ℤ) - ((n : ℤ) + j + 1)) (s : ℤ))
                          • W.smul (W.smul a (s : ℤ) c)
                              ((p : ℤ) + (i : ℤ) - 3 * n - 3 - j - s) d)
                = ∑ s ∈ Finset.range N,
                    ∑ p ∈ Finset.range (K + n + 1),
                      cbz ((K : ℤ) + n) (p : ℤ) •
                        ∑ i ∈ Finset.range (M + n + 1),
                          (cbz ((M : ℤ) + n) (i : ℤ)
                              * cbz ((p : ℤ) - ((n : ℤ) + j + 1)) (s : ℤ))
                            • W.smul (W.smul a (s : ℤ) c)
                                ((p : ℤ) + (i : ℤ) - 3 * n - 3 - j - s) d from by
              rw [show (∑ p ∈ Finset.range (K + n + 1),
                        cbz ((K : ℤ) + n) (p : ℤ) •
                          ∑ i ∈ Finset.range (M + n + 1), ∑ s ∈ Finset.range N,
                            (cbz ((M : ℤ) + n) (i : ℤ)
                                * cbz ((p : ℤ) - ((n : ℤ) + j + 1)) (s : ℤ))
                              • W.smul (W.smul a (s : ℤ) c)
                                  ((p : ℤ) + (i : ℤ) - 3 * n - 3 - j - s) d)
                    = ∑ p ∈ Finset.range (K + n + 1), ∑ s ∈ Finset.range N,
                        cbz ((K : ℤ) + n) (p : ℤ) •
                          ∑ i ∈ Finset.range (M + n + 1),
                            (cbz ((M : ℤ) + n) (i : ℤ)
                                * cbz ((p : ℤ) - ((n : ℤ) + j + 1)) (s : ℤ))
                              • W.smul (W.smul a (s : ℤ) c)
                                  ((p : ℤ) + (i : ℤ) - 3 * n - 3 - j - s) d from
                  Finset.sum_congr rfl fun p _ => by
                    rw [Finset.sum_comm (s := Finset.range (M + n + 1)) (t := Finset.range N),
                      Finset.smul_sum]]
              rw [Finset.sum_comm (s := Finset.range (K + n + 1)) (t := Finset.range N)]]
          rw [Finset.smul_sum]]
    -- finally swap the outer `(j,s)` to put `∑_s` outermost.
    rw [Finset.sum_comm (s := Finset.range (n + 1)) (t := Finset.range N)]

/-! ## Membership 1: `leftProd W n a (circ W n c d) ∈ Oₙ` for homogeneous `a, c`. -/

/-- For homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, the right-slot product `leftProd W n a (circ W n c d)`
lies in `Oₙ(𝒱)` (Zhu Thm 2.1.1, depth-`n`).  Expand by `leftProd_homogeneous` + `circ_homogeneous`,
split each `a₍α₎(c₍β₎d)` by `mode_split_gen` into the **`c`-first family**
(`leftProd_circ_first_family_mem_On`) plus the **commutator family**
(`leftProd_circ_commutator_family_mem_On`). -/
theorem leftProd_circ_mem_On_homog (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ}
    {a c : 𝒱} (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) :
    leftProd W n a (circ W n c d) ∈ On W n := by
  rw [leftProd_homogeneous W n ha (circ W n c d)]
  -- normalise `(K+n).toNat+1 = K+n+1`, expand the inner `circ`, and split each mode product.
  rw [show ((K : ℤ) + (n : ℤ)).toNat + 1 = K + n + 1 from by
        rw [show ((K : ℤ) + (n : ℤ)) = ((K + n : ℕ) : ℤ) from by push_cast; ring, Int.toNat_natCast]]
  rw [show (∑ j ∈ Finset.range (n + 1),
            ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) •
              ∑ p ∈ Finset.range (K + n + 1),
                cbz ((K : ℤ) + (n : ℤ)) p •
                  W.smul a ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) (circ W n c d))
        = (∑ j ∈ Finset.range (n + 1),
            ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) •
              ∑ p ∈ Finset.range (K + n + 1),
                cbz ((K : ℤ) + (n : ℤ)) p •
                  ∑ i ∈ Finset.range ((M + (n : ℤ)).toNat + 1),
                    cbz (M + (n : ℤ)) i •
                      W.smul c ((i : ℤ) - 2 * (n : ℤ) - 2)
                        (W.smul a ((p : ℤ) - (n : ℤ) - (j : ℤ) - 1) d))
          + (∑ j ∈ Finset.range (n + 1),
              ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) •
                ∑ p ∈ Finset.range (K + n + 1),
                  cbz ((K : ℤ) + n) (p : ℤ) •
                    ∑ i ∈ Finset.range (M + n + 1),
                      cbz ((M : ℤ) + n) (i : ℤ)
                        • ⁅mode (W.Y a) ((p : ℤ) - (n : ℤ) - (j : ℤ) - 1),
                            mode (W.Y c) ((i : ℤ) - 2 * (n : ℤ) - 2)⁆ d) from ?_]
  · -- the `c`-first family (∈ Oₙ) plus the commutator family (∈ Oₙ).
    refine Submodule.add_mem _ ?_ (leftProd_circ_commutator_family_mem_On W n ha hc d)
    -- the `c`-first family: each inner i-sum is `circ W n c (a₍p−n−j−1₎d) ∈ Oₙ`.
    apply Submodule.sum_mem; intro j _
    apply Submodule.smul_mem
    apply Submodule.sum_mem; intro p _
    apply Submodule.smul_mem
    rw [← circ_homogeneous W n hc (W.smul a ((p : ℤ) - (n : ℤ) - (j : ℤ) - 1) d)]
    exact circ_mem_On W n c _
  · -- the split identity, summand by summand, via `circ_homogeneous` + `mode_split_gen`.
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_add]
    congr 1
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [circ_homogeneous W n hc d]
    -- the inner `circ`-residue expanded: distribute `W.smul a _` over the i-sum.
    rw [show W.smul a ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1))
              (∑ i ∈ Finset.range ((M + (n : ℤ)).toNat + 1),
                cbz (M + (n : ℤ)) i • W.smul c ((i : ℤ) - 2 * (n : ℤ) - 2) d)
          = ∑ i ∈ Finset.range ((M + (n : ℤ)).toNat + 1),
              cbz (M + (n : ℤ)) i
                • W.smul a ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1))
                    (W.smul c ((i : ℤ) - 2 * (n : ℤ) - 2) d) from by
        rw [PreVertexAlgebra.smul_def, map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [LinearMap.map_smul]; rfl]
    rw [← smul_add]
    congr 1
    -- normalise the two `i`-ranges to `M+n+1` and split each mode product.
    rw [show ((M + (n : ℤ)).toNat + 1) = M + n + 1 from by
          rw [show ((M : ℤ) + (n : ℤ)) = ((M + n : ℕ) : ℤ) from by push_cast; ring,
            Int.toNat_natCast]]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← smul_add]
    congr 1
    rw [show W.smul a ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1))
              (W.smul c ((i : ℤ) - 2 * (n : ℤ) - 2) d)
          = W.smul a ((p : ℤ) - (n : ℤ) - (j : ℤ) - 1)
              (W.smul c ((i : ℤ) - 2 * (n : ℤ) - 2) d) from by
        rw [show (p : ℤ) - ((n : ℤ) + (j : ℤ) + 1) = (p : ℤ) - (n : ℤ) - (j : ℤ) - 1 from by ring]]
    rw [mode_split_gen W a c d ((p : ℤ) - (n : ℤ) - (j : ℤ) - 1) ((i : ℤ) - 2 * (n : ℤ) - 2)]

/-- **Membership 1, de-homogenized:** `leftProd W n a (circ W n c d) ∈ Oₙ(𝒱)` for arbitrary
`a c d` (reduce `a` and `c` to homogeneous slices via `reduce_homogeneous`; negative grades vanish
by `positivity`). -/
theorem leftProd_circ_mem_On (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a c d : 𝒱) :
    leftProd W n a (circ W n c d) ∈ On W n := by
  refine reduce_homogeneous W (P := fun a => leftProd W n a (circ W n c d) ∈ On W n) ?_ ?_ ?_ a
  · intro K a ha
    -- reduce `c` to homogeneous as well.
    refine reduce_homogeneous W (P := fun c => leftProd W n a (circ W n c d) ∈ On W n) ?_ ?_ ?_ c
    · intro M c hc
      rcases lt_or_ge K 0 with hK | hK
      · rw [W.positivity K hK, Submodule.mem_bot] at ha
        subst ha; rw [leftProd_zero_left]; exact (On W n).zero_mem
      rcases lt_or_ge M 0 with hM | hM
      · rw [W.positivity M hM, Submodule.mem_bot] at hc
        subst hc
        rw [circ_zero_left W n d, leftProd_zero_right]
        exact (On W n).zero_mem
      · obtain ⟨K', rfl⟩ : ∃ K' : ℕ, K = (K' : ℤ) := ⟨K.toNat, by omega⟩
        obtain ⟨M', rfl⟩ : ∃ M' : ℕ, M = (M' : ℤ) := ⟨M.toNat, by omega⟩
        exact leftProd_circ_mem_On_homog W n ha hc d
    · show leftProd W n a (circ W n 0 d) ∈ On W n
      rw [circ_zero_left W n d, leftProd_zero_right]
      exact (On W n).zero_mem
    · intro x y hx hy
      show leftProd W n a (circ W n (x + y) d) ∈ On W n
      rw [circ_add_left, leftProd_add_right]
      exact (On W n).add_mem hx hy
  · show leftProd W n 0 (circ W n c d) ∈ On W n
    rw [leftProd_zero_left]; exact (On W n).zero_mem
  · intro x y hx hy
    show leftProd W n (x + y) (circ W n c d) ∈ On W n
    rw [leftProd_add_left]
    exact (On W n).add_mem hx hy

/-! ## Membership 1 ⟹ the `LeftDescends.on_mem` field (`𝒱 *ₙ Oₙ ⊆ Oₙ`). -/

/-- **`𝒱 *ₙ Oₙ(𝒱) ⊆ Oₙ(𝒱)`** (the `LeftDescends.on_mem` field): for all `a` and all `x ∈ Oₙ`,
`leftProd W n a x ∈ Oₙ`.  Reduce `x` to circle generators (`leftProd_On_of_gen`) and apply the
proved membership 1 `leftProd_circ_mem_On`. -/
theorem leftProd_On_mem_On (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a : 𝒱) :
    ∀ x ∈ On W n, leftProd W n a x ∈ On W n :=
  leftProd_On_of_gen W n a (fun c d => leftProd_circ_mem_On W n a c d)

/-!
## The remaining three memberships: PRECISE stated targets (NOT `sorry`)

With **membership 1** (`leftProd_circ_mem_On`) proved, the `LeftDescends.on_mem` field
(`leftProd_On_mem_On` : `𝒱 *ₙ Oₙ ⊆ Oₙ`) is discharged unconditionally — one of the two
bimodule-descent `on_mem` directions.  The bridge machinery built here — `coeffSn_eq_coeffPn`
(combining `ZhuRes.gen_vandermonde` + `ZhuRes.gen_jsum`), `Sn_eq_finsum`, `PresOnCombo_eq_finsum`,
`Sn_mem_On` — is the exact depth-`n` lift of the `n = 0` `ZhuRightIdeal` residue bookkeeping and is
reusable for the iterate-style memberships once their associator decomposition is in place.

The three remaining circle-generator memberships (fields of `LeftDescends`/`RightDescends`) are:

* **`RightDescends.on_mem`** : `∀ x ∈ Oₙ, ∀ a, rightProd W n x a ∈ Oₙ`, reduced (via
  `rightProd_On_of_gen` + `On_eq_span`) to `∀ c d a, rightProd W n (circ W n c d) a ∈ Oₙ`.  Here the
  circle product is in the **first** (homogeneous-required) slot of `rightProd`; after the bilinear
  `rightProd_homogeneous` collapse on the homogeneous pieces of `circ W n c d` (`s = j`), the residue
  acts on the *iterated* mode `(c₍β₎d)₍γ₎a`.

* **`LeftDescends.gen_mem`** : `∀ g ∈ O W, ∀ b, leftProd W n g b ∈ Oₙ` (`O(𝒱) *ₙ 𝒱 ⊆ Oₙ`).  The
  `O(𝒱)`-generator `g = (L₋₁u+L₀u)*v = ∑ᵢ C(M,i) u₍ᵢ₋₂₎v` sits in the **first** slot of `leftProd`;
  again the residue acts on an iterate `(u₍β₎v)₍γ₎b`.

* **`RightDescends.gen_mem`** : `∀ x, ∀ g ∈ O W, rightProd W n x g ∈ Oₙ` (`𝒱 *ₙ O(𝒱) ⊆ Oₙ`).  After
  `rightProd_homogeneous` (homogeneous `x ∈ 𝒱_L`) + `zhuMul_L_base`, the term is
  `x₍γ₎(u₍ᵢ₋₂₎v)`; `mode_split_gen` splits it, but the resulting `u₍·₎`-first family is an `O(𝒱)`
  base residue, NOT an `Oₙ`-circle product (`O(𝒱) ⊄ Oₙ(𝒱)` for `n ≥ 1`), so it does not collapse via
  the commutator route alone.

Each of these is the depth-`n` lift of the *associator/iterate* machinery
(`ZhuUCore.u_core` / `ZhuVCore.v_core` / `ZhuAssociator.associator_core`, the `n = 0` left-ideal
direction), a separate development.  The provided combinatorial certificates `ZhuRes.gen_jsum` /
`ZhuRes.gen_vandermonde` are the *commutator-family* identities — they feed membership 1 (proved
above); the iterate-family analogs (the `μ`-coefficient `mode_iterate` decomposition) are what the
three above require.  Packaging the four into `LeftDescends`/`RightDescends` would then yield the
unconditional `An.lActU`/`An.rActU` with the `n = 0` anchors `An.lAct_zero_mk`/`An.rAct_zero_mk`;
that final packaging is deliberately NOT performed here (it would require the not-yet-built iterate
machinery), and is NOT faked/axiomatized.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.PresOn_eq_finsum
  #print axioms VOA.mode_split_gen
  #print axioms VOA.inner_reindexN
  #print axioms VOA.coeffSn_eq_coeffPn
  #print axioms VOA.Sn_eq_finsum
  #print axioms VOA.PresOnCombo_eq_finsum
  #print axioms VOA.Sn_mem_On
  #print axioms VOA.leftProd_circ_commutator_family_mem_On
  #print axioms VOA.leftProd_circ_mem_On_homog
  #print axioms VOA.leftProd_circ_mem_On
  #print axioms VOA.leftProd_On_mem_On
-/
