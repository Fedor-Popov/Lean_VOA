/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchRgenClose

/-!
# `hRgen` closed — the right-slot pure-mode residual `RgenRest ∈ Oₙ`.

This file discharges the single remaining homogeneous core of the right-slot `OnL` membership
(`hRgen`), namely

  `RgenRest W n K a c ∈ On W n`     (for `a ∈ 𝒱_K`, `c ∈ 𝒱_M` homogeneous),

and hence `hRgen` outright through `hRgen_closed_of_rest`.

## The key collapse identity (engine-verified, then proved here by a clean telescope)

The whole residual collapses onto a SINGLE circle product — every higher `PresOn` tower has weight
`0`:

  `RgenRest W n K a c = w₀(n) • circ W n a c`,   `w₀(n) = (-1)^{n+1}·(2n+1)·C(2n,n)`.

Since `circ W n a c ∈ Oₙ` (`circ_mem_On`), this closes `RgenRest ∈ Oₙ` immediately.

The proof is purely a per-mode scalar coefficient identity: for every mode value `p`,

  `∑_{j≤n} (-1)^j C(j+n,n) [ (p+1-K)·C(K+n,p+n+j+1) + (p+1)·C(K+n,p+n+j+2) ]
     = w₀(n)·C(K+n, p+2n+2)`,

which telescopes via `f j = h j − h (j+1)` with
`h j = (-1)^j · (-(C(j+n,n)·j)) · C(K+n,p+n+j+1)` (so `h 0 = 0`, `∑_{j≤n} f = -h(n+1)`),
the per-step identity using `cbz_upper_shift` (`m·C(m+n,n) = (m+n)·C(m+n-1,n)`) and
`cbz_upper_absorption` (`i·C(K,i) = K·C(K-1,i-1)`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators
open Finset

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The scalar tower weight and the per-mode coefficient identity. -/

/-- The single-tower weight `w₀(n) = (-1)^{n+1}·(2n+1)·C(2n,n)`. -/
noncomputable def rgenW0 (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ (n + 1) * (2 * (n : ℂ) + 1) * (Nat.choose (2 * n) n : ℂ)

/-- The telescoping function `h j = (-1)^j · (-(C(j+n,n)·j)) · C(K+n, p+n+j+1)`. -/
noncomputable def rgenH (K n : ℕ) (p : ℤ) (j : ℕ) : ℂ :=
  (-1 : ℂ) ^ j * (-(cbz ((j : ℤ) + n) n * (j : ℂ)))
    * cbz ((K : ℤ) + n) (p + n + (j : ℤ) + 1)

/-- The per-`j` summand of the residual coefficient (the bracket of `RgenRest` collected at mode
value `p`): `(-1)^j C(j+n,n) [ (p+1-K)·C(K+n,p+n+j+1) + (p+1)·C(K+n,p+n+j+2) ]`. -/
noncomputable def rgenF (K n : ℕ) (p : ℤ) (j : ℕ) : ℂ :=
  (-1 : ℂ) ^ j * cbz ((j : ℤ) + n) n
    * ((p + 1 - K) * cbz ((K : ℤ) + n) (p + n + (j : ℤ) + 1)
        + (p + 1) * cbz ((K : ℤ) + n) (p + n + (j : ℤ) + 2))

/-- **Per-`j` telescope step.**  `rgenF K n p j = rgenH K n p j − rgenH K n p (j+1)`. -/
theorem rgenF_eq_telescope (K n : ℕ) (p : ℤ) (j : ℕ) :
    rgenF K n p j = rgenH K n p j - rgenH K n p (j + 1) := by
  -- shorthand for the two binomials in the slot grading.
  set A : ℂ := cbz ((K : ℤ) + n) (p + n + (j : ℤ) + 1) with hA
  set B : ℂ := cbz ((K : ℤ) + n) (p + n + (j : ℤ) + 2) with hB
  set Cj : ℂ := cbz ((j : ℤ) + n) n with hCj
  set Cj1 : ℂ := cbz ((j : ℤ) + 1 + n) n with hCj1
  -- index absorption at top `(K+n : ℕ)`, lower index `r = p+n+j+2`:  B·r = A·((K+n) − r + 1).
  have habsB : B * (p + (n : ℤ) + (j : ℤ) + 2) = A * ((K : ℤ) + n - (p + n + (j : ℤ) + 2) + 1) := by
    have h := cbz_absorption (K + n) (p + n + (j : ℤ) + 2)
    rw [show (((K + n : ℕ)) : ℤ) = (K : ℤ) + n from by push_cast; ring,
        show (p + (n : ℤ) + (j : ℤ) + 2 - 1) = p + n + (j : ℤ) + 1 from by ring] at h
    rw [hA, hB]; push_cast at h ⊢; linear_combination h
  -- the C(j+n,n) shift:  (j+1)·C(j+1+n,n) = (j+1+n)·C(j+n,n).
  have hshift : ((j : ℂ) + 1) * Cj1 = ((j : ℤ) + 1 + n) * Cj := by
    have h := cbz_upper_shift (j + 1) n
    rw [show (((j + 1 : ℕ)) : ℤ) = (j : ℤ) + 1 from by push_cast; ring,
        show ((j : ℤ) + 1 + n - 1) = (j : ℤ) + n from by ring] at h
    rw [hCj, hCj1]; push_cast at h ⊢; linear_combination h
  -- expand both definitions; normalise the `(j+1)`-cast and the binomial indices to A, B, Cj, Cj1.
  rw [rgenF, rgenH, rgenH, ← hA, ← hB, ← hCj]
  rw [show (((j + 1 : ℕ)) : ℤ) = (j : ℤ) + 1 from by push_cast; ring,
      show (p + (n : ℤ) + ((j : ℤ) + 1) + 1) = p + n + (j : ℤ) + 2 from by ring, ← hB]
  rw [← hCj1, pow_succ]
  -- the A-coefficient identity:  (p+1-K)A = -B(p+n+j+2) − jA.
  have key : (p + 1 - (K : ℤ)) * A = -(B * (p + (n : ℤ) + (j : ℤ) + 2)) - (j : ℂ) * A := by
    rw [habsB]; push_cast; ring
  push_cast at key hshift ⊢
  -- close: the goal is a polynomial identity once `key` and `hshift` are substituted.
  linear_combination
    ((-1 : ℂ) ^ j * Cj) * key + ((-1 : ℂ) ^ j * B) * hshift

/-- `rgenH K n p 0 = 0` (the `j`-factor kills it). -/
theorem rgenH_zero (K n : ℕ) (p : ℤ) : rgenH K n p 0 = 0 := by
  simp [rgenH]

/-- `rgenH K n p (n+1) = -(rgenW0 n)·C(K+n, p+2n+2)` (the closed-form endpoint of the telescope).
Uses `(n+1)·C(2n+1,n) = (2n+1)·C(2n,n)`. -/
theorem rgenH_succ (K n : ℕ) (p : ℤ) :
    rgenH K n p (n + 1) = -(rgenW0 n) * cbz ((K : ℤ) + n) (p + 2 * n + 2) := by
  -- (n+1)·C(2n+1,n) = (2n+1)·C(2n,n)  via cbz_upper_shift, in `Nat.choose` form.
  have hchoose : ((n : ℂ) + 1) * (Nat.choose (2 * n + 1) n : ℂ)
      = (2 * (n : ℂ) + 1) * (Nat.choose (2 * n) n : ℂ) := by
    have h := cbz_upper_shift (n + 1) n
    -- C(n+1+n, n) = C(2n+1,n);  C(n+n,n) = C(2n,n)
    rw [show (((n + 1 : ℕ)) : ℤ) + n = (((2 * n + 1 : ℕ)) : ℤ) from by push_cast; ring,
        cbz_natCast_eq_choose (by omega : n ≤ 2 * n + 1),
        show ((((2 * n + 1 : ℕ)) : ℤ) - 1) = (((2 * n : ℕ)) : ℤ) from by push_cast; ring,
        cbz_natCast_eq_choose (by omega : n ≤ 2 * n)] at h
    push_cast at h ⊢
    linear_combination h
  rw [rgenH, rgenW0]
  rw [show (((n + 1 : ℕ)) : ℤ) + n = (((2 * n + 1 : ℕ)) : ℤ) from by push_cast; ring,
      cbz_natCast_eq_choose (by omega : n ≤ 2 * n + 1),
      show (p + (n : ℤ) + (((n + 1 : ℕ)) : ℤ) + 1) = p + 2 * n + 2 from by push_cast; ring]
  push_cast
  linear_combination
    (-((-1 : ℂ) ^ (n + 1)) * cbz ((K : ℤ) + n) (p + 2 * n + 2)) * hchoose

/-- **The per-mode coefficient collapse.**  For every mode value `p`,
`∑_{j≤n} rgenF K n p j = rgenW0 n · C(K+n, p+2n+2)` — the residual coefficient equals a single
circle-product coefficient (all higher towers vanish).  Telescoping
`rgenF j = rgenH j − rgenH (j+1)`, `rgenH 0 = 0`, `rgenH (n+1) = -(rgenW0)·C`. -/
theorem rgenF_sum (K n : ℕ) (p : ℤ) :
    (∑ j ∈ Finset.range (n + 1), rgenF K n p j)
      = rgenW0 n * cbz ((K : ℤ) + n) (p + 2 * n + 2) := by
  rw [Finset.sum_congr rfl fun j _ => rgenF_eq_telescope K n p j,
      Finset.sum_range_sub' (fun j => rgenH K n p j) (n + 1),
      rgenH_zero, rgenH_succ]
  ring

/-! ## The vector-level finsum collapse `RgenRest = w₀ • circ`. -/

open ZhuHR in
/-- `circ W n a c` for `a ∈ 𝒱_K` (`K : ℕ`) in the mode-value finsum form
`∑ᶠ p, C(K+n, p+2n+2) • a₍p₎c`. -/
theorem circ_homog_finsum (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K : ℕ} {a : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (c : 𝒱) :
    circ W n a c = ∑ᶠ p : ℤ, cbz ((K : ℤ) + n) (p + 2 * n + 2) • W.smul a p c := by
  rw [circ_homogeneous W n ha c,
    show (((K : ℤ) + (n : ℤ)).toNat + 1) = K + n + 1 from by
      rw [show ((K : ℤ) + (n : ℤ)) = ((K + n : ℕ) : ℤ) from by push_cast; ring, Int.toNat_natCast]]
  rw [show (∑ i ∈ Finset.range (K + n + 1),
            cbz ((K : ℤ) + (n : ℤ)) i • W.smul a ((i : ℤ) - 2 * (n : ℤ) - 2) c)
        = ∑ i ∈ Finset.range (K + n + 1),
            cbz ((K : ℤ) + (n : ℤ)) i • W.smul a ((i : ℤ) + (-(2 * (n : ℤ)) - 2)) c from
      Finset.sum_congr rfl fun i _ => by
        rw [show (i : ℤ) - 2 * (n : ℤ) - 2 = (i : ℤ) + (-(2 * (n : ℤ)) - 2) from by ring]]
  rw [ZhuHR.rangeSmul_eq_finsumZ (fun q : ℤ => cbz ((K : ℤ) + n) q) (fun q => W.smul a q c)
      (-(2 * (n : ℤ)) - 2)
      (fun q hq => cbz_apply_neg _ hq)
      (fun q hq => cbz_lt (by positivity) (by push_cast at hq ⊢; omega))]
  rw [← finsum_comp_equiv (Equiv.addRight (-(2 * (n : ℤ)) - 2))
      (f := fun p : ℤ => cbz ((K : ℤ) + n) (p + 2 * n + 2) • W.smul a p c)]
  refine finsum_congr fun q => ?_
  simp only [Equiv.coe_addRight]
  rw [show (q + (-(2 * (n : ℤ)) - 2)) + 2 * n + 2 = q from by ring]

/-- Finite support of `p ↦ C(K+n, p+e) • a₍p₎c`, for any shift `e`. -/
theorem cbzKn_shift_support_fin (W : VertexOperatorAlgebra 𝒱) (K n : ℕ) (a c : 𝒱) (e : ℤ) :
    Function.HasFiniteSupport (fun p : ℤ => cbz ((K : ℤ) + n) (p + e) • W.smul a p c) :=
  ZhuHR.smul_support_of_scalar W a c _
    (ZhuHR.cbz_shift_support_fin (d := (K : ℤ) + n) (by positivity) e)

/-- Finite support of the term-1 bracket scalar `p ↦ (p+1-K)·C(K+n,p+n+j+1) • a₍p₎c`. -/
theorem cbzKn_shift_support_fin' (W : VertexOperatorAlgebra 𝒱) (K n : ℕ) (a c : 𝒱) (j : ℤ) :
    Function.HasFiniteSupport
      (fun p : ℤ => ((p + 1 - K) * cbz ((K : ℤ) + n) (p + n + j + 1)) • W.smul a p c) := by
  refine ZhuHR.smul_support_of_scalar W a c _
    (Set.Finite.subset (ZhuHR.cbz_shift_support_fin (d := (K : ℤ) + n) (by positivity) (n + j + 1))
      (fun p hp => ?_))
  rw [Function.mem_support] at hp ⊢
  intro h; apply hp
  rw [show p + (n : ℤ) + j + 1 = p + ((n : ℤ) + j + 1) from by ring, h, mul_zero]

/-- Finite support of the term-2 bracket scalar `p ↦ (p+1)·C(K+n,p+n+j+2) • a₍p₎c`. -/
theorem cbzKn_shift_support_fin'' (W : VertexOperatorAlgebra 𝒱) (K n : ℕ) (a c : 𝒱) (j : ℤ) :
    Function.HasFiniteSupport
      (fun p : ℤ => ((p + 1) * cbz ((K : ℤ) + n) (p + n + j + 2)) • W.smul a p c) := by
  refine ZhuHR.smul_support_of_scalar W a c _
    (Set.Finite.subset (ZhuHR.cbz_shift_support_fin (d := (K : ℤ) + n) (by positivity) (n + j + 2))
      (fun p hp => ?_))
  rw [Function.mem_support] at hp ⊢
  intro h; apply hp
  rw [show p + (n : ℤ) + j + 2 = p + ((n : ℤ) + j + 2) from by ring, h, mul_zero]

/-- **Per-`j` block of `RgenRest`, in mode-value finsum form.**  For `a ∈ 𝒱_K` (`K : ℕ`), the inner
`i`-sum of `RgenRest`'s `j`-block collapses to `∑ᶠ p, (rgenF-bracket) • a₍p₎c`. -/
theorem RgenRest_block_finsum (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K : ℕ} {a : 𝒱}
    (_ha : a ∈ W.grading (K : ℤ)) (c : 𝒱) (j : ℕ) :
    (∑ i ∈ Finset.range ((K : ℤ) + (n : ℤ)).toNat.succ,
        cbz ((K : ℤ) + (n : ℤ)) i •
          ((((i : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) + 1 - K) •
              W.smul a ((i : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) c
            + (((i : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) : ℂ) •
              W.smul a ((i : ℤ) - ((n : ℤ) + (j : ℤ) + 1) - 1) c))
      = ∑ᶠ p : ℤ,
          ((p + 1 - K) * cbz ((K : ℤ) + n) (p + n + (j : ℤ) + 1)
              + (p + 1) * cbz ((K : ℤ) + n) (p + n + (j : ℤ) + 2)) • W.smul a p c := by
  -- normalise the range and the zsmul `(m+1-K)` to a ℂ-smul.
  rw [show (((K : ℤ) + (n : ℤ)).toNat.succ) = K + n + 1 from by
        rw [show ((K : ℤ) + (n : ℤ)) = ((K + n : ℕ) : ℤ) from by push_cast; ring,
          Int.toNat_natCast]]
  -- split into the two single-mode residues.
  rw [show (∑ i ∈ Finset.range (K + n + 1),
            cbz ((K : ℤ) + (n : ℤ)) i •
              ((((i : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) + 1 - K) •
                  W.smul a ((i : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) c
                + (((i : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) : ℂ) •
                  W.smul a ((i : ℤ) - ((n : ℤ) + (j : ℤ) + 1) - 1) c))
        = (∑ i ∈ Finset.range (K + n + 1),
            ((((i : ℤ) - ((n : ℤ) + (j : ℤ) + 1) + 1 - K : ℤ) : ℂ) * cbz ((K : ℤ) + n) i)
              • W.smul a ((i : ℤ) + (-((n : ℤ) + (j : ℤ) + 1))) c)
          + (∑ i ∈ Finset.range (K + n + 1),
            ((((i : ℤ) - ((n : ℤ) + (j : ℤ) + 1) : ℤ) : ℂ) * cbz ((K : ℤ) + n) i)
              • W.smul a ((i : ℤ) + (-((n : ℤ) + (j : ℤ) + 1) - 1)) c) from by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_add]
      congr 1
      · rw [← Int.cast_smul_eq_zsmul ℂ ((i : ℤ) - ((n : ℤ) + (j : ℤ) + 1) + 1 - K),
          smul_smul, mul_comm,
          show (i : ℤ) + (-((n : ℤ) + (j : ℤ) + 1))
            = (i : ℤ) - ((n : ℤ) + (j : ℤ) + 1) from by ring]
      · rw [smul_smul, mul_comm,
          show (i : ℤ) + (-((n : ℤ) + (j : ℤ) + 1) - 1)
            = (i : ℤ) - ((n : ℤ) + (j : ℤ) + 1) - 1 from by ring]
        push_cast; ring_nf]
  -- reindex each finite range to a `∑ᶠ p`.
  rw [ZhuHR.rangeSmul_eq_finsumZ
      (fun q : ℤ => ((q - ((n : ℤ) + (j : ℤ) + 1) + 1 - K : ℤ) : ℂ) * cbz ((K : ℤ) + n) q)
      (fun q => W.smul a q c) (-((n : ℤ) + (j : ℤ) + 1))
      (fun q hq => by simp only; rw [cbz_apply_neg _ hq, mul_zero])
      (fun q hq => by
        simp only; rw [cbz_lt (by positivity) (by push_cast at hq ⊢; omega), mul_zero])]
  rw [ZhuHR.rangeSmul_eq_finsumZ
      (fun q : ℤ => ((q - ((n : ℤ) + (j : ℤ) + 1) : ℤ) : ℂ) * cbz ((K : ℤ) + n) q)
      (fun q => W.smul a q c) (-((n : ℤ) + (j : ℤ) + 1) - 1)
      (fun q hq => by simp only; rw [cbz_apply_neg _ hq, mul_zero])
      (fun q hq => by
        simp only; rw [cbz_lt (by positivity) (by push_cast at hq ⊢; omega), mul_zero])]
  -- split the RHS combined finsum into the two single-bracket finsums.
  rw [show (∑ᶠ p : ℤ,
        ((p + 1 - K) * cbz ((K : ℤ) + n) (p + n + (j : ℤ) + 1)
            + (p + 1) * cbz ((K : ℤ) + n) (p + n + (j : ℤ) + 2)) • W.smul a p c)
      = (∑ᶠ p : ℤ, ((p + 1 - K) * cbz ((K : ℤ) + n) (p + n + (j : ℤ) + 1)) • W.smul a p c)
        + (∑ᶠ p : ℤ, ((p + 1) * cbz ((K : ℤ) + n) (p + n + (j : ℤ) + 2)) • W.smul a p c) from by
      rw [← finsum_add_distrib (cbzKn_shift_support_fin' W K n a c (j : ℤ))
        (cbzKn_shift_support_fin'' W K n a c (j : ℤ))]
      refine finsum_congr fun p => ?_
      rw [add_smul]]
  -- shift each RHS finsum index so both sides are `∑ᶠ q, _ • a₍q+d₎c`.
  rw [← finsum_comp_equiv (Equiv.addRight (-((n : ℤ) + (j : ℤ) + 1)))
      (f := fun p : ℤ => ((p + 1 - K) * cbz ((K : ℤ) + n) (p + n + (j : ℤ) + 1)) • W.smul a p c),
    ← finsum_comp_equiv (Equiv.addRight (-((n : ℤ) + (j : ℤ) + 1) - 1))
      (f := fun p : ℤ => ((p + 1) * cbz ((K : ℤ) + n) (p + n + (j : ℤ) + 2)) • W.smul a p c)]
  congr 1
  · refine finsum_congr fun q => ?_
    simp only [Equiv.coe_addRight]
    rw [show (q + -((n : ℤ) + (j : ℤ) + 1)) + n + (j : ℤ) + 1 = q from by ring]
    congr 1
    push_cast; ring
  · refine finsum_congr fun q => ?_
    simp only [Equiv.coe_addRight]
    rw [show (q + (-((n : ℤ) + (j : ℤ) + 1) - 1)) + n + (j : ℤ) + 2 = q from by ring]
    congr 1
    push_cast; ring

/-! ## `RgenRest = w₀ • circ`, the membership `RgenRest ∈ Oₙ`, and `hRgen`. -/

/-- Finite support of `p ↦ rgenF K n p j • a₍p₎c` (for fixed `j`). -/
theorem rgenF_support_fin (W : VertexOperatorAlgebra 𝒱) (n K : ℕ) (a c : 𝒱) (j : ℕ) :
    Function.HasFiniteSupport (fun p : ℤ => (rgenF K n p j) • W.smul a p c) := by
  refine ZhuHR.smul_support_of_scalar W a c _ (Set.Finite.subset
    ((ZhuHR.cbz_shift_support_fin (d := (K : ℤ) + n) (by positivity) ((n : ℤ) + j + 1)).union
      (ZhuHR.cbz_shift_support_fin (d := (K : ℤ) + n) (by positivity) ((n : ℤ) + j + 2)))
    (fun p hp => ?_))
  rw [Function.mem_support] at hp
  rw [Set.mem_union, Function.mem_support, Function.mem_support]
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨h1, h2⟩ := hcon
  apply hp
  rw [rgenF, show p + (n : ℤ) + (j : ℤ) + 1 = p + ((n : ℤ) + (j : ℤ) + 1) from by ring,
      show p + (n : ℤ) + (j : ℤ) + 2 = p + ((n : ℤ) + (j : ℤ) + 2) from by ring, h1, h2]
  ring

/-- **`RgenRest = w₀(n) • circ W n a c`** for homogeneous `a ∈ 𝒱_K` (`K : ℕ`).  Each `RgenRest`
`j`-block collapses (via `RgenRest_block_finsum`) to a mode-value finsum; pulling the FZ scalar
`(-1)^j C(j+n,n)` in and swapping the finite `j`-sum past the finsum gives
`∑ᶠ p, (∑_j rgenF) • a₍p₎c`, which by `rgenF_sum` equals
`∑ᶠ p, w₀·C(K+n,p+2n+2) • a₍p₎c = w₀•circ`. -/
theorem RgenRest_eq_w0_circ (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K : ℕ} {a : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (c : 𝒱) :
    RgenRest W n K a c = rgenW0 n • circ W n a c := by
  rw [RgenRest]
  -- rewrite each `j`-block by `RgenRest_block_finsum`, then pull the FZ scalar into the finsum.
  rw [show (∑ j ∈ Finset.range (n + 1),
            ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) •
              ∑ i ∈ Finset.range ((K + (n : ℤ)).toNat + 1),
                cbz (K + (n : ℤ)) i •
                  ((((i : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) + 1 - K) •
                      W.smul a ((i : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) c
                    + (((i : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) : ℂ) •
                      W.smul a ((i : ℤ) - ((n : ℤ) + (j : ℤ) + 1) - 1) c))
        = ∑ j ∈ Finset.range (n + 1),
            ∑ᶠ p : ℤ, (rgenF K n p j) • W.smul a p c from
      Finset.sum_congr rfl fun j _ => by
        rw [RgenRest_block_finsum W n ha c j]
        have hfin : Function.HasFiniteSupport
            (fun p : ℤ =>
              ((p + 1 - K) * cbz ((K : ℤ) + n) (p + n + (j : ℤ) + 1)
                + (p + 1) * cbz ((K : ℤ) + n) (p + n + (j : ℤ) + 2)) • W.smul a p c) := by
          rw [show (fun p : ℤ =>
                ((p + 1 - K) * cbz ((K : ℤ) + n) (p + n + (j : ℤ) + 1)
                  + (p + 1) * cbz ((K : ℤ) + n) (p + n + (j : ℤ) + 2)) • W.smul a p c)
              = (fun p : ℤ =>
                    ((p + 1 - K) * cbz ((K : ℤ) + n) (p + n + (j : ℤ) + 1)) • W.smul a p c)
                + (fun p : ℤ => ((p + 1) * cbz ((K : ℤ) + n) (p + n + (j : ℤ) + 2)) • W.smul a p c)
              from by funext p; simp only [Pi.add_apply]; rw [add_smul]]
          exact (cbzKn_shift_support_fin' W K n a c (j : ℤ)).add
            (cbzKn_shift_support_fin'' W K n a c (j : ℤ))
        rw [smul_finsum' ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) hfin]
        refine finsum_congr fun p => ?_
        rw [smul_smul, rgenF]]
  -- swap the finite `j`-sum past the finsum, assemble `∑_j (...) = (∑_j rgenF)`.
  rw [show (∑ j ∈ Finset.range (n + 1),
            ∑ᶠ p : ℤ, (rgenF K n p j) • W.smul a p c)
        = ∑ᶠ p : ℤ, (∑ j ∈ Finset.range (n + 1), rgenF K n p j) • W.smul a p c from by
      rw [← finsum_sum_comm (Finset.range (n + 1))
          (fun p j => (rgenF K n p j) • W.smul a p c)
          (fun j _ => rgenF_support_fin W n K a c j)]
      refine finsum_congr fun p => ?_
      rw [← Finset.sum_smul]]
  -- apply the per-mode scalar collapse and recognise `w₀ • circ`.
  rw [show (∑ᶠ p : ℤ, (∑ j ∈ Finset.range (n + 1), rgenF K n p j) • W.smul a p c)
        = ∑ᶠ p : ℤ, (rgenW0 n * cbz ((K : ℤ) + n) (p + 2 * n + 2)) • W.smul a p c from
      finsum_congr fun p => by rw [rgenF_sum]]
  rw [circ_homog_finsum W n ha c]
  rw [show (∑ᶠ p : ℤ, cbz ((K : ℤ) + n) (p + 2 * n + 2) • W.smul a p c)
        = ∑ᶠ p : ℤ, cbz ((K : ℤ) + n) (p + (2 * (n : ℤ) + 2)) • W.smul a p c from
      finsum_congr fun p => by rw [show p + 2 * (n : ℤ) + 2 = p + (2 * (n : ℤ) + 2) from by ring]]
  rw [smul_finsum' (rgenW0 n) (cbzKn_shift_support_fin W K n a c (2 * (n : ℤ) + 2))]
  refine finsum_congr fun p => ?_
  rw [smul_smul, show p + 2 * (n : ℤ) + 2 = p + (2 * (n : ℤ) + 2) from by ring]

/-- `RgenRest W n K 0 c = 0` (left-linearity of every mode in the `a`-slot). -/
theorem RgenRest_zero_left (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (K : ℤ) (c : 𝒱) :
    RgenRest W n K 0 c = 0 := by
  rw [RgenRest]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [show (∑ i ∈ Finset.range ((K + (n : ℤ)).toNat + 1),
            cbz (K + (n : ℤ)) i •
              ((((i : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) + 1 - K) •
                  W.smul 0 ((i : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) c
                + (((i : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) : ℂ) •
                  W.smul 0 ((i : ℤ) - ((n : ℤ) + (j : ℤ) + 1) - 1) c))
        = 0 from ?_, smul_zero]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [PreVertexAlgebra.smul_zero_left, PreVertexAlgebra.smul_zero_left, smul_zero, smul_zero, add_zero,
    smul_zero]

/-! ## The closed core `RgenRest ∈ Oₙ` and the full field `hRgen`. -/

/-- **`RgenRest W n K a c ∈ Oₙ`** for homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M` (`K M : ℤ`).  For `K ≥ 0`
this is `RgenRest = w₀·circ ∈ Oₙ` (`RgenRest_eq_w0_circ` + `circ_mem_On`); for `K < 0`, `a = 0`
(`positivity`), so `RgenRest = 0`. -/
theorem RgenRest_mem (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (K M : ℤ) {a c : 𝒱}
    (ha : a ∈ W.grading K) (_hc : c ∈ W.grading M) :
    RgenRest W n K a c ∈ On W n := by
  rcases lt_or_ge K 0 with hK | hK
  · rw [W.positivity K hK, Submodule.mem_bot] at ha
    rw [ha, RgenRest_zero_left]
    exact (On W n).zero_mem
  · obtain ⟨K', rfl⟩ : ∃ K' : ℕ, K = (K' : ℤ) := ⟨K.toNat, by omega⟩
    rw [RgenRest_eq_w0_circ W n ha c]
    exact Submodule.smul_mem _ _ (circ_mem_On W n a c)

/-- **`hRgen` closed.**  The full right-slot `OnL` membership field
`∀ a c, leftProd W n a ((L₋₁+L₀)c) ∈ OnFull W n`, assembled from the proven core `RgenRest_mem`
through the `ZhuVermaAnArchRgenClose` reduction `hRgen_closed_of_rest`. -/
theorem hRgen_closed (W : VertexOperatorAlgebra 𝒱) (n : ℕ) :
    ∀ a c : 𝒱, leftProd W n a (W.L (-1) c + W.L 0 c) ∈ OnFull W n :=
  hRgen_closed_of_rest W n (fun K M _ _ ha hc => RgenRest_mem W n K M ha hc)

end VOA
