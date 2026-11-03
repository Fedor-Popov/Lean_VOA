/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnDescent2

/-!
# The single remaining combinatorial certificate `gen_jsum`

This file extends `Modules.ZhuVermaAnDescent2` (the depth-`n` generalized Vandermonde
`gen_vandermonde`) by proving the **single combinatorial target** flagged at the end of that file:
the Frenkel–Zhu depth-`n` `j`-sum `J(t,μ)` collapses onto the `ν`-weighted `Pres_mem_On`-tower
family.

## The descent coefficient `ν(n,t,e)` (closed form, found via the local Mathematica kernel)

The `₃F₂`-type weights are a single hypergeometric term with no elementary product form:

  `ν(n,t,e) = (-1)^e · C(2n+1+t,n) · C(n+t,n) · C(n,e) · (n+t+1)/(n+t+e+1)`.

(`ν(n,t,0)=C(2n+1+t,n)C(n+t,n)`, `ν(n,0,n)=(-1)^n C(2n,n)`; `ν(2,0,·)={10,-15,6}`.)
The closed form was determined by the consecutive-ratio recurrence
`ν(n,t,e+1)/ν(n,t,e) = -(n-e)(n+1+t+e)/((e+1)(n+t+e+2))`.

## The certificate: NO Zeilberger needed — three classical pieces

Numerically (Mathematica) the depth-`n` `j`-sum equals the `ν`-tower combination *as an identity of
`cbz`-coefficients in two arbitrary integers* `X` (= `Ws+2n+1+t`) and `Y` (= `μ+3n+3+t`):

  `∑_{j=0}^n (-1)^j C(j+n,n) C(n+j+t,t) C(X, Y+j) = ∑_{e=0}^n ν(n,t,e) C(X+e, Y+e)`.   (`gen_jsum_XY`)

This factors cleanly into elementary, fully-formalizable steps — the WZ machinery is unnecessary:

* **`cbz_diag_vandermonde`** — the *diagonal Vandermonde* `C(X+e,Y+e) = ∑_{j=0}^e C(e,j) C(X,Y+j)`
  (off `cbz_mul_vandermonde`).  Expanding each RHS tower and swapping the triangular sum reduces
  `gen_jsum_XY` to matching, for each `j`, the coefficient of `C(X,Y+j)`:
* **`gen_jsum_scalar`** — `(-1)^j C(j+n,n) C(n+j+t,t) = ∑_{e=j}^n ν(n,t,e) C(e,j)`.
  Via `C(n,e)C(e,j)=C(n,j)C(n-j,e-j)` (`Nat.choose_mul`) and `e=j+f` this collapses through:
* **`alt_beta_sum`** — the classic alternating Beta-integral sum
  `∑_{f=0}^m (-1)^f C(m,f)/(c+f) = m!/∏_{f=0}^m (c+f)` (`c : ℕ`, `c≥1`), proved by induction on `m`
  via the recurrence `S(m,c) = S(m-1,c) - S(m-1,c+1)` (`alt_beta_rec`), leaving the pure-ℕ factorial
  identity **`gen_jsum_natid`**.

## Status

* `alt_beta_rec`, `alt_beta_sum`, `gen_jsum_natid`, `gen_jsum_scalar`, `cbz_diag_vandermonde`,
   `gen_jsum_XY`, `gen_jsum`, `gen_jsum_zero` — all proved, axiom-clean
   (`[propext, Classical.choice, Quot.sound]`).

**Not proved here.** Discharging the four circle-generator memberships (`LeftDescends`/`RightDescends`) from `gen_jsum`
   + `Pres_mem_On` is the depth-`n` analog of the `n=0` two-sided-ideal bookkeeping of
   `Modules.ZhuRightIdeal` (`mode_split`/`mode_commutator_uniform`/`inner_reindex` residue
   accounting); precise statement recorded at the file end.  `gen_jsum` is the combinatorial core
   of that step (the `S_mem_O`-analog), so the remaining work is VOA-level residue bookkeeping, not
   combinatorics.

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

/-! ## The alternating Beta-integral sum `∑_f (-1)^f C(m,f)/(c+f) = m!/∏(c+f)`. -/

/-- **The Beta-sum recurrence** `S(k+1,c) = S(k,c) - S(k,c+1)` (from Pascal
`C(k+1,f)=C(k,f)+C(k,f-1)` + the index shift `f ↦ f+1`). -/
theorem alt_beta_rec (k c : ℕ) :
    (∑ f ∈ Finset.range (k+2), (-1:ℂ)^f * ((k+1).choose f : ℂ) / ((c : ℂ) + (f:ℂ)))
      = (∑ f ∈ Finset.range (k+1), (-1:ℂ)^f * (k.choose f : ℂ) / ((c : ℂ) + (f:ℂ)))
        - (∑ f ∈ Finset.range (k+1), (-1:ℂ)^f * (k.choose f : ℂ) / (((c:ℂ)+1) + (f:ℂ))) := by
  rw [Finset.sum_range_succ' (fun f => (-1:ℂ)^f * (k.choose f : ℂ) / ((c : ℂ) + (f:ℂ))) k,
      Finset.sum_range_succ' (fun f => (-1:ℂ)^f * (k.choose f : ℂ) / (((c:ℂ)+1) + (f:ℂ))) k]
  rw [Finset.sum_range_succ' (fun f => (-1:ℂ)^f * ((k+1).choose f : ℂ) / ((c : ℂ) + (f:ℂ))) (k+1)]
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, Nat.cast_zero, add_zero, mul_one]
  have hLHS : ∀ g ∈ Finset.range (k+1),
      (-1:ℂ)^(g+1) * ((k+1).choose (g+1) : ℂ) / ((c : ℂ) + ((g:ℕ)+1 : ℕ))
        = (-1:ℂ)^(g+1) * (k.choose g : ℂ) / ((c : ℂ) + ((g:ℕ)+1 : ℕ))
          + (-1:ℂ)^(g+1) * (k.choose (g+1) : ℂ) / ((c : ℂ) + ((g:ℕ)+1 : ℕ)) := by
    intro g _; rw [Nat.choose_succ_succ k g]; push_cast; ring
  rw [Finset.sum_congr rfl hLHS, Finset.sum_add_distrib]
  have hB : (∑ x ∈ Finset.range (k+1), (-1:ℂ)^(x+1) * (k.choose (x+1) : ℂ) / ((c : ℂ) + ((x:ℕ)+1 : ℕ)))
      = ∑ k_1 ∈ Finset.range k, (-1:ℂ)^(k_1+1) * (k.choose (k_1+1) : ℂ) / ((c : ℂ) + ((k_1:ℕ)+1 : ℕ)) := by
    rw [Finset.sum_range_succ, show k.choose (k+1) = 0 from Nat.choose_eq_zero_of_lt (by omega)]; simp
  have hA : (∑ x ∈ Finset.range (k+1), (-1:ℂ)^(x+1) * (k.choose x : ℂ) / ((c : ℂ) + ((x:ℕ)+1 : ℕ)))
      = - (∑ k_1 ∈ Finset.range k, (-1:ℂ)^(k_1+1) * (k.choose (k_1+1) : ℂ) / (((c:ℂ)+1) + ((k_1:ℕ)+1 : ℕ)))
        - 1/((c:ℂ)+1) := by
    rw [Finset.sum_range_succ' (fun x => (-1:ℂ)^(x+1) * (k.choose x : ℂ) / ((c : ℂ) + ((x:ℕ)+1 : ℕ))) k]
    rw [show (-(∑ k_1 ∈ Finset.range k, (-1:ℂ)^(k_1+1) * (k.choose (k_1+1) : ℂ) / (((c:ℂ)+1) + ((k_1:ℕ)+1 : ℕ))))
          = (∑ k_1 ∈ Finset.range k, -((-1:ℂ)^(k_1+1) * (k.choose (k_1+1) : ℂ) / (((c:ℂ)+1) + ((k_1:ℕ)+1 : ℕ)))) from by
        rw [Finset.sum_neg_distrib]]
    rw [show (∑ x ∈ Finset.range k, (-1:ℂ)^(x+1+1) * (k.choose (x+1) : ℂ) / ((c : ℂ) + ((x:ℕ)+1+1 : ℕ)))
          = (∑ k_1 ∈ Finset.range k, -((-1:ℂ)^(k_1+1) * (k.choose (k_1+1) : ℂ) / (((c:ℂ)+1) + ((k_1:ℕ)+1 : ℕ)))) from
        Finset.sum_congr rfl fun x _ => by push_cast; ring]
    simp only [Nat.choose_zero_right, Nat.cast_one]; push_cast; ring
  rw [hB, hA]; ring

/-- **The alternating Beta-integral sum** (positive-natural base `c`): for `c ≥ 1`,
`∑_{f=0}^m (-1)^f C(m,f)/(c+f) = m!/∏_{f=0}^m (c+f)`.  Proved by induction on `m` via
`alt_beta_rec`. -/
theorem alt_beta_sum (m c : ℕ) (hc : 1 ≤ c) :
    ∑ f ∈ Finset.range (m+1), (-1:ℂ)^f * (m.choose f : ℂ) / ((c : ℂ) + (f:ℂ))
      = (m.factorial : ℂ) / ∏ f ∈ Finset.range (m+1), ((c : ℂ) + (f:ℂ)) := by
  induction m generalizing c with
  | zero => simp
  | succ k ih =>
    have ihc1 : ∑ f ∈ Finset.range (k+1), (-1:ℂ)^f * (k.choose f : ℂ) / (((c:ℂ)+1) + (f:ℂ))
        = (k.factorial : ℂ) / ∏ f ∈ Finset.range (k+1), (((c:ℂ)+1) + (f:ℂ)) := by
      have := ih (c+1) (by omega)
      rw [show ((c+1 : ℕ) : ℂ) = (c:ℂ)+1 from by push_cast; ring] at this
      exact this
    rw [alt_beta_rec k c, ih c hc, ihc1]
    have hposne : ∀ (f : ℕ), ((c:ℂ)+(f:ℂ)) ≠ 0 := by
      intro f
      rw [show ((c:ℂ)+(f:ℂ)) = ((c+f : ℕ) : ℂ) from by push_cast; ring]
      exact_mod_cast (by omega : 0 < c + f).ne'
    set P : ℂ := ∏ f ∈ Finset.range (k+1), ((c : ℂ) + (f:ℂ)) with hP
    have hPne : P ≠ 0 := by rw [hP]; exact Finset.prod_ne_zero_iff.mpr fun f _ => hposne f
    have hck1 : ((c:ℂ) + ((k:ℕ)+1 : ℕ)) ≠ 0 := by
      rw [show ((c:ℂ) + ((k:ℕ)+1 : ℕ)) = ((c + (k+1) : ℕ) : ℂ) from by push_cast; ring]
      exact_mod_cast (by omega : 0 < c + (k+1)).ne'
    have hcne : (c:ℂ) ≠ 0 := by exact_mod_cast (by omega : 0 < c).ne'
    have hQ : (∏ f ∈ Finset.range (k+1+1), ((c : ℂ) + (f:ℂ))) = P * ((c:ℂ) + ((k:ℕ)+1 : ℕ)) := by
      rw [Finset.prod_range_succ]
    have hPc1 : (∏ f ∈ Finset.range (k+1), (((c:ℂ)+1) + (f:ℂ)))
        = P * ((c:ℂ) + ((k:ℕ)+1 : ℕ)) / (c:ℂ) := by
      rw [eq_div_iff hcne, ← hQ, Finset.prod_range_succ' (fun f => (c:ℂ)+(f:ℂ)) (k+1)]
      rw [show (∏ f ∈ Finset.range (k+1), (((c:ℂ)+1) + (f:ℂ)))
            = (∏ f ∈ Finset.range (k+1), ((c:ℂ) + ((f:ℕ)+1 : ℕ))) from
          Finset.prod_congr rfl fun f _ => by push_cast; ring]
      push_cast; ring
    rw [hQ, hPc1, Nat.factorial_succ]
    have hck1' : (c:ℂ) + ((k:ℂ)+1) ≠ 0 := by
      rw [show (c:ℂ) + ((k:ℂ)+1) = ((c + (k+1) : ℕ) : ℂ) from by push_cast; ring]
      exact_mod_cast (by omega : 0 < c + (k+1)).ne'
    push_cast
    field_simp
    ring

/-! ## The pure-ℕ factorial identity underlying the final collapse. -/

/-- The pure-ℕ factorial identity (the scalar collapse after `alt_beta_sum`):
`C(j+n,n)·C(n+j+t,t)·(2n+t+1)! = C(2n+1+t,n)·C(n+t,n)·(n+t+1)·C(n,j)·(n-j)!·(n+t+j)!`.  Proved by
solving each `C(·,·)` into its factorial ratio (`Nat.choose_mul_factorial_mul_factorial`) and
clearing denominators. -/
theorem gen_jsum_natid (n t j : ℕ) (hj : j ≤ n) :
    Nat.choose (j+n) n * Nat.choose (n+j+t) t * (2*n+t+1).factorial
      = Nat.choose (2*n+1+t) n * Nat.choose (n+t) n * (n+t+1) * Nat.choose n j
          * (n-j).factorial * (n+t+j).factorial := by
  have goalC : (Nat.choose (j+n) n : ℂ) * (Nat.choose (n+j+t) t : ℂ) * ((2*n+t+1).factorial : ℂ)
      = (Nat.choose (2*n+1+t) n : ℂ) * (Nat.choose (n+t) n : ℂ) * ((n+t+1 :ℕ): ℂ) * (Nat.choose n j : ℂ)
          * ((n-j).factorial : ℂ) * ((n+t+j).factorial : ℂ) := by
    have F1 : (Nat.choose (j+n) n : ℂ) * (n.factorial : ℂ) * (j.factorial : ℂ) = ((j+n).factorial : ℂ) := by
      have := Nat.choose_mul_factorial_mul_factorial (by omega : n ≤ j+n)
      rw [show (j+n)-n = j from by omega] at this; exact_mod_cast this
    have F2 : (Nat.choose (n+j+t) t : ℂ) * (t.factorial : ℂ) * ((n+j).factorial : ℂ) = ((n+j+t).factorial : ℂ) := by
      have := Nat.choose_mul_factorial_mul_factorial (by omega : t ≤ n+j+t)
      rw [show (n+j+t)-t = n+j from by omega] at this; exact_mod_cast this
    have F3 : (Nat.choose (2*n+1+t) n : ℂ) * (n.factorial : ℂ) * ((n+1+t).factorial : ℂ) = ((2*n+1+t).factorial : ℂ) := by
      have := Nat.choose_mul_factorial_mul_factorial (by omega : n ≤ 2*n+1+t)
      rw [show (2*n+1+t)-n = n+1+t from by omega] at this; exact_mod_cast this
    have F4 : (Nat.choose (n+t) n : ℂ) * (n.factorial : ℂ) * (t.factorial : ℂ) = ((n+t).factorial : ℂ) := by
      have := Nat.choose_mul_factorial_mul_factorial (by omega : n ≤ n+t)
      rw [show (n+t)-n = t from by omega] at this; exact_mod_cast this
    have F5 : (Nat.choose n j : ℂ) * (j.factorial : ℂ) * ((n-j).factorial : ℂ) = (n.factorial : ℂ) := by
      have := Nat.choose_mul_factorial_mul_factorial hj; exact_mod_cast this
    rw [show (n+1+t).factorial = (n+t+1).factorial from by congr 1; ring] at F3
    have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have hj' : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have ht : (t.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have hnt1 : ((n+t+1).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have hntp : ((n+t).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have hntj : ((n+t+j).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have hnj : ((n+j).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have hntp1 : ((n+t+1:ℕ):ℂ) ≠ 0 := by exact_mod_cast (by omega : 0 < n+t+1).ne'
    have hnjf : (((n-j).factorial):ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have hsucc : ((n+t+1).factorial : ℂ) = ((n+t+1:ℕ):ℂ) * ((n+t).factorial : ℂ) := by
      rw [show n+t+1 = (n+t)+1 from rfl, Nat.factorial_succ]; push_cast; ring
    have hC1 : (Nat.choose (j+n) n : ℂ) = ((j+n).factorial : ℂ) / ((n.factorial : ℂ) * (j.factorial : ℂ)) := by
      rw [eq_div_iff (mul_ne_zero hn hj')]; linear_combination F1
    have hC2 : (Nat.choose (n+j+t) t : ℂ) = ((n+j+t).factorial : ℂ) / ((t.factorial : ℂ) * ((n+j).factorial : ℂ)) := by
      rw [eq_div_iff (mul_ne_zero ht hnj)]; linear_combination F2
    have hC3 : (Nat.choose (2*n+1+t) n : ℂ) = ((2*n+1+t).factorial : ℂ) / ((n.factorial : ℂ) * ((n+t+1).factorial : ℂ)) := by
      rw [eq_div_iff (mul_ne_zero hn hnt1)]; linear_combination F3
    have hC4 : (Nat.choose (n+t) n : ℂ) = ((n+t).factorial : ℂ) / ((n.factorial : ℂ) * (t.factorial : ℂ)) := by
      rw [eq_div_iff (mul_ne_zero hn ht)]; linear_combination F4
    have hC5 : (Nat.choose n j : ℂ) = (n.factorial : ℂ) / ((j.factorial : ℂ) * ((n-j).factorial : ℂ)) := by
      rw [eq_div_iff (mul_ne_zero hj' (by exact_mod_cast (Nat.factorial_pos _).ne'))]; linear_combination F5
    rw [hC1, hC2, hC3, hC4, hC5, hsucc]
    rw [show (j+n).factorial = (n+j).factorial from by rw [Nat.add_comm],
        show (n+j+t).factorial = (n+t+j).factorial from by congr 1; ring]
    field_simp [hntp1, hnjf]
    ring_nf
  exact_mod_cast goalC

/-! ## The descent coefficient `ν(n,t,e)` and the scalar coefficient identity. -/

/-- The `₃F₂`-type Frenkel–Zhu depth-`n` descent weight (closed form, no elementary product):
`ν(n,t,e) = (-1)^e C(2n+1+t,n) C(n+t,n) C(n,e) (n+t+1)/(n+t+e+1)`.  `ν(n,t,0)=C(2n+1+t,n)C(n+t,n)`,
`ν(n,0,n)=(-1)^n C(2n,n)`. -/
noncomputable def nu (n t e : ℕ) : ℂ :=
  (-1:ℂ)^e * (Nat.choose (2*n+1+t) n : ℂ) * (Nat.choose (n+t) n : ℂ) * (Nat.choose n e : ℂ)
    * ((n+t+1 : ℕ) : ℂ) / ((n+t+e+1 : ℕ) : ℂ)

/-- Restrict a `range (n+1)` sum to `[j,n]` when the summand vanishes below `j`, reindexing `e=j+f`. -/
theorem reindex_drop (n j : ℕ) (hj : j ≤ n) (g : ℕ → ℂ) (hz : ∀ e, e < j → g e = 0) :
    ∑ e ∈ Finset.range (n+1), g e = ∑ f ∈ Finset.range (n-j+1), g (j + f) := by
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive g (Nat.zero_le j) (by omega : j ≤ n+1)]
  rw [show ∑ e ∈ Finset.Ico 0 j, g e = 0 from Finset.sum_eq_zero (fun e he => hz e (by simp at he; omega))]
  rw [zero_add, Finset.sum_Ico_eq_sum_range]
  simp only [show n + 1 - j = n - j + 1 from by omega]

/-- **The scalar coefficient identity** underlying `gen_jsum`: for `j ≤ n`,
`(-1)^j C(j+n,n) C(n+j+t,t) = ∑_{e=0}^n ν(n,t,e) C(e,j)` (terms with `e<j` vanish since `C(e,j)=0`).
Proved by reindexing `e=j+f`, collapsing `C(n,j+f)C(j+f,j)=C(n,j)C(n-j,f)`, applying `alt_beta_sum`
(`m=n-j`, `c=n+t+j+1`), then `gen_jsum_natid`. -/
theorem gen_jsum_scalar (n t j : ℕ) (hj : j ≤ n) :
    (-1:ℂ)^j * (Nat.choose (j+n) n : ℂ) * (Nat.choose (n+j+t) t : ℂ)
      = ∑ e ∈ Finset.range (n+1), nu n t e * (Nat.choose e j : ℂ) := by
  rw [reindex_drop n j hj (fun e => nu n t e * (Nat.choose e j : ℂ))
      (fun e he => by simp only [Nat.choose_eq_zero_of_lt he, Nat.cast_zero, mul_zero])]
  have hrew : ∀ f ∈ Finset.range (n-j+1),
      nu n t (j+f) * (Nat.choose (j+f) j : ℂ)
        = ((-1:ℂ)^j * (Nat.choose (2*n+1+t) n : ℂ) * (Nat.choose (n+t) n : ℂ) * ((n+t+1 : ℕ):ℂ)
            * (Nat.choose n j : ℂ))
          * ((-1:ℂ)^f * (Nat.choose (n-j) f : ℂ) / (((n+t+j+1 : ℕ):ℂ) + (f:ℂ))) := by
    intro f _
    rw [nu]
    have hcm : (Nat.choose n (j+f) : ℂ) * (Nat.choose (j+f) j : ℂ)
        = (Nat.choose n j : ℂ) * (Nat.choose (n-j) f : ℂ) := by
      have : Nat.choose n (j+f) * Nat.choose (j+f) j = Nat.choose n j * Nat.choose (n-j) f := by
        rw [Nat.choose_mul (by omega : j ≤ j+f), show (j+f)-j = f from by omega]
      exact_mod_cast this
    have hcast : ((n+t+(j+f)+1 : ℕ) : ℂ) = ((n+t+j+1 : ℕ):ℂ) + (f:ℂ) := by push_cast; ring
    have hden : ((n+t+j+1 : ℕ):ℂ) + (f:ℂ) ≠ 0 := by
      rw [← hcast]; exact_mod_cast (by omega : 0 < n+t+(j+f)+1).ne'
    rw [hcast, pow_add]
    field_simp
    linear_combination ((Nat.choose (2*n+1+t) n : ℂ) * (Nat.choose (n+t) n : ℂ) * ((n+t+1:ℕ):ℂ)) * hcm
  rw [Finset.sum_congr rfl hrew, ← Finset.mul_sum,
      alt_beta_sum (n-j) (n+t+j+1) (by omega)]
  have hprod : (∏ f ∈ Finset.range (n-j+1), (((n+t+j+1:ℕ):ℂ) + (f:ℂ)))
      = ((2*n+t+1).factorial : ℂ) / ((n+t+j).factorial : ℂ) := by
    have hN : (∏ f ∈ Finset.range (n-j+1), ((n+t+j+1)+f)) = (n+t+j+1).ascFactorial (n-j+1) := by
      rw [Nat.ascFactorial_eq_prod_range]
    have hfac := Nat.factorial_mul_ascFactorial (n+t+j) (n-j+1)
    rw [show (n+t+j)+(n-j+1) = 2*n+t+1 from by omega] at hfac
    have hcastP : (∏ f ∈ Finset.range (n-j+1), (((n+t+j+1:ℕ):ℂ) + (f:ℂ)))
        = ((∏ f ∈ Finset.range (n-j+1), ((n+t+j+1)+f) : ℕ) : ℂ) := by
      rw [Nat.cast_prod]
      exact Finset.prod_congr rfl fun f _ => by push_cast; ring
    rw [hcastP, hN, eq_div_iff (by exact_mod_cast (Nat.factorial_pos (n+t+j)).ne')]
    rw [← Nat.cast_mul]
    congr 1
    rw [mul_comm]; exact hfac
  rw [hprod]
  have hnat := gen_jsum_natid n t j hj
  have hnatC : (Nat.choose (j+n) n : ℂ) * (Nat.choose (n+j+t) t : ℂ) * ((2*n+t+1).factorial : ℂ)
      = (Nat.choose (2*n+1+t) n : ℂ) * (Nat.choose (n+t) n : ℂ) * ((n+t+1:ℕ):ℂ) * (Nat.choose n j : ℂ)
          * ((n-j).factorial : ℂ) * ((n+t+j).factorial : ℂ) := by exact_mod_cast hnat
  have hfacne : ((2*n+t+1).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hfacne2 : ((n+t+j).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  field_simp
  linear_combination hnatC

/-! ## The diagonal Vandermonde and the assembled certificate `gen_jsum`. -/

/-- **Diagonal Vandermonde** `C(X+e, Y+e) = ∑_{j=0}^e C(e,j)·C(X, Y+j)` (all `X Y : ℤ`, `e : ℕ`),
off `cbz_mul_vandermonde` + the support reflection `i ↦ e-i` (`Nat.choose_symm`). -/
theorem cbz_diag_vandermonde (X Y : ℤ) (e : ℕ) :
    cbz (X + (e:ℤ)) (Y + (e:ℤ))
      = ∑ j ∈ Finset.range (e+1), (Nat.choose e j : ℂ) * cbz X (Y + (j:ℤ)) := by
  have hvm := cbz_mul_vandermonde (e:ℤ) X (Y + (e:ℤ))
  rw [show ((e:ℤ) + X) = (X + (e:ℤ)) from by ring] at hvm
  rw [← hvm]
  rw [finsumZ_eq_range_sum (fun p => cbz (e:ℤ) p * cbz X ((Y + (e:ℤ)) - p)) (N := e+1)
      (fun p hp => by dsimp only; rw [cbz_apply_neg (e:ℤ) hp, zero_mul])
      (fun p hp => by dsimp only; rw [cbz_lt (by positivity) (by push_cast at hp; omega), zero_mul])]
  rw [← Finset.sum_range_reflect (fun i => cbz (e:ℤ) (i:ℤ) * cbz X ((Y + (e:ℤ)) - (i:ℤ))) (e+1)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hje : j ≤ e := by have := Finset.mem_range.mp hj; omega
  rw [show e + 1 - 1 - j = e - j from by omega]
  rw [show cbz (e:ℤ) ((e - j : ℕ):ℤ) = (Nat.choose e (e-j) : ℂ) from by
        rw [cbz_natCast_eq_choose (by omega : e - j ≤ e)]]
  rw [Nat.choose_symm hje]
  congr 1
  rw [show ((Y + (e:ℤ)) - ((e - j : ℕ):ℤ)) = (Y + (j:ℤ)) from by
    rw [Nat.cast_sub hje]; push_cast; ring]

/-- Triangular sum swap `∑_{e≤n}∑_{j≤e} = ∑_{j≤n}∑_{e∈[j,n]}`. -/
theorem tri_swap (n : ℕ) (f : ℕ → ℕ → ℂ) :
    ∑ e ∈ Finset.range (n+1), ∑ j ∈ Finset.range (e+1), f e j
      = ∑ j ∈ Finset.range (n+1), ∑ e ∈ Finset.Ico j (n+1), f e j := by
  apply Finset.sum_comm'; intro e j; simp only [Finset.mem_range, Finset.mem_Ico]; omega

/-- **`gen_jsum` (abstract `cbz`-coefficient form).** The Frenkel–Zhu depth-`n` `j`-sum collapses
onto the `ν`-weighted diagonal tower family, as an identity of `cbz`-coefficients in arbitrary
integers `X Y`:
`∑_{j=0}^n (-1)^j C(j+n,n) C(n+j+t,t) C(X, Y+j) = ∑_{e=0}^n ν(n,t,e)·C(X+e, Y+e)`.
Expand each RHS tower via `cbz_diag_vandermonde`, swap the triangle (`tri_swap`), and match the
coefficient of `C(X,Y+j)` via `gen_jsum_scalar`. -/
theorem gen_jsum_XY (n t : ℕ) (X Y : ℤ) :
    ∑ j ∈ Finset.range (n+1),
        ((-1:ℂ)^j * (Nat.choose (j+n) n : ℂ) * (Nat.choose (n+j+t) t : ℂ)) * cbz X (Y + (j:ℤ))
      = ∑ e ∈ Finset.range (n+1), nu n t e * cbz (X + (e:ℤ)) (Y + (e:ℤ)) := by
  rw [show (∑ e ∈ Finset.range (n+1), nu n t e * cbz (X + (e:ℤ)) (Y + (e:ℤ)))
        = ∑ e ∈ Finset.range (n+1), ∑ j ∈ Finset.range (e+1),
            (nu n t e * (Nat.choose e j : ℂ)) * cbz X (Y + (j:ℤ)) from
      Finset.sum_congr rfl fun e _ => by
        rw [cbz_diag_vandermonde X Y e, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring]
  rw [tri_swap n (fun e j => (nu n t e * (Nat.choose e j : ℂ)) * cbz X (Y + (j:ℤ)))]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
  rw [← Finset.sum_mul]
  congr 1
  rw [gen_jsum_scalar n t j hjn]
  rw [show Finset.range (n+1) = Finset.Ico 0 (n+1) from by rw [Finset.range_eq_Ico],
      ← Finset.sum_Ico_consecutive (fun e => nu n t e * (Nat.choose e j : ℂ))
        (Nat.zero_le j) (by omega : j ≤ n+1)]
  rw [show ∑ e ∈ Finset.Ico 0 j, nu n t e * (Nat.choose e j : ℂ) = 0 from
      Finset.sum_eq_zero fun e he => by
        rw [show e.choose j = 0 from Nat.choose_eq_zero_of_lt (by simp at he; omega),
          Nat.cast_zero, mul_zero]]
  rw [zero_add]

/-- **`gen_jsum` (keystone-facing form).** Specialize `gen_jsum_XY` to `X = Ws+2n+1+t`,
`Y = μ+3n+3+t`: the FZ depth-`n` commutator-family `j`-sum coefficient collapses onto the
`ν`-weighted `Pres_mem_On` towers `C(Ws+n+(n+1+t+e), μ+2n+2+(n+1+t+e))`. -/
theorem gen_jsum (n t : ℕ) (Ws μ : ℤ) :
    ∑ j ∈ Finset.range (n+1),
        ((-1:ℂ)^j * (Nat.choose (j+n) n : ℂ) * (Nat.choose (n+j+t) t : ℂ))
          * cbz (Ws + 2*n+1+t) (μ + 3*n+3+(j:ℤ)+t)
      = ∑ e ∈ Finset.range (n+1),
          nu n t e * cbz (Ws + (n:ℤ) + ((n:ℤ)+1+t+e)) (μ + 2*n+2+((n:ℤ)+1+t+e)) := by
  rw [show (∑ j ∈ Finset.range (n+1),
            ((-1:ℂ)^j * (Nat.choose (j+n) n : ℂ) * (Nat.choose (n+j+t) t : ℂ))
              * cbz (Ws + 2*n+1+t) (μ + 3*n+3+(j:ℤ)+t))
        = ∑ j ∈ Finset.range (n+1),
            ((-1:ℂ)^j * (Nat.choose (j+n) n : ℂ) * (Nat.choose (n+j+t) t : ℂ))
              * cbz ((Ws + 2*(n:ℤ)+1+t)) ((μ + 3*(n:ℤ)+3+t) + (j:ℤ)) from
      Finset.sum_congr rfl fun j _ => by congr 2 <;> push_cast <;> ring]
  rw [show (∑ e ∈ Finset.range (n+1),
            nu n t e * cbz (Ws + (n:ℤ) + ((n:ℤ)+1+t+e)) (μ + 2*n+2+((n:ℤ)+1+t+e)))
        = ∑ e ∈ Finset.range (n+1),
            nu n t e * cbz ((Ws + 2*(n:ℤ)+1+t) + (e:ℤ)) ((μ + 3*(n:ℤ)+3+t) + (e:ℤ)) from
      Finset.sum_congr rfl fun e _ => by congr 2 <;> push_cast <;> ring]
  exact gen_jsum_XY n t (Ws + 2*(n:ℤ)+1+t) (μ + 3*(n:ℤ)+3+t)

/-- `ν(0,t,0) = 1`, so `gen_jsum_zero` is exactly the single Zhu tower. -/
@[simp] theorem nu_zero_zero (t : ℕ) : nu 0 t 0 = 1 := by
  rw [nu]
  simp only [Nat.zero_add, Nat.mul_zero, Nat.zero_add, Nat.choose_self, Nat.choose_zero_right,
    Nat.cast_one, mul_one, one_mul, pow_zero]
  rw [show (t+0+1 : ℕ) = t+1 from by omega]
  have ht : ((t+1 : ℕ):ℂ) ≠ 0 := by exact_mod_cast (by omega : 0 < t+1).ne'
  field_simp

/-- **The `n = 0` anchor.** Specializing `gen_jsum` at `n = 0` collapses both single-term sums to the
single Zhu tower `C(Ws+1+t, μ+3+t)` (weight `ν(0,t,0)=1`), recovering `ZhuHR.S_mem_O`. -/
theorem gen_jsum_zero (t : ℕ) (Ws μ : ℤ) :
    ((-1:ℂ)^0 * (Nat.choose (0+0) 0 : ℂ) * (Nat.choose (0+0+t) t : ℂ))
        * cbz (Ws + 2*(0:ℕ)+1+t) (μ + 3*(0:ℕ)+3+(0:ℤ)+t)
      = cbz (Ws + 1 + t) (μ + 3 + t) := by
  have h := gen_jsum 0 t Ws μ
  simp only [Finset.sum_range_one, Nat.cast_zero, pow_zero, Nat.choose_self, Nat.cast_one,
    Nat.zero_add, mul_one, one_mul, nu_zero_zero] at h ⊢
  rw [h]
  congr 1 <;> push_cast <;> ring

end ZhuRes

/-!
## The four descent memberships: PRECISE remaining target (NOT `sorry`)

With `gen_jsum` proved (axiom-clean), the single *combinatorial* obstruction flagged at the end of
`Modules.ZhuVermaAnDescent2` is discharged.  The remaining work to make the descended bimodule
actions `An.lAct`/`An.rAct` of `Modules.ZhuVermaAnDescent` *unconditional* is the VOA-level residue
bookkeeping (NOT combinatorics) — the depth-`n` analog of the `n=0` two-sided-ideal argument carried
out in `Modules.ZhuRightIdeal` (`mode_split`, `mode_commutator_uniform`, `inner_reindex`,
`S_mem_O`, `commutator_family_mem_O`).

### `leftDescends_holds` / `rightDescends_holds`
Each of the four circle-generator memberships (the fields of `LeftDescends`/`RightDescends`)
reduces, exactly as documented in `Modules.ZhuVermaAnDescent2`, to:
* the **`c`-first family**, already proved in `leftProd_circ_first_family_mem_On`;
* the **commutator family**, whose coefficient of `(w_s)₍μ₎d` (with `w_s := a₍ₛ₎c ∈ 𝒱_{K+M-s-1}`) is
  the depth-`n` `j`-sum `J(t,μ)`, now equal — via **`ZhuRes.gen_jsum`** — to
  `∑_{e=0}^n ν(n,t,e)·C(Ws+n+(n+1+t+e), μ+2n+2+(n+1+t+e))`, i.e. (summed over `μ` against `(w_s)₍μ₎d`)
  `∑_e ν(n,t,e)·PresOn W Ws n (n+1+t+e) w_s d`, each summand `∈ On W n` by the keystone
  **`Pres_mem_On`**.

Packaging the resulting `∈ On W n` memberships into `LeftDescends W n`/`RightDescends W n` (for all
`n`) yields the unconditional actions `An.lAct W n (leftDescends_holds W n)` /
`An.rAct W n (rightDescends_holds W n)`, with the `n=0` anchors `An.lAct_zero_mk`/`An.rAct_zero_mk`.
The `n=0` instance of `gen_jsum` is `ZhuRes.gen_jsum_zero` (single tower `ν=1`), matching
`ZhuHR.S_mem_O`.

The bridge from `gen_jsum` to these memberships is the depth-`n` lift of `ZhuRightIdeal`'s
`S_mem_O`/`commutator_family_mem_O` (the `finsum`-over-`μ` collapse `∑ᶠ_μ J(t,μ)·(w_s)₍μ₎d =
∑_e ν·PresOn`), built on the already-proved `Pres_mem_On` + `inner_reindex` + `PresCombo_eq_finsum`
analogs — pure VOA residue accounting, with the combinatorial certificate `gen_jsum` in hand.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.ZhuRes.alt_beta_rec
  #print axioms VOA.ZhuRes.alt_beta_sum
  #print axioms VOA.ZhuRes.gen_jsum_natid
  #print axioms VOA.ZhuRes.gen_jsum_scalar
  #print axioms VOA.ZhuRes.cbz_diag_vandermonde
  #print axioms VOA.ZhuRes.gen_jsum_XY
  #print axioms VOA.ZhuRes.gen_jsum
  #print axioms VOA.ZhuRes.gen_jsum_zero
-/
