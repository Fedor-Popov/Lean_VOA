/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchFiltration

/-!
# Closing the surjection filtration `O_n(𝒱) ⊆ O₀(𝒱)`.

This file discharges the single remaining circle membership left open by
`ZhuVermaAnArchFiltration`, namely `circ W n c d ∈ O W` (Dong–Li–Mason, *J. Algebra* 206 (1998),
Prop. 2.4: `O_n ⊆ O₀`).  Together with `OnFull_le_OnFull_zero_of_circ` this yields
`OnFull W n ≤ OnFull W 0`, the inclusion driving the algebra surjection `A_n(𝒱) ↠ A₀(𝒱)`.

## The DLM pole-reduction, made effective.

Write the two-parameter FZ residue (proved in `ZhuVermaAnArchFiltration`)
`Gres W a b T p = ∑_{i=0}^{T} C(T,i)·a₍ᵢ₋ₚ₎b = Res_z Y(a,z)b (1+z)^T / z^p`.
For homogeneous `a ∈ 𝒱_M` set the **`H`-family**
`H W M a b n m := Gres W a b (M+n) (2+n+m)  = Res_z Y(a,z)b (1+z)^{M+n}/z^{2+n+m}`.
Then `circ W n a b = H W M a b n n` (numerator `M+n`, pole `2n+2 = 2+n+n`; via `circ_eq_Gres`), and
the depth-`m=0` slice is exactly the FZ keystone `H W M a b n 0 = Pres W M a b n ∈ O(𝒱)`
(`Pres_mem_O`, `ZhuModule`).

The closure runs on the **(1+z)-power Pascal recursion** `cbz_pascal_up`:
`Gres a T p = Gres a (T-1) p + Gres a (T-1) (p-1)` (`Gres_tpascal`), which in `H`-coordinates is
`H W M a b (n+1) m = H W M a b n (m+1) + H W M a b n m`.  Solving for the `m+1` term,
`H W M a b n (m+1) = H W M a b (n+1) m - H W M a b n m`,
both right-hand summands have the SAME parameter `m`.  An induction on `m` (base `m = 0` = `Pres`)
therefore proves `H W M a b n m ∈ O(𝒱)` for ALL `n, m` — crossing the `p − (T−M)` "excess-of-pole"
lines that the earlier excess-preserving recursions (`Gres_recursion`, `Pres_succ`) could not.  At
`m = n` this is `circ W n a b ∈ O(𝒱)`.  Bilinear extension in the left factor (`circ_add_left`,
`circ_smul_left`, `eq_zero_of_mem_neg_grading` for the `< 0` grades) removes the homogeneity
hypothesis.

All results here are axiom-clean `[propext, Classical.choice, Quot.sound]`; no existing def changed.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The `(1+z)`-power Pascal recursion for `Gres`. -/

/-- **`(1+z)`-power Pascal recursion (T-Pascal).**  For `T ≥ 1` and `p ≥ 1`:
`Gres a T p = Gres a (T-1) p + Gres a (T-1) (p-1)`.
Proof: expand the top binomial via `cbz_pascal_up` `C(T,i) = C(T-1,i) + C(T-1,i-1)`; the `C(T-1,i)`
sum loses its top term (`C(T-1,T)=0`) onto `range T`, giving `Gres a (T-1) p`; the `C(T-1,i-1)` sum
loses its bottom term (`C(T-1,-1)=0`) and reindexes `i ↦ i-1` onto `range T`, giving
`Gres a (T-1) (p-1)` (mode `(i+1)-p = i-(p-1)`). -/
theorem Gres_tpascal (W : VertexOperatorAlgebra 𝒱) (a b : 𝒱) (T p : ℕ) (hT : 1 ≤ T) (hp : 1 ≤ p) :
    Gres W a b T p = Gres W a b (T - 1) p + Gres W a b (T - 1) (p - 1) := by
  obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
  have hTsub : T' + 1 - 1 = T' := by omega
  -- Split Gres a (T'+1) p via cbz_pascal_up over range (T'+2).
  have hsplit : Gres W a b (T' + 1) p
      = (∑ i ∈ Finset.range (T' + 2), cbz (T' : ℤ) (i : ℤ) • W.smul a ((i : ℤ) - p) b)
        + (∑ i ∈ Finset.range (T' + 2),
            cbz (T' : ℤ) ((i : ℤ) - 1) • W.smul a ((i : ℤ) - p) b) := by
    unfold Gres
    rw [show (T' + 1 + 1) = T' + 2 from rfl, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← add_smul]
    congr 1
    have hpu := cbz_pascal_up (T' : ℤ) (i : ℤ)
    rw [show ((T' + 1 : ℕ) : ℤ) = (T' : ℤ) + 1 from by push_cast; ring, hpu]
  -- First sum: drop the top i = T'+1 term (C(T',T'+1) = 0) onto range (T'+1) = Gres a T' p.
  have hfirst : (∑ i ∈ Finset.range (T' + 2), cbz (T' : ℤ) (i : ℤ) • W.smul a ((i : ℤ) - p) b)
      = Gres W a b T' p := by
    unfold Gres
    rw [show T' + 2 = (T' + 1) + 1 from rfl, Finset.sum_range_succ]
    rw [show cbz (T' : ℤ) ((T' + 1 : ℕ) : ℤ) = 0 from
        cbz_lt (by positivity) (by exact_mod_cast by omega), zero_smul, add_zero]
  -- Second sum: drop bottom i = 0 (C(T',-1) = 0), reindex onto range (T'+1) → Gres a T' (p-1).
  have hsecond : (∑ i ∈ Finset.range (T' + 2),
        cbz (T' : ℤ) ((i : ℤ) - 1) • W.smul a ((i : ℤ) - p) b)
      = Gres W a b T' (p - 1) := by
    have hpsub : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by push_cast [Nat.cast_sub hp]; ring
    rw [Finset.sum_range_succ'
        (fun i => cbz (T' : ℤ) ((i : ℤ) - 1) • W.smul a ((i : ℤ) - p) b) (T' + 1)]
    rw [show cbz (T' : ℤ) ((0 : ℕ) - 1 : ℤ) = 0 from cbz_apply_neg _ (by norm_num),
      zero_smul, add_zero]
    unfold Gres
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 2
    · push_cast; ring
    · rw [hpsub]; push_cast; ring
  rw [hsplit, hfirst, hsecond, hTsub]

/-! ## The `H`-family and its membership in `O(𝒱)`. -/

/-- The FZ `H`-family `H W M a b n m = Gres W a b (M+n) (2+n+m)`
(`= Res_z Y(a,z)b (1+z)^{M+n}/z^{2+n+m}`).
At `m = 0` it is the keystone `Pres W M a b n`; at `m = n` (for `a ∈ 𝒱_M`) it is `circ W n a b`. -/
noncomputable def Hres (W : VertexOperatorAlgebra 𝒱) (M : ℕ) (a b : 𝒱) (n m : ℕ) : 𝒱 :=
  Gres W a b (M + n) (2 + n + m)

/-- `H W M a b n 0 = Pres W M a b n`: the `m = 0` slice is the FZ keystone residue. -/
theorem Hres_zero_eq_Pres (W : VertexOperatorAlgebra 𝒱) (M : ℕ) (a b : 𝒱) (n : ℕ) :
    Hres W M a b n 0 = Pres W M a b n := by
  unfold Hres Gres Pres
  rw [show 2 + n + 0 = n + 2 from by ring]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (((M + n : ℕ) : ℤ)) = (M : ℤ) + (n : ℤ) from by push_cast; ring,
    show ((i : ℤ) - ((n + 2 : ℕ) : ℤ)) = (i : ℤ) - 2 - (n : ℤ) from by push_cast; ring]

/-- **The `H`-family Pascal recursion (in `H`-coordinates).**  `Gres_tpascal` at `T = M+n+1`,
`p = 2+(n+1)+m` reads `H W M a b (n+1) m = H W M a b n (m+1) + H W M a b n m`.  (The `T-1 = M+n`
and `p-1 = 2+n+m` branches are exactly `H n (m+1)` and `H n m`.) -/
theorem Hres_pascal (W : VertexOperatorAlgebra 𝒱) (M : ℕ) (a b : 𝒱) (n m : ℕ) :
    Hres W M a b (n + 1) m = Hres W M a b n (m + 1) + Hres W M a b n m := by
  unfold Hres
  have h := Gres_tpascal W a b (M + (n + 1)) (2 + (n + 1) + m) (by omega) (by omega)
  rw [show M + (n + 1) - 1 = M + n from by omega,
    show 2 + (n + 1) + m - 1 = 2 + n + m from by omega] at h
  rw [h, show 2 + (n + 1) + m = 2 + n + (m + 1) from by ring]

/-- **`H W M a b n m ∈ O(𝒱)` for all `n, m`** (for homogeneous `a ∈ 𝒱_M`).  Induction on `m`:
* `m = 0`: `H n 0 = Pres W M a b n ∈ O(𝒱)` (`Hres_zero_eq_Pres`, `Pres_mem_O`).
* `m+1`: from `Hres_pascal` at `n`, `H n (m+1) = H (n+1) m − H n m`; both summands are
  at parameter `m`, hence in `O(𝒱)` by the induction hypothesis (applied at depths `n+1` and `n`).
-/
theorem Hres_mem_O (W : VertexOperatorAlgebra 𝒱) {M : ℕ} {a : 𝒱}
    (ha : a ∈ W.grading (M : ℤ)) (b : 𝒱) (m n : ℕ) : Hres W M a b n m ∈ O W := by
  induction m generalizing n with
  | zero =>
    rw [Hres_zero_eq_Pres W M a b n]
    exact Pres_mem_O W ha b n
  | succ m ih =>
    -- H n (m+1) = H (n+1) m - H n m, both ∈ O W by IH at parameter m.
    have hpasc := Hres_pascal W M a b n m
    -- hpasc : H (n+1) m = H n (m+1) + H n m
    have heq : Hres W M a b n (m + 1) = Hres W M a b (n + 1) m - Hres W M a b n m := by
      rw [hpasc]; abel
    rw [heq]
    exact Submodule.sub_mem _ (ih (n + 1)) (ih n)

/-! ## `circ W n c d ∈ O W` and the filtration inclusion. -/

/-- For homogeneous `a ∈ 𝒱_M`, `circ W n a b = H W M a b n n ∈ O(𝒱)` (the `m = n` slice). -/
theorem circ_homog_mem_O (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M : ℕ} {a : 𝒱}
    (ha : a ∈ W.grading (M : ℤ)) (b : 𝒱) : circ W n a b ∈ O W := by
  have hcirc : circ W n a b = Hres W M a b n n := by
    rw [circ_eq_Gres W n ha b, Hres, show 2 + n + n = 2 * n + 2 from by ring]
  rw [hcirc]
  exact Hres_mem_O W ha b n n

/-- **`circ W n c d ∈ O W` for ALL `c d`** (Dong–Li–Mason Prop. 2.4: `O_n ⊆ O₀`).  Bilinear
extension of `circ_homog_mem_O` in the left factor over the internal grading
(`circ_add_left`; the `< 0` grades contribute `0` via `W.positivity` + `circ_zero_left`). -/
theorem circ_n_mem_O (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (c d : 𝒱) : circ W n c d ∈ O W := by
  have hctop : c ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun c => circ W n c d ∈ O W) hctop ?_ ?_ ?_
  · intro i x hx
    rcases lt_or_ge i 0 with hi | hi
    · have hx0 : x = 0 := by
        rw [W.positivity i hi] at hx; exact (Submodule.mem_bot ℂ).mp hx
      rw [hx0, circ_zero_left W n d]
      exact (O W).zero_mem
    · obtain ⟨M, rfl⟩ : ∃ M : ℕ, i = (M : ℤ) := ⟨i.toNat, by omega⟩
      exact circ_homog_mem_O W n hx d
  · show circ W n 0 d ∈ O W
    rw [circ_zero_left W n d]; exact (O W).zero_mem
  · intro x y hx hy
    rw [circ_add_left W n x y d]
    exact (O W).add_mem hx hy

/-- `circ W n c d ∈ OnFull W 0` (= `O W`, via `OnFull_zero_eq_O`). -/
theorem circ_mem_OnFull_zero (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (c d : 𝒱) :
    circ W n c d ∈ OnFull W 0 := by
  rw [OnFull_zero_eq_O W]; exact circ_n_mem_O W n c d

/-- **`OnFull W n ≤ OnFull W 0`** (Dong–Li–Mason Prop. 2.4).  The `OnL`-generator family is already
`≤ OnFull W 0` (`OnL_le_OnFull_zero`); the `n`-dependent circle generators land in `OnFull W 0` by
`circ_mem_OnFull_zero`.  This is the inclusion driving the surjection `A_n(𝒱) ↠ A₀(𝒱)`. -/
theorem OnFull_le_OnFull_zero (W : VertexOperatorAlgebra 𝒱) (n : ℕ) :
    OnFull W n ≤ OnFull W 0 :=
  OnFull_le_OnFull_zero_of_circ W n (circ_mem_OnFull_zero W n)

/-- **`O_n(𝒱) ⊆ O₀(𝒱) = O(𝒱)`** at the level of the circle-only spans `On`. -/
theorem On_le_On_zero (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : On W n ≤ O W := by
  rw [On_eq_span, Submodule.span_le]
  rintro x ⟨c, d, rfl⟩
  exact circ_n_mem_O W n c d

/-! ## The unconditional algebra surjection `A_n(𝒱) ↠ A₀(𝒱)`. -/

/-- **`A_n(𝒱) ↠ A₀(𝒱)`**, unconditional (the inclusion `OnFull_le_OnFull_zero` is proved). -/
noncomputable def AnFull_to_A0' (W : VertexOperatorAlgebra 𝒱) (n : ℕ) :
    (𝒱 ⧸ OnFull W n) →ₗ[ℂ] (𝒱 ⧸ OnFull W 0) :=
  AnFull_to_A0 W n (OnFull_le_OnFull_zero W n)

theorem AnFull_to_A0'_surjective (W : VertexOperatorAlgebra 𝒱) (n : ℕ) :
    Function.Surjective (AnFull_to_A0' W n) :=
  AnFull_to_A0_surjective W n (OnFull_le_OnFull_zero W n)

end VOA
