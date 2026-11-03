/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.ContragredientFHLGen
import VOA.Modules.ContragredientFromResidual

/-!
# Closing the contragredient module: the general module FHL Borcherds identity

This file proves the **general-case RHS reduction** `rhs_gen_eq` — the only genuinely new lemma.

The strategy mirrors the quasi-primary base case `dualAdjResidualMvecAt_qp`
(`Modules.ContragredientFHLBase`): both the LHS `RHS_smul` (the `∑ cbz m i • dualAdj … (u₍ℓ+i₎v) …`)
and the RHS (the general `(a,b)` `L₁`-tower double sum) of `rhs_gen_eq` are reduced to a common
**u-first** flattened antidiagonal `∑_{A,B} (A!B!)⁻¹ • ∑ᶠ r, c r • V A B r`, where
`V A B r = mode (Y_M ((L₁ᵃu)₍ℓ+r₎(L₁ᵇv))) (D − A − B − r) xα`.

The key combinatorial simplifications:

* `K_closed`: the `e^{zL₁}`-comultiplication coefficient `K` (`Modules.ContragredientFHLComul`) has
  the closed form `a!·K p s b a = b!·gBinom (2p−s−2−a) (b−a)` (`a ≤ b`).  This eliminates `K`.
* `dualAdj_finsum`: the `dualAdj` Finset-`t`-sum extends to a `∑ᶠ t : ℕ` (the surplus terms are
  zero vectors by `L_one_pow_eq_zero`), so the comultiplication can be applied with no truncation.
* The per-`r` coefficient on **both** sides then collapses by the SAME Vandermonde lemma
  (`vand_finsum`), exactly as in the quasi-primary base case.
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End Dual)
open scoped BigOperators
open Classical

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## The comultiplication coefficient `K` in closed `gBinom` form. -/

/-- **Falling recursion for `gBinom`.** `(k+1)·gBinom n (k+1) = (n−k)·gBinom n k`. -/
theorem gBinom_falling (n : ℤ) (k : ℕ) :
    ((k : ℂ) + 1) * gBinom n (k + 1) = ((n : ℂ) - (k : ℂ)) * gBinom n k := by
  have hk : ((k.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  refine mul_left_cancel₀ hk ?_
  rw [show ((k.factorial : ℂ)) * (((k : ℂ) + 1) * gBinom n (k + 1))
        = (((k + 1).factorial : ℂ)) * gBinom n (k + 1) from by
    rw [Nat.factorial_succ]; push_cast; ring]
  rw [show ((k.factorial : ℂ)) * (((n : ℂ) - (k : ℂ)) * gBinom n k)
        = ((n : ℂ) - (k : ℂ)) * (((k.factorial : ℂ)) * gBinom n k) from by ring]
  rw [gBinom_mul_factorial n (k + 1), gBinom_mul_factorial n k,
      Finset.prod_range_succ (fun i => ((n : ℂ) - (i : ℂ))) k]
  ring

/-- **Closed form for `K`.** For `a ≤ b`, `a! · K p s b a = b! · gBinom (2p−s−2−a) (b−a)`.
Eliminates the `K`-recursion: the comultiplication coefficient is a single shifted generalized
binomial.  Proved by induction on `b`. -/
theorem K_closed (p s : ℤ) :
    ∀ (b a : ℕ), a ≤ b →
      ((a.factorial : ℂ)) * K p s b a
        = (b.factorial : ℂ) * gBinom (2 * p - s - 2 - (a : ℤ)) (b - a) := by
  intro b
  induction b with
  | zero =>
      intro a ha
      have ha0 : a = 0 := by omega
      subst ha0; rw [K]; simp
  | succ b ih =>
      intro a ha
      rcases a with _ | a
      · -- a = 0 : K p s (b+1) 0 = (2p-s-b-2) K p s b 0
        rw [K]
        have ih0 := ih 0 (by omega)
        simp only [Nat.factorial_zero, Nat.cast_one, one_mul, Nat.cast_zero, sub_zero,
          Nat.sub_zero] at ih0 ⊢
        rw [ih0]
        rw [show (((b + 1 : ℕ)).factorial : ℂ) = ((b : ℂ) + 1) * (b.factorial : ℂ) from by
          rw [Nat.factorial_succ]; push_cast; ring]
        have hfall := gBinom_falling (2 * p - s - 2) b
        rw [show ((2 * p - (s : ℤ) - (b : ℤ) - 2 : ℤ) : ℂ)
              = (((2 * p - s - 2 : ℤ) : ℂ)) - (b : ℂ) from by push_cast; ring]
        rw [show ((((2 * p - s - 2 : ℤ) : ℂ)) - (b : ℂ)) *
              ((b.factorial : ℂ) * gBinom (2 * p - s - 2) b)
            = (b.factorial : ℂ) *
              (((((2 * p - s - 2 : ℤ) : ℂ)) - (b : ℂ)) * gBinom (2 * p - s - 2) b) from by
            ring]
        rw [← hfall]; ring
      · -- a = a'+1, with a+1 ≤ b+1 i.e. a ≤ b
        have hab : a ≤ b := by omega
        rw [K, Nat.factorial_succ, Nat.cast_mul, mul_add]
        have ih1 := ih (a + 1)
        have ih2 := ih a hab
        rcases Nat.lt_or_ge a b with hlt | hge
        · -- a < b : term1 nonzero, use ih1 with (a+1 ≤ b)
          have ih1' := ih1 (by omega)
          -- term 1
          rw [show (((a + 1 : ℕ) : ℂ) * (a.factorial : ℂ)) *
                (((2 * p - ((a : ℤ) + 1) - (s : ℤ) - (b : ℤ) - 2 : ℤ) : ℂ) * K p s b (a + 1))
              = (((2 * p - ((a : ℤ) + 1) - (s : ℤ) - (b : ℤ) - 2 : ℤ) : ℂ)) *
                  (((a + 1 : ℕ).factorial : ℂ) * K p s b (a + 1)) from by
            rw [Nat.factorial_succ]; push_cast; ring]
          rw [ih1']
          -- term 2
          rw [show (((a + 1 : ℕ) : ℂ) * (a.factorial : ℂ)) * K p s b a
                = ((a : ℂ) + 1) * ((a.factorial : ℂ) * K p s b a) from by push_cast; ring]
          rw [ih2]
          -- assemble: both terms are b! · gBinom. Reduce target gBinom index.
          rw [show (b + 1 - (a + 1) : ℕ) = b - a from by omega]
          rw [show (b - (a + 1) : ℕ) = (b - a) - 1 from by omega]
          obtain ⟨d, hd⟩ : ∃ d, b - a = d + 1 := ⟨b - a - 1, by omega⟩
          rw [hd, show (d + 1 - 1 : ℕ) = d from by omega]
          simp only [Nat.cast_add, Nat.cast_one]
          set X : ℤ := 2 * p - s - 2 - ((a : ℤ) + 1) with hX
          -- coefficients as single integer casts
          have hc1 : ((2 * p - ((a : ℤ) + 1) - (s : ℤ) - (b : ℤ) - 2 : ℤ) : ℂ)
              = ((X : ℤ) : ℂ) - (b : ℂ) := by rw [hX]; push_cast; ring
          have hgX : (2 * p - s - 2 - (a : ℤ)) = X + 1 := by rw [hX]; ring
          rw [hc1, hgX]
          -- Pascal: gBinom (X+1) (d+1) = gBinom X (d+1) + gBinom X d.
          have hpas : gBinom (X + 1) (d + 1) = gBinom X (d + 1) + gBinom X d := by
            have := gBinom_succ_pascal (X + 1) d
            rwa [show (X + 1 - 1 : ℤ) = X from by ring] at this
          rw [hpas]
          rw [show (((b + 1 : ℕ)).factorial : ℂ) = ((b : ℂ) + 1) * (b.factorial : ℂ) from by
            rw [Nat.factorial_succ]; push_cast; ring]
          have hfall := gBinom_falling X d
          have hbne : ((b.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero b
          have hbval : (b : ℂ) = (a : ℂ) + (d : ℂ) + 1 := by
            have hbb : b = a + d + 1 := by omega
            rw [hbb]; push_cast; ring
          have hXval : ((X : ℤ) : ℂ) = ((2 * p - s - 2 : ℤ) : ℂ) - ((a : ℂ) + 1) := by
            rw [hX]; push_cast; ring
          -- close: factor b!, then a scalar identity provable from hfall (falling recursion).
          rw [hbval]
          have hfall' : (((d : ℂ) + 1)) * gBinom X (d + 1)
              = (((X : ℤ) : ℂ) - (d : ℂ)) * gBinom X d := hfall
          rw [hXval] at hfall' ⊢
          linear_combination (-(b.factorial : ℂ)) * hfall'
        · -- a = b (since a ≤ b and a ≥ b)
          have hae : a = b := by omega
          subst hae
          -- term1 K p s a (a+1) = 0
          rw [K_vanish p s a (a + 1) (by omega), mul_zero, mul_zero, zero_add]
          rw [show ((a + 1 : ℕ) : ℂ) * (a.factorial : ℂ) * K p s a a
                = ((a : ℂ) + 1) * ((a.factorial : ℂ) * K p s a a) from by push_cast; ring]
          rw [ih2]
          rw [show (a + 1 - (a + 1) : ℕ) = 0 from by omega, show (a - a : ℕ) = 0 from by omega]
          rw [gBinom_zero, gBinom_zero]
          rw [show (((a + 1 : ℕ)).factorial : ℂ) = ((a : ℂ) + 1) * (a.factorial : ℂ) from by
            rw [Nat.factorial_succ]; push_cast; ring]
          ring

/-! ## Extending the `dualAdj` `L₁`-tower to an infinite `∑ᶠ t`. -/

/-- A single `L₁`-tower term of `dualAdj` (state `u' ∈ 𝒱_wt`).  Vanishes for `t > wt.toNat`. -/
private noncomputable def dterm (N : OrdVModule W M) (wt : ℤ) (u' : 𝒱) (k : ℤ) (xα : M) (t : ℕ) : M :=
  ((t.factorial : ℂ)⁻¹) • mode (N.YM (((W.L 1) ^ t) u')) (2 * wt - k - 2 - (t : ℤ)) xα

/-- The `t`-th tower term vanishes once `t > wt` (so `wt − t < 0`), since `L₁ᵗ u' = 0`. -/
private theorem dterm_zero (N : OrdVModule W M) {wt : ℤ} {u' : 𝒱} (hu' : u' ∈ W.grading wt)
    (k : ℤ) (xα : M) {t : ℕ} (ht : wt - (t : ℤ) < 0) :
    dterm N wt u' k xα t = 0 := by
  rw [dterm, L_one_pow_eq_zero W hu' ht, map_zero]
  show ((t.factorial : ℂ)⁻¹) • mode (0 : (End ℂ M)⟦z^±⟧) (2 * wt - k - 2 - (t : ℤ)) xα = 0
  rw [show mode (0 : (End ℂ M)⟦z^±⟧) (2 * wt - k - 2 - (t : ℤ)) = 0 from rfl]; simp

/-- **`dualAdj` as an infinite `∑ᶠ t` `L₁`-tower.**  The Finset `dualAdj_clean` sum over
`t ∈ range (wt.toNat+1)` extends to a `∑ᶠ t : ℕ` because the surplus terms `t > wt` are zero
vectors (`dterm_zero`).  This frees the comultiplication from any truncation. -/
private theorem dualAdj_finsum (N : OrdVModule W M) {wt : ℤ} {u' : 𝒱} (hu' : u' ∈ W.grading wt)
    (k : ℤ) {α : ℂ} {xα : M} (hxα : xα ∈ N.weight α) :
    dualAdj N wt u' k α xα = (-1 : ℂ) ^ wt • ∑ᶠ t : ℕ, dterm N wt u' k xα t := by
  rw [dualAdj_clean N hu' k hxα]
  have hfs : (∑ᶠ t : ℕ, dterm N wt u' k xα t)
      = ∑ t ∈ Finset.range (wt.toNat + 1), dterm N wt u' k xα t := by
    rw [finsum_eq_finsetSum_of_support_subset (dterm N wt u' k xα)
        (s := Finset.range (wt.toNat + 1)) ?_]
    intro t ht
    rw [Function.mem_support] at ht
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hge
    exact ht (dterm_zero N hu' k xα (by omega))
  rw [hfs]
  rfl

/-! ## The common u-first `L₁`-tower vector `V` and its per-`r` coefficient. -/

/-- The common **u-first** tower vector
`V = mode (Y_M ((L₁ᵃu)₍ℓ+r₎(L₁ᵇv))) (D − A − B − r) xα`, `D = 2p+2q−2ℓ−m−n−4`. -/
private noncomputable def Vtow (N : OrdVModule W M) (u v : 𝒱) (p q ℓ m n : ℤ)
    (xα : M) (A B : ℕ) (r : ℤ) : M :=
  mode (N.YM (W.smul (((W.L 1) ^ A) u) (ℓ + r) (((W.L 1) ^ B) v)))
    ((2 * p + 2 * q - 2 * ℓ - m - n - 4) - (A : ℤ) - (B : ℤ) - r) xα

/-- The common per-`r` block coefficient `(−1)^{ℓ+1} · gBinom (2p−ℓ−m−2−A) r` (`0` for `r < 0`). -/
private noncomputable def fcoeff (p ℓ m : ℤ) (A : ℕ) (r : ℤ) : ℂ :=
  if 0 ≤ r then (-1 : ℂ) ^ (ℓ + 1) * gBinom (2 * p - ℓ - m - 2 - (A : ℤ)) r.toNat else 0

/-- The **RHS_gen** Vandermonde collapse: the skew-transported block coefficient collapses (via
`vand_finsum`) to `fcoeff`.  Parametric copy of `lhs_coeff_eq` (`B`-shift in `cbz`, `A+B`-shift in
`gBinom`) without the global `(−1)^{p+q}`. -/
private theorem rhsgen_coeff (p q ℓ m n : ℤ) (A B : ℕ) (r : ℕ) :
    (∑ᶠ j : ℕ, cbz (2 * q - ℓ - n - 2 - (B:ℤ)) (r - (j:ℤ)) * (- (-1:ℂ)^(ℓ + (r - (j:ℤ))))
        * gBinom ((2*p+2*q-2*ℓ-m-n-4 - (A:ℤ) - (B:ℤ)) - (r - (j:ℤ))) j)
      = fcoeff p ℓ m A (r:ℤ) := by
  have hcongr : ∀ j : ℕ,
      cbz (2 * q - ℓ - n - 2 - (B:ℤ)) ((r:ℤ) - (j:ℤ)) * (- (-1:ℂ)^(ℓ + ((r:ℤ) - (j:ℤ))))
        * gBinom ((2*p+2*q-2*ℓ-m-n-4 - (A:ℤ) - (B:ℤ)) - ((r:ℤ) - (j:ℤ))) j
      = (- (-1:ℂ)^(ℓ + (r:ℤ))) *
          ((-1:ℂ)^j * cbz (2 * q - ℓ - n - 2 - (B:ℤ)) ((r:ℤ) - (j:ℤ))
            * gBinom ((2*p+2*q-2*ℓ-m-n-4 - (A:ℤ) - (B:ℤ)) - ((r:ℤ) - (j:ℤ))) j) := by
    intro j
    rw [show (ℓ + ((r:ℤ) - (j:ℤ))) = (ℓ + (r:ℤ)) - (j:ℤ) from by ring, signSplit (ℓ + (r:ℤ)) j]
    ring
  rw [finsum_congr hcongr, ← mul_finsum]
  rw [vand_finsum (2 * q - ℓ - n - 2 - (B:ℤ)) (2*p+2*q-2*ℓ-m-n-4 - (A:ℤ) - (B:ℤ)) r]
  rw [fcoeff, if_pos (by positivity), Int.toNat_natCast]
  rw [show (2*p+2*q-2*ℓ-m-n-4 - (A:ℤ) - (B:ℤ)) - (2 * q - ℓ - n - 2 - (B:ℤ))
        = 2 * p - ℓ - m - 2 - (A:ℤ) from by ring]
  rw [← negOne_zpow_natCast r]
  rw [show (- (-1:ℂ)^(ℓ + (r:ℤ))) * ((-1:ℂ)^(r:ℤ) * gBinom (2 * p - ℓ - m - 2 - (A:ℤ)) r)
      = (-((-1:ℂ)^(ℓ + (r:ℤ)) * (-1:ℂ)^(r:ℤ))) * gBinom (2 * p - ℓ - m - 2 - (A:ℤ)) r from by ring]
  congr 1
  rw [← negOne_zpow_add, negOne_neg_zpow]
  exact negOne_zpow_eq _ _ ⟨(r:ℤ), by ring⟩

/-- **RHS_gen block flatten.**  Each `(a,b)` block of the RHS (a v-first `Y_M` product, skewed to
u-first via `mode_skew_gbinom`, then antidiagonal-reindexed) equals `∑ᶠ r, fcoeff … • V a b r`. -/
private theorem rhsgen_block (N : OrdVModule W M) {p : ℤ} {u : 𝒱} (hu : u ∈ W.grading p)
    {q : ℤ} {v : 𝒱} (hv : v ∈ W.grading q)
    (ℓ m n : ℤ) {α : ℂ} {xα : M} (hxα : xα ∈ N.weight α) (a b : ℕ) :
    (∑ᶠ i : ℤ, cbz (2 * q - ℓ - n - 2 - (b : ℤ)) i •
        mode (N.YM (W.smul ((W.L 1 ^ b) v) (ℓ + i) ((W.L 1 ^ a) u)))
          ((2 * q - ℓ - n - 2 - (b : ℤ)) + (2 * p - ℓ - m - 2 - (a : ℤ)) - i) xα)
      = ∑ᶠ r : ℤ, fcoeff p ℓ m a r • Vtow N u v p q ℓ m n xα a b r := by
  have hau : ((W.L 1 ^ a) u) ∈ W.grading (p - (a : ℤ)) := L_one_pow_mem W hu a
  have hbv : ((W.L 1 ^ b) v) ∈ W.grading (q - (b : ℤ)) := L_one_pow_mem W hv b
  set D : ℤ := 2 * p + 2 * q - 2 * ℓ - m - n - 4 with hD
  set V : ℤ → M := fun r => Vtow N u v p q ℓ m n xα a b r with hVdef
  -- truncation of the u-first product mode in `r`
  obtain ⟨Ns, hNs⟩ := W.toPreVertexAlgebra.smul_eventually_zero ((W.L 1 ^ a) u) ((W.L 1 ^ b) v)
  have hVzero : ∀ r : ℤ, (Ns - ℓ) ≤ r → V r = 0 := by
    intro r hr
    show Vtow N u v p q ℓ m n xα a b r = 0
    rw [Vtow, show W.smul ((W.L 1 ^ a) u) (ℓ + r) ((W.L 1 ^ b) v) = 0 from hNs (ℓ + r) (by omega),
      map_zero]
    rfl
  -- skew each summand to the u-first tower
  set g : ℤ → ℕ → ℂ := fun i j =>
    cbz (2 * q - ℓ - n - 2 - (b : ℤ)) i * (- (-1:ℂ)^(ℓ+i)) * gBinom (D - (a:ℤ) - (b:ℤ) - i) j with hg
  have hskew : (∑ᶠ i : ℤ, cbz (2 * q - ℓ - n - 2 - (b : ℤ)) i •
        mode (N.YM (W.smul ((W.L 1 ^ b) v) (ℓ + i) ((W.L 1 ^ a) u)))
          ((2 * q - ℓ - n - 2 - (b : ℤ)) + (2 * p - ℓ - m - 2 - (a : ℤ)) - i) xα)
      = ∑ᶠ (i : ℤ), ∑ᶠ (j : ℕ), g i j • V (i + (j : ℤ)) := by
    refine finsum_congr (fun i => ?_)
    rw [show (2 * q - ℓ - n - 2 - (b : ℤ)) + (2 * p - ℓ - m - 2 - (a : ℤ)) - i
          = D - (a:ℤ) - (b:ℤ) - i from by rw [hD]; ring]
    rw [mode_skew_gbinom N ((W.L 1 ^ a) u) ((W.L 1 ^ b) v) (ℓ + i) (D - (a:ℤ) - (b:ℤ) - i) xα]
    rw [smul_finsum]
    refine finsum_congr (fun j : ℕ => ?_)
    rw [hg, hVdef]
    show cbz (2 * q - ℓ - n - 2 - (b : ℤ)) i •
          ((- (-1:ℂ)^(ℓ+i)) * gBinom (D - (a:ℤ) - (b:ℤ) - i) j) •
            mode (N.YM (W.smul ((W.L 1 ^ a) u) ((ℓ + i) + (j:ℤ)) ((W.L 1 ^ b) v)))
              ((D - (a:ℤ) - (b:ℤ) - i) - (j:ℤ)) xα
        = (cbz (2 * q - ℓ - n - 2 - (b : ℤ)) i * (- (-1:ℂ)^(ℓ+i)) * gBinom (D - (a:ℤ) - (b:ℤ) - i) j) •
            Vtow N u v p q ℓ m n xα a b (i + (j:ℤ))
    rw [Vtow]
    rw [show (ℓ + (i + (j:ℤ))) = (ℓ + i) + (j:ℤ) from by ring,
        show (2 * p + 2 * q - 2 * ℓ - m - n - 4) - (a:ℤ) - (b:ℤ) - (i + (j:ℤ))
          = (D - (a:ℤ) - (b:ℤ) - i) - (j:ℤ) from by rw [hD]; ring]
    rw [smul_smul]; ring_nf
  rw [hskew]
  obtain ⟨hfin, hfin2, hfinr⟩ := antidiag_fins g V (Ns - ℓ)
    (fun i hi j => by rw [hg]; simp only []; rw [cbz_apply_neg _ hi]; ring) hVzero
  rw [antidiag_reindex g V hfin hfin2 hfinr]
  refine finsum_congr (fun r => ?_)
  rcases lt_or_ge r 0 with hr | hr
  · rw [show (∑ᶠ j : ℕ, g (r - (j:ℤ)) j) = (∑ᶠ _j : ℕ, (0:ℂ)) from
        finsum_congr (fun j => by
          rw [hg]; simp only []
          rw [cbz_apply_neg (2 * q - ℓ - n - 2 - (b : ℤ)) (by omega : r - (j:ℤ) < 0)]; ring)]
    rw [finsum_zero, zero_smul, fcoeff, if_neg (by omega), zero_smul]
  · obtain ⟨rn, rfl⟩ : ∃ rn : ℕ, r = (rn : ℤ) := ⟨r.toNat, (Int.toNat_of_nonneg hr).symm⟩
    congr 1
    rw [← rhsgen_coeff p q ℓ m n a b rn]

/-! ## The RHS_smul flatten:  reorganizing `dualAdj`-of-product into the u-first tower. -/

/-- The `mode`-of-comultiplication of a single `L₁ᵗ(u₍s₎v)`, reindexed from the comul `(B',A')`
double sum to the u-power/v-power `(A,B)` block with `A = A'`, `B = t − B'`.  Uses the closed form
`K_closed`, so each summand is `(A!B!)⁻¹·gBinom (2p−s−2−A) (t−A−B)` times a u-first tower mode. -/
private theorem mode_comul_block (N : OrdVModule W M) {p : ℤ} {u : 𝒱} (hu : u ∈ W.grading p)
    (v : 𝒱) (s : ℤ) (t : ℕ) (kk : ℤ) (xα : M) :
    mode (N.YM (((W.L 1) ^ t) (W.smul u s v))) kk xα
      = ∑ B ∈ Finset.range (t + 1), ∑ A ∈ Finset.range (t - B + 1),
          ((t.factorial : ℂ) * ((A.factorial : ℂ)⁻¹) * ((B.factorial : ℂ)⁻¹)
            * gBinom (2 * p - s - 2 - (A : ℤ)) (t - A - B)) •
            mode (N.YM (W.smul (((W.L 1) ^ A) u) (s + ((t - A - B : ℕ) : ℤ)) (((W.L 1) ^ B) v))) kk xα := by
  -- push `mode (Y_M ·) kk xα` (the linear map `modeAtState`) through the comul double sum
  rw [show mode (N.YM (((W.L 1) ^ t) (W.smul u s v))) kk xα
        = modeAtState N kk xα (((W.L 1) ^ t) (W.smul u s v)) from rfl]
  rw [L1pow_smul_comul W hu v s t]
  -- reflect the outer comul sum `B' ↦ t - B'` (pure Finset identity inside the linear map)
  rw [show (∑ B' ∈ Finset.range (t + 1), ∑ A ∈ Finset.range (B' + 1),
            ((t.choose B' : ℂ) * K p s B' A) •
              W.smul (((W.L 1) ^ A) u) (s + ((B' - A : ℕ) : ℤ)) (((W.L 1) ^ (t - B')) v))
          = ∑ B ∈ Finset.range (t + 1), ∑ A ∈ Finset.range ((t - B) + 1),
            ((t.choose (t - B) : ℂ) * K p s (t - B) A) •
              W.smul (((W.L 1) ^ A) u) (s + (((t - B) - A : ℕ) : ℤ)) (((W.L 1) ^ B) v) from by
        rw [← Finset.sum_range_reflect
              (fun B => ∑ A ∈ Finset.range ((t - B) + 1),
                ((t.choose (t - B) : ℂ) * K p s (t - B) A) •
                  W.smul (((W.L 1) ^ A) u) (s + (((t - B) - A : ℕ) : ℤ)) (((W.L 1) ^ B) v)) (t + 1)]
        refine Finset.sum_congr rfl (fun B' hB' => ?_)
        rw [Finset.mem_range] at hB'
        rw [show (t + 1 - 1 - B') = t - B' from by omega,
            show (t - (t - B')) = B' from by omega]]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun B hB => ?_)
  rw [Finset.mem_range] at hB
  rw [map_sum]
  refine Finset.sum_congr rfl (fun A hA => ?_)
  rw [Finset.mem_range, Nat.lt_succ_iff] at hA
  rw [map_smul, modeAtState_apply]
  rw [show ((t - B) - A : ℕ) = (t - A - B : ℕ) from by omega]
  congr 1
  -- coefficient:  C(t, t-B) · K p s (t-B) A  =  (A!⁻¹ B!⁻¹) · gBinom (2p-s-2-A) (t-A-B)
  have hcomb : ((t.choose (t - B) : ℂ))
      = ((t.factorial : ℂ)) * (((t - B).factorial : ℂ)⁻¹) * ((B.factorial : ℂ)⁻¹) := by
    have h2 := Nat.choose_mul_factorial_mul_factorial (show t - B ≤ t from by omega)
    rw [show t - (t - B) = B from by omega] at h2
    have h2' : ((t.choose (t - B) : ℂ)) * ((((t - B).factorial : ℂ)) * (B.factorial : ℂ))
        = (t.factorial : ℂ) := by push_cast [← h2]; push_cast; ring
    have htBf : (((t - B).factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (t - B)
    have hBf : ((B.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero B
    field_simp
    linear_combination h2'
  rw [hcomb]
  have hKc := K_closed p s (t - B) A (by omega)
  have hAfac : ((A.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero A
  have htBfac : (((t - B).factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (t - B)
  rw [show ((t - B) - A : ℕ) = (t - A - B : ℕ) from by omega] at hKc
  have hKval : K p s (t - B) A
      = (((t - B).factorial : ℂ)) * ((A.factorial : ℂ)⁻¹) * gBinom (2 * p - s - 2 - (A : ℤ)) (t - A - B) := by
    field_simp at hKc ⊢
    linear_combination hKc
  rw [hKval]
  set G : ℂ := gBinom (2 * p - s - 2 - (A : ℤ)) (t - A - B) with hG
  have hBf : ((B.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero B
  have htf : ((t.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero t
  field_simp

/-- **ℕ-shift of a finsum**: if `H` vanishes below `c`, then `∑ᶠ t, H t = ∑ᶠ j, H (c + j)`. -/
private theorem finsum_shift_nat (c : ℕ) (H : ℕ → M) (hH : ∀ t : ℕ, t < c → H t = 0) :
    (∑ᶠ t : ℕ, H t) = ∑ᶠ j : ℕ, H (c + j) := by
  have hsub : Function.support H ⊆ Set.range (fun j : ℕ => c + j) := by
    intro t ht
    rw [Function.mem_support] at ht
    have htc : c ≤ t := by by_contra hlt; exact ht (hH t (by omega))
    exact ⟨t - c, by show c + (t - c) = t; omega⟩
  have hinj : Function.Injective (fun j : ℕ => c + j) := add_right_injective c
  rw [← finsum_mem_range hinj (f := H)]
  rw [← finsum_mem_inter_support H (Set.range (fun j : ℕ => c + j)),
    ← finsum_mem_univ (f := H), ← finsum_mem_inter_support H Set.univ, Set.univ_inter,
    Set.inter_eq_right.mpr hsub]

/-- The **RHS_smul** Vandermonde collapse: the comul-side block coefficient collapses (via
`vand_finsum`) to `(−1)^{p+q} · fcoeff`.  Parametric copy of `rhs_coeff_eq` (`A`-shift in the
`gBinom`). -/
private theorem rhssmul_coeff (p q ℓ m : ℤ) (A : ℕ) (r : ℕ) :
    (∑ᶠ j : ℕ, cbz m (r - (j:ℤ))
        * ((-1:ℂ)^(p+q-(ℓ+(r - (j:ℤ)))-1) * gBinom (2*p-(ℓ+(r - (j:ℤ)))-2-(A:ℤ)) j))
      = (-1:ℂ)^(p+q) * fcoeff p ℓ m A (r:ℤ) := by
  have hcongr : ∀ j : ℕ,
      cbz m ((r:ℤ) - (j:ℤ))
        * ((-1:ℂ)^(p+q-(ℓ+((r:ℤ) - (j:ℤ)))-1) * gBinom (2*p-(ℓ+((r:ℤ) - (j:ℤ)))-2-(A:ℤ)) j)
      = (-1:ℂ)^(p+q-ℓ-(r:ℤ)-1) *
          ((-1:ℂ)^j * cbz m ((r:ℤ) - (j:ℤ)) * gBinom ((2*p-ℓ-2-(A:ℤ)) - ((r:ℤ) - (j:ℤ))) j) := by
    intro j
    rw [show (p+q-(ℓ+((r:ℤ) - (j:ℤ)))-1) = (p+q-ℓ-(r:ℤ)-1) + (j:ℤ) from by ring,
        negOne_zpow_add, negOne_zpow_natCast,
        show (2*p-(ℓ+((r:ℤ) - (j:ℤ)))-2-(A:ℤ)) = (2*p-ℓ-2-(A:ℤ)) - ((r:ℤ) - (j:ℤ)) from by ring]
    ring
  rw [finsum_congr hcongr, ← mul_finsum]
  rw [vand_finsum m (2*p-ℓ-2-(A:ℤ)) r]
  rw [fcoeff, if_pos (by positivity), Int.toNat_natCast]
  rw [show (2*p-ℓ-2-(A:ℤ)) - m = 2*p-ℓ-m-2-(A:ℤ) from by ring]
  rw [← negOne_zpow_natCast r,
      show ((-1:ℂ)^(p+q-ℓ-(r:ℤ)-1) * ((-1:ℂ)^(r:ℤ) * gBinom (2*p-ℓ-m-2-(A:ℤ)) r))
      = ((-1:ℂ)^(p+q-ℓ-(r:ℤ)-1) * (-1:ℂ)^(r:ℤ)) * gBinom (2*p-ℓ-m-2-(A:ℤ)) r from by ring]
  rw [show (-1:ℂ)^(p+q) * ((-1:ℂ)^(ℓ+1) * gBinom (2*p-ℓ-m-2-(A:ℤ)) r)
        = ((-1:ℂ)^(p+q) * (-1:ℂ)^(ℓ+1)) * gBinom (2*p-ℓ-m-2-(A:ℤ)) r from by ring]
  congr 1
  rw [← negOne_zpow_add, ← negOne_zpow_add]
  exact negOne_zpow_eq _ _ ⟨-ℓ - 1, by ring⟩

/-- The comul tower coefficient `cbz m i · (−1)^{P_i} · (A!B!)⁻¹ · gBinom (2p−(ℓ+i)−2−A) j`. -/
private noncomputable def gtow (p q ℓ m : ℤ) (A B : ℕ) (i : ℤ) (j : ℕ) : ℂ :=
  cbz m i * (-1:ℂ) ^ (p + q - (ℓ + i) - 1) * (((A.factorial : ℂ)⁻¹) * ((B.factorial : ℂ)⁻¹))
    * gBinom (2 * p - (ℓ + i) - 2 - (A : ℤ)) j

/-- `Vtow A B r = 0` once `A > p` (then `L₁ᵃu = 0`). -/
private theorem Vtow_zero_left (N : OrdVModule W M) {p : ℤ} {u : 𝒱} (hu : u ∈ W.grading p)
    (v : 𝒱) (q ℓ m n : ℤ) (xα : M) {A : ℕ} (hA : p - (A : ℤ) < 0) (B : ℕ) (r : ℤ) :
    Vtow N u v p q ℓ m n xα A B r = 0 := by
  rw [Vtow, L_one_pow_eq_zero W hu hA, W.smul_zero_left, map_zero]; rfl

/-- `Vtow A B r = 0` once `B > q` (then `L₁ᵇv = 0`). -/
private theorem Vtow_zero_right (N : OrdVModule W M) {p : ℤ} (u : 𝒱) {q : ℤ} {v : 𝒱}
    (hv : v ∈ W.grading q) (ℓ m n : ℤ) (xα : M) (A : ℕ) {B : ℕ} (hB : q - (B : ℤ) < 0) (r : ℤ) :
    Vtow N u v p q ℓ m n xα A B r = 0 := by
  rw [Vtow, L_one_pow_eq_zero W hv hB, W.smul_zero_right, map_zero]; rfl

/-- **Triangle → box (with indicator).**  For a summand `G` vanishing whenever `A > P` or `B > Q`,
the comul triangle sum `∑_{B≤t} ∑_{A≤t−B}` equals the fixed box `∑_{B≤Q} ∑_{A≤P}` with an
`[A+B≤t]` indicator. -/
private theorem tri_to_box {G : ℕ → ℕ → M} (P Q t : ℕ)
    (hG : ∀ A B, (P < A ∨ Q < B) → G A B = 0) :
    (∑ B ∈ Finset.range (t + 1), ∑ A ∈ Finset.range (t - B + 1), G A B)
      = ∑ B ∈ Finset.range (Q + 1), ∑ A ∈ Finset.range (P + 1),
          (if A + B ≤ t then G A B else 0) := by
  classical
  set R : ℕ := t + Q + P + 1 with hR
  set H : ℕ → ℕ → M := fun B A => if A + B ≤ t ∧ A ≤ P ∧ B ≤ Q then G A B else 0 with hH
  -- inner identity: per B, the LHS triangle row and the RHS box row both equal the
  -- big common row `∑_{A∈range(R+1)} H B A`
  have hrow : ∀ B : ℕ, (∑ A ∈ Finset.range (R + 1), H B A)
      = if B ≤ t then (∑ A ∈ Finset.range (t - B + 1), G A B) else 0 := by
    intro B
    by_cases hBt : B ≤ t
    · rw [if_pos hBt]
      have hsub : (∑ A ∈ Finset.range (t - B + 1), H B A)
          = ∑ A ∈ Finset.range (R + 1), H B A :=
        Finset.sum_subset (Finset.range_subset_range.mpr (by omega : t - B + 1 ≤ R + 1))
          (fun A _ hA => by rw [Finset.mem_range] at hA; simp only [hH]; rw [if_neg (by omega)])
      rw [← hsub]
      refine Finset.sum_congr rfl (fun A hA => ?_)
      rw [Finset.mem_range] at hA; simp only [hH]
      rcases Nat.lt_or_ge P A with hAP | hAP
      · rw [if_neg (by omega), hG A B (Or.inl hAP)]
      · rcases Nat.lt_or_ge Q B with hBQ | hBQ
        · rw [if_neg (by omega), hG A B (Or.inr hBQ)]
        · rw [if_pos ⟨by omega, hAP, hBQ⟩]
    · rw [if_neg hBt]
      refine Finset.sum_eq_zero (fun A _ => ?_)
      simp only [hH]; rw [if_neg (by omega)]
  have hrow2 : ∀ B : ℕ, (∑ A ∈ Finset.range (R + 1), H B A)
      = if B ≤ Q then (∑ A ∈ Finset.range (P + 1), (if A + B ≤ t then G A B else 0)) else 0 := by
    intro B
    by_cases hBQ : B ≤ Q
    · rw [if_pos hBQ]
      have hsub : (∑ A ∈ Finset.range (P + 1), H B A)
          = ∑ A ∈ Finset.range (R + 1), H B A :=
        Finset.sum_subset (Finset.range_subset_range.mpr (by omega : P + 1 ≤ R + 1))
          (fun A _ hA => by rw [Finset.mem_range] at hA; simp only [hH]; rw [if_neg (by omega)])
      rw [← hsub]
      refine Finset.sum_congr rfl (fun A hA => ?_)
      rw [Finset.mem_range] at hA; simp only [hH]
      by_cases hc : A + B ≤ t
      · rw [if_pos hc, if_pos ⟨hc, by omega, hBQ⟩]
      · rw [if_neg hc, if_neg (by omega)]
    · rw [if_neg hBQ]
      refine Finset.sum_eq_zero (fun A _ => ?_)
      simp only [hH]; rw [if_neg (by omega)]
  -- now sum the rows over `range(R+1)` and compare via the `if`-truncations
  have hbig : (∑ B ∈ Finset.range (R + 1), ∑ A ∈ Finset.range (R + 1), H B A)
      = ∑ B ∈ Finset.range (R + 1), (if B ≤ t then (∑ A ∈ Finset.range (t - B + 1), G A B) else 0) :=
    Finset.sum_congr rfl (fun B _ => hrow B)
  have hbig2 : (∑ B ∈ Finset.range (R + 1), ∑ A ∈ Finset.range (R + 1), H B A)
      = ∑ B ∈ Finset.range (R + 1),
          (if B ≤ Q then (∑ A ∈ Finset.range (P + 1), (if A + B ≤ t then G A B else 0)) else 0) :=
    Finset.sum_congr rfl (fun B _ => hrow2 B)
  have hLHS : (∑ B ∈ Finset.range (t + 1), ∑ A ∈ Finset.range (t - B + 1), G A B)
      = ∑ B ∈ Finset.range (R + 1), ∑ A ∈ Finset.range (R + 1), H B A := by
    rw [hbig]
    have hsb : (∑ B ∈ Finset.range (t + 1),
              (if B ≤ t then (∑ A ∈ Finset.range (t - B + 1), G A B) else 0))
        = ∑ B ∈ Finset.range (R + 1),
              (if B ≤ t then (∑ A ∈ Finset.range (t - B + 1), G A B) else 0) :=
      Finset.sum_subset (Finset.range_subset_range.mpr (by omega : t + 1 ≤ R + 1))
        (fun B _ hB => by simp only [Finset.mem_range, not_lt] at hB; rw [if_neg (by omega)])
    rw [← hsb]
    refine Finset.sum_congr rfl (fun B hB => ?_)
    rw [Finset.mem_range] at hB; rw [if_pos (by omega)]
  have hRHS : (∑ B ∈ Finset.range (Q + 1), ∑ A ∈ Finset.range (P + 1),
          (if A + B ≤ t then G A B else 0))
      = ∑ B ∈ Finset.range (R + 1), ∑ A ∈ Finset.range (R + 1), H B A := by
    rw [hbig2]
    have hsb : (∑ B ∈ Finset.range (Q + 1),
              (if B ≤ Q then (∑ A ∈ Finset.range (P + 1), (if A + B ≤ t then G A B else 0)) else 0))
        = ∑ B ∈ Finset.range (R + 1),
              (if B ≤ Q then (∑ A ∈ Finset.range (P + 1), (if A + B ≤ t then G A B else 0)) else 0) :=
      Finset.sum_subset (Finset.range_subset_range.mpr (by omega : Q + 1 ≤ R + 1))
        (fun B _ hB => by simp only [Finset.mem_range, not_lt] at hB; rw [if_neg (by omega)])
    rw [← hsb]
    refine Finset.sum_congr rfl (fun B hB => ?_)
    rw [Finset.mem_range] at hB; rw [if_pos (by omega)]
  rw [hLHS, hRHS]

/-- **Per-`i` expansion of `cbz m i • dualAdj`** into the fixed `(A,B)`-Finset u-first tower, with a
`∑ᶠ`-depth `j`. -/
private theorem dualAdj_block_i (N : OrdVModule W M) {p : ℤ} {u : 𝒱} (hu : u ∈ W.grading p)
    {q : ℤ} {v : 𝒱} (hv : v ∈ W.grading q)
    (ℓ m n : ℤ) {α : ℂ} {xα : M} (hxα : xα ∈ N.weight α) (i : ℤ) :
    cbz m i • dualAdj N (p + q - (ℓ + i) - 1) (W.smul u (ℓ + i) v) (m + n - i) α xα
      = ∑ B ∈ Finset.range (q.toNat + 1), ∑ A ∈ Finset.range (p.toNat + 1),
          ∑ᶠ j : ℕ, gtow p q ℓ m A B i j • Vtow N u v p q ℓ m n xα A B (i + (j : ℤ)) := by
  set P : ℤ := p + q - (ℓ + i) - 1 with hP
  have hsmem : W.smul u (ℓ + i) v ∈ W.grading P := W.smul_mem_grading hu hv (ℓ + i)
  -- `Vtow` vanishing data for `tri_to_box`
  have hGzero : ∀ (A B : ℕ) (j : ℕ),
      (p.toNat < A ∨ q.toNat < B) →
      gtow p q ℓ m A B i j • Vtow N u v p q ℓ m n xα A B (i + (j : ℤ)) = 0 := by
    rintro A B j (hA | hB)
    · rw [Vtow_zero_left N hu v q ℓ m n xα (by omega) B, smul_zero]
    · rw [Vtow_zero_right N u hv ℓ m n xα A (by omega), smul_zero]
  -- per-`t` expansion: `cbz m i • (-1)^P • dterm t` = box-with-indicator over (A,B)
  have hterm : ∀ t : ℕ,
      cbz m i • ((-1:ℂ) ^ P • dterm N P (W.smul u (ℓ + i) v) (m + n - i) xα t)
        = ∑ B ∈ Finset.range (q.toNat + 1), ∑ A ∈ Finset.range (p.toNat + 1),
            (if A + B ≤ t then
              gtow p q ℓ m A B i (t - A - B) • Vtow N u v p q ℓ m n xα A B (i + ((t - A - B : ℕ) : ℤ))
             else 0) := by
    intro t
    rw [dterm, mode_comul_block N hu v (ℓ + i) t (2 * P - (m + n - i) - 2 - (t:ℤ)) xα]
    rw [← tri_to_box p.toNat q.toNat t (G := fun A B =>
          gtow p q ℓ m A B i (t - A - B) • Vtow N u v p q ℓ m n xα A B (i + ((t - A - B : ℕ) : ℤ)))
        (fun A B h => hGzero A B (t - A - B) h)]
    -- combine the three outer scalars and push into the comul double sum
    rw [smul_smul, smul_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun B hB => ?_)
    rw [Finset.mem_range] at hB
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun A hA => ?_)
    rw [Finset.mem_range, Nat.lt_succ_iff] at hA
    have hAB : A + B ≤ t := by omega
    have htAB : ((t - A - B : ℕ) : ℤ) = (t : ℤ) - (A : ℤ) - (B : ℤ) := by omega
    -- scalars:  (cbz·(-1)^P·(t!)⁻¹) • ((t!·A!⁻¹B!⁻¹·gBinom) • mode) = (gtow) • Vtow
    rw [smul_smul]
    rw [gtow, Vtow]
    have hstate : (ℓ + i) + ((t - A - B : ℕ) : ℤ) = ℓ + (i + ((t - A - B : ℕ) : ℤ)) := by ring
    have hmode : (2 * P - (m + n - i) - 2 - (t:ℤ))
        = (2 * p + 2 * q - 2 * ℓ - m - n - 4) - (A:ℤ) - (B:ℤ) - (i + ((t - A - B : ℕ) : ℤ)) := by
      rw [hP, htAB]; ring
    rw [hstate, hmode]
    congr 1
    -- coefficient identity (t! cancels)
    have htf : ((t.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero t
    rw [hP]
    field_simp
  -- assemble: extend dualAdj to ∑ᶠ t, plug `hterm`, swap finite (A,B) sums out, shift t→j
  rw [dualAdj_finsum N hsmem (m + n - i) hxα, smul_finsum, smul_finsum]
  rw [finsum_congr hterm]
  -- finiteness of each per-(A,B) `∑ᶠ t` summand (the indexed `if`-term)
  have hfinAB : ∀ A B : ℕ, Function.HasFiniteSupport (fun t : ℕ =>
      (if A + B ≤ t then
        gtow p q ℓ m A B i (t - A - B) • Vtow N u v p q ℓ m n xα A B (i + ((t - A - B : ℕ) : ℤ))
       else 0)) := by
    intro A B
    obtain ⟨Ns, hNs⟩ := W.toPreVertexAlgebra.smul_eventually_zero (((W.L 1) ^ A) u) (((W.L 1) ^ B) v)
    show (Function.support _).Finite
    apply Set.Finite.subset (Set.finite_Icc 0 ((Ns - ℓ - i + (A:ℤ) + (B:ℤ)).toNat))
    intro t ht
    rw [Function.mem_support] at ht
    rw [Set.mem_Icc]
    refine ⟨Nat.zero_le _, ?_⟩
    by_contra hge
    apply ht
    by_cases hc : A + B ≤ t
    · have htAB : ((t - A - B : ℕ) : ℤ) = (t : ℤ) - (A : ℤ) - (B : ℤ) := by omega
      have hVz : Vtow N u v p q ℓ m n xα A B (i + ((t - A - B : ℕ) : ℤ)) = 0 := by
        rw [Vtow,
          show W.smul (((W.L 1) ^ A) u) (ℓ + (i + ((t - A - B : ℕ) : ℤ))) (((W.L 1) ^ B) v) = 0 from
            hNs _ (by rw [htAB]; omega), map_zero]
        rfl
      rw [if_pos hc, hVz, smul_zero]
    · rw [if_neg hc]
  -- swap the finite (B,A) sums out of `∑ᶠ t`
  rw [finsum_sum_comm (Finset.range (q.toNat + 1)) _ (fun B _ => by
    apply hasFiniteSupport_finsetSum (Finset.range (p.toNat + 1))
    intro A _; exact hfinAB A B)]
  refine Finset.sum_congr rfl (fun B _ => ?_)
  rw [finsum_sum_comm (Finset.range (p.toNat + 1)) _ (fun A _ => hfinAB A B)]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  -- per (A,B): shift `t = A + B + j`
  rw [finsum_shift_nat (A + B) _ (fun t htlt => by rw [if_neg (by omega)])]
  refine finsum_congr (fun j => ?_)
  rw [if_pos (by omega)]
  congr 2
  · show ((A + B + j) - A - B : ℕ) = j; omega
  · show i + (((A + B + j) - A - B : ℕ) : ℤ) = i + (j : ℤ)
    congr 1; show (((A + B + j) - A - B : ℕ) : ℤ) = (j : ℤ); congr 1; omega

/-! ## The general module FHL Borcherds RHS reduction. -/

theorem rhs_gen_eq (N : OrdVModule W M) {p : ℤ} {u : 𝒱} (hu : u ∈ W.grading p)
    {q : ℤ} {v : 𝒱} (hv : v ∈ W.grading q)
    (ℓ m n : ℤ) {α : ℂ} {xα : M} (hxα : xα ∈ N.weight α) :
    (∑ᶠ i : ℤ, cbz m i •
        dualAdj N (p + q - (ℓ + i) - 1) (W.smul u (ℓ + i) v) (m + n - i) α xα)
      = (-1 : ℂ) ^ (p + q) •
          ∑ b ∈ Finset.range (q.toNat + 1), ∑ a ∈ Finset.range (p.toNat + 1),
            (((a.factorial : ℂ)⁻¹) * ((b.factorial : ℂ)⁻¹)) •
              ∑ᶠ i : ℤ, cbz (2 * q - ℓ - n - 2 - (b : ℤ)) i •
                mode (N.YM (W.smul ((W.L 1 ^ b) v) (ℓ + i) ((W.L 1 ^ a) u)))
                  ((2 * q - ℓ - n - 2 - (b : ℤ)) + (2 * p - ℓ - m - 2 - (a : ℤ)) - i) xα := by
  -- RHS: flatten each block to the u-first tower via `rhsgen_block`, then push the
  -- global `(-1)^{p+q}` into the `(a,b)` double sum, fusing it with `(a!b!)⁻¹`.
  rw [Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => by
    rw [rhsgen_block N hu hv ℓ m n hxα a b]))]
  simp only [Finset.smul_sum, smul_smul]
  -- LHS: per-`i` expansion, then swap the finite (B,A) sums out of `∑ᶠ i`
  rw [finsum_congr (fun i => dualAdj_block_i N hu hv ℓ m n hxα i)]
  -- finiteness of the per-(A,B) `∑ᶠ i ∑ᶠ j` summand and the inner `∑ᶠ j`
  have hgfin : ∀ A B : ℕ,
      (Function.support (fun pr : ℤ × ℕ => gtow p q ℓ m A B pr.1 pr.2 •
        Vtow N u v p q ℓ m n xα A B (pr.1 + (pr.2 : ℤ)))).Finite
      ∧ (Function.support (fun pr : ℤ × ℕ => gtow p q ℓ m A B (pr.1 - (pr.2 : ℤ)) pr.2 •
          Vtow N u v p q ℓ m n xα A B pr.1)).Finite
      ∧ (∀ r : ℤ, (Function.support (fun j : ℕ => gtow p q ℓ m A B (r - (j : ℤ)) j)).Finite) := by
    intro A B
    obtain ⟨Ns, hNs⟩ := W.toPreVertexAlgebra.smul_eventually_zero (((W.L 1) ^ A) u) (((W.L 1) ^ B) v)
    refine antidiag_fins (fun i j => gtow p q ℓ m A B i j) (fun r => Vtow N u v p q ℓ m n xα A B r)
      (Ns - ℓ) (fun i hi j => by simp only [gtow]; rw [cbz_apply_neg _ hi]; ring) (fun r hr => ?_)
    show Vtow N u v p q ℓ m n xα A B r = 0
    rw [Vtow, show W.smul (((W.L 1) ^ A) u) (ℓ + r) (((W.L 1) ^ B) v) = 0 from hNs _ (by omega),
      map_zero]; rfl
  -- i-support of `fun i => ∑ᶠ j, gtow•Vtow(i+j)` is finite
  have hifin : ∀ A B : ℕ, Function.HasFiniteSupport (fun i : ℤ =>
      ∑ᶠ j : ℕ, gtow p q ℓ m A B i j • Vtow N u v p q ℓ m n xα A B (i + (j : ℤ))) := by
    intro A B
    obtain ⟨Ns, hNs⟩ := W.toPreVertexAlgebra.smul_eventually_zero (((W.L 1) ^ A) u) (((W.L 1) ^ B) v)
    show (Function.support _).Finite
    apply Set.Finite.subset (Set.finite_Icc 0 (Ns - ℓ))
    intro i hi
    rw [Function.mem_support] at hi; rw [Set.mem_Icc]
    refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
    · refine finsum_eq_zero_of_forall_eq_zero (fun j => ?_)
      simp only [gtow]; rw [cbz_apply_neg _ h]; simp
    · refine finsum_eq_zero_of_forall_eq_zero (fun j => ?_)
      have hVz : Vtow N u v p q ℓ m n xα A B (i + (j:ℤ)) = 0 := by
        rw [Vtow, show W.smul (((W.L 1) ^ A) u) (ℓ + (i + (j:ℤ))) (((W.L 1) ^ B) v) = 0 from
          hNs _ (by omega), map_zero]; rfl
      rw [hVz, smul_zero]
  rw [finsum_sum_comm (Finset.range (q.toNat + 1)) _ (fun B _ =>
    hasFiniteSupport_finsetSum (Finset.range (p.toNat + 1)) _ (fun A _ => hifin A B))]
  refine Finset.sum_congr rfl (fun B _ => ?_)
  rw [finsum_sum_comm (Finset.range (p.toNat + 1)) _ (fun A _ => hifin A B)]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  -- per (A,B): antidiagonal-reindex then collapse the per-`r` coefficient
  obtain ⟨hfin, hfin2, hfinr⟩ := hgfin A B
  rw [antidiag_reindex (fun i j => gtow p q ℓ m A B i j) (fun r => Vtow N u v p q ℓ m n xα A B r)
        hfin hfin2 hfinr]
  -- finiteness of `r ↦ fcoeff • Vtow`
  have hffin : (Function.support (fun r : ℤ =>
      fcoeff p ℓ m A r • Vtow N u v p q ℓ m n xα A B r)).Finite := by
    obtain ⟨Ns, hNs⟩ := W.toPreVertexAlgebra.smul_eventually_zero (((W.L 1) ^ A) u) (((W.L 1) ^ B) v)
    apply Set.Finite.subset (Set.finite_Icc 0 (Ns - ℓ))
    intro r hr
    rw [Function.mem_support] at hr; rw [Set.mem_Icc]
    refine ⟨not_lt.mp fun h => hr ?_, not_lt.mp fun h => hr ?_⟩
    · rw [fcoeff, if_neg (by omega), zero_smul]
    · have hVz : Vtow N u v p q ℓ m n xα A B r = 0 := by
        rw [Vtow, show W.smul (((W.L 1) ^ A) u) (ℓ + r) (((W.L 1) ^ B) v) = 0 from hNs _ (by omega),
          map_zero]; rfl
      rw [hVz, smul_zero]
  -- pull the constant into the RHS finsum
  rw [smul_finsum' ((-1:ℂ) ^ (p + q) * (((A.factorial : ℂ)⁻¹) * ((B.factorial : ℂ)⁻¹))) hffin]
  -- match per `r`
  refine finsum_congr (fun r => ?_)
  rw [smul_smul]
  congr 1
  rcases lt_or_ge r 0 with hr | hr
  · rw [fcoeff, if_neg (by omega), mul_zero]
    refine finsum_eq_zero_of_forall_eq_zero (fun j => ?_)
    rw [gtow, cbz_apply_neg _ (by omega : r - (j:ℤ) < 0)]; ring
  · obtain ⟨rn, rfl⟩ : ∃ rn : ℕ, r = (rn : ℤ) := ⟨r.toNat, (Int.toNat_of_nonneg hr).symm⟩
    -- `∑ᶠ j gtow(rn-j) j = (-1)^{p+q} (A!⁻¹B!⁻¹) fcoeff` (via rhssmul_coeff)
    have hpull : (∑ᶠ j : ℕ, gtow p q ℓ m A B ((rn:ℤ) - (j:ℤ)) j)
        = (((A.factorial : ℂ)⁻¹) * ((B.factorial : ℂ)⁻¹)) *
            (∑ᶠ j : ℕ, cbz m ((rn:ℤ) - (j:ℤ))
              * ((-1:ℂ)^(p+q-(ℓ+((rn:ℤ) - (j:ℤ)))-1)
                * gBinom (2*p-(ℓ+((rn:ℤ) - (j:ℤ)))-2-(A:ℤ)) j)) := by
      rw [mul_finsum]
      refine finsum_congr (fun j => ?_)
      rw [gtow]; ring
    rw [hpull, rhssmul_coeff p q ℓ m A rn]
    ring

/-! ## Assembly: the per-datum identity, the global residual, and the closed contragredient. -/

/-- **The general per-datum module FHL Borcherds identity.** Combines the general LHS reduction
`lhs_gen_eq` with the new RHS reduction `rhs_gen_eq` (both sides equal the same u-first tower
double sum), with NO quasi-primary assumption. -/
theorem dualAdjResidualMvecAt_gen (N : OrdVModule W M) {p : ℤ} {u : 𝒱} (hu : u ∈ W.grading p)
    {q : ℤ} {v : 𝒱} (hv : v ∈ W.grading q) (ℓ m n : ℤ) {α : ℂ} {xα : M}
    (hxα : xα ∈ N.weight α) :
    DualAdjResidualMvecAt N p u q v ℓ m n α xα := by
  unfold DualAdjResidualMvecAt
  rw [lhs_gen_eq N hu hv ℓ m n hxα, rhs_gen_eq N hu hv ℓ m n hxα]

/-- **The global `M`-vector module FHL Borcherds identity** (the clean `f`-free crux), for every
homogeneous datum. -/
theorem dualAdjResidualMvec_holds (N : OrdVModule W M) : DualAdjResidualMvec N :=
  fun _wtu _uu hu _wtv _vv hv ℓ m n _α _xα hxα => dualAdjResidualMvecAt_gen N hu hv ℓ m n hxα

/-- **The fully-discharged contragredient module** `M* = ⨁_α (M_α)*` as a graded `𝒱`-module
(Gannon §5.3.1, eq. 5.1.11a), built from the proved residual `dualAdjResidualMvec_holds` with
NO remaining hypothesis: the module-level FHL/`ι_z` full invariance is discharged. -/
noncomputable def contragredientModule (N : OrdVModule W M) : OrdVModule W (RestrictedDual N) :=
  contragredient_of_dualAdjResidual N (dualAdjResidual_of_mvec N (dualAdjResidualMvec_holds N))

/-- **The main result of `Modules/ContragredientFromResidual`, unconditional.**  The full
graded contragredient `OrdVModule M* = ⨁_α (M_α)*` produced by `contragredient_of_dualAdjResidual`
with its sole `DualAdjResidual N` hypothesis discharged by the proved residual
`dualAdjResidualMvec_holds` (via `dualAdjResidual_of_mvec`).  Exposed under the `FromResidual` name
with **no carried hypothesis**; definitionally the fully-closed `contragredientModule N`. -/
noncomputable def contragredientFromResidual (N : OrdVModule W M) : OrdVModule W (RestrictedDual N) :=
  contragredientModule N

/-- The residual-discharged contragredient module has weight spaces `(M*)_α = (M_α)*`. -/
@[simp] theorem contragredientFromResidual_weight (N : OrdVModule W M) (α : ℂ) :
    (contragredientFromResidual N).weight α = RestrictedDual.weight N α := rfl

/-- **`ContragredientJacobi N` is unconditional.** Via the bridge
`contragredientJacobi_of_dualAdjResidual` fed by the proved residual, the module-level
FHL/`ι_z` full-invariance statement holds with NO hypothesis. Consequently the
`ContragredientJacobi`-gated `contragredient N` (`Modules/ContragredientJacobi.lean`) is also
unconditional: `contragredient N (contragredientJacobi_holds N)`. -/
theorem contragredientJacobi_holds (N : OrdVModule W M) : ContragredientJacobi N :=
  contragredientJacobi_of_dualAdjResidual N (dualAdjResidual_of_mvec N (dualAdjResidualMvec_holds N))

/-! ### The headline `Modules/Contragredient` (Gannon 5.3.4–5.3.5), unconditional.

The full twisted-adjoint contragredient OrdVModule `M* = ⨁_α (M_α)*` of any `N` is the hypothesis-free
`contragredientModule N` (`= contragredientFromResidual N`) — definitionally the parametric
`contragredient N hJac` fed the proved `contragredientJacobi_holds N`.  The `5.3.4b`
graded-dimension identity `contragredient_gradedDim` (`χ_{M*}(τ) = χ_M(τ)`) is a theorem that
holds unconditionally; the `5.3.5b` `Unitary` / `SelfContragredient` **predicates** are stated on
`N` (carrier `RestrictedDual N`) and so are statable/applicable to it verbatim (whether a given `N`
*satisfies* them is, as always, `N`-dependent) — all with no `ContragredientJacobi` hypothesis. -/

/-- The unconditional contragredient module is definitionally the parametric `contragredient N hJac`
with the proved `contragredientJacobi_holds N` plugged in. -/
theorem contragredientModule_eq_contragredient (N : OrdVModule W M) :
    contragredientModule N = contragredient N (contragredientJacobi_holds N) := rfl

-- `5.3.4b` (`contragredient_gradedDim`) and `5.3.5b` (`Unitary` / `SelfContragredient`) compile
-- verbatim against the unconditional headline module:
example (N : OrdVModule W M) : contragredientGradedDim N = gradedDim N := contragredient_gradedDim N
example (N : OrdVModule W M) : Prop := SelfContragredient N
example [StarRing ℂ] (N : OrdVModule W M) : Type _ := Unitary N

-- Axiom check (run + verified; all print exactly [propext, Classical.choice, Quot.sound]):
-- #print axioms VOA.dualAdjResidualMvec_holds
-- #print axioms VOA.contragredientModule
-- #print axioms VOA.contragredientJacobi_holds

end VOA
