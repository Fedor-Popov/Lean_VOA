/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDJ49Iterate
import VOA.Modules.ZhuVermaAnArchDJ48BdryHolds
import VOA.Modules.ZhuMuIdentity

/-!
# C2 — Dong–Jiang Lemma 4.8/4.9: the pure-`𝒱` statement `(★)` is a THEOREM

`ZhuVermaAnArchDJ49Star` states the pure-`𝒱` membership `(★)` (`DJ49Star` / `DJ49StarPrime`) that
carries the whole `ℓ < 0` half of `ModuleIterate`, and `ZhuVermaAnArchDJ49Iterate` reduces
`ModuleIterate (muFullRhoU W U)` — for *every* `A(𝒱)`-module `U` at once — to it.  Both files
carried `(★)` as an explicit hypothesis.

**This file PROVES it** (`dj49StarPrime_holds`, `dj49Star_holds`), unconditionally, axiom-clean and
pbw-free, hence turns `moduleIterate_of_dj49Star` into the unconditional
`moduleIterate_muFullRhoU` / `muFullWeakU_uncond`, and — §8 — transports it to the **balanced**
Dong–Jiang carrier `DJCarrier W U = ⊕ₙ A_{n,0}(𝒱) ⊗_{A(𝒱)} U` at base level `0`:

* `djModeZero_iterate_incl` — the `ℓ < 0` iterate identity on one graded piece;
* `djModeZero_iterate_neg` — the same for arbitrary `u, v ∈ 𝒱` and arbitrary `x ∈ M(U)`.

⚠ **WHAT IS NOT HERE.**  The `ℓ ≥ 0` half on `DJCarrier`.  `moduleIterate_nonneg` (and the
`MBL`/`MBR` apparatus it rests on) is stated for a `VHat.VHatRep`, and **no `VHatRep` (nor
`ModeData`) has been built on `DJCarrier`** — `djModeZero` is defined directly, not through a
Lie morphism `V̂ →ₗ⁅ℂ⁆ End ℂ (DJCarrier W U)`.  Its bracket law is already proved
(`djModeZero_commutator_gen`, unconditional); what is missing for the packaging is the `L₋₁`
derivative relation on `DJCarrier` plus the Lie-morphism assembly.  Consequently **no `WeakModule`
on `DJCarrier` is claimed here**.

## The route

Write `E = wt u + n` (a natural number), `A₀ = E − ℓ − 1`, `P = wt v − N − 1 + n`,
`B₀ = q − wt u + 1`; the level constraint `q = wt u + wt v − ℓ − N − 2 + n` gives `ℓ + B₀ = P`,
`ℓ + A₀ = E − 1` and `A₀ + P + 2 = q + n + 2`.

1. **Both alternating sums collapse to a single residue family** (`dj49c2_collapse`).  Expanding
   `x *^q_{n,p} y = ∑ₛ C(−a−1,s)·Res_z (1+z)^{wt x+n}z^{−a−s−1}Y(x,z)y` with `a = n + q − p` and
   reindexing the resulting triangle by `w = i + s` (`dj49c2_triangle`), the inner `i`-sum is a
   Vandermonde convolution (`dj49c2_inner_vand`):
   ```
   ∑ᵢ (−1)ⁱC(ℓ,i)·(x *^q_{n,Λ−i} y)
       = ∑_{w=0}^{Λ} (−1)^w C(ℓ+Z+w, w)·Res_z (1+z)^{wt x+n}z^{−Z−w−1}Y(x,z)y ,
   ```
   with `Z = n + q − Λ`.  Applied at `Λ = P` (giving `C(−E,w)`) and at `Λ = E − 1` (giving
   `(−1)^w C(P+w,w)`).
2. **Skew symmetry** (`resHom_skew_mod_Onm`) turns the second family into a `u`-mode family with
   `(1+z)`-exponent `w`, at the cost of the sign `(−1)^{B₀+w}`; combined with `(−1)^{ℓ}` and
   `(−1)^w` this is exactly `(−1)^P`, independent of `w`.
3. **One scalar identity** (`dj49c2_scalar`) finishes it.  With `c = ℓ − P − 1 − j` the coefficient
   of `u₍ⱼ₎v` in `(★)` is
   ```
   [c = −P−1] − ∑_{w=0}^{P} C(−E,w)C(E,c+P+1−w) + (−1)^P ∑_{w=0}^{E−1} C(P+w,w)C(w,c)
     = ∑_{k=0}^{−P−1} d_k · C(E, c−k),      d_k = C(−E,P+1+k) + (−1)^{P+k}C(P+k+E, E−1),
   ```
   and `C(E, c−k) = C(E, j+q+n+2+k)` is exactly the generator that `resFull_offdiag_mem_Onm`
   annihilates.  The identity is proved coefficientwise in `k`: three Vandermonde convolutions
   (`cbz_vandermonde`) turn each of the four pieces into a `k`-`finsum` against `C(E, c−k)`, and the
   resulting `k`-summand vanishes identically by two upper-index-negation lemmas
   (`dj49c2_S1`, `dj49c2_S2`).

The truncated alternating Vandermonde `dj49_master` of `ZhuVermaAnArchDJ49Master` is the `P ≥ 0`
shadow of this computation; both come from `cbz_vandermonde` + `alt_cbz_eq`.

## Engine verification (checked before formalization)

`certificates/mathematica/c2_star_scalar2.wl` checks `(★)`'s coefficient identity **directly from the
definitions** of `anmGen`, `resHom` and the skew rewrite, over `0 ≤ wt u, wt v ≤ 4`, `0 ≤ q ≤ 5`,
`0 ≤ n ≤ 4`, `−6 ≤ ℓ ≤ −1` (4320 parameter sets) and `−60 ≤ j ≤ 12`: **0 failures**.
`certificates/mathematica/c2_scalar_final.wl` checks the closed scalar identity above and its two
sub-lemmas over `0 ≤ E ≤ 6`, `−12 ≤ P ≤ 12`, `−25 ≤ c ≤ 25`: **0 failures**, while the three
sharpness controls (drop the leftover / drop the skew family / shift `c` by one) produce 72, 150
and 216 mismatches.  Per C-16 the sweep carries two already-Lean-proved identities as self-tests
(`dj49_master`, `cbz_vandermonde`); both return 0.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References
Dong–Jiang math/0601626 §4 (Lemmas 4.8, 4.9), §2 (Lemmas 2.3, 2.4);
`ZhuVermaAnArchDJ49Star` (`DJ49Star`, `DJ49StarPrime`, `anmGenZ`, `resFull_offdiag_mem_Onm`,
`coeffFinsum_offdiag_mem_Onm`), `ZhuVermaAnArchDJ49Iterate` (`moduleIterate_of_dj49Star`),
`ZhuVermaAnArchResSkew` (`resFull`, `resHom_eq_resFull`, `resHom_skew_mod_Onm`,
`finsetSum_smul_resFull`, `finsum_finsetSum_comm'`, `sgn_add`), `ZhuVermaAnArchDJ48`
(`alt_cbz_eq`, `range_to_intFinsum`), `Foundations/IotaZExpansion` (`cbz_vandermonde`,
`cbz_zero_left`), `ZhuMuIdentity` (`ZhuMu.cbz_symm`).
-/

namespace VOA

open VertexOperatorAlgebra
open VHat VHat.VHatRep
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §1  Sign bookkeeping -/

/-- `negOnePow` and `sgn` are the same function (both `if Even n then 1 else -1`). -/
theorem negOnePow_eq_sgn (x : ℤ) : negOnePow x = sgn x := rfl

/-- `(-1)^{a+b} = (-1)^a·(-1)^b`. -/
theorem negOnePow_add' (a b : ℤ) : negOnePow (a + b) = negOnePow a * negOnePow b := by
  simpa only [negOnePow_eq_sgn] using sgn_add a b

/-- `(-1)^{x+2} = (-1)^x`. -/
theorem negOnePow_add_two (x : ℤ) : negOnePow (x + 2) = negOnePow x := by
  rw [negOnePow_add', show negOnePow 2 = 1 from by norm_num [negOnePow], mul_one]

/-- `(-1)^k · (-1)^k = 1` for a natural exponent. -/
theorem dj49c2_sq_sign (k : ℕ) : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
  rw [← pow_add, show k + k = 2 * k from by ring, pow_mul]
  norm_num

/-! ## §2  Two `Finset` reindexing helpers and the triangular reindex -/

/-- Shifting the summation variable of a guarded `range`-sum. -/
theorem dj49c2_shift_sum {X : Type*} [AddCommMonoid X] (T i : ℕ) (hi : i ≤ T) (g : ℕ → X) :
    (∑ w ∈ Finset.range (T + 1), if i ≤ w then g (w - i) else 0)
      = ∑ s ∈ Finset.range (T + 1 - i), g s := by
  classical
  have hsplit : (∑ w ∈ Finset.range (T + 1), if i ≤ w then g (w - i) else 0)
      = (∑ w ∈ Finset.Ico 0 i, if i ≤ w then g (w - i) else 0)
        + ∑ w ∈ Finset.Ico i (T + 1), if i ≤ w then g (w - i) else 0 := by
    rw [Finset.sum_Ico_consecutive _ (Nat.zero_le i) (by omega : i ≤ T + 1),
      ← Finset.range_eq_Ico]
  rw [hsplit,
    Finset.sum_eq_zero (s := Finset.Ico 0 i)
      (fun w hw => by rw [Finset.mem_Ico] at hw; exact if_neg (by omega)),
    zero_add, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [if_pos (by omega)]
  congr 1
  omega

/-- Truncating a guarded `range`-sum. -/
theorem dj49c2_cut_sum {X : Type*} [AddCommMonoid X] (T w : ℕ) (hw : w ≤ T) (g : ℕ → X) :
    (∑ i ∈ Finset.range (T + 1), if i ≤ w then g i else 0)
      = ∑ i ∈ Finset.range (w + 1), g i := by
  classical
  have hsplit : (∑ i ∈ Finset.range (T + 1), if i ≤ w then g i else 0)
      = (∑ i ∈ Finset.Ico 0 (w + 1), if i ≤ w then g i else 0)
        + ∑ i ∈ Finset.Ico (w + 1) (T + 1), if i ≤ w then g i else 0 := by
    rw [Finset.sum_Ico_consecutive _ (Nat.zero_le (w + 1)) (by omega : w + 1 ≤ T + 1),
      ← Finset.range_eq_Ico]
  rw [hsplit,
    Finset.sum_eq_zero (s := Finset.Ico (w + 1) (T + 1))
      (fun i hi => by rw [Finset.mem_Ico] at hi; exact if_neg (by omega)),
    add_zero, ← Finset.range_eq_Ico]
  exact Finset.sum_congr rfl fun i hi => by
    rw [Finset.mem_range] at hi; rw [if_pos (by omega)]

/-- **The triangular reindex** `(i, s) ↦ (w, i)` with `w = i + s`. -/
theorem dj49c2_triangle {X : Type*} [AddCommMonoid X] (T : ℕ) (f : ℕ → ℕ → X) :
    (∑ i ∈ Finset.range (T + 1), ∑ s ∈ Finset.range (T + 1 - i), f i s)
      = ∑ w ∈ Finset.range (T + 1), ∑ i ∈ Finset.range (w + 1), f i (w - i) := by
  classical
  have h1 : ∀ i ∈ Finset.range (T + 1),
      (∑ s ∈ Finset.range (T + 1 - i), f i s)
        = ∑ w ∈ Finset.range (T + 1), if i ≤ w then f i (w - i) else 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    exact (dj49c2_shift_sum T i (by omega) (fun s => f i s)).symm
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Finset.mem_range] at hw
  exact dj49c2_cut_sum T w (by omega) (fun i => f i (w - i))

/-- A module-valued `ℤ`-`finsum` supported in `[0, R)` is the corresponding `range` sum. -/
theorem dj49c2_intFinsum_to_range (R : ℕ) (F : ℤ → 𝒱)
    (hneg : ∀ x : ℤ, x < 0 → F x = 0) (htop : ∀ x : ℤ, (R : ℤ) ≤ x → F x = 0) :
    (∑ᶠ x : ℤ, F x) = ∑ k ∈ Finset.range R, F (k : ℤ) := by
  have hsub : (Function.support fun k : ℕ => F (k : ℤ)) ⊆ ↑(Finset.range R) := by
    intro k hk
    rw [Function.mem_support] at hk
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hcon
    push_neg at hcon
    exact hk (htop (k : ℤ) (by exact_mod_cast hcon))
  rw [← finsum_nat_to_int (fun k : ℕ => F (k : ℤ)) F hneg (fun _ => rfl)]
  exact finsum_eq_sum_of_support_subset _ hsub

/-- A `ℂ`-valued `range` sum, as a `ℤ`-`finsum`. -/
theorem dj49c2_range_to_finsum (R : ℕ) (G : ℤ → ℂ)
    (hGneg : ∀ x : ℤ, x < 0 → G x = 0) (hGtop : ∀ x : ℤ, (R : ℤ) ≤ x → G x = 0) :
    (∑ k ∈ Finset.range R, G (k : ℤ)) = ∑ᶠ x : ℤ, G x := by
  cases R with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty]
    refine (finsum_eq_zero_of_forall_eq_zero fun x => ?_).symm
    rcases lt_or_ge x 0 with hx | hx
    · exact hGneg x hx
    · exact hGtop x (by exact_mod_cast hx)
  | succ R =>
    exact range_to_intFinsum R R le_rfl G (fun x hx => by
      rcases hx with hx | hx
      · exact hGneg x hx
      · exact hGtop x (by push_cast at hx ⊢; omega))

/-! ## §3  The Vandermonde workhorses -/

/-- **The inner Vandermonde of the alternating sum**:
`∑_{i=0}^{w} (−1)ⁱ C(ℓ,i)·C(−Z−i−1, w−i) = (−1)^w · C(ℓ+Z+w, w)`. -/
theorem dj49c2_inner_vand (Z ℓ : ℤ) (w : ℕ) :
    (∑ i ∈ Finset.range (w + 1),
        ((-1 : ℂ) ^ i * cbz ℓ (i : ℤ)) * cbz (-(Z + (i : ℤ)) - 1) ((w - i : ℕ) : ℤ))
      = (-1 : ℂ) ^ w * cbz (ℓ + Z + (w : ℤ)) (w : ℤ) := by
  have hterm : ∀ i ∈ Finset.range (w + 1),
      ((-1 : ℂ) ^ i * cbz ℓ (i : ℤ)) * cbz (-(Z + (i : ℤ)) - 1) ((w - i : ℕ) : ℤ)
        = (-1 : ℂ) ^ w * (cbz ℓ (i : ℤ) * cbz (Z + (w : ℤ)) ((w : ℤ) - (i : ℤ))) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hiw : i ≤ w := by omega
    have hcast : ((w - i : ℕ) : ℤ) = (w : ℤ) - (i : ℤ) := by rw [Nat.cast_sub hiw]
    have hcbz : cbz (-(Z + (i : ℤ)) - 1) ((w : ℤ) - (i : ℤ))
        = (-1 : ℂ) ^ (w - i) * cbz (Z + (w : ℤ)) ((w : ℤ) - (i : ℤ)) := by
      have halt := alt_cbz_eq (Z + (i : ℤ)) (w - i)
      rw [hcast, show (Z + (i : ℤ)) + ((w : ℤ) - (i : ℤ)) = Z + (w : ℤ) from by ring] at halt
      rw [← halt]
    have hsign : (-1 : ℂ) ^ i * (-1 : ℂ) ^ (w - i) = (-1 : ℂ) ^ w := by
      rw [← pow_add, show i + (w - i) = w from by omega]
    rw [hcast, hcbz, ← hsign]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  have hr := range_to_intFinsum w w le_rfl
    (fun x : ℤ => cbz ℓ x * cbz (Z + (w : ℤ)) ((w : ℤ) - x))
    (fun x hx => by
      show cbz ℓ x * cbz (Z + (w : ℤ)) ((w : ℤ) - x) = 0
      rcases hx with hx | hx
      · rw [cbz_apply_neg ℓ hx, zero_mul]
      · rw [cbz_apply_neg (Z + (w : ℤ)) (by omega : (w : ℤ) - x < 0), mul_zero])
  rw [hr]
  have hv := cbz_vandermonde ℓ (Z + (w : ℤ)) (w : ℤ)
  rw [cbzConvol] at hv
  rw [hv, show ℓ + (Z + (w : ℤ)) = ℓ + Z + (w : ℤ) from by ring]

/-- **`(S1)`** — the negative Vandermonde behind the skew family:
`∑_{w=0}^{E−1} C(P+w, w)·C(w−E, k) = (−1)^k·C(P+k+E, E−1)`. -/
theorem dj49c2_S1 (E : ℕ) (P : ℤ) (k : ℕ) :
    (∑ w ∈ Finset.range E, cbz (P + (w : ℤ)) (w : ℤ) * cbz ((w : ℤ) - (E : ℤ)) (k : ℤ))
      = (-1 : ℂ) ^ k * cbz (P + (k : ℤ) + (E : ℤ)) ((E : ℤ) - 1) := by
  rcases Nat.eq_zero_or_pos E with hE0 | hEpos
  · subst hE0
    rw [Finset.range_zero, Finset.sum_empty, Nat.cast_zero,
      cbz_apply_neg (P + (k : ℤ) + 0) (by norm_num), mul_zero]
  have hcastE1 : ((E - 1 : ℕ) : ℤ) = (E : ℤ) - 1 := by
    rw [Nat.cast_sub hEpos]; norm_num
  have hterm : ∀ w ∈ Finset.range E,
      cbz (P + (w : ℤ)) (w : ℤ) * cbz ((w : ℤ) - (E : ℤ)) (k : ℤ)
        = ((-1 : ℂ) ^ k * (-1 : ℂ) ^ (E - 1))
          * (cbz (-P - 1) (w : ℤ) * cbz (-(k : ℤ) - 1) ((E : ℤ) - 1 - (w : ℤ))) := by
    intro w hw
    rw [Finset.mem_range] at hw
    have hwE : w ≤ E - 1 := by omega
    have h1 : cbz (P + (w : ℤ)) (w : ℤ) = (-1 : ℂ) ^ w * cbz (-P - 1) (w : ℤ) := by
      have h := alt_cbz_eq P w
      calc cbz (P + (w : ℤ)) (w : ℤ)
          = ((-1 : ℂ) ^ w * (-1 : ℂ) ^ w) * cbz (P + (w : ℤ)) (w : ℤ) := by
            rw [dj49c2_sq_sign w, one_mul]
        _ = (-1 : ℂ) ^ w * ((-1 : ℂ) ^ w * cbz (P + (w : ℤ)) (w : ℤ)) := by ring
        _ = (-1 : ℂ) ^ w * cbz (-P - 1) (w : ℤ) := by rw [h]
    have hcastW : ((E - 1 - w : ℕ) : ℤ) = (E : ℤ) - 1 - (w : ℤ) := by
      rw [Nat.cast_sub hwE, hcastE1]
    have hcastT : ((E - 1 - w + k : ℕ) : ℤ) = (E : ℤ) - 1 - (w : ℤ) + (k : ℤ) := by
      push_cast [hcastW]; ring
    have h2 : cbz ((w : ℤ) - (E : ℤ)) (k : ℤ)
        = (-1 : ℂ) ^ k * cbz ((E : ℤ) - 1 - (w : ℤ) + (k : ℤ)) (k : ℤ) := by
      have h := alt_cbz_eq ((E : ℤ) - 1 - (w : ℤ)) k
      rw [show -((E : ℤ) - 1 - (w : ℤ)) - 1 = (w : ℤ) - (E : ℤ) from by ring] at h
      rw [← h]
    have h3 : cbz ((E : ℤ) - 1 - (w : ℤ) + (k : ℤ)) (k : ℤ)
        = cbz ((E : ℤ) - 1 - (w : ℤ) + (k : ℤ)) ((E : ℤ) - 1 - (w : ℤ)) := by
      rw [← hcastT, ZhuMu.cbz_symm (E - 1 - w + k) (k : ℤ), hcastT,
        show (E : ℤ) - 1 - (w : ℤ) + (k : ℤ) - (k : ℤ) = (E : ℤ) - 1 - (w : ℤ) from by ring]
    have h4 : cbz ((E : ℤ) - 1 - (w : ℤ) + (k : ℤ)) ((E : ℤ) - 1 - (w : ℤ))
        = (-1 : ℂ) ^ (E - 1 - w) * cbz (-(k : ℤ) - 1) ((E : ℤ) - 1 - (w : ℤ)) := by
      have h := alt_cbz_eq (k : ℤ) (E - 1 - w)
      rw [hcastW, show (k : ℤ) + ((E : ℤ) - 1 - (w : ℤ))
        = (E : ℤ) - 1 - (w : ℤ) + (k : ℤ) from by ring] at h
      calc cbz ((E : ℤ) - 1 - (w : ℤ) + (k : ℤ)) ((E : ℤ) - 1 - (w : ℤ))
          = ((-1 : ℂ) ^ (E - 1 - w) * (-1 : ℂ) ^ (E - 1 - w))
              * cbz ((E : ℤ) - 1 - (w : ℤ) + (k : ℤ)) ((E : ℤ) - 1 - (w : ℤ)) := by
            rw [dj49c2_sq_sign (E - 1 - w), one_mul]
        _ = (-1 : ℂ) ^ (E - 1 - w) * ((-1 : ℂ) ^ (E - 1 - w)
              * cbz ((E : ℤ) - 1 - (w : ℤ) + (k : ℤ)) ((E : ℤ) - 1 - (w : ℤ))) := by ring
        _ = (-1 : ℂ) ^ (E - 1 - w) * cbz (-(k : ℤ) - 1) ((E : ℤ) - 1 - (w : ℤ)) := by rw [h]
    have hsignsplit : (-1 : ℂ) ^ w * (-1 : ℂ) ^ (E - 1 - w) = (-1 : ℂ) ^ (E - 1) := by
      rw [← pow_add, show w + (E - 1 - w) = E - 1 from by omega]
    rw [h1, h2, h3, h4, ← hsignsplit]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hr := range_to_intFinsum (E - 1) (E - 1) le_rfl
    (fun x : ℤ => cbz (-P - 1) x * cbz (-(k : ℤ) - 1) ((E : ℤ) - 1 - x))
    (fun x hx => by
      show cbz (-P - 1) x * cbz (-(k : ℤ) - 1) ((E : ℤ) - 1 - x) = 0
      rcases hx with hx | hx
      · rw [cbz_apply_neg (-P - 1) hx, zero_mul]
      · rw [cbz_apply_neg (-(k : ℤ) - 1)
          (by rw [hcastE1] at hx; omega : (E : ℤ) - 1 - x < 0), mul_zero])
  rw [show E - 1 + 1 = E from by omega] at hr
  rw [hr]
  have hv := cbz_vandermonde (-P - 1) (-(k : ℤ) - 1) ((E : ℤ) - 1)
  rw [cbzConvol] at hv
  rw [hv]
  have h := alt_cbz_eq (P + (k : ℤ) + 1) (E - 1)
  rw [hcastE1, show (P + (k : ℤ) + 1) + ((E : ℤ) - 1) = P + (k : ℤ) + (E : ℤ) from by ring,
    show -(P + (k : ℤ) + 1) - 1 = -P - 1 + (-(k : ℤ) - 1) from by ring] at h
  rw [← h, show ((-1 : ℂ) ^ k * (-1 : ℂ) ^ (E - 1))
        * ((-1 : ℂ) ^ (E - 1) * cbz (P + (k : ℤ) + (E : ℤ)) ((E : ℤ) - 1))
      = ((-1 : ℂ) ^ (E - 1) * (-1 : ℂ) ^ (E - 1))
        * ((-1 : ℂ) ^ k * cbz (P + (k : ℤ) + (E : ℤ)) ((E : ℤ) - 1)) from by ring,
    dj49c2_sq_sign (E - 1), one_mul]

/-- **`(S2)`** — the leftover coefficient vanishes once `P + k ≥ 0`. -/
theorem dj49c2_S2 (E : ℕ) (P k : ℤ) (h : 0 ≤ P + k) :
    cbz (-(E : ℤ)) (P + 1 + k)
        + negOnePow (P + k) * cbz (P + k + (E : ℤ)) ((E : ℤ) - 1) = 0 := by
  obtain ⟨G, hG⟩ : ∃ G : ℕ, P + k = (G : ℤ) := ⟨_, (Int.toNat_of_nonneg h).symm⟩
  have hR : P + 1 + k = ((G + 1 : ℕ) : ℤ) := by push_cast; omega
  have hT : P + k + (E : ℤ) = ((E + G : ℕ) : ℤ) := by push_cast; omega
  have halt := alt_cbz_eq ((E : ℤ) - 1) (G + 1)
  rw [show -((E : ℤ) - 1) - 1 = -(E : ℤ) from by ring,
    show ((E : ℤ) - 1) + ((G + 1 : ℕ) : ℤ) = ((E + G : ℕ) : ℤ) from by push_cast; ring] at halt
  have hsymm : cbz ((E + G : ℕ) : ℤ) ((G + 1 : ℕ) : ℤ)
      = cbz ((E + G : ℕ) : ℤ) ((E : ℤ) - 1) := by
    rw [ZhuMu.cbz_symm (E + G) ((G + 1 : ℕ) : ℤ),
      show ((E + G : ℕ) : ℤ) - ((G + 1 : ℕ) : ℤ) = (E : ℤ) - 1 from by push_cast; ring]
  rw [hR, ← halt, hT, hsymm, hG, negOnePow_natCast, pow_succ]
  ring

/-! ## §4  The scalar core of Dong–Jiang Lemma 4.9 -/

/-- The leftover coefficient `d_k = C(−E, P+1+k) + (−1)^{P+k}·C(P+k+E, E−1)`. -/
noncomputable def dj49Leftover (E : ℕ) (P : ℤ) (k : ℕ) : ℂ :=
  cbz (-(E : ℤ)) (P + 1 + (k : ℤ))
    + negOnePow (P + (k : ℤ)) * cbz (P + (k : ℤ) + (E : ℤ)) ((E : ℤ) - 1)

/-- The generator `C(E, c−k)` vanishes off the window `[c−E, c]`. -/
theorem dj49c2_cbz_win (E : ℕ) (c k : ℤ) (h : k < c - (E : ℤ) ∨ c < k) :
    cbz (E : ℤ) (c - k) = 0 := by
  rcases h with h | h
  · exact cbz_lt (by positivity) (by omega)
  · exact cbz_apply_neg (E : ℤ) (by omega)

/-- Anything vanishing off the window `[c−E, c]` has finite support. -/
theorem dj49c2_win_finite (E : ℕ) (c : ℤ) (F : ℤ → ℂ)
    (hF : ∀ k : ℤ, k < c - (E : ℤ) ∨ c < k → F k = 0) : (Function.support F).Finite := by
  refine Set.Finite.subset (Set.finite_Icc (c - (E : ℤ)) c) ?_
  intro k hk
  rw [Function.mem_support] at hk
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · by_contra h; push_neg at h; exact hk (hF k (Or.inl h))
  · by_contra h; push_neg at h; exact hk (hF k (Or.inr h))

/-- Four `k`-`finsum`s against `C(E, c−k)` with identically vanishing total summand cancel. -/
theorem dj49c2_four (E : ℕ) (c : ℤ) (a b g d : ℤ → ℂ)
    (h : ∀ k : ℤ, a k - b k + g k - d k = 0) :
    (∑ᶠ k : ℤ, a k * cbz (E : ℤ) (c - k)) - (∑ᶠ k : ℤ, b k * cbz (E : ℤ) (c - k))
        + (∑ᶠ k : ℤ, g k * cbz (E : ℤ) (c - k)) - (∑ᶠ k : ℤ, d k * cbz (E : ℤ) (c - k)) = 0 := by
  have hf : ∀ f : ℤ → ℂ,
      (Function.support fun k : ℤ => f k * cbz (E : ℤ) (c - k)).Finite := fun f =>
    dj49c2_win_finite E c _ (fun k hk => by rw [dj49c2_cbz_win E c k hk, mul_zero])
  have hab : (Function.support fun k : ℤ =>
      a k * cbz (E : ℤ) (c - k) - b k * cbz (E : ℤ) (c - k)).Finite :=
    dj49c2_win_finite E c _ (fun k hk => by rw [dj49c2_cbz_win E c k hk]; ring)
  have habg : (Function.support fun k : ℤ =>
      a k * cbz (E : ℤ) (c - k) - b k * cbz (E : ℤ) (c - k)
        + g k * cbz (E : ℤ) (c - k)).Finite :=
    dj49c2_win_finite E c _ (fun k hk => by rw [dj49c2_cbz_win E c k hk]; ring)
  rw [← finsum_sub_distrib (hf a) (hf b), ← finsum_add_distrib hab (hf g),
    ← finsum_sub_distrib habg (hf d)]
  refine finsum_eq_zero_of_forall_eq_zero fun k => ?_
  have hk := h k
  linear_combination cbz (E : ℤ) (c - k) * hk

/-- **THE SCALAR CORE OF DONG–JIANG LEMMA 4.9.**  For every `E : ℕ` and `P c : ℤ`,

`[c = −P−1] − ∑_{w<P+1} C(−E,w)·C(E,c+P+1−w) + (−1)^P·∑_{w<E} C(P+w,w)·C(w,c)`
`  = ∑_{k<−P} d_k · C(E, c−k)`,   `d_k = C(−E,P+1+k) + (−1)^{P+k}·C(P+k+E,E−1)`.

Engine-verified over `0 ≤ E ≤ 6`, `−12 ≤ P ≤ 12`, `−25 ≤ c ≤ 25` with three sharpness controls
firing (module docstring). -/
theorem dj49c2_scalar (E : ℕ) (P c : ℤ) :
    (if c = -P - 1 then (1 : ℂ) else 0)
        - (∑ w ∈ Finset.range (P + 1).toNat,
            cbz (-(E : ℤ)) (w : ℤ) * cbz (E : ℤ) (c + P + 1 - (w : ℤ)))
        + negOnePow P * (∑ w ∈ Finset.range E, cbz (P + (w : ℤ)) (w : ℤ) * cbz (w : ℤ) c)
      = ∑ k ∈ Finset.range (-P).toNat, dj49Leftover E P k * cbz (E : ℤ) (c - (k : ℤ)) := by
  classical
  -- (1) the Kronecker delta, as a convolution against the generator family
  have h1 : (if c = -P - 1 then (1 : ℂ) else 0)
      = ∑ᶠ k : ℤ, cbz (-(E : ℤ)) (P + 1 + k) * cbz (E : ℤ) (c - k) := by
    have hv := cbz_vandermonde (-(E : ℤ)) (E : ℤ) (c + P + 1)
    rw [cbzConvol, show (-(E : ℤ) + (E : ℤ)) = 0 from by ring, cbz_zero_left] at hv
    have hshift : (∑ᶠ k : ℤ, cbz (-(E : ℤ)) (P + 1 + k) * cbz (E : ℤ) (c - k))
        = ∑ᶠ w : ℤ, cbz (-(E : ℤ)) w * cbz (E : ℤ) ((c + P + 1) - w) := by
      rw [← finsum_comp_equiv (Equiv.addLeft (P + 1))
        (f := fun w : ℤ => cbz (-(E : ℤ)) w * cbz (E : ℤ) ((c + P + 1) - w))]
      refine finsum_congr fun k => ?_
      show cbz (-(E : ℤ)) (P + 1 + k) * cbz (E : ℤ) (c - k)
        = cbz (-(E : ℤ)) (P + 1 + k) * cbz (E : ℤ) ((c + P + 1) - (P + 1 + k))
      rw [show (c + P + 1) - (P + 1 + k) = c - k from by ring]
    rw [hshift, hv]
    by_cases hc : c = -P - 1
    · rw [if_pos hc, if_pos (by omega)]
    · rw [if_neg hc, if_neg (by omega)]
  -- (2) the truncated `A`-family
  have h2 : (∑ w ∈ Finset.range (P + 1).toNat,
        cbz (-(E : ℤ)) (w : ℤ) * cbz (E : ℤ) (c + P + 1 - (w : ℤ)))
      = ∑ᶠ k : ℤ, (if k < 0 then cbz (-(E : ℤ)) (P + 1 + k) else 0) * cbz (E : ℤ) (c - k) := by
    have hG := dj49c2_range_to_finsum (P + 1).toNat
      (fun x : ℤ => (if x < P + 1 then cbz (-(E : ℤ)) x else 0) * cbz (E : ℤ) (c + P + 1 - x))
      (fun x hx => by
        show (if x < P + 1 then cbz (-(E : ℤ)) x else 0) * cbz (E : ℤ) (c + P + 1 - x) = 0
        by_cases hlt : x < P + 1
        · rw [if_pos hlt, cbz_apply_neg (-(E : ℤ)) hx, zero_mul]
        · rw [if_neg hlt, zero_mul])
      (fun x hx => by
        show (if x < P + 1 then cbz (-(E : ℤ)) x else 0) * cbz (E : ℤ) (c + P + 1 - x) = 0
        rw [if_neg (by omega), zero_mul])
    have hLHS : (∑ w ∈ Finset.range (P + 1).toNat,
          cbz (-(E : ℤ)) (w : ℤ) * cbz (E : ℤ) (c + P + 1 - (w : ℤ)))
        = ∑ w ∈ Finset.range (P + 1).toNat,
            (if (w : ℤ) < P + 1 then cbz (-(E : ℤ)) (w : ℤ) else 0)
              * cbz (E : ℤ) (c + P + 1 - (w : ℤ)) := by
      refine Finset.sum_congr rfl fun w hw => ?_
      rw [Finset.mem_range] at hw
      rw [if_pos (by omega)]
    rw [hLHS, hG,
      ← finsum_comp_equiv (Equiv.subRight (P + 1))
        (f := fun k : ℤ =>
          (if k < 0 then cbz (-(E : ℤ)) (P + 1 + k) else 0) * cbz (E : ℤ) (c - k))]
    refine finsum_congr fun x => ?_
    show (if x < P + 1 then cbz (-(E : ℤ)) x else 0) * cbz (E : ℤ) (c + P + 1 - x)
      = (if x - (P + 1) < 0 then cbz (-(E : ℤ)) (P + 1 + (x - (P + 1))) else 0)
          * cbz (E : ℤ) (c - (x - (P + 1)))
    rw [show P + 1 + (x - (P + 1)) = x from by ring,
      show c - (x - (P + 1)) = c + P + 1 - x from by ring]
    by_cases hlt : x < P + 1
    · rw [if_pos hlt, if_pos (by omega)]
    · rw [if_neg hlt, if_neg (by omega)]
  -- (3) the skew family
  have h3 : negOnePow P * (∑ w ∈ Finset.range E,
        cbz (P + (w : ℤ)) (w : ℤ) * cbz (w : ℤ) c)
      = ∑ᶠ k : ℤ, (negOnePow P * ∑ w ∈ Finset.range E,
          cbz (P + (w : ℤ)) (w : ℤ) * cbz ((w : ℤ) - (E : ℤ)) k) * cbz (E : ℤ) (c - k) := by
    have hfin : ∀ w ∈ Finset.range E, (Function.support fun k : ℤ =>
        negOnePow P * (cbz (P + (w : ℤ)) (w : ℤ) * cbz ((w : ℤ) - (E : ℤ)) k)
          * cbz (E : ℤ) (c - k)).Finite := fun w _ =>
      dj49c2_win_finite E c _ (fun k hk => by rw [dj49c2_cbz_win E c k hk, mul_zero])
    have hswap : (∑ᶠ k : ℤ, ∑ w ∈ Finset.range E,
          negOnePow P * (cbz (P + (w : ℤ)) (w : ℤ) * cbz ((w : ℤ) - (E : ℤ)) k)
            * cbz (E : ℤ) (c - k))
        = ∑ w ∈ Finset.range E, ∑ᶠ k : ℤ,
          negOnePow P * (cbz (P + (w : ℤ)) (w : ℤ) * cbz ((w : ℤ) - (E : ℤ)) k)
            * cbz (E : ℤ) (c - k) :=
      finsum_finsetSum_comm' (𝒱 := ℂ) (Finset.range E) _ hfin
    have hinner : ∀ w : ℕ, (∑ᶠ k : ℤ,
          negOnePow P * (cbz (P + (w : ℤ)) (w : ℤ) * cbz ((w : ℤ) - (E : ℤ)) k)
            * cbz (E : ℤ) (c - k))
        = negOnePow P * (cbz (P + (w : ℤ)) (w : ℤ) * cbz (w : ℤ) c) := by
      intro w
      have hv := cbz_vandermonde ((w : ℤ) - (E : ℤ)) (E : ℤ) c
      rw [cbzConvol, show ((w : ℤ) - (E : ℤ) + (E : ℤ)) = (w : ℤ) from by ring] at hv
      rw [← hv, mul_finsum, mul_finsum]
      refine finsum_congr fun k => ?_
      ring
    calc negOnePow P * (∑ w ∈ Finset.range E, cbz (P + (w : ℤ)) (w : ℤ) * cbz (w : ℤ) c)
        = ∑ w ∈ Finset.range E, negOnePow P * (cbz (P + (w : ℤ)) (w : ℤ) * cbz (w : ℤ) c) := by
          rw [Finset.mul_sum]
      _ = ∑ w ∈ Finset.range E, ∑ᶠ k : ℤ,
            negOnePow P * (cbz (P + (w : ℤ)) (w : ℤ) * cbz ((w : ℤ) - (E : ℤ)) k)
              * cbz (E : ℤ) (c - k) := Finset.sum_congr rfl fun w _ => (hinner w).symm
      _ = ∑ᶠ k : ℤ, ∑ w ∈ Finset.range E,
            negOnePow P * (cbz (P + (w : ℤ)) (w : ℤ) * cbz ((w : ℤ) - (E : ℤ)) k)
              * cbz (E : ℤ) (c - k) := hswap.symm
      _ = ∑ᶠ k : ℤ, (negOnePow P * ∑ w ∈ Finset.range E,
            cbz (P + (w : ℤ)) (w : ℤ) * cbz ((w : ℤ) - (E : ℤ)) k) * cbz (E : ℤ) (c - k) := by
          refine finsum_congr fun k => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
  -- (4) the leftover
  have h4 : (∑ k ∈ Finset.range (-P).toNat, dj49Leftover E P k * cbz (E : ℤ) (c - (k : ℤ)))
      = ∑ᶠ k : ℤ, (if 0 ≤ k ∧ k < -P then dj49Leftover E P k.toNat else 0)
          * cbz (E : ℤ) (c - k) := by
    have hG := dj49c2_range_to_finsum (-P).toNat
      (fun x : ℤ => (if 0 ≤ x ∧ x < -P then dj49Leftover E P x.toNat else 0)
        * cbz (E : ℤ) (c - x))
      (fun x hx => by
        show (if 0 ≤ x ∧ x < -P then dj49Leftover E P x.toNat else 0)
          * cbz (E : ℤ) (c - x) = 0
        rw [if_neg (by omega), zero_mul])
      (fun x hx => by
        show (if 0 ≤ x ∧ x < -P then dj49Leftover E P x.toNat else 0)
          * cbz (E : ℤ) (c - x) = 0
        rw [if_neg (by omega), zero_mul])
    rw [← hG]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    show dj49Leftover E P k * cbz (E : ℤ) (c - (k : ℤ))
      = (if 0 ≤ (k : ℤ) ∧ (k : ℤ) < -P then dj49Leftover E P (k : ℤ).toNat else 0)
        * cbz (E : ℤ) (c - (k : ℤ))
    rw [if_pos (⟨by positivity, by omega⟩ : 0 ≤ (k : ℤ) ∧ (k : ℤ) < -P), Int.toNat_natCast]
  -- assemble
  rw [h1, h2, h3, h4]
  have hpt : ∀ k : ℤ,
      cbz (-(E : ℤ)) (P + 1 + k)
        - (if k < 0 then cbz (-(E : ℤ)) (P + 1 + k) else 0)
        + (negOnePow P * ∑ w ∈ Finset.range E,
            cbz (P + (w : ℤ)) (w : ℤ) * cbz ((w : ℤ) - (E : ℤ)) k)
        - (if 0 ≤ k ∧ k < -P then dj49Leftover E P k.toNat else 0) = 0 := by
    intro k
    rcases lt_or_ge k 0 with hk | hk
    · have hz : (∑ w ∈ Finset.range E,
          cbz (P + (w : ℤ)) (w : ℤ) * cbz ((w : ℤ) - (E : ℤ)) k) = 0 :=
        Finset.sum_eq_zero fun w _ => by
          rw [cbz_apply_neg ((w : ℤ) - (E : ℤ)) hk, mul_zero]
      rw [if_pos hk, hz, mul_zero, if_neg (by omega)]
      ring
    · obtain ⟨K0, hK0⟩ : ∃ K0 : ℕ, k = (K0 : ℤ) := ⟨_, (Int.toNat_of_nonneg hk).symm⟩
      have hS1 := dj49c2_S1 E P K0
      rw [← hK0] at hS1
      have hg : negOnePow P * (∑ w ∈ Finset.range E,
          cbz (P + (w : ℤ)) (w : ℤ) * cbz ((w : ℤ) - (E : ℤ)) k)
          = negOnePow (P + k) * cbz (P + k + (E : ℤ)) ((E : ℤ) - 1) := by
        rw [hS1, negOnePow_add', hK0, negOnePow_natCast]
        ring
      rw [if_neg (by omega : ¬ k < 0), hg]
      by_cases hk2 : k < -P
      · rw [if_pos ⟨hk, hk2⟩, dj49Leftover, hK0, Int.toNat_natCast, ← hK0]
        ring
      · rw [if_neg (by omega)]
        have hS2 := dj49c2_S2 E P k (by omega)
        linear_combination hS2
  have hfour := dj49c2_four E c
    (fun k => cbz (-(E : ℤ)) (P + 1 + k))
    (fun k => if k < 0 then cbz (-(E : ℤ)) (P + 1 + k) else 0)
    (fun k => negOnePow P * ∑ w ∈ Finset.range E,
      cbz (P + (w : ℤ)) (w : ℤ) * cbz ((w : ℤ) - (E : ℤ)) k)
    (fun k => if 0 ≤ k ∧ k < -P then dj49Leftover E P k.toNat else 0) hpt
  linear_combination hfour

/-- The scalar core in the `j`-variable actually used by `(★)`. -/
theorem dj49c2_scalar_j (E : ℕ) (P A₀ B₀ Q ℓ j : ℤ)
    (hA₀ : A₀ = (E : ℤ) - ℓ - 1) (hB₀ : B₀ = P - ℓ) (hQ : Q = A₀ + P + 2) :
    (if j = ℓ then (1 : ℂ) else 0)
        - (∑ w ∈ Finset.range (P + 1).toNat,
            cbz (-(E : ℤ)) (w : ℤ) * cbz (E : ℤ) (j + (A₀ + (w : ℤ) + 1)))
        + (∑ w ∈ Finset.range E,
            (negOnePow P * cbz (P + (w : ℤ)) (w : ℤ)) * cbz (w : ℤ) (j + (B₀ + (w : ℤ) + 1)))
      = ∑ k ∈ Finset.range (-P).toNat,
          dj49Leftover E P k * cbz (E : ℤ) (j + (Q + (k : ℤ))) := by
  have h := dj49c2_scalar E P (ℓ - P - 1 - j)
  have hδ : (if j = ℓ then (1 : ℂ) else 0)
      = (if ℓ - P - 1 - j = -P - 1 then (1 : ℂ) else 0) := by
    by_cases hj : j = ℓ
    · rw [if_pos hj, if_pos (by omega)]
    · rw [if_neg hj, if_neg (by omega)]
  have hAsum : (∑ w ∈ Finset.range (P + 1).toNat,
        cbz (-(E : ℤ)) (w : ℤ) * cbz (E : ℤ) (j + (A₀ + (w : ℤ) + 1)))
      = ∑ w ∈ Finset.range (P + 1).toNat,
          cbz (-(E : ℤ)) (w : ℤ) * cbz (E : ℤ) ((ℓ - P - 1 - j) + P + 1 - (w : ℤ)) :=
    Finset.sum_congr rfl fun w _ => by
      rw [ZhuMu.cbz_symm E (j + (A₀ + (w : ℤ) + 1)),
        show (E : ℤ) - (j + (A₀ + (w : ℤ) + 1)) = (ℓ - P - 1 - j) + P + 1 - (w : ℤ) from by
          rw [hA₀]; ring]
  have hBsum : (∑ w ∈ Finset.range E,
        (negOnePow P * cbz (P + (w : ℤ)) (w : ℤ)) * cbz (w : ℤ) (j + (B₀ + (w : ℤ) + 1)))
      = negOnePow P * ∑ w ∈ Finset.range E,
          cbz (P + (w : ℤ)) (w : ℤ) * cbz (w : ℤ) (ℓ - P - 1 - j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [ZhuMu.cbz_symm w (j + (B₀ + (w : ℤ) + 1)),
      show (w : ℤ) - (j + (B₀ + (w : ℤ) + 1)) = ℓ - P - 1 - j from by rw [hB₀]; ring, mul_assoc]
  have hLsum : (∑ k ∈ Finset.range (-P).toNat,
        dj49Leftover E P k * cbz (E : ℤ) (j + (Q + (k : ℤ))))
      = ∑ k ∈ Finset.range (-P).toNat,
          dj49Leftover E P k * cbz (E : ℤ) ((ℓ - P - 1 - j) - (k : ℤ)) :=
    Finset.sum_congr rfl fun k _ => by
      rw [ZhuMu.cbz_symm E (j + (Q + (k : ℤ))),
        show (E : ℤ) - (j + (Q + (k : ℤ))) = (ℓ - P - 1 - j) - (k : ℤ) from by
          rw [hQ, hA₀]; ring]
  rw [hδ, hAsum, hBsum, hLsum]
  exact h

/-! ## §5  Collapsing the alternating Dong–Jiang sum to a single residue family -/

/-- `anmGen` expanded as a `Finset` combination of `resHom`s, with upper-index-negated weights. -/
theorem anmGen_eq_resHom_sum (W : VertexOperatorAlgebra 𝒱) (q n p : ℕ) (x y : 𝒱) :
    anmGen W q n p x y
      = ∑ s ∈ Finset.range (p + 1),
          cbz (-((n : ℤ) + (q : ℤ) - (p : ℤ)) - 1) (s : ℤ)
            • resHom W (n : ℤ) ((n : ℤ) + (q : ℤ) - (p : ℤ) + (s : ℤ) + 1) x y := by
  rw [anmGen]
  exact Finset.sum_congr rfl fun s _ => by rw [alt_cbz_eq ((n : ℤ) + (q : ℤ) - (p : ℤ)) s]

/-- **The collapse lemma.**  For every threshold `Λ : ℤ` and `Z = n + q − Λ`,

`∑ᵢ (−1)ⁱC(ℓ,i)·(x *^q_{n,Λ−i} y)`
`  = ∑_{w=0}^{Λ} (−1)^w C(ℓ+Z+w, w)·Res_z (1+z)^{wt x+n} z^{−Z−w−1} Y(x,z)y`

(the intermediate level is read through `anmGenZ`, so negative levels contribute `0`).  Both halves
of `(★)` are instances: `Λ = P` for the `u`-first family, `Λ = E − 1` for the `v`-first one. -/
theorem dj49c2_collapse (W : VertexOperatorAlgebra 𝒱) (n q : ℕ) (x y : 𝒱) (ℓ Λ : ℤ) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) • anmGenZ W q n (Λ - i) x y)
      = ∑ w ∈ Finset.range (Λ + 1).toNat,
          ((-1 : ℂ) ^ w * cbz (ℓ + ((n : ℤ) + (q : ℤ) - Λ) + (w : ℤ)) (w : ℤ))
            • resHom W (n : ℤ) (((n : ℤ) + (q : ℤ) - Λ) + (w : ℤ) + 1) x y := by
  classical
  rcases lt_or_ge Λ 0 with hΛ | hΛ
  · rw [show (Λ + 1).toNat = 0 from by omega, Finset.range_zero, Finset.sum_empty]
    refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
    rcases lt_or_ge i 0 with hi | hi
    · rw [cbz_apply_neg ℓ hi, mul_zero, zero_smul]
    · rw [anmGenZ_of_neg W q n (by omega : Λ - i < 0), smul_zero]
  obtain ⟨T, hT⟩ : ∃ T : ℕ, Λ = (T : ℤ) := ⟨_, (Int.toNat_of_nonneg hΛ).symm⟩
  have hrange : (Λ + 1).toNat = T + 1 := by omega
  rw [hrange, dj49c2_intFinsum_to_range (T + 1)
    (fun i : ℤ => (negOnePow i * cbz ℓ i) • anmGenZ W q n (Λ - i) x y)
    (fun i hi => by
      show (negOnePow i * cbz ℓ i) • anmGenZ W q n (Λ - i) x y = 0
      rw [cbz_apply_neg ℓ hi, mul_zero, zero_smul])
    (fun i hi => by
      show (negOnePow i * cbz ℓ i) • anmGenZ W q n (Λ - i) x y = 0
      rw [anmGenZ_of_neg W q n (by push_cast at hi; omega : Λ - i < 0), smul_zero])]
  have hexp : ∀ i ∈ Finset.range (T + 1),
      (negOnePow (i : ℤ) * cbz ℓ (i : ℤ)) • anmGenZ W q n (Λ - (i : ℤ)) x y
        = ∑ s ∈ Finset.range (T + 1 - i),
            (((-1 : ℂ) ^ i * cbz ℓ (i : ℤ))
                * cbz (-(((n : ℤ) + (q : ℤ) - Λ) + (i : ℤ)) - 1) (s : ℤ))
              • resHom W (n : ℤ)
                  (((n : ℤ) + (q : ℤ) - Λ) + (i : ℤ) + (s : ℤ) + 1) x y := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hiT : i ≤ T := by omega
    have hcast : ((T - i : ℕ) : ℤ) = Λ - (i : ℤ) := by rw [Nat.cast_sub hiT, hT]
    rw [anmGenZ_of_eq W q n hcast.symm x y, anmGen_eq_resHom_sum W q n (T - i) x y,
      Finset.smul_sum, negOnePow_natCast, show (T - i) + 1 = T + 1 - i from by omega]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [smul_smul, hcast]
    congr 2 <;> ring
  rw [Finset.sum_congr rfl hexp, dj49c2_triangle T (fun i s =>
    (((-1 : ℂ) ^ i * cbz ℓ (i : ℤ))
        * cbz (-(((n : ℤ) + (q : ℤ) - Λ) + (i : ℤ)) - 1) (s : ℤ))
      • resHom W (n : ℤ) (((n : ℤ) + (q : ℤ) - Λ) + (i : ℤ) + (s : ℤ) + 1) x y)]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Finset.mem_range] at hw
  have hinner : ∀ i ∈ Finset.range (w + 1),
      (((-1 : ℂ) ^ i * cbz ℓ (i : ℤ))
          * cbz (-(((n : ℤ) + (q : ℤ) - Λ) + (i : ℤ)) - 1) ((w - i : ℕ) : ℤ))
        • resHom W (n : ℤ)
            (((n : ℤ) + (q : ℤ) - Λ) + (i : ℤ) + ((w - i : ℕ) : ℤ) + 1) x y
      = (((-1 : ℂ) ^ i * cbz ℓ (i : ℤ))
          * cbz (-(((n : ℤ) + (q : ℤ) - Λ) + (i : ℤ)) - 1) ((w - i : ℕ) : ℤ))
        • resHom W (n : ℤ) (((n : ℤ) + (q : ℤ) - Λ) + (w : ℤ) + 1) x y := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hcast : ((w - i : ℕ) : ℤ) = (w : ℤ) - (i : ℤ) := by rw [Nat.cast_sub (by omega)]
    rw [hcast, show ((n : ℤ) + (q : ℤ) - Λ) + (i : ℤ) + ((w : ℤ) - (i : ℤ)) + 1
      = ((n : ℤ) + (q : ℤ) - Λ) + (w : ℤ) + 1 from by ring]
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_smul,
    dj49c2_inner_vand ((n : ℤ) + (q : ℤ) - Λ) ℓ w]

/-! ## §6  `(★)` -/

/-- Support finiteness for a coefficient-weighted family of modes. -/
theorem dj49c2_mode_finite (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (F : ℤ → 𝒱) (b : ℤ)
    (hlow : ∀ j : ℤ, j < b → F j = 0) (hhigh : ∀ j : ℤ, W.smul u j v = 0 → F j = 0) :
    (Function.support F).Finite := by
  obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero u v
  refine Set.Finite.subset (Set.finite_Icc b Nz) ?_
  intro j hj
  rw [Function.mem_support] at hj
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · by_contra h; push_neg at h; exact hj (hlow j h)
  · by_contra h; push_neg at h; exact hj (hhigh j (hNz j (by omega)))

/-- **`(★)` IS A THEOREM** — the pure-`𝒱` membership behind Dong–Jiang Lemma 4.9, in the
sharp (prime-ideal) form `DJ49StarPrime`.  No hypothesis, no axiom, pbw-free. -/
theorem dj49StarPrime_holds (W : VertexOperatorAlgebra 𝒱) : DJ49StarPrime W := by
  classical
  intro K M u v hu hv n q ℓ N hℓ hq
  set E : ℕ := K + n with hEdef
  have hEc : (E : ℤ) = (K : ℤ) + (n : ℤ) := by rw [hEdef]; push_cast; ring
  set P : ℤ := (M : ℤ) - N - 1 + (n : ℤ) with hPdef
  set A₀ : ℤ := (n : ℤ) + (q : ℤ) - P with hA₀def
  set B₀ : ℤ := (n : ℤ) + (q : ℤ) - ((E : ℤ) - 1) with hB₀def
  have hA₀ : A₀ = (E : ℤ) - ℓ - 1 := by rw [hA₀def, hPdef, hEc]; omega
  have hB₀ : B₀ = P - ℓ := by rw [hB₀def, hPdef, hEc]; omega
  -- (I) split the alternating sum into its two halves
  have hfinA : (Function.support fun i : ℤ =>
      (negOnePow i * cbz ℓ i) • anmGenZ W q n (P - i) u v).Finite := by
    refine Set.Finite.subset (Set.finite_Icc 0 P) ?_
    intro i hi
    rw [Function.mem_support] at hi
    rw [Set.mem_Icc]
    refine ⟨?_, ?_⟩
    · by_contra h; push_neg at h
      exact hi (by rw [cbz_apply_neg ℓ h, mul_zero, zero_smul])
    · by_contra h; push_neg at h
      exact hi (by rw [anmGenZ_of_neg W q n (by omega : P - i < 0), smul_zero])
  have hfinB : (Function.support fun i : ℤ =>
      (negOnePow i * cbz ℓ i) • anmGenZ W q n (((E : ℤ) - 1) - i) v u).Finite := by
    refine Set.Finite.subset (Set.finite_Icc 0 ((E : ℤ) - 1)) ?_
    intro i hi
    rw [Function.mem_support] at hi
    rw [Set.mem_Icc]
    refine ⟨?_, ?_⟩
    · by_contra h; push_neg at h
      exact hi (by rw [cbz_apply_neg ℓ h, mul_zero, zero_smul])
    · by_contra h; push_neg at h
      exact hi (by rw [anmGenZ_of_neg W q n (by omega : ((E : ℤ) - 1) - i < 0), smul_zero])
  have hfinB' : (Function.support fun i : ℤ =>
      negOnePow ℓ • ((negOnePow i * cbz ℓ i) • anmGenZ W q n (((E : ℤ) - 1) - i) v u)).Finite := by
    refine Set.Finite.subset hfinB ?_
    intro i hi
    rw [Function.mem_support] at hi ⊢
    intro h
    exact hi (by rw [h, smul_zero])
  have hsplit : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (anmGenZ W q n ((M : ℤ) - N - i - 1 + (n : ℤ)) u v
          - negOnePow ℓ • anmGenZ W q n ((K : ℤ) - i - 1 + (n : ℤ)) v u))
      = (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) • anmGenZ W q n (P - i) u v)
        - negOnePow ℓ • (∑ᶠ i : ℤ,
            (negOnePow i * cbz ℓ i) • anmGenZ W q n (((E : ℤ) - 1) - i) v u) := by
    rw [smul_finsum' (negOnePow ℓ) hfinB, ← finsum_sub_distrib hfinA hfinB']
    refine finsum_congr fun i => ?_
    rw [show (M : ℤ) - N - i - 1 + (n : ℤ) = P - i from by rw [hPdef]; ring,
      show (K : ℤ) - i - 1 + (n : ℤ) = ((E : ℤ) - 1) - i from by rw [hEc]; ring,
      smul_sub, smul_comm]
  rw [hsplit]
  -- (II) collapse both halves
  have hcolA := dj49c2_collapse W n q u v ℓ P
  have hcolB := dj49c2_collapse W n q v u ℓ ((E : ℤ) - 1)
  rw [← hA₀def] at hcolA
  rw [← hB₀def, show (((E : ℤ) - 1) + 1).toNat = E from by omega] at hcolB
  rw [hcolA, hcolB]
  -- (III) the `u`-family, as `resFull`s with the negated weight
  have hAfam : (∑ w ∈ Finset.range (P + 1).toNat,
        ((-1 : ℂ) ^ w * cbz (ℓ + A₀ + (w : ℤ)) (w : ℤ))
          • resHom W (n : ℤ) (A₀ + (w : ℤ) + 1) u v)
      = ∑ w ∈ Finset.range (P + 1).toNat,
          cbz (-(E : ℤ)) (w : ℤ) • resFull W ((K : ℤ) + (n : ℤ)) (A₀ + (w : ℤ) + 1) u v := by
    refine Finset.sum_congr rfl fun w _ => ?_
    have hco : (-1 : ℂ) ^ w * cbz (ℓ + A₀ + (w : ℤ)) (w : ℤ) = cbz (-(E : ℤ)) (w : ℤ) := by
      have h := alt_cbz_eq ((E : ℤ) - 1) w
      rw [show -((E : ℤ) - 1) - 1 = -(E : ℤ) from by ring] at h
      rw [show ℓ + A₀ + (w : ℤ) = ((E : ℤ) - 1) + (w : ℤ) from by rw [hA₀]; ring, h]
    rw [hco, resHom_eq_resFull W hu (A₀ + (w : ℤ) + 1) v]
  rw [hAfam]
  -- (IV) the skew family
  set SB : 𝒱 := ∑ w ∈ Finset.range E,
    (negOnePow P * cbz (P + (w : ℤ)) (w : ℤ)) • resFull W (w : ℤ) (B₀ + (w : ℤ) + 1) u v with hSB
  have hBfam : negOnePow ℓ • (∑ w ∈ Finset.range E,
        ((-1 : ℂ) ^ w * cbz (ℓ + B₀ + (w : ℤ)) (w : ℤ))
          • resHom W (n : ℤ) (B₀ + (w : ℤ) + 1) v u) - SB ∈ Onm W q n := by
    rw [hSB, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun w _ => ?_
    have hskew := resHom_skew_mod_Onm W q n hu hv (B₀ + (w : ℤ) + 1)
    rw [show (K : ℤ) + (B₀ + (w : ℤ) + 1) - (q : ℤ) - 2 = (w : ℤ) from by
      rw [hB₀def, hEc]; ring] at hskew
    have h := Submodule.smul_mem (Onm W q n)
      (negOnePow ℓ * ((-1 : ℂ) ^ w * cbz (ℓ + B₀ + (w : ℤ)) (w : ℤ))) hskew
    rw [smul_sub, smul_smul] at h
    have hcoef : negOnePow ℓ * ((-1 : ℂ) ^ w * cbz (ℓ + B₀ + (w : ℤ)) (w : ℤ))
          * sgn (B₀ + (w : ℤ) + 1 + 1)
        = negOnePow P * cbz (P + (w : ℤ)) (w : ℤ) := by
      rw [← negOnePow_eq_sgn, show B₀ + (w : ℤ) + 1 + 1 = (B₀ + (w : ℤ)) + 2 from by ring,
        negOnePow_add_two, ← negOnePow_natCast w,
        show ℓ + B₀ + (w : ℤ) = P + (w : ℤ) from by rw [hB₀]; ring,
        show negOnePow ℓ * (negOnePow (w : ℤ) * cbz (P + (w : ℤ)) (w : ℤ))
              * negOnePow (B₀ + (w : ℤ))
            = (negOnePow ℓ * negOnePow (w : ℤ) * negOnePow (B₀ + (w : ℤ)))
              * cbz (P + (w : ℤ)) (w : ℤ) from by ring,
        ← negOnePow_add', ← negOnePow_add',
        show ℓ + (w : ℤ) + (B₀ + (w : ℤ)) = P + 2 * (w : ℤ) from by rw [hB₀]; ring]
      congr 1
      have heven : negOnePow (2 * (w : ℤ)) = 1 := by
        have hev : Even (2 * (w : ℤ)) := ⟨(w : ℤ), by ring⟩
        simp [negOnePow, hev]
      rw [negOnePow_add', heven, mul_one]
    rw [hcoef] at h
    rw [show negOnePow ℓ • (((-1 : ℂ) ^ w * cbz (ℓ + B₀ + (w : ℤ)) (w : ℤ))
          • resHom W (n : ℤ) (B₀ + (w : ℤ) + 1) v u)
        = (negOnePow ℓ * ((-1 : ℂ) ^ w * cbz (ℓ + B₀ + (w : ℤ)) (w : ℤ)))
          • resHom W (n : ℤ) (B₀ + (w : ℤ) + 1) v u from smul_smul _ _ _]
    exact h
  -- (V) the main coefficient computation
  have hmain : W.smul u ℓ v
      - (∑ w ∈ Finset.range (P + 1).toNat,
          cbz (-(E : ℤ)) (w : ℤ) • resFull W ((K : ℤ) + (n : ℤ)) (A₀ + (w : ℤ) + 1) u v)
      + SB ∈ Onm W q n := by
    have hδ : W.smul u ℓ v = ∑ᶠ j : ℤ, (if j = ℓ then (1 : ℂ) else 0) • W.smul u j v := by
      rw [finsum_eq_single (fun j : ℤ => (if j = ℓ then (1 : ℂ) else 0) • W.smul u j v) ℓ
        (fun j hj => by
          show (if j = ℓ then (1 : ℂ) else 0) • W.smul u j v = 0
          rw [if_neg hj, zero_smul])]
      rw [if_pos rfl, one_smul]
    have hAcoef := finsetSum_smul_resFull W (Finset.range (P + 1).toNat)
      (fun w : ℕ => cbz (-(E : ℤ)) (w : ℤ)) (fun _ : ℕ => (K : ℤ) + (n : ℤ))
      (fun w : ℕ => A₀ + (w : ℤ) + 1) u v
    have hBcoef := finsetSum_smul_resFull W (Finset.range E)
      (fun w : ℕ => negOnePow P * cbz (P + (w : ℤ)) (w : ℤ)) (fun w : ℕ => (w : ℤ))
      (fun w : ℕ => B₀ + (w : ℤ) + 1) u v
    rw [hδ, hAcoef, hSB, hBcoef]
    have hfin1 : (Function.support fun j : ℤ =>
        (if j = ℓ then (1 : ℂ) else 0) • W.smul u j v).Finite :=
      dj49c2_mode_finite W u v _ ℓ
        (fun j hj => by rw [if_neg (by omega : ¬ j = ℓ), zero_smul])
        (fun j hj => by rw [hj, smul_zero])
    have hfin2 : (Function.support fun j : ℤ =>
        (∑ w ∈ Finset.range (P + 1).toNat,
          cbz (-(E : ℤ)) (w : ℤ) * cbz ((K : ℤ) + (n : ℤ)) (j + (A₀ + (w : ℤ) + 1)))
        • W.smul u j v).Finite :=
      dj49c2_mode_finite W u v _ (-A₀ - ((P + 1).toNat : ℤ))
        (fun j hj => by
          rw [Finset.sum_eq_zero fun w hw => by
            rw [Finset.mem_range] at hw
            rw [cbz_apply_neg ((K : ℤ) + (n : ℤ))
              (by push_cast at hj ⊢; omega : j + (A₀ + (w : ℤ) + 1) < 0), mul_zero], zero_smul])
        (fun j hj => by rw [hj, smul_zero])
    have hfin3 : (Function.support fun j : ℤ =>
        (∑ w ∈ Finset.range E,
          negOnePow P * cbz (P + (w : ℤ)) (w : ℤ) * cbz (w : ℤ) (j + (B₀ + (w : ℤ) + 1)))
        • W.smul u j v).Finite :=
      dj49c2_mode_finite W u v _ (-B₀ - (E : ℤ))
        (fun j hj => by
          rw [Finset.sum_eq_zero fun w hw => by
            rw [Finset.mem_range] at hw
            rw [cbz_apply_neg (w : ℤ)
              (by push_cast at hj ⊢; omega : j + (B₀ + (w : ℤ) + 1) < 0), mul_zero], zero_smul])
        (fun j hj => by rw [hj, smul_zero])
    have hfin12 : (Function.support fun j : ℤ =>
        (if j = ℓ then (1 : ℂ) else 0) • W.smul u j v
          - (∑ w ∈ Finset.range (P + 1).toNat,
              cbz (-(E : ℤ)) (w : ℤ) * cbz ((K : ℤ) + (n : ℤ)) (j + (A₀ + (w : ℤ) + 1)))
            • W.smul u j v).Finite :=
      dj49c2_mode_finite W u v _ (min ℓ (-A₀ - ((P + 1).toNat : ℤ)))
        (fun j hj => by
          rw [if_neg (by omega : ¬ j = ℓ),
            Finset.sum_eq_zero fun w hw => by
              rw [Finset.mem_range] at hw
              rw [cbz_apply_neg ((K : ℤ) + (n : ℤ))
                (by push_cast at hj ⊢; omega : j + (A₀ + (w : ℤ) + 1) < 0), mul_zero],
            zero_smul, sub_zero])
        (fun j hj => by rw [hj]; simp)
    rw [← finsum_sub_distrib hfin1 hfin2, ← finsum_add_distrib hfin12 hfin3]
    have hcoef : ∀ j : ℤ,
        (if j = ℓ then (1 : ℂ) else 0) • W.smul u j v
            - (∑ w ∈ Finset.range (P + 1).toNat,
                cbz (-(E : ℤ)) (w : ℤ) * cbz ((K : ℤ) + (n : ℤ)) (j + (A₀ + (w : ℤ) + 1)))
              • W.smul u j v
            + (∑ w ∈ Finset.range E,
                negOnePow P * cbz (P + (w : ℤ)) (w : ℤ) * cbz (w : ℤ) (j + (B₀ + (w : ℤ) + 1)))
              • W.smul u j v
          = (∑ k ∈ Finset.range (-P).toNat,
              dj49Leftover E P k * cbz ((K : ℤ) + (n : ℤ))
                (j + ((q : ℤ) + (n : ℤ) + 2 + (k : ℤ)))) • W.smul u j v := by
      intro j
      rw [← sub_smul, ← add_smul]
      congr 1
      have hsc := dj49c2_scalar_j E P A₀ B₀ ((q : ℤ) + (n : ℤ) + 2) ℓ j hA₀ hB₀
        (by rw [hA₀def, hPdef]; ring)
      rw [← hEc]
      have hB2 : (∑ w ∈ Finset.range E,
            negOnePow P * cbz (P + (w : ℤ)) (w : ℤ) * cbz (w : ℤ) (j + (B₀ + (w : ℤ) + 1)))
          = ∑ w ∈ Finset.range E,
            (negOnePow P * cbz (P + (w : ℤ)) (w : ℤ)) * cbz (w : ℤ) (j + (B₀ + (w : ℤ) + 1)) :=
        Finset.sum_congr rfl fun w _ => by ring
      have hL2 : (∑ k ∈ Finset.range (-P).toNat,
            dj49Leftover E P k * cbz (E : ℤ) (j + ((q : ℤ) + (n : ℤ) + 2 + (k : ℤ))))
          = ∑ k ∈ Finset.range (-P).toNat,
            dj49Leftover E P k
              * cbz (E : ℤ) (j + (((q : ℤ) + (n : ℤ) + 2) + (k : ℤ))) :=
        Finset.sum_congr rfl fun k _ => by
          rw [show (q : ℤ) + (n : ℤ) + 2 + (k : ℤ) = ((q : ℤ) + (n : ℤ) + 2) + (k : ℤ) from
            by ring]
      rw [hB2, hL2]
      exact hsc
    rw [finsum_congr hcoef]
    exact coeffFinsum_offdiag_mem_Onm W q n hu v (Finset.range (-P).toNat) (dj49Leftover E P)
  -- (VI) assemble
  have hfinal : W.smul u ℓ v
      - ((∑ w ∈ Finset.range (P + 1).toNat,
            cbz (-(E : ℤ)) (w : ℤ) • resFull W ((K : ℤ) + (n : ℤ)) (A₀ + (w : ℤ) + 1) u v)
          - negOnePow ℓ • (∑ w ∈ Finset.range E,
              ((-1 : ℂ) ^ w * cbz (ℓ + B₀ + (w : ℤ)) (w : ℤ))
                • resHom W (n : ℤ) (B₀ + (w : ℤ) + 1) v u))
      = (W.smul u ℓ v
          - (∑ w ∈ Finset.range (P + 1).toNat,
              cbz (-(E : ℤ)) (w : ℤ) • resFull W ((K : ℤ) + (n : ℤ)) (A₀ + (w : ℤ) + 1) u v)
          + SB)
        + (negOnePow ℓ • (∑ w ∈ Finset.range E,
              ((-1 : ℂ) ^ w * cbz (ℓ + B₀ + (w : ℤ)) (w : ℤ))
                • resHom W (n : ℤ) (B₀ + (w : ℤ) + 1) v u) - SB) := by
    abel
  rw [hfinal]
  exact Submodule.add_mem _ hmain hBfam

/-- `(★)` in the `OnmFull` form used by the operator transport. -/
theorem dj49Star_holds (W : VertexOperatorAlgebra 𝒱) : DJ49Star W :=
  dj49Star_of_prime W (dj49StarPrime_holds W)

/-! ## §7  Consequences: `ModuleIterate` and the weak-module structure become unconditional -/

/-- **`ModuleIterate (muFullRhoU W U)`, unconditionally** — Dong–Jiang Lemma 4.9 for `M(U)`,
for every `A(𝒱)`-module `U`.  The `ℓ ≥ 0` half was already free (`moduleIterate_nonneg`); the
`ℓ < 0` half is `(★)`, a theorem. -/
theorem moduleIterate_muFullRhoU (W : VertexOperatorAlgebra 𝒱) (U : AMod W) :
    ModuleIterate (muFullRhoU W U) :=
  moduleIterate_of_dj49Star W U (dj49Star_holds W)

/-- **`M̃(U) = ⊕ₙ A_{n,0}(𝒱) ⊗_ℂ U` is a weak `𝒱`-module, unconditionally.**

⚠ SCOPE: this is the `⊗_ℂ` cover `MUFull`, **not** Dong–Jiang's balanced `DJCarrier`
(`= ⊕ₙ A_{n,0}(𝒱) ⊗_{A(𝒱)} U`).  The balanced statement needs the operator transport of §8 below
plus a `VHatRep`/`ModeData` packaging on `DJCarrier`, which is NOT built here. -/
noncomputable def muFullWeakU_uncond (W : VertexOperatorAlgebra 𝒱) (U : AMod W) :
    WeakModule W (MUFull W U) :=
  muFullWeakOfStar W U (dj49Star_holds W)

/-! ## §8  The two operator inputs of the **balanced** (`DJCarrier`) transport

`(★)` is a statement about `𝒱` alone, so it serves the balanced carrier as well.  The transport of
`(★)` from representatives to operators on `M(U)(n) = A_{n,0}(𝒱) ⊗_{A(𝒱)} U` needs exactly the two
lemmas below (the balanced analogues of `oFullU_eq_zero_of_mem` and `oFullU_comp`, which drive
`muFullMode_iterate_incl`).  Both are unconditional at base level `0`.

⚠ NOT proved here: the four-regime level bookkeeping on `DJCarrier` and the `ℓ ≥ 0` half — the
latter is `moduleIterate_nonneg`, which is stated for a `VHat.VHatRep`, and no `VHatRep` (nor
`ModeData`) has been built on `DJCarrier`.  See the file-level report. -/

section DJCarrierInputs

variable {W : VertexOperatorAlgebra 𝒱}

/-- **The balanced mode operator of an ideal element vanishes** (base level `0`): if
`D ∈ O_{q,n}(𝒱)` then `D` acts as `0` from `M(U)(n)` to `M(U)(q)`.  Unconditional; the balanced
analogue of `oFullU_eq_zero_of_mem`, from DJ Lemma 2.8's right inclusion. -/
theorem djPieceAct_eq_zero_of_mem (U : AmMod W 0) (q n : ℕ) {D : 𝒱}
    (hD : D ∈ OnmFull W q n) :
    djPieceAct W U q n (djLeftSlot_zero W q n) D = 0 := by
  refine djPiece_ext (f := djPieceAct W U q n (djLeftSlot_zero W q n) D) (g := 0) ?_
  intro g w
  rw [djPieceAct_mk, LinearMap.zero_apply,
    show mkAnmFull W q 0 (anmGen W q 0 n D g) = 0 from by
      rw [mkAnmFull, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact anmGen_OnmFull_right_unconditional W q 0 n g D hD,
    TensorProduct.zero_tmul, map_zero]

/-- **DJ Lemma 4.1 on the BALANCED piece** (base level `0`, unconditional): two `M(U)`-modes
compose to a single mode,

`(a ∗^q_{0,p} −) ∘ (b ∗^p_{0,n} −) = ((a ∗^q_{n,p} b) ∗^q_{0,n} −)`  on `M(U)(n)`.

The defect is DJ's bare associator, a generator of `O''_{q,0} ≤ O_{q,0}`
(`bareAssoc_mem_OnmFull`).  This is the balanced analogue of `oFullU_comp`. -/
theorem djPieceAct_comp_zero (U : AmMod W 0) (q p n : ℕ) (a b : 𝒱) :
    (djPieceAct W U q p (djLeftSlot_zero W q p) a).comp
        (djPieceAct W U p n (djLeftSlot_zero W p n) b)
      = djPieceAct W U q n (djLeftSlot_zero W q n) (anmGen W q n p a b) := by
  refine djPiece_ext ?_
  intro g w
  rw [LinearMap.comp_apply, djPieceAct_mk, djPieceAct_mk, djPieceAct_mk, ← sub_eq_zero,
    ← map_sub, ← TensorProduct.sub_tmul, ← map_sub]
  have hmem : anmGen W q 0 p a (anmGen W p 0 n b g) - anmGen W q 0 n (anmGen W q n p a b) g
      ∈ OnmFull W q 0 := by
    have h := Submodule.neg_mem _ (bareAssoc_mem_OnmFull W q 0 n p a b g)
    rwa [neg_sub] at h
  rw [show mkAnmFull W q 0 (anmGen W q 0 p a (anmGen W p 0 n b g)
        - anmGen W q 0 n (anmGen W q n p a b) g) = 0 from by
      rw [mkAnmFull, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hmem,
    TensorProduct.zero_tmul, map_zero]

/-- **The evaluation map `D ↦ o_{q,n}(D)x`, bundled**, on the balanced piece. -/
noncomputable def djPieceActAt (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) (q n : ℕ)
    (x : DJPiece W U n) : 𝒱 →ₗ[ℂ] DJCarrier W U where
  toFun D := DJCarrier.incl W U q (djPieceAct W U q n (djLeftSlot_zero W q n) D x)
  map_add' D₁ D₂ := by
    simp only [djPieceAct_add_acting, LinearMap.add_apply, map_add]
  map_smul' c D := by
    simp only [djPieceAct_smul_acting, LinearMap.smul_apply, map_smul, RingHom.id_apply]

@[simp] theorem djPieceActAt_apply (U : AmMod W 0) (q n : ℕ) (x : DJPiece W U n) (D : 𝒱) :
    djPieceActAt W U q n x D
      = DJCarrier.incl W U q (djPieceAct W U q n (djLeftSlot_zero W q n) D x) := rfl

/-- The balanced evaluation map kills the ideal. -/
theorem djPieceActAt_eq_zero_of_mem (U : AmMod W 0) (q n : ℕ) (x : DJPiece W U n) {D : 𝒱}
    (hD : D ∈ OnmFull W q n) : djPieceActAt W U q n x D = 0 := by
  rw [djPieceActAt_apply, djPieceAct_eq_zero_of_mem U q n hD, LinearMap.zero_apply, map_zero]

/-- **The `ℓ < 0` ITERATE IDENTITY ON ONE GRADED PIECE OF THE BALANCED `M(U)`** —
Dong–Jiang Lemma 4.9 for `DJCarrier` at base level `0`, unconditional.

All four level regimes of the `⊗_ℂ` template `muFullMode_iterate_incl` recur: the common target
level `q = K + M − ℓ − N − 2 + n` is negative (everything vanishes), or nonnegative with either
intermediate level `pᵢ = M − N − i − 1 + n`, `p'ᵢ = K − i − 1 + n` negative (that term vanishes) or
nonnegative (the two modes compose to a single mode by `djPieceAct_comp_zero`).  The
representative-level input is `(★)` = `dj49Star_holds`. -/
theorem djModeZero_iterate_incl (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0)
    {K M : ℕ} {u v : 𝒱} (hu : u ∈ W.grading (K : ℤ)) (hv : v ∈ W.grading (M : ℤ))
    {ℓ : ℤ} (hℓ : ℓ < 0) (N : ℤ) (n : ℕ) (x : DJPiece W U n) :
    djModeZero W U N (W.smul u ℓ v) (DJCarrier.incl W U n x)
      = ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
          (djModeZero W U (ℓ - i) u (djModeZero W U (N + i) v (DJCarrier.incl W U n x))
            - negOnePow ℓ • djModeZero W U (ℓ + N - i) v
                (djModeZero W U i u (DJCarrier.incl W U n x))) := by
  have hstar := dj49Star_holds W
  have hD := djActionDescent_zero W
  have huv : W.smul u ℓ v ∈ W.grading ((K : ℤ) + (M : ℤ) - ℓ - 1) := smul_mem_grading W hu hv ℓ
  have hEu : ∀ (s t : ℕ) (p : ℤ) (y : DJPiece W U s), (K : ℤ) - p - 1 + (s : ℤ) = (t : ℤ) →
      djModeZero W U p u (DJCarrier.incl W U s y)
        = DJCarrier.incl W U t (djPieceAct W U t s (djLeftSlot_zero W t s) u y) := by
    intro s t p y h
    rw [djModeZero, djMode_apply_incl U hD p hu s y,
      djLevelIncl_eq_of_target U hD (show muTargetLevel (K : ℤ) p s = (t : ℤ) from h) u,
      LinearMap.comp_apply]
  have hZu : ∀ (s : ℕ) (p : ℤ) (y : DJPiece W U s), (K : ℤ) - p - 1 + (s : ℤ) < 0 →
      djModeZero W U p u (DJCarrier.incl W U s y) = 0 := by
    intro s p y h
    rw [djModeZero, djMode_apply_incl U hD p hu s y,
      djLevelIncl_of_neg U hD (show muTargetLevel (K : ℤ) p s < 0 from h) u, LinearMap.zero_apply]
  have hEv : ∀ (s t : ℕ) (p : ℤ) (y : DJPiece W U s), (M : ℤ) - p - 1 + (s : ℤ) = (t : ℤ) →
      djModeZero W U p v (DJCarrier.incl W U s y)
        = DJCarrier.incl W U t (djPieceAct W U t s (djLeftSlot_zero W t s) v y) := by
    intro s t p y h
    rw [djModeZero, djMode_apply_incl U hD p hv s y,
      djLevelIncl_eq_of_target U hD (show muTargetLevel (M : ℤ) p s = (t : ℤ) from h) v,
      LinearMap.comp_apply]
  have hZv : ∀ (s : ℕ) (p : ℤ) (y : DJPiece W U s), (M : ℤ) - p - 1 + (s : ℤ) < 0 →
      djModeZero W U p v (DJCarrier.incl W U s y) = 0 := by
    intro s p y h
    rw [djModeZero, djMode_apply_incl U hD p hv s y,
      djLevelIncl_of_neg U hD (show muTargetLevel (M : ℤ) p s < 0 from h) v, LinearMap.zero_apply]
  by_cases hT : 0 ≤ (K : ℤ) + (M : ℤ) - ℓ - N - 2 + (n : ℤ)
  · obtain ⟨q, hq⟩ : ∃ q : ℕ, (K : ℤ) + (M : ℤ) - ℓ - N - 2 + (n : ℤ) = (q : ℤ) :=
      ⟨_, (Int.toNat_of_nonneg hT).symm⟩
    have hL : djModeZero W U N (W.smul u ℓ v) (DJCarrier.incl W U n x)
        = djPieceActAt W U q n x (W.smul u ℓ v) := by
      rw [djModeZero, djMode_apply_incl U hD N huv n x,
        djLevelIncl_eq_of_target U hD
          (show muTargetLevel ((K : ℤ) + (M : ℤ) - ℓ - 1) N n = (q : ℤ) from by
            simp only [muTargetLevel]; omega) (W.smul u ℓ v)]
      rfl
    have hA : ∀ i : ℤ,
        djModeZero W U (ℓ - i) u (djModeZero W U (N + i) v (DJCarrier.incl W U n x))
          = djPieceActAt W U q n x (anmGenZ W q n ((M : ℤ) - N - i - 1 + (n : ℤ)) u v) := by
      intro i
      by_cases hp : 0 ≤ (M : ℤ) - N - i - 1 + (n : ℤ)
      · obtain ⟨Pi, hPi⟩ : ∃ Pi : ℕ, (M : ℤ) - N - i - 1 + (n : ℤ) = (Pi : ℤ) :=
          ⟨_, (Int.toNat_of_nonneg hp).symm⟩
        have hcomp := congrArg (fun f : DJPiece W U n →ₗ[ℂ] DJPiece W U q => f x)
          (djPieceAct_comp_zero U q Pi n u v)
        simp only [LinearMap.comp_apply] at hcomp
        rw [hEv n Pi (N + i) x (by omega),
          hEu Pi q (ℓ - i) (djPieceAct W U Pi n (djLeftSlot_zero W Pi n) v x) (by omega), hcomp,
          anmGenZ_of_eq W q n hPi u v]
        rfl
      · rw [hZv n (N + i) x (by omega), map_zero, anmGenZ_of_neg W q n (by omega), map_zero]
    have hBm : ∀ i : ℤ,
        djModeZero W U (ℓ + N - i) v (djModeZero W U i u (DJCarrier.incl W U n x))
          = djPieceActAt W U q n x (anmGenZ W q n ((K : ℤ) - i - 1 + (n : ℤ)) v u) := by
      intro i
      by_cases hp : 0 ≤ (K : ℤ) - i - 1 + (n : ℤ)
      · obtain ⟨Pi, hPi⟩ : ∃ Pi : ℕ, (K : ℤ) - i - 1 + (n : ℤ) = (Pi : ℤ) :=
          ⟨_, (Int.toNat_of_nonneg hp).symm⟩
        have hcomp := congrArg (fun f : DJPiece W U n →ₗ[ℂ] DJPiece W U q => f x)
          (djPieceAct_comp_zero U q Pi n v u)
        simp only [LinearMap.comp_apply] at hcomp
        rw [hEu n Pi i x (by omega),
          hEv Pi q (ℓ + N - i) (djPieceAct W U Pi n (djLeftSlot_zero W Pi n) u x) (by omega),
          hcomp, anmGenZ_of_eq W q n hPi v u]
        rfl
      · rw [hZu n i x (by omega), map_zero, anmGenZ_of_neg W q n (by omega), map_zero]
    have hfin : (Function.support fun i : ℤ => (negOnePow i * cbz ℓ i) •
        (anmGenZ W q n ((M : ℤ) - N - i - 1 + (n : ℤ)) u v
          - negOnePow ℓ • anmGenZ W q n ((K : ℤ) - i - 1 + (n : ℤ)) v u)).Finite := by
      refine Set.Finite.subset (Set.finite_Icc 0
        (max ((M : ℤ) - N - 1 + (n : ℤ)) ((K : ℤ) - 1 + (n : ℤ)))) ?_
      intro i hi
      rw [Function.mem_support] at hi
      rw [Set.mem_Icc]
      refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
      · rw [cbz_apply_neg ℓ h, mul_zero, zero_smul]
      · have h₁ : (M : ℤ) - N - 1 + (n : ℤ) ≤ max ((M : ℤ) - N - 1 + (n : ℤ))
            ((K : ℤ) - 1 + (n : ℤ)) := le_max_left _ _
        have h₂ : (K : ℤ) - 1 + (n : ℤ) ≤ max ((M : ℤ) - N - 1 + (n : ℤ))
            ((K : ℤ) - 1 + (n : ℤ)) := le_max_right _ _
        rw [anmGenZ_of_neg W q n (show (M : ℤ) - N - i - 1 + (n : ℤ) < 0 from by omega),
          anmGenZ_of_neg W q n (show (K : ℤ) - i - 1 + (n : ℤ) < 0 from by omega)]
        simp
    have hRHS : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
          (djModeZero W U (ℓ - i) u (djModeZero W U (N + i) v (DJCarrier.incl W U n x))
            - negOnePow ℓ • djModeZero W U (ℓ + N - i) v
                (djModeZero W U i u (DJCarrier.incl W U n x))))
        = djPieceActAt W U q n x (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
            (anmGenZ W q n ((M : ℤ) - N - i - 1 + (n : ℤ)) u v
              - negOnePow ℓ • anmGenZ W q n ((K : ℤ) - i - 1 + (n : ℤ)) v u)) := by
      rw [map_finsum (djPieceActAt W U q n x) hfin]
      refine finsum_congr fun i => ?_
      rw [hA i, hBm i, map_smul, map_sub, map_smul]
    have hz := djPieceActAt_eq_zero_of_mem U q n x (hstar K M u v hu hv n q ℓ N hℓ hq.symm)
    rw [map_sub] at hz
    rw [hL, hRHS, ← sub_eq_zero]
    exact hz
  · rw [not_le] at hT
    have hL : djModeZero W U N (W.smul u ℓ v) (DJCarrier.incl W U n x) = 0 := by
      rw [djModeZero, djMode_apply_incl U hD N huv n x,
        djLevelIncl_of_neg U hD
          (show muTargetLevel ((K : ℤ) + (M : ℤ) - ℓ - 1) N n < 0 from by
            simp only [muTargetLevel]; omega) (W.smul u ℓ v), LinearMap.zero_apply]
    rw [hL]
    refine (finsum_eq_zero_of_forall_eq_zero fun i => ?_).symm
    have h1 : djModeZero W U (ℓ - i) u
        (djModeZero W U (N + i) v (DJCarrier.incl W U n x)) = 0 := by
      by_cases hp : 0 ≤ (M : ℤ) - N - i - 1 + (n : ℤ)
      · obtain ⟨Pi, hPi⟩ : ∃ Pi : ℕ, (M : ℤ) - N - i - 1 + (n : ℤ) = (Pi : ℤ) :=
          ⟨_, (Int.toNat_of_nonneg hp).symm⟩
        rw [hEv n Pi (N + i) x (by omega),
          hZu Pi (ℓ - i) (djPieceAct W U Pi n (djLeftSlot_zero W Pi n) v x) (by omega)]
      · rw [hZv n (N + i) x (by omega), map_zero]
    have h2 : djModeZero W U (ℓ + N - i) v
        (djModeZero W U i u (DJCarrier.incl W U n x)) = 0 := by
      by_cases hp : 0 ≤ (K : ℤ) - i - 1 + (n : ℤ)
      · obtain ⟨Pi, hPi⟩ : ∃ Pi : ℕ, (K : ℤ) - i - 1 + (n : ℤ) = (Pi : ℤ) :=
          ⟨_, (Int.toNat_of_nonneg hp).symm⟩
        rw [hEu n Pi i x (by omega),
          hZv Pi (ℓ + N - i) (djPieceAct W U Pi n (djLeftSlot_zero W Pi n) u x) (by omega)]
      · rw [hZu n i x (by omega), map_zero]
    rw [h1, h2]
    simp

/-! ### From one graded piece to all of `M(U)` -/

/-- The right-hand side of the iterate identity on the balanced carrier. -/
noncomputable def djItRHS (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) (u v : 𝒱)
    (x : DJCarrier W U) (ℓ N : ℤ) : DJCarrier W U :=
  ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
    (djModeZero W U (ℓ - i) u (djModeZero W U (N + i) v x)
      - negOnePow ℓ • djModeZero W U (ℓ + N - i) v (djModeZero W U i u x))

/-- The summand family of `djItRHS` is finitely supported (DJ Lemma 4.6(1)). -/
theorem djItRHS_fin (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) (u v : 𝒱)
    (x : DJCarrier W U) (ℓ N : ℤ) :
    (Function.support fun i : ℤ => (negOnePow i * cbz ℓ i) •
      (djModeZero W U (ℓ - i) u (djModeZero W U (N + i) v x)
        - negOnePow ℓ • djModeZero W U (ℓ + N - i) v (djModeZero W U i u x))).Finite := by
  obtain ⟨Nv, hNv⟩ := djModeZero_truncation W U v x
  obtain ⟨Nu, hNu⟩ := djModeZero_truncation W U u x
  refine Set.Finite.subset (Set.finite_Icc 0 (max (Nv - N) Nu)) ?_
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg ℓ h, mul_zero, zero_smul]
  · have h₁ : Nv - N ≤ max (Nv - N) Nu := le_max_left _ _
    have h₂ : Nu ≤ max (Nv - N) Nu := le_max_right _ _
    rw [hNv (N + i) (by omega), hNu i (by omega)]
    simp

theorem djItRHS_zero_x (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) (u v : 𝒱) (ℓ N : ℤ) :
    djItRHS W U u v 0 ℓ N = 0 := by
  rw [djItRHS]
  exact finsum_eq_zero_of_forall_eq_zero fun i => by simp

/-- The zero vector acts as the zero mode. -/
theorem djModeZero_zero_acting (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) (p : ℤ) :
    djModeZero W U p (0 : 𝒱) = 0 := by
  rw [djModeZero, djMode_zero_acting]

theorem djItRHS_zero_u (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) (v : 𝒱)
    (x : DJCarrier W U) (ℓ N : ℤ) : djItRHS W U 0 v x ℓ N = 0 := by
  rw [djItRHS]
  refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
  rw [djModeZero_zero_acting, djModeZero_zero_acting]
  simp

theorem djItRHS_zero_v (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) (u : 𝒱)
    (x : DJCarrier W U) (ℓ N : ℤ) : djItRHS W U u 0 x ℓ N = 0 := by
  rw [djItRHS]
  refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
  rw [djModeZero_zero_acting, djModeZero_zero_acting]
  simp

theorem djItRHS_add_x (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) (u v : 𝒱)
    (x y : DJCarrier W U) (ℓ N : ℤ) :
    djItRHS W U u v (x + y) ℓ N = djItRHS W U u v x ℓ N + djItRHS W U u v y ℓ N := by
  rw [djItRHS, djItRHS, djItRHS,
    ← finsum_add_distrib (djItRHS_fin W U u v x ℓ N) (djItRHS_fin W U u v y ℓ N)]
  refine finsum_congr fun i => ?_
  simp only [map_add, smul_add, smul_sub]
  abel

theorem djItRHS_add_u (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) (u₁ u₂ v : 𝒱)
    (x : DJCarrier W U) (ℓ N : ℤ) :
    djItRHS W U (u₁ + u₂) v x ℓ N = djItRHS W U u₁ v x ℓ N + djItRHS W U u₂ v x ℓ N := by
  rw [djItRHS, djItRHS, djItRHS,
    ← finsum_add_distrib (djItRHS_fin W U u₁ v x ℓ N) (djItRHS_fin W U u₂ v x ℓ N)]
  refine finsum_congr fun i => ?_
  simp only [djModeZero, djMode_add_acting, LinearMap.add_apply, map_add, smul_add, smul_sub]
  abel

theorem djItRHS_add_v (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) (u v₁ v₂ : 𝒱)
    (x : DJCarrier W U) (ℓ N : ℤ) :
    djItRHS W U u (v₁ + v₂) x ℓ N = djItRHS W U u v₁ x ℓ N + djItRHS W U u v₂ x ℓ N := by
  rw [djItRHS, djItRHS, djItRHS,
    ← finsum_add_distrib (djItRHS_fin W U u v₁ x ℓ N) (djItRHS_fin W U u v₂ x ℓ N)]
  refine finsum_congr fun i => ?_
  simp only [djModeZero, djMode_add_acting, LinearMap.add_apply, map_add, smul_add, smul_sub]
  abel

/-- **DONG–JIANG LEMMA 4.9 ON THE BALANCED CARRIER, `ℓ < 0`, unconditional** — for arbitrary
`u, v ∈ 𝒱` and arbitrary `x ∈ M(U) = ⊕ₙ A_{n,0}(𝒱) ⊗_{A(𝒱)} U`:

`(u₍ℓ₎v)₍N₎ x = ∑ᵢ (−1)ⁱC(ℓ,i)·( u₍ℓ₋ᵢ₎v₍N₊ᵢ₎x − (−1)^ℓ v₍ℓ₊N₋ᵢ₎u₍ᵢ₎x )`.

No hypothesis, no axiom, pbw-free.  (`ℓ ≥ 0` is NOT covered here — see the module docstring.) -/
theorem djModeZero_iterate_neg (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0)
    {ℓ : ℤ} (hℓ : ℓ < 0) (N : ℤ) (u v : 𝒱) (x : DJCarrier W U) :
    djModeZero W U N (W.smul u ℓ v) x = djItRHS W U u v x ℓ N := by
  revert x
  refine reduce_homogeneous W (P := fun u => ∀ (v : 𝒱) (x : DJCarrier W U),
    djModeZero W U N (W.smul u ℓ v) x = djItRHS W U u v x ℓ N) ?_ ?_ ?_ u v
  · intro Ku a ha
    refine reduce_homogeneous W (P := fun v => ∀ x : DJCarrier W U,
      djModeZero W U N (W.smul a ℓ v) x = djItRHS W U a v x ℓ N) ?_ ?_ ?_
    · intro Mb b hb
      rcases lt_or_ge Ku 0 with hKneg | hKpos
      · have ha0 : a = 0 := by
          have h := W.positivity Ku hKneg
          rw [h, Submodule.mem_bot] at ha; exact ha
        subst ha0
        intro x
        rw [PreVertexAlgebra.smul_zero_left, djModeZero, djMode_zero_acting, LinearMap.zero_apply,
          djItRHS_zero_u]
      rcases lt_or_ge Mb 0 with hMneg | hMpos
      · have hb0 : b = 0 := by
          have h := W.positivity Mb hMneg
          rw [h, Submodule.mem_bot] at hb; exact hb
        subst hb0
        intro x
        rw [PreVertexAlgebra.smul_zero_right, djModeZero, djMode_zero_acting, LinearMap.zero_apply,
          djItRHS_zero_v]
      obtain ⟨K, rfl⟩ := Int.eq_ofNat_of_zero_le hKpos
      obtain ⟨M, rfl⟩ := Int.eq_ofNat_of_zero_le hMpos
      intro x
      refine DirectSum.induction_on x ?_ ?_ ?_
      · rw [map_zero, djItRHS_zero_x]
      · intro n y
        show djModeZero W U N (W.smul a ℓ b) (DJCarrier.incl W U n y) = _
        rw [djItRHS]
        exact djModeZero_iterate_incl W U ha hb hℓ N n y
      · intro x₁ x₂ h₁ h₂
        rw [map_add, h₁, h₂, djItRHS_add_x]
    · intro x
      rw [PreVertexAlgebra.smul_zero_right, djModeZero, djMode_zero_acting, LinearMap.zero_apply,
        djItRHS_zero_v]
    · intro v₁ v₂ h₁ h₂ x
      rw [PreVertexAlgebra.smul_add_right, djModeZero, djMode_add_acting, LinearMap.add_apply]
      rw [← djModeZero, ← djModeZero, h₁ x, h₂ x, djItRHS_add_v]
  · intro v x
    rw [PreVertexAlgebra.smul_zero_left, djModeZero, djMode_zero_acting, LinearMap.zero_apply,
      djItRHS_zero_u]
  · intro u₁ u₂ h₁ h₂ v x
    rw [PreVertexAlgebra.smul_add_left, djModeZero, djMode_add_acting, LinearMap.add_apply]
    rw [← djModeZero, ← djModeZero, h₁ v x, h₂ v x, djItRHS_add_u]

end DJCarrierInputs

end VOA

/-
`#print axioms` check (each of the following prints `[propext, Classical.choice, Quot.sound]`,
NO `pbw`, NO `sorryAx`):

  #print axioms VOA.dj49c2_triangle
  #print axioms VOA.dj49c2_inner_vand
  #print axioms VOA.dj49c2_S1
  #print axioms VOA.dj49c2_S2
  #print axioms VOA.dj49c2_scalar
  #print axioms VOA.dj49c2_scalar_j
  #print axioms VOA.dj49c2_collapse
  #print axioms VOA.dj49StarPrime_holds
  #print axioms VOA.dj49Star_holds
  #print axioms VOA.moduleIterate_muFullRhoU
  #print axioms VOA.muFullWeakU_uncond
  #print axioms VOA.djPieceAct_eq_zero_of_mem
  #print axioms VOA.djPieceAct_comp_zero
  #print axioms VOA.djModeZero_iterate_incl
  #print axioms VOA.djModeZero_iterate_neg
-/
