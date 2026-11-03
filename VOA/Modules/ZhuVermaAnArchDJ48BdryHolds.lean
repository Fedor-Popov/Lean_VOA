/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDJAction

/-!
# `DJ48Bdry` discharged, and Dong–Jiang Lemma 4.7 on `M(U)` in **all four regimes**

`ZhuVermaAnArchDJ23` names two pure-`𝒱` leaves under Dong–Jiang Lemma 4.7.  One of them,
`DJ23Comm` (DJ Lemma 2.3), was discharged in `ZhuVermaAnArchDJ23Final`; the other, **`DJ48Bdry`**
(DJ's `la4.8`, printed as Lemma 4.9 — `refs/dj.txt:1482`), had no `_holds`.  This file supplies it,
adds its mirror regime, and assembles the commutator formula on Dong–Jiang's **balanced** carrier
`DJCarrier` at general base level `m`.

## What DJ actually prove

DJ Lemma 4.7 (`refs/dj.txt:1410`, printed as Lemma 4.8) is the commutator formula
`[a_p, b_q] = ∑_{i ≥ 0} C(p,i)·(a₍ᵢ₎b)_{p+q−i}` on `M(U)`.  Their proof splits on the two
intermediate levels `n₁ = wt b − q − 1 + n` (the `b_q` target) and `n₂ = wt a − p − 1 + n` (the
`a_p` target), with common target `N = n₁ + n₂ − n = wt a + wt b − p − q − 2 + n`:

* `N < 0` — "clear from the definition of the actions" (every term has a negative target level);
* `n₁, n₂ ≥ 0` — the **interior** regime, DJ Lemma 2.3 (proved `dj23Comm_holds`);
* `n₁ < 0 ≤ n₂` and `n₂ < 0 ≤ n₁` — the two **mixed** regimes, where one of the two compositions
  is identically `0` because the product `∗` at a negative index is not even defined.  Here DJ
  invoke their Lemma 4.9 (`la4.8`).

## Contents

### §1–§2 The two mixed regimes as pure-`𝒱` statements
* **`dj48Bdry_holds : DJ48Bdry W`** — the repo's named leaf, discharged from the proved
  `dj48_case1` (an exact equality in `𝒱`) plus `W.positivity` for the negative-weight slice.
* `DJ48BdryB` / **`dj48BdryB_holds`** — the mirror regime (`p₁ < 0 ≤ p₂`), from the proved
  `dj48_case2`, with the right slot reduced to homogeneous by `reduce_homogeneous`.

Both are phrased with an integer weight `K` and an arbitrary (not necessarily homogeneous) `b`, so
they plug directly into the commutator assembly.  ⚠ DJ derive `la4.8` from their Lemma 2.4 at
general `m`; that detour is **not** needed here — `cbz_neg_upper` makes the alternating binomial
complete and both regimes collapse to a Vandermonde (`ZhuVermaAnArchDJ48`).

### §3 The mixed regimes on representatives, at general base level `m`
`anmGen_commutator_bdryA_gen` (`n₁ < 0`) and `anmGen_commutator_bdryB_gen` (`n₂ < 0`), the exact
companions of the proved interior `anmGen_commutator_interior_gen`.  Same three ingredients: the
`O''` reassociation `bareAssoc_mem_OnmFull`, the boundary lemma of §1/§2, and DJ Lemma 2.8's right
inclusion `anmGen_OnmFull_right_unconditional`.

### §4–§5 Descent to the balanced piece
`djPieceAct_eq_of_repr_mem` transports **any** representative-level congruence of the commutator
shape onto all of `M(U)(n)` (not merely the generators `[g] ⊗ w`), and the three regimes are read
off as `djPieceAct_commutator_{interior,bdryA,bdryB}_all`.

### §6 The operator-level commutator on `DJCarrier`, all four regimes
`djMode_commutator_incl` (on a level piece), **`djMode_commutator`** (on all of `M(U)`, homogeneous
`a, b`) and **`djMode_commutator_gen`** (arbitrary `a, b`):
```
  a_p b_q x − b_q a_p x = ∑ᵢ C(p,i)·(a₍ᵢ₎b)_{p+q−i} x
```
for every `p, q ∈ ℤ` and every `x ∈ M(U)`, at **general base level `m`**, given only DJ's action
descent `hD : DJActionDescent W m` (unconditional at `m = 0`, `djActionDescent_zero`).
`djModeZero_commutator` / `djModeZero_commutator_gen` are the hypothesis-free `m = 0` instances.

## Carried hypotheses

None beyond `DJActionDescent W m` (= DJ Lemma 2.8's left inclusion at base level `m`, itself a
theorem at `m = 0`).  In particular this file uses **no** `DJAnnEqAn`, no PBW datum, no `DJ23Comm`
assumption (it is the proved theorem `dj23Comm_holds`).

⚠ This is DJ Lemma 4.7 only.  DJ Lemma 4.8 (associativity / the iterate) is **not** proved here, so
`DJCarrier W U` is still **not** shown to be a `WeakModule`; nothing below claims otherwise.

Engine record (before formalizing): the two scalar cores `la48_c1_coeff`/`la48_c2_coeff` re-verified
over `−8 ≤ D ≤ 8`, negative index in `[−6,−1]`, `p ≤ 8`, `−6 ≤ ℓ ≤ 10` (11 271 instances each):
**0 failures**, while six deliberate corruptions (upper index `D+q`, dropped `(−1)ⁱ`, shifted lower
index, dropped `sgn`, shifted `sgn` argument) fail in 4 282–5 694 instances each.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), `sorry`-free, `pbw`-free; no existing file
mutated.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §4 (Lemma 4.7 = `refs/dj.txt:1410`,
Lemma 4.9 = `la4.8` = `refs/dj.txt:1482`), §2 (Lemma 2.3);
`ZhuVermaAnArchDJ48` (`dj48_case1`, `dj48_case2`), `ZhuVermaAnArchDJ23` (`DJ48Bdry`, `resExp`,
`anmGen_resExp_left`), `ZhuVermaAnArchDJ23Final` (`dj23Comm_holds`),
`ZhuVermaAnArchDJAction` (`djPieceAct`, `djMode`, `anmGen_commutator_interior_gen`),
`ZhuVermaAnArchDJ28Final` (`anmGen_OnmFull_right_unconditional`),
`ZhuVermaAnArchDJ27` (`bareAssoc_mem_OnmFull`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators TensorProduct DirectSum

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §1 `DJ48Bdry`, discharged -/

/-- **Dong–Jiang Lemma `la4.8`, first mixed regime — discharged.**  For homogeneous `a` of
(integer) weight `K`, arbitrary `b`, base level `m`, a nonnegative index `p₁` and a **negative**
index `d` with `N = p₁ + d − m ≥ 0`,

  `a ∗^N_{m,p₁} b − Res_z (1+z)^{K−1+m−d} Y(a,z)b ∈ O'_{N,m}(𝒱)`.

Proof: for `K < 0` the slice `𝒱_K` is `⊥` (`W.positivity`), so `a = 0` and both terms vanish; for
`K ≥ 0` this is the proved `dj48_case1`, which is even an **exact equality** in `𝒱` — the negativity
of `d` is exactly the hypothesis `N + m < p₁` there, and the two exponents agree,
`K − 1 + m − d = K − 1 + p₁ − N`. -/
theorem dj48Bdry_holds (W : VertexOperatorAlgebra 𝒱) : DJ48Bdry W := by
  intro K a ha b m p₁ N d hd hN
  rcases lt_or_ge K 0 with hKneg | hKpos
  · have ha0 : a = 0 := by
      have h := W.positivity K hKneg
      rw [h, Submodule.mem_bot] at ha
      exact ha
    subst ha0
    rw [anmGen_zero_left, resExp_zero_left, sub_zero]
    exact (Onm W N m).zero_mem
  · obtain ⟨Kn, rfl⟩ := Int.eq_ofNat_of_zero_le hKpos
    have hlt : (N : ℤ) + (m : ℤ) < (p₁ : ℤ) := by omega
    have h := dj48_case1 W ha b m p₁ N hlt
    rw [show (Kn : ℤ) - 1 + (m : ℤ) - d = (Kn : ℤ) - 1 + (p₁ : ℤ) - (N : ℤ) from by omega, h,
      sub_self]
    exact (Onm W N m).zero_mem

/-! ## §2 The mirror mixed regime -/

/-- **Dong–Jiang Lemma `la4.8`, second mixed regime**, `p₁ < 0 ≤ p₂` (the negative index is `d`):

  `−(b ∗^N_{m,p₂} a) − Res_z (1+z)^{K−1+m−p₂} Y(a,z)b ∈ O'_{N,m}(𝒱)`,   `N = d + p₂ − m ≥ 0`.

The companion of `DJ48Bdry`; here the sign and the argument order are DJ's, because the surviving
composition is `b_q a_p`. -/
def DJ48BdryB (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ (K : ℤ) (a : 𝒱), a ∈ W.grading K → ∀ (b : 𝒱) (m p₂ N : ℕ) (d : ℤ),
    d < 0 → (N : ℤ) = d + (p₂ : ℤ) - (m : ℤ) →
      -anmGen W N m p₂ b a - resExp W (K - 1 + (m : ℤ) - (p₂ : ℤ)) a b ∈ Onm W N m

/-- **The mirror mixed regime, discharged**, from the proved `dj48_case2` (whose `O'` enters
through `resHom_skew_mod_Onm`).  Both slots are reduced to their homogeneous slices — `a` by
`W.positivity`, `b` by `reduce_homogeneous` — because `dj48_case2` needs `ℕ`-weights on both. -/
theorem dj48BdryB_holds (W : VertexOperatorAlgebra 𝒱) : DJ48BdryB W := by
  intro K a ha b m p₂ N d hd hN
  rcases lt_or_ge K 0 with hKneg | hKpos
  · have ha0 : a = 0 := by
      have h := W.positivity K hKneg
      rw [h, Submodule.mem_bot] at ha
      exact ha
    subst ha0
    rw [anmGen_zero_right, resExp_zero_left, neg_zero, zero_sub, neg_zero]
    exact (Onm W N m).zero_mem
  · obtain ⟨Kn, rfl⟩ := Int.eq_ofNat_of_zero_le hKpos
    have hlt : (N : ℤ) + (m : ℤ) < (p₂ : ℤ) := by omega
    refine reduce_homogeneous W (P := fun b =>
      -anmGen W N m p₂ b a - resExp W ((Kn : ℤ) - 1 + (m : ℤ) - (p₂ : ℤ)) a b ∈ Onm W N m)
      ?_ ?_ ?_ b
    · intro Mb b hb
      rcases lt_or_ge Mb 0 with hMneg | hMpos
      · have hb0 : b = 0 := by
          have h := W.positivity Mb hMneg
          rw [h, Submodule.mem_bot] at hb
          exact hb
        subst hb0
        change -anmGen W N m p₂ 0 a - resExp W ((Kn : ℤ) - 1 + (m : ℤ) - (p₂ : ℤ)) a 0
          ∈ Onm W N m
        rw [anmGen_zero_left, resExp_zero_right, neg_zero, zero_sub, neg_zero]
        exact (Onm W N m).zero_mem
      · obtain ⟨Mn, rfl⟩ := Int.eq_ofNat_of_zero_le hMpos
        exact dj48_case2 W ha hb m p₂ N hlt
    · change -anmGen W N m p₂ 0 a - resExp W ((Kn : ℤ) - 1 + (m : ℤ) - (p₂ : ℤ)) a 0 ∈ Onm W N m
      rw [anmGen_zero_left, resExp_zero_right, neg_zero, zero_sub, neg_zero]
      exact (Onm W N m).zero_mem
    · intro x y hx hy
      show -anmGen W N m p₂ (x + y) a
          - resExp W ((Kn : ℤ) - 1 + (m : ℤ) - (p₂ : ℤ)) a (x + y) ∈ Onm W N m
      simp only at hx hy
      rw [anmGen_add_left, resExp_add_right]
      have hsplit : -(anmGen W N m p₂ x a + anmGen W N m p₂ y a)
            - (resExp W ((Kn : ℤ) - 1 + (m : ℤ) - (p₂ : ℤ)) a x
              + resExp W ((Kn : ℤ) - 1 + (m : ℤ) - (p₂ : ℤ)) a y)
          = (-anmGen W N m p₂ x a - resExp W ((Kn : ℤ) - 1 + (m : ℤ) - (p₂ : ℤ)) a x)
            + (-anmGen W N m p₂ y a
              - resExp W ((Kn : ℤ) - 1 + (m : ℤ) - (p₂ : ℤ)) a y) := by abel
      rw [hsplit]
      exact (Onm W N m).add_mem hx hy

/-! ## §3 The mixed regimes on representatives, at general base level `m` -/

/-- **DJ Lemma 4.7, mixed regime A, on representatives, at general base level `m`** — the `b`-target
level `n₁ = N + n − n₂` is negative (equivalently `N + n < n₂`), so the composition `a_p b_q`
vanishes identically and only `−b_q a_p` survives:

  `−b ∗^N_{m,n₂}(a ∗^{n₂}_{m,n} g) ≡ ∑ᵢ C(p,i)·(a₍ᵢ₎b) ∗^N_{m,n} g   (mod O_{N,m})`,

with `p = wt a − 1 + n − n₂`.  Ingredients: the `O''` reassociation `bareAssoc_mem_OnmFull`, the
boundary lemma `dj48BdryB_holds` at base level `n`, and DJ Lemma 2.8's right inclusion. -/
theorem anmGen_commutator_bdryA_gen (W : VertexOperatorAlgebra 𝒱) (m : ℕ)
    {K : ℤ} {a : 𝒱} (ha : a ∈ W.grading K) (b : 𝒱) {n n₂ N : ℕ} {p : ℤ}
    (hlt : (N : ℤ) + (n : ℤ) < (n₂ : ℤ)) (hp : p = K - 1 + (n : ℤ) - (n₂ : ℤ)) (g : 𝒱) :
    -anmGen W N m n₂ b (anmGen W n₂ m n a g)
        - ∑ᶠ i : ℕ, gBinom p i • anmGen W N m n (W.smul a i b) g
      ∈ OnmFull W N m := by
  have h₂ : anmGen W N m n₂ b (anmGen W n₂ m n a g)
      - anmGen W N m n (anmGen W N n n₂ b a) g ∈ OnmFull W N m := by
    have h := (OnmFull W N m).neg_mem (bareAssoc_mem_OnmFull W N m n n₂ b a g)
    rwa [neg_sub] at h
  have hD : -anmGen W N n n₂ b a - resExp W p a b ∈ OnmFull W N n := by
    have h := dj48BdryB_holds W K a ha b n n₂ N ((n : ℤ) + (N : ℤ) - (n₂ : ℤ))
      (by omega) (by omega)
    rw [show K - 1 + (n : ℤ) - (n₂ : ℤ) = p from hp.symm] at h
    exact Onm_le_OnmFull W N n h
  have h₃ : anmGen W N m n (-anmGen W N n n₂ b a - resExp W p a b) g ∈ OnmFull W N m :=
    anmGen_OnmFull_right_unconditional W N m n g _ hD
  rw [show anmGen W N m n (-anmGen W N n n₂ b a - resExp W p a b) g
      = -anmGen W N m n (anmGen W N n n₂ b a) g - anmGen W N m n (resExp W p a b) g from by
    have h1 := (anmGenLeftMap W N m n g).map_sub (-anmGen W N n n₂ b a) (resExp W p a b)
    have h2 := (anmGenLeftMap W N m n g).map_neg (anmGen W N n n₂ b a)
    simp only [anmGenLeftMap_apply] at h1 h2
    rw [h1, h2], anmGen_resExp_left] at h₃
  have hcomb : -anmGen W N m n₂ b (anmGen W n₂ m n a g)
      - ∑ᶠ i : ℕ, gBinom p i • anmGen W N m n (W.smul a i b) g
    = -(anmGen W N m n₂ b (anmGen W n₂ m n a g) - anmGen W N m n (anmGen W N n n₂ b a) g)
      + (-anmGen W N m n (anmGen W N n n₂ b a) g
          - ∑ᶠ i : ℕ, gBinom p i • anmGen W N m n (W.smul a i b) g) := by abel
  rw [hcomb]
  exact (OnmFull W N m).add_mem ((OnmFull W N m).neg_mem h₂) h₃

/-- **DJ Lemma 4.7, mixed regime B, on representatives, at general base level `m`** — the `a`-target
level `n₂ = N + n − n₁` is negative (equivalently `N + n < n₁`), so `b_q a_p` vanishes identically
and only `a_p b_q` survives:

  `a ∗^N_{m,n₁}(b ∗^{n₁}_{m,n} g) ≡ ∑ᵢ C(p,i)·(a₍ᵢ₎b) ∗^N_{m,n} g   (mod O_{N,m})`,

with `p = wt a − 1 + n₁ − N` (the value of `wt a − 1 + n − n₂` at the virtual negative `n₂`). -/
theorem anmGen_commutator_bdryB_gen (W : VertexOperatorAlgebra 𝒱) (m : ℕ)
    {K : ℤ} {a : 𝒱} (ha : a ∈ W.grading K) (b : 𝒱) {n n₁ N : ℕ} {p : ℤ}
    (hlt : (N : ℤ) + (n : ℤ) < (n₁ : ℤ)) (hp : p = K - 1 + (n₁ : ℤ) - (N : ℤ)) (g : 𝒱) :
    anmGen W N m n₁ a (anmGen W n₁ m n b g)
        - ∑ᶠ i : ℕ, gBinom p i • anmGen W N m n (W.smul a i b) g
      ∈ OnmFull W N m := by
  have h₁ : anmGen W N m n₁ a (anmGen W n₁ m n b g)
      - anmGen W N m n (anmGen W N n n₁ a b) g ∈ OnmFull W N m := by
    have h := (OnmFull W N m).neg_mem (bareAssoc_mem_OnmFull W N m n n₁ a b g)
    rwa [neg_sub] at h
  have hD : anmGen W N n n₁ a b - resExp W p a b ∈ OnmFull W N n := by
    have h := dj48Bdry_holds W K a ha b n n₁ N ((n : ℤ) + (N : ℤ) - (n₁ : ℤ)) (by omega) (by omega)
    rw [show K - 1 + (n : ℤ) - ((n : ℤ) + (N : ℤ) - (n₁ : ℤ)) = p from by omega] at h
    exact Onm_le_OnmFull W N n h
  have h₃ : anmGen W N m n (anmGen W N n n₁ a b - resExp W p a b) g ∈ OnmFull W N m :=
    anmGen_OnmFull_right_unconditional W N m n g _ hD
  rw [show anmGen W N m n (anmGen W N n n₁ a b - resExp W p a b) g
      = anmGen W N m n (anmGen W N n n₁ a b) g - anmGen W N m n (resExp W p a b) g from by
    have h1 := (anmGenLeftMap W N m n g).map_sub (anmGen W N n n₁ a b) (resExp W p a b)
    simp only [anmGenLeftMap_apply] at h1
    rw [h1], anmGen_resExp_left] at h₃
  have hcomb : anmGen W N m n₁ a (anmGen W n₁ m n b g)
      - ∑ᶠ i : ℕ, gBinom p i • anmGen W N m n (W.smul a i b) g
    = (anmGen W N m n₁ a (anmGen W n₁ m n b g) - anmGen W N m n (anmGen W N n n₁ a b) g)
      + (anmGen W N m n (anmGen W N n n₁ a b) g
          - ∑ᶠ i : ℕ, gBinom p i • anmGen W N m n (W.smul a i b) g) := by abel
  rw [hcomb]
  exact (OnmFull W N m).add_mem h₁ h₃

/-! ## §4 Descent of a representative-level congruence onto the balanced piece -/

section Piece

variable {W : VertexOperatorAlgebra 𝒱} {m : ℕ}

/-- The action of the zero vector on the balanced piece is zero. -/
theorem djPieceAct_zero_acting (U : AmMod W m) (N n : ℕ) (h : DJLeftSlot W N m n) :
    djPieceAct W U N n h (0 : 𝒱) = 0 := by
  have h0 := djPieceAct_smul_acting U N n h (0 : ℂ) (0 : 𝒱)
  simpa using h0

/-- The commutator's OPE family has finite support at the level of `M(U)(n)`-operators. -/
theorem commSum_djPiece_support_finite (U : AmMod W m) (N n : ℕ) (h : DJLeftSlot W N m n) (p : ℤ)
    (a b : 𝒱) (x : DJPiece W U n) :
    (Function.support fun i : ℕ => gBinom p i • djPieceAct W U N n h (W.smul a i b) x).Finite := by
  obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero a b
  refine Set.Finite.subset (Set.finite_Iio Nz.toNat) ?_
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Iio]
  by_contra hcon
  rw [not_lt] at hcon
  exact hi (by
    rw [hNz i (by omega), djPieceAct_zero_acting, LinearMap.zero_apply, smul_zero])

/-- **The descent helper.**  If a `ℂ`-linear `Φ : M(U)(n) → M(U)(N)` is induced on generators by a
representative-level map `φ : 𝒱 → 𝒱`, and `φ g` agrees with the OPE tail
`∑ᵢ C(p,i)·(a₍ᵢ₎b) ∗^N_{m,n} g` modulo the full ideal `O_{N,m}`, then `Φ` **is** the corresponding
operator OPE tail on **every** element of `M(U)(n)`, not just the generators `[g] ⊗ w`. -/
theorem djPieceAct_eq_of_repr_mem (U : AmMod W m) {n N : ℕ} {p : ℤ} (a b : 𝒱)
    (h₅ : DJLeftSlot W N m n) (Φ : DJPiece W U n →ₗ[ℂ] DJPiece W U N) (φ : 𝒱 → 𝒱)
    (hΦ : ∀ (g : 𝒱) (w : U.carrier),
      Φ (mkDJPiece W U n (mkAnmFull W n m g ⊗ₜ[ℂ] w))
        = mkDJPiece W U N (mkAnmFull W N m (φ g) ⊗ₜ[ℂ] w))
    (hmem : ∀ g : 𝒱,
      φ g - ∑ᶠ i : ℕ, gBinom p i • anmGen W N m n (W.smul a i b) g ∈ OnmFull W N m)
    (x : DJPiece W U n) :
    Φ x = ∑ᶠ i : ℕ, gBinom p i • djPieceAct W U N n h₅ (W.smul a i b) x := by
  obtain ⟨z, rfl⟩ := mkDJPiece_surjective U n x
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero]
    exact (finsum_eq_zero_of_forall_eq_zero fun i => by rw [map_zero, smul_zero]).symm
  | tmul t w =>
    refine Submodule.Quotient.induction_on _ t fun g => ?_
    change Φ (mkDJPiece W U n (mkAnmFull W n m g ⊗ₜ[ℂ] w))
      = ∑ᶠ i : ℕ, gBinom p i • djPieceAct W U N n h₅ (W.smul a i b)
          (mkDJPiece W U n (mkAnmFull W n m g ⊗ₜ[ℂ] w))
    rw [hΦ g w]
    let Ψ : 𝒱 →ₗ[ℂ] DJPiece W U N :=
      ((mkDJPiece W U N).comp
        ((TensorProduct.mk ℂ (AnmFull W N m) U.carrier).flip w)).comp (mkAnmFull W N m)
    have hΨ : ∀ y : 𝒱, Ψ y = mkDJPiece W U N (mkAnmFull W N m y ⊗ₜ[ℂ] w) := fun _ => rfl
    have hker : ∀ y ∈ OnmFull W N m, Ψ y = 0 := by
      intro y hy
      have hz : mkAnmFull W N m y = 0 := by
        rw [mkAnmFull, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hy
      rw [hΨ, hz, TensorProduct.zero_tmul, map_zero]
    have hfin := commSum_repr_support_finite_gen W N m n p a b g
    have hRHS : (∑ᶠ i : ℕ, gBinom p i • djPieceAct W U N n h₅ (W.smul a i b)
          (mkDJPiece W U n (mkAnmFull W n m g ⊗ₜ[ℂ] w)))
        = Ψ (∑ᶠ i : ℕ, gBinom p i • anmGen W N m n (W.smul a i b) g) := by
      rw [map_finsum Ψ hfin]
      refine finsum_congr fun i => ?_
      rw [djPieceAct_mk, map_smul, hΨ]
    rw [hRHS, show mkDJPiece W U N (mkAnmFull W N m (φ g) ⊗ₜ[ℂ] w) = Ψ (φ g) from rfl,
      ← sub_eq_zero, ← map_sub]
    exact hker _ (hmem g)
  | add z₁ z₂ hz₁ hz₂ =>
    rw [map_add, map_add, hz₁, hz₂,
      ← finsum_add_distrib (commSum_djPiece_support_finite U N n h₅ p a b (mkDJPiece W U n z₁))
        (commSum_djPiece_support_finite U N n h₅ p a b (mkDJPiece W U n z₂))]
    exact finsum_congr fun i => by rw [map_add, smul_add]

/-! ## §5 The three nontrivial regimes on the balanced piece, on **all** of `M(U)(n)` -/

/-- **DJ Lemma 4.7, interior regime, on all of `M(U)(n)`** (both intermediate levels nonnegative),
at general base level `m`. -/
theorem djPieceAct_commutator_interior_all (U : AmMod W m) {K : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading K) (b : 𝒱) {n n₁ n₂ N : ℕ} {p : ℤ}
    (hN : (N : ℤ) = (n₁ : ℤ) + (n₂ : ℤ) - (n : ℤ)) (hp : p = K - 1 + (n : ℤ) - (n₂ : ℤ))
    (h₁ : DJLeftSlot W N m n₁) (h₂ : DJLeftSlot W n₁ m n) (h₃ : DJLeftSlot W N m n₂)
    (h₄ : DJLeftSlot W n₂ m n) (h₅ : DJLeftSlot W N m n) (x : DJPiece W U n) :
    djPieceAct W U N n₁ h₁ a (djPieceAct W U n₁ n h₂ b x)
        - djPieceAct W U N n₂ h₃ b (djPieceAct W U n₂ n h₄ a x)
      = ∑ᶠ i : ℕ, gBinom p i • djPieceAct W U N n h₅ (W.smul a i b) x := by
  have h := djPieceAct_eq_of_repr_mem U a b h₅
    ((djPieceAct W U N n₁ h₁ a).comp (djPieceAct W U n₁ n h₂ b)
      - (djPieceAct W U N n₂ h₃ b).comp (djPieceAct W U n₂ n h₄ a))
    (fun g => anmGen W N m n₁ a (anmGen W n₁ m n b g) - anmGen W N m n₂ b (anmGen W n₂ m n a g))
    (fun g w => by
      change djPieceAct W U N n₁ h₁ a (djPieceAct W U n₁ n h₂ b
            (mkDJPiece W U n (mkAnmFull W n m g ⊗ₜ[ℂ] w)))
          - djPieceAct W U N n₂ h₃ b (djPieceAct W U n₂ n h₄ a
            (mkDJPiece W U n (mkAnmFull W n m g ⊗ₜ[ℂ] w))) = _
      rw [djPieceAct_mk, djPieceAct_mk, djPieceAct_mk, djPieceAct_mk, ← map_sub,
        ← TensorProduct.sub_tmul, ← map_sub])
    (fun g => anmGen_commutator_interior_gen W m ha b hN hp g) x
  simpa only [LinearMap.sub_apply, LinearMap.comp_apply] using h

/-- **DJ Lemma 4.7, mixed regime A, on all of `M(U)(n)`** — the `b`-target is negative, so `a_p b_q`
vanishes identically. -/
theorem djPieceAct_commutator_bdryA_all (U : AmMod W m) {K : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading K) (b : 𝒱) {n n₂ N : ℕ} {p : ℤ}
    (hlt : (N : ℤ) + (n : ℤ) < (n₂ : ℤ)) (hp : p = K - 1 + (n : ℤ) - (n₂ : ℤ))
    (h₃ : DJLeftSlot W N m n₂) (h₄ : DJLeftSlot W n₂ m n) (h₅ : DJLeftSlot W N m n)
    (x : DJPiece W U n) :
    -djPieceAct W U N n₂ h₃ b (djPieceAct W U n₂ n h₄ a x)
      = ∑ᶠ i : ℕ, gBinom p i • djPieceAct W U N n h₅ (W.smul a i b) x := by
  have h := djPieceAct_eq_of_repr_mem U a b h₅
    (-(djPieceAct W U N n₂ h₃ b).comp (djPieceAct W U n₂ n h₄ a))
    (fun g => -anmGen W N m n₂ b (anmGen W n₂ m n a g))
    (fun g w => by
      change -djPieceAct W U N n₂ h₃ b (djPieceAct W U n₂ n h₄ a
            (mkDJPiece W U n (mkAnmFull W n m g ⊗ₜ[ℂ] w))) = _
      rw [djPieceAct_mk, djPieceAct_mk, ← map_neg, ← TensorProduct.neg_tmul, ← map_neg])
    (fun g => anmGen_commutator_bdryA_gen W m ha b hlt hp g) x
  simpa only [LinearMap.neg_apply, LinearMap.comp_apply] using h

/-- **DJ Lemma 4.7, mixed regime B, on all of `M(U)(n)`** — the `a`-target is negative, so `b_q a_p`
vanishes identically. -/
theorem djPieceAct_commutator_bdryB_all (U : AmMod W m) {K : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading K) (b : 𝒱) {n n₁ N : ℕ} {p : ℤ}
    (hlt : (N : ℤ) + (n : ℤ) < (n₁ : ℤ)) (hp : p = K - 1 + (n₁ : ℤ) - (N : ℤ))
    (h₁ : DJLeftSlot W N m n₁) (h₂ : DJLeftSlot W n₁ m n) (h₅ : DJLeftSlot W N m n)
    (x : DJPiece W U n) :
    djPieceAct W U N n₁ h₁ a (djPieceAct W U n₁ n h₂ b x)
      = ∑ᶠ i : ℕ, gBinom p i • djPieceAct W U N n h₅ (W.smul a i b) x := by
  have h := djPieceAct_eq_of_repr_mem U a b h₅
    ((djPieceAct W U N n₁ h₁ a).comp (djPieceAct W U n₁ n h₂ b))
    (fun g => anmGen W N m n₁ a (anmGen W n₁ m n b g))
    (fun g w => by
      change djPieceAct W U N n₁ h₁ a (djPieceAct W U n₁ n h₂ b
            (mkDJPiece W U n (mkAnmFull W n m g ⊗ₜ[ℂ] w))) = _
      rw [djPieceAct_mk, djPieceAct_mk])
    (fun g => anmGen_commutator_bdryB_gen W m ha b hlt hp g) x
  simpa only [LinearMap.comp_apply] using h

end Piece

/-! ## §6 The operator-level commutator on `DJCarrier`, all four regimes -/

section Mode

variable {W : VertexOperatorAlgebra 𝒱} {m : ℕ}

/-- The mode `a_p` on a level-`n` vector, at a **named** nonnegative target level. -/
theorem djMode_incl_target (U : AmMod W m) (hD : DJActionDescent W m) {k p : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading k) {n N : ℕ} (hN : muTargetLevel k p n = (N : ℤ)) (x : DJPiece W U n) :
    djMode W U hD p a (DJCarrier.incl W U n x)
      = DJCarrier.incl W U N (djPieceAct W U N n (hD N n) a x) := by
  rw [djMode_apply_incl U hD p ha, djLevelIncl_eq_of_target U hD hN a, LinearMap.comp_apply]

/-- The commutator's OPE family has finite support at the level of `M(U)`-operators. -/
theorem commSum_djCarrier_support_finite (U : AmMod W m) (hD : DJActionDescent W m) (p q : ℤ)
    (a b : 𝒱) (x : DJCarrier W U) :
    (Function.support fun i : ℕ =>
        gBinom p i • djMode W U hD (p + q - (i : ℤ)) (W.smul a i b) x).Finite := by
  obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero a b
  refine Set.Finite.subset (Set.finite_Iio Nz.toNat) ?_
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Iio]
  by_contra hcon
  rw [not_lt] at hcon
  exact hi (by rw [hNz i (by omega), djMode_zero_acting, LinearMap.zero_apply, smul_zero])

/-- The OPE tail on a level-`n` vector, when the common target level `N` is **nonnegative**: every
summand has the same target `N`, so the whole sum is the inclusion of a sum in `M(U)(N)`. -/
theorem djMode_ope_incl (U : AmMod W m) (hD : DJActionDescent W m) {K M : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading K) (hb : b ∈ W.grading M) (p q : ℤ) {n N : ℕ}
    (hT : K + M - p - q - 2 + (n : ℤ) = (N : ℤ)) (x : DJPiece W U n) :
    (∑ᶠ i : ℕ, gBinom p i • djMode W U hD (p + q - (i : ℤ)) (W.smul a i b)
        (DJCarrier.incl W U n x))
      = DJCarrier.incl W U N
          (∑ᶠ i : ℕ, gBinom p i • djPieceAct W U N n (hD N n) (W.smul a i b) x) := by
  have hstep : ∀ i : ℕ,
      gBinom p i • djMode W U hD (p + q - (i : ℤ)) (W.smul a i b) (DJCarrier.incl W U n x)
        = DJCarrier.incl W U N (gBinom p i • djPieceAct W U N n (hD N n) (W.smul a i b) x) := by
    intro i
    have hmode : djMode W U hD (p + q - (i : ℤ)) (W.smul a i b) (DJCarrier.incl W U n x)
        = DJCarrier.incl W U N (djPieceAct W U N n (hD N n) (W.smul a i b) x) :=
      djMode_incl_target U hD (W.smul_mem_grading ha hb (i : ℤ))
        (by simp only [muTargetLevel]; omega) x
    rw [hmode, map_smul]
  rw [finsum_congr hstep]
  exact (map_finsum (DJCarrier.incl W U N)
    (commSum_djPiece_support_finite U N n (hD N n) p a b x)).symm

/-- The OPE tail on a level-`n` vector vanishes when the common target level is **negative**. -/
theorem djMode_ope_incl_zero (U : AmMod W m) (hD : DJActionDescent W m) {K M : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading K) (hb : b ∈ W.grading M) (p q : ℤ) {n : ℕ}
    (hT : K + M - p - q - 2 + (n : ℤ) < 0) (x : DJPiece W U n) :
    (∑ᶠ i : ℕ, gBinom p i • djMode W U hD (p + q - (i : ℤ)) (W.smul a i b)
        (DJCarrier.incl W U n x)) = 0 := by
  refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
  rw [djMode_incl_eq_zero U hD (W.smul_mem_grading ha hb (i : ℤ)) (by omega) x, smul_zero]

/-- **Dong–Jiang Lemma 4.7 on a level piece of `DJCarrier`, in ALL FOUR REGIMES.**  For
homogeneous `a` (weight `K`), homogeneous `b` (weight `M`), all `p, q ∈ ℤ` and every
`x ∈ M(U)(n)`:

  `a_p b_q x − b_q a_p x = ∑ᵢ C(p,i)·(a₍ᵢ₎b)_{p+q−i} x`.

The four regimes, split on the intermediate levels `n₁ = M − q − 1 + n`, `n₂ = K − p − 1 + n` and
the common target `N = n₁ + n₂ − n`:
`N < 0` (everything vanishes), `n₁, n₂ ≥ 0` (interior), `n₁ < 0` (regime A), `n₂ < 0` (regime B). -/
theorem djMode_commutator_incl (U : AmMod W m) (hD : DJActionDescent W m) {K M : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading K) (hb : b ∈ W.grading M) (p q : ℤ) (n : ℕ) (x : DJPiece W U n) :
    djMode W U hD p a (djMode W U hD q b (DJCarrier.incl W U n x))
        - djMode W U hD q b (djMode W U hD p a (DJCarrier.incl W U n x))
      = ∑ᶠ i : ℕ, gBinom p i • djMode W U hD (p + q - (i : ℤ)) (W.smul a i b)
          (DJCarrier.incl W U n x) := by
  rcases lt_or_ge (K + M - p - q - 2 + (n : ℤ)) 0 with hTneg | hTpos
  · -- Regime 0: the common target level is negative — every term vanishes.
    rw [djMode_ope_incl_zero U hD ha hb p q hTneg x]
    have hfirst : djMode W U hD p a (djMode W U hD q b (DJCarrier.incl W U n x)) = 0 := by
      rcases lt_or_ge (M - q - 1 + (n : ℤ)) 0 with h₁ | h₁
      · have e : djMode W U hD q b (DJCarrier.incl W U n x) = 0 :=
          djMode_incl_eq_zero U hD hb (by omega) x
        rw [e, map_zero]
      · obtain ⟨n₁, hn₁⟩ : ∃ n₁ : ℕ, M - q - 1 + (n : ℤ) = (n₁ : ℤ) :=
          ⟨_, (Int.toNat_of_nonneg h₁).symm⟩
        have e : djMode W U hD q b (DJCarrier.incl W U n x)
            = DJCarrier.incl W U n₁ (djPieceAct W U n₁ n (hD n₁ n) b x) :=
          djMode_incl_target U hD hb (by simp only [muTargetLevel]; omega) x
        rw [e]
        exact djMode_incl_eq_zero U hD ha (by omega) _
    have hsecond : djMode W U hD q b (djMode W U hD p a (DJCarrier.incl W U n x)) = 0 := by
      rcases lt_or_ge (K - p - 1 + (n : ℤ)) 0 with h₂ | h₂
      · have e : djMode W U hD p a (DJCarrier.incl W U n x) = 0 :=
          djMode_incl_eq_zero U hD ha (by omega) x
        rw [e, map_zero]
      · obtain ⟨n₂, hn₂⟩ : ∃ n₂ : ℕ, K - p - 1 + (n : ℤ) = (n₂ : ℤ) :=
          ⟨_, (Int.toNat_of_nonneg h₂).symm⟩
        have e : djMode W U hD p a (DJCarrier.incl W U n x)
            = DJCarrier.incl W U n₂ (djPieceAct W U n₂ n (hD n₂ n) a x) :=
          djMode_incl_target U hD ha (by simp only [muTargetLevel]; omega) x
        rw [e]
        exact djMode_incl_eq_zero U hD hb (by omega) _
    rw [hfirst, hsecond, sub_zero]
  · obtain ⟨N, hN⟩ : ∃ N : ℕ, K + M - p - q - 2 + (n : ℤ) = (N : ℤ) :=
      ⟨_, (Int.toNat_of_nonneg hTpos).symm⟩
    rw [djMode_ope_incl U hD ha hb p q hN x]
    rcases lt_or_ge (M - q - 1 + (n : ℤ)) 0 with h₁ | h₁
    · -- Regime A: the `b`-target is negative, so `a_p b_q` vanishes.
      obtain ⟨n₂, hn₂⟩ : ∃ n₂ : ℕ, K - p - 1 + (n : ℤ) = (n₂ : ℤ) :=
        ⟨_, (Int.toNat_of_nonneg (by omega)).symm⟩
      have hlt' : (N : ℤ) + (n : ℤ) < (n₂ : ℤ) := by omega
      have hp' : p = K - 1 + (n : ℤ) - (n₂ : ℤ) := by omega
      have e1 : djMode W U hD q b (DJCarrier.incl W U n x) = 0 :=
        djMode_incl_eq_zero U hD hb (by omega) x
      have e2 : djMode W U hD p a (DJCarrier.incl W U n x)
          = DJCarrier.incl W U n₂ (djPieceAct W U n₂ n (hD n₂ n) a x) :=
        djMode_incl_target U hD ha (by simp only [muTargetLevel]; omega) x
      have e3 : djMode W U hD q b (DJCarrier.incl W U n₂ (djPieceAct W U n₂ n (hD n₂ n) a x))
          = DJCarrier.incl W U N
              (djPieceAct W U N n₂ (hD N n₂) b (djPieceAct W U n₂ n (hD n₂ n) a x)) :=
        djMode_incl_target U hD hb (by simp only [muTargetLevel]; omega) _
      rw [e1, map_zero, e2, e3, zero_sub, ← map_neg]
      exact congrArg (DJCarrier.incl W U N)
        (djPieceAct_commutator_bdryA_all U ha b hlt' hp' (hD N n₂) (hD n₂ n) (hD N n) x)
    · obtain ⟨n₁, hn₁⟩ : ∃ n₁ : ℕ, M - q - 1 + (n : ℤ) = (n₁ : ℤ) :=
        ⟨_, (Int.toNat_of_nonneg h₁).symm⟩
      have e1 : djMode W U hD q b (DJCarrier.incl W U n x)
          = DJCarrier.incl W U n₁ (djPieceAct W U n₁ n (hD n₁ n) b x) :=
        djMode_incl_target U hD hb (by simp only [muTargetLevel]; omega) x
      have e2 : djMode W U hD p a (DJCarrier.incl W U n₁ (djPieceAct W U n₁ n (hD n₁ n) b x))
          = DJCarrier.incl W U N
              (djPieceAct W U N n₁ (hD N n₁) a (djPieceAct W U n₁ n (hD n₁ n) b x)) :=
        djMode_incl_target U hD ha (by simp only [muTargetLevel]; omega) _
      rcases lt_or_ge (K - p - 1 + (n : ℤ)) 0 with h₂ | h₂
      · -- Regime B: the `a`-target is negative, so `b_q a_p` vanishes.
        have hlt' : (N : ℤ) + (n : ℤ) < (n₁ : ℤ) := by omega
        have hp' : p = K - 1 + (n₁ : ℤ) - (N : ℤ) := by omega
        have e3 : djMode W U hD p a (DJCarrier.incl W U n x) = 0 :=
          djMode_incl_eq_zero U hD ha (by omega) x
        rw [e1, e2, e3, map_zero, sub_zero]
        exact congrArg (DJCarrier.incl W U N)
          (djPieceAct_commutator_bdryB_all U ha b hlt' hp' (hD N n₁) (hD n₁ n) (hD N n) x)
      · -- Interior regime: both intermediate levels are nonnegative.
        obtain ⟨n₂, hn₂⟩ : ∃ n₂ : ℕ, K - p - 1 + (n : ℤ) = (n₂ : ℤ) :=
          ⟨_, (Int.toNat_of_nonneg h₂).symm⟩
        have hNlev : (N : ℤ) = (n₁ : ℤ) + (n₂ : ℤ) - (n : ℤ) := by omega
        have hp' : p = K - 1 + (n : ℤ) - (n₂ : ℤ) := by omega
        have e3 : djMode W U hD p a (DJCarrier.incl W U n x)
            = DJCarrier.incl W U n₂ (djPieceAct W U n₂ n (hD n₂ n) a x) :=
          djMode_incl_target U hD ha (by simp only [muTargetLevel]; omega) x
        have e4 : djMode W U hD q b (DJCarrier.incl W U n₂ (djPieceAct W U n₂ n (hD n₂ n) a x))
            = DJCarrier.incl W U N
                (djPieceAct W U N n₂ (hD N n₂) b (djPieceAct W U n₂ n (hD n₂ n) a x)) :=
          djMode_incl_target U hD hb (by simp only [muTargetLevel]; omega) _
        rw [e1, e2, e3, e4, ← map_sub]
        exact congrArg (DJCarrier.incl W U N)
          (djPieceAct_commutator_interior_all U ha b hNlev hp' (hD N n₁) (hD n₁ n) (hD N n₂)
            (hD n₂ n) (hD N n) x)

/-- **Dong–Jiang Lemma 4.7 on all of `M(U) = DJCarrier W U`, in all four regimes**, at general
base level `m`.  For homogeneous `a, b` and all `p, q ∈ ℤ`,

  `[a_p, b_q] = ∑_{i ≥ 0} C(p,i)·(a₍ᵢ₎b)_{p+q−i}`

as `ℂ`-linear operators on `M(U)`.  The only input is DJ's action descent
`hD : DJActionDescent W m` (DJ Lemma 2.8's left inclusion), which is a **theorem** at `m = 0`. -/
theorem djMode_commutator (U : AmMod W m) (hD : DJActionDescent W m) {K M : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading K) (hb : b ∈ W.grading M) (p q : ℤ) (x : DJCarrier W U) :
    djMode W U hD p a (djMode W U hD q b x) - djMode W U hD q b (djMode W U hD p a x)
      = ∑ᶠ i : ℕ, gBinom p i • djMode W U hD (p + q - (i : ℤ)) (W.smul a i b) x := by
  refine DirectSum.induction_on x ?_ ?_ ?_
  · simp only [map_zero, smul_zero, finsum_zero, sub_zero]
  · intro n y
    exact djMode_commutator_incl U hD ha hb p q n y
  · intro y z hy hz
    have hsplit : djMode W U hD p a (djMode W U hD q b (y + z))
        - djMode W U hD q b (djMode W U hD p a (y + z))
      = (djMode W U hD p a (djMode W U hD q b y) - djMode W U hD q b (djMode W U hD p a y))
        + (djMode W U hD p a (djMode W U hD q b z)
          - djMode W U hD q b (djMode W U hD p a z)) := by
      simp only [map_add]; abel
    rw [hsplit, hy, hz,
      ← finsum_add_distrib (commSum_djCarrier_support_finite U hD p q a b y)
        (commSum_djCarrier_support_finite U hD p q a b z)]
    exact finsum_congr fun i => by rw [map_add, smul_add]

/-! ### Removing the homogeneity of `a` and `b`

Both sides are `ℂ`-bilinear in `(a, b)`: the left one because `djMode` is linear in the acting
vector (`djMode_add_acting`), the right one because `a₍ᵢ₎b` is bilinear
(`PreVertexAlgebra.smul_add_left`/`smul_add_right`) and the OPE family stays finitely supported. -/

/-- The commutator identity, as a predicate in the right slot — the shape `reduce_homogeneous`
consumes. -/
private def CommIdRight (U : AmMod W m) (hD : DJActionDescent W m) (a : 𝒱) (p q : ℤ)
    (x : DJCarrier W U) (b : 𝒱) : Prop :=
  djMode W U hD p a (djMode W U hD q b x) - djMode W U hD q b (djMode W U hD p a x)
    = ∑ᶠ i : ℕ, gBinom p i • djMode W U hD (p + q - (i : ℤ)) (W.smul a i b) x

/-- **Dong–Jiang Lemma 4.7 on `M(U)`, for ARBITRARY `a, b ∈ 𝒱`** (no homogeneity), all four
regimes, at general base level `m`:

  `[a_p, b_q] = ∑_{i ≥ 0} C(p,i)·(a₍ᵢ₎b)_{p+q−i}`   on all of `M(U) = DJCarrier W U`.

Obtained from the homogeneous `djMode_commutator` by reducing each slot to its graded pieces. -/
theorem djMode_commutator_gen (U : AmMod W m) (hD : DJActionDescent W m) (a b : 𝒱) (p q : ℤ)
    (x : DJCarrier W U) :
    djMode W U hD p a (djMode W U hD q b x) - djMode W U hD q b (djMode W U hD p a x)
      = ∑ᶠ i : ℕ, gBinom p i • djMode W U hD (p + q - (i : ℤ)) (W.smul a i b) x := by
  refine reduce_homogeneous W (P := fun a => ∀ c : 𝒱, CommIdRight U hD a p q x c) ?_ ?_ ?_ a b
  · -- `a` homogeneous: reduce the right slot
    intro K a ha
    refine reduce_homogeneous W (P := fun c => CommIdRight U hD a p q x c) ?_ ?_ ?_
    · intro M b hb
      exact djMode_commutator U hD ha hb p q x
    · change djMode W U hD p a (djMode W U hD q 0 x) - djMode W U hD q 0 (djMode W U hD p a x)
        = ∑ᶠ i : ℕ, gBinom p i • djMode W U hD (p + q - (i : ℤ)) (W.smul a i 0) x
      rw [djMode_zero_acting, LinearMap.zero_apply, LinearMap.zero_apply, map_zero, sub_zero]
      exact (finsum_eq_zero_of_forall_eq_zero fun i => by
        rw [show W.smul a (i : ℤ) 0 = 0 from W.smul_zero_right _ _, djMode_zero_acting,
          LinearMap.zero_apply, smul_zero]).symm
    · intro b₁ b₂ h₁ h₂
      change djMode W U hD p a (djMode W U hD q (b₁ + b₂) x)
          - djMode W U hD q (b₁ + b₂) (djMode W U hD p a x)
        = ∑ᶠ i : ℕ, gBinom p i • djMode W U hD (p + q - (i : ℤ)) (W.smul a i (b₁ + b₂)) x
      have hsplit : djMode W U hD p a (djMode W U hD q (b₁ + b₂) x)
          - djMode W U hD q (b₁ + b₂) (djMode W U hD p a x)
        = (djMode W U hD p a (djMode W U hD q b₁ x)
            - djMode W U hD q b₁ (djMode W U hD p a x))
          + (djMode W U hD p a (djMode W U hD q b₂ x)
            - djMode W U hD q b₂ (djMode W U hD p a x)) := by
        rw [djMode_add_acting]
        simp only [LinearMap.add_apply, map_add]
        abel
      rw [hsplit, h₁, h₂,
        ← finsum_add_distrib (commSum_djCarrier_support_finite U hD p q a b₁ x)
          (commSum_djCarrier_support_finite U hD p q a b₂ x)]
      refine finsum_congr fun i => ?_
      rw [show W.smul a (i : ℤ) (b₁ + b₂) = W.smul a (i : ℤ) b₁ + W.smul a (i : ℤ) b₂ from
        PreVertexAlgebra.smul_add_right _ _ _ _ _, djMode_add_acting, LinearMap.add_apply, smul_add]
  · -- `a = 0`
    intro c
    change djMode W U hD p 0 (djMode W U hD q c x) - djMode W U hD q c (djMode W U hD p 0 x)
      = ∑ᶠ i : ℕ, gBinom p i • djMode W U hD (p + q - (i : ℤ)) (W.smul 0 i c) x
    rw [djMode_zero_acting, LinearMap.zero_apply, LinearMap.zero_apply, map_zero, zero_sub,
      neg_zero]
    exact (finsum_eq_zero_of_forall_eq_zero fun i => by
      rw [show W.smul 0 (i : ℤ) c = 0 from W.smul_zero_left _ _, djMode_zero_acting,
        LinearMap.zero_apply, smul_zero]).symm
  · -- additivity in `a`
    intro a₁ a₂ h₁ h₂ c
    have hc₁ := h₁ c
    have hc₂ := h₂ c
    change djMode W U hD p (a₁ + a₂) (djMode W U hD q c x)
        - djMode W U hD q c (djMode W U hD p (a₁ + a₂) x)
      = ∑ᶠ i : ℕ, gBinom p i • djMode W U hD (p + q - (i : ℤ)) (W.smul (a₁ + a₂) i c) x
    have hsplit : djMode W U hD p (a₁ + a₂) (djMode W U hD q c x)
        - djMode W U hD q c (djMode W U hD p (a₁ + a₂) x)
      = (djMode W U hD p a₁ (djMode W U hD q c x)
          - djMode W U hD q c (djMode W U hD p a₁ x))
        + (djMode W U hD p a₂ (djMode W U hD q c x)
          - djMode W U hD q c (djMode W U hD p a₂ x)) := by
      rw [djMode_add_acting]
      simp only [LinearMap.add_apply, map_add]
      abel
    rw [hsplit, hc₁, hc₂,
      ← finsum_add_distrib (commSum_djCarrier_support_finite U hD p q a₁ c x)
        (commSum_djCarrier_support_finite U hD p q a₂ c x)]
    refine finsum_congr fun i => ?_
    rw [show W.smul (a₁ + a₂) (i : ℤ) c = W.smul a₁ (i : ℤ) c + W.smul a₂ (i : ℤ) c from
      PreVertexAlgebra.smul_add_left _ _ _ _ _, djMode_add_acting, LinearMap.add_apply, smul_add]

/-- The hypothesis-free base-level instance: DJ Lemma 4.7 on `M(U)` at `m = 0`, all four regimes. -/
theorem djModeZero_commutator (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) {K M : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading K) (hb : b ∈ W.grading M) (p q : ℤ) (x : DJCarrier W U) :
    djModeZero W U p a (djModeZero W U q b x) - djModeZero W U q b (djModeZero W U p a x)
      = ∑ᶠ i : ℕ, gBinom p i • djModeZero W U (p + q - (i : ℤ)) (W.smul a i b) x :=
  djMode_commutator U (djActionDescent_zero W) ha hb p q x

/-- The hypothesis-free base-level instance for **arbitrary** `a, b`: DJ Lemma 4.7 on `M(U)` at
`m = 0`, all four regimes, no homogeneity, no carried hypothesis whatsoever. -/
theorem djModeZero_commutator_gen (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) (a b : 𝒱)
    (p q : ℤ) (x : DJCarrier W U) :
    djModeZero W U p a (djModeZero W U q b x) - djModeZero W U q b (djModeZero W U p a x)
      = ∑ᶠ i : ℕ, gBinom p i • djModeZero W U (p + q - (i : ℤ)) (W.smul a i b) x :=
  djMode_commutator_gen U (djActionDescent_zero W) a b p q x

end Mode

end VOA

/-
`#print axioms` check (each of the following prints `[propext, Classical.choice, Quot.sound]`,
NO `pbw`, NO `sorryAx`):

  #print axioms VOA.dj48Bdry_holds
  #print axioms VOA.dj48BdryB_holds
  #print axioms VOA.anmGen_commutator_bdryA_gen
  #print axioms VOA.anmGen_commutator_bdryB_gen
  #print axioms VOA.djPieceAct_eq_of_repr_mem
  #print axioms VOA.djPieceAct_commutator_interior_all
  #print axioms VOA.djPieceAct_commutator_bdryA_all
  #print axioms VOA.djPieceAct_commutator_bdryB_all
  #print axioms VOA.djMode_commutator_incl
  #print axioms VOA.djMode_commutator
  #print axioms VOA.djMode_commutator_gen
  #print axioms VOA.djModeZero_commutator
  #print axioms VOA.djModeZero_commutator_gen
-/
