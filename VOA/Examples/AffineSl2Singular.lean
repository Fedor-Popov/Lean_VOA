/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.Examples.AffineSl2VOA

/-!
# The weight-3 singular vector of `V^k(𝔰𝔩₂)`, and `k = -4/3` as a THEOREM

The representation-theoretic input for deformation rigidity of simple affine VOAs
(Linshaw–Qi, arXiv:2601.12017, Thm 5.1): explicit control of the singular vector of the
universal affine VOA `V^k(𝔰𝔩₂) = WakModule k` at conformal weight `3`.

**Nothing here is transcribed from the literature.**  The singularity conditions are imposed on a
general element of the weight-3 charge-2 space and solved; the level drops out of the elimination
as the single equation `(3k + 4)·g = 0`.  See the discrepancy report in §D below.

## §A  Conventions found in this repository (read off `Examples/AffineSl2`)

* Colours `colE = 0`, `colF = 1`, `colH = 2` of the Chevalley basis of `𝔰𝔩₂`, with
  `fabc` giving `⁅h,e⁆ = 2e`, `⁅h,f⁆ = -2f`, `⁅e,f⁆ = h`, and the normalised Killing form
  `kappa` giving `κ(e,f) = κ(f,e) = 1`, `κ(h,h) = 2`, all other entries `0`.
* Modes: `J k a m : End ℂ (WakModule k)` is `x_a ⊗ tᵐ` acting on the level-`k` vacuum module.
  `current_comm` reads
  `⁅J^a_m, J^b_n⁆ = ∑_c f^{ab}_c J^c_{m+n} + m·k·κ(a,b)·δ_{m+n,0}`,
  so in the named form used here
  `⁅e_m, f_n⁆ = h_{m+n} + m k δ`, `⁅h_m, e_n⁆ = 2 e_{m+n}`, `⁅h_m, f_n⁆ = -2 f_{m+n}`,
  `⁅h_m, h_n⁆ = 2 m k δ`, `⁅e_m,e_n⁆ = ⁅f_m,f_n⁆ = 0`.
  Note the sign convention this forces: `⁅f_m, e_n⁆ = -h_{m+n} + m k δ` (the central term keeps
  the *left* mode `m`, not `n`).  This is the single place where a convention slip would flip an
  answer, and it is isolated in `Jc_ne`/`Jc_eq`.
* Vacuum `vacuumA k`, annihilated by `J k a n` for `n ≥ 0` (`J_vac`).
* Energy grading `gradingZA k n` (the `ℓ₀`-eigenspace of eigenvalue `-n`); `J k a m` maps
  `gradingZA k n` to `gradingZA k (n - m)`, and `gradingZA k n = ⊥` for `n < 0`.
* **Naming**: this file uses no Virasoro-module name; in particular it does **not** mention
  `VirUniv`, so the naming convention for `VirUniv` (universal vacuum module vs. simple quotient
  `L(c,0)`) does not touch any declaration here.

## §B  The weight-3, charge-2 subspace and the linear system

Under the Cartan charge (`h₀`-eigenvalue: `e ↦ +2`, `h ↦ 0`, `f ↦ -2`), the PBW monomials of
conformal weight `3` and charge `+2` are exactly five:
`M1 = e₋₃|0⟩`, `M2 = e₋₂h₋₁|0⟩`, `M3 = h₋₂e₋₁|0⟩`, `M4 = e₋₁e₋₁f₋₁|0⟩`, `M5 = e₋₁h₋₁h₋₁|0⟩`
(normal order: modes weakly increasing left-to-right, ties broken `e < f < h`).

Which conditions are imposed, and why they suffice.  For the affine algebra `𝔰𝔩₂^` the positive
part `n̂₊ = ℂ e₀ ⊕ span{x_n : n ≥ 1}` is generated as a Lie algebra by the two affine Chevalley
raising generators `e₀` and `f₁`.  A singular (= affine highest-weight) vector is therefore one
annihilated by `e₀` and `f₁`; it need **not** be `𝔰𝔩₂`-invariant, and indeed the vector below is
not — it has `h₀`-charge `+2` (`sl2Singular_H0`), i.e. it is the highest-weight vector of an
`𝔰𝔩₂` adjoint (spin-1) triplet, so `f₀ s ≠ 0`.  Imposing `f₀ s = 0` as well would ask for an
`𝔰𝔩₂` singlet and has **no** nonzero solution at weight 3 at any level.

`e₀` maps the space to the weight-3 charge-4 span `{P1 = e₋₂e₋₁|0⟩, P2 = e₋₁e₋₁h₋₁|0⟩}`
(`E0_ansatz`), and `f₁` to the weight-2 charge-0 span
`{Q1 = h₋₂|0⟩, Q2 = e₋₁f₋₁|0⟩, Q3 = h₋₁h₋₁|0⟩}` (`F1_ansatz`).  Writing
`s = a M1 + b M2 + c M3 + d M4 + g M5` this gives the 5×5 system `SingSys`:

```
  b + c + 2g          = 0      (coefficient of P1 in e₀ s, divided by -2)
  d - 4g              = 0      (coefficient of P2 in e₀ s)
  -a + (k-2) c        = 0      (coefficient of Q1 in f₁ s)
  c + (k+1) d + 2g    = 0      (coefficient of Q2 in f₁ s, divided by 2)
  k g - b             = 0      (coefficient of Q3 in f₁ s)
```

whose determinant is `-4(3k+4)`.

## §C  Results

* `SingSys_param` — every solution is `b = kg`, `c = -(k+2)g`, `d = 4g`, `a = -(k-2)(k+2)g`,
  together with the elimination `(3k+4)·g = 0`.
* `exists_nonzero_solution_iff` — **the level is a theorem**: a nonzero solution exists iff
  `3k + 4 = 0`, i.e. `k = -4/3`.
* `sl2Singular : WakModule (-4/3)` — the explicit integral vector (`g = 9`)
  `s = 20 e₋₃|0⟩ - 12 e₋₂h₋₁|0⟩ - 6 h₋₂e₋₁|0⟩ + 36 e₋₁e₋₁f₋₁|0⟩ + 9 e₋₁h₋₁h₋₁|0⟩`.
* `sl2Singular_E0`, `sl2Singular_E1`, `sl2Singular_F1`, `sl2Singular_H1` — the direct
  verifications; `sl2Singular_H0 : h₀ s = 2 s`; and `sl2Singular_pos` — every mode of positive
  level annihilates `s` (levels 2, 3 by brackets of the level-1 relations, levels `≥ 4` by the
  energy grading).
* `SingSys_of_annihilated`, `ansatz_eq_zero_of_level_ne` — the converse direction, conditional on
  PBW independence of the *target* monomials `{P1,P2}` and `{Q1,Q2,Q3}`.
* `sl2Singular_ne_zero_of_indep` — nonvanishing, conditional on PBW independence of `M1,…,M5`.
  (The unconditional, `pbw`-free nonvanishing is `Wak.sl2Singular_ne_zero`, `Examples.WakimotoFree`.)

## §D  Agreement with the literature form (there is no discrepancy)

Linshaw–Qi, *Deformation rigidity of some simple affine VOAs*, arXiv:2601.12017v2, §5 give

  `s = −48 h₍₋₁₎e₍₋₂₎𝟙 + 36 e₍₋₁₎²f₍₋₁₎𝟙 − 6 h₍₋₂₎e₍₋₁₎𝟙 + 9 h₍₋₁₎²e₍₋₁₎𝟙 + 80 e₍₋₃₎𝟙`

(their source is Adamović, J. Pure Appl. Alg. **196** (2005) 119–134).  This **agrees exactly**
with `ansatz (-4/3) 20 (-12) (-6) 36 9`; the two differ only by operator ordering.  Reordering
with `⁅h₍₋₁₎,e₍₋₂₎⁆ = 2e₍₋₃₎` and `⁅h₍₋₁₎,e₍₋₁₎⁆ = 2e₍₋₂₎`:

  `h₍₋₁₎e₍₋₂₎𝟙 = M2 + 2·M1`,   `h₍₋₁₎²e₍₋₁₎𝟙 = M5 + 4·M2 + 4·M1`,

so  `80·M1 − 48(M2+2M1) − 6·M3 + 36·M4 + 9(M5+4M2+4M1) = 20M1 − 12M2 − 6M3 + 36M4 + 9M5`,
which is this file's vector on the nose.  Machine-checked as `lqVector_eq_ansatz`
(`Examples/AffineSl2Rigidity43.lean`).

⚠ **There is no discrepancy.**  Comparing the
`e₋₂h₋₁` coefficients `−12` and `−48` while tracking only the `h₍₋₁₎e₍₋₂₎` term forgets that
`9·h₍₋₁₎²e₍₋₁₎𝟙` contributes a further `9·4 = 36` to the very same monomial: `−48 + 36 = −12`.
Explanations such as a rescaled extract or normally-ordered field products are unnecessary.
Recorded here so the false alarm is not raised again.

## §E  What is NOT proved here (honest gaps)

1. **Weight-3 spanning.**  The full statement `gradingZA k 3 = span{the 22 PBW monomials}`
   (`3 + 9 + 10` monomials: `x₋₃`, `x₋₂y₋₁`, and the degree-3 symmetric monomials in `x₋₁`) is
   *not* proved.  `AffineLie.eigenspace_eq_degSpan` reduces it to straightening every degree-3
   `negWord`, which is a separate finite but sizeable induction.  Consequently the results here
   say "there is a singular vector of this shape, and within the five-monomial ansatz it exists
   only at `k = -4/3`", not "these are all weight-3 singular vectors".
2. **Nonvanishing.**  In this file only conditionally (`sl2Singular_ne_zero_of_indep`).  Proved
   unconditionally and `pbw`-free downstream: `Wak.sl2Singular_ne_zero` (`Examples.WakimotoFree`).
3. **The ideal / `L_{-4/3}(𝔰𝔩₂) ≠ V^{-4/3}(𝔰𝔩₂)`.**  Not in this file; proved downstream as
   `LQ43.sl2Singular_mem_maxGradedIdeal` and `LQ43.maxGradedIdeal_ne_bot`
   (`Examples.AffineSl2Rigidity43`).

## §F  Cross-check (CAS, NOT formalised)

A computer-algebra sweep of the affine `𝔰𝔩₂` vacuum module — imposing `e₀ s = 0` and `f₁ s = 0`
on every `(weight, charge)` sector and reading off the levels at which the coefficient matrix
drops rank — gives, for weights `1..4`:

| weight | charge | dim | singular levels |
|---|---|---|---|
| 1 | +2 | 1 | `k = 0` |
| 2 | +4 | 1 | `k = 1` |
| 2 | 0 | 3 | `k = -2` (critical) |
| 3 | +6 | 1 | `k = 2` |
| 3 | **+2** | **5** | **`k = -4/3`** |
| 4 | +8 | 1 | `k = 3` |
| 4 | +4 | 6 | `k = -1/2` |

every other sector in that range having no singular vector at any level.  So at weight 3 the
charge-`+2` sector is the only one that produces a singular vector, and it does so only at
`k = -4/3`; the `k = 0, 1, 2, 3` entries are the familiar `e₋₁^{k+1}|0⟩` integrable-level vectors,
`k = -2` is the critical-level Sugawara vector, and `k = -1/2` is the next admissible level
(`k + 2 = 3/2`), matching `k = -4/3` (`k + 2 = 2/3`) as boundary-admissible data.  This table is
context only — it is a CAS computation, not a Lean theorem; the charge-`+2` weight-3 row is what
is formalised above.

## §G  Axioms

Everything in this file is `sorry`-free and introduces no axiom.  `#print axioms` on every
main result (`exists_nonzero_solution_iff`, `SingSys_param`, `sl2Singular`,
`sl2Singular_E0/F1/H0/pos`, `SingSys_of_annihilated`, `ansatz_eq_zero_of_level_ne`,
`sl2Singular_ne_zero_of_indep`) reports exactly `[propext, Classical.choice, Quot.sound]` —
**`pbw`-free**: the computational content rests on `current_comm` and `vacuum_pos_annihilate`,
neither of which reaches the PBW theorem `VOA.pbw`.

## References
Linshaw–Qi, arXiv:2601.12017 §5; Kac, *Infinite Dimensional Lie Algebras* §9–§10 (singular
vectors and the Kac–Kazhdan condition); Gannon §3.2.
-/

open scoped BigOperators
open Module (End)
open VOA VOA.AffineVOA VOA.AffineLie

namespace VOA.Sl2Sing

/-! ## §1  The applied commutators -/

/-- Applied affine commutator, non-central branch. -/
theorem Jc_ne (k : ℂ) (a b : Fin 3) {m n : ℤ} (h : m + n ≠ 0) (v : WakModule k) :
    J k a m (J k b n v) = J k b n (J k a m v)
      + (fabc a b 0 • J k 0 (m + n) v + fabc a b 1 • J k 1 (m + n) v
          + fabc a b 2 • J k 2 (m + n) v) := by
  have hop : J k a m * J k b n - J k b n * J k a m = ∑ c, fabc a b c • J k c (m + n) := by
    rw [current_comm, if_neg h, add_zero]
  have hv : J k a m (J k b n v) - J k b n (J k a m v)
      = ∑ c, fabc a b c • J k c (m + n) v := by
    have h2 := LinearMap.congr_fun hop v
    simpa only [LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply] using h2
  rw [Fin.sum_univ_three, sub_eq_iff_eq_add] at hv
  rw [hv]; abel

/-- Applied affine commutator, central branch `m + n = 0`. -/
theorem Jc_eq (k : ℂ) (a b : Fin 3) {m n : ℤ} (h : m + n = 0) (v : WakModule k) :
    J k a m (J k b n v) = J k b n (J k a m v)
      + (fabc a b 0 • J k 0 (m + n) v + fabc a b 1 • J k 1 (m + n) v
          + fabc a b 2 • J k 2 (m + n) v)
      + ((m : ℂ) * k * kappa a b) • v := by
  have hop : J k a m * J k b n - J k b n * J k a m
      = (∑ c, fabc a b c • J k c (m + n)) + ((m : ℂ) * k * kappa a b) • LinearMap.id := by
    rw [current_comm, if_pos h]
  have hv : J k a m (J k b n v) - J k b n (J k a m v)
      = (∑ c, fabc a b c • J k c (m + n) v) + ((m : ℂ) * k * kappa a b) • v := by
    have h2 := LinearMap.congr_fun hop v
    simpa only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, LinearMap.id_coe, id_eq] using h2
  rw [Fin.sum_univ_three, sub_eq_iff_eq_add] at hv
  rw [hv]; abel

/-! ### The nine push-right rules, with the resulting mode named `s` -/

/-- Two e-current modes commute at every pair of indices: both the Lie bracket
and the invariant self-pairing of e vanish. This moves an e-mode toward the vacuum. -/
theorem EEs (k : ℂ) (m n : ℤ) (v : WakModule k) :
    J k colE m (J k colE n v) = J k colE n (J k colE m v) := by
  by_cases h : m + n = 0
  · rw [Jc_eq k colE colE h v]; simp [fabc, kappa]
  · rw [Jc_ne k colE colE h v]; simp [fabc]

/-- Two f-current modes commute for the same reason: the f-f bracket and
central pairing are zero, even when the indices sum to zero. -/
theorem FFs (k : ℂ) (m n : ℤ) (v : WakModule k) :
    J k colF m (J k colF n v) = J k colF n (J k colF m v) := by
  by_cases h : m + n = 0
  · rw [Jc_eq k colF colF h v]; simp [fabc, kappa]
  · rw [Jc_ne k colF colF h v]; simp [fabc]

/-- Moving an h-mode past an e-mode adds twice the e-mode at the summed
index, reflecting the Cartan weight +2 of e. There is no central correction. -/
theorem HEs (k : ℂ) (m n s : ℤ) (hs : m + n = s) (v : WakModule k) :
    J k colH m (J k colE n v) = J k colE n (J k colH m v) + (2 : ℂ) • J k colE s v := by
  subst hs
  by_cases h : m + n = 0
  · rw [Jc_eq k colH colE h v]; simp [fabc, kappa]
  · rw [Jc_ne k colH colE h v]; simp [fabc]

/-- Moving an e-mode past an h-mode subtracts twice the e-mode at the
summed index. Reversing the order reverses the Lie-bracket sign. -/
theorem EHs (k : ℂ) (m n s : ℤ) (hs : m + n = s) (v : WakModule k) :
    J k colE m (J k colH n v) = J k colH n (J k colE m v) - (2 : ℂ) • J k colE s v := by
  subst hs
  by_cases h : m + n = 0
  · rw [Jc_eq k colE colH h v]; simp [fabc, kappa]; module
  · rw [Jc_ne k colE colH h v]; simp [fabc]; module

/-- Moving an h-mode past an f-mode subtracts twice the f-mode at the
summed index, reflecting the Cartan weight -2 of f. -/
theorem HFs (k : ℂ) (m n s : ℤ) (hs : m + n = s) (v : WakModule k) :
    J k colH m (J k colF n v) = J k colF n (J k colH m v) - (2 : ℂ) • J k colF s v := by
  subst hs
  by_cases h : m + n = 0
  · rw [Jc_eq k colH colF h v]; simp [fabc, kappa]; module
  · rw [Jc_ne k colH colF h v]; simp [fabc]; module

/-- Moving an f-mode past an h-mode adds twice the f-mode at the summed
index. This is the opposite-order form of the Cartan action on f. -/
theorem FHs (k : ℂ) (m n s : ℤ) (hs : m + n = s) (v : WakModule k) :
    J k colF m (J k colH n v) = J k colH n (J k colF m v) + (2 : ℂ) • J k colF s v := by
  subst hs
  by_cases h : m + n = 0
  · rw [Jc_eq k colF colH h v]; simp [fabc, kappa]
  · rw [Jc_ne k colF colH h v]; simp [fabc]

/-- When the two indices do not sum to zero, moving e past f contributes
only the h-mode at their sum. The central term is absent at these indices. -/
theorem EFs (k : ℂ) (m n s : ℤ) (hs : m + n = s) (hne : s ≠ 0) (v : WakModule k) :
    J k colE m (J k colF n v) = J k colF n (J k colE m v) + J k colH s v := by
  subst hs
  rw [Jc_ne k colE colF hne v]; simp [fabc]

/-- At opposite indices, moving e past f contributes h-zero and the
scalar m times k. The central coefficient uses the LEFT mode index m. -/
theorem EFz (k : ℂ) (m n : ℤ) (hs : m + n = 0) (v : WakModule k) :
    J k colE m (J k colF n v)
      = J k colF n (J k colE m v) + J k colH 0 v + ((m : ℂ) * k) • v := by
  rw [Jc_eq k colE colF hs v, hs]; simp [fabc, kappa]

/-- Away from opposite indices, moving f past e contributes minus the
h-mode at their sum, since the finite-dimensional bracket is [f,e] = -h. -/
theorem FEs (k : ℂ) (m n s : ℤ) (hs : m + n = s) (hne : s ≠ 0) (v : WakModule k) :
    J k colF m (J k colE n v) = J k colE n (J k colF m v) - J k colH s v := by
  subst hs
  rw [Jc_ne k colF colE hne v]; simp [fabc]; module

/-- At opposite indices, moving f past e contributes minus h-zero but
PLUS m times k. The symmetric invariant pairing keeps the central sign positive
relative to the left index, even though the finite Lie bracket changes sign. -/
theorem FEz (k : ℂ) (m n : ℤ) (hs : m + n = 0) (v : WakModule k) :
    J k colF m (J k colE n v)
      = J k colE n (J k colF m v) - J k colH 0 v + ((m : ℂ) * k) • v := by
  rw [Jc_eq k colF colE hs v, hs]; simp [fabc, kappa]; module

/-- Two Cartan modes commute unless their indices sum to zero: the
finite Cartan bracket is zero, leaving only the possible central term. -/
theorem HHs (k : ℂ) (m n : ℤ) (hne : m + n ≠ 0) (v : WakModule k) :
    J k colH m (J k colH n v) = J k colH n (J k colH m v) := by
  rw [Jc_ne k colH colH hne v]; simp [fabc]

/-- Cartan modes at opposite indices have central commutator 2 m k.
The factor two is the normalization of the invariant pairing of h with itself. -/
theorem HHz (k : ℂ) (m n : ℤ) (hs : m + n = 0) (v : WakModule k) :
    J k colH m (J k colH n v) = J k colH n (J k colH m v) + (2 * (m : ℂ) * k) • v := by
  rw [Jc_eq k colH colH hs v]; simp [fabc, kappa]; module

/-! ## §2  Vacuum annihilation -/

theorem J_vac (k : ℂ) (a : Fin 3) {n : ℤ} (hn : 0 ≤ n) : J k a n (vacuumA k) = 0 :=
  vacuum_pos_annihilate kappaForm kappaForm_isInvariant k (basis a) n hn

theorem E_vac0 (k : ℂ) : J k colE 0 (vacuumA k) = 0 := J_vac k colE (by norm_num)
theorem E_vac1 (k : ℂ) : J k colE 1 (vacuumA k) = 0 := J_vac k colE (by norm_num)
theorem F_vac0 (k : ℂ) : J k colF 0 (vacuumA k) = 0 := J_vac k colF (by norm_num)
theorem F_vac1 (k : ℂ) : J k colF 1 (vacuumA k) = 0 := J_vac k colF (by norm_num)
theorem H_vac0 (k : ℂ) : J k colH 0 (vacuumA k) = 0 := J_vac k colH (by norm_num)
theorem H_vac1 (k : ℂ) : J k colH 1 (vacuumA k) = 0 := J_vac k colH (by norm_num)

/-! ## §3  One-generator helper computations -/

theorem E0H1 (k : ℂ) :
    J k colE 0 (J k colH (-1) (vacuumA k)) = (-2 : ℂ) • J k colE (-1) (vacuumA k) := by
  rw [EHs k 0 (-1) (-1) (by norm_num), E_vac0, map_zero, zero_sub]; module

theorem E0F1 (k : ℂ) :
    J k colE 0 (J k colF (-1) (vacuumA k)) = J k colH (-1) (vacuumA k) := by
  rw [EFs k 0 (-1) (-1) (by norm_num) (by norm_num), E_vac0, map_zero, zero_add]

theorem E0E1 (k : ℂ) : J k colE 0 (J k colE (-1) (vacuumA k)) = 0 := by
  rw [EEs k 0 (-1), E_vac0, map_zero]

theorem E1E1 (k : ℂ) : J k colE 1 (J k colE (-1) (vacuumA k)) = 0 := by
  rw [EEs k 1 (-1), E_vac1, map_zero]

theorem E1H1 (k : ℂ) : J k colE 1 (J k colH (-1) (vacuumA k)) = 0 := by
  rw [EHs k 1 (-1) 0 (by norm_num), E_vac1, map_zero, E_vac0, smul_zero, sub_zero]

theorem E1F1 (k : ℂ) : J k colE 1 (J k colF (-1) (vacuumA k)) = k • vacuumA k := by
  rw [EFz k 1 (-1) (by norm_num), E_vac1, map_zero, zero_add, H_vac0, zero_add]
  push_cast; module

theorem F0H1 (k : ℂ) :
    J k colF 0 (J k colH (-1) (vacuumA k)) = (2 : ℂ) • J k colF (-1) (vacuumA k) := by
  rw [FHs k 0 (-1) (-1) (by norm_num), F_vac0, map_zero, zero_add]

theorem F1H1 (k : ℂ) : J k colF 1 (J k colH (-1) (vacuumA k)) = 0 := by
  rw [FHs k 1 (-1) 0 (by norm_num), F_vac1, map_zero, F_vac0, smul_zero, add_zero]

theorem F1F1 (k : ℂ) : J k colF 1 (J k colF (-1) (vacuumA k)) = 0 := by
  rw [FFs k 1 (-1), F_vac1, map_zero]

theorem F1E1 (k : ℂ) : J k colF 1 (J k colE (-1) (vacuumA k)) = k • vacuumA k := by
  rw [FEz k 1 (-1) (by norm_num), F_vac1, map_zero, zero_sub, H_vac0, neg_zero, zero_add]
  push_cast; module

theorem H0H1 (k : ℂ) : J k colH 0 (J k colH (-1) (vacuumA k)) = 0 := by
  rw [HHs k 0 (-1) (by norm_num), H_vac0, map_zero]

theorem H0E1 (k : ℂ) :
    J k colH 0 (J k colE (-1) (vacuumA k)) = (2 : ℂ) • J k colE (-1) (vacuumA k) := by
  rw [HEs k 0 (-1) (-1) (by norm_num), H_vac0, map_zero, zero_add]

theorem H0F1 (k : ℂ) :
    J k colH 0 (J k colF (-1) (vacuumA k)) = (-2 : ℂ) • J k colF (-1) (vacuumA k) := by
  rw [HFs k 0 (-1) (-1) (by norm_num), H_vac0, map_zero, zero_sub]; module

theorem H1H1 (k : ℂ) : J k colH 1 (J k colH (-1) (vacuumA k)) = (2 * k) • vacuumA k := by
  rw [HHz k 1 (-1) (by norm_num), H_vac1, map_zero, zero_add]; push_cast; module

theorem H1E1 (k : ℂ) : J k colH 1 (J k colE (-1) (vacuumA k)) = 0 := by
  rw [HEs k 1 (-1) 0 (by norm_num), H_vac1, map_zero, E_vac0, smul_zero, add_zero]

theorem H1F1 (k : ℂ) : J k colH 1 (J k colF (-1) (vacuumA k)) = 0 := by
  rw [HFs k 1 (-1) 0 (by norm_num), H_vac1, map_zero, F_vac0, smul_zero, sub_zero]

/-- Reordering: `h₋₁ e₋₁ |0⟩ = e₋₁ h₋₁ |0⟩ + 2 e₋₂ |0⟩`. -/
theorem Hm1Em1 (k : ℂ) :
    J k colH (-1) (J k colE (-1) (vacuumA k))
      = J k colE (-1) (J k colH (-1) (vacuumA k)) + (2 : ℂ) • J k colE (-2) (vacuumA k) :=
  HEs k (-1) (-1) (-2) (by norm_num) _

/-- Reordering: `f₋₁ e₋₁ |0⟩ = e₋₁ f₋₁ |0⟩ - h₋₂ |0⟩`. -/
theorem Fm1Em1 (k : ℂ) :
    J k colF (-1) (J k colE (-1) (vacuumA k))
      = J k colE (-1) (J k colF (-1) (vacuumA k)) - J k colH (-2) (vacuumA k) :=
  FEs k (-1) (-1) (-2) (by norm_num) (by norm_num) _

/-- Reordering: `e₋₁ e₋₂ |0⟩ = e₋₂ e₋₁ |0⟩`. -/
theorem Em1Em2 (k : ℂ) :
    J k colE (-1) (J k colE (-2) (vacuumA k)) = J k colE (-2) (J k colE (-1) (vacuumA k)) :=
  EEs k (-1) (-2) _

/-- `e₀` on `h₋₁ h₋₁ |0⟩`. -/
theorem E0_HH1 (k : ℂ) :
    J k colE 0 (J k colH (-1) (J k colH (-1) (vacuumA k)))
      = (-4 : ℂ) • J k colE (-1) (J k colH (-1) (vacuumA k))
        + (-4 : ℂ) • J k colE (-2) (vacuumA k) := by
  rw [EHs k 0 (-1) (-1) (by norm_num), E0H1, map_smul, Hm1Em1]
  module

/-! ## §4  The weight-3 charge-2 monomials and the target monomials -/

/-- `e₋₃|0⟩`. -/
noncomputable def M1 (k : ℂ) : WakModule k := J k colE (-3) (vacuumA k)
/-- `e₋₂h₋₁|0⟩`. -/
noncomputable def M2 (k : ℂ) : WakModule k := J k colE (-2) (J k colH (-1) (vacuumA k))
/-- `h₋₂e₋₁|0⟩`. -/
noncomputable def M3 (k : ℂ) : WakModule k := J k colH (-2) (J k colE (-1) (vacuumA k))
/-- `e₋₁e₋₁f₋₁|0⟩`. -/
noncomputable def M4 (k : ℂ) : WakModule k :=
  J k colE (-1) (J k colE (-1) (J k colF (-1) (vacuumA k)))
/-- `e₋₁h₋₁h₋₁|0⟩`. -/
noncomputable def M5 (k : ℂ) : WakModule k :=
  J k colE (-1) (J k colH (-1) (J k colH (-1) (vacuumA k)))

theorem M1_def (k : ℂ) : M1 k = J k colE (-3) (vacuumA k) := rfl
theorem M2_def (k : ℂ) : M2 k = J k colE (-2) (J k colH (-1) (vacuumA k)) := rfl
theorem M3_def (k : ℂ) : M3 k = J k colH (-2) (J k colE (-1) (vacuumA k)) := rfl
theorem M4_def (k : ℂ) :
    M4 k = J k colE (-1) (J k colE (-1) (J k colF (-1) (vacuumA k))) := rfl
theorem M5_def (k : ℂ) :
    M5 k = J k colE (-1) (J k colH (-1) (J k colH (-1) (vacuumA k))) := rfl

/-- `e₋₂e₋₁|0⟩` (weight 3, charge 4). -/
noncomputable def P1 (k : ℂ) : WakModule k := J k colE (-2) (J k colE (-1) (vacuumA k))
/-- `e₋₁e₋₁h₋₁|0⟩` (weight 3, charge 4). -/
noncomputable def P2 (k : ℂ) : WakModule k :=
  J k colE (-1) (J k colE (-1) (J k colH (-1) (vacuumA k)))
/-- `h₋₂|0⟩` (weight 2, charge 0). -/
noncomputable def Q1 (k : ℂ) : WakModule k := J k colH (-2) (vacuumA k)
/-- `e₋₁f₋₁|0⟩` (weight 2, charge 0). -/
noncomputable def Q2 (k : ℂ) : WakModule k := J k colE (-1) (J k colF (-1) (vacuumA k))
/-- `h₋₁h₋₁|0⟩` (weight 2, charge 0). -/
noncomputable def Q3 (k : ℂ) : WakModule k := J k colH (-1) (J k colH (-1) (vacuumA k))
/-- `e₋₁e₋₁|0⟩` (weight 2, charge 4). -/
noncomputable def R1 (k : ℂ) : WakModule k := J k colE (-1) (J k colE (-1) (vacuumA k))
/-- `e₋₂|0⟩` (weight 2, charge 2). -/
noncomputable def S1 (k : ℂ) : WakModule k := J k colE (-2) (vacuumA k)
/-- `e₋₁h₋₁|0⟩` (weight 2, charge 2). -/
noncomputable def S2 (k : ℂ) : WakModule k := J k colE (-1) (J k colH (-1) (vacuumA k))

theorem P1_def (k : ℂ) : P1 k = J k colE (-2) (J k colE (-1) (vacuumA k)) := rfl
theorem P2_def (k : ℂ) :
    P2 k = J k colE (-1) (J k colE (-1) (J k colH (-1) (vacuumA k))) := rfl
theorem Q1_def (k : ℂ) : Q1 k = J k colH (-2) (vacuumA k) := rfl
theorem Q2_def (k : ℂ) : Q2 k = J k colE (-1) (J k colF (-1) (vacuumA k)) := rfl
theorem Q3_def (k : ℂ) : Q3 k = J k colH (-1) (J k colH (-1) (vacuumA k)) := rfl
theorem R1_def (k : ℂ) : R1 k = J k colE (-1) (J k colE (-1) (vacuumA k)) := rfl
theorem S1_def (k : ℂ) : S1 k = J k colE (-2) (vacuumA k) := rfl
theorem S2_def (k : ℂ) : S2 k = J k colE (-1) (J k colH (-1) (vacuumA k)) := rfl

/-! ## §5  The action of the raising operators on the five monomials -/

/-! ### `e₀` -/

theorem E0_M1 (k : ℂ) : J k colE 0 (M1 k) = 0 := by
  rw [M1_def, EEs k 0 (-3), E_vac0, map_zero]

theorem E0_M2 (k : ℂ) : J k colE 0 (M2 k) = (-2 : ℂ) • P1 k := by
  rw [M2_def, EEs k 0 (-2), E0H1, map_smul, P1_def]

theorem E0_M3 (k : ℂ) : J k colE 0 (M3 k) = (-2 : ℂ) • P1 k := by
  rw [M3_def, EHs k 0 (-2) (-2) (by norm_num), E0E1, map_zero, zero_sub, P1_def]
  module

theorem E0_M4 (k : ℂ) : J k colE 0 (M4 k) = P2 k := by
  rw [M4_def, EEs k 0 (-1), EEs k 0 (-1), E0F1, P2_def]

theorem E0_M5 (k : ℂ) : J k colE 0 (M5 k) = (-4 : ℂ) • P1 k + (-4 : ℂ) • P2 k := by
  rw [M5_def, EEs k 0 (-1), E0_HH1, map_add, map_smul, map_smul, Em1Em2, P1_def, P2_def]
  module

/-! ### `f₁` -/

theorem F1_M1 (k : ℂ) : J k colF 1 (M1 k) = (-1 : ℂ) • Q1 k := by
  rw [M1_def, FEs k 1 (-3) (-2) (by norm_num) (by norm_num), F_vac1, map_zero, zero_sub, Q1_def]
  module

theorem F1_M2 (k : ℂ) : J k colF 1 (M2 k) = (-1 : ℂ) • Q3 k := by
  rw [M2_def, FEs k 1 (-2) (-1) (by norm_num) (by norm_num), F1H1, map_zero, zero_sub, Q3_def]
  module

theorem F1_M3 (k : ℂ) : J k colF 1 (M3 k) = (k - 2) • Q1 k + (2 : ℂ) • Q2 k := by
  rw [M3_def, FHs k 1 (-2) (-1) (by norm_num), F1E1, map_smul, Fm1Em1, Q1_def, Q2_def]
  module

theorem F1_M4 (k : ℂ) : J k colF 1 (M4 k) = (2 * k + 2) • Q2 k := by
  have hF1A : J k colF 1 (J k colE (-1) (J k colF (-1) (vacuumA k)))
      = (k + 2) • J k colF (-1) (vacuumA k) := by
    rw [FEz k 1 (-1) (by norm_num), F1F1, map_zero, zero_sub, H0F1]
    push_cast; module
  have hH0A : J k colH 0 (J k colE (-1) (J k colF (-1) (vacuumA k))) = 0 := by
    rw [HEs k 0 (-1) (-1) (by norm_num), H0F1, map_smul]
    module
  rw [M4_def, FEz k 1 (-1) (by norm_num), hF1A, hH0A, map_smul, Q2_def]
  push_cast; module

theorem F1_M5 (k : ℂ) : J k colF 1 (M5 k) = (4 : ℂ) • Q2 k + k • Q3 k := by
  have hF1C : J k colF 1 (J k colH (-1) (J k colH (-1) (vacuumA k)))
      = (4 : ℂ) • J k colF (-1) (vacuumA k) := by
    rw [FHs k 1 (-1) 0 (by norm_num), F1H1, map_zero, zero_add, F0H1]
    module
  have hH0C : J k colH 0 (J k colH (-1) (J k colH (-1) (vacuumA k))) = 0 := by
    rw [HHs k 0 (-1) (by norm_num), H0H1, map_zero]
  rw [M5_def, FEz k 1 (-1) (by norm_num), hF1C, hH0C, map_smul, Q2_def, Q3_def]
  push_cast; module

/-! ### `e₁` -/

theorem E1_M1 (k : ℂ) : J k colE 1 (M1 k) = 0 := by
  rw [M1_def, EEs k 1 (-3), E_vac1, map_zero]

theorem E1_M2 (k : ℂ) : J k colE 1 (M2 k) = 0 := by
  rw [M2_def, EEs k 1 (-2), E1H1, map_zero]

theorem E1_M3 (k : ℂ) : J k colE 1 (M3 k) = (-2 : ℂ) • R1 k := by
  rw [M3_def, EHs k 1 (-2) (-1) (by norm_num), E1E1, map_zero, zero_sub, R1_def]
  module

theorem E1_M4 (k : ℂ) : J k colE 1 (M4 k) = k • R1 k := by
  rw [M4_def, EEs k 1 (-1), EEs k 1 (-1), E1F1, map_smul, map_smul, R1_def]

theorem E1_M5 (k : ℂ) : J k colE 1 (M5 k) = (4 : ℂ) • R1 k := by
  have hE1C : J k colE 1 (J k colH (-1) (J k colH (-1) (vacuumA k)))
      = (4 : ℂ) • J k colE (-1) (vacuumA k) := by
    rw [EHs k 1 (-1) 0 (by norm_num), E1H1, map_zero, zero_sub, E0H1]
    module
  rw [M5_def, EEs k 1 (-1), hE1C, map_smul, R1_def]

/-! ### `h₁` -/

theorem H1_M1 (k : ℂ) : J k colH 1 (M1 k) = (2 : ℂ) • S1 k := by
  rw [M1_def, HEs k 1 (-3) (-2) (by norm_num), H_vac1, map_zero, zero_add, S1_def]

theorem H1_M2 (k : ℂ) : J k colH 1 (M2 k) = (2 * k) • S1 k + (2 : ℂ) • S2 k := by
  rw [M2_def, HEs k 1 (-2) (-1) (by norm_num), H1H1, map_smul, S1_def, S2_def]

theorem H1_M3 (k : ℂ) : J k colH 1 (M3 k) = 0 := by
  rw [M3_def, HHs k 1 (-2) (by norm_num), H1E1, map_zero]

theorem H1_M4 (k : ℂ) : J k colH 1 (M4 k) = (4 : ℂ) • S2 k := by
  have hE0A : J k colE 0 (J k colE (-1) (J k colF (-1) (vacuumA k)))
      = J k colE (-1) (J k colH (-1) (vacuumA k)) := by
    rw [EEs k 0 (-1), E0F1]
  have hH1A : J k colH 1 (J k colE (-1) (J k colF (-1) (vacuumA k)))
      = (2 : ℂ) • J k colH (-1) (vacuumA k) := by
    rw [HEs k 1 (-1) 0 (by norm_num), H1F1, map_zero, zero_add, E0F1]
  rw [M4_def, HEs k 1 (-1) 0 (by norm_num), hH1A, map_smul, hE0A, S2_def]
  module

theorem H1_M5 (k : ℂ) : J k colH 1 (M5 k) = (-8 : ℂ) • S1 k + (4 * k - 8) • S2 k := by
  have hH1C : J k colH 1 (J k colH (-1) (J k colH (-1) (vacuumA k)))
      = (4 * k) • J k colH (-1) (vacuumA k) := by
    rw [HHz k 1 (-1) (by norm_num), H1H1, map_smul]
    push_cast; module
  rw [M5_def, HEs k 1 (-1) 0 (by norm_num), hH1C, map_smul, E0_HH1, S1_def, S2_def]
  module

/-! ### `h₀` (the Cartan charge) -/

theorem H0_M1 (k : ℂ) : J k colH 0 (M1 k) = (2 : ℂ) • M1 k := by
  rw [M1_def, HEs k 0 (-3) (-3) (by norm_num), H_vac0, map_zero, zero_add]

theorem H0_M2 (k : ℂ) : J k colH 0 (M2 k) = (2 : ℂ) • M2 k := by
  rw [M2_def, HEs k 0 (-2) (-2) (by norm_num), H0H1, map_zero, zero_add]

theorem H0_M3 (k : ℂ) : J k colH 0 (M3 k) = (2 : ℂ) • M3 k := by
  rw [M3_def, HHs k 0 (-2) (by norm_num), H0E1, map_smul]

theorem H0_M4 (k : ℂ) : J k colH 0 (M4 k) = (2 : ℂ) • M4 k := by
  have hH0A : J k colH 0 (J k colE (-1) (J k colF (-1) (vacuumA k))) = 0 := by
    rw [HEs k 0 (-1) (-1) (by norm_num), H0F1, map_smul]
    module
  rw [M4_def, HEs k 0 (-1) (-1) (by norm_num), hH0A, map_zero, zero_add]

theorem H0_M5 (k : ℂ) : J k colH 0 (M5 k) = (2 : ℂ) • M5 k := by
  have hH0C : J k colH 0 (J k colH (-1) (J k colH (-1) (vacuumA k))) = 0 := by
    rw [HHs k 0 (-1) (by norm_num), H0H1, map_zero]
  rw [M5_def, HEs k 0 (-1) (-1) (by norm_num), hH0C, map_zero, zero_add]

/-! ## §6  The general ansatz and the resulting linear system -/

/-- The general element of the span of the five weight-3, charge-2 monomials. -/
noncomputable def ansatz (k a b c d g : ℂ) : WakModule k :=
  a • M1 k + b • M2 k + c • M3 k + d • M4 k + g • M5 k

theorem ansatz_def (k a b c d g : ℂ) :
    ansatz k a b c d g = a • M1 k + b • M2 k + c • M3 k + d • M4 k + g • M5 k := rfl

theorem E0_ansatz (k a b c d g : ℂ) :
    J k colE 0 (ansatz k a b c d g)
      = (-2 * (b + c + 2 * g)) • P1 k + (d - 4 * g) • P2 k := by
  rw [ansatz_def]
  simp only [map_add, map_smul, E0_M1, E0_M2, E0_M3, E0_M4, E0_M5, smul_zero]
  module

theorem F1_ansatz (k a b c d g : ℂ) :
    J k colF 1 (ansatz k a b c d g)
      = (-a + (k - 2) * c) • Q1 k + (2 * (c + (k + 1) * d + 2 * g)) • Q2 k
        + (k * g - b) • Q3 k := by
  rw [ansatz_def]
  simp only [map_add, map_smul, F1_M1, F1_M2, F1_M3, F1_M4, F1_M5]
  module

theorem E1_ansatz (k a b c d g : ℂ) :
    J k colE 1 (ansatz k a b c d g) = (-2 * c + k * d + 4 * g) • R1 k := by
  rw [ansatz_def]
  simp only [map_add, map_smul, E1_M1, E1_M2, E1_M3, E1_M4, E1_M5, smul_zero]
  module

theorem H1_ansatz (k a b c d g : ℂ) :
    J k colH 1 (ansatz k a b c d g)
      = (2 * a + 2 * k * b - 8 * g) • S1 k + (2 * b + 4 * d + (4 * k - 8) * g) • S2 k := by
  rw [ansatz_def]
  simp only [map_add, map_smul, H1_M1, H1_M2, H1_M3, H1_M4, H1_M5, smul_zero]
  module

theorem H0_ansatz (k a b c d g : ℂ) :
    J k colH 0 (ansatz k a b c d g) = (2 : ℂ) • ansatz k a b c d g := by
  rw [ansatz_def]
  simp only [map_add, map_smul, H0_M1, H0_M2, H0_M3, H0_M4, H0_M5]
  module

/-- **The singularity system.**  Five linear equations in `(a,b,c,d,g)` over `ℚ(k)`: the two
coefficients of `e₀ s` in `{e₋₂e₋₁|0⟩, e₋₁e₋₁h₋₁|0⟩}` and the three coefficients of `f₁ s`
in `{h₋₂|0⟩, e₋₁f₋₁|0⟩, h₋₁h₋₁|0⟩}`. -/
def SingSys (k a b c d g : ℂ) : Prop :=
  b + c + 2 * g = 0 ∧ d - 4 * g = 0 ∧ -a + (k - 2) * c = 0
    ∧ c + (k + 1) * d + 2 * g = 0 ∧ k * g - b = 0

theorem E0_ansatz_eq_zero {k a b c d g : ℂ} (h : SingSys k a b c d g) :
    J k colE 0 (ansatz k a b c d g) = 0 := by
  obtain ⟨h1, h2, -, -, -⟩ := h
  have e1 : (-2 * (b + c + 2 * g) : ℂ) = 0 := by linear_combination (-2 : ℂ) * h1
  rw [E0_ansatz, e1, h2, zero_smul, zero_smul, add_zero]

theorem F1_ansatz_eq_zero {k a b c d g : ℂ} (h : SingSys k a b c d g) :
    J k colF 1 (ansatz k a b c d g) = 0 := by
  obtain ⟨-, -, h3, h4, h5⟩ := h
  have e2 : (2 * (c + (k + 1) * d + 2 * g) : ℂ) = 0 := by linear_combination (2 : ℂ) * h4
  rw [F1_ansatz, h3, e2, h5, zero_smul, zero_smul, zero_smul, add_zero, add_zero]

/-- **Solving the system.**  Every solution is determined by `g`, and `g` must satisfy
`(3k+4)·g = 0`.  This is where the level is forced. -/
theorem SingSys_param {k a b c d g : ℂ} (h : SingSys k a b c d g) :
    b = k * g ∧ c = -(k + 2) * g ∧ d = 4 * g ∧ a = -((k - 2) * (k + 2)) * g
      ∧ (3 * k + 4) * g = 0 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨by linear_combination -h5, by linear_combination h1 + h5,
    by linear_combination h2, ?_, ?_⟩
  · linear_combination (-1 : ℂ) * h3 + (k - 2) * h1 + (k - 2) * h5
  · linear_combination h4 - h1 - h5 - (k + 1) * h2

/-- If a solution has `g ≠ 0` then the level is `-4/3`. -/
theorem SingSys_level {k a b c d g : ℂ} (h : SingSys k a b c d g) (hg : g ≠ 0) :
    3 * k + 4 = 0 := by
  obtain ⟨-, -, -, -, h5⟩ := SingSys_param h
  exact (mul_eq_zero.mp h5).resolve_right hg

/-- Away from `k = -4/3` the only solution is the zero one. -/
theorem SingSys_trivial_of_level {k a b c d g : ℂ} (h : SingSys k a b c d g)
    (hk : 3 * k + 4 ≠ 0) : a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ g = 0 := by
  obtain ⟨hb, hc, hd, ha, h5⟩ := SingSys_param h
  have hg : g = 0 := (mul_eq_zero.mp h5).resolve_left hk
  subst hg
  exact ⟨by rw [ha]; ring, by rw [hb]; ring, by rw [hc]; ring, by rw [hd]; ring, rfl⟩

/-- At `k = -4/3` the integral vector `(20, -12, -6, 36, 9)` solves the system. -/
theorem SingSys_of_level {k : ℂ} (hk : 3 * k + 4 = 0) : SingSys k 20 (-12) (-6) 36 9 := by
  have hk' : k = -4 / 3 := by linear_combination hk / 3
  subst hk'
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **The level is a theorem, not an assumption.**  A nonzero singular vector in the
weight-3 charge-2 space exists exactly when `3k + 4 = 0`, i.e. `k = -4/3`. -/
theorem exists_nonzero_solution_iff (k : ℂ) :
    (∃ a b c d g : ℂ, ¬(a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ g = 0) ∧ SingSys k a b c d g)
      ↔ 3 * k + 4 = 0 := by
  constructor
  · rintro ⟨a, b, c, d, g, hne, h⟩
    by_contra hk
    exact hne (SingSys_trivial_of_level h hk)
  · intro hk
    refine ⟨20, -12, -6, 36, 9, ?_, SingSys_of_level hk⟩
    rintro ⟨h, -, -, -, -⟩
    norm_num at h

/-- **Necessity of the system** (given independence of the target monomials): a vector of the
ansatz shape is killed by `e₀` and `f₁` only if the five equations hold.  The hypotheses are
exactly the PBW independence of the weight-3 charge-4 pair `{e₋₂e₋₁|0⟩, e₋₁e₋₁h₋₁|0⟩}` and of
the weight-2 charge-0 triple `{h₋₂|0⟩, e₋₁f₋₁|0⟩, h₋₁h₋₁|0⟩}`. -/
theorem SingSys_of_annihilated {k a b c d g : ℂ}
    (hP : LinearIndependent ℂ ![P1 k, P2 k])
    (hQ : LinearIndependent ℂ ![Q1 k, Q2 k, Q3 k])
    (hE : J k colE 0 (ansatz k a b c d g) = 0)
    (hF : J k colF 1 (ansatz k a b c d g) = 0) : SingSys k a b c d g := by
  rw [E0_ansatz] at hE
  rw [F1_ansatz] at hF
  have hsumP : ∑ i, (![-2 * (b + c + 2 * g), d - 4 * g] : Fin 2 → ℂ) i •
      (![P1 k, P2 k]) i = 0 := by
    rw [Fin.sum_univ_two]; simpa using hE
  have hsumQ : ∑ i, (![-a + (k - 2) * c, 2 * (c + (k + 1) * d + 2 * g), k * g - b] : Fin 3 → ℂ) i •
      (![Q1 k, Q2 k, Q3 k]) i = 0 := by
    rw [Fin.sum_univ_three]; simpa using hF
  have hP0 := Fintype.linearIndependent_iff.mp hP _ hsumP
  have hQ0 := Fintype.linearIndependent_iff.mp hQ _ hsumQ
  have e1 := hP0 0
  have e2 := hP0 1
  have e3 := hQ0 0
  have e4 := hQ0 1
  have e5 := hQ0 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at e1 e2 e3 e4 e5
  exact ⟨by linear_combination -e1 / 2, e2, e3, by linear_combination e4 / 2, e5⟩

/-- **No singular vector away from `k = -4/3`.**  Modulo the same independence hypotheses, at any
level with `3k + 4 ≠ 0` the only weight-3 charge-2 vector killed by `e₀` and `f₁` is `0`. -/
theorem ansatz_eq_zero_of_level_ne {k a b c d g : ℂ}
    (hP : LinearIndependent ℂ ![P1 k, P2 k])
    (hQ : LinearIndependent ℂ ![Q1 k, Q2 k, Q3 k]) (hk : 3 * k + 4 ≠ 0)
    (hE : J k colE 0 (ansatz k a b c d g) = 0)
    (hF : J k colF 1 (ansatz k a b c d g) = 0) : ansatz k a b c d g = 0 := by
  obtain ⟨ha, hb, hc, hd, hg⟩ :=
    SingSys_trivial_of_level (SingSys_of_annihilated hP hQ hE hF) hk
  simp [ansatz_def, ha, hb, hc, hd, hg]

/-! ## §7  The singular vector at `k = -4/3` -/

/-- **The weight-3 singular vector of `V^{-4/3}(𝔰𝔩₂)`**, with integral coefficients:
`s = 20 e₋₃|0⟩ - 12 e₋₂h₋₁|0⟩ - 6 h₋₂e₋₁|0⟩ + 36 e₋₁e₋₁f₋₁|0⟩ + 9 e₋₁h₋₁h₋₁|0⟩`. -/
noncomputable def sl2Singular : WakModule (-4 / 3 : ℂ) := ansatz (-4 / 3) 20 (-12) (-6) 36 9

theorem sl2Singular_def :
    sl2Singular = ansatz (-4 / 3 : ℂ) 20 (-12) (-6) 36 9 := rfl

theorem SingSys_sing : SingSys (-4 / 3 : ℂ) 20 (-12) (-6) 36 9 :=
  SingSys_of_level (by norm_num)

theorem sl2Singular_E0 : J (-4 / 3 : ℂ) colE 0 sl2Singular = 0 :=
  E0_ansatz_eq_zero SingSys_sing

theorem sl2Singular_F1 : J (-4 / 3 : ℂ) colF 1 sl2Singular = 0 :=
  F1_ansatz_eq_zero SingSys_sing

theorem sl2Singular_E1 : J (-4 / 3 : ℂ) colE 1 sl2Singular = 0 := by
  rw [sl2Singular_def, E1_ansatz, show (-2 * (-6 : ℂ) + (-4 / 3) * 36 + 4 * 9) = 0 by norm_num,
    zero_smul]

theorem sl2Singular_H1 : J (-4 / 3 : ℂ) colH 1 sl2Singular = 0 := by
  rw [sl2Singular_def, H1_ansatz,
    show (2 * (20 : ℂ) + 2 * (-4 / 3) * (-12) - 8 * 9) = 0 by norm_num,
    show (2 * (-12 : ℂ) + 4 * 36 + (4 * (-4 / 3) - 8) * 9) = 0 by norm_num,
    zero_smul, zero_smul, add_zero]

/-- The Cartan charge of the singular vector is `+2`: it is a highest-weight vector for the
horizontal `𝔰𝔩₂`, **not** an `𝔰𝔩₂`-invariant. -/
theorem sl2Singular_H0 : J (-4 / 3 : ℂ) colH 0 sl2Singular = (2 : ℂ) • sl2Singular :=
  H0_ansatz _ _ _ _ _ _

/-! ## §8  Grading and the full positive part -/

theorem M1_mem (k : ℂ) : M1 k ∈ gradingZA k 3 := by
  have h := J_mem_gradingZA k colE (-3) 0 (vacuumA_mem_gradingZA_zero k)
  rwa [show (0 : ℤ) - -3 = 3 by norm_num] at h

theorem M2_mem (k : ℂ) : M2 k ∈ gradingZA k 3 := by
  have h1 := J_mem_gradingZA k colH (-1) 0 (vacuumA_mem_gradingZA_zero k)
  rw [show (0 : ℤ) - -1 = 1 by norm_num] at h1
  have h2 := J_mem_gradingZA k colE (-2) 1 h1
  rwa [show (1 : ℤ) - -2 = 3 by norm_num] at h2

theorem M3_mem (k : ℂ) : M3 k ∈ gradingZA k 3 := by
  have h1 := J_mem_gradingZA k colE (-1) 0 (vacuumA_mem_gradingZA_zero k)
  rw [show (0 : ℤ) - -1 = 1 by norm_num] at h1
  have h2 := J_mem_gradingZA k colH (-2) 1 h1
  rwa [show (1 : ℤ) - -2 = 3 by norm_num] at h2

theorem M4_mem (k : ℂ) : M4 k ∈ gradingZA k 3 := by
  have h1 := J_mem_gradingZA k colF (-1) 0 (vacuumA_mem_gradingZA_zero k)
  rw [show (0 : ℤ) - -1 = 1 by norm_num] at h1
  have h2 := J_mem_gradingZA k colE (-1) 1 h1
  rw [show (1 : ℤ) - -1 = 2 by norm_num] at h2
  have h3 := J_mem_gradingZA k colE (-1) 2 h2
  rwa [show (2 : ℤ) - -1 = 3 by norm_num] at h3

theorem M5_mem (k : ℂ) : M5 k ∈ gradingZA k 3 := by
  have h1 := J_mem_gradingZA k colH (-1) 0 (vacuumA_mem_gradingZA_zero k)
  rw [show (0 : ℤ) - -1 = 1 by norm_num] at h1
  have h2 := J_mem_gradingZA k colH (-1) 1 h1
  rw [show (1 : ℤ) - -1 = 2 by norm_num] at h2
  have h3 := J_mem_gradingZA k colE (-1) 2 h2
  rwa [show (2 : ℤ) - -1 = 3 by norm_num] at h3

theorem ansatz_mem (k a b c d g : ℂ) : ansatz k a b c d g ∈ gradingZA k 3 := by
  rw [ansatz_def]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ (M1_mem k)) (Submodule.smul_mem _ _ (M2_mem k)))
    (Submodule.smul_mem _ _ (M3_mem k))) (Submodule.smul_mem _ _ (M4_mem k)))
    (Submodule.smul_mem _ _ (M5_mem k))

theorem of_two_smul_eq_zero {k : ℂ} {x : WakModule k} (h : (2 : ℂ) • x = 0) : x = 0 := by
  have h2 : ((2 : ℂ)⁻¹ * 2) • x = 0 := by rw [← smul_smul, h, smul_zero]
  rwa [show ((2 : ℂ)⁻¹ * 2) = 1 by norm_num, one_smul] at h2

/-- **The whole positive part annihilates.**  A weight-3 vector killed by the three level-one
modes is killed by every mode of positive level: levels 2 and 3 follow by brackets, and levels
`≥ 4` by the energy grading. -/
theorem pos_ann {k : ℂ} {v : WakModule k} (hv : v ∈ gradingZA k 3)
    (hE1 : J k colE 1 v = 0) (hF1 : J k colF 1 v = 0) (hH1 : J k colH 1 v = 0)
    (a : Fin 3) {m : ℤ} (hm : 1 ≤ m) : J k a m v = 0 := by
  have hE2 : J k colE 2 v = 0 := by
    have h := HEs k 1 1 2 (by norm_num) v
    rw [hE1, hH1, map_zero, map_zero, zero_add] at h
    exact of_two_smul_eq_zero h.symm
  have hF2 : J k colF 2 v = 0 := by
    have h := HFs k 1 1 2 (by norm_num) v
    rw [hF1, hH1, map_zero, map_zero, zero_sub] at h
    exact of_two_smul_eq_zero (neg_eq_zero.mp h.symm)
  have hH2 : J k colH 2 v = 0 := by
    have h := EFs k 1 1 2 (by norm_num) (by norm_num) v
    rw [hF1, hE1, map_zero, map_zero, zero_add] at h
    exact h.symm
  have hE3 : J k colE 3 v = 0 := by
    have h := HEs k 1 2 3 (by norm_num) v
    rw [hE2, hH1, map_zero, map_zero, zero_add] at h
    exact of_two_smul_eq_zero h.symm
  have hF3 : J k colF 3 v = 0 := by
    have h := HFs k 1 2 3 (by norm_num) v
    rw [hF2, hH1, map_zero, map_zero, zero_sub] at h
    exact of_two_smul_eq_zero (neg_eq_zero.mp h.symm)
  have hH3 : J k colH 3 v = 0 := by
    have h := EFs k 1 2 3 (by norm_num) (by norm_num) v
    rw [hF2, hE1, map_zero, map_zero, zero_add] at h
    exact h.symm
  rcases lt_or_ge m 4 with hlt | hge
  · have key : ∀ b : Fin 3, J k b 1 v = 0 ∧ J k b 2 v = 0 ∧ J k b 3 v = 0 := by
      intro b
      fin_cases b
      · exact ⟨hE1, hE2, hE3⟩
      · exact ⟨hF1, hF2, hF3⟩
      · exact ⟨hH1, hH2, hH3⟩
    have hm3 : m = 1 ∨ m = 2 ∨ m = 3 := by omega
    rcases hm3 with rfl | rfl | rfl
    · exact (key a).1
    · exact (key a).2.1
    · exact (key a).2.2
  · exact J_gradingZA_eq_zero k a (by omega) hv

theorem sl2Singular_mem : sl2Singular ∈ gradingZA (-4 / 3 : ℂ) 3 := ansatz_mem _ _ _ _ _ _

/-- **`s` is a singular vector**: every mode of positive level kills it. -/
theorem sl2Singular_pos (a : Fin 3) {m : ℤ} (hm : 1 ≤ m) :
    J (-4 / 3 : ℂ) a m sl2Singular = 0 :=
  pos_ann sl2Singular_mem sl2Singular_E1 sl2Singular_F1 sl2Singular_H1 a hm

/-- **Nonvanishing, conditional on PBW independence** of the five monomials.  The
unconditional version is `Wak.sl2Singular_ne_zero` (`Examples.WakimotoFree`). -/
theorem sl2Singular_ne_zero_of_indep
    (hli : LinearIndependent ℂ
      ![M1 (-4 / 3 : ℂ), M2 (-4 / 3 : ℂ), M3 (-4 / 3 : ℂ), M4 (-4 / 3 : ℂ),
        M5 (-4 / 3 : ℂ)]) : sl2Singular ≠ 0 := by
  intro h0
  have hsum : ∑ i, (![(20 : ℂ), -12, -6, 36, 9]) i •
      (![M1 (-4 / 3 : ℂ), M2 (-4 / 3 : ℂ), M3 (-4 / 3 : ℂ), M4 (-4 / 3 : ℂ),
        M5 (-4 / 3 : ℂ)]) i = 0 := by
    rw [Fin.sum_univ_five]
    simpa [sl2Singular_def, ansatz_def] using h0
  have h20 := Fintype.linearIndependent_iff.mp hli _ hsum 0
  norm_num at h20

end VOA.Sl2Sing
