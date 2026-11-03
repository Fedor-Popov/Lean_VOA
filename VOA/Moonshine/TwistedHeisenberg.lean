/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# The `θ`-twisted Heisenberg algebra and its Fock module `S[θ]`  (Moonshine step M4)

The `θ`-twisted (half-integer moded) Heisenberg algebra of rank `r` (FLM §§1.7, 3.2, 9.1) and its
canonical Fock module `S[θ]`, modelled on the untwisted `VOA.HeisenbergN` development
(`Examples/HeisenbergNFock`).  We work with the standard form `δ_ij` on `ℂ^r`; the Leech form is
diagonalizable over `ℂ`, and the transport is left to the consumer.

## Conventions
* **Mode indexing.**  `modeT r i k` is the mode `h_i(k/2)`, `k : ℤ`.  Only **odd** `k` are
  meaningful; for even `k` the definition returns `0` (junk, documented in `modeT_even`).  This
  matches `TwistedModule.YM u k = u₍k/N₎` with `N = 2` (`Modularity/Twisted.lean`).
* **Fock space.**  `FockT r = MvPolynomial (ℕ × Fin r) ℂ`; the variable `(n, i)` is the creation
  mode `h_i(-n-½) = modeT r i (-(2n+1))`, and the vacuum is `1`.
* **Annihilators** are scaled partial derivatives: `h_i(n+½) = (n+½) ∂/∂X_{(n,i)}`.
* **Grading.**  `gradingT r d` (`d : ℕ`) is the **doubled** weight-`d` piece (variable `(n,i)` has
  doubled weight `2n+1`); its `L₀`-eigenvalue is `levelT r d = d/2 + r/16`.  The `ℚ`-indexed
  eigenspace family is `weightT r q`, equal to `gradingT r d` at `q = levelT r d` and `⊥` off
  `r/16 + ½ℕ`.

## Main declarations
* `modeT_comm` — `[h_i(k/2), h_j(l/2)] = (k/2) δ_ij δ_{k+l,0}` for odd `k, l`.
* `modeT_vacT` — positive modes kill the vacuum; `span_creationWordT_vacT` — creation words on
  the vacuum span `S[θ]`.
* `gradingT_isInternal`, `weightT_isInternal`, `gradingT_finiteDimensional`,
  `weightT_finiteDimensional`, `finrank_gradingT` (dimension = number of exponent vectors).
* `weightT_vacuum` (`L₀ = r/16` piece is `ℂ·vacT`), `finrank_weightT_half` (`L₀ = r/16 + ½`
  piece has dimension `r`), `weightT_eq_bot_of_lt`.
* `thetaT` — the involution `θ` (negate all variables) as an `AlgEquiv`; `thetaT_thetaT`,
  `thetaT_monomial` / `coeff_thetaT` (`θ = (-1)^N`), `thetaT_mem_gradingT`, `thetaT_modeT`
  (`θ h(k/2) = -h(k/2) θ`), `thetaT_eq_self_iff` / `thetaT_eq_neg_iff` (the `±1` eigenspaces).
* `L0T = ½ E + r/16` with `E` the weighted Euler derivation; `L0T_of_mem_weightT` (diagonal with
  eigenvalue `q`), `L0T_eq_modeSum` (`L₀ p = Σ_{v ∈ vars p} h(-n-½) h(n+½) p + (r/16) p`),
  `L0T_comm_modeT` (`[L₀, h_i(k/2)] = -(k/2) h_i(k/2)`).

## Status
Step M4: proved, `#print axioms` =
`[propext, Classical.choice, Quot.sound]`, no `pbw`.  Unconditional (no hypotheses beyond the
data).  Not done in this file: the twisted vertex operators `Y^T(u, z)` (step M6), the transport to the
Leech form, and the tensor factor `T` (step M5).

## References
* FLM, *Vertex Operator Algebras and the Monster*, §§1.7, 3.2, 9.1.
-/

namespace VOA

namespace TwistedHeisenberg

open MvPolynomial

/-! ## The Fock space and the modes -/

/-- The `θ`-twisted rank-`r` Fock space `S[θ] = FockT r = ℂ[h_i(-n-½) : n ∈ ℕ, i : Fin r]`.
The variable `(n, i)` stands for the creation mode `h_i(-n-½) = h_i(-(2n+1)/2)`. -/
abbrev FockT (r : ℕ) : Type := MvPolynomial (ℕ × Fin r) ℂ

/-- The vacuum `1 ∈ S[θ]`. -/
noncomputable def vacT (r : ℕ) : FockT r := 1

/-- The polynomial variable carrying the odd mode index `k`: `((|k| - 1)/2, i)`.  For odd `k < 0`
this is the variable of `h_i(k/2)`; for odd `k > 0` it is the variable annihilated by
`h_i(k/2)`. -/
def varT {r : ℕ} (i : Fin r) (k : ℤ) : ℕ × Fin r := (((|k| - 1) / 2).toNat, i)

/-- Creation operator: multiplication by the variable `(n, i)`, i.e. `h_i(-n-½)`. -/
noncomputable def mulXT {r : ℕ} (v : ℕ × Fin r) : Module.End ℂ (FockT r) :=
  Algebra.lmul ℂ (FockT r) (X v)

/-- Creation operators act by multiplication by their variable. -/
@[simp] theorem mulXT_apply {r : ℕ} (v : ℕ × Fin r) (p : FockT r) : mulXT v p = X v * p := rfl

/-- The partial derivative along the variable `v`, as a linear endomorphism. -/
noncomputable def pderivT {r : ℕ} (v : ℕ × Fin r) : Module.End ℂ (FockT r) :=
  (pderiv v : Derivation ℂ (FockT r) (FockT r)).toLinearMap

/-- The derivative endomorphism is the ordinary partial derivative. -/
@[simp] theorem pderivT_apply {r : ℕ} (v : ℕ × Fin r) (p : FockT r) :
    pderivT v p = pderiv v p := rfl

/-- **The twisted Heisenberg modes** `modeT r i k = h_i(k/2)`, indexed by `k : ℤ`:

* `k` odd, `k < 0`: creation, multiplication by the variable `varT i k = ((-k-1)/2, i)`;
* `k` odd, `k > 0`: annihilation, `(k/2) • ∂/∂X_{((k-1)/2, i)}`;
* `k` even: `0` (junk value; `θ`-twisted fields have no integral modes). -/
noncomputable def modeT (r : ℕ) (i : Fin r) (k : ℤ) : Module.End ℂ (FockT r) :=
  if k % 2 = 0 then 0
  else if k < 0 then mulXT (varT i k)
  else ((k : ℂ) / 2) • pderivT (varT i k)

/-- Integral (even-`k`) modes vanish: the twisted Heisenberg algebra has only half-integral
modes. -/
theorem modeT_even (r : ℕ) (i : Fin r) {k : ℤ} (hk : k % 2 = 0) : modeT r i k = 0 := by
  rw [modeT, if_pos hk]

/-- Negative odd modes are creation operators. -/
theorem modeT_neg (r : ℕ) (i : Fin r) {k : ℤ} (hk : Odd k) (hneg : k < 0) :
    modeT r i k = mulXT (varT i k) := by
  rw [modeT, if_neg (by rw [Int.odd_iff] at hk; omega), if_pos hneg]

/-- Positive odd modes are scaled partial derivatives. -/
theorem modeT_pos (r : ℕ) (i : Fin r) {k : ℤ} (hk : Odd k) (hpos : 0 < k) :
    modeT r i k = ((k : ℂ) / 2) • pderivT (varT i k) := by
  rw [modeT, if_neg (by rw [Int.odd_iff] at hk; omega), if_neg (by omega)]

/-- Application form of `modeT_neg`. -/
theorem modeT_apply_neg (r : ℕ) (i : Fin r) {k : ℤ} (hk : Odd k) (hneg : k < 0) (p : FockT r) :
    modeT r i k p = X (varT i k) * p := by
  rw [modeT_neg r i hk hneg, mulXT_apply]

/-- Application form of `modeT_pos`. -/
theorem modeT_apply_pos (r : ℕ) (i : Fin r) {k : ℤ} (hk : Odd k) (hpos : 0 < k) (p : FockT r) :
    modeT r i k p = ((k : ℂ) / 2) • pderiv (varT i k) p := by
  rw [modeT_pos r i hk hpos]; rfl

/-- The creation mode `h_i(-n-½) = modeT r i (-(2n+1))` multiplies by the variable `(n, i)`. -/
theorem modeT_creation (r : ℕ) (i : Fin r) (n : ℕ) (p : FockT r) :
    modeT r i (-(2 * n + 1)) p = X (n, i) * p := by
  rw [modeT_apply_neg r i ⟨-(n : ℤ) - 1, by ring⟩ (by omega)]
  congr 2
  simp only [varT, Prod.mk.injEq, and_true]
  rw [abs_of_neg (by omega)]
  omega

/-- The annihilation mode `h_i(n+½) = modeT r i (2n+1)` is `(n+½) ∂/∂X_{(n,i)}`. -/
theorem modeT_annihilation (r : ℕ) (i : Fin r) (n : ℕ) (p : FockT r) :
    modeT r i (2 * n + 1) p = (((2 * n + 1 : ℤ) : ℂ) / 2) • pderiv (n, i) p := by
  rw [modeT_apply_pos r i ⟨(n : ℤ), by ring⟩ (by omega)]
  congr 3
  simp only [varT, Prod.mk.injEq, and_true]
  rw [abs_of_pos (by omega)]
  omega

/-! ## The commutation relation -/

/-- The canonical commutator `[∂_u, X_v] = δ_{uv}` on `S[θ]`. -/
theorem pderiv_X_mul_sub {r : ℕ} (u v : ℕ × Fin r) (p : FockT r) :
    pderiv u (X v * p) - X v * pderiv u p = if u = v then p else 0 := by
  rw [pderiv_mul, pderiv_X]
  by_cases h : u = v
  · subst h; simp
  · rw [Pi.single_apply, if_neg (Ne.symm h), if_neg h]; ring

/-- Partial derivatives commute on `S[θ]`. -/
theorem pderiv_pderiv_comm {r : ℕ} (u v : ℕ × Fin r) (p : FockT r) :
    pderiv u (pderiv v p) = pderiv v (pderiv u p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p s h =>
    rw [pderiv_mul, pderiv_mul, map_add, map_add, pderiv_mul, pderiv_mul]
    simp only [pderiv_X, Pi.single_apply, h]
    by_cases hsu : s = u <;> by_cases hsv : s = v <;>
      simp_all <;> ring

/-- **The twisted Heisenberg commutation relation** (FLM (9.1.x)): for odd `k, l`,
`[h_i(k/2), h_j(l/2)] = (k/2) δ_{ij} δ_{k+l,0} · id`. -/
theorem modeT_comm (r : ℕ) (i j : Fin r) {k l : ℤ} (hk : Odd k) (hl : Odd l) :
    modeT r i k * modeT r j l - modeT r j l * modeT r i k
      = (if i = j ∧ k + l = 0 then (k : ℂ) / 2 else 0) • LinearMap.id := by
  have hk' := Int.odd_iff.mp hk
  have hl' := Int.odd_iff.mp hl
  refine LinearMap.ext fun p => ?_
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
      LinearMap.smul_apply, LinearMap.id_apply]
  rcases lt_or_gt_of_ne (show k ≠ 0 by omega) with hkn | hkp <;>
    rcases lt_or_gt_of_ne (show l ≠ 0 by omega) with hln | hlp
  · rw [modeT_apply_neg r i hk hkn, modeT_apply_neg r j hl hln, modeT_apply_neg r j hl hln,
      modeT_apply_neg r i hk hkn, if_neg (by omega), zero_smul, mul_left_comm, sub_self]
  · rw [modeT_apply_neg r i hk hkn, modeT_apply_pos r j hl hlp, modeT_apply_pos r j hl hlp,
      modeT_apply_neg r i hk hkn, mul_smul_comm, ← smul_sub]
    have hc := pderiv_X_mul_sub (varT j l) (varT i k) p
    have hc' : X (varT i k) * pderiv (varT j l) p - pderiv (varT j l) (X (varT i k) * p)
        = -(if varT j l = varT i k then p else 0) := by rw [← hc]; ring
    rw [hc']
    by_cases h : i = j ∧ k + l = 0
    · rw [if_pos h, if_pos (by
        simp only [varT, Prod.mk.injEq]; refine ⟨?_, h.1.symm⟩
        rw [abs_of_pos hlp, abs_of_neg hkn]; omega)]
      have : (l : ℂ) = -(k : ℂ) := by rw [show l = -k by omega]; push_cast; ring
      rw [this, smul_neg, ← neg_smul]; congr 1; ring
    · rw [if_neg h, if_neg (by
        simp only [varT, Prod.mk.injEq, not_and]
        intro h1 h2; apply h; refine ⟨h2.symm, ?_⟩
        rw [abs_of_pos hlp, abs_of_neg hkn] at h1; omega)]
      simp
  · rw [modeT_apply_pos r i hk hkp, modeT_apply_neg r j hl hln, modeT_apply_neg r j hl hln,
      modeT_apply_pos r i hk hkp, mul_smul_comm, ← smul_sub, pderiv_X_mul_sub]
    by_cases h : i = j ∧ k + l = 0
    · rw [if_pos h, if_pos (by
        simp only [varT, Prod.mk.injEq]; refine ⟨?_, h.1⟩
        rw [abs_of_pos hkp, abs_of_neg hln]; omega)]
    · rw [if_neg h, if_neg (by
        simp only [varT, Prod.mk.injEq, not_and]
        intro h1 h2; apply h; refine ⟨h2, ?_⟩
        rw [abs_of_pos hkp, abs_of_neg hln] at h1; omega)]
      simp
  · rw [modeT_apply_pos r i hk hkp, modeT_apply_pos r j hl hlp, modeT_apply_pos r i hk hkp,
      modeT_apply_pos r j hl hlp, if_neg (by omega), zero_smul, Derivation.map_smul,
      Derivation.map_smul, pderiv_pderiv_comm, smul_smul, smul_smul, mul_comm, sub_self]

/-! ## The vacuum and the creation monomials -/

/-- Every positive mode annihilates the vacuum: `h_i(k/2) 1 = 0` for `k > 0` (and trivially for
even `k`). -/
theorem modeT_vacT (r : ℕ) (i : Fin r) {k : ℤ} (hk : 0 < k) : modeT r i k (vacT r) = 0 := by
  by_cases he : k % 2 = 0
  · rw [modeT_even r i he, LinearMap.zero_apply]
  · rw [modeT_apply_pos r i (Int.odd_iff.mpr (by omega)) hk, vacT, pderiv_one, smul_zero]

/-- The creation word `h_{v₁}(-n₁-½) ⋯ h_{vₘ}(-nₘ-½)` attached to a list of variables
`[(n₁, v₁), …]`, as an endomorphism of `S[θ]`. -/
noncomputable def creationWordT (r : ℕ) (l : List (ℕ × Fin r)) : Module.End ℂ (FockT r) :=
  (l.map fun v => modeT r v.2 (-(2 * v.1 + 1))).prod

/-- A creation word applied to the vacuum is the corresponding monomial `∏ X_v`. -/
theorem creationWordT_vacT (r : ℕ) (l : List (ℕ × Fin r)) :
    creationWordT r l (vacT r) = (l.map X).prod := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    simp only [creationWordT, List.map_cons, List.prod_cons, Module.End.mul_apply] at ih ⊢
    rw [ih, modeT_creation]

/-- **`S[θ]` is spanned by creation words on the vacuum.** -/
theorem span_creationWordT_vacT (r : ℕ) :
    Submodule.span ℂ (Set.range fun l => creationWordT r l (vacT r)) = ⊤ := by
  simp_rw [creationWordT_vacT]
  have htop : Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range (X : ℕ × Fin r → FockT r)))
      = ⊤ := Algebra.toSubmodule_eq_top.2 (MvPolynomial.adjoin_range_X)
  rw [eq_top_iff, ← htop, Algebra.adjoin_eq_span]
  refine Submodule.span_mono fun x hx => ?_
  induction hx using Submonoid.closure_induction with
  | mem x hx => obtain ⟨v, rfl⟩ := hx; exact ⟨[v], by simp⟩
  | one => exact ⟨[], by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l, rfl⟩ := hx; obtain ⟨m, rfl⟩ := hy
    exact ⟨l ++ m, by simp⟩

/-! ## The `L₀`-grading

The variable `(n, i)` (the mode `h_i(-n-½)`) has `L₀`-weight `n + ½`.  To stay in `ℕ` we grade by
the **doubled** weight `wT (n, i) = 2n + 1`: `gradingT r d` is the span of monomials of doubled
weight `d`, whose `L₀`-eigenvalue is `d/2 + r/16`. -/

/-- Doubled weight of the variable `(n, i)`: `2n + 1 = 2 · (n + ½)`. -/
def wT {r : ℕ} : ℕ × Fin r → ℕ := fun v => 2 * v.1 + 1

/-- Evaluation of the doubled weight. -/
@[simp] theorem wT_apply {r : ℕ} (v : ℕ × Fin r) : wT v = 2 * v.1 + 1 := rfl

/-- The doubled-weight-`d` piece of `S[θ]` (`L₀`-eigenvalue `d/2 + r/16`). -/
def gradingT (r d : ℕ) : Submodule ℂ (FockT r) := weightedHomogeneousSubmodule ℂ wT d

/-- Membership in a graded piece is weighted homogeneity. -/
theorem mem_gradingT {r d : ℕ} {p : FockT r} :
    p ∈ gradingT r d ↔ p.IsWeightedHomogeneous wT d := Iff.rfl

/-- The vacuum has doubled weight `0` (`L₀ = r/16`). -/
theorem vacT_mem_gradingT (r : ℕ) : vacT r ∈ gradingT r 0 :=
  isWeightedHomogeneous_one ℂ wT

/-- `h_i(-n-½)` raises the doubled weight by `2n+1`. -/
theorem modeT_creation_mem (r : ℕ) (i : Fin r) (n : ℕ) {d : ℕ} {p : FockT r}
    (hp : p ∈ gradingT r d) : modeT r i (-(2 * n + 1)) p ∈ gradingT r (d + (2 * n + 1)) := by
  rw [modeT_creation]
  have hX := isWeightedHomogeneous_X ℂ (wT (r := r)) (n, i)
  rw [wT_apply] at hX
  have := hX.mul hp
  rwa [add_comm] at this

/-- `h_i(n+½)` lowers the doubled weight by `2n+1`. -/
theorem modeT_annihilation_mem (r : ℕ) (i : Fin r) (n : ℕ) {d : ℕ} {p : FockT r}
    (hp : p ∈ gradingT r (d + (2 * n + 1))) : modeT r i (2 * n + 1) p ∈ gradingT r d := by
  rw [modeT_annihilation]
  exact Submodule.smul_mem _ _ (IsWeightedHomogeneous.pderiv hp (by simp))

/-- **`S[θ] = ⊕_d (S[θ])_d`** (doubled-weight grading). -/
theorem gradingT_isInternal (r : ℕ) : DirectSum.IsInternal (gradingT r) :=
  (MvPolynomial.weightedDecomposition ℂ (wT (r := r))).isInternal

/-- Exponent vectors of doubled weight `d`. -/
def degSetT (r d : ℕ) : Set ((ℕ × Fin r) →₀ ℕ) := {m | Finsupp.weight wT m = d}

/-- Finitely many exponent vectors have a given doubled weight (all variable weights are `≥ 1`,
and a variable of index `n` has weight `2n+1`). -/
theorem degSetT_finite (r d : ℕ) : (degSetT r d).Finite := by
  classical
  have hle : ∀ m ∈ degSetT r d, ∀ v, m v ≤ d := fun m hm v => by
    have := Finsupp.le_weight (wT (r := r)) (s := v) (by simp) m
    rw [show Finsupp.weight wT m = d from hm] at this; exact this
  have hlt : ∀ m ∈ degSetT r d, ∀ v, m v ≠ 0 → v.1 < d := fun m hm v hv => by
    have := Finsupp.le_weight_of_ne_zero' (wT (r := r)) hv
    rw [show Finsupp.weight wT m = d from hm, wT_apply] at this; omega
  rw [← Set.finite_coe_iff]
  refine Finite.of_injective
    (β := Fin d × Fin r → Fin (d + 1))
    (fun m v => ⟨m.1 (v.1, v.2), by have := hle m.1 m.2 (v.1, v.2); omega⟩) ?_
  rintro ⟨m, hm⟩ ⟨m', hm'⟩ h
  refine Subtype.ext (Finsupp.ext fun v => ?_)
  by_cases hv : v.1 < d
  · have := congrFun h ⟨⟨v.1, hv⟩, v.2⟩
    simpa using congrArg Fin.val this
  · have h1 : m v = 0 := by by_contra hne; exact hv (hlt m hm v hne)
    have h2 : m' v = 0 := by by_contra hne; exact hv (hlt m' hm' v hne)
    rw [h1, h2]

/-- A graded piece is the span of the monomials of that doubled weight. -/
theorem gradingT_eq_supported (r d : ℕ) :
    gradingT r d = Finsupp.supported ℂ ℂ (degSetT r d) :=
  weightedHomogeneousSubmodule_eq_finsupp_supported ℂ wT d

/-- Each graded piece of `S[θ]` is finite-dimensional. -/
instance gradingT_finiteDimensional (r d : ℕ) : FiniteDimensional ℂ (gradingT r d) := by
  have hs := degSetT_finite r d
  letI : Fintype (degSetT r d) := hs.fintype
  rw [gradingT_eq_supported]
  exact FiniteDimensional.of_injective
    (Finsupp.supportedEquivFinsupp (R := ℂ) (M := ℂ) (degSetT r d)).toLinearMap
    (Finsupp.supportedEquivFinsupp (R := ℂ) (M := ℂ) (degSetT r d)).injective

/-- `finrank (gradingT r d) = #{exponent vectors of doubled weight d}`. -/
theorem finrank_gradingT (r d : ℕ) :
    Module.finrank ℂ (gradingT r d) = Nat.card (degSetT r d) := by
  have hs := degSetT_finite r d
  letI : Fintype (degSetT r d) := hs.fintype
  have e := (LinearEquiv.ofEq _ _ (gradingT_eq_supported r d)).trans
    (Finsupp.supportedEquivFinsupp (R := ℂ) (M := ℂ) (degSetT r d))
  rw [e.finrank_eq, Module.finrank_finsupp_self, Nat.card_eq_fintype_card]

/-- The only exponent vector of doubled weight `0` is `0`. -/
theorem degSetT_zero (r : ℕ) : degSetT r 0 = {0} := by
  ext m
  simp only [degSetT, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    ext v
    by_contra hv
    have := Finsupp.le_weight_of_ne_zero' (wT (r := r)) hv
    rw [h, wT_apply] at this; omega
  · rintro rfl; simp

/-- The exponent vectors of doubled weight `1` are the single variables `(0, i)`. -/
theorem degSetT_one (r : ℕ) :
    degSetT r 1 = Set.range fun i : Fin r => Finsupp.single ((0 : ℕ), i) 1 := by
  ext m
  simp only [degSetT, Set.mem_setOf_eq, Set.mem_range]
  constructor
  · intro h
    have hm0 : m ≠ 0 := by rintro rfl; simp at h
    obtain ⟨v, hv⟩ := Finsupp.ne_iff.mp hm0
    have hv' : m v ≠ 0 := by simpa using hv
    have hsplit := Finsupp.weight_sub_single_add (w := wT (r := r)) hv'
    rw [h, wT_apply] at hsplit
    have hv1 : v.1 = 0 := by omega
    have hrest : Finsupp.weight wT (m - Finsupp.single v 1) = 0 := by omega
    have hz : m - Finsupp.single v 1 = 0 := by
      ext u
      by_contra hu
      have := Finsupp.le_weight_of_ne_zero' (wT (r := r)) hu
      rw [hrest, wT_apply] at this; omega
    refine ⟨v.2, ?_⟩
    have hv2 : ((0 : ℕ), v.2) = v := by ext <;> simp [hv1]
    rw [hv2]
    refine le_antisymm (Finsupp.single_le_iff.mpr (by omega)) (tsub_eq_zero_iff_le.mp hz)
  · rintro ⟨i, rfl⟩
    simp [Finsupp.weight_apply, Finsupp.sum_single_index]

/-- **The ground state is unique**: the doubled-weight-`0` piece (`L₀ = r/16`) is `ℂ · vacT`. -/
theorem gradingT_zero (r : ℕ) : gradingT r 0 = ℂ ∙ vacT r := by
  apply le_antisymm
  · intro p hp
    have hconst : p = C (coeff 0 p) := by
      ext m
      rw [coeff_C]
      by_cases hm : m = 0
      · rw [if_pos hm.symm, hm]
      · rw [if_neg (Ne.symm hm)]
        by_contra hne
        have : m ∈ degSetT r 0 := hp hne
        rw [degSetT_zero] at this; exact hm this
    rw [hconst, show (C (coeff 0 p) : FockT r) = coeff 0 p • vacT r by
      rw [vacT, smul_eq_C_mul, mul_one]]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_singleton_le_iff_mem]; exact vacT_mem_gradingT r

/-- The ground-state level is one-dimensional. -/
theorem finrank_gradingT_zero (r : ℕ) : Module.finrank ℂ (gradingT r 0) = 1 := by
  rw [finrank_gradingT, degSetT_zero, Nat.card_unique]

/-- **The first excited level** (`L₀ = r/16 + ½`) has dimension `r`: it is spanned by the
`h_i(-½) 1`, `i : Fin r`. -/
theorem finrank_gradingT_one (r : ℕ) : Module.finrank ℂ (gradingT r 1) = r := by
  rw [finrank_gradingT, degSetT_one, Nat.card_range_of_injective, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  intro i j h
  have := congrArg (fun f => f ((0 : ℕ), i)) h
  by_contra hij
  simp [hij] at this

/-! ### The `ℚ`-valued `L₀`-grading

`weightT r q` is the `L₀`-eigenspace of eigenvalue `q ∈ ℚ`: it is `gradingT r d` when
`q = d/2 + r/16` and `⊥` when `q ∉ r/16 + ½ℕ`. -/

/-- The doubled weight `d` corresponds to the `L₀`-eigenvalue `d/2 + r/16`. -/
def levelT (r d : ℕ) : ℚ := (d : ℚ) / 2 + (r : ℚ) / 16

/-- Distinct doubled weights give distinct `L₀`-eigenvalues. -/
theorem levelT_injective (r : ℕ) : Function.Injective (levelT r) := by
  intro d e h
  simp only [levelT] at h
  exact_mod_cast (show (d : ℚ) = e by linarith)

/-- The `L₀`-eigenspace of eigenvalue `q : ℚ` in `S[θ]`. -/
noncomputable def weightT (r : ℕ) (q : ℚ) : Submodule ℂ (FockT r) :=
  ⨆ (d : ℕ) (_ : levelT r d = q), gradingT r d

/-- At `q = d/2 + r/16` the eigenspace is the doubled-weight-`d` piece. -/
theorem weightT_levelT (r d : ℕ) : weightT r (levelT r d) = gradingT r d := by
  apply le_antisymm
  · refine iSup₂_le fun e he => ?_
    rw [levelT_injective r he]
  · exact le_iSup₂_of_le d rfl le_rfl

/-- Away from `r/16 + ½ℕ` the eigenspace is zero. -/
theorem weightT_eq_bot {r : ℕ} {q : ℚ} (hq : ∀ d : ℕ, levelT r d ≠ q) : weightT r q = ⊥ := by
  rw [weightT, eq_bot_iff]
  exact iSup₂_le fun d hd => absurd hd (hq d)

/-- **`S[θ] = ⊕_{q ∈ ℚ} S[θ]_q`**, the `L₀`-eigenspace decomposition. -/
theorem weightT_isInternal (r : ℕ) : DirectSum.IsInternal (weightT r) := by
  have hA := gradingT_isInternal r
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · rw [← iSupIndep_ne_bot]
    have hex : ∀ q : {q : ℚ // weightT r q ≠ ⊥}, ∃ d : ℕ, levelT r d = q.1 := by
      rintro ⟨q, hq⟩
      by_contra h
      push Not at h
      exact hq (weightT_eq_bot h)
    choose g hg using hex
    have hginj : Function.Injective g := by
      intro a b h
      exact Subtype.ext (by rw [← hg a, ← hg b, h])
    have hcomp : (fun q : {q : ℚ // weightT r q ≠ ⊥} => weightT r q.1) = gradingT r ∘ g := by
      funext q
      simp only [Function.comp_apply]
      rw [← weightT_levelT, hg q]
    rw [hcomp]
    exact hA.submodule_iSupIndep.comp hginj
  · rw [eq_top_iff, ← hA.submodule_iSup_eq_top]
    exact iSup_le fun d => (weightT_levelT r d) ▸ le_iSup (weightT r) (levelT r d)

/-- Every `L₀`-eigenspace of `S[θ]` is finite-dimensional. -/
instance weightT_finiteDimensional (r : ℕ) (q : ℚ) : FiniteDimensional ℂ (weightT r q) := by
  by_cases h : ∃ d : ℕ, levelT r d = q
  · obtain ⟨d, rfl⟩ := h
    rw [weightT_levelT]; infer_instance
  · push Not at h
    rw [weightT_eq_bot h]; infer_instance

/-- **Vacuum weight `r/16`**: the `L₀ = r/16` eigenspace is `ℂ · vacT`. -/
theorem weightT_vacuum (r : ℕ) : weightT r ((r : ℚ) / 16) = ℂ ∙ vacT r := by
  have : levelT r 0 = (r : ℚ) / 16 := by simp [levelT]
  rw [← this, weightT_levelT, gradingT_zero]

/-- The `L₀ = r/16` eigenspace is one-dimensional. -/
theorem finrank_weightT_vacuum (r : ℕ) : Module.finrank ℂ (weightT r ((r : ℚ) / 16)) = 1 := by
  have : levelT r 0 = (r : ℚ) / 16 := by simp [levelT]
  rw [← this, weightT_levelT, finrank_gradingT_zero]

/-- The `L₀ = r/16 + ½` eigenspace has dimension `r`. -/
theorem finrank_weightT_half (r : ℕ) :
    Module.finrank ℂ (weightT r ((r : ℚ) / 16 + 1 / 2)) = r := by
  have : levelT r 1 = (r : ℚ) / 16 + 1 / 2 := by simp [levelT]; ring
  rw [← this, weightT_levelT, finrank_gradingT_one]

/-- There are no states of `L₀`-weight below `r/16`. -/
theorem weightT_eq_bot_of_lt {r : ℕ} {q : ℚ} (hq : q < (r : ℚ) / 16) : weightT r q = ⊥ :=
  weightT_eq_bot fun d hd => by
    simp only [levelT] at hd
    have : (0 : ℚ) ≤ d := d.cast_nonneg
    linarith

/-! ## The involution `θ`

`θ` is the lift of `-1` on the Cartan subalgebra: `θ h_i(t) θ⁻¹ = -h_i(t)`.  On `S[θ]` it is the
algebra automorphism negating every variable, i.e. `θ = (-1)^N` with `N` the oscillator number. -/

/-- The algebra endomorphism negating every variable. -/
noncomputable def thetaHom (r : ℕ) : FockT r →ₐ[ℂ] FockT r := aeval fun v => -X v

/-- `θ X_v = -X_v`. -/
@[simp] theorem thetaHom_X (r : ℕ) (v : ℕ × Fin r) : thetaHom r (X v) = -X v := by
  simp [thetaHom]

/-- `θ ∘ θ = id`. -/
theorem thetaHom_comp_self (r : ℕ) : (thetaHom r).comp (thetaHom r) = AlgHom.id ℂ (FockT r) :=
  algHom_ext fun v => by simp

/-- **The involution `θ` of `S[θ]`**, an algebra automorphism. -/
noncomputable def thetaT (r : ℕ) : FockT r ≃ₐ[ℂ] FockT r :=
  AlgEquiv.ofAlgHom (thetaHom r) (thetaHom r) (thetaHom_comp_self r) (thetaHom_comp_self r)

/-- The automorphism `θ` applies the negation endomorphism. -/
@[simp] theorem thetaT_apply (r : ℕ) (p : FockT r) : thetaT r p = thetaHom r p := rfl

/-- `θ h_i(-n-½) 1 = -h_i(-n-½) 1`. -/
@[simp] theorem thetaT_X (r : ℕ) (v : ℕ × Fin r) : thetaT r (X v) = -X v := thetaHom_X r v

/-- `θ` is an involution. -/
theorem thetaT_thetaT (r : ℕ) (p : FockT r) : thetaT r (thetaT r p) = p :=
  congrArg (fun φ : FockT r →ₐ[ℂ] FockT r => φ p) (thetaHom_comp_self r)

/-- The vacuum is `θ`-invariant. -/
theorem thetaT_vacT (r : ℕ) : thetaT r (vacT r) = vacT r := map_one _

/-- Negating every variable in a monomial multiplies it by `(-1)^{degree}`. -/
theorem prod_neg_X {r : ℕ} (m : (ℕ × Fin r) →₀ ℕ) :
    (m.prod fun v e => (-X v : FockT r) ^ e)
      = (-1 : FockT r) ^ m.degree * m.prod fun v e => (X v : FockT r) ^ e := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _), hf, hg, map_add, pow_add]
    ring
  | single v e =>
    rw [Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp),
      Finsupp.degree_single, neg_pow]

/-- **`θ = (-1)^N` on monomials**: `θ X^m = (-1)^{|m|} X^m`, `|m|` the number of oscillators. -/
theorem thetaT_monomial (r : ℕ) (m : (ℕ × Fin r) →₀ ℕ) (c : ℂ) :
    thetaT r (monomial m c) = (-1 : ℂ) ^ m.degree • monomial m c := by
  rw [thetaT_apply, thetaHom, monomial_eq, map_mul, aeval_C, map_finsuppProd]
  simp only [map_pow, aeval_X]
  rw [prod_neg_X, Algebra.smul_def, map_pow, map_neg, map_one, algebraMap_eq]
  ring

/-- `θ` acts on coefficients by the oscillator-number sign. -/
theorem coeff_thetaT (r : ℕ) (m : (ℕ × Fin r) →₀ ℕ) (p : FockT r) :
    coeff m (thetaT r p) = (-1 : ℂ) ^ m.degree * coeff m p := by
  induction p using MvPolynomial.induction_on' with
  | monomial n c =>
    rw [thetaT_monomial, coeff_smul, coeff_monomial, smul_eq_mul]
    by_cases h : n = m
    · subst h; simp
    · simp [h]
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

/-- `θ` preserves the `L₀`-grading. -/
theorem thetaT_mem_gradingT {r d : ℕ} {p : FockT r} (hp : p ∈ gradingT r d) :
    thetaT r p ∈ gradingT r d := by
  intro m hm
  rw [coeff_thetaT] at hm
  exact hp (right_ne_zero_of_mul hm)

/-- `θ` preserves every `L₀`-eigenspace. -/
theorem thetaT_mem_weightT {r : ℕ} {q : ℚ} {p : FockT r} (hp : p ∈ weightT r q) :
    thetaT r p ∈ weightT r q := by
  by_cases h : ∃ d : ℕ, levelT r d = q
  · obtain ⟨d, rfl⟩ := h
    rw [weightT_levelT] at hp ⊢; exact thetaT_mem_gradingT hp
  · push Not at h
    rw [weightT_eq_bot h, Submodule.mem_bot] at hp ⊢
    rw [hp, map_zero]

/-- `θ` anticommutes with every twisted mode: `θ h_i(k/2) = -h_i(k/2) θ`. -/
theorem thetaT_modeT (r : ℕ) (i : Fin r) (k : ℤ) (p : FockT r) :
    thetaT r (modeT r i k p) = -modeT r i k (thetaT r p) := by
  by_cases he : k % 2 = 0
  · simp [modeT_even r i he]
  have hk : Odd k := Int.odd_iff.mpr (by omega)
  rcases lt_or_gt_of_ne (show k ≠ 0 by omega) with hkn | hkp
  · rw [modeT_apply_neg r i hk hkn, modeT_apply_neg r i hk hkn, map_mul, thetaT_X, neg_mul]
  · rw [modeT_apply_pos r i hk hkp, modeT_apply_pos r i hk hkp, map_smul, ← smul_neg]
    congr 1
    induction p using MvPolynomial.induction_on with
    | C c => simp [← algebraMap_eq]
    | add p q hp hq => simp only [map_add, hp, hq, neg_add]
    | mul_X p s h =>
      rw [pderiv_mul, map_add, map_mul, map_mul, h, thetaT_X, map_mul, thetaT_X, pderiv_mul,
        (pderiv (R := ℂ) (varT i k)).map_neg (X s), pderiv_X]
      by_cases hs : varT i k = s
      · subst hs; simp; ring
      · simp [hs]

/-- `θ`-fixed vectors are exactly those supported on even oscillator number. -/
theorem thetaT_eq_self_iff (r : ℕ) (p : FockT r) :
    thetaT r p = p ↔ ∀ m, coeff m p ≠ 0 → Even m.degree := by
  constructor
  · intro h m hm
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have := congrArg (coeff m) h
    rw [coeff_thetaT, hodd.neg_one_pow] at this
    exact hm (by linear_combination -this / 2)
  · intro h
    ext m
    rw [coeff_thetaT]
    by_cases hm : coeff m p = 0
    · rw [hm, mul_zero]
    · rw [(h m hm).neg_one_pow, one_mul]

/-- `θ`-anti-fixed vectors are exactly those supported on odd oscillator number. -/
theorem thetaT_eq_neg_iff (r : ℕ) (p : FockT r) :
    thetaT r p = -p ↔ ∀ m, coeff m p ≠ 0 → Odd m.degree := by
  constructor
  · intro h m hm
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have := congrArg (coeff m) h
    rw [coeff_thetaT, hev.neg_one_pow, coeff_neg] at this
    exact hm (by linear_combination this / 2)
  · intro h
    ext m
    rw [coeff_thetaT, coeff_neg]
    by_cases hm : coeff m p = 0
    · rw [hm, mul_zero, neg_zero]
    · rw [(h m hm).neg_one_pow]; ring

/-- `θ = -1` on the first excited level `h_i(-½) 1`. -/
theorem thetaT_of_mem_gradingT_one {r : ℕ} {p : FockT r} (hp : p ∈ gradingT r 1) :
    thetaT r p = -p := by
  rw [thetaT_eq_neg_iff]
  intro m hm
  have : m ∈ degSetT r 1 := hp hm
  rw [degSetT_one] at this
  obtain ⟨i, rfl⟩ := this
  simp

/-! ## The Virasoro operator `L₀`

`L₀ = Σ_i Σ_{n ≥ 0} h_i(-n-½) h_i(n+½) + r/16`.  We define it through the weighted Euler
derivation `E = Σ_v wT(v) X_v ∂_v` (a well-defined derivation, although the sum is infinite),
`L₀ = ½ E + r/16`, and then prove the mode-sum formula on each vector (where the sum is finite). -/

/-- The doubled-weight Euler derivation `E X_v = (2n+1) X_v` for `v = (n, i)`. -/
noncomputable def eulerT (r : ℕ) : Derivation ℂ (FockT r) (FockT r) :=
  mkDerivation ℂ fun v => ((wT v : ℕ) : ℂ) • (X v : FockT r)

/-- `E X_v = wT(v) X_v`. -/
@[simp] theorem eulerT_X (r : ℕ) (v : ℕ × Fin r) :
    eulerT r (X v) = ((wT v : ℕ) : ℂ) • (X v : FockT r) := mkDerivation_X _ _ _

/-- `E` acts on the monomial `X^m` by its doubled weight. -/
theorem eulerT_monomial (r : ℕ) (m : (ℕ × Fin r) →₀ ℕ) (c : ℂ) :
    eulerT r (monomial m c) = ((Finsupp.weight wT m : ℕ) : ℂ) • monomial m c := by
  induction m using Finsupp.induction_linear generalizing c with
  | zero => simp [← C_apply]
  | add f g hf hg =>
    have hsplit : (monomial (f + g) c : FockT r) = monomial f c * monomial g 1 := by
      rw [monomial_mul, mul_one]
    rw [hsplit, Derivation.leibniz, hf, hg, map_add, smul_eq_mul, smul_eq_mul]
    simp only [Algebra.smul_def, algebraMap_eq, Nat.cast_add, map_add]
    ring
  | single v e =>
    rw [← C_mul_X_pow_eq_monomial, Derivation.leibniz, Derivation.leibniz_pow, eulerT_X,
      ← algebraMap_eq, Derivation.map_algebraMap, smul_zero, add_zero, Finsupp.weight_single]
    rcases e with _ | k
    · simp
    · rw [Nat.add_sub_cancel, smul_eq_mul (X v ^ k), algebraMap_smul, ← Algebra.smul_def,
        mul_smul_comm, ← pow_succ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul, smul_smul]
      congr 1
      rw [smul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one]; ring

/-- Euler's identity: on the doubled-weight-`d` piece, `E` acts by `d`. -/
theorem eulerT_of_mem_gradingT {r d : ℕ} {p : FockT r} (hp : p ∈ gradingT r d) :
    eulerT r p = (d : ℂ) • p := by
  conv_lhs => rw [MvPolynomial.as_sum p]
  conv_rhs => rw [MvPolynomial.as_sum p]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [eulerT_monomial, show Finsupp.weight wT m = d from hp (mem_support_iff.mp hm)]

/-- **The Virasoro operator** `L₀ = ½ E + r/16` on `S[θ]`. -/
noncomputable def L0T (r : ℕ) : Module.End ℂ (FockT r) :=
  (1 / 2 : ℂ) • (eulerT r).toLinearMap + ((r : ℂ) / 16) • LinearMap.id

/-- Unfolding of `L0T`. -/
theorem L0T_apply (r : ℕ) (p : FockT r) :
    L0T r p = (1 / 2 : ℂ) • eulerT r p + ((r : ℂ) / 16) • p := rfl

/-- **`L₀` is diagonal on the grading**: on `gradingT r d` it acts by `d/2 + r/16`. -/
theorem L0T_of_mem_gradingT {r d : ℕ} {p : FockT r} (hp : p ∈ gradingT r d) :
    L0T r p = ((levelT r d : ℚ) : ℂ) • p := by
  rw [L0T_apply, eulerT_of_mem_gradingT hp, smul_smul, ← add_smul, levelT]
  congr 1; push_cast; ring

/-- `weightT r q` is the `L₀`-eigenspace of eigenvalue `q`. -/
theorem L0T_of_mem_weightT {r : ℕ} {q : ℚ} {p : FockT r} (hp : p ∈ weightT r q) :
    L0T r p = (q : ℂ) • p := by
  by_cases h : ∃ d : ℕ, levelT r d = q
  · obtain ⟨d, rfl⟩ := h
    rw [weightT_levelT] at hp; exact L0T_of_mem_gradingT hp
  · push Not at h
    rw [weightT_eq_bot h, Submodule.mem_bot] at hp
    rw [hp, map_zero, smul_zero]

/-- The vacuum has `L₀`-weight `r/16`. -/
theorem L0T_vacT (r : ℕ) : L0T r (vacT r) = ((r : ℂ) / 16) • vacT r := by
  rw [L0T_of_mem_gradingT (vacT_mem_gradingT r), levelT]; congr 1; push_cast; ring

/-- `E` is the (finite, on each vector) sum `Σ_{v ∈ vars p} wT(v) X_v ∂_v p`. -/
theorem eulerT_eq_sum (r : ℕ) (p : FockT r) :
    eulerT r p = ∑ v ∈ p.vars, ((wT v : ℕ) : ℂ) • (X v * pderiv v p) := by
  let D : Derivation ℂ (FockT r) (FockT r) :=
    ∑ v ∈ p.vars, ((wT v : ℕ) : ℂ) • ((X v : FockT r) • pderiv v)
  have hD : ∀ q : FockT r, D q = ∑ v ∈ p.vars, ((wT v : ℕ) : ℂ) • (X v * pderiv v q) := by
    intro q
    rw [← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply, Derivation.smul_apply,
      smul_eq_mul]
  rw [← hD]
  refine derivation_eq_of_forall_mem_vars fun i hi => ?_
  rw [hD, eulerT_X, Finset.sum_eq_single i]
  · rw [pderiv_X_self, mul_one]
  · intro b _ hb; rw [pderiv_X_of_ne (Ne.symm hb), mul_zero, smul_zero]
  · intro h; exact absurd hi h

/-- **The mode-sum formula** `L₀ = Σ_i Σ_{n ≥ 0} h_i(-n-½) h_i(n+½) + r/16`, on each vector
(only the variables of `p` contribute, since `h_i(n+½) p = 0` otherwise). -/
theorem L0T_eq_modeSum (r : ℕ) (p : FockT r) :
    L0T r p = ∑ v ∈ p.vars, modeT r v.2 (-(2 * v.1 + 1)) (modeT r v.2 (2 * v.1 + 1) p)
      + ((r : ℂ) / 16) • p := by
  rw [L0T_apply, eulerT_eq_sum, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [modeT_annihilation, modeT_creation, mul_smul_comm, smul_smul, wT_apply]
  congr 1
  push_cast; ring

/-- `[E, ∂_v] = -wT(v) ∂_v`. -/
theorem eulerT_pderiv (r : ℕ) (v : ℕ × Fin r) (p : FockT r) :
    eulerT r (pderiv v p) = pderiv v (eulerT r p) - ((wT v : ℕ) : ℂ) • pderiv v p := by
  have h : ⁅eulerT r, (pderiv v : Derivation ℂ (FockT r) (FockT r))⁆
      = -(((wT v : ℕ) : ℂ) • (pderiv v : Derivation ℂ (FockT r) (FockT r))) := by
    refine MvPolynomial.derivation_ext fun u => ?_
    by_cases huv : u = v
    · subst huv; simp [Derivation.commutator_apply]
    · simp [Derivation.commutator_apply, huv]
  have := congrArg (fun D : Derivation ℂ (FockT r) (FockT r) => D p) h
  simp only [Derivation.commutator_apply, Derivation.neg_apply, Derivation.smul_apply] at this
  linear_combination this

/-- **`[L₀, h_i(k/2)] = -(k/2) h_i(k/2)`**: modes shift the `L₀`-eigenvalue by `-k/2`. -/
theorem L0T_comm_modeT (r : ℕ) (i : Fin r) (k : ℤ) :
    L0T r * modeT r i k - modeT r i k * L0T r = -((k : ℂ) / 2) • modeT r i k := by
  by_cases he : k % 2 = 0
  · simp [modeT_even r i he]
  have hk : Odd k := Int.odd_iff.mpr (by omega)
  refine LinearMap.ext fun p => ?_
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, LinearMap.smul_apply]
  rcases lt_or_gt_of_ne (show k ≠ 0 by omega) with hkn | hkp
  · have hw : ((wT (varT i k) : ℕ) : ℂ) = -(k : ℂ) := by
      have : ((wT (varT i k) : ℕ) : ℤ) = -k := by
        simp only [wT_apply, varT]; rw [abs_of_neg hkn]; omega
      exact_mod_cast this
    rw [modeT_apply_neg r i hk hkn, modeT_apply_neg r i hk hkn, L0T_apply, L0T_apply,
      Derivation.leibniz, eulerT_X, hw, smul_eq_mul, smul_eq_mul, mul_smul_comm, mul_add,
      mul_smul_comm, mul_smul_comm, mul_comm p]
    module
  · have hw : ((wT (varT i k) : ℕ) : ℂ) = (k : ℂ) := by
      have : ((wT (varT i k) : ℕ) : ℤ) = k := by
        simp only [wT_apply, varT]; rw [abs_of_pos hkp]; omega
      exact_mod_cast this
    rw [modeT_apply_pos r i hk hkp, modeT_apply_pos r i hk hkp, map_smul, L0T_apply, L0T_apply,
      eulerT_pderiv, hw, map_add, Derivation.map_smul, Derivation.map_smul]
    module

end TwistedHeisenberg

end VOA
