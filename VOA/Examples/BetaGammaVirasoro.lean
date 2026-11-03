/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.BetaGamma
import Mathlib.Data.Int.Interval

/-!
# `βγ` symplectic bosons: the Virasoro algebra at `c = -1`, and **half-integer weights**

The `βγ` system of `Examples/BetaGamma` carries two *commuting* fields `β`, `γ`.  This file
builds its Virasoro modes **directly as normally-ordered bilinears in the `β`, `γ` modes**, in
the explicit style of `Examples/VirasoroFock` (`Lld`, `Lld_virasoro`) and
`Examples/SymplecticFermionVirasoroB` (`Lsf`, `Lsf_virasoro`), and proves

`[Lₘ, Lₙ] = (m-n)L_{m+n} + δ_{m+n,0}·(m³-m)/12·(-1)`.

Nothing here uses the vertex-operator machinery (`nprodε`, `reconstructε`); the only inputs are
the canonical **commutation** relations of `Examples/BetaGamma` (`beta_gamma_comm`, `beta_comm`,
`gamma_comm`) and elementary facts about the polynomial Fock space.

## Why this file exists: the first genuinely half-integer conformal weight

Every `SuperVertexAlgebra` instance in the library so far is a symplectic-fermion variant, whose
conformal weights are **integers in both parities**.  The `ℂ`-valued grading of
`Core/SuperVertexAlgebra` therefore had never been exercised at a non-integer weight.  Here it
is, at the level of `L₀`-eigenvalues:

* `Lbg_zero_bM_creation` : `L₀ (β₋ₖ₋₁ₗ₂ |0⟩) = (k + 1/2)·β₋ₖ₋₁ₗ₂|0⟩`,
* `Lbg_zero_bM_neg_one`  : `L₀ (β₋₁ₗ₂|0⟩) = (1/2)·β₋₁ₗ₂|0⟩` with `β₋₁ₗ₂|0⟩ = X₍ᵢₙₗ ₀₎ ≠ 0`.

So `1/2 ∈ ℂ` really occurs as a conformal weight on a nonzero vector, and it occurs in the
**even** (bosonic) sector — the fields are commuting, locality is at `ε = 1`.  This is the
Axis-A-without-Axis-B corner: half-integer moding with no Koszul sign anywhere.

## Conventions and the mode indexing

`Examples/BetaGamma` indexes fields by the `z`-exponent, with `beta n` an *annihilation*
operator for `n ≥ 0` and a *creation* operator for `n < 0`, and

  `beta m * gamma n - gamma n * beta m = δ_{m+n+1,0}`.

We keep that integer index and call it `bM m`, `gM m`.  In physicists' notation, where
`β(z) = Σ_{r ∈ ℤ+1/2} β_r z^{-r-1/2}` for a weight-`1/2` field,

  **`bM m = β_{m+1/2}`,  `gM m = γ_{m+1/2}`,**

so the relation above is `[β_r, γ_s] = δ_{r+s,0}` with `r = m+1/2`, `s = n+1/2`.  The
half-integrality of the moding is *carried by the ℤ-index shift*, and it is what puts the `1/2`s
into every weight formula below.

## The modes, and how the normalization is **derived**

For an arbitrary coefficient family `A : ℤ → ℂ` we set

  `LbgA A n = Σ_j A j · :bM j · gM (n-j-1):`   (`LbgA`, a locally finite `finsum`),

with the *bosonic* normal ordering (annihilators to the right — no sign, this is not a fermion).
The two brackets come out in closed form for **any** `A`:

  `LbgA_bracket_bM` : `[LbgA A n, bM k] = -A(n+k)·bM (n+k)`,
  `LbgA_bracket_gM` : `[LbgA A n, gM k] =  A(-k-1)·gM (n+k)`.

Demanding that `β` be primary of weight `h` — i.e. `[Lₙ, β_r] = ((h-1)n - r)β_{n+r}` with
`r = k+1/2` — therefore **forces** `A j = j + 1/2 - h·n` (`Acoef_forced`); demanding that `γ` be
primary of weight `h'` forces `A j = j + 1/2 + (h'-1)·n` (`Acoef_forced_gamma`).  Comparing the
two gives `h + h' = 1` (`weights_sum_one`) — the familiar statement that the `βγ` weights are
`(λ, 1-λ)`.  The symmetric point `h = h' = 1/2` is the case in which the `ℤ+1/2`-moded Fock
vacuum is the `SL(2)`-invariant one, and it is the case we carry through:

  `Acoef n j = j + 1/2 - n/2`,  `Lbg n = LbgA (Acoef n) n`.

The central charge is then **read off** from a single finite sum, `gateBG_sum`:

  `Xop m (-m)|0⟩ = -Σ_{j=-m}^{-1} (j + 1/2 + m/2)² |0⟩ = -(m³-m)/12 |0⟩`,

so `c·(m³-m)/12 = -(m³-m)/12`, i.e. **`c = -1`** (`centralCharge`, `Lbg_virasoro`).  This
agrees with the literature value for the `λ = 1/2` symplectic bosons.

### Remark on general `λ` (reported, not proved here)

Repeating the vacuum computation with `A j = j + 1/2 - λ·n` gives

  `Xop M (-M)|0⟩ = [-(λ(1-λ) - 1/6)M³ + M/12]|0⟩`,

whose `M³` coefficient matches `c/12` with `c = 2(6λ² - 6λ + 1)` (the standard `βγ` value, e.g.
`c = 11` at `λ = 3/2` for the superstring superghosts) but whose `M`-linear coefficient matches
`c = -1`.  The two agree exactly when `(2λ-1)² = 0`.  This is not a contradiction: the moding of
this Fock space is pinned at `ℤ + 1/2` by the construction, so for `λ ≠ 1/2` the normally-ordered
`L₀` differs from the true Virasoro `L₀` by the constant `(2λ-1)²/8`, and only at `λ = 1/2` does
the normal-ordering point coincide with the `SL(2)`-invariant vacuum.  Only `λ = 1/2` is
formalized below.

## Proof architecture (identical to `SymplecticFermionVirasoroB`, minus every sign)

1. `Lbg_bM_apply` / `Lbg_gM_apply` — the primary-of-weight-`1/2` brackets, one delta-gated
   `finsum` collapse each.
2. `Xop_comm_phiM` — hence `Xop m n := [Lₘ,Lₙ] - (m-n)L_{m+n}` commutes with every mode
   (Jacobi; the scalar identity is `wtBG_jacobi`).
3. `eq_smul_of_comm_of_vac` — an operator commuting with every `mulX` is determined by its value
   on `|0⟩ = 1`; here this is just `MvPolynomial.induction_on`, far cheaper than the Clifford
   spanning argument of the fermionic case.
4. `Lbg_ann_zero` + `Xop_vac_L0` — off the diagonal `m+n = 0` the defect kills the vacuum.
5. `gateBG_sum` — on the diagonal, one finite sum `Σ_{i<M} (M-2i-1)²/4 = (M³-M)/12`.

## References
* Kac, *VA for Beginners* §3.6; Friedan–Martinec–Shenker (1986) for the `(λ, 1-λ)` ghost systems;
  Arakawa–Kawasetsu, *Quasi-lisse vertex algebras and MLDEs* (2018) §5.
-/

namespace VOA.BGVir

open MvPolynomial VOA.BetaGamma

/-! ## §A  The mode operators, the CCR, and the vacuum

`bM m = β_{m+1/2}` and `gM m = γ_{m+1/2}`; creation for `m ≤ -1`, annihilation for `m ≥ 0`. -/

/-- The `β` modes.  In physicists' notation `bM m = β_{m+1/2}`. -/
noncomputable def bM (m : ℤ) : Module.End ℂ Fock := beta m

/-- The `γ` modes.  In physicists' notation `gM m = γ_{m+1/2}`. -/
noncomputable def gM (m : ℤ) : Module.End ℂ Fock := gamma m

/-- The vacuum of the polynomial Fock space. -/
noncomputable def vacBG : Fock := 1

theorem beta_nonneg {m : ℤ} (hm : 0 ≤ m) : beta m = der (Sum.inr m.toNat) := if_pos hm

theorem beta_neg {m : ℤ} (hm : m < 0) : beta m = mulX (Sum.inl (-m - 1).toNat) :=
  if_neg (by omega)

theorem gamma_nonneg {m : ℤ} (hm : 0 ≤ m) : gamma m = -der (Sum.inl m.toNat) := if_pos hm

theorem gamma_neg {m : ℤ} (hm : m < 0) : gamma m = mulX (Sum.inr (-m - 1).toNat) :=
  if_neg (by omega)

/-- **The `βγ` canonical commutation relation in mode form**: `[bM m, gM n] = δ_{m+n+1,0}`,
i.e. `[β_r, γ_s] = δ_{r+s,0}` with `r = m+1/2`, `s = n+1/2`. -/
theorem bM_gM_comm (m n : ℤ) (x : Fock) :
    bM m (gM n x) - gM n (bM m x) = (if m + n + 1 = 0 then (1 : ℂ) else 0) • x := by
  have h := LinearMap.congr_fun (beta_gamma_comm m n) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  change beta m (gamma n x) - gamma n (beta m x) = _
  rw [h]
  by_cases hmn : m + n + 1 = 0
  · rw [if_pos hmn, if_pos hmn]; simp
  · rw [if_neg hmn, if_neg hmn]; simp

/-- `β` commutes with itself — these are **bosons**. -/
theorem bM_bM_comm (m n : ℤ) (x : Fock) : bM m (bM n x) = bM n (bM m x) := by
  have h := LinearMap.congr_fun (beta_comm m n) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at h
  change beta m (beta n x) = beta n (beta m x)
  exact sub_eq_zero.mp h

/-- `γ` commutes with itself. -/
theorem gM_gM_comm (m n : ℤ) (x : Fock) : gM m (gM n x) = gM n (gM m x) := by
  have h := LinearMap.congr_fun (gamma_comm m n) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at h
  change gamma m (gamma n x) = gamma n (gamma m x)
  exact sub_eq_zero.mp h

/-- Nonnegative modes annihilate the vacuum: `β_r|0⟩ = 0` for `r ≥ 1/2`. -/
theorem bM_vac {m : ℤ} (hm : 0 ≤ m) : bM m vacBG = 0 := by
  rw [bM, beta_nonneg hm, vacBG]
  change pderiv (Sum.inr m.toNat) (1 : Fock) = 0
  simp

theorem gM_vac {m : ℤ} (hm : 0 ≤ m) : gM m vacBG = 0 := by
  rw [gM, gamma_nonneg hm, vacBG]
  change -(pderiv (Sum.inl m.toNat) (1 : Fock)) = 0
  simp

/-- The negative `β` modes are multiplication by the `inl` variables. -/
theorem bM_neg_eq_mulX (k : ℕ) : bM (-(k : ℤ) - 1) = mulX (Sum.inl k) := by
  rw [bM, beta_neg (by omega), show -(-(k : ℤ) - 1) - 1 = ((k : ℕ) : ℤ) from by ring,
    Int.toNat_natCast]

/-- The negative `γ` modes are multiplication by the `inr` variables. -/
theorem gM_neg_eq_mulX (k : ℕ) : gM (-(k : ℤ) - 1) = mulX (Sum.inr k) := by
  rw [gM, gamma_neg (by omega), show -(-(k : ℤ) - 1) - 1 = ((k : ℕ) : ℤ) from by ring,
    Int.toNat_natCast]

/-! ### Lower truncation

`β`, `γ` are *fields*: on a fixed polynomial all sufficiently high modes vanish, because a
polynomial involves only finitely many variables. -/

/-- A bound past which no variable of `x` occurs. -/
noncomputable def varBound (x : Fock) : ℕ := x.vars.sup (fun i => Sum.elim id id i + 1)

theorem notMem_vars_of_le {x : Fock} {i : ℕ ⊕ ℕ} (h : varBound x ≤ Sum.elim id id i) :
    i ∉ x.vars := by
  intro hm
  have hle : Sum.elim id id i + 1 ≤ varBound x :=
    Finset.le_sup (f := fun i : ℕ ⊕ ℕ => Sum.elim id id i + 1) hm
  omega

/-- **Lower truncation for `β`.** -/
theorem bM_high (x : Fock) : ∃ N : ℤ, ∀ m : ℤ, N ≤ m → bM m x = 0 := by
  refine ⟨(varBound x : ℤ), fun m hm => ?_⟩
  have hm0 : (0 : ℤ) ≤ m := le_trans (Int.natCast_nonneg _) hm
  rw [bM, beta_nonneg hm0]
  change pderiv (Sum.inr m.toNat) x = 0
  refine pderiv_eq_zero_of_notMem_vars (notMem_vars_of_le ?_)
  change varBound x ≤ m.toNat
  omega

/-- **Lower truncation for `γ`.** -/
theorem gM_high (x : Fock) : ∃ N : ℤ, ∀ m : ℤ, N ≤ m → gM m x = 0 := by
  refine ⟨(varBound x : ℤ), fun m hm => ?_⟩
  have hm0 : (0 : ℤ) ≤ m := le_trans (Int.natCast_nonneg _) hm
  rw [gM, gamma_nonneg hm0]
  change -(pderiv (Sum.inl m.toNat) x) = 0
  rw [pderiv_eq_zero_of_notMem_vars
    (notMem_vars_of_le (by change varBound x ≤ m.toNat; omega))]
  exact neg_zero

/-! ### Rigidity: an operator commuting with all creations is a scalar

The polynomial Fock space is generated from `|0⟩ = 1` by multiplication operators, so this is
just `MvPolynomial.induction_on`. -/

/-- **Rigidity.**  An operator commuting with every `mulX` is determined by its value on the
vacuum; if that value is `c·|0⟩` the operator is `c·id`. -/
theorem eq_smul_of_comm_of_vac (F : Module.End ℂ Fock) (c : ℂ)
    (hcomm : ∀ (i : ℕ ⊕ ℕ) (y : Fock), F (mulX i y) = mulX i (F y))
    (hvac : F vacBG = c • vacBG) : F = c • (1 : Module.End ℂ Fock) := by
  refine LinearMap.ext fun x => ?_
  induction x using MvPolynomial.induction_on with
  | C a =>
      have hCa : (C a : Fock) = a • vacBG := by rw [vacBG, smul_eq_C_mul, mul_one]
      rw [hCa, map_smul, hvac]
      simp only [LinearMap.smul_apply, Module.End.one_apply, map_smul, vacBG]
  | add p q hp hq =>
      rw [map_add, hp, hq]
      simp only [LinearMap.smul_apply, Module.End.one_apply, map_add]
  | mul_X p i hp =>
      have hcm : p * X i = mulX i p := by rw [mulX_apply]; ring
      rw [hcm, hcomm i p, hp]
      simp only [LinearMap.smul_apply, Module.End.one_apply, map_smul]

/-! ## §B  The Virasoro modes

`LbgA A n = Σ_j A j · :bM j · gM (n-j-1):` with **bosonic** normal ordering.  The two mode
indices sum to `n - 1`, i.e. `(j+1/2) + (n-j-1+1/2) = n`, so `Lₙ` lowers the `L₀`-weight by `n`
as it should. -/

/-- The normally ordered operator `:bM j · gM (n-j-1):` (annihilators to the right — no sign). -/
noncomputable def bgOp (n j : ℤ) : Module.End ℂ Fock :=
  if j < 0 then bM j * gM (n - j - 1) else gM (n - j - 1) * bM j

theorem bgOp_apply (n j : ℤ) (x : Fock) :
    bgOp n j x = if j < 0 then bM j (gM (n - j - 1) x) else gM (n - j - 1) (bM j x) := by
  rw [bgOp]
  split_ifs <;> simp only [Module.End.mul_apply]

/-- **Summability.**  For `j` large the right-hand factor is a high `β`-annihilation mode; for
`j` very negative the right-hand factor is a high `γ`-annihilation mode. -/
theorem bgOp_support_finite (n : ℤ) (x : Fock) :
    (Function.support fun j : ℤ => bgOp n j x).Finite := by
  obtain ⟨Mb, hb⟩ := bM_high x
  obtain ⟨Mg, hg⟩ := gM_high x
  apply Set.Finite.subset ((Set.finite_Icc (n - Mg) (-1)).union (Set.finite_Icc 0 (Mb - 1)))
  intro j hj
  rw [Function.mem_support] at hj
  by_cases hjneg : j < 0
  · have hlt : ¬ (Mg ≤ n - j - 1) := fun hle => hj (by
      rw [bgOp_apply, if_pos hjneg, hg (n - j - 1) hle, map_zero])
    exact Or.inl (Set.mem_Icc.mpr ⟨by omega, by omega⟩)
  · have hlt : ¬ (Mb ≤ j) := fun hle => hj (by
      rw [bgOp_apply, if_neg hjneg, hb j hle, map_zero])
    exact Or.inr (Set.mem_Icc.mpr ⟨by omega, by omega⟩)

theorem bgTerm_support_finite (A : ℤ → ℂ) (n : ℤ) (x : Fock) :
    (Function.support fun j : ℤ => A j • bgOp n j x).Finite := by
  apply (bgOp_support_finite n x).subset
  intro j hj
  rw [Function.mem_support] at hj ⊢
  intro h
  exact hj (by rw [h, smul_zero])

/-- **The Virasoro mode with an arbitrary coefficient family**, defined by its (finite) action on
each vector.  Keeping `A` general is what makes the normalization *derived* rather than assumed:
see `Acoef_forced`. -/
noncomputable def LbgA (A : ℤ → ℂ) (n : ℤ) : Module.End ℂ Fock where
  toFun x := ∑ᶠ j : ℤ, A j • bgOp n j x
  map_add' x y := by
    rw [← finsum_add_distrib (bgTerm_support_finite A n x) (bgTerm_support_finite A n y)]
    exact finsum_congr fun j => by rw [map_add, smul_add]
  map_smul' c x := by
    rw [RingHom.id_apply, smul_finsum' c (bgTerm_support_finite A n x)]
    exact finsum_congr fun j => by rw [map_smul, smul_comm]

theorem LbgA_apply (A : ℤ → ℂ) (n : ℤ) (x : Fock) :
    LbgA A n x = ∑ᶠ j : ℤ, A j • bgOp n j x := rfl

/-! ## §C  The brackets `[LbgA A n, bM k]` and `[LbgA A n, gM k]`

The normal-ordering constant is central, so it drops out of any bracket; what remains is a single
`δ`-gated term. -/

/-- Reordering the two factors of `bgOp` costs only a **central** scalar, so its bracket with any
operator equals the bracket of the plain product `bM j · gM (n-j-1)`. -/
theorem bgOp_bracket_eq (n j : ℤ) (P : Module.End ℂ Fock) (x : Fock) :
    bgOp n j (P x) - P (bgOp n j x)
      = bM j (gM (n - j - 1) (P x)) - P (bM j (gM (n - j - 1) x)) := by
  by_cases hj : j < 0
  · rw [bgOp_apply, bgOp_apply, if_pos hj, if_pos hj]
  · have key : ∀ y : Fock, gM (n - j - 1) (bM j y)
        = bM j (gM (n - j - 1) y) - (if n = 0 then (1 : ℂ) else 0) • y := by
      intro y
      have h := bM_gM_comm j (n - j - 1) y
      rw [show j + (n - j - 1) + 1 = n from by ring] at h
      rw [← h]
      abel
    rw [bgOp_apply, bgOp_apply, if_neg hj, if_neg hj, key, key, map_sub, map_smul]
    abel

/-- The per-term bracket with a `β` mode: `[bM j gM s, bM k] = bM j [gM s, bM k]`. -/
theorem bgOp_bracket_bM (n j k : ℤ) (x : Fock) :
    bgOp n j (bM k x) - bM k (bgOp n j x)
      = (if n - j + k = 0 then (-1 : ℂ) else 0) • bM j x := by
  rw [bgOp_bracket_eq n j (bM k) x]
  have hswap : gM (n - j - 1) (bM k x)
      = bM k (gM (n - j - 1) x) - (if n - j + k = 0 then (1 : ℂ) else 0) • x := by
    have h := bM_gM_comm k (n - j - 1) x
    rw [show k + (n - j - 1) + 1 = n - j + k from by ring] at h
    rw [← h]
    abel
  rw [hswap, map_sub, map_smul, bM_bM_comm j k]
  by_cases hc : n - j + k = 0
  · rw [if_pos hc, if_pos hc]; module
  · rw [if_neg hc, if_neg hc]; module

/-- The per-term bracket with a `γ` mode: `[bM j gM s, gM k] = [bM j, gM k] gM s`. -/
theorem bgOp_bracket_gM (n j k : ℤ) (x : Fock) :
    bgOp n j (gM k x) - gM k (bgOp n j x)
      = (if j + k + 1 = 0 then (1 : ℂ) else 0) • gM (n - j - 1) x := by
  rw [bgOp_bracket_eq n j (gM k) x, gM_gM_comm (n - j - 1) k x]
  exact bM_gM_comm j k (gM (n - j - 1) x)

/-- **`[LbgA A n, bM k] = -A(n+k)·bM (n+k)`** — valid for *every* coefficient family `A`. -/
theorem LbgA_bracket_bM (A : ℤ → ℂ) (n k : ℤ) (x : Fock) :
    LbgA A n (bM k x) - bM k (LbgA A n x) = (-(A (n + k))) • bM (n + k) x := by
  classical
  have hs : (Function.support fun j : ℤ =>
      A j • (if n - j + k = 0 then (-1 : ℂ) else 0) • bM j x).Finite := by
    apply Set.Finite.subset (Set.finite_singleton (n + k))
    intro j hj
    rw [Function.mem_support] at hj
    rw [Set.mem_singleton_iff]
    by_contra hne
    exact hj (by rw [if_neg (by omega : ¬ (n - j + k = 0)), zero_smul, smul_zero])
  have hfin2 : (Function.support fun j : ℤ => bM k (A j • bgOp n j x)).Finite := by
    apply (bgTerm_support_finite A n x).subset
    intro j hj
    rw [Function.mem_support] at hj ⊢
    intro h
    exact hj (by rw [h, map_zero])
  have hL : LbgA A n (bM k x) - bM k (LbgA A n x)
      = ∑ᶠ j : ℤ, (A j • bgOp n j (bM k x) - bM k (A j • bgOp n j x)) := by
    rw [finsum_sub_distrib (bgTerm_support_finite A n (bM k x)) hfin2]
    congr 1
    change bM k (∑ᶠ j : ℤ, A j • bgOp n j x) = _
    exact map_finsum (bM k) (bgTerm_support_finite A n x)
  have hterm : ∀ j : ℤ, A j • bgOp n j (bM k x) - bM k (A j • bgOp n j x)
      = A j • (if n - j + k = 0 then (-1 : ℂ) else 0) • bM j x := by
    intro j
    rw [map_smul, ← smul_sub, bgOp_bracket_bM n j k x]
  rw [hL, finsum_congr hterm, finsum_eq_single _ (n + k)
    (fun j hj => by rw [if_neg (by omega : ¬ (n - j + k = 0)), zero_smul, smul_zero]),
    if_pos (by omega : n - (n + k) + k = 0)]
  module

/-- **`[LbgA A n, gM k] = A(-k-1)·gM (n+k)`** — valid for *every* coefficient family `A`. -/
theorem LbgA_bracket_gM (A : ℤ → ℂ) (n k : ℤ) (x : Fock) :
    LbgA A n (gM k x) - gM k (LbgA A n x) = (A (-k - 1)) • gM (n + k) x := by
  classical
  have hs : (Function.support fun j : ℤ =>
      A j • (if j + k + 1 = 0 then (1 : ℂ) else 0) • gM (n - j - 1) x).Finite := by
    apply Set.Finite.subset (Set.finite_singleton (-k - 1))
    intro j hj
    rw [Function.mem_support] at hj
    rw [Set.mem_singleton_iff]
    by_contra hne
    exact hj (by rw [if_neg (by omega : ¬ (j + k + 1 = 0)), zero_smul, smul_zero])
  have hfin2 : (Function.support fun j : ℤ => gM k (A j • bgOp n j x)).Finite := by
    apply (bgTerm_support_finite A n x).subset
    intro j hj
    rw [Function.mem_support] at hj ⊢
    intro h
    exact hj (by rw [h, map_zero])
  have hL : LbgA A n (gM k x) - gM k (LbgA A n x)
      = ∑ᶠ j : ℤ, (A j • bgOp n j (gM k x) - gM k (A j • bgOp n j x)) := by
    rw [finsum_sub_distrib (bgTerm_support_finite A n (gM k x)) hfin2]
    congr 1
    change gM k (∑ᶠ j : ℤ, A j • bgOp n j x) = _
    exact map_finsum (gM k) (bgTerm_support_finite A n x)
  have hterm : ∀ j : ℤ, A j • bgOp n j (gM k x) - gM k (A j • bgOp n j x)
      = A j • (if j + k + 1 = 0 then (1 : ℂ) else 0) • gM (n - j - 1) x := by
    intro j
    rw [map_smul, ← smul_sub, bgOp_bracket_gM n j k x]
  rw [hL, finsum_congr hterm, finsum_eq_single _ (-k - 1)
    (fun j hj => by rw [if_neg (by omega : ¬ (j + k + 1 = 0)), zero_smul, smul_zero]),
    if_pos (by omega : -k - 1 + k + 1 = 0), show n - (-k - 1) - 1 = n + k from by ring]
  module

/-! ## §D  Deriving the normalization

`bM j ≠ 0` for every `j`, so the two bracket formulas of §C pin `A` uniquely once a conformal
weight is demanded. -/

theorem bM_ne_zero (j : ℤ) : ∃ x : Fock, bM j x ≠ 0 := by
  by_cases hj : j < 0
  · refine ⟨vacBG, ?_⟩
    rw [show j = -((-j - 1).toNat : ℤ) - 1 from by omega, bM_neg_eq_mulX, mulX_apply, vacBG,
      mul_one]
    exact X_ne_zero _
  · refine ⟨X (Sum.inr j.toNat), ?_⟩
    rw [bM, beta_nonneg (by omega)]
    change pderiv (Sum.inr j.toNat) (X (Sum.inr j.toNat) : Fock) ≠ 0
    rw [pderiv_X_self]
    exact one_ne_zero

theorem gM_ne_zero (j : ℤ) : ∃ x : Fock, gM j x ≠ 0 := by
  by_cases hj : j < 0
  · refine ⟨vacBG, ?_⟩
    rw [show j = -((-j - 1).toNat : ℤ) - 1 from by omega, gM_neg_eq_mulX, mulX_apply, vacBG,
      mul_one]
    exact X_ne_zero _
  · refine ⟨X (Sum.inl j.toNat), ?_⟩
    rw [gM, gamma_nonneg (by omega)]
    change -(pderiv (Sum.inl j.toNat) (X (Sum.inl j.toNat) : Fock)) ≠ 0
    rw [pderiv_X_self]
    exact neg_ne_zero.mpr one_ne_zero

theorem smul_eq_smul_of_ne_zero {c d : ℂ} {v : Fock} (hv : v ≠ 0) (h : c • v = d • v) : c = d := by
  have h0 : (c - d) • v = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h0 with h1 | h1
  · exact sub_eq_zero.mp h1
  · exact absurd h1 hv

/-- **The `β`-side derivation.**  Demanding that `β` be primary of conformal weight `h`,
`[Lₙ, β_r] = ((h-1)n - r)β_{n+r}` with `r = k + 1/2`, **forces** `A j = j + 1/2 - h·n`. -/
theorem Acoef_forced (A : ℤ → ℂ) (n : ℤ) (h : ℂ)
    (hprim : ∀ (k : ℤ) (x : Fock), LbgA A n (bM k x) - bM k (LbgA A n x)
        = ((h - 1) * (n : ℂ) - (k : ℂ) - 1 / 2) • bM (n + k) x) :
    ∀ j : ℤ, A j = (j : ℂ) + 1 / 2 - h * (n : ℂ) := by
  intro j
  obtain ⟨x, hx⟩ := bM_ne_zero j
  have hk := hprim (j - n) x
  rw [LbgA_bracket_bM, show n + (j - n) = j from by ring] at hk
  have hs := smul_eq_smul_of_ne_zero hx hk
  have : A j = -((h - 1) * (n : ℂ) - ((j - n : ℤ) : ℂ) - 1 / 2) := by
    rw [← hs]; ring
  rw [this]
  push_cast
  ring

/-- **The `γ`-side derivation.**  Demanding that `γ` be primary of conformal weight `h'`
**forces** `A j = j + 1/2 + (h'-1)·n`. -/
theorem Acoef_forced_gamma (A : ℤ → ℂ) (n : ℤ) (h' : ℂ)
    (hprim : ∀ (k : ℤ) (x : Fock), LbgA A n (gM k x) - gM k (LbgA A n x)
        = ((h' - 1) * (n : ℂ) - (k : ℂ) - 1 / 2) • gM (n + k) x) :
    ∀ j : ℤ, A j = (j : ℂ) + 1 / 2 + (h' - 1) * (n : ℂ) := by
  intro j
  obtain ⟨x, hx⟩ := gM_ne_zero (n + (-j - 1))
  have hk := hprim (-j - 1) x
  rw [LbgA_bracket_gM, show -(-j - 1) - 1 = j from by ring] at hk
  have hs := smul_eq_smul_of_ne_zero hx hk
  rw [hs]
  push_cast
  ring

/-- **`h + h' = 1`.**  If the *same* normally ordered bilinear makes `β` primary of weight `h`
and `γ` primary of weight `h'` (at any `n ≠ 0`), the two weights are complementary — the
classical statement that the `βγ` weights are `(λ, 1-λ)`.  The symmetric point is `h = h' = 1/2`,
formalized below. -/
theorem weights_sum_one (A : ℤ → ℂ) (n : ℤ) (hn : n ≠ 0) (h h' : ℂ)
    (hb : ∀ (k : ℤ) (x : Fock), LbgA A n (bM k x) - bM k (LbgA A n x)
        = ((h - 1) * (n : ℂ) - (k : ℂ) - 1 / 2) • bM (n + k) x)
    (hg : ∀ (k : ℤ) (x : Fock), LbgA A n (gM k x) - gM k (LbgA A n x)
        = ((h' - 1) * (n : ℂ) - (k : ℂ) - 1 / 2) • gM (n + k) x) :
    h + h' = 1 := by
  have e1 := Acoef_forced A n h hb 0
  have e2 := Acoef_forced_gamma A n h' hg 0
  have hnc : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have he : ((0 : ℤ) : ℂ) + 1 / 2 - h * (n : ℂ)
      = ((0 : ℤ) : ℂ) + 1 / 2 + (h' - 1) * (n : ℂ) := e1.symm.trans e2
  have hkey : (h + h' - 1) * (n : ℂ) = 0 := by
    have hd : (h + h' - 1) * (n : ℂ)
        = -((((0 : ℤ) : ℂ) + 1 / 2 - h * (n : ℂ))
            - (((0 : ℤ) : ℂ) + 1 / 2 + (h' - 1) * (n : ℂ))) := by ring
    rw [hd, he, sub_self, neg_zero]
  rcases mul_eq_zero.mp hkey with hz | hz
  · exact sub_eq_zero.mp hz
  · exact absurd hz hnc

/-! ## §E  The weight-`1/2` modes `Lₙ` -/

/-- The coefficient family for the symmetric point `λ = 1/2`: `A j = j + 1/2 - n/2`. -/
noncomputable def Acoef (n : ℤ) (j : ℤ) : ℂ := (j : ℂ) + 1 / 2 - (n : ℂ) / 2

/-- **The Virasoro modes of the `βγ` system**, `Lₙ = Σ_j (j + 1/2 - n/2) :bM j · gM (n-j-1):`.
The coefficient is forced by `Acoef_forced` at `h = 1/2`. -/
noncomputable def Lbg (n : ℤ) : Module.End ℂ Fock := LbgA (Acoef n) n

/-- The weight-`1/2` primary factor: `[Lₙ, φ_r] = (-n/2 - r)φ_{n+r}` with `r = k + 1/2`. -/
noncomputable def wtBG (n k : ℤ) : ℂ := -(n : ℂ) / 2 - (k : ℂ) - 1 / 2

theorem Lbg_apply (n : ℤ) (x : Fock) : Lbg n x = ∑ᶠ j : ℤ, Acoef n j • bgOp n j x := rfl

/-- **`β` is primary of conformal weight `1/2`**: `[Lₙ, β_r] = (-n/2 - r)β_{n+r}`. -/
theorem Lbg_bM_apply (n k : ℤ) (x : Fock) :
    Lbg n (bM k x) = bM k (Lbg n x) + wtBG n k • bM (n + k) x := by
  simp only [Lbg]
  have h := LbgA_bracket_bM (Acoef n) n k x
  have hc : -(Acoef n (n + k)) = wtBG n k := by
    simp only [Acoef, wtBG]; push_cast; ring
  rw [hc, sub_eq_iff_eq_add] at h
  rw [h, add_comm]

/-- **`γ` is primary of conformal weight `1/2`**: `[Lₙ, γ_r] = (-n/2 - r)γ_{n+r}`. -/
theorem Lbg_gM_apply (n k : ℤ) (x : Fock) :
    Lbg n (gM k x) = gM k (Lbg n x) + wtBG n k • gM (n + k) x := by
  simp only [Lbg]
  have h := LbgA_bracket_gM (Acoef n) n k x
  have hc : Acoef n (-k - 1) = wtBG n k := by
    simp only [Acoef, wtBG]; push_cast; ring
  rw [hc, sub_eq_iff_eq_add] at h
  rw [h, add_comm]

/-- **The weight-`1/2` primary condition, literally.**  For a primary field `φ` of conformal
weight `h`, `[Lₙ, φ_r] = ((h-1)n - r)φ_{n+r}`.  Here `h = 1/2` and `r = k + 1/2`, both written
out: this is the statement in which the half-integer weight and the half-integer mode index are
visible as such. -/
theorem Lbg_bM_primary (n k : ℤ) (x : Fock) :
    Lbg n (bM k x) - bM k (Lbg n x)
      = (((1 : ℂ) / 2 - 1) * (n : ℂ) - ((k : ℂ) + 1 / 2)) • bM (n + k) x := by
  rw [Lbg_bM_apply n k x]
  simp only [wtBG]
  module

/-- The `γ` half: `γ` too is primary of weight `1/2`, with modes in `ℤ + 1/2`. -/
theorem Lbg_gM_primary (n k : ℤ) (x : Fock) :
    Lbg n (gM k x) - gM k (Lbg n x)
      = (((1 : ℂ) / 2 - 1) * (n : ℂ) - ((k : ℂ) + 1 / 2)) • gM (n + k) x := by
  rw [Lbg_gM_apply n k x]
  simp only [wtBG]
  module

/-- Both fields packaged as one family, so the Jacobi computation is done once. -/
noncomputable def phiM (a : Fin 2) (m : ℤ) : Module.End ℂ Fock := if a = 0 then bM m else gM m

@[simp] theorem phiM_zero (m : ℤ) : phiM 0 m = bM m := if_pos rfl

@[simp] theorem phiM_one (m : ℤ) : phiM 1 m = gM m := if_neg (by decide)

theorem Lbg_phiM_apply (n : ℤ) (a : Fin 2) (k : ℤ) (x : Fock) :
    Lbg n (phiM a k x) = phiM a k (Lbg n x) + wtBG n k • phiM a (n + k) x := by
  simp only [phiM]
  split_ifs
  · exact Lbg_bM_apply n k x
  · exact Lbg_gM_apply n k x

theorem phiM_vac {a : Fin 2} {m : ℤ} (hm : 0 ≤ m) : phiM a m vacBG = 0 := by
  simp only [phiM]
  split_ifs
  · exact bM_vac hm
  · exact gM_vac hm

/-! ## §F  Vacuum relations -/

theorem bgOp_vac_of_nonneg (n j : ℤ) (hj : 0 ≤ j) : bgOp n j vacBG = 0 := by
  rw [bgOp_apply, if_neg (by omega), bM_vac hj, map_zero]

/-- `Lₙ|0⟩ = 0` for `n ≥ -1`.  At `n = -1` the exceptional term `j = -1` is killed not by the
normal ordering but by the *coefficient* `Acoef (-1) (-1) = 0` — the half-integer moding at
work. -/
theorem Lbg_vacuum {n : ℤ} (hn : -1 ≤ n) : Lbg n vacBG = 0 := by
  have h : ∀ j : ℤ, Acoef n j • bgOp n j vacBG = 0 := by
    intro j
    by_cases hj : j < 0
    · by_cases hs : (0 : ℤ) ≤ n - j - 1
      · rw [bgOp_apply, if_pos hj, gM_vac hs, map_zero, smul_zero]
      · have hj1 : j = -1 := by omega
        have hn1 : n = -1 := by omega
        have hz : Acoef n j = 0 := by rw [Acoef, hj1, hn1]; push_cast; ring
        rw [hz, zero_smul]
    · rw [bgOp_vac_of_nonneg n j (by omega), smul_zero]
  rw [Lbg_apply]
  exact (finsum_congr h).trans finsum_zero

/-- **`L_p` kills anything killed by all annihilation modes** (`p ≥ 0`): every term of `L_p` has
an annihilation mode on the right. -/
theorem Lbg_ann_zero (y : Fock) (hb : ∀ k : ℤ, 0 ≤ k → bM k y = 0)
    (hg : ∀ k : ℤ, 0 ≤ k → gM k y = 0) {p : ℤ} (hp : 0 ≤ p) : Lbg p y = 0 := by
  have h : ∀ j : ℤ, Acoef p j • bgOp p j y = 0 := by
    intro j
    by_cases hj : j < 0
    · rw [bgOp_apply, if_pos hj, hg (p - j - 1) (by omega), map_zero, smul_zero]
    · rw [bgOp_apply, if_neg hj, hb j (by omega), map_zero, smul_zero]
  rw [Lbg_apply]
  exact (finsum_congr h).trans finsum_zero

/-- The `L₀`-weight of `L_p|0⟩` is `-p`, proved term by term. -/
theorem Lbg_zero_Lbg_vac (p : ℤ) : Lbg 0 (Lbg p vacBG) = (-(p : ℂ)) • Lbg p vacBG := by
  have hfin := bgTerm_support_finite (Acoef p) p vacBG
  have h2 : ∀ j : ℤ, Lbg 0 (Acoef p j • bgOp p j vacBG)
      = (-(p : ℂ)) • (Acoef p j • bgOp p j vacBG) := by
    intro j
    by_cases hj : j < 0
    · have hy : Lbg 0 (gM (p - j - 1) vacBG) = wtBG 0 (p - j - 1) • gM (p - j - 1) vacBG := by
        rw [Lbg_gM_apply 0 (p - j - 1) vacBG, Lbg_vacuum (by norm_num : (-1 : ℤ) ≤ 0), map_zero,
          show (0 : ℤ) + (p - j - 1) = p - j - 1 from by ring, zero_add]
      rw [bgOp_apply, if_pos hj, map_smul, Lbg_bM_apply 0 j (gM (p - j - 1) vacBG), hy,
        show (0 : ℤ) + j = j from by ring, map_smul]
      simp only [wtBG]
      push_cast
      module
    · rw [bgOp_vac_of_nonneg p j (by omega), smul_zero, map_zero, smul_zero]
  have h1 : Lbg 0 (Lbg p vacBG) = ∑ᶠ j : ℤ, Lbg 0 (Acoef p j • bgOp p j vacBG) := by
    change Lbg 0 (∑ᶠ j : ℤ, Acoef p j • bgOp p j vacBG) = _
    exact map_finsum (Lbg 0) hfin
  rw [h1, finsum_congr h2, ← smul_finsum' (-(p : ℂ)) hfin, Lbg_apply]

/-! ## §G  Half-integer conformal weights

The `L₀`-eigenvalue of `β_{-k-1/2}|0⟩` is `k + 1/2`: a genuinely non-integral conformal weight,
carried by an **even** (bosonic) vector. -/

/-- `L₀ (β_{-k-1/2}|0⟩) = (k + 1/2)·β_{-k-1/2}|0⟩` — a **half-integer** conformal weight. -/
theorem Lbg_zero_bM_creation (k : ℕ) :
    Lbg 0 (bM (-(k : ℤ) - 1) vacBG) = ((k : ℂ) + 1 / 2) • bM (-(k : ℤ) - 1) vacBG := by
  rw [Lbg_bM_apply 0 (-(k : ℤ) - 1) vacBG, Lbg_vacuum (by norm_num : (-1 : ℤ) ≤ 0), map_zero,
    show (0 : ℤ) + (-(k : ℤ) - 1) = -(k : ℤ) - 1 from by ring, zero_add]
  congr 1
  simp only [wtBG]
  push_cast
  ring

/-- `L₀ (γ_{-k-1/2}|0⟩) = (k + 1/2)·γ_{-k-1/2}|0⟩`. -/
theorem Lbg_zero_gM_creation (k : ℕ) :
    Lbg 0 (gM (-(k : ℤ) - 1) vacBG) = ((k : ℂ) + 1 / 2) • gM (-(k : ℤ) - 1) vacBG := by
  rw [Lbg_gM_apply 0 (-(k : ℤ) - 1) vacBG, Lbg_vacuum (by norm_num : (-1 : ℤ) ≤ 0), map_zero,
    show (0 : ℤ) + (-(k : ℤ) - 1) = -(k : ℤ) - 1 from by ring, zero_add]
  congr 1
  simp only [wtBG]
  push_cast
  ring

/-- The vacuum is nonzero. -/
theorem vacBG_ne_zero : (vacBG : Fock) ≠ 0 := one_ne_zero

/-- **The witness vector.**  `β_{-1/2}|0⟩ = X₍ᵢₙₗ ₀₎ ≠ 0` has `L₀`-eigenvalue exactly `1/2`. -/
theorem Lbg_zero_bM_neg_one :
    Lbg 0 (bM (-1) vacBG) = (1 / 2 : ℂ) • bM (-1) vacBG := by
  have h := Lbg_zero_bM_creation 0
  rw [show -((0 : ℕ) : ℤ) - 1 = (-1 : ℤ) from by norm_num] at h
  rw [h]
  congr 1
  push_cast
  ring

theorem bM_neg_one_vac_eq : bM (-1) vacBG = X (Sum.inl 0) := by
  rw [show (-1 : ℤ) = -((0 : ℕ) : ℤ) - 1 from by norm_num, bM_neg_eq_mulX, mulX_apply, vacBG,
    mul_one]

theorem bM_neg_one_vac_ne_zero : bM (-1) vacBG ≠ 0 := by
  rw [bM_neg_one_vac_eq]
  exact X_ne_zero _

/-! ## §H  The defect operator `Xop` and its rigidity -/

/-- `Xop m n = [Lₘ, Lₙ] - (m-n)L_{m+n}`: the operator the Virasoro relation claims is central. -/
noncomputable def Xop (m n : ℤ) : Module.End ℂ Fock :=
  Lbg m * Lbg n - Lbg n * Lbg m - ((m : ℂ) - (n : ℂ)) • Lbg (m + n)

theorem Xop_apply (m n : ℤ) (x : Fock) :
    Xop m n x = Lbg m (Lbg n x) - Lbg n (Lbg m x) - ((m : ℂ) - (n : ℂ)) • Lbg (m + n) x := by
  rw [Xop]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply]

theorem Xop_antisymm (m n : ℤ) : Xop m n = - Xop n m := by
  rw [Xop, Xop, show n + m = m + n from by ring]
  module

/-- The scalar Jacobi identity behind `Xop_comm_phiM`, for weight `1/2`. -/
theorem wtBG_jacobi (m n k : ℤ) :
    wtBG n k * wtBG m (n + k)
      = wtBG m k * wtBG n (m + k) + ((m : ℂ) - (n : ℂ)) * wtBG (m + n) k := by
  simp only [wtBG]
  push_cast
  ring

/-- **`Xop` commutes with every mode.**  The Jacobi identity written out; the scalar
cancellation is `wtBG_jacobi`. -/
theorem Xop_comm_phiM (m n : ℤ) (a : Fin 2) (k : ℤ) (x : Fock) :
    Xop m n (phiM a k x) = phiM a k (Xop m n x) := by
  have e1 : Lbg m (Lbg n (phiM a k x))
      = phiM a k (Lbg m (Lbg n x)) + wtBG m k • phiM a (m + k) (Lbg n x)
        + wtBG n k • phiM a (n + k) (Lbg m x)
        + (wtBG m k * wtBG n (m + k) + ((m : ℂ) - (n : ℂ)) * wtBG (m + n) k)
            • phiM a (m + n + k) x := by
    rw [Lbg_phiM_apply n a k x, map_add, map_smul, Lbg_phiM_apply m a k (Lbg n x),
      Lbg_phiM_apply m a (n + k) x, show m + (n + k) = m + n + k from by ring, ← wtBG_jacobi]
    module
  have e2 : Lbg n (Lbg m (phiM a k x))
      = phiM a k (Lbg n (Lbg m x)) + wtBG n k • phiM a (n + k) (Lbg m x)
        + wtBG m k • phiM a (m + k) (Lbg n x)
        + (wtBG m k * wtBG n (m + k)) • phiM a (m + n + k) x := by
    rw [Lbg_phiM_apply m a k x, map_add, map_smul, Lbg_phiM_apply n a k (Lbg m x),
      Lbg_phiM_apply n a (m + k) x, show n + (m + k) = m + n + k from by ring]
    module
  have e3 : Lbg (m + n) (phiM a k x)
      = phiM a k (Lbg (m + n) x) + wtBG (m + n) k • phiM a (m + n + k) x := by
    rw [Lbg_phiM_apply (m + n) a k x, show m + n + k = m + n + k from rfl]
  rw [Xop_apply, Xop_apply, e1, e2, e3, map_sub, map_sub, map_smul]
  module

theorem Xop_comm_mulX (m n : ℤ) (i : ℕ ⊕ ℕ) (y : Fock) :
    Xop m n (mulX i y) = mulX i (Xop m n y) := by
  cases i with
  | inl k =>
      rw [← bM_neg_eq_mulX k, ← phiM_zero (-(k : ℤ) - 1)]
      exact Xop_comm_phiM m n 0 (-(k : ℤ) - 1) y
  | inr k =>
      rw [← gM_neg_eq_mulX k, ← phiM_one (-(k : ℤ) - 1)]
      exact Xop_comm_phiM m n 1 (-(k : ℤ) - 1) y

/-! ## §I  `[L₀, L_p] = -p·L_p`, and the vanishing of the defect off the diagonal -/

theorem Xop_zero_left (p : ℤ) : Xop 0 p = 0 := by
  have h : Xop 0 p = (0 : ℂ) • (1 : Module.End ℂ Fock) := by
    refine eq_smul_of_comm_of_vac _ _ (Xop_comm_mulX 0 p) ?_
    rw [Xop_apply, Lbg_vacuum (by norm_num : (-1 : ℤ) ≤ 0), map_zero,
      show (0 : ℤ) + p = p from by ring, Lbg_zero_Lbg_vac p]
    push_cast
    module
  rw [h, zero_smul]

theorem Lbg_zero_comm_apply (p : ℤ) (y : Fock) :
    Lbg 0 (Lbg p y) = Lbg p (Lbg 0 y) - (p : ℂ) • Lbg p y := by
  have h := LinearMap.congr_fun (Xop_zero_left p) y
  rw [Xop_apply, show (0 : ℤ) + p = p from by ring] at h
  simp only [LinearMap.zero_apply] at h
  push_cast at h
  rw [sub_eq_zero, sub_eq_iff_eq_add] at h
  rw [h]
  module

theorem Xop_vac_L0 (m n : ℤ) :
    Lbg 0 (Xop m n vacBG) = (-((m : ℂ) + (n : ℂ))) • Xop m n vacBG := by
  have ha : Lbg 0 (Lbg m (Lbg n vacBG)) = (-((m : ℂ) + (n : ℂ))) • Lbg m (Lbg n vacBG) := by
    rw [Lbg_zero_comm_apply m (Lbg n vacBG), Lbg_zero_Lbg_vac n, map_smul]
    module
  have hb : Lbg 0 (Lbg n (Lbg m vacBG)) = (-((m : ℂ) + (n : ℂ))) • Lbg n (Lbg m vacBG) := by
    rw [Lbg_zero_comm_apply n (Lbg m vacBG), Lbg_zero_Lbg_vac m, map_smul]
    module
  have hc : Lbg 0 (Lbg (m + n) vacBG) = (-((m : ℂ) + (n : ℂ))) • Lbg (m + n) vacBG := by
    rw [Lbg_zero_Lbg_vac (m + n)]
    congr 1
    push_cast
    ring
  rw [Xop_apply, map_sub, map_sub, map_smul, ha, hb, hc]
  module

/-- **Off the diagonal the defect kills the vacuum.** -/
theorem Xop_vac_zero {m n : ℤ} (h : m + n ≠ 0) : Xop m n vacBG = 0 := by
  have hannb : ∀ k : ℤ, 0 ≤ k → bM k (Xop m n vacBG) = 0 := by
    intro k hk
    rw [← phiM_zero k, ← Xop_comm_phiM, phiM_vac hk, map_zero]
  have hanng : ∀ k : ℤ, 0 ≤ k → gM k (Xop m n vacBG) = 0 := by
    intro k hk
    rw [← phiM_one k, ← Xop_comm_phiM, phiM_vac hk, map_zero]
  have h1 : Lbg 0 (Xop m n vacBG) = 0 := Lbg_ann_zero _ hannb hanng (le_refl 0)
  have h2 := Xop_vac_L0 m n
  rw [h1] at h2
  have hc : ((m : ℂ) + (n : ℂ)) ≠ 0 := by
    have hz : ((m + n : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr h
    push_cast at hz
    exact hz
  rcases smul_eq_zero.mp h2.symm with h3 | h3
  · exact absurd (neg_eq_zero.mp h3) hc
  · exact h3

/-! ## §J  The central term: one finite sum, and `c = -1`

`Xop M (-M)|0⟩ = L_M(L_{-M}|0⟩)`, and `L_M` acting on `bM j · gM (-M-j-1)|0⟩` produces
`-(j + 1/2 + M/2)²|0⟩` by two applications of the primary bracket and one contraction.  Summing
`Σ_{j=-M}^{-1} (j + 1/2 + M/2)² = (M³-M)/12` gives `c = -1`. -/

theorem sumId (N : ℕ) : ∑ i ∈ Finset.range N, (i : ℂ) = (N : ℂ) * ((N : ℂ) - 1) / 2 := by
  induction N with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem sumSq (N : ℕ) :
    ∑ i ∈ Finset.range N, (i : ℂ) ^ 2 = (N : ℂ) * ((N : ℂ) - 1) * (2 * (N : ℂ) - 1) / 6 := by
  induction N with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- `Σ_{i<N} (N - 2i - 1)² = (N³-N)/3`: the arithmetic behind `c = -1`. -/
theorem quadSumBG (N : ℕ) :
    ∑ i ∈ Finset.range N, ((N : ℂ) - 2 * (i : ℂ) - 1) ^ 2 = ((N : ℂ) ^ 3 - (N : ℂ)) / 3 := by
  have expand : ∀ i ∈ Finset.range N,
      ((N : ℂ) - 2 * (i : ℂ) - 1) ^ 2
        = 4 * (i : ℂ) ^ 2 + ((-(4 : ℂ)) * ((N : ℂ) - 1)) * (i : ℂ) + ((N : ℂ) - 1) ^ 2 := by
    intro i _; ring
  rw [Finset.sum_congr rfl expand, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, sumSq, sumId, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  ring

/-- The one contraction of the whole file: for `-M ≤ j ≤ -1`, `bM (M+j) gM (-M-j-1)|0⟩ = |0⟩`. -/
theorem bM_gM_pair_vac {M j : ℤ} (_hM : 0 ≤ M) (hjM : -M ≤ j) (_hj : j < 0) :
    bM (M + j) (gM (-M - j - 1) vacBG) = vacBG := by
  have h := bM_gM_comm (M + j) (-M - j - 1) vacBG
  rw [show M + j + (-M - j - 1) + 1 = 0 from by ring, if_pos rfl, one_smul,
    bM_vac (by omega : (0 : ℤ) ≤ M + j), map_zero, sub_zero] at h
  exact h

/-- The coefficient family whose sum is the central charge. -/
noncomputable def gateBG (M : ℕ) (j : ℤ) : ℂ :=
  if -(M : ℤ) ≤ j ∧ j < 0 then -(((j : ℂ) + 1 / 2 + (M : ℂ) / 2)) ^ 2 else 0

/-- `L_M` applied to the `j`-th term of `L_{-M}|0⟩`, term by term. -/
theorem Lbg_bgTerm_vac (M : ℕ) (j : ℤ) :
    Lbg (M : ℤ) (Acoef (-(M : ℤ)) j • bgOp (-(M : ℤ)) j vacBG) = gateBG M j • vacBG := by
  by_cases hj : j < 0
  · by_cases hk : -(M : ℤ) ≤ j
    · have hy : Lbg (M : ℤ) (gM (-(M : ℤ) - j - 1) vacBG) = 0 := by
        rw [Lbg_gM_apply (M : ℤ) (-(M : ℤ) - j - 1) vacBG,
          Lbg_vacuum (by omega : (-1 : ℤ) ≤ (M : ℤ)), map_zero,
          show (M : ℤ) + (-(M : ℤ) - j - 1) = -j - 1 from by ring,
          gM_vac (by omega : (0 : ℤ) ≤ -j - 1), smul_zero, zero_add]
      rw [bgOp_apply, if_pos hj, map_smul,
        Lbg_bM_apply (M : ℤ) j (gM (-(M : ℤ) - j - 1) vacBG), hy, map_zero, zero_add,
        bM_gM_pair_vac (by omega : (0 : ℤ) ≤ (M : ℤ)) hk hj, gateBG, if_pos ⟨hk, hj⟩,
        Acoef, wtBG, smul_smul]
      congr 1
      push_cast
      ring
    · rw [bgOp_apply, if_pos hj, gM_vac (by omega : (0 : ℤ) ≤ -(M : ℤ) - j - 1), map_zero,
        smul_zero, map_zero, gateBG, if_neg (fun hcon => hk hcon.1), zero_smul]
  · rw [bgOp_vac_of_nonneg _ j (by omega), smul_zero, map_zero, gateBG,
      if_neg (fun hcon => hj hcon.2), zero_smul]

theorem gateBG_support (M : ℕ) :
    Function.support (gateBG M) ⊆ ↑((Finset.range M).image (fun i : ℕ => -(i : ℤ) - 1)) := by
  intro j hj
  rw [Function.mem_support] at hj
  have hcond : -(M : ℤ) ≤ j ∧ j < 0 := by
    by_contra hc
    exact hj (by rw [gateBG, if_neg hc])
  exact Finset.mem_coe.mpr (Finset.mem_image.mpr
    ⟨(-j - 1).toNat, Finset.mem_range.mpr (by omega), by omega⟩)

theorem gateBG_support_finite (M : ℕ) : (Function.support (gateBG M)).Finite :=
  Set.Finite.subset (Finset.finite_toSet _) (gateBG_support M)

/-- `Σ_j gate = -(M³-M)/12` — the number from which `c = -1` is read off. -/
theorem gateBG_sum (M : ℕ) : ∑ᶠ j : ℤ, gateBG M j = -(((M : ℂ) ^ 3 - (M : ℂ)) / 12) := by
  rw [finsum_eq_sum_of_support_subset _ (gateBG_support M),
    Finset.sum_image (by
      intro a _ b _ hab
      have hab' : -(a : ℤ) - 1 = -(b : ℤ) - 1 := hab
      omega)]
  have h : ∀ i ∈ Finset.range M,
      gateBG M (-(i : ℤ) - 1) = (-(1 / 4 : ℂ)) * ((M : ℂ) - 2 * (i : ℂ) - 1) ^ 2 := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [gateBG, if_pos ⟨by omega, by omega⟩]
    push_cast
    ring
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, quadSumBG]
  ring

theorem Xop_central_nat (M : ℕ) :
    Xop (M : ℤ) (-(M : ℤ)) vacBG = (-(((M : ℂ) ^ 3 - (M : ℂ)) / 12)) • vacBG := by
  have h0 : Lbg (M : ℤ) vacBG = 0 := Lbg_vacuum (by omega)
  have hfin := bgTerm_support_finite (Acoef (-(M : ℤ))) (-(M : ℤ)) vacBG
  rw [Xop_apply, h0, map_zero, show (M : ℤ) + -(M : ℤ) = 0 from by ring,
    Lbg_vacuum (by norm_num : (-1 : ℤ) ≤ 0), smul_zero, sub_zero, sub_zero]
  have h1 : Lbg (M : ℤ) (Lbg (-(M : ℤ)) vacBG)
      = ∑ᶠ j : ℤ, Lbg (M : ℤ) (Acoef (-(M : ℤ)) j • bgOp (-(M : ℤ)) j vacBG) := by
    change Lbg (M : ℤ) (∑ᶠ j : ℤ, Acoef (-(M : ℤ)) j • bgOp (-(M : ℤ)) j vacBG) = _
    exact map_finsum (Lbg (M : ℤ)) hfin
  rw [h1, finsum_congr (fun j => Lbg_bgTerm_vac M j),
    ← finsum_smul' (gateBG_support_finite M) vacBG, gateBG_sum]

theorem Xop_central (m : ℤ) :
    Xop m (-m) vacBG = (-(((m : ℂ) ^ 3 - (m : ℂ)) / 12)) • vacBG := by
  by_cases hm : (0 : ℤ) ≤ m
  · obtain ⟨M, rfl⟩ : ∃ M : ℕ, m = (M : ℤ) := ⟨m.toNat, (Int.toNat_of_nonneg hm).symm⟩
    exact Xop_central_nat M
  · obtain ⟨M, hM⟩ : ∃ M : ℕ, -m = (M : ℤ) :=
      ⟨(-m).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    have hm' : m = -(M : ℤ) := by omega
    subst hm'
    rw [neg_neg, Xop_antisymm, LinearMap.neg_apply, Xop_central_nat M, ← neg_smul]
    congr 1
    push_cast
    ring

/-! ## §K  The Virasoro relation, and the central charge -/

/-- **The central charge of the `λ = 1/2` `βγ` system**, *derived* in `Xop_central`:
`Xop m (-m)|0⟩ = -(m³-m)/12·|0⟩`, and the Virasoro central term is `(m³-m)/12·c`, so `c = -1`. -/
noncomputable def centralCharge : ℂ := -1

/-- **The Virasoro algebra at `c = -1` for the `βγ` symplectic bosons**:
`[Lₘ, Lₙ] = (m-n)L_{m+n} + δ_{m+n,0}·(m³-m)/12·(-1)·id`. -/
theorem Lbg_virasoro (m n : ℤ) :
    Lbg m * Lbg n - Lbg n * Lbg m
      = ((m : ℂ) - (n : ℂ)) • Lbg (m + n)
        + (if m + n = 0 then ((m : ℂ) ^ 3 - (m : ℂ)) / 12 * centralCharge else 0)
            • (1 : Module.End ℂ Fock) := by
  have hX : Xop m n
      = (if m + n = 0 then ((m : ℂ) ^ 3 - (m : ℂ)) / 12 * centralCharge else 0)
          • (1 : Module.End ℂ Fock) := by
    by_cases h : m + n = 0
    · have hn : n = -m := by omega
      subst hn
      rw [if_pos h]
      refine eq_smul_of_comm_of_vac _ _ (Xop_comm_mulX m (-m)) ?_
      rw [Xop_central m, centralCharge]
      congr 1
      ring
    · rw [if_neg h, zero_smul]
      have hz := eq_smul_of_comm_of_vac (Xop m n) 0 (Xop_comm_mulX m n)
        (by rw [Xop_vac_zero h, zero_smul])
      rw [hz, zero_smul]
  rw [Xop, sub_eq_iff_eq_add'] at hX
  exact hX

/-- The same statement with the central charge spelled out, matching
`Examples/VirasoroFock.Lld_virasoro` and `SymplecticFermionVirasoroB.Lsf_virasoro_id`. -/
theorem Lbg_virasoro_id (m n : ℤ) :
    Lbg m * Lbg n - Lbg n * Lbg m
      = ((m : ℂ) - (n : ℂ)) • Lbg (m + n)
        + (if m + n = 0 then ((m : ℂ) ^ 3 - (m : ℂ)) / 12 * (-1) else 0)
            • (LinearMap.id : Module.End ℂ Fock) := Lbg_virasoro m n

/-! ## §L  The conformal vector, and non-degeneracy -/

/-- The **conformal vector** `ω = L₋₂|0⟩`.  It is a sum of *two* terms — a weight-`1/2` mode
times a weight-`3/2` mode, in both orders — because the moding is half-integral. -/
noncomputable def omegaBG : Fock := Lbg (-2) vacBG

/-- Only `j = -2` and `j = -1` contribute to `L₋₂|0⟩`. -/
theorem omegaBG_support :
    Function.support (fun j : ℤ => Acoef (-2) j • bgOp (-2) j vacBG) ⊆ ↑({-2, -1} : Finset ℤ) := by
  intro j hj
  rw [Function.mem_support] at hj
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
  by_cases hc1 : j = -2
  · exact Or.inl hc1
  by_cases hc2 : j = -1
  · exact Or.inr hc2
  refine absurd ?_ hj
  by_cases hjn : j < 0
  · rw [bgOp_apply, if_pos hjn, gM_vac (by omega : (0 : ℤ) ≤ -2 - j - 1), map_zero, smul_zero]
  · rw [bgOp_vac_of_nonneg _ j (by omega), smul_zero]

/-- **The conformal vector, explicitly.**
`ω = (1/2)·β₋₁ₗ₂γ₋₃ₗ₂|0⟩ - (1/2)·β₋₃ₗ₂γ₋₁ₗ₂|0⟩ = (1/2)(X₍ᵢₙₗ ₀₎X₍ᵢₙᵣ ₁₎ - X₍ᵢₙₗ ₁₎X₍ᵢₙᵣ ₀₎)`.
Each term is a weight-`1/2` mode times a weight-`3/2` mode: **two half-integers summing to the
integer 2**.  In the symplectic-fermion analogue the conformal vector is the single term
`χ⁻₋₁χ⁺₋₁|0⟩` (`1 + 1`); the two-term antisymmetric shape here is exactly what half-integer
moding produces. -/
theorem omegaBG_eq :
    omegaBG = (1 / 2 : ℂ) • (X (Sum.inl 0) * X (Sum.inr 1) : Fock)
      - (1 / 2 : ℂ) • (X (Sum.inl 1) * X (Sum.inr 0) : Fock) := by
  have hb2 : bM (-2) = mulX (Sum.inl 1) := by
    rw [show (-2 : ℤ) = -((1 : ℕ) : ℤ) - 1 from by norm_num, bM_neg_eq_mulX]
  have hb1 : bM (-1) = mulX (Sum.inl 0) := by
    rw [show (-1 : ℤ) = -((0 : ℕ) : ℤ) - 1 from by norm_num, bM_neg_eq_mulX]
  have hg1 : gM (-1) = mulX (Sum.inr 0) := by
    rw [show (-1 : ℤ) = -((0 : ℕ) : ℤ) - 1 from by norm_num, gM_neg_eq_mulX]
  have hg2 : gM (-2) = mulX (Sum.inr 1) := by
    rw [show (-2 : ℤ) = -((1 : ℕ) : ℤ) - 1 from by norm_num, gM_neg_eq_mulX]
  rw [omegaBG, Lbg_apply, finsum_eq_sum_of_support_subset _ omegaBG_support,
    Finset.sum_pair (by decide : (-2 : ℤ) ≠ -1), bgOp_apply, bgOp_apply,
    if_pos (by norm_num : (-2 : ℤ) < 0), if_pos (by norm_num : (-1 : ℤ) < 0),
    show (-2 : ℤ) - -2 - 1 = -1 from by norm_num,
    show (-2 : ℤ) - -1 - 1 = -2 from by norm_num, hb2, hb1, hg1, hg2]
  simp only [mulX_apply, vacBG, mul_one, Acoef]
  push_cast
  module

/-- `L₀ω = 2ω`. -/
theorem Lbg_zero_omegaBG : Lbg 0 omegaBG = (2 : ℂ) • omegaBG := by
  rw [omegaBG, Lbg_zero_Lbg_vac (-2)]
  congr 1
  push_cast
  ring

/-- `L₁ω = 0`: the conformal vector is quasi-primary. -/
theorem Lbg_one_omegaBG : Lbg 1 omegaBG = 0 := by
  have h := LinearMap.congr_fun (Lbg_virasoro 1 (-2)) vacBG
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply,
    if_neg (by norm_num : ¬ ((1 : ℤ) + -2 = 0)), zero_smul, add_zero,
    show (1 : ℤ) + -2 = -1 from by ring, Lbg_vacuum (le_refl (-1 : ℤ)), smul_zero,
    Lbg_vacuum (by norm_num : (-1 : ℤ) ≤ 1), map_zero, sub_zero] at h
  rw [omegaBG, h]

/-- `L₂ω = (c/2)|0⟩ = (-1/2)|0⟩`: the central charge exhibited as a double contraction. -/
theorem Lbg_two_omegaBG : Lbg 2 omegaBG = (-(1 : ℂ) / 2) • vacBG := by
  have h := LinearMap.congr_fun (Lbg_virasoro 2 (-2)) vacBG
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply,
    if_pos (by norm_num : (2 : ℤ) + -2 = 0), show (2 : ℤ) + -2 = 0 from by ring,
    Lbg_vacuum (by norm_num : (-1 : ℤ) ≤ 0), smul_zero, zero_add,
    Lbg_vacuum (by norm_num : (-1 : ℤ) ≤ 2), map_zero, sub_zero] at h
  rw [omegaBG, h, centralCharge]
  congr 1
  push_cast
  ring

/-- **`c = -1` is forced.**  Any scalar `c` for which the Virasoro relation holds with central
term `δ_{m+n,0}·(m³-m)/12·c` must equal `-1`.  Together with `Lbg_virasoro` (which exhibits such a
`c`) this *determines* the central charge rather than quoting it: the value is read off from
`Xop_central`, and nothing else can work.  Note this is a statement about a **nonzero**
representation — see `vacBG_ne_zero`, `omegaBG_ne_zero`, `Lbg_two_ne_zero`. -/
theorem centralCharge_unique (c : ℂ)
    (hc : ∀ m n : ℤ, Lbg m * Lbg n - Lbg n * Lbg m
        = ((m : ℂ) - (n : ℂ)) • Lbg (m + n)
          + (if m + n = 0 then ((m : ℂ) ^ 3 - (m : ℂ)) / 12 * c else 0)
              • (1 : Module.End ℂ Fock)) :
    c = -1 := by
  have h := LinearMap.congr_fun (hc 2 (-2)) vacBG
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply,
    if_pos (by norm_num : (2 : ℤ) + -2 = 0), show (2 : ℤ) + -2 = 0 from by ring,
    Lbg_vacuum (by norm_num : (-1 : ℤ) ≤ 0), smul_zero, zero_add,
    Lbg_vacuum (by norm_num : (-1 : ℤ) ≤ 2), map_zero, sub_zero,
    show Lbg 2 (Lbg (-2) vacBG) = Lbg 2 omegaBG from rfl, Lbg_two_omegaBG] at h
  have hv := smul_eq_smul_of_ne_zero vacBG_ne_zero h
  have hstep : c = 2 * (((((2 : ℤ)) : ℂ) ^ 3 - (((2 : ℤ)) : ℂ)) / 12 * c) := by push_cast; ring
  rw [← hv] at hstep
  rw [hstep]
  norm_num

/-- The conformal vector is nonzero, so `L₂ω = (c/2)|0⟩` is a real statement about `c`. -/
theorem omegaBG_ne_zero : omegaBG ≠ 0 := by
  intro h
  have h2 : (-(1 : ℂ) / 2) • (vacBG : Fock) = 0 := by rw [← Lbg_two_omegaBG, h, map_zero]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 (by norm_num)
  · exact vacBG_ne_zero h3

/-- The modes act nontrivially: `L₂ ≠ 0`. -/
theorem Lbg_two_ne_zero : Lbg 2 ≠ 0 := by
  intro h
  have h2 : (-(1 : ℂ) / 2) • (vacBG : Fock) = 0 := by
    rw [← Lbg_two_omegaBG, h, LinearMap.zero_apply]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 (by norm_num)
  · exact vacBG_ne_zero h3

/-! ## §M  `L₋₁` as the translation operator

A translation operator `T` for the `βγ` system is built separately.  Given it, the
identity `L₋₁ = T` follows from `Lbg_neg_one_creation` below together with `T|0⟩ = 0` and the
matching commutator `[T, mulX (inl k)] = (k+1)·mulX (inl (k+1))` (and likewise for `inr`), by the
same two-line induction over monomials as `eq_smul_of_comm_of_vac`.  Stated here as the concrete
mode identity so that no dependence on another in-flight file is created. -/

/-- `[L₋₁, β_{-k-1/2}] = (k+1)·β_{-k-3/2}`: `L₋₁` raises each creation index by one with weight
`k+1`.  This is exactly the commutator characterizing the translation operator `T`. -/
theorem Lbg_neg_one_creation_inl (k : ℕ) (x : Fock) :
    Lbg (-1) (mulX (Sum.inl k) x)
      = mulX (Sum.inl k) (Lbg (-1) x) + ((k : ℂ) + 1) • mulX (Sum.inl (k + 1)) x := by
  rw [← bM_neg_eq_mulX k, Lbg_bM_apply (-1) (-(k : ℤ) - 1) x,
    show (-1 : ℤ) + (-(k : ℤ) - 1) = -((k + 1 : ℕ) : ℤ) - 1 from by push_cast; ring,
    bM_neg_eq_mulX (k + 1)]
  congr 2
  simp only [wtBG]
  push_cast
  ring

/-- The `γ` half of the same statement. -/
theorem Lbg_neg_one_creation_inr (k : ℕ) (x : Fock) :
    Lbg (-1) (mulX (Sum.inr k) x)
      = mulX (Sum.inr k) (Lbg (-1) x) + ((k : ℂ) + 1) • mulX (Sum.inr (k + 1)) x := by
  rw [← gM_neg_eq_mulX k, Lbg_gM_apply (-1) (-(k : ℤ) - 1) x,
    show (-1 : ℤ) + (-(k : ℤ) - 1) = -((k + 1 : ℕ) : ℤ) - 1 from by push_cast; ring,
    gM_neg_eq_mulX (k + 1)]
  congr 2
  simp only [wtBG]
  push_cast
  ring

/-- `L₋₁|0⟩ = 0`. -/
theorem Lbg_neg_one_vacuum : Lbg (-1) vacBG = 0 := Lbg_vacuum (le_refl (-1 : ℤ))

end VOA.BGVir

/-! ## §N  Axiom audit

Every result above was checked with `#print axioms` to depend only on
`[propext, Classical.choice, Quot.sound]` — no `sorry`, no `native_decide`, no new axioms. -/
