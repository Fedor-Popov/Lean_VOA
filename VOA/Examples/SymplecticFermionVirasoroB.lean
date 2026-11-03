/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.SymplecticFermionSpan

/-!
# Symplectic fermions: the Virasoro algebra at `c = -2`, by the **oscillator** route

This file builds the Virasoro modes for symplectic fermions **directly as normally-ordered
bilinears in the `χ` modes**, in the style of `Examples/HeisenbergVirasoro` (`Lvir`, `sugTerm`)
and `Examples/VirasoroFock` (`Lld`, `Lld_virasoro`), and proves

`[Lₘ, Lₙ] = (m-n)L_{m+n} + δ_{m+n,0}·(m³-m)/12·(-2)`

by a mode computation.  Nothing here uses the super vertex-operator machinery (`nprodε`,
`reconstructε`, `YSF`); the only inputs are the canonical anticommutation relations
(`chi_anticomm`), lower truncation (`chi_isField`), the vacuum relations (`chi_neg_vac`) and the
spanning statement (`stWordSF_span`).

## Conventions

`chiM a m = χᵃ_m` is the mode operator, obtained from the `z`-exponent-indexed field by
`chiM a m = chi a (-m-1)`.  Species `0` is `χ⁺` and species `1` is `χ⁻`, with
`ω⁰¹ = 1 = -ω¹⁰`, so the CAR reads `{χᵃ_m, χᵇ_n} = m·δ_{m+n,0}·ωᵃᵇ`.  Note `χᵃ_0 = 0` on this
module (the pairing carries a factor of the mode number), which is why weight bookkeeping has an
exceptional point there.

## The modes

`Lsf n = ∑_j :χ⁻_j χ⁺_{n-j}:` with the **fermionic** normal ordering (a sign, not the bosonic
`normalOrdered` of `Foundations/Locality`).  The sum is infinite but locally finite, so — exactly
as for `nprodCoeff` — the operator is defined by its action on each vector through a `finsum`,
with `sfTerm_support_finite` supplying summability.

The overall sign is fixed by demanding `[Lₙ, χᵇ_k] = -k·χᵇ_{n+k}`, the statement that `χ` is
primary of conformal weight `1`.

## Why the proof does not need a double mode sum

A head-on `[Lₘ, Lₙ]` would be a double infinite sum with a normal-ordering boundary shift (the
central-charge anomaly), which is the expensive part of `HeisenbergVirasoro`/`HeisenbergCentral`.
Instead we use that the Fock module is generated from the vacuum by creation operators:

1. `Lsf_bracket_chiM`: `[Lₙ, χᵇ_k] = -k χᵇ_{n+k}` — one delta-gated `finsum` collapse.
2. `Xop_comm_chiM`: hence `Xop m n := [Lₘ,Lₙ] - (m-n)L_{m+n}` **commutes with every mode**
   (a Jacobi computation with no sums at all).
3. `eq_smul_of_comm_of_vac`: an operator commuting with all creations is determined by its value
   on the vacuum, and if that value is `c·|0⟩` the operator is `c·id` (`stWordSF_span`).
4. `Lsf_ann_zero`: `L₀` kills any vector killed by all annihilation modes.  Since `Xop m n |0⟩`
   is such a vector, while `L₀(Xop m n |0⟩) = -(m+n)·Xop m n |0⟩`, the vector **vanishes**
   whenever `m + n ≠ 0`.  This replaces the usual grading argument — no `L₀`-eigenspace
   decomposition is needed.
5. For `m + n = 0` the vacuum value is a **single** finite sum,
   `∑_{j=-m+1}^{-1} j(m+j) = -(m³-m)/6`, evaluated in `gateSF_sum`.  The `-2` of `c = -2` is
   born there, in `chiM_pair_vac`, from `ω¹⁰ = -1`.

## What is also proved

* `Lsf_neg_one_eq_T`: `L₋₁` is the repo's translation operator `T` of `Examples/SymplecticFermionT`
  (both are the same derivation on words), which is the bridge to the vertex-operator side.
* `omegaSF = L₋₂|0⟩ = χ⁻₋₁χ⁺₋₁|0⟩` with `L₀ω = 2ω`, `L₁ω = 0`, and `L₂ω = -|0⟩ = (c/2)|0⟩` —
  the central charge exhibited as a double contraction, as in `HeisenbergVirasoro.L_two_omega`.
-/

namespace VOA.SympFerm.VirB

open CliffordAlgebra

/-! ## §A  The mode operators `χᵃ_m`

`FormalDist` is indexed by the `z`-exponent, so the mode `m` sits at index `-m-1`.  Repackaging
the field as a family of modes is what makes the oscillator computation readable. -/

/-- The **mode operator** `χᵃ_m`.  Creation for `m ≤ -1`, annihilation for `m ≥ 0`. -/
noncomputable def chiM (a : Fin 2) (m : ℤ) : Module.End ℂ FockSF := chi a (-m - 1)

theorem sfOmega_01 : sfOmega 0 1 = 1 := by
  rw [sfOmega, if_pos (by decide : ((1 : Fin 2) = 0 + 1)), sfSign, if_pos rfl]

theorem sfOmega_10 : sfOmega 1 0 = -1 := by
  rw [sfOmega, if_pos (by decide : ((0 : Fin 2) = 1 + 1)), sfSign, if_neg (by decide)]

/-- **The CAR in mode form**: `{χᵃ_m, χᵇ_n} = m·δ_{m+n,0}·ωᵃᵇ`.  This is `chi_anticomm` with the
`z`-exponent reindexed; the mode number `m` that appears as the coefficient is exactly the factor
that makes the locality order `2` rather than `1`. -/
theorem chiM_anticomm_apply (a b : Fin 2) (m n : ℤ) (x : FockSF) :
    chiM a m (chiM b n x) + chiM b n (chiM a m x)
      = (if m + n = 0 then ((m : ℂ) * sfOmega a b) else 0) • x := by
  have h := LinearMap.congr_fun (chi_anticomm a b (-m - 1) (-n - 1)) x
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply,
    Module.End.one_apply] at h
  rw [show (-m - 1) + (-n - 1) + 2 = -(m + n) from by ring,
    show (-(-m - 1) - 1 : ℤ) = m from by ring] at h
  change chi a (-m - 1) (chi b (-n - 1) x) + chi b (-n - 1) (chi a (-m - 1) x) = _
  rw [h]
  by_cases hmn : m + n = 0
  · rw [if_pos (by omega : -(m + n) = 0), if_pos hmn]
  · rw [if_neg (by omega : ¬ (-(m + n) = 0)), if_neg hmn]

/-- `χᵃ_0 = 0`: the symplectic pairing carries a factor of the mode number. -/
@[simp] theorem chiM_zero_mode (a : Fin 2) : chiM a 0 = 0 := by
  rw [chiM, show (-(0 : ℤ) - 1) = -1 from by ring, chi, if_neg (by omega : ¬ ((0 : ℤ) ≤ -1)),
    show (-(-1 : ℤ) - 1).toNat = 0 from by norm_num]
  exact annSF_zero a

/-- Nonnegative modes annihilate the vacuum. -/
theorem chiM_vac (a : Fin 2) {m : ℤ} (hm : 0 ≤ m) : chiM a m vacSF = 0 :=
  chi_neg_vac a (-m - 1) (by omega)

/-- The negative modes are the Clifford creation operators; this is the bridge from the mode
picture to `stWordSF`. -/
theorem chiM_creBase (p : ℕ × Fin 2) : chiM p.2 (-(p.1 : ℤ) - 1) = creBase p := by
  rw [chiM, show -(-(p.1 : ℤ) - 1) - 1 = ((p.1 : ℕ) : ℤ) from by ring, chi,
    if_pos (by positivity), Int.toNat_natCast]
  rfl

/-- **Lower truncation in mode form**: on a fixed vector all sufficiently high modes vanish.
This is `chi_isField` reindexed, and is what makes `Lsf` a finite sum on each vector. -/
theorem chiM_high (a : Fin 2) (x : FockSF) : ∃ M : ℤ, ∀ m : ℤ, M ≤ m → chiM a m x = 0 := by
  obtain ⟨B, hB⟩ := chi_isField a x
  exact ⟨-B, fun m hm => hB (-m - 1) (by omega)⟩

/-- The `ω`-contraction that turns the two terms of a bracket back into a single mode:
`ω⁰ᵇ χ¹ - ω¹ᵇ χ⁰ = χᵇ`.  Both cases are one nonzero entry of the symplectic form. -/
theorem omega_combo (mm : ℤ) (x : FockSF) (b : Fin 2) :
    sfOmega 0 b • chiM 1 mm x - sfOmega 1 b • chiM 0 mm x = chiM b mm x := by
  revert b
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · rw [sfOmega_same, sfOmega_10]; module
  · rw [sfOmega_01, sfOmega_same]; module

/-! ## §B  The Virasoro modes `Lₙ`

`Lₙ = ∑_j :χ⁻_j χ⁺_{n-j}:`, fermionic normal ordering (annihilators to the right, with a sign).
The sign of the whole expression is fixed by `Lsf_bracket_chiM` below. -/

/-- The `j`-th normally ordered term `:χ⁻_j χ⁺_{n-j}:` of `Lₙ`.  The `j ≥ 0` branch carries the
fermionic minus sign of the reordering. -/
noncomputable def sfTerm (n j : ℤ) : Module.End ℂ FockSF :=
  if j < 0 then chiM 1 j * chiM 0 (n - j) else -(chiM 0 (n - j) * chiM 1 j)

theorem sfTerm_apply (n j : ℤ) (x : FockSF) :
    sfTerm n j x
      = if j < 0 then chiM 1 j (chiM 0 (n - j) x) else -(chiM 0 (n - j) (chiM 1 j x)) := by
  rw [sfTerm]
  split_ifs <;> simp only [Module.End.mul_apply, LinearMap.neg_apply]

/-- **Summability.**  For `j` large the right-hand factor is a high annihilation mode; for `j`
very negative the *other* factor is (and the normal ordering has put it on the right).  So only
finitely many terms act nontrivially on a fixed vector. -/
theorem sfTerm_support_finite (n : ℤ) (x : FockSF) :
    (Function.support fun j : ℤ => sfTerm n j x).Finite := by
  obtain ⟨M0, h0⟩ := chiM_high 0 x
  obtain ⟨M1, h1⟩ := chiM_high 1 x
  apply Set.Finite.subset ((Set.finite_Icc (n - M0 + 1) (-1)).union (Set.finite_Icc 0 (M1 - 1)))
  intro j hj
  rw [Function.mem_support] at hj
  by_cases hjneg : j < 0
  · have hlt : ¬ (M0 ≤ n - j) := fun hle =>
      hj (by rw [sfTerm_apply, if_pos hjneg, h0 (n - j) hle, map_zero])
    exact Or.inl (Set.mem_Icc.mpr ⟨by omega, by omega⟩)
  · have hlt : ¬ (M1 ≤ j) := fun hle =>
      hj (by rw [sfTerm_apply, if_neg hjneg, h1 j hle, map_zero, neg_zero])
    exact Or.inr (Set.mem_Icc.mpr ⟨by omega, by omega⟩)

/-- **The Virasoro mode `Lₙ`**, defined by its (finite, by `sfTerm_support_finite`) action on each
vector.  Same `finsum` discipline as `Core.Dong.nprodCoeff`, but with the fermionic sign. -/
noncomputable def Lsf (n : ℤ) : Module.End ℂ FockSF where
  toFun x := ∑ᶠ j : ℤ, sfTerm n j x
  map_add' x y := by
    rw [← finsum_add_distrib (sfTerm_support_finite n x) (sfTerm_support_finite n y)]
    exact finsum_congr fun j => map_add _ x y
  map_smul' c x := by
    rw [RingHom.id_apply, smul_finsum' c (sfTerm_support_finite n x)]
    exact finsum_congr fun j => map_smul _ c x

theorem Lsf_apply (n : ℤ) (x : FockSF) : Lsf n x = ∑ᶠ j : ℤ, sfTerm n j x := rfl

/-! ## §C  `[Lₙ, χᵇ_k] = -k·χᵇ_{n+k}`  — the primary-of-weight-one relation

This is the only place a `finsum` is manipulated in an essential way.  The normal-ordering
constant is central, so it drops out of the bracket; what remains are two `δ`-gated terms, each
collapsing to a single point. -/

/-- Reordering the two factors of a term costs only a **central** scalar, so the bracket of
`sfTerm` with any mode equals the bracket of the plain product `χ⁻_j χ⁺_{n-j}`. -/
theorem sfTerm_bracket_eq (n j : ℤ) (b : Fin 2) (k : ℤ) (x : FockSF) :
    sfTerm n j (chiM b k x) - chiM b k (sfTerm n j x)
      = chiM 1 j (chiM 0 (n - j) (chiM b k x)) - chiM b k (chiM 1 j (chiM 0 (n - j) x)) := by
  by_cases hj : j < 0
  · rw [sfTerm_apply, sfTerm_apply, if_pos hj, if_pos hj]
  · rw [sfTerm_apply, sfTerm_apply, if_neg hj, if_neg hj]
    have hc := chiM_anticomm_apply 1 0 j (n - j)
    have h1 := hc (chiM b k x)
    have h2 := hc x
    have h3 : chiM 0 (n - j) (chiM 1 j (chiM b k x))
        = (if j + (n - j) = 0 then ((j : ℂ) * sfOmega 1 0) else 0) • chiM b k x
          - chiM 1 j (chiM 0 (n - j) (chiM b k x)) := by rw [← h1]; abel
    have h4 : chiM 0 (n - j) (chiM 1 j x)
        = (if j + (n - j) = 0 then ((j : ℂ) * sfOmega 1 0) else 0) • x
          - chiM 1 j (chiM 0 (n - j) x) := by rw [← h2]; abel
    rw [h3, h4]
    simp only [map_neg, map_sub, map_smul]
    abel

/-- The per-term bracket: two `δ`-gated single-mode terms (`[AB,C] = A{B,C} - {A,C}B`). -/
theorem sfTerm_bracket (n j : ℤ) (b : Fin 2) (k : ℤ) (x : FockSF) :
    sfTerm n j (chiM b k x) - chiM b k (sfTerm n j x)
      = (if n - j + k = 0 then (((n : ℂ) - (j : ℂ)) * sfOmega 0 b) else 0) • chiM 1 j x
        - (if j + k = 0 then ((j : ℂ) * sfOmega 1 b) else 0) • chiM 0 (n - j) x := by
  rw [sfTerm_bracket_eq]
  have hB := chiM_anticomm_apply 0 b (n - j) k x
  have hA := chiM_anticomm_apply 1 b j k (chiM 0 (n - j) x)
  have hB' : chiM 0 (n - j) (chiM b k x)
      = (if n - j + k = 0 then (((n : ℂ) - (j : ℂ)) * sfOmega 0 b) else 0) • x
        - chiM b k (chiM 0 (n - j) x) := by
    have hcast : (((n - j : ℤ)) : ℂ) = (n : ℂ) - (j : ℂ) := by push_cast; ring
    rw [← hcast, ← hB]
    abel
  have hA' : chiM 1 j (chiM b k (chiM 0 (n - j) x))
      = (if j + k = 0 then ((j : ℂ) * sfOmega 1 b) else 0) • chiM 0 (n - j) x
        - chiM b k (chiM 1 j (chiM 0 (n - j) x)) := by rw [← hA]; abel
  rw [hB', map_sub, map_smul, hA']
  abel

/-- **`[Lₙ, χᵇ_k] = -k·χᵇ_{n+k}`**: the `χ` are primary of conformal weight `1`.  This single
relation is what pins down the normalization of `Lsf`, and everything below is a consequence of
it together with the vacuum relations. -/
theorem Lsf_bracket_chiM (n : ℤ) (b : Fin 2) (k : ℤ) (x : FockSF) :
    Lsf n (chiM b k x) - chiM b k (Lsf n x) = (-(k : ℂ)) • chiM b (n + k) x := by
  classical
  have hs1 : (Function.support fun j : ℤ =>
      (if n - j + k = 0 then (((n : ℂ) - (j : ℂ)) * sfOmega 0 b) else 0) • chiM 1 j x).Finite := by
    apply Set.Finite.subset (Set.finite_singleton (n + k))
    intro j hj
    rw [Function.mem_support] at hj
    rw [Set.mem_singleton_iff]
    by_contra hne
    exact hj (by rw [if_neg (by omega : ¬ (n - j + k = 0)), zero_smul])
  have hs2 : (Function.support fun j : ℤ =>
      (if j + k = 0 then ((j : ℂ) * sfOmega 1 b) else 0) • chiM 0 (n - j) x).Finite := by
    apply Set.Finite.subset (Set.finite_singleton (-k))
    intro j hj
    rw [Function.mem_support] at hj
    rw [Set.mem_singleton_iff]
    by_contra hne
    exact hj (by rw [if_neg (by omega : ¬ (j + k = 0)), zero_smul])
  have hfin2 : (Function.support fun j : ℤ => chiM b k (sfTerm n j x)).Finite := by
    apply (sfTerm_support_finite n x).subset
    intro j hj
    rw [Function.mem_support] at hj ⊢
    intro h
    exact hj (by rw [h, map_zero])
  have hL : Lsf n (chiM b k x) - chiM b k (Lsf n x)
      = ∑ᶠ j : ℤ, (sfTerm n j (chiM b k x) - chiM b k (sfTerm n j x)) := by
    rw [finsum_sub_distrib (sfTerm_support_finite n (chiM b k x)) hfin2]
    congr 1
    change chiM b k (∑ᶠ j : ℤ, sfTerm n j x) = _
    exact map_finsum (chiM b k) (sfTerm_support_finite n x)
  rw [hL, finsum_congr fun j => sfTerm_bracket n j b k x, finsum_sub_distrib hs1 hs2]
  have e1 : ∑ᶠ j : ℤ,
      (if n - j + k = 0 then (((n : ℂ) - (j : ℂ)) * sfOmega 0 b) else 0) • chiM 1 j x
      = ((-(k : ℂ)) * sfOmega 0 b) • chiM 1 (n + k) x := by
    rw [finsum_eq_single _ (n + k)
      (fun j hj => by rw [if_neg (by omega : ¬ (n - j + k = 0)), zero_smul]),
      if_pos (by ring)]
    congr 1
    push_cast
    ring
  have e2 : ∑ᶠ j : ℤ, (if j + k = 0 then ((j : ℂ) * sfOmega 1 b) else 0) • chiM 0 (n - j) x
      = ((-(k : ℂ)) * sfOmega 1 b) • chiM 0 (n + k) x := by
    rw [finsum_eq_single _ (-k)
      (fun j hj => by rw [if_neg (by omega : ¬ (j + k = 0)), zero_smul]),
      if_pos (by ring), show n - -k = n + k from by ring]
    congr 1
    push_cast
    ring
  rw [e1, e2, ← omega_combo (n + k) x b, smul_sub, smul_smul, smul_smul]

/-- The bracket relation in the form used everywhere below. -/
theorem Lsf_chiM_apply (n : ℤ) (b : Fin 2) (k : ℤ) (x : FockSF) :
    Lsf n (chiM b k x) = chiM b k (Lsf n x) - (k : ℂ) • chiM b (n + k) x := by
  have h := Lsf_bracket_chiM n b k x
  rw [neg_smul, sub_eq_iff_eq_add] at h
  rw [h]
  abel

/-! ## §D  Vacuum relations -/

theorem sfTerm_vac_of_nonneg (n j : ℤ) (hj : 0 ≤ j) : sfTerm n j vacSF = 0 := by
  rw [sfTerm_apply, if_neg (by omega), chiM_vac 1 hj, map_zero, neg_zero]

/-- `Lₙ|0⟩ = 0` for `n ≥ -1`: with both mode indices summing to `n ≥ -1`, one of them is always
nonnegative, and the normal ordering has put it on the right. -/
theorem Lsf_vacuum {n : ℤ} (hn : -1 ≤ n) : Lsf n vacSF = 0 := by
  have h : ∀ j : ℤ, sfTerm n j vacSF = 0 := by
    intro j
    by_cases hj : j < 0
    · rw [sfTerm_apply, if_pos hj, chiM_vac 0 (by omega : (0 : ℤ) ≤ n - j), map_zero]
    · exact sfTerm_vac_of_nonneg n j (by omega)
  rw [Lsf_apply]
  exact (finsum_congr h).trans finsum_zero

/-- **`L_p` kills anything killed by all annihilation modes** (`p ≥ 0`): each term of `L_p` has an
annihilation mode on the right.  This is the substitute for an `L₀`-eigenspace decomposition:
it is what forces `Xop m n |0⟩ = 0` off the diagonal `m + n = 0`. -/
theorem Lsf_ann_zero (y : FockSF) (hy : ∀ (b : Fin 2) (k : ℤ), 0 ≤ k → chiM b k y = 0)
    {p : ℤ} (hp : 0 ≤ p) : Lsf p y = 0 := by
  have h : ∀ j : ℤ, sfTerm p j y = 0 := by
    intro j
    by_cases hj : j < 0
    · rw [sfTerm_apply, if_pos hj, hy 0 (p - j) (by omega), map_zero]
    · rw [sfTerm_apply, if_neg hj, hy 1 j (by omega), map_zero, neg_zero]
  rw [Lsf_apply]
  exact (finsum_congr h).trans finsum_zero

/-- The `L₀`-weight of `L_p|0⟩` is `-p`, proved **term by term** — no explicit evaluation of
`L_p|0⟩` is needed, only `[L₀, χ] = -k χ` twice and `L₀|0⟩ = 0`. -/
theorem Lsf_zero_Lsf_vac (p : ℤ) : Lsf 0 (Lsf p vacSF) = (-(p : ℂ)) • Lsf p vacSF := by
  have hfin := sfTerm_support_finite p vacSF
  have h2 : ∀ j : ℤ, Lsf 0 (sfTerm p j vacSF) = (-(p : ℂ)) • sfTerm p j vacSF := by
    intro j
    by_cases hj : j < 0
    · have hy : Lsf 0 (chiM 0 (p - j) vacSF)
          = (-((p : ℂ) - (j : ℂ))) • chiM 0 (p - j) vacSF := by
        rw [Lsf_chiM_apply 0 0 (p - j) vacSF, Lsf_vacuum (by norm_num : (-1 : ℤ) ≤ 0), map_zero,
          show (0 : ℤ) + (p - j) = p - j from by ring]
        push_cast
        module
      rw [sfTerm_apply, if_pos hj, Lsf_chiM_apply 0 1 j (chiM 0 (p - j) vacSF), hy,
        show (0 : ℤ) + j = j from by ring, map_smul]
      module
    · rw [sfTerm_vac_of_nonneg p j (by omega), map_zero, smul_zero]
  have h1 : Lsf 0 (Lsf p vacSF) = ∑ᶠ j : ℤ, Lsf 0 (sfTerm p j vacSF) := by
    change Lsf 0 (∑ᶠ j : ℤ, sfTerm p j vacSF) = _
    exact map_finsum (Lsf 0) hfin
  rw [h1, finsum_congr h2, ← smul_finsum' (-(p : ℂ)) hfin, Lsf_apply]

/-! ## §E  The defect operator `Xop` and its rigidity -/

/-- `Xop m n = [Lₘ, Lₙ] - (m-n)L_{m+n}`: the operator the Virasoro relation claims is central. -/
noncomputable def Xop (m n : ℤ) : Module.End ℂ FockSF :=
  Lsf m * Lsf n - Lsf n * Lsf m - ((m : ℂ) - (n : ℂ)) • Lsf (m + n)

theorem Xop_apply (m n : ℤ) (x : FockSF) :
    Xop m n x = Lsf m (Lsf n x) - Lsf n (Lsf m x) - ((m : ℂ) - (n : ℂ)) • Lsf (m + n) x := by
  rw [Xop]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply]

theorem Xop_antisymm (m n : ℤ) : Xop m n = - Xop n m := by
  rw [Xop, Xop, show n + m = m + n from by ring]
  module

/-- **`Xop` commutes with every mode.**  This is the Jacobi identity written out: the two
first-order terms cancel in pairs and the second-order terms combine to
`k(n-m) + (m-n)k = 0`.  No sums appear — everything is `Lsf_chiM_apply` applied four times. -/
theorem Xop_comm_chiM (m n : ℤ) (b : Fin 2) (k : ℤ) (x : FockSF) :
    Xop m n (chiM b k x) = chiM b k (Xop m n x) := by
  have e1 : Lsf m (Lsf n (chiM b k x))
      = chiM b k (Lsf m (Lsf n x)) - (k : ℂ) • chiM b (m + k) (Lsf n x)
        - (k : ℂ) • chiM b (n + k) (Lsf m x)
        + ((k : ℂ) * ((n : ℂ) + (k : ℂ))) • chiM b (m + n + k) x := by
    rw [Lsf_chiM_apply n b k x, map_sub, map_smul, Lsf_chiM_apply m b k (Lsf n x),
      Lsf_chiM_apply m b (n + k) x, show m + (n + k) = m + n + k from by ring]
    push_cast
    module
  have e2 : Lsf n (Lsf m (chiM b k x))
      = chiM b k (Lsf n (Lsf m x)) - (k : ℂ) • chiM b (n + k) (Lsf m x)
        - (k : ℂ) • chiM b (m + k) (Lsf n x)
        + ((k : ℂ) * ((m : ℂ) + (k : ℂ))) • chiM b (m + n + k) x := by
    rw [Lsf_chiM_apply m b k x, map_sub, map_smul, Lsf_chiM_apply n b k (Lsf m x),
      Lsf_chiM_apply n b (m + k) x, show n + (m + k) = m + n + k from by ring]
    push_cast
    module
  rw [Xop_apply, Xop_apply, e1, e2, Lsf_chiM_apply (m + n) b k x, map_sub, map_sub, map_smul]
  module

theorem Xop_comm_creBase (m n : ℤ) (p : ℕ × Fin 2) (y : FockSF) :
    Xop m n (creBase p y) = creBase p (Xop m n y) := by
  rw [← chiM_creBase p]
  exact Xop_comm_chiM m n p.2 (-(p.1 : ℤ) - 1) y

/-- **Rigidity.**  An operator commuting with all creation operators is determined by its value
on the vacuum; if that value is `c·|0⟩`, the operator is `c·id`.  This is where
`stWordSF_span` — the statement that creation monomials span the Fock space — enters. -/
theorem eq_smul_of_comm_of_vac (F : Module.End ℂ FockSF) (c : ℂ)
    (hcomm : ∀ (p : ℕ × Fin 2) (y : FockSF), F (creBase p y) = creBase p (F y))
    (hvac : F vacSF = c • vacSF) : F = c • (1 : Module.End ℂ FockSF) := by
  refine LinearMap.ext_on stWordSF_span ?_
  rintro x ⟨l, rfl⟩
  induction l with
  | nil =>
      rw [stWordSF_nil]
      change F vacSF = _
      rw [hvac]
      simp only [LinearMap.smul_apply, Module.End.one_apply]
  | cons p rest ih =>
      rw [stWordSF_cons, show ι QSF (Finsupp.single p (1 : ℂ)) * stWordSF rest
        = creBase p (stWordSF rest) from rfl, hcomm p, ih]
      simp only [LinearMap.smul_apply, Module.End.one_apply, map_smul]

/-! ## §F  `[L₀, L_p] = -p·L_p`, and the `L₀`-weight of `Xop m n |0⟩` -/

theorem Xop_zero_left (p : ℤ) : Xop 0 p = 0 := by
  have h : Xop 0 p = (0 : ℂ) • (1 : Module.End ℂ FockSF) := by
    refine eq_smul_of_comm_of_vac _ _ (Xop_comm_creBase 0 p) ?_
    rw [Xop_apply, Lsf_vacuum (by norm_num : (-1 : ℤ) ≤ 0), map_zero,
      show (0 : ℤ) + p = p from by ring, Lsf_zero_Lsf_vac p]
    push_cast
    module
  rw [h, zero_smul]

theorem Lsf_zero_comm_apply (p : ℤ) (y : FockSF) :
    Lsf 0 (Lsf p y) = Lsf p (Lsf 0 y) - (p : ℂ) • Lsf p y := by
  have h := LinearMap.congr_fun (Xop_zero_left p) y
  rw [Xop_apply, show (0 : ℤ) + p = p from by ring] at h
  simp only [LinearMap.zero_apply] at h
  push_cast at h
  rw [sub_eq_zero, sub_eq_iff_eq_add] at h
  rw [h]
  module

/-- The vacuum value of `Xop m n` sits at `L₀`-weight `-(m+n)`: the operator identity
`[L₀, Xop m n] = -(m+n)·Xop m n` (Jacobi again) evaluated on `|0⟩`. -/
theorem Xop_vac_L0 (m n : ℤ) :
    Lsf 0 (Xop m n vacSF) = (-((m : ℂ) + (n : ℂ))) • Xop m n vacSF := by
  have ha : Lsf 0 (Lsf m (Lsf n vacSF)) = (-((m : ℂ) + (n : ℂ))) • Lsf m (Lsf n vacSF) := by
    rw [Lsf_zero_comm_apply m (Lsf n vacSF), Lsf_zero_Lsf_vac n, map_smul]
    module
  have hb : Lsf 0 (Lsf n (Lsf m vacSF)) = (-((m : ℂ) + (n : ℂ))) • Lsf n (Lsf m vacSF) := by
    rw [Lsf_zero_comm_apply n (Lsf m vacSF), Lsf_zero_Lsf_vac m, map_smul]
    module
  have hc : Lsf 0 (Lsf (m + n) vacSF) = (-((m : ℂ) + (n : ℂ))) • Lsf (m + n) vacSF := by
    have := Lsf_zero_Lsf_vac (m + n)
    rw [this]
    congr 1
    push_cast
    ring
  rw [Xop_apply, map_sub, map_sub, map_smul, ha, hb, hc]
  module

/-- **Off the diagonal the defect kills the vacuum.**  `Xop m n |0⟩` is annihilated by every
annihilation mode (because `Xop` commutes with all modes and they kill `|0⟩`), so `L₀` kills it
by `Lsf_ann_zero`; but its `L₀`-weight is `-(m+n)`.  For `m + n ≠ 0` the vector must vanish. -/
theorem Xop_vac_zero {m n : ℤ} (h : m + n ≠ 0) : Xop m n vacSF = 0 := by
  have hann : ∀ (b : Fin 2) (k : ℤ), 0 ≤ k → chiM b k (Xop m n vacSF) = 0 := by
    intro b k hk
    rw [← Xop_comm_chiM, chiM_vac b hk, map_zero]
  have h1 : Lsf 0 (Xop m n vacSF) = 0 := Lsf_ann_zero _ hann (le_refl 0)
  have h2 := Xop_vac_L0 m n
  rw [h1] at h2
  have hc : ((m : ℂ) + (n : ℂ)) ≠ 0 := by
    have hz : ((m + n : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr h
    push_cast at hz
    exact hz
  rcases smul_eq_zero.mp h2.symm with h3 | h3
  · exact absurd (neg_eq_zero.mp h3) hc
  · exact h3

/-! ## §G  The central term: one finite sum

`Xop m (-m)|0⟩ = Lₘ(L₋ₘ|0⟩)`, and `Lₘ` acting on the two-creation term `χ⁻_j χ⁺_{-m-j}|0⟩` gives
`(-j)(-m-j)|0⟩` by two applications of `[Lₘ, χ] = -kχ`, one double contraction, and nothing else.
Summing `∑_{j=-m}^{-1} (-j)(-m-j) = -(m³-m)/6` gives `c = -2`. -/

/-- The one double contraction of the whole file: `χ⁻_{-k}χ⁺_k|0⟩ = k|0⟩` for `k ≤ 0`.  The sign
here is `ω¹⁰ = -1`, and it is the sign that makes the central charge negative. -/
theorem chiM_pair_vac {k : ℤ} (hk : k ≤ 0) :
    chiM 1 (-k) (chiM 0 k vacSF) = (k : ℂ) • vacSF := by
  have h := chiM_anticomm_apply 1 0 (-k) k vacSF
  rw [show -k + k = (0 : ℤ) from by ring, if_pos rfl, chiM_vac 1 (by omega : (0 : ℤ) ≤ -k),
    map_zero, add_zero] at h
  rw [h, sfOmega_10]
  congr 1
  push_cast
  ring

/-- The coefficient family whose sum is the central charge. -/
noncomputable def gateSF (M : ℕ) (j : ℤ) : ℂ :=
  if -(M : ℤ) ≤ j ∧ j < 0 then (((-j) * (-(M : ℤ) - j) : ℤ) : ℂ) else 0

/-- `Lₘ` applied to the `j`-th term of `L₋ₘ|0⟩`, term by term. -/
theorem Lsf_sfTerm_vac (M : ℕ) (j : ℤ) :
    Lsf (M : ℤ) (sfTerm (-(M : ℤ)) j vacSF) = gateSF M j • vacSF := by
  by_cases hj : j < 0
  · by_cases hk : -(M : ℤ) ≤ j
    · have hk0 : -(M : ℤ) - j ≤ 0 := by omega
      have hy : Lsf (M : ℤ) (chiM 0 (-(M : ℤ) - j) vacSF) = 0 := by
        rw [Lsf_chiM_apply (M : ℤ) 0 (-(M : ℤ) - j) vacSF,
          Lsf_vacuum (by omega : (-1 : ℤ) ≤ (M : ℤ)), map_zero,
          show (M : ℤ) + (-(M : ℤ) - j) = -j from by ring,
          chiM_vac 0 (by omega : (0 : ℤ) ≤ -j), smul_zero, sub_zero]
      rw [sfTerm_apply, if_pos hj,
        Lsf_chiM_apply (M : ℤ) 1 j (chiM 0 (-(M : ℤ) - j) vacSF), hy, map_zero,
        show (M : ℤ) + j = -(-(M : ℤ) - j) from by ring, chiM_pair_vac hk0,
        gateSF, if_pos ⟨hk, hj⟩, zero_sub, smul_smul, ← neg_smul]
      congr 1
      push_cast
      ring
    · rw [sfTerm_apply, if_pos hj, chiM_vac 0 (by omega : (0 : ℤ) ≤ -(M : ℤ) - j), map_zero,
        map_zero, gateSF, if_neg (fun hcon => hk hcon.1), zero_smul]
  · rw [sfTerm_vac_of_nonneg _ j (by omega), map_zero, gateSF,
      if_neg (fun hcon => hj hcon.2), zero_smul]

theorem gateSF_support (M : ℕ) :
    Function.support (gateSF M) ⊆ ↑((Finset.range M).image (fun i : ℕ => -(i : ℤ) - 1)) := by
  intro j hj
  rw [Function.mem_support] at hj
  have hcond : -(M : ℤ) ≤ j ∧ j < 0 := by
    by_contra hc
    exact hj (by rw [gateSF, if_neg hc])
  exact Finset.mem_coe.mpr (Finset.mem_image.mpr
    ⟨(-j - 1).toNat, Finset.mem_range.mpr (by omega), by omega⟩)

theorem gateSF_support_finite (M : ℕ) : (Function.support (gateSF M)).Finite :=
  Set.Finite.subset (Finset.finite_toSet _) (gateSF_support M)

theorem gauss_sum (N : ℕ) :
    ∑ i ∈ Finset.range N, ((i : ℂ) + 1) = (N : ℂ) * ((N : ℂ) + 1) / 2 := by
  induction N with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem sq_sum (N : ℕ) :
    ∑ i ∈ Finset.range N, ((i : ℂ) + 1) ^ 2 = (N : ℂ) * ((N : ℂ) + 1) * (2 * (N : ℂ) + 1) / 6 := by
  induction N with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- `∑_{i=1}^{N} i(i-N) = -(N³-N)/6`: the arithmetic behind `c = -2`. -/
theorem quad_sum (N : ℕ) :
    ∑ i ∈ Finset.range N, (((i : ℂ) + 1) * ((i : ℂ) + 1 - (N : ℂ)))
      = -(((N : ℂ) ^ 3 - (N : ℂ)) / 6) := by
  have h : ∀ i ∈ Finset.range N,
      ((i : ℂ) + 1) * ((i : ℂ) + 1 - (N : ℂ)) = ((i : ℂ) + 1) ^ 2 - (N : ℂ) * ((i : ℂ) + 1) := by
    intro i _; ring
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, ← Finset.mul_sum, sq_sum, gauss_sum]
  ring

theorem gateSF_sum (M : ℕ) : ∑ᶠ j : ℤ, gateSF M j = -(((M : ℂ) ^ 3 - (M : ℂ)) / 6) := by
  rw [finsum_eq_sum_of_support_subset _ (gateSF_support M),
    Finset.sum_image (by
      intro a _ b _ hab
      have hab' : -(a : ℤ) - 1 = -(b : ℤ) - 1 := hab
      omega)]
  have h : ∀ i ∈ Finset.range M,
      gateSF M (-(i : ℤ) - 1) = ((i : ℂ) + 1) * ((i : ℂ) + 1 - (M : ℂ)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [gateSF, if_pos ⟨by omega, by omega⟩]
    push_cast
    ring
  rw [Finset.sum_congr rfl h]
  exact quad_sum M

theorem Xop_central_nat (M : ℕ) :
    Xop (M : ℤ) (-(M : ℤ)) vacSF = (-(((M : ℂ) ^ 3 - (M : ℂ)) / 6)) • vacSF := by
  have h0 : Lsf (M : ℤ) vacSF = 0 := Lsf_vacuum (by omega)
  have hfin := sfTerm_support_finite (-(M : ℤ)) vacSF
  rw [Xop_apply, h0, map_zero, show (M : ℤ) + -(M : ℤ) = 0 from by ring,
    Lsf_vacuum (by norm_num : (-1 : ℤ) ≤ 0), smul_zero, sub_zero, sub_zero]
  have h1 : Lsf (M : ℤ) (Lsf (-(M : ℤ)) vacSF)
      = ∑ᶠ j : ℤ, Lsf (M : ℤ) (sfTerm (-(M : ℤ)) j vacSF) := by
    change Lsf (M : ℤ) (∑ᶠ j : ℤ, sfTerm (-(M : ℤ)) j vacSF) = _
    exact map_finsum (Lsf (M : ℤ)) hfin
  rw [h1, finsum_congr (fun j => Lsf_sfTerm_vac M j),
    ← finsum_smul' (gateSF_support_finite M) vacSF, gateSF_sum]

theorem Xop_central (m : ℤ) :
    Xop m (-m) vacSF = (-(((m : ℂ) ^ 3 - (m : ℂ)) / 6)) • vacSF := by
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

/-! ## §H  The Virasoro relation -/

/-- **The Virasoro algebra at `c = -2` for symplectic fermions**:
`[Lₘ, Lₙ] = (m-n)L_{m+n} + δ_{m+n,0}·(m³-m)/12·(-2)·id`. -/
theorem Lsf_virasoro (m n : ℤ) :
    Lsf m * Lsf n - Lsf n * Lsf m
      = ((m : ℂ) - (n : ℂ)) • Lsf (m + n)
        + (if m + n = 0 then ((m : ℂ) ^ 3 - (m : ℂ)) / 12 * (-2) else 0)
            • (1 : Module.End ℂ FockSF) := by
  have hX : Xop m n
      = (if m + n = 0 then ((m : ℂ) ^ 3 - (m : ℂ)) / 12 * (-2) else 0)
          • (1 : Module.End ℂ FockSF) := by
    by_cases h : m + n = 0
    · have hn : n = -m := by omega
      subst hn
      rw [if_pos h]
      refine eq_smul_of_comm_of_vac _ _ (Xop_comm_creBase m (-m)) ?_
      rw [Xop_central m]
      congr 1
      ring
    · rw [if_neg h, zero_smul]
      have hz := eq_smul_of_comm_of_vac (Xop m n) 0 (Xop_comm_creBase m n)
        (by rw [Xop_vac_zero h, zero_smul])
      rw [hz, zero_smul]
  rw [Xop, sub_eq_iff_eq_add'] at hX
  exact hX

/-- The same statement with `LinearMap.id`, matching `Examples/VirasoroFock.Lld_virasoro`. -/
theorem Lsf_virasoro_id (m n : ℤ) :
    Lsf m * Lsf n - Lsf n * Lsf m
      = ((m : ℂ) - (n : ℂ)) • Lsf (m + n)
        + (if m + n = 0 then ((m : ℂ) ^ 3 - (m : ℂ)) / 12 * (-2) else 0)
            • (LinearMap.id : Module.End ℂ FockSF) :=
  Lsf_virasoro m n

/-! ## §I  `L₋₁ = T`, and the conformal vector

`T` (`Examples/SymplecticFermionT`) is the translation operator the vertex-operator side uses.
It satisfies exactly the commutation relation `L₋₁` does, so the two agree on the spanning set. -/

/-- `L₋₁` **is** the repo's translation operator `T`.  Both are the derivation raising each
creation index by one with weight `k+1`, and both kill the vacuum. -/
theorem Lsf_neg_one_eq_T : Lsf (-1) = T := by
  refine LinearMap.ext_on stWordSF_span ?_
  rintro x ⟨l, rfl⟩
  induction l with
  | nil =>
      rw [stWordSF_nil]
      change Lsf (-1) vacSF = T (1 : FockSF)
      rw [Lsf_vacuum (le_refl _), T_one]
  | cons p rest ih =>
      have hcre : ι QSF (Finsupp.single p (1 : ℂ)) * stWordSF rest
          = creBase p (stWordSF rest) := rfl
      have hT := LinearMap.congr_fun (T_creBase p) (stWordSF rest)
      rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
        LinearMap.smul_apply, sub_eq_iff_eq_add] at hT
      have hL := Lsf_chiM_apply (-1) p.2 (-(p.1 : ℤ) - 1) (stWordSF rest)
      rw [chiM_creBase p, show (-1 : ℤ) + (-(p.1 : ℤ) - 1) = -((p.1 + 1 : ℕ) : ℤ) - 1 from by
        push_cast; ring, chiM_creBase (p.1 + 1, p.2)] at hL
      rw [stWordSF_cons, hcre, hL, ih, hT]
      push_cast
      module

/-- The **conformal vector** `ω = L₋₂|0⟩ = χ⁻₋₁χ⁺₋₁|0⟩`.  Only `j = -1` survives in `L₋₂|0⟩`:
any other `j` puts a nonnegative mode on the right of the normal ordering. -/
noncomputable def omegaSF : FockSF := Lsf (-2) vacSF

theorem omegaSF_eq : omegaSF = stWordSF [(0, 1), (0, 0)] := by
  have h : ∀ j : ℤ, j ≠ -1 → sfTerm (-2) j vacSF = 0 := by
    intro j hj
    by_cases hjn : j < 0
    · rw [sfTerm_apply, if_pos hjn, chiM_vac 0 (by omega : (0 : ℤ) ≤ -2 - j), map_zero]
    · exact sfTerm_vac_of_nonneg _ j (by omega)
  rw [omegaSF, Lsf_apply, finsum_eq_single _ (-1) h, sfTerm_apply,
    if_pos (by norm_num : (-1 : ℤ) < 0), show (-2 : ℤ) - -1 = -1 from by ring]
  rw [show (-1 : ℤ) = -((0 : ℕ) : ℤ) - 1 from by norm_num, chiM_creBase (0, 0),
    chiM_creBase (0, 1)]
  rw [stWordSF_cons, stWordSF_cons, stWordSF_nil]
  change ι QSF (Finsupp.single ((0, 1) : ℕ × Fin 2) (1 : ℂ))
      * (ι QSF (Finsupp.single ((0, 0) : ℕ × Fin 2) (1 : ℂ)) * (1 : FockSF)) = _
  rw [mul_one]

/-- `L₀ω = 2ω`: the conformal vector has weight `2`. -/
theorem Lsf_zero_omegaSF : Lsf 0 omegaSF = (2 : ℂ) • omegaSF := by
  rw [omegaSF, Lsf_zero_Lsf_vac (-2)]
  congr 1
  push_cast
  ring

/-- `L₁ω = 0`: the conformal vector is quasi-primary. -/
theorem Lsf_one_omegaSF : Lsf 1 omegaSF = 0 := by
  have h := LinearMap.congr_fun (Lsf_virasoro 1 (-2)) vacSF
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply,
    if_neg (by norm_num : ¬ ((1 : ℤ) + -2 = 0)), zero_smul, add_zero,
    show (1 : ℤ) + -2 = -1 from by ring, Lsf_vacuum (le_refl (-1 : ℤ)), smul_zero,
    Lsf_vacuum (by norm_num : (-1 : ℤ) ≤ 1), map_zero, sub_zero] at h
  rw [omegaSF, h]

/-- `L₂ω = -|0⟩ = (c/2)|0⟩` with `c = -2`: the central charge as a double contraction,
the analogue of `HeisenbergVirasoro.L_two_omega`. -/
theorem Lsf_two_omegaSF : Lsf 2 omegaSF = (-1 : ℂ) • vacSF := by
  have h := LinearMap.congr_fun (Lsf_virasoro 2 (-2)) vacSF
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply,
    if_pos (by norm_num : (2 : ℤ) + -2 = 0), show (2 : ℤ) + -2 = 0 from by ring,
    Lsf_vacuum (by norm_num : (-1 : ℤ) ≤ 0), smul_zero, zero_add,
    Lsf_vacuum (by norm_num : (-1 : ℤ) ≤ 2), map_zero, sub_zero] at h
  rw [omegaSF, h]
  congr 1
  push_cast
  ring

/-! ## §J  Non-degeneracy

A Virasoro relation on a zero module would be vacuously true, and a conformal vector that
happened to be `0` would make `L₂ω = (c/2)|0⟩` say nothing about `c`.  Both are ruled out here,
so the value `c = -2` is a real statement about a nonzero representation. -/

/-- The vacuum is nonzero (the Clifford algebra is nontrivial). -/
theorem vacSF_ne_zero : (vacSF : FockSF) ≠ 0 := one_ne_zero

/-- The conformal vector is nonzero: `L₂ω = -|0⟩ ≠ 0`. -/
theorem omegaSF_ne_zero : omegaSF ≠ 0 := by
  intro h
  have h2 : ((-1 : ℂ)) • (vacSF : FockSF) = 0 := by rw [← Lsf_two_omegaSF, h, map_zero]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 (by norm_num)
  · exact vacSF_ne_zero h3

/-- The modes act nontrivially: `L₂ ≠ 0`.  So the central term of `Lsf_virasoro` is not an
identity between zero operators. -/
theorem Lsf_two_ne_zero : Lsf 2 ≠ 0 := by
  intro h
  have h2 : ((-1 : ℂ)) • (vacSF : FockSF) = 0 := by
    rw [← Lsf_two_omegaSF, h, LinearMap.zero_apply]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 (by norm_num)
  · exact vacSF_ne_zero h3

end VOA.SympFerm.VirB
