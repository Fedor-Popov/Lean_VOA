/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchGate
import VOA.Modules.ZhuVermaAnArchDJ48
import VOA.Modules.ZhuRingResidue
import VOA.Modules.ZhuMuIdentity

/-!
# THE ZERO-MODE LAW on the bottom `Ω(M)` of a weak module

For every weak `𝒱`-module `M`, every `w ∈ Ω(M)`, homogeneous `u` of weight `k`, `v` of weight `l`,
and all `n, m, p ∈ ℕ`:

```
        o( u *ⁿ_{m,p} v ) w  =  u₍ₖ₋₁₊ₑ₎ v₍ₗ₋₁₋ₑ₎ w ,      e = p − n ,   INDEPENDENT OF m.
```

A **single monomial, with coefficient exactly `1`** — `oOmega_anmGen_law`.  The bundled, grade-free
form `oOmega_anmGen_law'` (arbitrary, non-homogeneous slots) reads

```
        o( u *ⁿ_{m,p} v ) w  =  o_{n,p}(u) · o_{p,n}(v) w        (`oLevW A (p−n)`, `oLevW A (n−p)`).
```

## Why the weak-module / `Ω(M)` level

The repo's existing Zhu layer (`ZhuModule.rhoLW`, `actA`, `ZeroModeMult.oMod_zhuMul_lowest`) is
stated for `OrdVModule`, which carries `finrank : ∀ α, FiniteDimensional ℂ (weight α)`.  The regular
module `U = A(𝒱)` is infinite dimensional already for the Heisenberg VOA, so that layer cannot be
fed the object B2 produces.  Everything here is therefore proved on

* `Omega A` — a `Submodule ℂ M` defined purely from a `WeakModule`: `w` killed by every mode
  `v₍ₙ₎` with `n ≥ wt v`.  No grading, no level family, no finiteness, no `L₀`.

and specialised afterwards to the `AdmLev` bottom level via `lev_zero_le_Omega : L.lev 0 ≤ Omega A`
(so all of it applies verbatim to `M̄₀(U)`, the interface `ZhuVermaAnArchGate` uses).

## What is proved here (all axiom-clean, `sorry`-free)

1. **The binomial cancellation** — `alt_cbz_shift_vanish`:
   `∑_{j=0}^{N} (−1)^j C(N,j) C(j−q, i) = 0` for `i < N`.  This is the *entire* cancellation content
   of the law; it is the proved `altShift_vanish` (a finite difference of a polynomial of degree
   `i < N`), restated in the `(−1)^j` normalisation, and consumed through the proved packaging
   `resHom_vOutside_coeff_vanish`.
2. **The `u`-outside expansion on `Ω(M)`** — `oOmega_resHom_uOutside`: the whole `v`-outside Jacobi
   family cancels identically, leaving a pure `u`-outside double sum.  (The `m = 0`, `D = 0` mirror
   of the proved `oLevW_resHom_uOutside`, re-proved over `Ω(M)` because `Ω(M)` has no level family.)
3. **The residue law** — `oOmega_resHom_law`:
   `o(Res_z (1+z)^{wt u+s} z^{−q} Y(u,z)v) w = ∑_{d≥0} C(s−d, s−q+1−d) · u₍ₖ₋₁₊d₎ v₍ₗ₋₁₋d₎ w`,
   the `u`-outside family Vandermonde-collapsed offset by offset (`zeroModeCoeff_collapse`).
4. **THE LAW** — `oOmega_anmGen_law` (homogeneous slots) and `oOmega_anmGen_law'` (all slots):
   the outer Dong–Jiang weights collapse to a Kronecker delta at `d = e = p − n`
   (`zeroModeOuter_collapse`).
5. **The structural corollaries**:
   * `oOmega_anmGen_vanish_of_lt` — `e < 0` (`p < n`) ⟹ `o(u *ⁿ_{m,p} v) w = 0`, since the surviving
     `v`-mode index is `≥ wt v` and kills `Ω(M)`;
   * `oOmega_anmGenBar_mult` — `e = 0` (`p = n`) ⟹ `o(u ∗̄ⁿ_m v) w = o(u) o(v) w`: **Zhu
     multiplicativity for the whole Dong–Jiang family**, for every `n` and `m`, generalising the
     proved `oLevW_zhuMul_lev_zero` (Gannon 5.3.9a) from `∗ = ∗̄⁰₀`;
   * `oOmega_anmRight_law` — the same law in the right-action (`p = m`) normalisation.
6. **B0** — `Onm_diag_annihilates_Omega`: `O_p(𝒱) = O'_{p,p}(𝒱)` annihilates `Ω(M)` for
   **every** `p` (Dong–Jiang Theorem 4.3 at the bottom level).  This is a **corollary of the law**,
   not a separate Dong–Li–Mason port: `anmCirc_eq_anmGen` identifies `u ∘ⁿ_m v = u *^{n+1}_{m,0} v`,
   whose `e = −(n+1) < 0`; the grading branch is the level-free proved `oLevW_anmLgen_vanish`.
   `O_annihilates_Omega` is the `p = 0` case (Zhu's classical statement).
7. **`DJCompositionLev` at `(n,m) = (0,0)`, every `p`** — `djCompositionLev_base`, in exactly the
   index shape of the carried hypothesis.
8. **Consistency anchor** — `oOmega_zhuMul_mult`: at `(n,m,p) = (0,0,0)` the law reproduces the
   independently-proved `oLevW_zhuMul_lev_zero`, pinning every sign and index.

## What is NOT proved here (the exact residual)

* `DJCompositionLev W` in general.  The law is a `D = 0`, `m_lev = 0` statement
  (`o = o_{0,0}` acting on the bottom); Dong–Jiang Lemma 4.1 is the `D = m − n` statement on the
  level-`m` piece.  The two agree at `n = m = 0` (item 7) and are **different statements**
  otherwise.  The intermediate-level instances that `oLevW_assocDefect_vanish` consumes
  (`hdj A L p₃ p₁ p₂ a b` with `w ∈ L.lev p₁`, `p₁ ≠ 0`) are NOT supplied here.
* Consequently the `(0,0)` gate `OnmFull W 0 0 ≤ O W` is **not** claimed.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`) §2 (the products `*ⁿ_{m,p}`, `O'/O''`),
§4 (`o_{n,m}`, Lemma 4.1, Thm 4.3);  Dong–Li–Mason, J. Algebra 206 (1998) 67–96 §2–3 (`Ω_n(M)`);
Gannon §5.3.2 (5.3.9a).  Repo: `ZhuVermaAnArchGate` (`AdmLev`, `oLevW`, `oLevW_anmLgen_vanish`),
`ZhuVermaAnArchGateB1` (`resHom_vOutside_coeff_vanish`), `ZhuVermaAnArchGradedModeVanish`
(`altShift_vanish`), `ZhuVermaAnArchDJ48` (`alt_cbz_eq`), `ZhuMuIdentity` (`ZhuMu.cbz_symm`),
`Foundations.IotaZExpansion` (`cbz_vandermonde`).
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## (0) Two generic bookkeeping lemmas for `ℤ`-indexed sums -/

/-- A `Finset.range` sum of an `ℤ`-indexed family supported in `[0, N)` is the full `ℤ`-`finsum`.
The `ℂ`-valued case is `ZhuRes.finsumZ_eq_range_sum`; this is the module-valued mirror. -/
theorem range_sum_eq_finsumZ {M : Type*} [AddCommMonoid M] (N : ℕ) (F : ℤ → M)
    (hF : ∀ x : ℤ, x < 0 ∨ (N : ℤ) ≤ x → F x = 0) :
    (∑ j ∈ Finset.range N, F (j : ℤ)) = ∑ᶠ x : ℤ, F x := by
  have hsubset : Function.support F ⊆ ↑((Finset.range N).map ⟨(Int.ofNat ·), by
      intro a b h; simpa using h⟩) := by
    intro p hp
    rw [Function.mem_support] at hp
    have hp0 : 0 ≤ p := by by_contra h; exact hp (hF p (Or.inl (by omega)))
    have hpN : p < (N : ℤ) := by by_contra h; exact hp (hF p (Or.inr (by omega)))
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Finset.mem_range,
      Function.Embedding.coeFn_mk]
    exact ⟨p.toNat, by omega, by simp [Int.toNat_of_nonneg hp0]⟩
  rw [finsum_eq_finsetSum_of_support_subset F hsubset, Finset.sum_map]
  rfl

/-- Shift-invariance of a `ℤ`-`finsum`. -/
theorem finsumZ_shift {M : Type*} [AddCommMonoid M] (F : ℤ → M) (c : ℤ) :
    (∑ᶠ d : ℤ, F (d + c)) = ∑ᶠ j : ℤ, F j :=
  finsum_comp_equiv (Equiv.addRight c)

/-! ## (1) The one binomial cancellation: a finite difference of a low-degree polynomial -/

/-- **The finite-difference identity** `∑_{j=0}^{N} (−1)^j C(N,j) C(j−q, i) = 0` for `i < N`:
the `N`-th finite difference annihilates the polynomial `x ↦ C(x−q, i)` of degree `i < N`.
This is the *entire* binomial cancellation content of the zero-mode law; it is the proved
`altShift_vanish`, restated in the `(-1)^j` normalisation. -/
theorem alt_cbz_shift_vanish (q : ℤ) {N i : ℕ} (hiN : i < N) :
    ∑ j ∈ Finset.range (N + 1),
      (-1 : ℂ) ^ j * cbz (N : ℤ) (j : ℤ) * cbz ((j : ℤ) - q) (i : ℤ) = 0 := by
  rw [← altShift_vanish (c := q) (M := N) (j := i) hiN]
  exact Finset.sum_congr rfl fun j _ => by rw [negOnePow_natCast]

/-! ## (2) `Ω(M)` — the bottom of a **weak** module -/

section Omega

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **`Ω(M)`, the bottom of a weak module** (Dong–Li–Mason `Ω(M) = Ω₀(M)`): the vectors killed by
every mode `v₍ₙ₎` with `n ≥ wt v`.  No grading, no level family, no finiteness — this is the
weakest possible home for the zero-mode calculus, and in particular it accommodates an
infinite-dimensional bottom (which the repo's `OrdVModule` layer, carrying `finrank`, cannot). -/
def Omega (A : WeakModule W M) : Submodule ℂ M where
  carrier := {w : M | ∀ (β : ℤ) (v : 𝒱), v ∈ W.grading β → ∀ n : ℤ, β ≤ n → mode (A.YM v) n w = 0}
  add_mem' := by
    intro a b ha hb β v hv n hn
    rw [map_add, ha β v hv n hn, hb β v hv n hn, add_zero]
  zero_mem' := by
    intro β v hv n _
    rw [map_zero]
  smul_mem' := by
    intro c a ha β v hv n hn
    rw [map_smul, ha β v hv n hn, smul_zero]

@[simp] theorem mem_Omega (A : WeakModule W M) (w : M) :
    w ∈ Omega A ↔
      ∀ (β : ℤ) (v : 𝒱), v ∈ W.grading β → ∀ n : ℤ, β ≤ n → mode (A.YM v) n w = 0 := Iff.rfl

/-- The defining property of `Ω(M)`: high modes kill the bottom. -/
theorem Omega_mode_vanish {A : WeakModule W M} {w : M} (hw : w ∈ Omega A) {β : ℤ} {v : 𝒱}
    (hv : v ∈ W.grading β) {n : ℤ} (hn : β ≤ n) : mode (A.YM v) n w = 0 := hw β v hv n hn

/-- **The bottom level of an `AdmLev` sits inside `Ω(M)`.**  So every statement proved below over
`Ω(M)` specialises to `L.lev 0`, the interface `ZhuVermaAnArchGate` (and hence `M̄₀(U)`) uses. -/
theorem lev_zero_le_Omega {A : WeakModule W M} (L : AdmLev W A) : L.lev 0 ≤ Omega A := by
  intro w hw β v hv n hn
  exact modeW_vanish_of_lev L hv hw (by omega)

/-! ## (3) The `u`-outside expansion on `Ω(M)`

The `m = 0`, `D = 0` mirror of `oLevW_resHom_uOutside`, re-proved over `Ω(M)` (which carries no
level family at all).  The `v`-outside Jacobi family cancels identically by the finite-difference
identity of §1 (in the proved packaging `resHom_vOutside_coeff_vanish`). -/

/-- Per-pole Jacobi step on `Ω(M)`: both families kept, with explicit truncation bounds. -/
private theorem oOmega_smul_step (A : WeakModule W M) {k l : ℤ} {u v : 𝒱}
    (hu : u ∈ W.grading k) (hv : v ∈ W.grading l) {w : M} (hw : w ∈ Omega A) (ℓ B : ℤ)
    (hB : -k + ℓ + 2 ≤ B) :
    oLevW A 0 (W.smul u ℓ v) w
      = (∑ i ∈ Finset.Ico (0 : ℤ) B, (negOnePow i * cbz ℓ i) •
            mode (A.YM u) (ℓ - i) (mode (A.YM v) (k + l - ℓ - 2 + i) w))
        - ∑ i ∈ Finset.Ico (0 : ℤ) k,
            (negOnePow i * cbz ℓ i * negOnePow ℓ) •
              mode (A.YM v) (k + l - 2 - i) (mode (A.YM u) i w) := by
  classical
  have hgr : W.smul u ℓ v ∈ W.grading (k + l - ℓ - 1) := W.smul_mem_grading hu hv ℓ
  rw [oLevW_homogeneous A 0 hgr, show k + l - ℓ - 1 - 1 + 0 = k + l - ℓ - 2 from by ring,
    module_iterate0 A u v w ℓ (k + l - ℓ - 2)]
  set F : ℤ → M := fun i => (negOnePow i * cbz ℓ i) •
    mode (A.YM u) (ℓ - i) (mode (A.YM v) (k + l - ℓ - 2 + i) w) with hF
  set G : ℤ → M := fun i => (negOnePow i * cbz ℓ i * negOnePow ℓ) •
    mode (A.YM v) (k + l - 2 - i) (mode (A.YM u) i w) with hG
  have hFsupp : (Function.support F) ⊆ ↑(Finset.Ico (0 : ℤ) B) := by
    intro i hi
    simp only [hF, Function.mem_support] at hi
    simp only [Finset.coe_Ico, Set.mem_Ico]
    have h0 : 0 ≤ i := by
      by_contra hneg
      exact hi (by rw [cbz_apply_neg ℓ (by omega), mul_zero, zero_smul])
    refine ⟨h0, ?_⟩
    by_contra hge
    exact hi (by
      rw [Omega_mode_vanish hw hv (n := k + l - ℓ - 2 + i) (by omega), map_zero, smul_zero])
  have hGsupp : (Function.support G) ⊆ ↑(Finset.Ico (0 : ℤ) k) := by
    intro i hi
    simp only [hG, Function.mem_support] at hi
    simp only [Finset.coe_Ico, Set.mem_Ico]
    have h0 : 0 ≤ i := by
      by_contra hneg
      exact hi (by rw [cbz_apply_neg ℓ (by omega), mul_zero, zero_mul, zero_smul])
    refine ⟨h0, ?_⟩
    by_contra hge
    exact hi (by rw [Omega_mode_vanish hw hu (n := i) (by omega), map_zero, smul_zero])
  have hsplit : ∀ i : ℤ, (negOnePow i * cbz ℓ i) •
      (mode (A.YM u) (ℓ - i) (mode (A.YM v) (k + l - ℓ - 2 + i) w)
        - negOnePow ℓ • mode (A.YM v) (ℓ + (k + l - ℓ - 2) - i) (mode (A.YM u) i w))
      = F i - G i := by
    intro i
    rw [hF, hG, smul_sub, smul_smul, show ℓ + (k + l - ℓ - 2) - i = k + l - 2 - i from by ring]
  rw [funext hsplit, finsum_sub_distrib (Set.Finite.subset (Finset.Ico (0 : ℤ) B).finite_toSet
      hFsupp) (Set.Finite.subset (Finset.Ico (0 : ℤ) k).finite_toSet hGsupp),
    finsum_eq_sum_of_support_subset _ hFsupp, finsum_eq_sum_of_support_subset _ hGsupp]

/-- **The `u`-outside expansion on `Ω(M)`.**  For `s ≥ 0` and homogeneous `u ∈ 𝒱ₖ`, `v ∈ 𝒱ₗ`, the
zero mode of the generic residue `Res_z (1+z)^{wt u + s} z^{−q} Y(u,z)v` on the bottom is a **pure
`u`-outside** double sum; the whole `v`-outside Jacobi family cancels identically. -/
theorem oOmega_resHom_uOutside (A : WeakModule W M) {s : ℤ} (hs : 0 ≤ s) (q : ℤ) {k l : ℤ}
    (hk : 0 ≤ k) {u v : 𝒱} (hu : u ∈ W.grading k) (hv : v ∈ W.grading l) {w : M}
    (hw : w ∈ Omega A) :
    oLevW A 0 (resHom W s q u v) w
      = ∑ j ∈ Finset.range ((k + s).toNat + 1),
          ∑ i ∈ Finset.Ico (0 : ℤ) (s - q + 2),
            (cbz (k + s) (j : ℤ) * (negOnePow i * cbz ((j : ℤ) - q) i)) •
              mode (A.YM u) ((j : ℤ) - q - i)
                (mode (A.YM v) (k + l - ((j : ℤ) - q) - 2 + i) w) := by
  classical
  have hks : (0 : ℤ) ≤ k + s := by omega
  rw [resHom_homogeneous W s q hu v, map_sum, LinearMap.coe_sum, Finset.sum_apply]
  have hstep : ∀ j ∈ Finset.range ((k + s).toNat + 1),
      (oLevW A 0 (cbz (k + s) (j : ℤ) • W.smul u ((j : ℤ) - q) v)) w
        = (∑ i ∈ Finset.Ico (0 : ℤ) (s - q + 2),
              (cbz (k + s) (j : ℤ) * (negOnePow i * cbz ((j : ℤ) - q) i)) •
                mode (A.YM u) ((j : ℤ) - q - i)
                  (mode (A.YM v) (k + l - ((j : ℤ) - q) - 2 + i) w))
          - ∑ i ∈ Finset.Ico (0 : ℤ) k,
              (cbz (k + s) (j : ℤ) *
                (negOnePow i * cbz ((j : ℤ) - q) i * negOnePow ((j : ℤ) - q))) •
                mode (A.YM v) (k + l - 2 - i) (mode (A.YM u) i w) := by
    intro j hj
    have hjle : (j : ℤ) ≤ k + s := by
      have hj' : j ≤ (k + s).toNat := by
        simp only [Finset.mem_range] at hj; omega
      omega
    have hB : -k + ((j : ℤ) - q) + 2 ≤ s - q + 2 := by omega
    rw [map_smul, LinearMap.smul_apply,
      oOmega_smul_step A hu hv hw ((j : ℤ) - q) (s - q + 2) hB, smul_sub, Finset.smul_sum,
      Finset.smul_sum]
    congr 1 <;> exact Finset.sum_congr rfl (fun i _ => by rw [smul_smul])
  rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib]
  have hY : ∑ j ∈ Finset.range ((k + s).toNat + 1),
      ∑ i ∈ Finset.Ico (0 : ℤ) k,
        (cbz (k + s) (j : ℤ) *
          (negOnePow i * cbz ((j : ℤ) - q) i * negOnePow ((j : ℤ) - q))) •
          mode (A.YM v) (k + l - 2 - i) (mode (A.YM u) i w) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    simp only [Finset.mem_Ico] at hi
    rw [← Finset.sum_smul, resHom_vOutside_coeff_vanish (k + s) q hks hi.1 (by omega), zero_smul]
  rw [hY, sub_zero]

end Omega

/-! ## (4) Reindexing a `cbz`-supported sum by the `u`-mode offset -/

/-- **The reindexing step.**  A sum over the `cbz`-row `[0, P]` of vectors `T (j − c)` is the same
as the sum over the offsets `d ∈ [0, E)` of `T d`, provided `T` vanishes in negative offsets (this
is the `Ω(M)` input) and the `cbz`-row has run out past `E`. -/
private theorem sum_reindex_cbz {N : Type*} [AddCommMonoid N] [Module ℂ N] {P : ℤ} (hP : 0 ≤ P)
    (c E : ℤ) (f : ℤ → ℂ) (T : ℤ → N) (hT : ∀ d : ℤ, d < 0 → T d = 0)
    (hhi : ∀ d : ℤ, E ≤ d → P < d + c) :
    (∑ j ∈ Finset.range (P.toNat + 1), (cbz P (j : ℤ) * f (j : ℤ)) • T ((j : ℤ) - c))
      = ∑ d ∈ Finset.Ico (0 : ℤ) E, (cbz P (d + c) * f (d + c)) • T d := by
  classical
  have hcast : ((P.toNat : ℕ) : ℤ) = P := Int.toNat_of_nonneg hP
  rw [range_sum_eq_finsumZ (P.toNat + 1) (fun j : ℤ => (cbz P j * f j) • T (j - c)) (by
      intro x hx
      dsimp only
      rcases hx with hx | hx
      · rw [cbz_apply_neg P hx, zero_mul, zero_smul]
      · have : ((P.toNat + 1 : ℕ) : ℤ) = P + 1 := by push_cast [hcast]; ring
        rw [cbz_lt hP (by omega : P < x), zero_mul, zero_smul]),
    ← finsumZ_shift (fun j : ℤ => (cbz P j * f j) • T (j - c)) c,
    show (fun d : ℤ => (cbz P (d + c) * f (d + c)) • T (d + c - c))
        = (fun d : ℤ => (cbz P (d + c) * f (d + c)) • T d) from
      funext (fun d => by rw [add_sub_cancel_right])]
  refine finsum_eq_sum_of_support_subset _ ?_
  intro d hd
  simp only [Function.mem_support] at hd
  simp only [Finset.coe_Ico, Set.mem_Ico]
  constructor
  · by_contra h
    exact hd (by rw [hT d (by omega), smul_zero])
  · by_contra h
    exact hd (by rw [cbz_lt hP (hhi d (by omega)), zero_mul, zero_smul])

/-! ## (5) The two scalar collapses (pure `cbz` combinatorics) -/

/-- **First Vandermonde collapse.**  For `d ≥ 0` the whole `j`-sum of the `u`-outside expansion,
collected at a fixed `u`-mode offset `d`, is the single generalized binomial `C(s−d, s−q+1−d)`.
Upper-index negation (`alt_cbz_eq`) turns the alternating factor into an ordinary `cbz`, binomial
symmetry (`ZhuMu.cbz_symm`) reverses the `(k+s)`-row, and `cbz_vandermonde` convolves. -/
theorem zeroModeCoeff_collapse {k s : ℤ} (hk : 0 ≤ k) (hs : 0 ≤ s) (q : ℤ) {d : ℤ} (hd : 0 ≤ d) :
    (∑ i ∈ Finset.Ico (0 : ℤ) (s - q + 2),
        cbz (k + s) (d + (q + i + k - 1)) * (negOnePow i * cbz (d + (q + i + k - 1) - q) i))
      = cbz (s - d) (s - q + 1 - d) := by
  classical
  have hks : (0 : ℤ) ≤ k + s := by omega
  have hcast : (((k + s).toNat : ℕ) : ℤ) = k + s := Int.toNat_of_nonneg hks
  -- Termwise rewrite into a genuine convolution.
  have hterm : ∀ i : ℤ,
      cbz (k + s) (d + (q + i + k - 1)) * (negOnePow i * cbz (d + (q + i + k - 1) - q) i)
        = cbz (-k - d) i * cbz (k + s) ((s - q + 1 - d) - i) := by
    intro i
    rcases lt_or_ge i 0 with hi | hi
    · rw [cbz_apply_neg _ hi, cbz_apply_neg (-k - d) hi, mul_zero, zero_mul, mul_zero]
    · obtain ⟨I, rfl⟩ : ∃ I : ℕ, i = (I : ℤ) := ⟨i.toNat, by omega⟩
      have halt : negOnePow (I : ℤ) * cbz (d + (q + (I : ℤ) + k - 1) - q) (I : ℤ)
          = cbz (-k - d) (I : ℤ) := by
        rw [negOnePow_natCast, show d + (q + (I : ℤ) + k - 1) - q = (k - 1 + d) + (I : ℤ) from by
          ring, alt_cbz_eq (k - 1 + d) I, show -(k - 1 + d) - 1 = -k - d from by ring]
      rw [halt, show cbz (k + s) (d + (q + (I : ℤ) + k - 1))
            = cbz (((k + s).toNat : ℕ) : ℤ) (d + (q + (I : ℤ) + k - 1)) from by rw [hcast],
        ZhuMu.cbz_symm, hcast,
        show k + s - (d + (q + (I : ℤ) + k - 1)) = (s - q + 1 - d) - (I : ℤ) from by ring, mul_comm]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  -- Extend to a `ℤ`-finsum and apply Vandermonde.
  have hsupp : (Function.support
      (fun i : ℤ => cbz (-k - d) i * cbz (k + s) ((s - q + 1 - d) - i)))
        ⊆ ↑(Finset.Ico (0 : ℤ) (s - q + 2)) := by
    intro i hi
    simp only [Function.mem_support] at hi
    simp only [Finset.coe_Ico, Set.mem_Ico]
    constructor
    · by_contra h
      exact hi (by rw [cbz_apply_neg (-k - d) (by omega), zero_mul])
    · by_contra h
      exact hi (by rw [cbz_apply_neg (k + s) (by omega), mul_zero])
  rw [← finsum_eq_sum_of_support_subset _ hsupp,
    show (∑ᶠ i : ℤ, cbz (-k - d) i * cbz (k + s) ((s - q + 1 - d) - i))
      = cbzConvol (-k - d) (k + s) (s - q + 1 - d) from rfl,
    cbz_vandermonde, show -k - d + (k + s) = s - d from by ring]

/-- **Second Vandermonde collapse — the Kronecker delta.**  Summing the outer Dong–Jiang weights
`(−1)^t C(m+n−p+t, t)` against the first collapse produces `C(e−1−d, e−d)`, which is `1` exactly at
`d = e = p − n` and `0` at every other `d ≥ 0`.  This is where the single surviving monomial of the
zero-mode law comes from. -/
theorem zeroModeOuter_collapse {m e : ℤ} (p : ℕ) (hp : (p : ℤ) - e ≥ 0) {d : ℤ} (hd : 0 ≤ d) :
    (∑ t ∈ Finset.range (p + 1),
        ((-1 : ℂ) ^ t * cbz (m - e + (t : ℤ)) (t : ℤ)) * cbz (m - d) (e - (t : ℤ) - d))
      = cbz (e - 1 - d) (e - d) := by
  classical
  have hterm : ∀ t : ℕ,
      ((-1 : ℂ) ^ t * cbz (m - e + (t : ℤ)) (t : ℤ)) * cbz (m - d) (e - (t : ℤ) - d)
        = cbz (e - m - 1) (t : ℤ) * cbz (m - d) ((e - d) - (t : ℤ)) := by
    intro t
    rw [alt_cbz_eq (m - e) t, show -(m - e) - 1 = e - m - 1 from by ring,
      show e - (t : ℤ) - d = (e - d) - (t : ℤ) from by ring]
  rw [Finset.sum_congr rfl (fun t _ => hterm t),
    range_sum_eq_finsumZ (p + 1) (fun t : ℤ => cbz (e - m - 1) t * cbz (m - d) ((e - d) - t))
      (by
        intro x hx
        dsimp only
        rcases hx with hx | hx
        · rw [cbz_apply_neg (e - m - 1) hx, zero_mul]
        · have hxp : ((p + 1 : ℕ) : ℤ) = (p : ℤ) + 1 := by push_cast; ring
          rw [cbz_apply_neg (m - d) (by omega : e - d - x < 0), mul_zero]),
    show (∑ᶠ t : ℤ, cbz (e - m - 1) t * cbz (m - d) ((e - d) - t))
      = cbzConvol (e - m - 1) (m - d) (e - d) from rfl,
    cbz_vandermonde, show e - m - 1 + (m - d) = e - 1 - d from by ring]

/-! ## (6) THE ZERO-MODE LAW -/

section Law

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **The residue law on `Ω(M)`.**  For homogeneous `u ∈ 𝒱ₖ`, `v ∈ 𝒱ₗ` and `s ≥ 0`,
`o(Res_z (1+z)^{wt u + s} z^{−q} Y(u,z)v) w` is, on the bottom, the finite sum of the monomials
`u₍ₖ₋₁₊d₎ v₍ₗ₋₁₋d₎ w` with the single generalized-binomial weight `C(s−d, s−q+1−d)`.
Every `v`-outside term has already cancelled (`oOmega_resHom_uOutside`); the `u`-outside family
Vandermonde-collapses offset by offset (`zeroModeCoeff_collapse`).  The offsets `d < 0` are absent
because they carry a `v`-mode `≥ wt v`, which kills `Ω(M)`. -/
theorem oOmega_resHom_law (A : WeakModule W M) {s : ℤ} (hs : 0 ≤ s) (q : ℤ) {k l : ℤ}
    (hk : 0 ≤ k) {u v : 𝒱} (hu : u ∈ W.grading k) (hv : v ∈ W.grading l) {w : M}
    (hw : w ∈ Omega A) :
    oLevW A 0 (resHom W s q u v) w
      = ∑ d ∈ Finset.Ico (0 : ℤ) (s - q + 2),
          cbz (s - d) (s - q + 1 - d) •
            mode (A.YM u) (k - 1 + d) (mode (A.YM v) (l - 1 - d) w) := by
  classical
  rw [oOmega_resHom_uOutside A hs q hk hu hv hw, Finset.sum_comm]
  have hstep : ∀ i ∈ Finset.Ico (0 : ℤ) (s - q + 2),
      (∑ j ∈ Finset.range ((k + s).toNat + 1),
          (cbz (k + s) (j : ℤ) * (negOnePow i * cbz ((j : ℤ) - q) i)) •
            mode (A.YM u) ((j : ℤ) - q - i)
              (mode (A.YM v) (k + l - ((j : ℤ) - q) - 2 + i) w))
        = ∑ d ∈ Finset.Ico (0 : ℤ) (s - q + 2),
            (cbz (k + s) (d + (q + i + k - 1)) *
                (negOnePow i * cbz (d + (q + i + k - 1) - q) i)) •
              mode (A.YM u) (k - 1 + d) (mode (A.YM v) (l - 1 - d) w) := by
    intro i hi
    simp only [Finset.mem_Ico] at hi
    have hkey := sum_reindex_cbz (P := k + s) (by omega) (q + i + k - 1) (s - q + 2)
      (fun x : ℤ => negOnePow i * cbz (x - q) i)
      (fun d : ℤ => mode (A.YM u) (k - 1 + d) (mode (A.YM v) (l - 1 - d) w))
      (fun d hd => by
        dsimp only
        rw [Omega_mode_vanish hw hv (n := l - 1 - d) (by omega), map_zero])
      (fun d hd => by omega)
    refine Eq.trans ?_ hkey
    refine Finset.sum_congr rfl (fun j _ => ?_)
    dsimp only
    rw [show k - 1 + ((j : ℤ) - (q + i + k - 1)) = (j : ℤ) - q - i from by ring,
      show l - 1 - ((j : ℤ) - (q + i + k - 1)) = k + l - ((j : ℤ) - q) - 2 + i from by ring]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  simp only [Finset.mem_Ico] at hd
  rw [← Finset.sum_smul, zeroModeCoeff_collapse hk hs q hd.1]

/-- **THE ZERO-MODE LAW.**  For every weak module `M`, every `w ∈ Ω(M)`, homogeneous `u` of
weight `k` and `v` of weight `l`, and all `n, m, p`,

`o( u *ⁿ_{m,p} v ) w  =  u₍ₖ₋₁₊ₑ₎ v₍ₗ₋₁₋ₑ₎ w`,   `e = p − n`,   **independently of `m`**.

A single monomial, with coefficient exactly `1`.  The whole `v`-outside Jacobi family cancels by
the finite-difference identity (§1), the `u`-outside family Vandermonde-collapses offset by offset
(`zeroModeCoeff_collapse`), and the outer Dong–Jiang weights collapse to a Kronecker delta at
`d = e` (`zeroModeOuter_collapse`).  No `OrdVModule`, no grading of `M`, no finiteness. -/
theorem oOmega_anmGen_law (A : WeakModule W M) (n m p : ℕ) {k l : ℤ} (hk : 0 ≤ k) {u v : 𝒱}
    (hu : u ∈ W.grading k) (hv : v ∈ W.grading l) {w : M} (hw : w ∈ Omega A) :
    oLevW A 0 (anmGen W n m p u v) w
      = mode (A.YM u) (k - 1 + ((p : ℤ) - (n : ℤ)))
          (mode (A.YM v) (l - 1 - ((p : ℤ) - (n : ℤ))) w) := by
  classical
  set e : ℤ := (p : ℤ) - (n : ℤ) with he
  set Tf : ℤ → M := fun d => mode (A.YM u) (k - 1 + d) (mode (A.YM v) (l - 1 - d) w) with hTf
  have hT0 : ∀ d : ℤ, d < 0 → Tf d = 0 := by
    intro d hd
    rw [hTf]
    dsimp only
    rw [Omega_mode_vanish hw hv (n := l - 1 - d) (by omega), map_zero]
  rw [anmGen, map_sum, LinearMap.coe_sum, Finset.sum_apply]
  have hterm : ∀ t ∈ Finset.range (p + 1),
      (oLevW A 0 (((-1 : ℂ) ^ t * cbz ((m : ℤ) + (n : ℤ) - (p : ℤ) + (t : ℤ)) (t : ℤ))
          • resHom W (m : ℤ) ((m : ℤ) + (n : ℤ) - (p : ℤ) + (t : ℤ) + 1) u v)) w
        = ∑ d ∈ Finset.Ico (0 : ℤ) (e + 1),
            (((-1 : ℂ) ^ t * cbz ((m : ℤ) - e + (t : ℤ)) (t : ℤ))
              * cbz ((m : ℤ) - d) (e - (t : ℤ) - d)) • Tf d := by
    intro t _
    rw [map_smul, LinearMap.smul_apply, oOmega_resHom_law A (Int.natCast_nonneg m)
      ((m : ℤ) + (n : ℤ) - (p : ℤ) + (t : ℤ) + 1) hk hu hv hw,
      show (m : ℤ) - ((m : ℤ) + (n : ℤ) - (p : ℤ) + (t : ℤ) + 1) + 2 = e - (t : ℤ) + 1 from by
        rw [he]; ring,
      Finset.smul_sum]
    have hcoef : ∀ d : ℤ,
        ((-1 : ℂ) ^ t * cbz ((m : ℤ) + (n : ℤ) - (p : ℤ) + (t : ℤ)) (t : ℤ)) •
            (cbz ((m : ℤ) - d)
              ((m : ℤ) - ((m : ℤ) + (n : ℤ) - (p : ℤ) + (t : ℤ) + 1) + 1 - d) • Tf d)
          = (((-1 : ℂ) ^ t * cbz ((m : ℤ) - e + (t : ℤ)) (t : ℤ))
              * cbz ((m : ℤ) - d) (e - (t : ℤ) - d)) • Tf d := by
      intro d
      rw [smul_smul,
        show (m : ℤ) - ((m : ℤ) + (n : ℤ) - (p : ℤ) + (t : ℤ) + 1) + 1 - d = e - (t : ℤ) - d from by
          rw [he]; ring,
        show (m : ℤ) + (n : ℤ) - (p : ℤ) + (t : ℤ) = (m : ℤ) - e + (t : ℤ) from by rw [he]; ring]
    rw [Finset.sum_congr rfl (fun d _ => hcoef d)]
    refine Finset.sum_subset (Finset.Ico_subset_Ico le_rfl (by omega)) (fun d hd hd' => ?_)
    simp only [Finset.mem_Ico, not_and, not_lt] at hd hd'
    rw [cbz_apply_neg ((m : ℤ) - d) (by omega : e - (t : ℤ) - d < 0), mul_zero, zero_smul]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  have hcollapse : ∀ d ∈ Finset.Ico (0 : ℤ) (e + 1),
      (∑ t ∈ Finset.range (p + 1),
        (((-1 : ℂ) ^ t * cbz ((m : ℤ) - e + (t : ℤ)) (t : ℤ))
          * cbz ((m : ℤ) - d) (e - (t : ℤ) - d)) • Tf d)
        = cbz (e - 1 - d) (e - d) • Tf d := by
    intro d hd
    simp only [Finset.mem_Ico] at hd
    rw [← Finset.sum_smul, zeroModeOuter_collapse p (by rw [he]; omega) hd.1]
  rw [Finset.sum_congr rfl hcollapse]
  rcases lt_or_ge e 0 with hneg | hpos
  · rw [show Finset.Ico (0 : ℤ) (e + 1) = (∅ : Finset ℤ) from Finset.Ico_eq_empty (by omega),
      Finset.sum_empty]
    exact (hT0 e hneg).symm
  · rw [Finset.sum_eq_single_of_mem e (by simp only [Finset.mem_Ico]; omega)
      (fun b hb hbe => ?_)]
    · rw [show e - 1 - e = -1 from by ring, show e - e = (0 : ℤ) from by ring, cbz_zero, one_smul]
    · simp only [Finset.mem_Ico] at hb
      rw [cbz_lt (by omega : (0 : ℤ) ≤ e - 1 - b) (by omega : e - 1 - b < e - b), zero_smul]

/-! ### The bundled (grade-free) form, valid for arbitrary slots -/

/-- A **strictly positive** level shift kills the bottom: `o_{n,m}` with `m > n` annihilates `Ω(M)`,
for every `v` (no homogeneity needed). -/
theorem oLevW_vanish_of_pos (A : WeakModule W M) {d : ℤ} (hd : 0 < d) (v : 𝒱) {w : M}
    (hw : w ∈ Omega A) : oLevW A d v w = 0 := by
  have hvtop : v ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading (motive := fun v => oLevW A d v w = 0) hvtop ?_ ?_ ?_
  · intro i y hy
    rw [oLevW_homogeneous A d hy]
    exact Omega_mode_vanish hw hy (by omega)
  · change oLevW A d 0 w = 0
    rw [map_zero, LinearMap.zero_apply]
  · intro y z hy hz
    change oLevW A d (y + z) w = 0
    rw [map_add, LinearMap.add_apply, hy, hz, add_zero]

/-- **THE ZERO-MODE LAW, bundled form** — `u`, `v` arbitrary (not necessarily homogeneous):

`o( u *ⁿ_{m,p} v ) w  =  o_{n,p}(u) · o_{p,n}(v) w`  for `w ∈ Ω(M)`,

with the two level-shifted zero modes `oLevW A (p−n)` and `oLevW A (n−p)`.  On homogeneous slots
this is exactly `oOmega_anmGen_law`; both sides are `ℂ`-bilinear in `(u,v)`, so it extends to all
of `𝒱 × 𝒱`.  Note the **`m`-independence**: the right-hand side does not mention `m`. -/
theorem oOmega_anmGen_law' (A : WeakModule W M) (n m p : ℕ) (u v : 𝒱) {w : M} (hw : w ∈ Omega A) :
    oLevW A 0 (anmGen W n m p u v) w
      = oLevW A ((p : ℤ) - (n : ℤ)) u (oLevW A ((n : ℤ) - (p : ℤ)) v w) := by
  have hzeroL : ∀ y : 𝒱, anmGen W n m p (0 : 𝒱) y = 0 := by
    intro y
    have := anmGen_smul_left W n m p (0 : ℂ) (0 : 𝒱) y
    rwa [zero_smul, zero_smul] at this
  have hzeroR : ∀ y : 𝒱, anmGen W n m p y (0 : 𝒱) = 0 := by
    intro y
    have := anmGen_smul_right W n m p (0 : ℂ) y (0 : 𝒱)
    rwa [zero_smul, zero_smul] at this
  have key : ∀ (k : ℤ) (u' : 𝒱), u' ∈ W.grading k → ∀ v' : 𝒱,
      oLevW A 0 (anmGen W n m p u' v') w
        = oLevW A ((p : ℤ) - (n : ℤ)) u' (oLevW A ((n : ℤ) - (p : ℤ)) v' w) := by
    intro k u' hu' v'
    rcases lt_or_ge k 0 with hneg | hpos
    · rw [W.positivity k hneg, Submodule.mem_bot] at hu'
      subst hu'
      simp only [hzeroL, map_zero, LinearMap.zero_apply]
    · have hvtop : v' ∈ ⨆ i, W.grading i := by
        rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
      refine Submodule.iSup_induction W.grading
        (motive := fun v' => oLevW A 0 (anmGen W n m p u' v') w
          = oLevW A ((p : ℤ) - (n : ℤ)) u' (oLevW A ((n : ℤ) - (p : ℤ)) v' w)) hvtop ?_ ?_ ?_
      · intro i y hy
        rw [oOmega_anmGen_law A n m p hpos hu' hy hw, oLevW_homogeneous A _ hu',
          oLevW_homogeneous A _ hy,
          show i - 1 + ((n : ℤ) - (p : ℤ)) = i - 1 - ((p : ℤ) - (n : ℤ)) from by ring]
      · change oLevW A 0 (anmGen W n m p u' 0) w = _
        simp only [hzeroR, map_zero, LinearMap.zero_apply]
      · intro y z hy hz
        change oLevW A 0 (anmGen W n m p u' (y + z)) w = _
        rw [anmGen_add_right, map_add, LinearMap.add_apply, hy, hz, map_add, LinearMap.add_apply,
          map_add]
  have hutop : u ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun u => oLevW A 0 (anmGen W n m p u v) w
      = oLevW A ((p : ℤ) - (n : ℤ)) u (oLevW A ((n : ℤ) - (p : ℤ)) v w)) hutop ?_ ?_ ?_
  · intro i y hy
    exact key i y hy v
  · change oLevW A 0 (anmGen W n m p 0 v) w = _
    simp only [hzeroL, map_zero, LinearMap.zero_apply]
  · intro y z hy hz
    change oLevW A 0 (anmGen W n m p (y + z) v) w = _
    rw [anmGen_add_left, map_add, LinearMap.add_apply, hy, hz, map_add, LinearMap.add_apply]

end Law

/-! ## (7) The structural corollaries -/

/-- The Dong–Jiang **circle generator is a `p = 0` instance of the general product**, one index up:
`u ∘ⁿ_m v = u *^{n+1}_{m,0} v` (both are `Res_z (1+z)^{wt u + m} z^{−(n+m+2)} Y(u,z)v`).  This is
what makes the `O'`-branch of `B0` a corollary of the zero-mode law rather than a separate port. -/
theorem anmCirc_eq_anmGen (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (u v : 𝒱) :
    anmCirc W n m u v = anmGen W (n + 1) m 0 u v := by
  rw [anmCirc, anmGen, Finset.sum_range_one]
  simp only [Nat.cast_zero, pow_zero, cbz_zero, mul_one, one_smul, add_zero, sub_zero]
  rw [show (m : ℤ) + ((n + 1 : ℕ) : ℤ) + 1 = (n : ℤ) + (m : ℤ) + 2 from by push_cast; ring]

section Corollaries

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **`e < 0` ⟹ zero.**  If `p < n` the surviving `v`-mode index is `≥ wt v`, so it kills the
bottom: `o(u *ⁿ_{m,p} v) w = 0` for every `w ∈ Ω(M)`, all `u, v`, every `m`. -/
theorem oOmega_anmGen_vanish_of_lt (A : WeakModule W M) {n m p : ℕ} (hpn : p < n) (u v : 𝒱)
    {w : M} (hw : w ∈ Omega A) : oLevW A 0 (anmGen W n m p u v) w = 0 := by
  rw [oOmega_anmGen_law' A n m p u v hw,
    oLevW_vanish_of_pos A (d := (n : ℤ) - (p : ℤ)) (by omega) v hw, map_zero]

/-- **`e = 0` ⟹ Zhu multiplicativity for the WHOLE Dong–Jiang family.**  At `p = n` the general
product is Dong–Jiang's left action `∗̄ⁿ_m`, and `o(u ∗̄ⁿ_m v) w = o(u) o(v) w` on the bottom — for
**every** `n` and `m`, generalising the repo's `oLevW_zhuMul_lev_zero` (5.3.9a) from the Zhu
product `∗ = ∗̄⁰₀` to the entire family. -/
theorem oOmega_anmGenBar_mult (A : WeakModule W M) (n m : ℕ) (u v : 𝒱) {w : M}
    (hw : w ∈ Omega A) :
    oLevW A 0 (anmGenBar W n m u v) w = oLevW A 0 u (oLevW A 0 v w) := by
  rw [anmGenBar, oOmega_anmGen_law' A n m n u v hw, sub_self]

/-- **B0, circle branch**: the Dong–Jiang circle generator annihilates the bottom, at every
level `n, m` — in particular `u ∘^p_p v` for every `p`. -/
theorem oOmega_anmCirc_vanish (A : WeakModule W M) (n m : ℕ) (u v : 𝒱) {w : M}
    (hw : w ∈ Omega A) : oLevW A 0 (anmCirc W n m u v) w = 0 := by
  rw [anmCirc_eq_anmGen W n m u v]
  exact oOmega_anmGen_vanish_of_lt A (Nat.zero_lt_succ n) u v hw

/-- **B0 — `O_p(𝒱) = O'_{p,p}(𝒱)` annihilates the bottom `Ω(M)`, for every `p`.**
Dong–Jiang Theorem 4.3 at the bottom level, obtained as a corollary of the zero-mode law
(circle branch) together with the level-free `oLevW_anmLgen_vanish` (grading branch) — not as a
separate body of Dong–Li–Mason theory. -/
theorem Onm_diag_annihilates_Omega (A : WeakModule W M) (p : ℕ) {x : 𝒱} (hx : x ∈ Onm W p p)
    {w : M} (hw : w ∈ Omega A) : oLevW A 0 x w = 0 := by
  have hle : Onm W p p ≤ levAnnW A 0 w := by
    simp only [Onm, OnmL]
    refine sup_le (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
    · rintro y ⟨c, d, rfl⟩
      exact oOmega_anmCirc_vanish A p p c d hw
    · rintro y ⟨c, rfl⟩
      have hz := oLevW_anmLgen_vanish A p p c
      rw [sub_self] at hz
      change oLevW A 0 (anmLgen W p p c) w = 0
      rw [hz, LinearMap.zero_apply]
  exact hle hx

/-- **Zhu's classical `O(𝒱)`-annihilation on the bottom** — the `p = 0` case. -/
theorem O_annihilates_Omega (A : WeakModule W M) {x : 𝒱} (hx : x ∈ O W) {w : M}
    (hw : w ∈ Omega A) : oLevW A 0 x w = 0 :=
  Onm_diag_annihilates_Omega A 0 (by rwa [Onm_zero_zero_eq_O]) hw

/-- **Dong–Jiang Lemma 4.1 at `(n,m) = (0,0)`, for every `p`** — in exactly the index shape of
`DJCompositionLev`.  This is the `n = m = 0` slice of the carried composition hypothesis, a
THEOREM (the general `(n,m)` slices are a different statement and are NOT proved here). -/
theorem djCompositionLev_base (A : WeakModule W M) (p : ℕ) (u v : 𝒱) {w : M} (hw : w ∈ Omega A) :
    oLevW A (((0 : ℕ) : ℤ) - ((0 : ℕ) : ℤ)) (anmGen W 0 0 p u v) w
      = oLevW A ((p : ℤ) - ((0 : ℕ) : ℤ)) u (oLevW A (((0 : ℕ) : ℤ) - (p : ℤ)) v w) := by
  have h := oOmega_anmGen_law' A 0 0 p u v hw
  simpa using h

/-- **Consistency anchor.**  At `(n,m,p) = (0,0,0)` the Dong–Jiang product is Zhu's, and the law
reproduces the independently proved `o(u ∗ v) w = o(u) o(v) w` (Gannon 5.3.9a,
`ZhuVermaAnArchGate.oLevW_zhuMul_lev_zero`).  Nothing about the normalisation is left to chance. -/
theorem oOmega_zhuMul_mult (A : WeakModule W M) (u v : 𝒱) {w : M} (hw : w ∈ Omega A) :
    oLevW A 0 (zhuMul W u v) w = oLevW A 0 u (oLevW A 0 v w) := by
  have hz : anmGen W 0 0 0 u v = zhuMul W u v := by
    rw [anmGen, Finset.range_one, Finset.sum_singleton]
    norm_num [resHom_zero_one]
  rw [← hz]
  have h := oOmega_anmGen_law' A 0 0 0 u v hw
  simpa using h

/-- **The law in the right-action (`p = m`) normalisation**:
`o(u *ⁿ_m v) w = o_{n,m}(u) o_{m,n}(v) w` on the bottom.  (`anmRight` is `*^n_{m,m}`.) -/
theorem oOmega_anmRight_law (A : WeakModule W M) (n m : ℕ) (u v : 𝒱) {w : M}
    (hw : w ∈ Omega A) :
    oLevW A 0 (anmRight W n m u v) w
      = oLevW A ((m : ℤ) - (n : ℤ)) u (oLevW A ((n : ℤ) - (m : ℤ)) v w) := by
  rw [← anmGen_eq_anmRight W n m u v]
  exact oOmega_anmGen_law' A n m m u v hw

/-! ### Specialisation to the `AdmLev` bottom level (the interface `M̄₀(U)` carries) -/

/-- The zero-mode law on the bottom level of a non-negatively levelled weak module. -/
theorem oLev_anmGen_law_lev_zero (A : WeakModule W M) (L : AdmLev W A) (n m p : ℕ) (u v : 𝒱)
    {w : M} (hw : w ∈ L.lev 0) :
    oLevW A 0 (anmGen W n m p u v) w
      = oLevW A ((p : ℤ) - (n : ℤ)) u (oLevW A ((n : ℤ) - (p : ℤ)) v w) :=
  oOmega_anmGen_law' A n m p u v (lev_zero_le_Omega L hw)

/-- `O_p(𝒱)` annihilates the bottom level of a non-negatively levelled weak module, every `p`. -/
theorem Onm_diag_annihilates_lev_zero (A : WeakModule W M) (L : AdmLev W A) (p : ℕ) {x : 𝒱}
    (hx : x ∈ Onm W p p) {w : M} (hw : w ∈ L.lev 0) : oLevW A 0 x w = 0 :=
  Onm_diag_annihilates_Omega A p hx (lev_zero_le_Omega L hw)

/-- Zhu multiplicativity for the whole Dong–Jiang family, on the bottom level. -/
theorem oLev_anmGenBar_mult_lev_zero (A : WeakModule W M) (L : AdmLev W A) (n m : ℕ) (u v : 𝒱)
    {w : M} (hw : w ∈ L.lev 0) :
    oLevW A 0 (anmGenBar W n m u v) w = oLevW A 0 u (oLevW A 0 v w) :=
  oOmega_anmGenBar_mult A n m u v (lev_zero_le_Omega L hw)

end Corollaries

end VOA
