/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUVhat
import VOA.Core.Borcherds

/-!
# The module Jacobi 5.3.1b for `M(U)` — reduced to a single residual identity

This file discharges the genuine remaining crux `VHat.VHatRep.IsModuleJacobi`
(`ZhuVermaAnArchMUVhat`) — the **module Borcherds identity 5.3.1b** for a `V̂`-representation `ρ` (the
action engine of `M(U)`).  The result is a *reduction*, in the spirit of `Core.Borcherds`:

> **`IsModuleJacobi ρ`** holds **iff** the single `m = 0` residual — the **module iterate identity**
> `ModuleIterate ρ` (the analogue of `Core.mode_iterate` 5.1.7d, but on `M`) — holds,
> **given** the field/truncation property of `ρ` (`ActModeTruncated ρ`).

The point — and the answer to "what must `M(U)/ρ` satisfy for `IsModuleJacobi`?" — is that the whole
`ℓ ≠ 0` content of the module Jacobi is *not* free from `V̂` being a Lie algebra, but it **is**
entirely packaged in the one `m = 0` slice `ModuleIterate`.  The other slice (`ℓ = 0`, locality) is
already proved unconditionally as `VHatRep.actMode_bracket`.  Everything in between is the *same*
purely-formal Pascal recursion + anti-diagonal pin that `Core.Borcherds` runs (`BL_rec`/`BR_rec` +
`antidiag_pin`), mirrored verbatim for the mode action `ρ.actMode` in place of `W.smul`.

So the module Jacobi reduces to exactly two inputs:

* **`ℓ = 0` boundary (locality):** `VHatRep.actMode_bracket` — *proved* (no hypothesis).
* **`m = 0` base (associativity / iterate):** `ModuleIterate ρ` — the genuine remaining identity.
  `ModuleIterate ρ` is *precisely* the DLM3 associativity-defect relation (eqs 4.3–4.4): the loop
  Lie algebra `V̂` only sees commutators, never the iterate `u₍ℓ₎v` as a single mode, so a generic
  `V̂`-module fails it; it holds on `M̄(U) = U(V̂)⊗_{U(P)}U` modulo the defect relations, i.e. on the
  honest induced module.  This is the lifting-direction core, isolated to one explicit identity wired
  to `Core.Borcherds.jacobi`/`Core.mode_iterate`.

**Engine check (`certificates/mathematica/mujac_self.wl`, adjoint rep `actMode = W.smul`):** both the
residual `ModuleIterate` (m = 0) and the full module Jacobi (general `ℓ, m, n`) evaluate to `0`
for the rank-1 Heisenberg VOA across `(u, v, x, ℓ, m, n)` samples — confirming the reduction target.

Everything is `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`).

## References
DLM3 §4 (eqs 4.3–4.4); Gannon §5.3.1 (Def 5.3.1b), §5.1.3 (5.1.7); H. Li hep-th/9406211 §2;
`Core.Borcherds` (`borcherds`, `antidiag_pin`), `Core.BorcherdsIdentity` (`mode_iterate`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat
namespace VHatRep

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- Generic version of `Core.WeakAssoc.finsum_nat_to_int` for an arbitrary target `P`: reindex a
`ℕ`-`finsum` to a `ℤ`-`finsum` via an extension `F` vanishing on negatives. -/
theorem finsum_nat_to_int_gen {P : Type*} [AddCommMonoid P] (g : ℕ → P) (F : ℤ → P)
    (hF0 : ∀ p : ℤ, p < 0 → F p = 0) (hFg : ∀ j : ℕ, F (j : ℤ) = g j) :
    (∑ᶠ j : ℕ, g j) = ∑ᶠ p : ℤ, F p := by
  have hinj : Function.Injective (fun j : ℕ => (j : ℤ)) := fun a b h => by simpa using h
  have hsub : Function.support F ⊆ Set.range (fun j : ℕ => (j : ℤ)) := by
    intro p hp
    rw [Function.mem_support] at hp
    rcases lt_or_ge p 0 with hlt | hge
    · exact absurd (hF0 p hlt) hp
    · exact ⟨p.toNat, by simp [Int.toNat_of_nonneg hge]⟩
  -- restrict the `ℤ`-`finsum` to its support range, then reindex along `ℕ ↪ ℤ`.
  have hmem : (∑ᶠ p : ℤ, F p) = ∑ᶠ p ∈ Set.range (fun j : ℕ => (j : ℤ)), F p := by
    rw [← finsum_mem_inter_support F (Set.range (fun j : ℕ => (j : ℤ))),
      ← finsum_mem_univ (f := F), ← finsum_mem_inter_support F Set.univ, Set.univ_inter,
      Set.inter_eq_right.mpr hsub]
  rw [hmem, finsum_mem_range hinj]
  exact finsum_congr fun j => (hFg j).symm

/-! ## Elementary `actMode` algebra -/

/-- `actMode 0 m = 0` (linearity in the first slot). -/
@[simp] theorem actMode_zero_left (ρ : VHatRep W M) (m : ℤ) :
    ρ.actMode (0 : 𝒱) m = 0 := by
  simp only [actMode_def, gen_zero_left, map_zero]

/-- `actMode (W.smul u i v)` vanishes once `i` exceeds the OPE locality bound (VOA regularity pushed
through the linear action). The companion to `BR_fin`'s upper bound. -/
theorem actMode_smul_eventually_zero (ρ : VHatRep W M) (u v : 𝒱) :
    ∃ N : ℤ, ∀ i : ℤ, N ≤ i → ∀ p : ℤ, ρ.actMode (W.smul u i v) p = 0 := by
  obtain ⟨N, hN⟩ := W.toPreVertexAlgebra.smul_eventually_zero u v
  exact ⟨N, fun i hi p => by rw [hN i hi, actMode_zero_left]⟩

/-! ## The field/truncation property of a representation

A `WeakModule` field `Y_M(a, z) = Σ a₍ₘ₎ z^{-m-1}` is *lower truncated*: for fixed `a, x` the modes
`a₍ₘ₎ x` vanish for `m` sufficiently large. This is exactly the `field`/`truncation` data of a module
(`WeakModule`, item (2) in `ZhuVermaAnArchMUVhat`'s remaining-engineering list); it is **not** implied
by `ρ` being a Lie morphism, so we carry it as an explicit hypothesis on `ρ`. -/

/-- **The truncation property of `ρ`** (module field property): for each `a : 𝒱` and `x : M` the
modes `ρ.actMode a m x` vanish for all sufficiently large `m`. -/
def ActModeTruncated (ρ : VHatRep W M) : Prop :=
  ∀ (a : 𝒱) (x : M), ∃ N : ℤ, ∀ m : ℤ, N ≤ m → ρ.actMode a m x = 0

/-! ## The two sides of the module Borcherds (mirror of `Core.Borcherds`'s `BL`/`BR`) -/

/-- The RHS family `Σᶠ i, C(m,i)·(u₍ℓ₊ᵢ₎v)₍ₘ₊ₙ₋ᵢ₎ x`. -/
noncomputable def MBR (ρ : VHatRep W M) (u v : 𝒱) (x : M) (ℓ m n : ℤ) : M :=
  ∑ᶠ i : ℤ, cbz m i • ρ.actMode (W.smul u (ℓ + i) v) (m + n - i) x

/-- The first LHS half `Σᶠ i, (-1)ⁱC(ℓ,i)·u₍ℓ₊ₘ₋ᵢ₎(v₍ₙ₊ᵢ₎ x)`. -/
noncomputable def MPuv (ρ : VHatRep W M) (u v : 𝒱) (x : M) (ℓ m n : ℤ) : M :=
  ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) • ρ.actMode u (ℓ + m - i) (ρ.actMode v (n + i) x)

/-- The second LHS half `Σᶠ i, (-1)ⁱC(ℓ,i)·v₍ℓ₊ₙ₋ᵢ₎(u₍ₘ₊ᵢ₎ x)`. -/
noncomputable def MPvu (ρ : VHatRep W M) (u v : 𝒱) (x : M) (ℓ m n : ℤ) : M :=
  ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) • ρ.actMode v (ℓ + n - i) (ρ.actMode u (m + i) x)

/-- The LHS `Puv − (-1)^ℓ·Pvu`. -/
noncomputable def MBL (ρ : VHatRep W M) (u v : 𝒱) (x : M) (ℓ m n : ℤ) : M :=
  MPuv ρ u v x ℓ m n - negOnePow ℓ • MPvu ρ u v x ℓ m n

/-! ## Finiteness of the three families -/

/-- `MBR` is finitely supported: `cbz m i` kills `i < 0`, and the iterate vanishes for `ℓ + i ≥ N`
(VOA regularity, `actMode_smul_eventually_zero`). **No truncation hypothesis needed.** -/
theorem MBR_fin (ρ : VHatRep W M) (u v : 𝒱) (x : M) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ =>
      cbz m i • ρ.actMode (W.smul u (ℓ + i) v) (m + n - i) x).Finite := by
  obtain ⟨N, hN⟩ := W.toPreVertexAlgebra.smul_eventually_zero u v
  apply Set.Finite.subset (Set.finite_Icc 0 (N - ℓ))
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg m h, zero_smul]
  · rw [hN (ℓ + i) (by omega), actMode_zero_left, LinearMap.zero_apply, smul_zero]

/-- `MPuv` is finitely supported **given truncation**: `cbz ℓ i` kills `i < 0`, and
`ρ.actMode v (n + i) x = 0` for large `i` by `ActModeTruncated`. -/
theorem MPuv_fin (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (u v : 𝒱) (x : M) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ =>
      (negOnePow i * cbz ℓ i) • ρ.actMode u (ℓ + m - i) (ρ.actMode v (n + i) x)).Finite := by
  obtain ⟨Nv, hNv⟩ := htr v x
  apply Set.Finite.subset (Set.finite_Icc 0 (Nv - n))
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg ℓ h, mul_zero, zero_smul]
  · rw [hNv (n + i) (by omega), map_zero, smul_zero]

/-- `MPvu` is finitely supported **given truncation** (symmetric to `MPuv_fin`). -/
theorem MPvu_fin (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (u v : 𝒱) (x : M) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ =>
      (negOnePow i * cbz ℓ i) • ρ.actMode v (ℓ + n - i) (ρ.actMode u (m + i) x)).Finite := by
  obtain ⟨Nu, hNu⟩ := htr u x
  apply Set.Finite.subset (Set.finite_Icc 0 (Nu - m))
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg ℓ h, mul_zero, zero_smul]
  · rw [hNu (m + i) (by omega), map_zero, smul_zero]

theorem MPuv_fin' (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (u v : 𝒱) (x : M) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ =>
      (negOnePow i * cbz ℓ (i - 1)) • ρ.actMode u (ℓ + 1 + m - i) (ρ.actMode v (n + i) x)).Finite := by
  obtain ⟨Nv, hNv⟩ := htr v x
  apply Set.Finite.subset (Set.finite_Icc 1 (Nv - n))
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg ℓ (by omega), mul_zero, zero_smul]
  · rw [hNv (n + i) (by omega), map_zero, smul_zero]

theorem MPvu_fin' (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (u v : 𝒱) (x : M) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ =>
      (negOnePow i * cbz ℓ (i - 1)) • ρ.actMode v (ℓ + 1 + n - i) (ρ.actMode u (m + i) x)).Finite := by
  obtain ⟨Nu, hNu⟩ := htr u x
  apply Set.Finite.subset (Set.finite_Icc 1 (Nu - m))
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg ℓ (by omega), mul_zero, zero_smul]
  · rw [hNu (m + i) (by omega), map_zero, smul_zero]

/-! ## The Pascal recursions (purely formal; mirror `BR_rec`/`Puv_rec`/`Pvu_rec`/`BL_rec`) -/

theorem MBR_rec (ρ : VHatRep W M) (u v : 𝒱) (x : M) (ℓ m n : ℤ) :
    MBR ρ u v x ℓ (m + 1) n = MBR ρ u v x ℓ m (n + 1) + MBR ρ u v x (ℓ + 1) m n := by
  have fin2 : (Function.support fun i : ℤ =>
      cbz m (i - 1) • ρ.actMode (W.smul u (ℓ + i) v) (m + 1 + n - i) x).Finite := by
    obtain ⟨N, hN⟩ := W.toPreVertexAlgebra.smul_eventually_zero u v
    apply Set.Finite.subset (Set.finite_Icc 1 (N - ℓ))
    intro i hi
    rw [Function.mem_support] at hi; rw [Set.mem_Icc]
    refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
    · rw [cbz_apply_neg m (by omega), zero_smul]
    · rw [hN (ℓ + i) (by omega), actMode_zero_left, LinearMap.zero_apply, smul_zero]
  rw [MBR, MBR, MBR,
    show (∑ᶠ i : ℤ, cbz (m + 1) i • ρ.actMode (W.smul u (ℓ + i) v) (m + 1 + n - i) x)
        = ∑ᶠ i : ℤ, (cbz m i • ρ.actMode (W.smul u (ℓ + i) v) (m + 1 + n - i) x
            + cbz m (i - 1) • ρ.actMode (W.smul u (ℓ + i) v) (m + 1 + n - i) x) from
      finsum_congr fun i => by rw [cbz_pascal_up, add_smul],
    finsum_add_distrib (by
      have := MBR_fin ρ u v x ℓ m (n + 1)
      refine this.subset (fun i hi => ?_)
      simp only [Function.mem_support] at hi ⊢
      rw [show m + 1 + n - i = m + (n + 1) - i from by ring] at hi
      exact hi) fin2]
  congr 1
  · exact finsum_congr fun i => by rw [show m + 1 + n - i = m + (n + 1) - i from by ring]
  · rw [← finsum_int_succ_shift
      (fun i : ℤ => cbz m (i - 1) • ρ.actMode (W.smul u (ℓ + i) v) (m + 1 + n - i) x)]
    exact finsum_congr fun i => by
      rw [show i + 1 - 1 = i from by ring, show ℓ + (i + 1) = (ℓ + 1) + i from by ring,
        show m + 1 + n - (i + 1) = m + n - i from by ring]

theorem MPuv_rec (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (u v : 𝒱) (x : M) (ℓ m n : ℤ) :
    MPuv ρ u v x ℓ (m + 1) n = MPuv ρ u v x ℓ m (n + 1) + MPuv ρ u v x (ℓ + 1) m n := by
  have e1 : MPuv ρ u v x (ℓ + 1) m n
      = (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) • ρ.actMode u (ℓ + (m + 1) - i) (ρ.actMode v (n + i) x))
        + ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ (i - 1)) •
            ρ.actMode u (ℓ + 1 + m - i) (ρ.actMode v (n + i) x) := by
    rw [MPuv, show (∑ᶠ i : ℤ, (negOnePow i * cbz (ℓ + 1) i) •
            ρ.actMode u (ℓ + 1 + m - i) (ρ.actMode v (n + i) x))
          = ∑ᶠ i : ℤ, ((negOnePow i * cbz ℓ i) • ρ.actMode u (ℓ + (m + 1) - i) (ρ.actMode v (n + i) x)
              + (negOnePow i * cbz ℓ (i - 1)) •
                  ρ.actMode u (ℓ + 1 + m - i) (ρ.actMode v (n + i) x)) from
        finsum_congr fun i => by
          rw [cbz_pascal_up, mul_add, add_smul, show ℓ + 1 + m - i = ℓ + (m + 1) - i from by ring],
      finsum_add_distrib (MPuv_fin ρ htr u v x ℓ (m + 1) n) (MPuv_fin' ρ htr u v x ℓ m n)]
  have e2 : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        ρ.actMode u (ℓ + (m + 1) - i) (ρ.actMode v (n + i) x)) = MPuv ρ u v x ℓ (m + 1) n := by
    rw [MPuv]
  have e3 : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ (i - 1)) •
        ρ.actMode u (ℓ + 1 + m - i) (ρ.actMode v (n + i) x)) = -MPuv ρ u v x ℓ m (n + 1) := by
    have step1 : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ (i - 1)) •
          ρ.actMode u (ℓ + 1 + m - i) (ρ.actMode v (n + i) x))
        = ∑ᶠ i : ℤ, -((negOnePow i * cbz ℓ i) •
            ρ.actMode u (ℓ + m - i) (ρ.actMode v (n + 1 + i) x)) := by
      rw [← finsum_int_succ_shift
        (fun i : ℤ => (negOnePow i * cbz ℓ (i - 1)) •
          ρ.actMode u (ℓ + 1 + m - i) (ρ.actMode v (n + i) x))]
      exact finsum_congr fun i => by
        rw [show i + 1 - 1 = i from by ring, negOnePow_succ,
          show ℓ + 1 + m - (i + 1) = ℓ + m - i from by ring, show n + (i + 1) = n + 1 + i from by ring,
          neg_mul, neg_smul]
    rw [step1, finsum_neg_distrib
      (fun i : ℤ => (negOnePow i * cbz ℓ i) • ρ.actMode u (ℓ + m - i) (ρ.actMode v (n + 1 + i) x)),
      MPuv]
  rw [e1, e2, e3]; abel

theorem MPvu_rec (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (u v : 𝒱) (x : M) (ℓ m n : ℤ) :
    MPvu ρ u v x ℓ (m + 1) n = MPvu ρ u v x ℓ m (n + 1) - MPvu ρ u v x (ℓ + 1) m n := by
  have e1 : MPvu ρ u v x (ℓ + 1) m n
      = (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) • ρ.actMode v (ℓ + (n + 1) - i) (ρ.actMode u (m + i) x))
        + ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ (i - 1)) •
            ρ.actMode v (ℓ + 1 + n - i) (ρ.actMode u (m + i) x) := by
    rw [MPvu, show (∑ᶠ i : ℤ, (negOnePow i * cbz (ℓ + 1) i) •
            ρ.actMode v (ℓ + 1 + n - i) (ρ.actMode u (m + i) x))
          = ∑ᶠ i : ℤ, ((negOnePow i * cbz ℓ i) • ρ.actMode v (ℓ + (n + 1) - i) (ρ.actMode u (m + i) x)
              + (negOnePow i * cbz ℓ (i - 1)) •
                  ρ.actMode v (ℓ + 1 + n - i) (ρ.actMode u (m + i) x)) from
        finsum_congr fun i => by
          rw [cbz_pascal_up, mul_add, add_smul, show ℓ + 1 + n - i = ℓ + (n + 1) - i from by ring],
      finsum_add_distrib (MPvu_fin ρ htr u v x ℓ m (n + 1)) (MPvu_fin' ρ htr u v x ℓ m n)]
  have e2 : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        ρ.actMode v (ℓ + (n + 1) - i) (ρ.actMode u (m + i) x)) = MPvu ρ u v x ℓ m (n + 1) := by
    rw [MPvu]
  have e3 : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ (i - 1)) •
        ρ.actMode v (ℓ + 1 + n - i) (ρ.actMode u (m + i) x)) = -MPvu ρ u v x ℓ (m + 1) n := by
    have step1 : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ (i - 1)) •
          ρ.actMode v (ℓ + 1 + n - i) (ρ.actMode u (m + i) x))
        = ∑ᶠ i : ℤ, -((negOnePow i * cbz ℓ i) •
            ρ.actMode v (ℓ + n - i) (ρ.actMode u (m + 1 + i) x)) := by
      rw [← finsum_int_succ_shift
        (fun i : ℤ => (negOnePow i * cbz ℓ (i - 1)) •
          ρ.actMode v (ℓ + 1 + n - i) (ρ.actMode u (m + i) x))]
      exact finsum_congr fun i => by
        rw [show i + 1 - 1 = i from by ring, negOnePow_succ,
          show ℓ + 1 + n - (i + 1) = ℓ + n - i from by ring, show m + (i + 1) = m + 1 + i from by ring,
          neg_mul, neg_smul]
    rw [step1, finsum_neg_distrib
      (fun i : ℤ => (negOnePow i * cbz ℓ i) • ρ.actMode v (ℓ + n - i) (ρ.actMode u (m + 1 + i) x)),
      MPvu]
  rw [e1, e2, e3]; abel

theorem MBL_rec (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (u v : 𝒱) (x : M) (ℓ m n : ℤ) :
    MBL ρ u v x ℓ (m + 1) n = MBL ρ u v x ℓ m (n + 1) + MBL ρ u v x (ℓ + 1) m n := by
  simp only [MBL, MPuv_rec ρ htr u v x ℓ m n, MPvu_rec ρ htr u v x ℓ m n, negOnePow_succ]
  module

/-! ## `MBL` as a single `finsum` (matches `IsModuleJacobi`'s LHS) -/

theorem MBL_as_finsum (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (u v : 𝒱) (x : M) (ℓ m n : ℤ) :
    MBL ρ u v x ℓ m n = ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
      (ρ.actMode u (ℓ + m - i) (ρ.actMode v (n + i) x)
        - negOnePow ℓ • ρ.actMode v (ℓ + n - i) (ρ.actMode u (m + i) x)) := by
  have hfQn : (Function.support fun i : ℤ =>
      -((negOnePow i * cbz ℓ i) •
        (negOnePow ℓ • ρ.actMode v (ℓ + n - i) (ρ.actMode u (m + i) x)))).Finite := by
    refine (MPvu_fin ρ htr u v x ℓ m n).subset (fun i hi => ?_)
    simp only [Function.mem_support] at hi ⊢
    intro h; exact hi (by rw [smul_comm, h, smul_zero, neg_zero])
  symm
  rw [show (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
            (ρ.actMode u (ℓ + m - i) (ρ.actMode v (n + i) x)
              - negOnePow ℓ • ρ.actMode v (ℓ + n - i) (ρ.actMode u (m + i) x)))
        = ∑ᶠ i : ℤ, ((negOnePow i * cbz ℓ i) • ρ.actMode u (ℓ + m - i) (ρ.actMode v (n + i) x)
            + -((negOnePow i * cbz ℓ i) •
                (negOnePow ℓ • ρ.actMode v (ℓ + n - i) (ρ.actMode u (m + i) x))))
      from finsum_congr fun i => by rw [smul_sub, sub_eq_add_neg],
    finsum_add_distrib (MPuv_fin ρ htr u v x ℓ m n) hfQn, finsum_neg_distrib,
    show (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
            (negOnePow ℓ • ρ.actMode v (ℓ + n - i) (ρ.actMode u (m + i) x)))
        = negOnePow ℓ • MPvu ρ u v x ℓ m n from by
        rw [MPvu, smul_finsum' (negOnePow ℓ) (MPvu_fin ρ htr u v x ℓ m n)]
        exact finsum_congr fun i => by rw [smul_comm],
    MBL, MPuv, ← sub_eq_add_neg]

/-! ## The `ℓ = 0` boundary (locality) — *proved* from `actMode_bracket` -/

/-- `MBR` at `ℓ = 0` is the iterate-mode acting through `ρ`, summed against `cbz m i`. -/
theorem MBR_zero_ell (ρ : VHatRep W M) (u v : 𝒱) (x : M) (m n : ℤ) :
    MBR ρ u v x 0 m n = ∑ᶠ i : ℤ, cbz m i • ρ.actMode (W.smul u i v) (m + n - i) x := by
  rw [MBR]; exact finsum_congr fun i => by rw [zero_add]

/-- `MBR` at `ℓ = 0` as a `ℕ`-`finsum` with `gBinom` (matching the `actMode_bracket` shape). -/
theorem MBR_zero_ell_nat (ρ : VHatRep W M) (u v : 𝒱) (x : M) (m n : ℤ) :
    MBR ρ u v x 0 m n
      = ∑ᶠ i : ℕ, (gBinom m i) • ρ.actMode (W.smul u i v) (m + n - i) x := by
  rw [MBR_zero_ell,
    (finsum_nat_to_int_gen
      (fun j : ℕ => (gBinom m j) • ρ.actMode (W.smul u j v) (m + n - j) x)
      (fun p : ℤ => cbz m p • ρ.actMode (W.smul u p v) (m + n - p) x)
      (fun p hp => by simp only [cbz_apply_neg m hp, zero_smul])
      (fun j => by
        simp only [cbz_apply_nonneg m (Int.natCast_nonneg j), Int.toNat_natCast])).symm]

/-- **The `ℓ = 0` boundary of the module Jacobi**, proved from `actMode_bracket` (locality). The
commutator of single modes is the iterate-mode sum, which is exactly `MBR` at `ℓ = 0`. -/
theorem MBL_zero_ell (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (u v : 𝒱) (x : M) (m n : ℤ) :
    MBL ρ u v x 0 m n = MBR ρ u v x 0 m n := by
  have e0 : negOnePow (0 : ℤ) = 1 := by rw [negOnePow_eq_zpow]; norm_num
  -- `MBL` at `ℓ=0` collapses to the single `i=0` term = the bracket applied to `x`.
  have hBL : MBL ρ u v x 0 m n = ⁅ρ.actMode u m, ρ.actMode v n⁆ x := by
    rw [MBL, MPuv, MPvu,
      finsum_eq_single _ (0 : ℤ) (fun i hi => by rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul]),
      finsum_eq_single _ (0 : ℤ) (fun i hi => by rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul])]
    simp only [e0, cbz_zero_left, if_pos, mul_one, one_mul, one_smul, add_zero, zero_add, sub_zero]
    rw [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
  -- the bracket = `Σᶠ i:ℕ, gBinom m i • (u₍ᵢ₎v)₍ₘ₊ₙ₋ᵢ₎ x` (this is `actMode_bracket` applied to `x`).
  have hcommx : ⁅ρ.actMode u m, ρ.actMode v n⁆ x
      = ∑ᶠ i : ℕ, (gBinom m i) • ρ.actMode (W.smul u i v) (m + n - i) x := by
    have hbr := ρ.actMode_bracket u v m n
    have happ := congrArg (fun T : Module.End ℂ M => T x) hbr
    simp only at happ
    rw [happ]
    -- push `(· x)` through the finite OPE finsum
    have hfin : (Function.support fun i : ℕ =>
        (gBinom m i) • ρ.actMode (W.smul u i v) (m + n - i)).Finite := by
      obtain ⟨N, hN⟩ := W.toPreVertexAlgebra.smul_eventually_zero u v
      refine Set.Finite.subset (Set.finite_Iio N.toNat) ?_
      intro i hi
      rw [Function.mem_support] at hi
      rw [Set.mem_Iio]
      by_contra hcon
      rw [not_lt] at hcon
      refine hi ?_
      rw [hN i (le_trans (Int.self_le_toNat N) (by exact_mod_cast hcon)), actMode_zero_left,
        smul_zero]
    -- evaluation map `T ↦ T x` is linear, so commutes with the finite sum.
    let ev : Module.End ℂ M →ₗ[ℂ] M :=
      { toFun := fun T => T x, map_add' := fun S T => rfl, map_smul' := fun c T => rfl }
    have hev : ∀ T : Module.End ℂ M, ev T = T x := fun _ => rfl
    rw [← hev, map_finsum ev hfin]
    exact finsum_congr fun i => by rw [map_smul, hev]
  rw [hBL, hcommx, MBR_zero_ell_nat]

/-! ## The `m = 0` base — the genuine residual `ModuleIterate`

This is the single remaining identity to which the whole module Jacobi reduces. It is the module
analogue of `Core.mode_iterate` (5.1.7d): the iterate mode `(u₍ℓ₎v)₍ₙ₎` acting on `x` equals the
formal-`i` resummation of compositions of single modes. The loop Lie algebra `V̂` cannot express the
iterate as a single generator; this identity holds on `M̄(U)` precisely because of the DLM3
associativity-defect relations (eqs 4.3–4.4). -/

/-- **The module iterate identity `ModuleIterate ρ`** (DLM3 eqs 4.3–4.4; module 5.1.7d). The single
residual to which `IsModuleJacobi` reduces, beyond the proved locality boundary. -/
def ModuleIterate (ρ : VHatRep W M) : Prop :=
  ∀ (u v : 𝒱) (x : M) (ℓ N : ℤ),
    ρ.actMode (W.smul u ℓ v) N x
      = ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
          (ρ.actMode u (ℓ - i) (ρ.actMode v (N + i) x)
            - negOnePow ℓ • ρ.actMode v (ℓ + N - i) (ρ.actMode u i x))

/-- `MBR` at `m = 0` collapses to the single iterate mode `(u₍ℓ₎v)₍ₙ₎ x`. -/
theorem MBR_zero_m (ρ : VHatRep W M) (u v : 𝒱) (x : M) (ℓ n : ℤ) :
    MBR ρ u v x ℓ 0 n = ρ.actMode (W.smul u ℓ v) n x := by
  rw [MBR, finsum_eq_single _ (0 : ℤ)
      (fun i hi => by rw [cbz_zero_left, if_neg hi, zero_smul])]
  rw [cbz_zero_left, if_pos rfl, one_smul, show ℓ + (0 : ℤ) = ℓ from by ring,
    show (0 : ℤ) + n - 0 = n from by ring]

/-- **The `m = 0` base of the module Jacobi**, *given* the residual `ModuleIterate`. This is the only
place the residual is used; everything else (recursion, locality boundary) is unconditional. -/
theorem MBL_zero_m (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (hit : ModuleIterate ρ)
    (u v : 𝒱) (x : M) (ℓ n : ℤ) :
    MBL ρ u v x ℓ 0 n = MBR ρ u v x ℓ 0 n := by
  rw [MBR_zero_m, MBL_as_finsum ρ htr, hit u v x ℓ n]
  exact finsum_congr fun i => by
    rw [show ℓ + (0 : ℤ) - i = ℓ - i from by ring, show (0 : ℤ) + i = i from by ring]

/-! ## The reduction theorem — module Borcherds from the two slices -/

/-- **The module Borcherds identity `MBL = MBR` for all `(ℓ, m, n)`**, assembled from the two slices
exactly as `Core.Borcherds.borcherds`: the `m = 0` base is the residual `ModuleIterate` (via
`MBL_zero_m`), the `ℓ = 0` boundary is locality (`MBL_zero_ell`, from `actMode_bracket`), and the
`m < 0` step is pinned to the `ℓ = 0` column by `antidiag_pin`. -/
theorem module_borcherds (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (hit : ModuleIterate ρ)
    (u v : 𝒱) (x : M) (ℓ m n : ℤ) :
    MBL ρ u v x ℓ m n = MBR ρ u v x ℓ m n := by
  induction m using Int.induction_on generalizing ℓ n with
  | zero => exact MBL_zero_m ρ htr hit u v x ℓ n
  | succ k ih => rw [MBL_rec ρ htr, MBR_rec, ih ℓ (n + 1), ih (ℓ + 1) n]
  | pred k ih =>
      -- the `m < 0` anti-diagonal pin on the discrepancy `D = MBL − MBR`
      have key := antidiag_pin
        (fun ℓ' n' => MBL ρ u v x ℓ' (-(k : ℤ) - 1) n' - MBR ρ u v x ℓ' (-(k : ℤ) - 1) n')
        (fun ℓ' n' => by
          dsimp only
          have hbl := MBL_rec ρ htr u v x ℓ' (-(k : ℤ) - 1) n'
          have hbr := MBR_rec ρ u v x ℓ' (-(k : ℤ) - 1) n'
          rw [show (-(k : ℤ) - 1) + 1 = -(k : ℤ) from by ring] at hbl hbr
          have hih := ih ℓ' n'
          rw [hbl, hbr] at hih
          rw [neg_sub, sub_eq_sub_iff_add_eq_add]
          exact hih.trans (add_comm _ _))
        (fun n' => by dsimp only; rw [MBL_zero_ell ρ htr u v x (-(k : ℤ) - 1) n', sub_self])
        ℓ n
      exact sub_eq_zero.mp key

/-! ## The headline result: `IsModuleJacobi` from `ModuleIterate` -/

/-- **`IsModuleJacobi ρ` from the residual `ModuleIterate ρ`** (and truncation). The `IsModuleJacobi`
identity is `MBL = MBR` re-read through `MBL_as_finsum`/`MBR`; `module_borcherds` supplies it. This is
the discharge of the deep crux of Construction A: the module Borcherds 5.3.1b holds as soon as the one
associativity/iterate residual `ModuleIterate` holds (the `ℓ = 0` locality slice being already proved
in `actMode_bracket`). -/
theorem isModuleJacobi_of_iterate (ρ : VHatRep W M) (htr : ActModeTruncated ρ)
    (hit : ModuleIterate ρ) : ρ.IsModuleJacobi := by
  intro u v x ℓ m n
  have h := module_borcherds ρ htr hit u v x ℓ m n
  rw [MBL_as_finsum ρ htr] at h
  rw [h, MBR]

/-- **Conversely**, `IsModuleJacobi ρ` *implies* the residual `ModuleIterate ρ` (its `m = 0` slice).
Together with `isModuleJacobi_of_iterate` this pins down `ModuleIterate` as the *exact* residual
content of the module Jacobi beyond locality: under truncation, `IsModuleJacobi ↔ ModuleIterate`. -/
theorem moduleIterate_of_isModuleJacobi (ρ : VHatRep W M) (htr : ActModeTruncated ρ)
    (hj : ρ.IsModuleJacobi) : ModuleIterate ρ := by
  intro u v x ℓ N
  -- `IsModuleJacobi` at `m = 0`: its LHS is `MBL ρ u v x ℓ 0 N`, its RHS is `MBR ρ u v x ℓ 0 N`.
  have h := hj u v x ℓ 0 N
  -- the `m = 0` instance, repackaged through `MBL_as_finsum`/`MBR`.
  have hMBL : MBL ρ u v x ℓ 0 N = MBR ρ u v x ℓ 0 N := by
    rw [MBL_as_finsum ρ htr, MBR]; exact h
  -- target = `MBL_as_finsum` RHS (index-normalized) = `MBL = MBR = (u₍ℓ₎v)₍N₎ x`.
  rw [← MBR_zero_m ρ u v x ℓ N, ← hMBL, MBL_as_finsum ρ htr]
  exact finsum_congr fun i => by
    rw [show ℓ + (0 : ℤ) - i = ℓ - i from by ring, show (0 : ℤ) + i = i from by ring]

/-- **The reduction, packaged:** under the truncation/field property, the module Jacobi 5.3.1b is
*equivalent* to the single residual module-iterate identity. This is the precise answer to "what must
`M(U)/ρ` satisfy for `IsModuleJacobi`": exactly `ModuleIterate ρ` — the DLM3 associativity-defect
relation, i.e. that `M(U)` is the induced/defect quotient `M̄(U)`. -/
theorem isModuleJacobi_iff_iterate (ρ : VHatRep W M) (htr : ActModeTruncated ρ) :
    ρ.IsModuleJacobi ↔ ModuleIterate ρ :=
  ⟨moduleIterate_of_isModuleJacobi ρ htr, isModuleJacobi_of_iterate ρ htr⟩

end VHatRep
end VHat

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
