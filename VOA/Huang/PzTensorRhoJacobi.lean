/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.PzTensorRhoCoef

/-!
# The reversed Jacobi identity for `ρ` on compatible forms

`rho_jacobi`: if a bilinear form `β ∈ (M₁ ⊗ M₂)*` is lower truncated and satisfies the
compatibility condition for the states `a` and `b`, then the transposed coproducts satisfy the
Borcherds identity **in the reversed order** (they are transposes of a module action):

`Σ_i (−1)^i C(ℓ,i) [ρ(b,n+i) ρ(a,ℓ+m−i) β − (−1)^ℓ ρ(a,m+i) ρ(b,ℓ+n−i) β]
   = Σ_i C(m,i) ρ(a_{ℓ+i} b, m+n−i) β`,

for **all** `ℓ, m, n ∈ ℤ`.  (No `ρ`-stability of a space of forms is needed: the identity holds
form by form.)

Proof (finite sums throughout): evaluate at `(y₁, y₂)`, expand the outer `ρ` by its definition
into the `M₂`-part and the `M₁`-part, expand the inner `ρ` likewise **only** where the resulting
sum is finite; the remaining outside sums are localized by the compatibility slices
(`slice_holds`) after the coefficient identity `coef_lemma`.  The `M₂`-`M₂` terms recombine by the
module Jacobi identity of `M₂`, the `M₁`-`M₁` terms by that of `M₁` (after `iter_lemma`), and the
mixed terms cancel in pairs (`mix_lemma`).

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.PzTensorRho

open VOA
open scoped BigOperators

universe u v w

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M₁ : Type v} [AddCommGroup M₁] [Module ℂ M₁]
variable {M₂ : Type w} [AddCommGroup M₂] [Module ℂ M₂]

/-! ## Uniform truncation over finitely many vectors / states -/

theorem unif_trunc {M : Type*} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M) (a : 𝒱)
    (f : ℤ → M) (lo hi : ℤ) :
    ∃ N : ℤ, ∀ q, lo ≤ q → q ≤ hi → ∀ n, N ≤ n → mode (A.YM a) n (f q) = 0 := by
  classical
  choose Nq hNq using fun q => A.truncation a (f q)
  refine ⟨((Finset.Icc lo hi).sup fun q => (Nq q).toNat : ℕ), fun q hlo hhi n hn => ?_⟩
  refine hNq q n (le_trans ?_ hn)
  have h1 : (Nq q).toNat ≤ (Finset.Icc lo hi).sup fun q => (Nq q).toNat :=
    Finset.le_sup (f := fun q => (Nq q).toNat) (Finset.mem_Icc.2 ⟨hlo, hhi⟩)
  have h2 : Nq q ≤ ((Nq q).toNat : ℤ) := Int.self_le_toNat _
  exact le_trans h2 (by exact_mod_cast h1)

theorem unif_trunc_state {M : Type*} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M)
    (c : ℤ → 𝒱) (y : M) (lo hi : ℤ) :
    ∃ N : ℤ, ∀ q, lo ≤ q → q ≤ hi → ∀ n, N ≤ n → mode (A.YM (c q)) n y = 0 := by
  classical
  choose Nq hNq using fun q => A.truncation (c q) y
  refine ⟨((Finset.Icc lo hi).sup fun q => (Nq q).toNat : ℕ), fun q hlo hhi n hn => ?_⟩
  refine hNq q n (le_trans ?_ hn)
  have h1 : (Nq q).toNat ≤ (Finset.Icc lo hi).sup fun q => (Nq q).toNat :=
    Finset.le_sup (f := fun q => (Nq q).toNat) (Finset.mem_Icc.2 ⟨hlo, hhi⟩)
  have h2 : Nq q ≤ ((Nq q).toNat : ℤ) := Int.self_le_toNat _
  exact le_trans h2 (by exact_mod_cast h1)

section Jacobi

variable (A₁ : WeakModule W M₁) (A₂ : WeakModule W M₂)

theorem InL_zero_pt (a : 𝒱) (m L : ℤ) (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) (y₂ : M₂) :
    InL A₁ a m L β 0 y₂ = 0 := by
  unfold InL; simp

theorem InR_zero_pt (a : 𝒱) (m L : ℤ) (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) (y₂ : M₂) :
    InR A₂ a m L β 0 y₂ = 0 := by
  unfold InR; simp

/-! ## Localization of the outside sums -/

/-- **Localization**: the outside sum with the inner `ρ` evaluated at the `M₁`-shifted
points is a sum of local terms. -/
theorem loc_eq {c d : 𝒱} {β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ} (htr : TruncAt A₁ A₂ c β)
    (hcc : CompatAt A₁ A₂ c β) (ℓ p q : ℤ) (y₁ : M₁) (y₂ : M₂) :
    ∑ᶠ i, (negOnePow i * cbz ℓ i) * ∑ᶠ s, cbz (q + i) s
        * rhoL A₁ A₂ c (ℓ + p - i) β (mode (A₁.YM d) s y₁) y₂
      = ∑ᶠ s, ∑ᶠ t, cbz q (s - t) * (negOnePow t * cbz ℓ t)
            * InL A₁ c p (ℓ - t) β (mode (A₁.YM d) s y₁) y₂
        + ∑ᶠ s, ∑ᶠ t, cbz q (s - t) * (negOnePow t * cbz ℓ t)
            * InR A₂ c p (ℓ - t) β (mode (A₁.YM d) s y₁) y₂ := by
  obtain ⟨P, hP⟩ := htr
  obtain ⟨Nd, hNd⟩ := A₁.truncation d y₁
  set K : ℤ := max (ℓ + p - P) 0 with hK
  set Nd' : ℤ := max Nd 0 with hNd'
  have hX : ∀ i, K < i → rhoL A₁ A₂ c (ℓ + p - i) β = 0 := fun i hi => hP _ (by omega)
  -- exchange the order
  have h1 : ∑ᶠ i, (negOnePow i * cbz ℓ i) * ∑ᶠ s, cbz (q + i) s
        * rhoL A₁ A₂ c (ℓ + p - i) β (mode (A₁.YM d) s y₁) y₂
      = ∑ᶠ s, ∑ᶠ i, (negOnePow i * cbz ℓ i) * cbz (q + i) s
        * rhoL A₁ A₂ c (ℓ + p - i) β (mode (A₁.YM d) s y₁) y₂ := by
    simp only [mul_finsum]
    rw [finsum_comm_box _ 0 K 0 Nd' (fun i s his => by
      rcases his with h | h | h | h
      · rw [cbz_neg h]; ring
      · rw [hX i h]; simp
      · rw [show cbz (q + i) s = 0 from cbz_neg h]; ring
      · rw [hNd s (by omega)]; simp)]
    exact finsum_congr fun s => finsum_congr fun i => by ring
  rw [h1]
  -- localize each `s`-term
  have h2 : ∀ s, ∑ᶠ i, (negOnePow i * cbz ℓ i) * cbz (q + i) s
        * rhoL A₁ A₂ c (ℓ + p - i) β (mode (A₁.YM d) s y₁) y₂
      = ∑ᶠ t, cbz q (s - t) * (negOnePow t * cbz ℓ t)
            * InL A₁ c p (ℓ - t) β (mode (A₁.YM d) s y₁) y₂
        + ∑ᶠ t, cbz q (s - t) * (negOnePow t * cbz ℓ t)
            * InR A₂ c p (ℓ - t) β (mode (A₁.YM d) s y₁) y₂ := by
    intro s
    rw [coef_lemma ℓ q s (fun i => rhoL A₁ A₂ c (ℓ + p - i) β (mode (A₁.YM d) s y₁) y₂) (K + 1)
      (fun i hi => by dsimp only; rw [hX i (by omega)]; simp)]
    rw [← finsum_add_distrib
      (hfs_of _ 0 (max s 0) fun t ht => by
        rcases ht with ht | ht
        · rw [cbz_neg ht]; ring
        · rw [cbz_neg (show s - t < 0 by omega)]; ring)
      (hfs_of _ 0 (max s 0) fun t ht => by
        rcases ht with ht | ht
        · rw [cbz_neg ht]; ring
        · rw [cbz_neg (show s - t < 0 by omega)]; ring)]
    refine finsum_congr fun t => ?_
    have hO : ∑ᶠ k, (negOnePow k * cbz (ℓ - t) k)
          * rhoL A₁ A₂ c (ℓ + p - (t + k)) β (mode (A₁.YM d) s y₁) y₂
        = Out A₁ A₂ c p (ℓ - t) β (mode (A₁.YM d) s y₁) y₂ := by
      unfold Out
      exact finsum_congr fun k => by rw [show ℓ + p - (t + k) = p + (ℓ - t) - k by ring]
    rw [hO, slice_holds A₁ A₂ ⟨P, hP⟩ hcc]
    ring
  rw [finsum_congr h2, finsum_add_distrib]
  · exact hfs_of _ 0 Nd' fun s hs => by
      rcases hs with hs | hs
      · exact finsum_eq_zero_of_forall_eq_zero fun t => by
          rcases lt_or_ge t 0 with ht | ht
          · rw [cbz_neg ht]; ring
          · rw [cbz_neg (show s - t < 0 by omega)]; ring
      · rw [hNd s (by omega)]; simp only [InL_zero_pt, mul_zero, finsum_zero]
  · exact hfs_of _ 0 Nd' fun s hs => by
      rcases hs with hs | hs
      · exact finsum_eq_zero_of_forall_eq_zero fun t => by
          rcases lt_or_ge t 0 with ht | ht
          · rw [cbz_neg ht]; ring
          · rw [cbz_neg (show s - t < 0 by omega)]; ring
      · rw [hNd s (by omega)]; simp only [InR_zero_pt, mul_zero, finsum_zero]

/-! ## Reindexing the `M₁`-local terms -/

/-- The `M₁`–`M₁` local terms in the iterate shape `Σ_{r,s} C(p,r) C(q,s) Σ_t (…)`. -/
theorem reindex_eq (c d : 𝒱) (p q ℓ : ℤ) (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) (y₁ : M₁) (y₂ : M₂) :
    ∑ᶠ s, ∑ᶠ t, cbz q (s - t) * (negOnePow t * cbz ℓ t)
        * InL A₁ c p (ℓ - t) β (mode (A₁.YM d) s y₁) y₂
      = ∑ᶠ r, ∑ᶠ s, cbz p r * cbz q s * ∑ᶠ t, (negOnePow t * cbz ℓ t)
          * β (mode (A₁.YM c) (ℓ + r - t) (mode (A₁.YM d) (s + t) y₁)) y₂ := by
  obtain ⟨Nd, hNd⟩ := A₁.truncation d y₁
  set D : ℤ := max Nd 0 with hD
  obtain ⟨Nc, hNc⟩ := unif_trunc A₁ c (fun s => mode (A₁.YM d) s y₁) 0 D
  set B : ℤ := D + max (Nc - ℓ) 0 + 1 with hB
  set F : ℤ → ℤ → ℤ → ℂ := fun s t r => cbz q (s - t) * (negOnePow t * cbz ℓ t)
      * (cbz p r * β (mode (A₁.YM c) (ℓ - t + r) (mode (A₁.YM d) s y₁)) y₂) with hFdef
  have hF0 : ∀ s t r, (s < -B ∨ B < s ∨ t < -B ∨ B < t ∨ r < -B ∨ B < r) → F s t r = 0 := by
    intro s t r h
    simp only [hFdef]
    rcases lt_or_ge t 0 with ht | ht
    · rw [cbz_neg ht]; ring
    rcases lt_or_ge s t with hst | hst
    · rw [cbz_neg (show s - t < 0 by omega)]; ring
    rcases le_or_gt Nd s with hs | hs
    · rw [hNd s hs]; simp
    rcases lt_or_ge r 0 with hr | hr
    · rw [cbz_neg hr]; ring
    rw [hNc s (by omega) (by omega) _ (by omega)]
    · simp
  have hL : ∑ᶠ s, ∑ᶠ t, cbz q (s - t) * (negOnePow t * cbz ℓ t)
        * InL A₁ c p (ℓ - t) β (mode (A₁.YM d) s y₁) y₂ = ∑ᶠ s, ∑ᶠ t, ∑ᶠ r, F s t r := by
    refine finsum_congr fun s => finsum_congr fun t => ?_
    unfold InL
    rw [mul_finsum]
  rw [hL, finsum3_swap12 F B hF0]
  have hshift : ∀ t, ∑ᶠ s, ∑ᶠ r, F s t r = ∑ᶠ s, ∑ᶠ r, F (s + t) t r := fun t =>
    (finsum_shift (fun s => ∑ᶠ r, F s t r) t).symm
  rw [finsum_congr hshift]
  have hB1 : 1 ≤ B := by omega
  rw [finsum3_rev (fun t s r => F (s + t) t r) B (fun t s r h => by
    rcases lt_or_ge t 0 with ht | ht
    · simp only [hFdef]; rw [cbz_neg ht]; ring
    rcases lt_or_ge s 0 with hs | hs
    · simp only [hFdef]; rw [cbz_neg (show s + t - t < 0 by omega)]; ring
    exact hF0 _ _ _ (by omega))]
  refine finsum_congr fun r => finsum_congr fun s => ?_
  rw [mul_finsum]
  refine finsum_congr fun t => ?_
  simp only [hFdef]
  rw [show s + t - t = s by ring, show ℓ - t + r = ℓ + r - t by ring]
  ring

/-! ## The `M₂`–`M₂` terms: the module Jacobi identity of `M₂` -/

theorem p2_eq (a b : 𝒱) (ℓ m n : ℤ) (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) (y₁ : M₁) (y₂ : M₂) :
    ∑ᶠ i, (negOnePow i * cbz ℓ i)
        * β y₁ (mode (A₂.YM a) (ℓ + m - i) (mode (A₂.YM b) (n + i) y₂))
      - negOnePow ℓ * ∑ᶠ i, (negOnePow i * cbz ℓ i)
        * β y₁ (mode (A₂.YM b) (ℓ + n - i) (mode (A₂.YM a) (m + i) y₂))
      = ∑ᶠ i, cbz m i * β y₁ (mode (A₂.YM (W.smul a (ℓ + i) b)) (m + n - i) y₂) := by
  obtain ⟨Na, hNa⟩ := A₂.truncation a y₂
  obtain ⟨Nb, hNb⟩ := A₂.truncation b y₂
  obtain ⟨Nab, hNab⟩ := W.toPreVertexAlgebra.smul_eventually_zero a b
  set K : ℤ := max (max (Nb - n) (Na - m)) (Nab - ℓ) with hK
  have hJ := congrArg (β y₁) (A₂.jacobi a b y₂ ℓ m n)
  rw [map_finsum (β y₁) (hfs_of _ 0 K fun i hi => by
      rcases hi with hi | hi
      · rw [cbz_neg hi, mul_zero, zero_smul]
      · rw [hNb _ (by omega), hNa _ (by omega)]; simp),
    map_finsum (β y₁) (hfs_of _ 0 K fun i hi => by
      rcases hi with hi | hi
      · rw [cbz_neg hi, zero_smul]
      · rw [hNab _ (by omega)]; simp)] at hJ
  simp only [map_sub, map_smul, smul_eq_mul] at hJ
  rw [← hJ]
  rw [finsum_eq_Icc' _ 0 K (fun i hi => by
      rcases hi with hi | hi
      · rw [cbz_neg hi]; ring
      · rw [hNb _ (by omega)]; simp),
    finsum_eq_Icc' _ 0 K (fun i hi => by
      rcases hi with hi | hi
      · rw [cbz_neg hi]; ring
      · rw [hNa _ (by omega)]; simp),
    finsum_eq_Icc' _ 0 K (fun i hi => by
      rcases hi with hi | hi
      · rw [cbz_neg hi]; ring
      · rw [hNb _ (by omega), hNa _ (by omega)]; simp)]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ## The `M₁`–`M₁` terms: the module Jacobi identity of `M₁` -/

theorem p1_eq (a b : 𝒱) (ℓ m n : ℤ) (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) (y₁ : M₁) (y₂ : M₂) :
    (∑ᶠ r, ∑ᶠ s, cbz m r * cbz n s * ∑ᶠ t, (negOnePow t * cbz ℓ t)
        * β (mode (A₁.YM a) (ℓ + r - t) (mode (A₁.YM b) (s + t) y₁)) y₂)
      - negOnePow ℓ * (∑ᶠ s, ∑ᶠ r, cbz n s * cbz m r * ∑ᶠ t, (negOnePow t * cbz ℓ t)
        * β (mode (A₁.YM b) (ℓ + s - t) (mode (A₁.YM a) (r + t) y₁)) y₂)
      = ∑ᶠ i, cbz m i * ∑ᶠ s, cbz (m + n - i) s
          * β (mode (A₁.YM (W.smul a (ℓ + i) b)) s y₁) y₂ := by
  obtain ⟨Na, hNa⟩ := A₁.truncation a y₁
  obtain ⟨Nb, hNb⟩ := A₁.truncation b y₁
  set Na' : ℤ := max Na 0 with hNa'
  set Nb' : ℤ := max Nb 0 with hNb'
  obtain ⟨Nab, hNab⟩ := W.toPreVertexAlgebra.smul_eventually_zero a b
  set I : ℤ := max (Nab - ℓ) 0 with hI
  obtain ⟨S, hS⟩ := unif_trunc_state A₁ (fun i => W.smul a (ℓ + i) b) y₁ 0 I
  obtain ⟨Nu, hNu⟩ := unif_trunc A₁ a (fun q => mode (A₁.YM b) q y₁) 0 Nb'
  obtain ⟨Nv, hNv⟩ := unif_trunc A₁ b (fun q => mode (A₁.YM a) q y₁) 0 Na'
  set g : ℤ → ℤ → ℂ := fun i s => β (mode (A₁.YM (W.smul a (ℓ + i) b)) s y₁) y₂ with hg
  have hg0 : ∀ i s, 0 ≤ i → (I + 1 ≤ i ∨ max S 0 ≤ s) → g i s = 0 := by
    intro i s hi h
    simp only [hg]
    rcases le_or_gt (I + 1) i with hI' | hI'
    · rw [hNab _ (by omega)]; simp
    · rcases h with h | h
      · omega
      · rw [hS i hi (by omega) s (by omega)]; simp
  -- the per-`(r,s)` Jacobi identity of `M₁`
  set U : ℤ → ℤ → ℂ := fun r s => ∑ᶠ t, (negOnePow t * cbz ℓ t)
      * β (mode (A₁.YM a) (ℓ + r - t) (mode (A₁.YM b) (s + t) y₁)) y₂ with hU
  set V : ℤ → ℤ → ℂ := fun s r => ∑ᶠ t, (negOnePow t * cbz ℓ t)
      * β (mode (A₁.YM b) (ℓ + s - t) (mode (A₁.YM a) (r + t) y₁)) y₂ with hV
  have hjac : ∀ r s, U r s - negOnePow ℓ * V s r = ∑ᶠ i, cbz r i * g i (r + s - i) := by
    intro r s
    have hJ := congrArg (β.flip y₂) (A₁.jacobi a b y₁ ℓ r s)
    set K : ℤ := max (max (Nb - s) (Na - r)) (Nab - ℓ) with hK
    rw [map_finsum (β.flip y₂) (hfs_of _ 0 K fun i hi => by
        rcases hi with hi | hi
        · rw [cbz_neg hi, mul_zero, zero_smul]
        · rw [hNb _ (by omega), hNa _ (by omega)]; simp),
      map_finsum (β.flip y₂) (hfs_of _ 0 K fun i hi => by
        rcases hi with hi | hi
        · rw [cbz_neg hi, zero_smul]
        · rw [hNab _ (by omega)]; simp)] at hJ
    simp only [map_sub, map_smul, smul_eq_mul, LinearMap.flip_apply] at hJ
    simp only [hU, hV, hg]
    rw [← hJ, mul_finsum, ← finsum_sub_distrib
      (hfs_of _ 0 K fun i hi => by
        rcases hi with hi | hi
        · rw [cbz_neg hi]; ring
        · rw [hNb _ (by omega)]; simp)
      (hfs_of _ 0 K fun i hi => by
        rcases hi with hi | hi
        · rw [cbz_neg hi]; ring
        · rw [hNa _ (by omega)]; simp)]
    exact finsum_congr fun i => by ring
  -- boxes
  set B : ℤ := Na' + Nb' + max (Nu - ℓ) 0 + max (Nv - ℓ) 0 + I + max S 0 + 1 with hB
  have hUbox : ∀ r s, (r < -B ∨ B < r ∨ s < -B ∨ B < s) → cbz m r * cbz n s * U r s = 0 := by
    intro r s h
    rcases lt_or_ge r 0 with hr | hr
    · rw [cbz_neg hr]; ring
    rcases lt_or_ge s 0 with hs | hs
    · rw [cbz_neg hs]; ring
    have : U r s = 0 := by
      simp only [hU]
      refine finsum_eq_zero_of_forall_eq_zero fun t => ?_
      rcases lt_or_ge t 0 with ht | ht
      · rw [cbz_neg ht]; ring
      rcases le_or_gt Nb (s + t) with hst | hst
      · rw [hNb _ hst]; simp
      · rw [hNu (s + t) (by omega) (by omega) _ (by omega)]; simp
    rw [this, mul_zero]
  have hVbox : ∀ s r, (s < -B ∨ B < s ∨ r < -B ∨ B < r) → cbz n s * cbz m r * V s r = 0 := by
    intro s r h
    rcases lt_or_ge r 0 with hr | hr
    · rw [cbz_neg hr]; ring
    rcases lt_or_ge s 0 with hs | hs
    · rw [cbz_neg hs]; ring
    have : V s r = 0 := by
      simp only [hV]
      refine finsum_eq_zero_of_forall_eq_zero fun t => ?_
      rcases lt_or_ge t 0 with ht | ht
      · rw [cbz_neg ht]; ring
      rcases le_or_gt Na (r + t) with hrt | hrt
      · rw [hNa _ hrt]; simp
      · rw [hNv (r + t) (by omega) (by omega) _ (by omega)]; simp
    rw [this, mul_zero]
  have hWbox : ∀ r s, (r < -B ∨ B < r ∨ s < -B ∨ B < s) →
      cbz m r * cbz n s * ∑ᶠ i, cbz r i * g i (r + s - i) = 0 := by
    intro r s h
    rcases lt_or_ge r 0 with hr | hr
    · rw [cbz_neg hr]; ring
    rcases lt_or_ge s 0 with hs | hs
    · rw [cbz_neg hs]; ring
    have : ∑ᶠ i, cbz r i * g i (r + s - i) = 0 := by
      refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
      rcases lt_or_ge i 0 with hi | hi
      · rw [cbz_neg hi]; ring
      rcases le_or_gt (I + 1) i with hI' | hI'
      · rw [hg0 i _ hi (Or.inl hI')]; ring
      · rw [hg0 i _ hi (Or.inr (by omega))]; ring
    rw [this, mul_zero]
  have hcomb : (∑ᶠ r, ∑ᶠ s, cbz m r * cbz n s * U r s)
      - negOnePow ℓ * (∑ᶠ s, ∑ᶠ r, cbz n s * cbz m r * V s r)
      = ∑ᶠ r, ∑ᶠ s, cbz m r * cbz n s * ∑ᶠ i, cbz r i * g i (r + s - i) := by
    rw [finsum2_Icc _ B hUbox, finsum2_Icc _ B hVbox, finsum2_Icc _ B hWbox, Finset.sum_comm
      (f := fun s r => cbz n s * cbz m r * V s r), Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← hjac r s]
    ring
  simp only [hU, hV] at hcomb
  rw [hcomb, iter_lemma m n g (I + 1) (max S 0) hg0]

/-! ## The mixed terms cancel -/

theorem mixed_eq_1 (a b : 𝒱) (ℓ m n : ℤ) (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) (y₁ : M₁) (y₂ : M₂) :
    ∑ᶠ i, (negOnePow i * cbz ℓ i) * ∑ᶠ r, cbz (ℓ + m - i) r
        * β (mode (A₁.YM a) r y₁) (mode (A₂.YM b) (n + i) y₂)
      = negOnePow ℓ * ∑ᶠ r, ∑ᶠ t, cbz m (r - t) * (negOnePow t * cbz ℓ t)
          * InR A₂ b n (ℓ - t) β (mode (A₁.YM a) r y₁) y₂ := by
  obtain ⟨Na, hNa⟩ := A₁.truncation a y₁
  obtain ⟨Nb, hNb⟩ := A₂.truncation b y₂
  have := mix_lemma ℓ m (fun r j => β (mode (A₁.YM a) r y₁) (mode (A₂.YM b) (n + j) y₂)) Na
    (Nb - n) (fun r j h => by
      rcases h with h | h
      · dsimp only; rw [hNa r h]; simp
      · dsimp only; rw [hNb _ (by omega)]; simp)
  unfold InR
  rw [this]

theorem mixed_eq_2 (a b : 𝒱) (ℓ m n : ℤ) (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) (y₁ : M₁) (y₂ : M₂) :
    negOnePow ℓ * ∑ᶠ s, ∑ᶠ t, cbz n (s - t) * (negOnePow t * cbz ℓ t)
          * InR A₂ a m (ℓ - t) β (mode (A₁.YM b) s y₁) y₂
      = ∑ᶠ i, (negOnePow i * cbz ℓ i) * ∑ᶠ s, cbz (ℓ + n - i) s
        * β (mode (A₁.YM b) s y₁) (mode (A₂.YM a) (m + i) y₂) := by
  obtain ⟨Nb, hNb⟩ := A₁.truncation b y₁
  obtain ⟨Na, hNa⟩ := A₂.truncation a y₂
  have := mix_lemma ℓ n (fun s j => β (mode (A₁.YM b) s y₁) (mode (A₂.YM a) (m + j) y₂)) Nb
    (Na - m) (fun s j h => by
      rcases h with h | h
      · dsimp only; rw [hNb s h]; simp
      · dsimp only; rw [hNa _ (by omega)]; simp)
  unfold InR
  rw [this]

/-! ## Splitting the two sides -/

theorem sum6_split (f1 f2 f3 f4 f5 f6 : ℤ → ℂ) (S : Finset ℤ) (c : ℂ) :
    ∑ i ∈ S, ((f1 i + f2 i + f3 i) - c * (f4 i + f5 i + f6 i))
      = (∑ i ∈ S, f1 i + ∑ i ∈ S, f2 i + ∑ i ∈ S, f3 i)
        - c * (∑ i ∈ S, f4 i + ∑ i ∈ S, f5 i + ∑ i ∈ S, f6 i) := by
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_add_distrib]

theorem lhs_split {a b : 𝒱} {β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ} (hta : TruncAt A₁ A₂ a β)
    (htb : TruncAt A₁ A₂ b β) (ℓ m n : ℤ) (y₁ : M₁) (y₂ : M₂) :
    ∑ᶠ i, (negOnePow i * cbz ℓ i) * (rhoL A₁ A₂ b (n + i) (rhoL A₁ A₂ a (ℓ + m - i) β) y₁ y₂
        - negOnePow ℓ * rhoL A₁ A₂ a (m + i) (rhoL A₁ A₂ b (ℓ + n - i) β) y₁ y₂)
      = (∑ᶠ i, (negOnePow i * cbz ℓ i)
            * β y₁ (mode (A₂.YM a) (ℓ + m - i) (mode (A₂.YM b) (n + i) y₂))
          + ∑ᶠ i, (negOnePow i * cbz ℓ i) * ∑ᶠ r, cbz (ℓ + m - i) r
            * β (mode (A₁.YM a) r y₁) (mode (A₂.YM b) (n + i) y₂)
          + ∑ᶠ i, (negOnePow i * cbz ℓ i) * ∑ᶠ s, cbz (n + i) s
            * rhoL A₁ A₂ a (ℓ + m - i) β (mode (A₁.YM b) s y₁) y₂)
        - negOnePow ℓ * (∑ᶠ i, (negOnePow i * cbz ℓ i)
            * β y₁ (mode (A₂.YM b) (ℓ + n - i) (mode (A₂.YM a) (m + i) y₂))
          + ∑ᶠ i, (negOnePow i * cbz ℓ i) * ∑ᶠ s, cbz (ℓ + n - i) s
            * β (mode (A₁.YM b) s y₁) (mode (A₂.YM a) (m + i) y₂)
          + ∑ᶠ i, (negOnePow i * cbz ℓ i) * ∑ᶠ r, cbz (m + i) r
            * rhoL A₁ A₂ b (ℓ + n - i) β (mode (A₁.YM a) r y₁) y₂) := by
  obtain ⟨Pa, hPa⟩ := hta
  obtain ⟨Pb, hPb⟩ := htb
  obtain ⟨Na, hNa⟩ := A₂.truncation a y₂
  obtain ⟨Nb, hNb⟩ := A₂.truncation b y₂
  set K : ℤ := max (max (Nb - n) (ℓ + m - Pa)) (max (Na - m) (ℓ + n - Pb)) with hK
  have hpt : ∀ i, (negOnePow i * cbz ℓ i)
        * (rhoL A₁ A₂ b (n + i) (rhoL A₁ A₂ a (ℓ + m - i) β) y₁ y₂
          - negOnePow ℓ * rhoL A₁ A₂ a (m + i) (rhoL A₁ A₂ b (ℓ + n - i) β) y₁ y₂)
      = ((negOnePow i * cbz ℓ i)
            * β y₁ (mode (A₂.YM a) (ℓ + m - i) (mode (A₂.YM b) (n + i) y₂))
          + (negOnePow i * cbz ℓ i) * ∑ᶠ r, cbz (ℓ + m - i) r
            * β (mode (A₁.YM a) r y₁) (mode (A₂.YM b) (n + i) y₂)
          + (negOnePow i * cbz ℓ i) * ∑ᶠ s, cbz (n + i) s
            * rhoL A₁ A₂ a (ℓ + m - i) β (mode (A₁.YM b) s y₁) y₂)
        - negOnePow ℓ * ((negOnePow i * cbz ℓ i)
            * β y₁ (mode (A₂.YM b) (ℓ + n - i) (mode (A₂.YM a) (m + i) y₂))
          + (negOnePow i * cbz ℓ i) * ∑ᶠ s, cbz (ℓ + n - i) s
            * β (mode (A₁.YM b) s y₁) (mode (A₂.YM a) (m + i) y₂)
          + (negOnePow i * cbz ℓ i) * ∑ᶠ r, cbz (m + i) r
            * rhoL A₁ A₂ b (ℓ + n - i) β (mode (A₁.YM a) r y₁) y₂) := by
    intro i
    rw [rhoL_apply A₁ A₂ (rhoL A₁ A₂ a (ℓ + m - i) β) b,
      rhoL_apply A₁ A₂ β a (ℓ + m - i) y₁ (mode (A₂.YM b) (n + i) y₂),
      rhoL_apply A₁ A₂ (rhoL A₁ A₂ b (ℓ + n - i) β) a,
      rhoL_apply A₁ A₂ β b (ℓ + n - i) y₁ (mode (A₂.YM a) (m + i) y₂)]
    ring
  rw [finsum_congr hpt]
  have z1 : ∀ i, K < i → mode (A₂.YM b) (n + i) y₂ = 0 := fun i hi => hNb _ (by omega)
  have z2 : ∀ i, K < i → mode (A₂.YM a) (m + i) y₂ = 0 := fun i hi => hNa _ (by omega)
  have z3 : ∀ i, K < i → rhoL A₁ A₂ a (ℓ + m - i) β = 0 := fun i hi => hPa _ (by omega)
  have z4 : ∀ i, K < i → rhoL A₁ A₂ b (ℓ + n - i) β = 0 := fun i hi => hPb _ (by omega)
  have e1 := finsum_eq_Icc' (fun i => (negOnePow i * cbz ℓ i)
      * β y₁ (mode (A₂.YM a) (ℓ + m - i) (mode (A₂.YM b) (n + i) y₂))) 0 K (fun i hi => by
    rcases hi with hi | hi
    · dsimp only; rw [cbz_neg hi]; ring
    · dsimp only; rw [z1 i hi]; simp)
  have e2 := finsum_eq_Icc' (fun i => (negOnePow i * cbz ℓ i) * ∑ᶠ r, cbz (ℓ + m - i) r
      * β (mode (A₁.YM a) r y₁) (mode (A₂.YM b) (n + i) y₂)) 0 K (fun i hi => by
    rcases hi with hi | hi
    · dsimp only; rw [cbz_neg hi]; ring
    · dsimp only; rw [z1 i hi]; simp)
  have e3 := finsum_eq_Icc' (fun i => (negOnePow i * cbz ℓ i) * ∑ᶠ s, cbz (n + i) s
      * rhoL A₁ A₂ a (ℓ + m - i) β (mode (A₁.YM b) s y₁) y₂) 0 K (fun i hi => by
    rcases hi with hi | hi
    · dsimp only; rw [cbz_neg hi]; ring
    · dsimp only; rw [z3 i hi]; simp)
  have e4 := finsum_eq_Icc' (fun i => (negOnePow i * cbz ℓ i)
      * β y₁ (mode (A₂.YM b) (ℓ + n - i) (mode (A₂.YM a) (m + i) y₂))) 0 K (fun i hi => by
    rcases hi with hi | hi
    · dsimp only; rw [cbz_neg hi]; ring
    · dsimp only; rw [z2 i hi]; simp)
  have e5 := finsum_eq_Icc' (fun i => (negOnePow i * cbz ℓ i) * ∑ᶠ s, cbz (ℓ + n - i) s
      * β (mode (A₁.YM b) s y₁) (mode (A₂.YM a) (m + i) y₂)) 0 K (fun i hi => by
    rcases hi with hi | hi
    · dsimp only; rw [cbz_neg hi]; ring
    · dsimp only; rw [z2 i hi]; simp)
  have e6 := finsum_eq_Icc' (fun i => (negOnePow i * cbz ℓ i) * ∑ᶠ r, cbz (m + i) r
      * rhoL A₁ A₂ b (ℓ + n - i) β (mode (A₁.YM a) r y₁) y₂) 0 K (fun i hi => by
    rcases hi with hi | hi
    · dsimp only; rw [cbz_neg hi]; ring
    · dsimp only; rw [z4 i hi]; simp)
  beta_reduce at e1 e2 e3 e4 e5 e6
  rw [e1, e2, e3, e4, e5, e6]
  rw [finsum_eq_Icc' _ 0 K (fun i hi => by
    rcases hi with hi | hi
    · rw [cbz_neg hi]; ring
    · rw [z1 i hi, z2 i hi, z3 i hi, z4 i hi]; simp)]
  exact sum6_split _ _ _ _ _ _ _ _

theorem rhs_split (a b : 𝒱) (ℓ m n : ℤ) (β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) (y₁ : M₁) (y₂ : M₂) :
    ∑ᶠ i, cbz m i * rhoL A₁ A₂ (W.smul a (ℓ + i) b) (m + n - i) β y₁ y₂
      = ∑ᶠ i, cbz m i * β y₁ (mode (A₂.YM (W.smul a (ℓ + i) b)) (m + n - i) y₂)
        + ∑ᶠ i, cbz m i * ∑ᶠ s, cbz (m + n - i) s
          * β (mode (A₁.YM (W.smul a (ℓ + i) b)) s y₁) y₂ := by
  obtain ⟨Nab, hNab⟩ := W.toPreVertexAlgebra.smul_eventually_zero a b
  rw [← finsum_add_distrib
    (hfs_of _ 0 (Nab - ℓ) fun i hi => by
      rcases hi with hi | hi
      · rw [cbz_neg hi]; ring
      · rw [hNab _ (by omega)]; simp)
    (hfs_of _ 0 (Nab - ℓ) fun i hi => by
      rcases hi with hi | hi
      · rw [cbz_neg hi]; ring
      · rw [hNab _ (by omega)]; simp)]
  refine finsum_congr fun i => ?_
  rw [rhoL_apply]
  ring

/-! ## The reversed Jacobi identity -/

/-- **The reversed Jacobi identity for `ρ`** at every point, for every lower-truncated form
satisfying the compatibility condition for `a` and `b`. -/
theorem rho_jacobi_pt {a b : 𝒱} {β : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ} (hta : TruncAt A₁ A₂ a β)
    (htb : TruncAt A₁ A₂ b β) (hca : CompatAt A₁ A₂ a β) (hcb : CompatAt A₁ A₂ b β)
    (ℓ m n : ℤ) (y₁ : M₁) (y₂ : M₂) :
    ∑ᶠ i, (negOnePow i * cbz ℓ i) * (rhoL A₁ A₂ b (n + i) (rhoL A₁ A₂ a (ℓ + m - i) β) y₁ y₂
        - negOnePow ℓ * rhoL A₁ A₂ a (m + i) (rhoL A₁ A₂ b (ℓ + n - i) β) y₁ y₂)
      = ∑ᶠ i, cbz m i * rhoL A₁ A₂ (W.smul a (ℓ + i) b) (m + n - i) β y₁ y₂ := by
  rw [lhs_split A₁ A₂ hta htb, rhs_split,
    loc_eq A₁ A₂ hta hca ℓ m n y₁ y₂ (d := b), loc_eq A₁ A₂ htb hcb ℓ n m y₁ y₂ (d := a),
    reindex_eq A₁ a b m n ℓ β y₁ y₂, reindex_eq A₁ b a n m ℓ β y₁ y₂]
  have h2 := p2_eq A₂ a b ℓ m n β y₁ y₂
  have h1 := p1_eq A₁ a b ℓ m n β y₁ y₂
  have hm1 := mixed_eq_1 A₁ A₂ a b ℓ m n β y₁ y₂
  have hm2 := mixed_eq_2 A₁ A₂ a b ℓ m n β y₁ y₂
  have hs : negOnePow ℓ * negOnePow ℓ = 1 := negOnePow_mul_self ℓ
  set ALR := ∑ᶠ s, ∑ᶠ t, cbz n (s - t) * (negOnePow t * cbz ℓ t)
          * InR A₂ a m (ℓ - t) β (mode (A₁.YM b) s y₁) y₂ with hALR
  linear_combination h2 + h1 + hm1 + negOnePow ℓ * hm2 - ALR * hs

end Jacobi

end VOA.Huang.PzTensorRho
