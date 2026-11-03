/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Modularity.ZhuCoordinateCoeff
import VOA.Modularity.SquareBracketVirasoro
import VOA.Modularity.SqWeightSpanning
import VOA.Core.DeformationLiftedModes
import VOA.Modules.ZhuModule

/-!
# Square-bracket current modes satisfy the ordinary current relations

For a VOA `W` and weight-one states `a, b`, Zhu's square-bracket modes `a[m] = vSqZ W a 1 m`
obey exactly the same relations as the ordinary modes, *without* Zhu's change-of-coordinates
isomorphism:

* `sqCurrent_comm` — `[a[m], b[n]] = (a₍₀₎b)[m+n] + m·β·δ_{m+n,0}` when `a₍₁₎b = β·|0⟩`;
* `Lsq_sqCurrent_comm` — `[L[m], a[n]] = -n·a[m+n]` for `a` primary (`L₁a = 0`);
* `vSqZ_L_neg_one` — `(L₋₁a)[n] = -n·a[n-1] - p·a[n]` for `a ∈ V_p` (`p ≥ 1`);
* vacuum: `a[n]|0⟩ = 0` (`n ≥ 0`), `a[-1]|0⟩ = a`; `L[-2]|0⟩ = ω - (c/24)|0⟩`.

Each is proved on homogeneous vectors by expanding into finitely many ordinary modes
(`vSqZ_eq_sum`), applying the ordinary commutator, re-summing along antidiagonals
(`sum_box_eq_antidiag`), and invoking a coefficient identity of `ZhuCoordinateCoeff`.
-/

namespace VOA.ZhuCoordinate

open VOA

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱)

/-! ## Finite expansions -/

theorem smul_eq_zero_of_lt {a x : 𝒱} {p q : ℤ} (ha : a ∈ W.grading p) (hx : x ∈ W.grading q)
    {i : ℤ} (hi : p + q - 1 < i) : W.smul a i x = 0 := by
  have h := W.smul_mem_grading ha hx i
  rw [W.positivity _ (by omega), Submodule.mem_bot] at h
  exact h

/-- On a homogeneous vector a square-bracket mode is a finite sum of ordinary modes. -/
theorem vSqZ_eq_sum {a x : 𝒱} {p q : ℤ} (ha : a ∈ W.grading p) (hx : x ∈ W.grading q) (k : ℕ)
    (m : ℤ) (B : ℕ) (hB : p + q - 1 < m + B) :
    vSqZ W a k m x = ∑ s ∈ Finset.range B, sqBracketCoeffZ k m (m + s) • W.smul a (m + s) x := by
  rw [vSqZ_apply]
  let e : ℕ ↪ ℤ := ⟨fun s : ℕ => m + s, fun s t h => by simpa using h⟩
  rw [finsum_eq_sum_of_support_subset _ (s := (Finset.range B).map e)]
  · rw [Finset.sum_map]; rfl
  · intro i hi
    simp only [Function.mem_support] at hi
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Finset.mem_range]
    have h1 : m ≤ i := by
      by_contra h
      exact hi (by rw [sqBracketCoeffZ_of_lt k (by omega), zero_smul])
    have h2 : i ≤ p + q - 1 := by
      by_contra h
      exact hi (by
        rw [show mode (W.Y a) i x = W.smul a i x from rfl,
          smul_eq_zero_of_lt W ha hx (by omega), smul_zero])
    exact ⟨(i - m).toNat, by omega, by simp only [e, Function.Embedding.coeFn_mk]; omega⟩

/-- A box sum equals an antidiagonal sum when the summand vanishes off the triangle. -/
theorem sum_box_eq_antidiag {M : Type*} [AddCommMonoid M] (B : ℕ) (F : ℕ → ℕ → M)
    (hF : ∀ p r, B ≤ p + r → F p r = 0) :
    ∑ p ∈ Finset.range B, ∑ r ∈ Finset.range B, F p r
      = ∑ t ∈ Finset.range B, ∑ x ∈ Finset.antidiagonal t, F x.1 x.2 := by
  rw [← Finset.sum_product', Finset.sum_sigma']
  refine Finset.sum_bij_ne_zero (fun x _ _ => ⟨x.1 + x.2, x⟩) ?_ ?_ ?_ ?_
  · intro x _ hne
    rw [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal]
    refine ⟨?_, rfl⟩
    show x.1 + x.2 < B
    by_contra h
    exact hne (hF _ _ (by omega))
  · intro x _ _ y _ _ h
    simp only [Sigma.mk.inj_iff] at h
    exact eq_of_heq h.2
  · rintro ⟨t, ⟨p, r⟩⟩ hy hne
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal] at hy
    obtain ⟨ht, rfl⟩ := hy
    refine ⟨(p, r), ?_, hne, rfl⟩
    simp only [Finset.mem_product, Finset.mem_range]
    omega
  · intro x _ _
    rfl

/-- The commutator of two square-bracket modes on a homogeneous vector, as a box sum of ordinary
commutators. -/
theorem vSqZ_comm_box {a b x : 𝒱} {pa pb q : ℤ} (ha : a ∈ W.grading pa) (hb : b ∈ W.grading pb)
    (hx : x ∈ W.grading q) (ka kb : ℕ) (m n : ℤ) (B : ℕ)
    (h1 : pb + q - 1 < n + B) (h2 : pa + pb + q - n - 2 < m + B) (h3 : pa + q - 1 < m + B) :
    vSqZ W a ka m (vSqZ W b kb n x) - vSqZ W b kb n (vSqZ W a ka m x)
      = ∑ p ∈ Finset.range B, ∑ r ∈ Finset.range B,
          (sqBracketCoeffZ ka m (m + p) * sqBracketCoeffZ kb n (n + r)) •
            (W.smul a (m + p) (W.smul b (n + r) x) - W.smul b (n + r) (W.smul a (m + p) x)) := by
  rw [vSqZ_eq_sum W hb hx kb n B h1, vSqZ_eq_sum W ha hx ka m B h3, map_sum, map_sum]
  have eA : ∀ r ∈ Finset.range B, vSqZ W a ka m
      (sqBracketCoeffZ kb n (n + r) • W.smul b (n + r) x)
      = ∑ p ∈ Finset.range B, sqBracketCoeffZ kb n (n + r) •
          (sqBracketCoeffZ ka m (m + p) • W.smul a (m + p) (W.smul b (n + r) x)) := by
    intro r _
    have hy : W.smul b (n + r) x ∈ W.grading (pb + q - (n + r) - 1) :=
      W.smul_mem_grading hb hx _
    rw [map_smul, vSqZ_eq_sum W ha hy ka m B (by omega), Finset.smul_sum]
  have eB : ∀ p ∈ Finset.range B, vSqZ W b kb n
      (sqBracketCoeffZ ka m (m + p) • W.smul a (m + p) x)
      = ∑ r ∈ Finset.range B, sqBracketCoeffZ ka m (m + p) •
          (sqBracketCoeffZ kb n (n + r) • W.smul b (n + r) (W.smul a (m + p) x)) := by
    intro p _
    have hy : W.smul a (m + p) x ∈ W.grading (pa + q - (m + p) - 1) :=
      W.smul_mem_grading ha hx _
    rw [map_smul, vSqZ_eq_sum W hb hy kb n B (by omega), Finset.smul_sum]
  rw [Finset.sum_congr rfl eA, Finset.sum_congr rfl eB, Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [smul_smul, smul_smul, mul_comm (sqBracketCoeffZ kb n _), smul_sub]

/-! ## Square current commutator -/

/-- Homogeneous case of `sqCurrent_comm`. -/
theorem sqCurrent_comm_homog {a b x : 𝒱} (ha : a ∈ W.grading 1) (hb : b ∈ W.grading 1)
    {β : ℂ} (hp : W.smul a 1 b = β • W.vacuum) {q : ℤ} (hx : x ∈ W.grading q) (m n : ℤ) :
    vSqZ W a 1 m (vSqZ W b 1 n x) - vSqZ W b 1 n (vSqZ W a 1 m x)
      = vSqZ W (W.smul a 0 b) 1 (m + n) x + (if m + n = 0 then ((m : ℂ) * β) • x else 0) := by
  set B : ℕ := (q - m - n + 1).toNat + (q - m + 1).toNat + (q - n + 1).toNat + (1 - m - n).toNat
    with hBdef
  have hB1 : q - m - n + 1 ≤ (B : ℤ) := by omega
  have hB2 : q - m + 1 ≤ (B : ℤ) := by omega
  have hB3 : q - n + 1 ≤ (B : ℤ) := by omega
  have hB4 : 1 - m - n ≤ (B : ℤ) := by omega
  have hab : W.smul a 0 b ∈ W.grading 1 := by simpa using W.smul_mem_grading ha hb 0
  rw [vSqZ_comm_box W ha hb hx 1 1 m n B (by omega) (by omega) (by omega)]
  -- the ordinary commutator
  have hcomm : ∀ p r : ℕ, W.smul a (m + p) (W.smul b (n + r) x)
      - W.smul b (n + r) (W.smul a (m + p) x)
      = W.smul (W.smul a 0 b) (m + n + ↑(p + r)) x
        + (if m + n + ↑(p + r) = 0 then (((m : ℂ) + p) * β) • x else 0) := by
    intro p r
    have h := VOA.Deform.current_mode_commutator (W := W) ha hb β hp x (m + p) (n + r)
    rw [h, show m + ↑p + (n + ↑r) = m + n + ↑(p + r) by push_cast; ring]
    push_cast
    rfl
  simp_rw [hcomm]
  rw [sum_box_eq_antidiag B (fun p r => (sqBracketCoeffZ 1 m (m + p) * sqBracketCoeffZ 1 n (n + r)) •
      (W.smul (W.smul a 0 b) (m + n + ↑(p + r)) x
        + (if m + n + ↑(p + r) = 0 then (((m : ℂ) + p) * β) • x else 0)))]
  swap
  · intro p r hpr
    rw [smul_eq_zero_of_lt W hab hx (by push_cast; omega), if_neg (by push_cast; omega),
      add_zero, smul_zero]
  have hinner : ∀ t ∈ Finset.range B, ∑ x' ∈ Finset.antidiagonal t,
      (sqBracketCoeffZ 1 m (m + x'.1) * sqBracketCoeffZ 1 n (n + x'.2)) •
        (W.smul (W.smul a 0 b) (m + n + ↑(x'.1 + x'.2)) x
          + (if m + n + ↑(x'.1 + x'.2) = 0 then (((m : ℂ) + x'.1) * β) • x else 0))
      = sqBracketCoeffZ 1 (m + n) (m + n + t) • W.smul (W.smul a 0 b) (m + n + t) x
        + (if m + n + t = 0 then (((if t = 0 then (m : ℂ) else 0)) * β) • x else 0) := by
    intro t _
    have hx' : ∀ x' ∈ Finset.antidiagonal t,
        (sqBracketCoeffZ 1 m (m + x'.1) * sqBracketCoeffZ 1 n (n + x'.2)) •
          (W.smul (W.smul a 0 b) (m + n + ↑(x'.1 + x'.2)) x
            + (if m + n + ↑(x'.1 + x'.2) = 0 then (((m : ℂ) + x'.1) * β) • x else 0))
        = (sqBracketCoeffZ 1 m (m + x'.1) * sqBracketCoeffZ 1 n (n + x'.2)) •
            W.smul (W.smul a 0 b) (m + n + t) x
          + (if m + n + t = 0 then
              ((((m : ℂ) + x'.1) * sqBracketCoeffZ 1 m (m + x'.1) * sqBracketCoeffZ 1 n (n + x'.2))
                * β) • x else 0) := by
      intro x' hx'
      rw [Finset.mem_antidiagonal] at hx'
      rw [hx', smul_add]
      congr 1
      split_ifs
      · rw [smul_smul]; congr 1; ring
      · rw [smul_zero]
    rw [Finset.sum_congr rfl hx', Finset.sum_add_distrib, ← Finset.sum_smul,
      antidiag_coeff_one]
    congr 1
    by_cases h0 : m + n + (t : ℤ) = 0
    · simp only [if_pos h0]
      rw [← Finset.sum_smul, ← Finset.sum_mul, antidiag_central m n t h0]
    · simp only [if_neg h0]
      simp
  rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib,
    ← vSqZ_eq_sum W hab hx 1 (m + n) B (by omega)]
  congr 1
  by_cases hmn : m + n = 0
  · rw [if_pos hmn, Finset.sum_eq_single 0]
    · simp [hmn]
    · intro t _ ht
      rw [if_neg (by omega)]
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  · rw [if_neg hmn]
    refine Finset.sum_eq_zero fun t _ => ?_
    split_ifs with h1 h2
    · omega
    · simp
    · rfl


/-! ## From homogeneous vectors to all vectors -/

/-- Two linear maps agreeing on every homogeneous vector are equal. -/
theorem linearMap_ext_homog {f g : 𝒱 →ₗ[ℂ] 𝒱}
    (h : ∀ (q : ℤ) (x : 𝒱), x ∈ W.grading q → f x = g x) : f = g := by
  ext x
  have hx : x ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; trivial
  exact Submodule.iSup_induction (fun i => W.grading i) (motive := fun x => f x = g x) hx
    (fun q y hy => h q y hy) (by simp) (fun y z hy hz => by simp only at hy hz ⊢; rw [map_add, map_add, hy, hz])

/-- **The square-bracket current commutator** (any VOA, `a, b ∈ V₁`, `a₍₁₎b = β|0⟩`):
`[a[m], b[n]] = (a₍₀₎b)[m+n] + m·β·δ_{m+n,0}`. -/
theorem sqCurrent_comm {a b : 𝒱} (ha : a ∈ W.grading 1) (hb : b ∈ W.grading 1)
    {β : ℂ} (hp : W.smul a 1 b = β • W.vacuum) (m n : ℤ) (x : 𝒱) :
    vSqZ W a 1 m (vSqZ W b 1 n x) - vSqZ W b 1 n (vSqZ W a 1 m x)
      = vSqZ W (W.smul a 0 b) 1 (m + n) x + (if m + n = 0 then ((m : ℂ) * β) • x else 0) := by
  have key : vSqZ W a 1 m ∘ₗ vSqZ W b 1 n - vSqZ W b 1 n ∘ₗ vSqZ W a 1 m
      = vSqZ W (W.smul a 0 b) 1 (m + n)
        + (if m + n = 0 then ((m : ℂ) * β) • LinearMap.id else 0) := by
    refine linearMap_ext_homog W fun q y hy => ?_
    rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      sqCurrent_comm_homog W ha hb hp hy m n, LinearMap.add_apply]
    split_ifs <;> simp
  have := LinearMap.congr_fun key x
  rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.add_apply] at this
  rw [this]
  split_ifs <;> simp

/-! ## The Virasoro modes on square currents -/

/-- The ordinary commutator of `ω` with a primary weight-one state:
`[ω₍ᵢ₎, a₍ⱼ₎] = -j·a₍ᵢ₊ⱼ₋₁₎`. -/
theorem omega_current_comm {a : 𝒱} (ha : a ∈ W.grading 1) (ha1 : W.L 1 a = 0) (x : 𝒱)
    (i j : ℤ) :
    W.smul W.conformalVector i (W.smul a j x) - W.smul a j (W.smul W.conformalVector i x)
      = (-(j : ℂ)) • W.smul a (i + j - 1) x := by
  have h := W.jacobi W.conformalVector a x 0 i j
  rw [finsum_eq_single _ (0 : ℤ)
    (fun l hl => by rw [cbz_zero_left, if_neg hl, mul_zero, zero_smul])] at h
  simp only [cbz_zero_left, mul_one, one_smul, negOnePow,
    Even.zero, if_pos, zero_add, add_zero, sub_zero] at h
  rw [h]
  let F : ℤ → 𝒱 := fun l => cbz i l • W.smul (W.smul W.conformalVector l a) (i + j - l) x
  have hsupp : Function.support F ⊆ (↑({0, 1} : Finset ℤ) : Set ℤ) := by
    intro l hl
    by_contra hh
    have h0 : l ≠ 0 := fun h => hh (by simp [h])
    have h1 : l ≠ 1 := fun h => hh (by simp [h])
    apply hl
    dsimp [F]
    by_cases hn : l < 0
    · rw [cbz_apply_neg i hn, zero_smul]
    · by_cases h2 : l = 2
      · subst h2
        have : W.smul W.conformalVector 2 a = W.L 1 a := rfl
        rw [this, ha1, PreVertexAlgebra.smul_zero_left, smul_zero]
      · rw [smul_eq_zero_of_lt W W.conformal_mem ha (by omega), PreVertexAlgebra.smul_zero_left,
          smul_zero]
  change (∑ᶠ l : ℤ, F l) = _
  rw [finsum_eq_sum_of_support_subset F hsupp]
  have hb1 : cbz i 1 = (i : ℂ) := by simp [cbz, gBinom]
  have hL0 : W.smul W.conformalVector 0 a = W.L (-1) a := rfl
  have hL1 : W.smul W.conformalVector 1 a = a := by
    have : W.smul W.conformalVector 1 a = W.L 0 a := rfl
    rw [this, W.L_zero_grading a ha]; simp
  simp only [Finset.sum_insert, Finset.mem_singleton, zero_ne_one, not_false_eq_true,
    Finset.sum_singleton, F, cbz_zero, one_smul, sub_zero, hb1, hL0, hL1, smul_L_neg_one]
  rw [show i + j - 1 = i + j - 1 from rfl, ← Int.cast_smul_eq_zsmul ℂ]
  push_cast
  rw [← add_smul]
  congr 1
  ring

/-- Homogeneous case of `Lsq_sqCurrent_comm`. -/
theorem omegaSq_sqCurrent_comm_homog {a : 𝒱} (ha : a ∈ W.grading 1) (ha1 : W.L 1 a = 0)
    {q : ℤ} {x : 𝒱} (hx : x ∈ W.grading q) (m n : ℤ) :
    vSqZ W W.conformalVector 2 (m + 1) (vSqZ W a 1 n x)
        - vSqZ W a 1 n (vSqZ W W.conformalVector 2 (m + 1) x)
      = (-(n : ℂ)) • vSqZ W a 1 (m + n) x := by
  set B : ℕ := (q - m - n + 1).toNat + (q - m + 1).toNat + (q - n + 1).toNat with hBdef
  have hB1 : q - m - n + 1 ≤ (B : ℤ) := by omega
  have hB2 : q - m + 1 ≤ (B : ℤ) := by omega
  have hB3 : q - n + 1 ≤ (B : ℤ) := by omega
  rw [vSqZ_comm_box W W.conformal_mem ha hx 2 1 (m + 1) n B (by omega) (by omega) (by omega)]
  have hcomm : ∀ p r : ℕ, W.smul W.conformalVector (m + 1 + p) (W.smul a (n + r) x)
      - W.smul a (n + r) (W.smul W.conformalVector (m + 1 + p) x)
      = (-((n : ℂ) + r)) • W.smul a (m + n + ↑(p + r)) x := by
    intro p r
    rw [omega_current_comm W ha ha1, show m + 1 + ↑p + (n + ↑r) - 1 = m + n + ↑(p + r) by
      push_cast; ring]
    push_cast; rfl
  simp_rw [hcomm]
  rw [sum_box_eq_antidiag B (fun p r => (sqBracketCoeffZ 2 (m + 1) (m + 1 + p)
      * sqBracketCoeffZ 1 n (n + r)) • ((-((n : ℂ) + r)) • W.smul a (m + n + ↑(p + r)) x))]
  swap
  · intro p r hpr
    rw [smul_eq_zero_of_lt W ha hx (by push_cast; omega), smul_zero, smul_zero]
  rw [vSqZ_eq_sum W ha hx 1 (m + n) B (by omega), Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hx' : ∀ x' ∈ Finset.antidiagonal t,
      (sqBracketCoeffZ 2 (m + 1) (m + 1 + x'.1) * sqBracketCoeffZ 1 n (n + x'.2)) •
          ((-((n : ℂ) + x'.2)) • W.smul a (m + n + ↑(x'.1 + x'.2)) x)
        = (-(sqBracketCoeffZ 2 (m + 1) (m + 1 + x'.1)
            * (((n : ℂ) + x'.2) * sqBracketCoeffZ 1 n (n + x'.2)))) • W.smul a (m + n + t) x := by
    intro x' hx'
    rw [Finset.mem_antidiagonal] at hx'
    rw [hx', smul_smul]
    congr 1
    ring
  rw [Finset.sum_congr rfl hx', ← Finset.sum_smul, Finset.sum_neg_distrib, antidiag_virasoro,
    smul_smul]
  congr 1
  ring

/-- **`[L[m], a[n]] = -n·a[m+n]`** for a primary weight-one state `a` (any VOA). -/
theorem Lsq_sqCurrent_comm {a : 𝒱} (ha : a ∈ W.grading 1) (ha1 : W.L 1 a = 0) (m n : ℤ)
    (x : 𝒱) :
    Lsq W m (vSqZ W a 1 n x) - vSqZ W a 1 n (Lsq W m x) = (-(n : ℂ)) • vSqZ W a 1 (m + n) x := by
  have key : vSqZ W W.conformalVector 2 (m + 1) ∘ₗ vSqZ W a 1 n
      - vSqZ W a 1 n ∘ₗ vSqZ W W.conformalVector 2 (m + 1) = (-(n : ℂ)) • vSqZ W a 1 (m + n) := by
    refine linearMap_ext_homog W fun q y hy => ?_
    rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      omegaSq_sqCurrent_comm_homog W ha ha1 hy m n, LinearMap.smul_apply]
  have := LinearMap.congr_fun key x
  rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.smul_apply] at this
  rw [Lsq_apply, Lsq_apply, map_sub, map_smul, ← this]
  abel

/-! ## The translation rule -/

/-- **`(L₋₁a)[n] = -n·a[n-1] - p·a[n]`** for `a ∈ V_p`, `p = P+1 ≥ 1` (homogeneous `x`). -/
theorem vSqZ_L_neg_one_homog {a : 𝒱} (P : ℕ) (ha : a ∈ W.grading ((P + 1 : ℕ) : ℤ))
    {q : ℤ} {x : 𝒱} (hx : x ∈ W.grading q) (n : ℤ) :
    vSqZ W (W.L (-1) a) (P + 2) n x
      = (-(n : ℂ)) • vSqZ W a (P + 1) (n - 1) x - ((P : ℂ) + 1) • vSqZ W a (P + 1) n x := by
  set B : ℕ := (P + q - n + 3).toNat with hBdef
  have hB : P + q - n + 3 ≤ (B : ℤ) := by omega
  have hLa : W.L (-1) a ∈ W.grading ((P + 1 : ℕ) + 1 : ℤ) := by
    have := L_mem_grading W ha (-1); simpa using this
  rw [vSqZ_eq_sum W hLa hx (P + 2) n (B + 1) (by push_cast; omega),
    vSqZ_eq_sum W ha hx (P + 1) (n - 1) (B + 1) (by push_cast; omega),
    vSqZ_eq_sum W ha hx (P + 1) n B (by push_cast; omega)]
  have hterm : ∀ s ∈ Finset.range (B + 1), sqBracketCoeffZ (P + 2) n (n + s)
      • W.smul (W.L (-1) a) (n + s) x
      = (-(n : ℂ)) • (sqBracketCoeffZ (P + 1) (n - 1) (n - 1 + s) • W.smul a (n - 1 + s) x)
        - (if s = 0 then 0 else ((P : ℂ) + 1) * sqBracketCoeffZ (P + 1) n (n + (s - 1 : ℕ)))
          • W.smul a (n - 1 + s) x := by
    intro s _
    rw [smul_L_neg_one, ← Int.cast_smul_eq_zsmul ℂ, smul_smul,
      show n + (s : ℤ) - 1 = n - 1 + s by ring, smul_smul, ← sub_smul]
    congr 1
    have h := deriv_coeff P n s
    push_cast
    linear_combination (-1 : ℂ) * h
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.smul_sum]
  congr 1
  rw [Finset.sum_range_succ', if_pos rfl, zero_smul, add_zero, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [if_neg (Nat.succ_ne_zero s), Nat.add_sub_cancel, smul_smul,
    show n - 1 + ((s + 1 : ℕ) : ℤ) = n + (s : ℤ) by push_cast; ring]

/-- **The translation rule** `(L₋₁a)[n] = -n·a[n-1] - p·a[n]`, `a ∈ V_{P+1}`, on all vectors. -/
theorem vSqZ_L_neg_one {a : 𝒱} (P : ℕ) (ha : a ∈ W.grading ((P + 1 : ℕ) : ℤ)) (n : ℤ) :
    vSqZ W (W.L (-1) a) (P + 2) n
      = (-(n : ℂ)) • vSqZ W a (P + 1) (n - 1) - ((P : ℂ) + 1) • vSqZ W a (P + 1) n :=
  linearMap_ext_homog W fun _ _ hy => by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      vSqZ_L_neg_one_homog W P ha hy n]

/-! ## Square modes on the vacuum -/

theorem vSqZ_vacuum_of_nonneg (a : 𝒱) (k : ℕ) {n : ℤ} (hn : 0 ≤ n) :
    vSqZ W a k n W.vacuum = 0 := by
  rw [vSqZ_apply]
  refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
  by_cases hi : i < n
  · rw [sqBracketCoeffZ_of_lt k hi, zero_smul]
  · rw [show mode (W.Y a) i W.vacuum = W.smul a i W.vacuum from rfl,
      PreVertexAlgebra.smul_vacuum_nonneg _ _ (by omega), smul_zero]

theorem vSqZ_neg_one_vacuum (a : 𝒱) (k : ℕ) : vSqZ W a k (-1) W.vacuum = a := by
  rw [vSqZ_apply, finsum_eq_single _ (-1 : ℤ)]
  · rw [sqBracketCoeffZ_diag', one_smul]
    exact PreVertexAlgebra.smul_vacuum_neg_one _ a
  · intro i hi
    by_cases hlt : i < -1
    · rw [sqBracketCoeffZ_of_lt k hlt, zero_smul]
    · rw [show mode (W.Y a) i W.vacuum = W.smul a i W.vacuum from rfl,
        PreVertexAlgebra.smul_vacuum_nonneg _ _ (by omega), smul_zero]

/-- `a[-2]|0⟩ = L₋₁a + a` for `a ∈ V₁`. -/
theorem vSqZ_neg_two_vacuum {a : 𝒱} (ha : a ∈ W.grading 1) :
    vSqZ W a 1 (-2) W.vacuum = W.L (-1) a + a := by
  rw [vSqZ_eq_sum W ha W.vacuum_mem 1 (-2) 3 (by norm_num), Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one]
  have e0 : (-2 : ℤ) + ((0 : ℕ) : ℤ) = -2 := by norm_num
  have e1 : (-2 : ℤ) + ((1 : ℕ) : ℤ) = -1 := by norm_num
  have e2 : (-2 : ℤ) + ((2 : ℕ) : ℤ) = 0 := by norm_num
  rw [e0, e1, e2, PreVertexAlgebra.smul_vacuum_zero, smul_zero, add_zero,
    sqBracketCoeffZ_diag', c_one_neg_two_neg_one, one_smul, one_smul,
    PreVertexAlgebra.smul_vacuum_neg_one, ← VertexOperatorAlgebra.T_eq_Lneg1]
  rfl

/-- `L[-2]|0⟩ = ω - (c/24)|0⟩`. -/
theorem Lsq_neg_two_vacuum :
    Lsq W (-2) W.vacuum = W.conformalVector - (W.centralCharge / 24) • W.vacuum := by
  rw [Lsq_apply, show (-2 : ℤ) + 1 = -1 by norm_num, vSqZ_neg_one_vacuum,
    sqBracketCoeffZ_vacuum_neg_one, mul_one]

/-- `L[0]|0⟩ = 0`. -/
theorem Lsq_zero_vacuum : Lsq W 0 W.vacuum = 0 := by
  rw [Lsq_apply, vSqZ_vacuum_of_nonneg W _ _ (by norm_num),
    sqBracketCoeffZ_vacuum_of_ne _ (by norm_num)]
  simp

/-- `a[-1]b = a₍₋₁₎b + ½ a₍₀₎b - (1/12) a₍₁₎b` for `a, b ∈ V₁`. -/
theorem vSqZ_neg_one_current {a b : 𝒱} (ha : a ∈ W.grading 1) (hb : b ∈ W.grading 1) :
    vSqZ W a 1 (-1) b = W.smul a (-1) b + (1 / 2 : ℂ) • W.smul a 0 b
      - (1 / 12 : ℂ) • W.smul a 1 b := by
  rw [vSqZ_eq_sum W ha hb 1 (-1) 3 (by norm_num), Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  have e0 : (-1 : ℤ) + ((0 : ℕ) : ℤ) = -1 := by norm_num
  have e1 : (-1 : ℤ) + ((1 : ℕ) : ℤ) = 0 := by norm_num
  have e2 : (-1 : ℤ) + ((2 : ℕ) : ℤ) = 1 := by norm_num
  rw [e0, e1, e2, sqBracketCoeffZ_diag', c_one_neg_one_zero, c_one_neg_one_one, one_smul]
  rw [show (-1 / 12 : ℂ) = -(1 / 12) by ring, neg_smul]
  abel

/-! ## The `L[0]`-grading of square currents -/

/-- `a[n]` lowers the `L[0]`-weight by `n` (`a` primary of weight one). -/
theorem vSqZ_mem_sqWeightSpace {a : 𝒱} (ha : a ∈ W.grading 1) (ha1 : W.L 1 a = 0) (n : ℤ)
    {w : ℂ} {x : 𝒱} (hx : x ∈ sqWeightSpace W w) :
    vSqZ W a 1 n x ∈ sqWeightSpace W (w - n) := by
  rw [mem_sqWeightSpace_iff] at hx ⊢
  have h := Lsq_sqCurrent_comm W ha ha1 0 n x
  rw [hx, map_smul, zero_add] at h
  rw [sub_smul, neg_smul] at *
  linear_combination (norm := module) h

end VOA.ZhuCoordinate

section AxiomAudit
#print axioms VOA.ZhuCoordinate.sqCurrent_comm
#print axioms VOA.ZhuCoordinate.Lsq_sqCurrent_comm
#print axioms VOA.ZhuCoordinate.vSqZ_L_neg_one
#print axioms VOA.ZhuCoordinate.vSqZ_neg_one_current
#print axioms VOA.ZhuCoordinate.vSqZ_mem_sqWeightSpace
end AxiomAudit
