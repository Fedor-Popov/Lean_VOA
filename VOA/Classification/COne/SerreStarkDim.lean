/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkSturm
import VOA.Classification.COne.SerreStarkEasy

/-!
# Serre–Stark, stage S2-3b: the residual as a dimension bound (levels `24 ∣ N`)

The classification calls `ISerreStark` only at levels `N` with `24 ∣ N`
(`ModularData.exists_level`). For such `N`:

* `thetaSpan N`: the span (in functions on `ℍ`) of the `θ_{n₀,r,t}`, `0 ≤ n₀ < r`, `r, t ≥ 1`,
  `4 t r² ∣ N`; `thetaSpan_le`: it lies in `thetaTypeSpace N` (stage S2-3);
* `thetaTypeSpace` is finite-dimensional (stage S2-2);
* hence `ISerreStark24` (`ISerreStark` restricted to `24 ∣ N`) follows from the single numerical
  statement `SerreStarkDimBound24`: `dim M_{1/2}(Γ₁(N), θ) ≤ dim thetaSpan N`
  (`iSerreStark24_of_dimBound`).

`SerreStarkDimBound24` is TRUE: it is the dimension count of Serre–Stark Theorem A (with the
basis `θ_{ψ,t}`, `(ψ, t) ∈ Ω(N)`, each a combination of the `θ_{n₀,r,t}`); and conversely it is
implied by `SerreStarkTheoremA` (`dimBound24_of_theoremA`). So it is *equivalent* in strength to
the needed case of Theorem A — a reformulation, not a weakening: what remains is exactly the
upper bound on the dimension.
-/

open Complex
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace VOA.Classification.COne

/-- The index set `{(n₀, r, t) : 0 ≤ n₀ < r, 1 ≤ r, 1 ≤ t, 4 t r² ∣ N}`. -/
def thetaIndex (N : ℕ) : Finset (ℤ × ℕ × ℕ) :=
  ((Finset.range (N + 1) ×ˢ Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
    fun p : ℕ × ℕ × ℕ => p.1 < p.2.1 ∧ 1 ≤ p.2.1 ∧ 1 ≤ p.2.2 ∧ 4 * p.2.2 * p.2.1 ^ 2 ∣ N).image
    fun p => ((p.1 : ℤ), p.2.1, p.2.2)

theorem mem_thetaIndex_iff {N : ℕ} (hN : 0 < N) {p : ℤ × ℕ × ℕ} :
    p ∈ thetaIndex N ↔
      0 ≤ p.1 ∧ p.1 < p.2.1 ∧ 1 ≤ p.2.1 ∧ 1 ≤ p.2.2 ∧ 4 * p.2.2 * p.2.1 ^ 2 ∣ N := by
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨-, h1, h2, h3, h4⟩ := Finset.mem_filter.1 hq
    refine ⟨by positivity, ?_, h2, h3, h4⟩
    change ((q.1 : ℕ) : ℤ) < ((q.2.1 : ℕ) : ℤ)
    exact_mod_cast h1
  · rintro ⟨h0, h1, h2, h3, h4⟩
    have hle : 4 * p.2.2 * p.2.1 ^ 2 ≤ N := Nat.le_of_dvd hN h4
    have hsq : p.2.1 ≤ p.2.1 ^ 2 := Nat.le_self_pow two_ne_zero _
    have hsq1 : 1 ≤ p.2.1 ^ 2 := Nat.one_le_pow _ _ h2
    have hr : p.2.1 ≤ N := by
      calc p.2.1 ≤ p.2.1 ^ 2 := hsq
        _ ≤ (4 * p.2.2) * p.2.1 ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
        _ ≤ N := hle
    have ht : p.2.2 ≤ N := by
      calc p.2.2 ≤ 4 * p.2.2 := by omega
        _ ≤ (4 * p.2.2) * p.2.1 ^ 2 := Nat.le_mul_of_pos_right _ hsq1
        _ ≤ N := hle
    have h1' : p.1.toNat < p.2.1 := by omega
    refine Finset.mem_image.2 ⟨(p.1.toNat, p.2.1, p.2.2), Finset.mem_filter.2 ⟨?_, ?_⟩, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_range]
      exact ⟨by omega, by omega, by omega⟩
    · exact ⟨by omega, h2, h3, h4⟩
    · simp [Int.toNat_of_nonneg h0]

/-- The theta series of the index triple `p`, restricted to `ℍ`. -/
def thetaFn (p : ℤ × ℕ × ℕ) : ℍ → ℂ := restrictUpper (rankOneTheta p.1 p.2.1 p.2.2)

/-- The span of the `θ_{n₀,r,t}` of level `N`. -/
def thetaSpan (N : ℕ) : Submodule ℂ (ℍ → ℂ) :=
  Submodule.span ℂ (Set.range fun p : thetaIndex N => thetaFn p)

/-- **Easy half.** For `24 ∣ N`, the theta series lie in `M_{1/2}(Γ₁(N), θ)`. -/
theorem thetaSpan_le {N : ℕ} (hN : 0 < N) (h24 : 24 ∣ N) : thetaSpan N ≤ thetaTypeSpace N := by
  rw [thetaSpan, Submodule.span_le]
  rintro _ ⟨⟨p, hp⟩, rfl⟩
  obtain ⟨-, -, hr, ht, hdiv⟩ := (mem_thetaIndex_iff hN).1 hp
  exact ⟨_, isThetaTypeForm_rankOneTheta h24 p.1 hr ht hdiv, rfl⟩

/-- **The dimension residual** (levels `24 ∣ N`): `dim M_{1/2}(Γ₁(N), θ) ≤ dim span{θ_{n₀,r,t}}`.
TRUE by Serre–Stark Theorem A; equivalent to it at these levels given `thetaSpan_le`. -/
def SerreStarkDimBound24 : Prop :=
  ∀ N : ℕ, 0 < N → 24 ∣ N →
    Module.finrank ℂ (thetaTypeSpace N) ≤ Module.finrank ℂ (thetaSpan N)

theorem thetaTypeSpace_eq_thetaSpan (hD : SerreStarkDimBound24) {N : ℕ} (hN : 0 < N)
    (h24 : 24 ∣ N) : thetaSpan N = thetaTypeSpace N := by
  haveI : NeZero N := ⟨hN.ne'⟩
  have h4 : 4 ∣ N := (show 4 ∣ 24 by norm_num).trans h24
  haveI := finiteDimensional_thetaTypeSpace h4
  exact Submodule.eq_of_le_of_finrank_le (thetaSpan_le hN h24) (hD N hN h24)

/-- **Reduction.** The dimension bound gives `ISerreStark` at every level divisible by `24`. -/
theorem iSerreStark24_of_dimBound (hD : SerreStarkDimBound24) : ISerreStark24 := by
  classical
  intro N f hN h24 hf
  have hmem : restrictUpper f ∈ thetaSpan N := by
    rw [thetaTypeSpace_eq_thetaSpan hD hN h24]
    exact ⟨f, hf, rfl⟩
  rw [thetaSpan, Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  refine ⟨thetaIndex N, fun p => if h : p ∈ thetaIndex N then c ⟨p, h⟩ else 0, ?_, ?_⟩
  · intro p hp
    obtain ⟨-, -, hr, ht, hdiv⟩ := (mem_thetaIndex_iff hN).1 hp
    exact ⟨hr, ht, hdiv⟩
  · intro τ hτ
    have h := congrFun hc ⟨τ, hτ⟩
    rw [restrictUpper_apply] at h
    rw [← h, Finset.sum_apply, ← Finset.sum_coe_sort (thetaIndex N)]
    refine Finset.sum_congr rfl fun p _ => ?_
    change c p * thetaFn p ⟨τ, hτ⟩ =
      (if h : (p : ℤ × ℕ × ℕ) ∈ thetaIndex N then c ⟨p, h⟩ else 0) * _
    rw [dif_pos p.2]
    rfl

/-- Under Serre–Stark's Theorem A, every θ-type form of level `N` lies in `thetaSpan N`. -/
theorem thetaTypeSpace_le_thetaSpan_of_theoremA (hA : SerreStarkTheoremA) {N : ℕ} (hN : 0 < N)
    (h4 : 4 ∣ N) : thetaTypeSpace N ≤ thetaSpan N := by
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨m, r, t, ψ, c, hcond, hfe⟩ := hA N f hN h4 hf
  have hr : ∀ i, 0 < r i := fun i => by
    rcases Nat.eq_zero_or_pos (r i) with h | h
    · have := (hcond i).2.2.2
      rw [h] at this
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        zero_dvd_iff] at this
      omega
    · exact h
  have hmemj : ∀ i, ∀ j ∈ Finset.range (r i), thetaFn ((j : ℤ), r i, t i) ∈ thetaSpan N := by
    intro i j hj
    have hp : ((j : ℤ), r i, t i) ∈ thetaIndex N := by
      rw [mem_thetaIndex_iff hN]
      exact ⟨by positivity, by simpa using Finset.mem_range.1 hj, hr i, (hcond i).2.2.1,
        (hcond i).2.2.2⟩
    exact Submodule.subset_span ⟨⟨_, hp⟩, rfl⟩
  have heq : restrictUpper f = ∑ i, c i • ∑ j ∈ Finset.range (r i),
      ψ i (j : ZMod (r i)) • thetaFn ((j : ℤ), r i, t i) := by
    funext τ
    rw [restrictUpper_apply, hfe τ τ.2, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have ht : (0 : ℝ) < t i := by exact_mod_cast (hcond i).2.2.1
    rw [charTheta_eq_sum (r i) (hr i) (ψ i) ht τ.2, Pi.smul_apply, Finset.sum_apply,
      smul_eq_mul]
    congr 1
  rw [heq]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ <|
    Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (hmemj i j hj)

/-- `SerreStarkTheoremA` implies the dimension residual: the residual is no stronger than the
published theorem. -/
theorem dimBound24_of_theoremA (hA : SerreStarkTheoremA) : SerreStarkDimBound24 := by
  intro N hN h24
  have h4 : 4 ∣ N := (show 4 ∣ 24 by norm_num).trans h24
  haveI : Module.Finite ℂ (thetaSpan N) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  exact LinearMap.finrank_le_finrank_of_injective
    (f := Submodule.inclusion (thetaTypeSpace_le_thetaSpan_of_theoremA hA hN h4))
    (Submodule.inclusion_injective _)

end VOA.Classification.COne
