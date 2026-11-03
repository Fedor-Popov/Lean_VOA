/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.Twisted

/-!
# The all-indices twisted Jacobi identity is degenerate for `N ≥ 2`  (Moonshine step M6a)

**Remark.**  The twisted Jacobi identity (field `TwistedModule.jacobi` of `Modularity/Twisted.lean`)
cannot be stated for `u ∈ 𝒱ʲ` and **every** fractional index `k : ℤ`, including those with
`k ≢ −j (mod N)`, where `u₍k/N₎ = 0` by the support condition.  For such `k` the left side vanishes identically while the
right side need not: the Dong–Li–Mason mode identity is the coefficient of
`z₁^{−k/N−1} z₂^{−m/N−1}` of the generating identity, and that extraction is only meaningful on the
support coset.

**Certificate.**  Take `u = v = 𝟙 ∈ 𝒱⁰`, `ℓ = −1`, `k = 1`, `m = −N−1`.  Every left summand contains
a vacuum mode `𝟙₍r/N₎` with `r ≢ 0 (mod N)`, hence is `0`; the right side is
`C(1/N,0)·Y_M(𝟙₍₋₁₎𝟙)₍₋₁₎ x = x`.  So `x = 0` for every `x ∈ M`
(`jacobiAllIndices_eq_zero`): under that form no nonzero `M` carries a `TwistedModule g N M`
with `N ≥ 2`, the Moonshine target `TwistedModule θ 2 (FockT r)` included.

## The restricted identity

The DLM identity holds exactly on the support coset `k ≡ −j (mod N)` (`TwistedJacobi` below).  The
restriction loses nothing: for `k` off the coset both sides vanish whenever `v` decomposes into
`g`-eigenvectors (left side by `support`; right side by `support` applied to `u₍ₙ₎v ∈ 𝒱^{j+j'}`
when `m ≡ −j'`, and by `support` of `v` when `m ≢ −j'` — the latter is precisely where the
unrestricted form fails, since then `k + m` lands back on the support coset of `u₍ₙ₎v`).  The
field `TwistedModule.jacobi` of `Modularity/Twisted.lean` therefore carries the hypothesis
`(k + j) % (N : ℤ) = 0`; `OrdVModule.toTwisted` (`N = 1`) is unaffected.
The same over-quantification occurs in `Modules/SuperTwistedModule.lean`
(`SuperTwistedModule.jacobi`, same certificate with the even vacuum).

This file keeps the certificate (against the predicate `JacobiAllIndices`) as a recorded dead
end, and `TwistedJacobi`, which coincides with the field (`twistedJacobi_of_twistedModule`).
⚠ `SuperTwistedModule.jacobi` still has the over-quantified form.

## Status
`JacobiAllIndices`, `jacobiAllIndices_eq_zero`, `TwistedJacobi`,
`twistedJacobi_of_twistedModule` are `sorry`-free; `#print axioms` gives
`[propext, Classical.choice, Quot.sound]`.
-/

namespace VOA

open Module (End)

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- The vacuum lies in the `j = 0` eigenspace of every automorphism. -/
theorem Aut.vacuum_mem_twistedEigenspace_zero (g : Aut W) (N : ℕ) :
    W.vacuum ∈ g.twistedEigenspace N 0 := by
  rw [Aut.twistedEigenspace, Module.End.mem_eigenspace_iff]
  simp only [CharP.cast_eq_zero, mul_zero, neg_zero, zero_div, Complex.exp_zero, one_smul]
  exact g.map_vacuum

/-- `C(x, 0) = 1`. -/
@[simp] theorem cbinom_zero (x : ℂ) : cbinom x 0 = 1 := by simp [cbinom]

/-- An integer that is `1` modulo `N ≥ 2` is not `0` modulo `N`: the arithmetic behind the
certificate. -/
private theorem ne_neg_of_two_le {N : ℕ} (hN : 2 ≤ N) (i : ℤ) :
    (-1) * (N : ℤ) + 1 - i * N ≠ -(N : ℤ) ∧ 1 + i * (N : ℤ) ≠ -(N : ℤ) := by
  have hdvd : ∀ c : ℤ, c * (N : ℤ) = 1 ∨ c * (N : ℤ) = -1 → False := by
    intro c hc
    have h1 : (N : ℤ) ∣ 1 := by
      rcases hc with hc | hc
      · exact ⟨c, by rw [← hc]; ring⟩
      · exact ⟨-c, by linear_combination hc⟩
    have := Int.le_of_dvd one_pos h1
    omega
  refine ⟨fun h => hdvd i (Or.inl (by linear_combination -h)), fun h =>
    hdvd (i + 1) (Or.inr (by linear_combination h))⟩

/-- The twisted Jacobi identity **quantified over every fractional index `k`**, i.e. the
over-quantified form of `TwistedModule.jacobi`.  Kept only as the subject of the certificate
`jacobiAllIndices_eq_zero`. -/
def JacobiAllIndices (g : Aut W) (N : ℕ) {M : Type*} [AddCommGroup M] [Module ℂ M]
    (YM : 𝒱 →ₗ[ℂ] (ℤ → End ℂ M)) : Prop :=
  ∀ (j : ℕ) (u : 𝒱), u ∈ g.twistedEigenspace N j → ∀ (v : 𝒱) (x : M) (ℓ k m : ℤ),
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (YM u (ℓ * N + k - i * N) (YM v (m + i * N) x)
          - negOnePow ℓ • YM v (ℓ * N + m - i * N) (YM u (k + i * N) x)))
      = ∑ᶠ i : ℕ, cbinom ((k : ℂ) / N) i • YM (W.smul u (ℓ + i) v) (k + m - i * N) x

/-- **Dead-end certificate.**  For `N ≥ 2`, a fractional-mode map with the twisted vacuum
property satisfying the all-indices Jacobi identity is zero on every vector: at `u = v = 𝟙`,
`ℓ = −1`, `k = 1`, `m = −N−1` the identity reads `0 = x`. -/
theorem jacobiAllIndices_eq_zero {g : Aut W} {N : ℕ} (hN : 2 ≤ N) {M : Type*}
    [AddCommGroup M] [Module ℂ M] (YM : 𝒱 →ₗ[ℂ] (ℤ → End ℂ M))
    (hvac : ∀ k : ℤ, YM W.vacuum k = if k = -(N : ℤ) then 1 else 0)
    (hJ : JacobiAllIndices g N YM) (x : M) : x = 0 := by
  have h := hJ 0 W.vacuum (g.vacuum_mem_twistedEigenspace_zero N) W.vacuum x (-1) 1
    (-(N : ℤ) - 1)
  have hL : (∑ᶠ i : ℤ, (negOnePow i * cbz (-1) i) •
      (YM W.vacuum ((-1) * N + 1 - i * N) (YM W.vacuum ((-(N : ℤ) - 1) + i * N) x)
        - negOnePow (-1) • YM W.vacuum ((-1) * N + (-(N : ℤ) - 1) - i * N)
            (YM W.vacuum (1 + i * N) x))) = 0 := by
    refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
    obtain ⟨h1, h2⟩ := ne_neg_of_two_le hN i
    simp only [hvac, if_neg h1, if_neg h2]
    simp
  have hR : (∑ᶠ i : ℕ, cbinom ((1 : ℤ) / (N : ℂ)) i •
      YM (W.smul W.vacuum (-1 + i) W.vacuum) (1 + (-(N : ℤ) - 1) - i * N) x) = x := by
    rw [finsum_eq_single _ 0 (fun i hi => by
      rw [PreVertexAlgebra.smul_vacuum_left, if_neg (by omega), map_zero]
      simp)]
    rw [PreVertexAlgebra.smul_vacuum_left, if_pos (by simp), cbinom_zero, one_smul, hvac,
      if_pos (by push_cast; ring)]
    rfl
  rw [hL, hR] at h
  exact h.symm

/-- **The corrected twisted Jacobi identity** (Dong–Li–Mason, mode form) for a fractional-mode map
`YM u k = u₍k/N₎`: identical to `TwistedModule.jacobi` except that the fractional index of `u ∈ 𝒱ʲ`
is restricted to its support coset `k ≡ −j (mod N)`. -/
def TwistedJacobi (g : Aut W) (N : ℕ) {M : Type*} [AddCommGroup M] [Module ℂ M]
    (YM : 𝒱 →ₗ[ℂ] (ℤ → End ℂ M)) : Prop :=
  ∀ (j : ℕ) (u : 𝒱), u ∈ g.twistedEigenspace N j → ∀ (v : 𝒱) (x : M) (ℓ k m : ℤ),
    (k + j) % (N : ℤ) = 0 →
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (YM u (ℓ * N + k - i * N) (YM v (m + i * N) x)
          - negOnePow ℓ • YM v (ℓ * N + m - i * N) (YM u (k + i * N) x)))
      = ∑ᶠ i : ℕ, cbinom ((k : ℂ) / N) i • YM (W.smul u (ℓ + i) v) (k + m - i * N) x

/-- `TwistedJacobi` is exactly the (repaired) Jacobi field of `TwistedModule`. -/
theorem twistedJacobi_of_twistedModule {g : Aut W} {N : ℕ} {M : Type u} [AddCommGroup M]
    [Module ℂ M] (T : TwistedModule g N M) : TwistedJacobi g N T.YM :=
  fun j u hu v x ℓ k m hk => T.jacobi j u hu v x ℓ k m hk

end VOA
