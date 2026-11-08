/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGammaZeroBridge

/-!
# The `Γ₁ ⇒ Γ₀` upgrade on the abstract `ReplicableFamily` interface

Blueprint: the `Γ₀` upgrade argument of `Notes/moonshine/MOON_MONSTER.md`. The
replicate-equals-Hauptmodul theorem and the `Γ₀` corollary hold verbatim for member `k` of a
`ReplicableFamily`, with replicate `qSeriesFun (c (k * p))`. As an output,
`qSeriesFun (c (k * p)) = qSeriesFun (c k)` for every prime `p > M`.
-/

namespace VOA.Moonshine.ConwayNorton

open UpperHalfPlane Filter Topology CongruenceSubgroup Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups Manifold

/-- `q`-series are `1`-periodic. -/
lemma qSeriesFun_periodic (c : ℕ → ℂ) (τ : ℍ) :
    qSeriesFun c (glUpperUnipotent 1 • τ) = qSeriesFun c τ := by
  simp only [qSeriesFun, qPar_glUpperUnipotent_one]

namespace ReplicableFamily

variable {N : ℕ} (F : ReplicableFamily N)

/-- The replication formula of member `k` at a prime `p`, in two-block form. -/
lemma replicatesAtPrime (k : ℕ) {p : ℕ} (hp : p.Prime) :
    ReplicatesAtPrime (qSeriesFun (F.c k)) (qSeriesFun (F.c (k * p))) p hp := by
  obtain ⟨P, -, -, hP⟩ := F.replicable k p hp.pos
  refine ⟨fun x => P.eval x, fun τ => ?_⟩
  have := (hP τ).trans (heckeSum_prime (fun a => qSeriesFun (F.c (k * a))) hp τ)
  simpa only [mul_one] using this

/-- **`Γ₀` for a replicable family.** If member `k` is the normalised Hauptmodul of
`Γ ⊇ Γ₁(M)` (`Γ ≤ SL₂(ℝ)`, commensurable with `SL₂(ℤ)`) and each replicate
`qSeriesFun (c (k * p))`, `p > M` prime, is holomorphic and normalised, then `±Γ` is a moonshine
group of level `M` for member `k`. -/
theorem isMoonshineGroup_of_gammaOne (k : ℕ) {Γ : Subgroup (GL (Fin 2) ℝ)} {M : ℕ}
    (hM : 0 < M) (hdet : Γ.HasDetOne) (hΓ1 : gamma1GL M ≤ Γ)
    (hcomm : Subgroup.Commensurable Γ 𝒮ℒ) (hH : IsNormalizedHauptmodul Γ (qSeriesFun (F.c k)))
    (hhol : ∀ p : ℕ, p.Prime → M < p → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (qSeriesFun (F.c (k * p))))
    (hnorm : ∀ p : ℕ, p.Prime → M < p →
      Tendsto (fun τ : ℍ => qSeriesFun (F.c (k * p)) τ - (qPar τ)⁻¹) atImInfty (𝓝 0)) :
    IsMoonshineGroup Γ.adjoinNegOne M ∧
      IsNormalizedHauptmodul Γ.adjoinNegOne (qSeriesFun (F.c k)) :=
  isMoonshineGroup_adjoinNegOne_of_replicable hH hdet hΓ1 hM hcomm fun p hp hMp =>
    ⟨qSeriesFun (F.c (k * p)), hhol p hp hMp, qSeriesFun_periodic _, hnorm p hp hMp,
      F.replicatesAtPrime k hp⟩

/-- **Replicates at large primes are trivial**: in the setting of `isMoonshineGroup_of_gammaOne`,
`qSeriesFun (c (k * p)) = qSeriesFun (c k)` for every prime `p > M`. -/
theorem qSeriesFun_mul_prime_eq (k : ℕ) {Γ : Subgroup (GL (Fin 2) ℝ)} {M : ℕ}
    (hM : 0 < M) (hdet : Γ.HasDetOne) (hΓ1 : gamma1GL M ≤ Γ)
    (hH : IsNormalizedHauptmodul Γ (qSeriesFun (F.c k))) {p : ℕ} (hp : p.Prime) (hMp : M < p)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (qSeriesFun (F.c (k * p))))
    (hnorm : Tendsto (fun τ : ℍ => qSeriesFun (F.c (k * p)) τ - (qPar τ)⁻¹) atImInfty (𝓝 0)) :
    qSeriesFun (F.c (k * p)) = qSeriesFun (F.c k) := by
  have hcop : Nat.Coprime p M :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr (Nat.not_dvd_of_pos_of_lt hM hMp)
  obtain ⟨m, n, hmn⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have hmn' : m * p - (-n) * M = 1 := by linear_combination hmn
  obtain ⟨Φ, hΦ⟩ := F.replicatesAtPrime k hp
  exact (replicate_eq_and_diamond_mem hH hdet hΓ1 hM hp hMp hmn' hhol (qSeriesFun_periodic _)
    hnorm hΦ).1

end ReplicableFamily

end VOA.Moonshine.ConwayNorton
