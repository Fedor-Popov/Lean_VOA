/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNStatement

/-!
# Genus zero on the abstract interface: the shared interface of the genus-zero theorem

Definitions shared by the FP and LR halves of the genus-zero theorem (blueprint
`Notes/moonshine/MOON_M8_LEAN.md`, section "Split with LR"). Nothing is proved here except
unfoldings.

* `heckeOrbitSum F k m τ = Σ_{ad = m} Σ_{b < d} f_{k a}((a τ + b) / d)`: the replicate Hecke sum of
  order `m` of member `k`, i.e. the right-hand side of `ReplicableFamily.replicable`.
* `PrimeHeckeIdentityAt F k p hp` (the prime Hecke identity): for every `m ≥ 1`,
  `Σ_{j<p} H_m((τ+j)/p) + H_m(pτ) = H_{mp}(τ) + [p ∣ m] · p · H_{m/p}(τ)`;
  `PrimeHeckeIdentity F k` asks it at every prime `p ≡ 1 (mod N)`.
* `IsInjectiveModTranslations f` and `ReplicableFamily.NotInjectiveModTranslations F`
  (nontriviality: no member is injective modulo translations).
* `LargeValuesFromTop f`: every large value is taken high up.
* `symmetryGroup f = {γ ∈ GL(2,ℝ) | det γ = 1, f ∘ γ = f}`, with `HasDetOne`.
-/

namespace VOA.Moonshine.ConwayNorton

open UpperHalfPlane
open scoped MatrixGroups

/-- The replicate Hecke sum `H_m(τ) = Σ_{ad = m} Σ_{b < d} f_{k a}((a τ + b) / d)` of member `k`
of a replicable family: the right-hand side of the replication formula of order `m`
(`ReplicableFamily.replicable`). It is `0` for `m = 0`. -/
noncomputable def heckeOrbitSum {N : ℕ} (F : ReplicableFamily N) (k m : ℕ) (τ : ℍ) : ℂ :=
  ∑ a ∈ m.divisors.attach, ∑ b ∈ Finset.range (m / a),
    qSeriesFun (F.c (k * a)) (heckePoint a (m / a) b (Nat.pos_of_mem_divisors a.2)
      (Nat.div_pos (Nat.divisor_le a.2) (Nat.pos_of_mem_divisors a.2)) τ)

/-- The replication formula in terms of `heckeOrbitSum`: some monic polynomial of degree `m`
(the Faber polynomial) evaluated at `f_k` is `H_m`. -/
theorem ReplicableFamily.exists_monic_eval_eq_heckeOrbitSum {N : ℕ} (F : ReplicableFamily N)
    (k m : ℕ) (hm : 0 < m) :
    ∃ P : Polynomial ℂ, P.Monic ∧ P.natDegree = m ∧
      ∀ τ : ℍ, P.eval (qSeriesFun (F.c k) τ) = heckeOrbitSum F k m τ :=
  F.replicable k m hm

/-- **The prime Hecke identity at `p`**: for every `m ≥ 1` and
`τ ∈ ℍ`,
`Σ_{j<p} H_m((τ+j)/p) + H_m(p τ) = H_{m p}(τ) + (if p ∣ m then p · H_{m/p}(τ) else 0)`,
with `H = heckeOrbitSum F k`. It holds for every prime `p ≡ 1 (mod N)`; that theorem is proved
on the LR side. -/
def PrimeHeckeIdentityAt {N : ℕ} (F : ReplicableFamily N) (k p : ℕ) (hp : 0 < p) : Prop :=
  ∀ m : ℕ, 0 < m → ∀ τ : ℍ,
    (∑ j ∈ Finset.range p, heckeOrbitSum F k m (heckePoint 1 p j one_pos hp τ)) +
        heckeOrbitSum F k m (heckePoint p 1 0 hp one_pos τ) =
      heckeOrbitSum F k (m * p) τ +
        if p ∣ m then (p : ℂ) * heckeOrbitSum F k (m / p) τ else 0

/-- The prime Hecke identity at every admissible prime `p ≡ 1 (mod N)`: the form in which it is
consumed by the polynomial Hecke sums, the Hecke pairing and the pairing on connected domains. -/
def PrimeHeckeIdentity {N : ℕ} (F : ReplicableFamily N) (k : ℕ) : Prop :=
  ∀ p : ℕ, ∀ hp : p.Prime, p ≡ 1 [MOD N] → PrimeHeckeIdentityAt F k p hp.pos

/-- `f` is injective on `ℍ / ℤ`: equal values only at points differing by an integer. -/
def IsInjectiveModTranslations (f : ℍ → ℂ) : Prop :=
  ∀ σ τ : ℍ, f σ = f τ → ∃ n : ℤ, (σ : ℂ) = τ + n

/-- **Nontriviality** (proved on the LR side by the tower argument down to `J`): no member of the
family is injective on `ℍ / ℤ`. -/
def ReplicableFamily.NotInjectiveModTranslations {N : ℕ} (F : ReplicableFamily N) : Prop :=
  ∀ k : ℕ, ¬ IsInjectiveModTranslations (qSeriesFun (F.c k))

/-- **Large values come from the top**: there are `R` and `Y > 0` such that every value
`w` with `‖w‖ ≥ R` is taken at some point of height at least `Y`. -/
def LargeValuesFromTop (f : ℍ → ℂ) : Prop :=
  ∃ R Y : ℝ, 0 < Y ∧ ∀ w : ℂ, R ≤ ‖w‖ → ∃ σ : ℍ, Y ≤ σ.im ∧ f σ = w

/-- The symmetry group `{γ ∈ GL(2,ℝ) | det γ = 1 ∧ ∀ τ, f (γ • τ) = f τ}` of `f : ℍ → ℂ`. It
contains `−1`, which acts trivially. -/
def symmetryGroup (f : ℍ → ℂ) : Subgroup (GL (Fin 2) ℝ) where
  carrier := {g | g.det = 1 ∧ ∀ τ : ℍ, f (g • τ) = f τ}
  mul_mem' {a b} ha hb := ⟨by rw [map_mul, ha.1, hb.1, one_mul], fun τ => by
    rw [mul_smul, ha.2, hb.2]⟩
  one_mem' := ⟨map_one _, fun τ => by rw [one_smul]⟩
  inv_mem' {a} ha := ⟨by rw [map_inv, ha.1, inv_one], fun τ => by
    rw [← ha.2 (a⁻¹ • τ), smul_inv_smul]⟩

lemma mem_symmetryGroup {f : ℍ → ℂ} {g : GL (Fin 2) ℝ} :
    g ∈ symmetryGroup f ↔ g.det = 1 ∧ ∀ τ : ℍ, f (g • τ) = f τ :=
  Iff.rfl

instance hasDetOne_symmetryGroup (f : ℍ → ℂ) : (symmetryGroup f).HasDetOne :=
  ⟨fun hg => hg.1⟩

end VOA.Moonshine.ConwayNorton
