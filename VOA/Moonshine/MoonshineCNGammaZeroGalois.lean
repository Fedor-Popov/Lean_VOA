/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGammaZeroBridge

/-!
# Galois invariance of McKay–Thompson series from the `Γ₁` theorem

Blueprint: the `Γ₀` upgrade argument of `Notes/moonshine/MOON_MONSTER.md`. Galois invariance
(function form): for `g` of finite order `N` and `u` coprime to `N`, `T_{g^u} = T_g`. Dirichlet
gives a prime `p > M` with `p ≡ u (mod N)`, so `g^p = g^u`, and `replicate_eq_and_diamond_mem`
gives `T_{g^p} = T_g`.

The passage to `RationalTraces` (equality of `q`-coefficients, then the Ramanujan-sum argument on
the eigenvalues of `g` on `V♮_n`) is not formalised here.
-/

namespace VOA.Moonshine.ConwayNorton

open UpperHalfPlane Filter Topology CongruenceSubgroup Matrix Matrix.SpecialLinearGroup AutMonster
open scoped MatrixGroups Manifold

/-- **Galois invariance** `T_{g^u} = T_g` for `u` coprime to the order of `g`, from the `Γ₁`
theorem and replication of `g` at every prime. -/
theorem mckayThompsonFun_pow_eq_of_coprime (h1 : ConwayNortonGammaOne) {g : AutVnat}
    (hg : IsOfFinOrder g)
    (hrep : ∀ p : ℕ, p.Prime → ∃ P : Polynomial ℂ, ∀ τ : ℍ, P.eval (mckayThompsonFun g τ) =
      ∑ a ∈ p.divisors.attach, ∑ b ∈ Finset.range (p / a),
        mckayThompsonFun (g ^ (a : ℕ)) (heckePoint a (p / a) b (Nat.pos_of_mem_divisors a.2)
          (Nat.div_pos (Nat.divisor_le a.2) (Nat.pos_of_mem_divisors a.2)) τ))
    {u : ℕ} (hu : Nat.Coprime u (orderOf g)) :
    mckayThompsonFun (g ^ u) = mckayThompsonFun g := by
  obtain ⟨Γ, M, hM, hdet, hΓ1, -, hH⟩ := h1 g hg
  haveI : NeZero (orderOf g) := ⟨hg.orderOf_pos.ne'⟩
  have hunit : IsUnit (u : ZMod (orderOf g)) := (ZMod.isUnit_iff_coprime u _).mpr hu
  obtain ⟨p, hMp, hp, hpu⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunit M
  have hcop : Nat.Coprime p M :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr (Nat.not_dvd_of_pos_of_lt hM hMp)
  obtain ⟨m, n, hmn⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have hmn' : m * p - (-n) * M = 1 := by linear_combination hmn
  obtain ⟨Γ', M', -, -, -, -, hH'⟩ := h1 (g ^ p) hg.pow
  obtain ⟨Φ, hΦ⟩ := replicatesAtPrime_of_replication hp (hrep p hp)
  have hgp : g ^ p = g ^ u :=
    pow_eq_pow_iff_modEq.mpr ((ZMod.natCast_eq_natCast_iff _ _ _).mp hpu)
  rw [← hgp]
  exact (replicate_eq_and_diamond_mem hH hdet hΓ1 hM hp hMp hmn' hH'.holomorphic
    (mckayThompsonFun_periodic _) hH'.normalized hΦ).1

/-- `T_{g^u} = T_g` for `u` coprime to the order of `g`, from the `Γ₁` theorem and complete
replicability, given that every automorphism has finite order. -/
theorem mckayThompsonFun_pow_eq_of_coprime_of_completelyReplicable
    (hfin : ∀ g : AutVnat, IsOfFinOrder g) (h1 : ConwayNortonGammaOne)
    (hrep : CompletelyReplicable) (g : AutVnat) {u : ℕ} (hu : Nat.Coprime u (orderOf g)) :
    mckayThompsonFun (g ^ u) = mckayThompsonFun g :=
  mckayThompsonFun_pow_eq_of_coprime h1 (hfin g) (fun p hp => by
    obtain ⟨P, -, -, hP⟩ := hrep g p hp.pos
    exact ⟨P, hP⟩) hu

end VOA.Moonshine.ConwayNorton
