/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.PlusWeightOne
import VOA.Examples.HeisenbergNVOA
import VOA.Moonshine.HeisenbergTwistedModuleDefect
import VOA.Moonshine.TwistedHeisenberg

/-!
# The involution `σ` of the rank-`r` Heisenberg VOA and its eigenspaces  (Moonshine step M6a)

The Fock involution `σ = LatGen.sigmaN r` (negating every oscillator variable) is an automorphism
of the rank-`r` Heisenberg VOA `heisenbergNVOA r k hk` at every level `k ≠ 0`
(`HeisenbergN.sigmaHeisAut`).  The proof is the Heisenberg shadow of `LatGen.thetaAut`: `σ`
anticommutes with every oscillator, hence `σ Y(h(-i-1)𝟙, z) σ = −Y(h(-i-1)𝟙, z)`, and by the
`Intertw.nprod` calculus `σ Y_word(l) σ = (−1)^{|l|} Y_word(l)`, matching
`σ(wordState l) = (−1)^{|l|} wordState l`.

The `N = 2` eigenspaces of `Aut.twistedEigenspace` are identified with the `±1`-eigenspaces of
`σ` (`mem_twistedEigenspace_two_iff`): `𝒱ʲ = {v | σ v = (−1)ʲ v}`.  In particular the weight-one
generators `h_a(−1)𝟙 = X_{(0,a)}` lie in `𝒱¹` (`X_mem_twistedEigenspace_one`), the vacuum and `ω`
in `𝒱⁰`, and every monomial of degree `d` in `𝒱^d`.

## Level
The twisted Fock space `FockT r` of `Moonshine/TwistedHeisenberg.lean` has
`[h_i(k/2), h_j(l/2)] = (k/2) δ_{ij} δ_{k+l,0}`, matching `oscN r 1` (`[aᵃₘ, aᵇₙ] = m δ^{ab}
δ_{m+n,0}`), so the Moonshine target is the level `k = 1` VOA `heisVOA1 r`.  (With the twisted
Jacobi identity quantified over all fractional indices this target would be provably empty; see
`Moonshine/HeisenbergTwistedModuleDefect.lean`.)

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
-/

namespace VOA

namespace HeisenbergN

open MvPolynomial LatGen
open Module (End)

variable (r : ℕ)

/-- `σ` acts on a word state by the sign `(−1)^{|l|}` (the rank-`r` version of
`LatGen.sigmaN_wordStateN`). -/
theorem sigmaN_wordStateN' (l : List (ℕ × Fin r)) :
    sigmaN r (wordStateN l) = ((-1 : ℂ) ^ l.length) • wordStateN l := by
  induction l with
  | nil => rw [wordStateN_nil, sigmaN_one, List.length_nil, pow_zero, one_smul]
  | cons ia rest ih =>
      rw [wordStateN_cons, sigmaN_mul, sigmaN_X, ih, List.length_cons, pow_succ',
        mul_smul, mul_smul_comm, neg_mul, neg_one_smul, smul_neg]

/-- `σ` anticommutes with each basic current. -/
theorem sigmaN_currentN (k : ℂ) (a : Fin r) :
    Intertw (sigmaN r).toLinearMap (-1) (currentN r k a) (currentN r k a) := by
  intro t x
  change sigmaN r (oscN r k a (-t - 1) x) = _
  rw [sigmaN_oscN, neg_one_smul]
  rfl

/-- `σ` anticommutes with each generator field `Y(h_a(-i-1)𝟙, z)`. -/
theorem sigmaN_genFieldN (k : ℂ) (a : Fin r) (i : ℕ) :
    Intertw (sigmaN r).toLinearMap (-1) (genFieldN r k a i) (genFieldN r k a i) :=
  ((sigmaN_currentN r k a).deriv_iterate i).const_smul _

/-- `σ` commutes with the identity field. -/
theorem sigmaN_idFieldN :
    Intertw (sigmaN r).toLinearMap 1 (idFieldN r) (idFieldN r) := by
  intro t x
  rw [idFieldN_apply, one_smul]
  split_ifs
  · rfl
  · simp

/-- `σ Y_word(l) σ⁻¹ = (−1)^{|l|} Y_word(l)`. -/
theorem sigmaN_YwordN (k : ℂ) (l : List (ℕ × Fin r)) :
    Intertw (sigmaN r).toLinearMap ((-1 : ℂ) ^ l.length) (YwordN r k l) (YwordN r k l) := by
  induction l with
  | nil => rw [List.length_nil, pow_zero, YwordN_nil]; exact sigmaN_idFieldN r
  | cons ia rest ih =>
      rw [YwordN_cons, List.length_cons, pow_succ']
      exact Intertw.nprod _ _ _ _ (sigmaN_genFieldN r k ia.2 ia.1) ih

/-- **`σ` intertwines the Heisenberg vertex operators**: `σ(Y(u,z)x) = Y(σu,z)(σx)`. -/
theorem sigmaN_YN (k : ℂ) (u : FockN r) (t : ℤ) (x : FockN r) :
    sigmaN r (YN r k u t x) = YN r k (sigmaN r u) t (sigmaN r x) := by
  induction u using MvPolynomial.induction_on' generalizing x with
  | monomial d c =>
      have hmono : (monomial d c : FockN r) = c • monomial d 1 := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      have hσ : sigmaN r (monomial d 1) = ((-1 : ℂ) ^ (monoWordN d).length) • monomial d 1 := by
        rw [← wordStateN_monoWordN, sigmaN_wordStateN']
      rw [hmono, map_smul, map_smul, hσ]
      simp only [map_smul, YN_monomial_one]
      have h : sigmaN r (YmonN r k d t x)
          = ((-1 : ℂ) ^ (monoWordN d).length) • YmonN r k d t (sigmaN r x) :=
        sigmaN_YwordN r k (monoWordN d) t x
      change sigmaN r (c • (YmonN r k d t x))
        = c • (((-1 : ℂ) ^ (monoWordN d).length) • YmonN r k d t (sigmaN r x))
      rw [map_smul, h]
  | add p q hp hq =>
      simp only [map_add]
      change sigmaN r (YN r k p t x + YN r k q t x) =
        YN r k (sigmaN r p) t (sigmaN r x) + YN r k (sigmaN r q) t (sigmaN r x)
      rw [map_add, hp, hq]

/-- The conformal vector is `σ`-invariant. -/
theorem sigmaN_ωN (k : ℂ) : sigmaN r (ωN r k) = ωN r k := by
  rw [ωN, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ωNa, map_smul, sigmaN_oscN, sigmaN_oscN, map_neg, neg_neg, vacuumN, sigmaN_one]

/-- **The Fock involution `σ` is an automorphism of the rank-`r` Heisenberg VOA.** -/
noncomputable def sigmaHeisAut (k : ℂ) (hk : k ≠ 0) : Aut (heisenbergNVOA r k hk) where
  toLinearEquiv := sigmaN r
  map_smul' u n v := by
    change sigmaN r (mode (YN r k u) n v) = mode (YN r k (sigmaN r u)) n (sigmaN r v)
    rw [mode_apply, mode_apply]
    exact sigmaN_YN r k u _ v
  map_vacuum := sigmaN_one r
  map_omega := sigmaN_ωN r k

@[simp] theorem sigmaHeisAut_apply (k : ℂ) (hk : k ≠ 0) (v : FockN r) :
    sigmaHeisAut r k hk v = sigmaN r v := rfl

/-- `σ² = 1`. -/
theorem sigmaHeisAut_sq (k : ℂ) (hk : k ≠ 0) : sigmaHeisAut r k hk * sigmaHeisAut r k hk = 1 :=
  Aut.ext (LinearEquiv.ext fun x => sigmaN_sigmaN r x)

/-- The level-one rank-`r` Heisenberg VOA, whose normalization matches `FockT r`. -/
noncomputable abbrev heisVOA1 : VertexOperatorAlgebra (FockN r) :=
  heisenbergNVOA r 1 one_ne_zero

/-- The involution `σ` of `heisVOA1 r`. -/
noncomputable abbrev sigma1 : Aut (heisVOA1 r) := sigmaHeisAut r 1 one_ne_zero

/-! ## The `N = 2` eigenspaces -/

/-- The `N = 2` eigenvalue `exp(−2πi j/2) = (−1)ʲ`. -/
theorem exp_twisted_two (j : ℕ) :
    Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * j) / (2 : ℕ)) = (-1 : ℂ) ^ j := by
  rw [show -(2 * (Real.pi : ℂ) * Complex.I * j) / (2 : ℕ) = (j : ℂ) * (-(Real.pi * Complex.I)) by
    push_cast; ring, Complex.exp_nat_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

/-- **`𝒱ʲ = {v | σ v = (−1)ʲ v}`** for the `N = 2` twisted eigenspaces of `σ`. -/
theorem mem_twistedEigenspace_two_iff (k : ℂ) (hk : k ≠ 0) (j : ℕ) (v : FockN r) :
    v ∈ (sigmaHeisAut r k hk).twistedEigenspace 2 j ↔ sigmaN r v = ((-1 : ℂ) ^ j) • v := by
  rw [Aut.twistedEigenspace, Module.End.mem_eigenspace_iff, exp_twisted_two]
  rfl

/-- A monomial of degree `d` lies in `𝒱^d`. -/
theorem monomial_mem_twistedEigenspace (k : ℂ) (hk : k ≠ 0) (m : (ℕ × Fin r) →₀ ℕ) (c : ℂ) :
    (monomial m c : FockN r) ∈ (sigmaHeisAut r k hk).twistedEigenspace 2 m.degree := by
  rw [mem_twistedEigenspace_two_iff]
  rw [show (monomial m c : FockN r) = c • monomial m 1 by rw [smul_monomial, smul_eq_mul, mul_one],
    map_smul, sigmaN_monomial, smul_comm]

/-- **The weight-one generators `h_a(−1)𝟙 = X_{(0,a)}` lie in the `(−1)`-eigenspace `𝒱¹`.** -/
theorem X_mem_twistedEigenspace_one (k : ℂ) (hk : k ≠ 0) (v : ℕ × Fin r) :
    (X v : FockN r) ∈ (sigmaHeisAut r k hk).twistedEigenspace 2 1 := by
  rw [mem_twistedEigenspace_two_iff, sigmaN_X, pow_one, neg_one_smul]

/-- The vacuum lies in `𝒱⁰`. -/
theorem vacuumN_mem_twistedEigenspace_zero (k : ℂ) (hk : k ≠ 0) :
    vacuumN r ∈ (sigmaHeisAut r k hk).twistedEigenspace 2 0 :=
  (sigmaHeisAut r k hk).vacuum_mem_twistedEigenspace_zero 2

/-- Every state splits into its `σ`-even and `σ`-odd parts, `v = v⁺ + v⁻` with `v^± ∈ 𝒱^{0,1}`. -/
theorem exists_twistedEigen_decomp (k : ℂ) (hk : k ≠ 0) (v : FockN r) :
    ∃ v₀ ∈ (sigmaHeisAut r k hk).twistedEigenspace 2 0,
      ∃ v₁ ∈ (sigmaHeisAut r k hk).twistedEigenspace 2 1, v = v₀ + v₁ := by
  refine ⟨(1 / 2 : ℂ) • (v + sigmaN r v), ?_, (1 / 2 : ℂ) • (v - sigmaN r v), ?_, ?_⟩
  · rw [mem_twistedEigenspace_two_iff, pow_zero, one_smul, map_smul, map_add, sigmaN_sigmaN,
      add_comm]
  · rw [mem_twistedEigenspace_two_iff, pow_one, map_smul, map_sub, sigmaN_sigmaN, neg_one_smul,
      ← smul_neg, neg_sub]
  · rw [← smul_add]
    rw [show v + sigmaN r v + (v - sigmaN r v) = (2 : ℂ) • v by rw [two_smul]; abel, smul_smul]
    norm_num

end HeisenbergN

namespace Moonshine

open HeisenbergN TwistedHeisenberg

/-- The twisted Fock space is nonzero (it contains the vacuum `1 ≠ 0`). -/
instance (r : ℕ) : Nontrivial (FockT r) := inferInstanceAs (Nontrivial (MvPolynomial _ ℂ))

end Moonshine

end VOA
