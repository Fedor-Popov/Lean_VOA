/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.HeisenbergFock
import VOA.Examples.HeisenbergVertex
import VOA.Examples.HeisenbergVirasoro
import VOA.Examples.HeisenbergCentral
import VOA.Examples.HeisenbergGrading
import VOA.Core.VertexOperatorAlgebra

/-!
# FRONT A — the conformal bridge `Y(ω) = sugawaraField` and the VOA conformal axioms.
-/

namespace VOA

open scoped BigOperators
open MvPolynomial
open Module (End)

/-! ## §1  THE BRIDGE: `Y k (ω k) = sugawaraField k` -/

/-- `osc k (-1) (osc k (-1) vacuum) = X 0 ^ 2`: applying the lowest creation twice to the
vacuum is the square of the first variable. -/
theorem osc_neg_one_sq_vacuum (k : ℂ) :
    osc k (-1) (osc k (-1) vacuum) = (X 0 : Fock) ^ 2 := by
  rw [osc_neg_one_vacuum, osc_apply_neg k (by norm_num : (-1 : ℤ) < 0)]
  rw [show (-(-1 : ℤ) - 1).toNat = (0 : ℕ) from by norm_num]
  ring

/-- `X 0 ^ 2 = monomial (single 0 2) 1`. -/
theorem X_zero_sq_eq_monomial : (X 0 : Fock) ^ 2 = monomial (Finsupp.single 0 2) 1 := by
  rw [X_zero_eq_monomial, monomial_pow, one_pow]
  congr 1
  rw [Finsupp.smul_single, smul_eq_mul]

/-- `monoWord (single 0 2) = [0, 0]`: the state `(a₋₁)²1` has the two generators `0,0`. -/
theorem monoWord_single_zero_two : monoWord (Finsupp.single 0 2) = [0, 0] := by
  unfold monoWord
  rw [show (Finsupp.single 0 2 : ℕ →₀ ℕ).support = {0} from
    Finsupp.support_single 0 (by norm_num : (2 : ℕ) ≠ 0)]
  simp [Finsupp.single_eq_same]

/-- `nprod` depends only on the underlying distributions, not the field-witness proofs: if the
distributions agree (after a witness transport) the products agree. -/
theorem nprod_eq_nprod {a b a' b' : FormalDist (End ℂ Fock)}
    (ha : IsField a) (hb : IsField b) (ha' : IsField a') (hb' : IsField b')
    (haa : a = a') (hbb : b = b') :
    nprod ha hb = nprod ha' hb' := by
  subst haa; subst hbb; rfl

/-- `Yword k [0] = current k`: the length-1 word in the lowest generator is the basic current
(`nprod` with the identity field is the identity, and `genField k 0 = α`). -/
theorem Yword_zero (k : ℂ) : Yword k [0] = current k := by
  rw [Yword_cons]
  show nprod (genField_isField k 0) (idField_isField) = current k
  rw [nprod_idField (genField_isField k 0), genField_zero]

/-- `Yword k [0, 0] = nprod (current) (current)`: the iterated normal-ordered product of the
two lowest generators is the normal-ordered square of the basic current. -/
theorem Yword_zero_zero (k : ℂ) :
    Yword k [0, 0] = nprod (isField_current k) (isField_current k) := by
  rw [Yword_cons]
  exact nprod_eq_nprod (genField_isField k 0) (Yword_isField k [0])
    (isField_current k) (isField_current k) (genField_zero k) (Yword_zero k)

/-- **THE BRIDGE** (Gannon 5.2.5d): `Y(ω, z) = (1/2k):α(z)α(z): = sugawaraField`.  The conformal
vector `ω = (1/2k)a₋₁a₋₁1` is the monomial `(1/2k)X₀²`, and `Y(X₀²,z) = Yword [0,0] =
:α α:`, so `Y(ω,z) = (1/2k):αα: = sugawaraField`. -/
theorem Y_omega_eq_sugawara (k : ℂ) : Y k (ω k) = sugawaraField k := by
  rw [ω, map_smul, osc_neg_one_sq_vacuum, X_zero_sq_eq_monomial, Y_monomial_one,
    Ymon, monoWord_single_zero_two, Yword_zero_zero, sugawaraField]

/-! ## §2  `Lvir k n = mode (Y k (ω k)) (n+1)` -/

/-- The Sugawara mode `Lₙ` is the VOA Virasoro mode `ω₍ₙ₊₁₎ = mode (Y ω) (n+1)`:
`mode (Y ω) (n+1) = Y(ω)(-n-2) = sugawaraField(-n-2) = Lₙ` (the conformal-weight-2 shift). -/
theorem Lvir_eq_mode_Y_omega (k : ℂ) (n : ℤ) :
    Lvir k n = mode (Y k (ω k)) (n + 1) := by
  rw [mode_apply, Y_omega_eq_sugawara, show -(n + 1) - 1 = -n - 2 from by ring,
    sugawaraField]
  show Lvir k n = ((1 / (2 * k)) • nprod (isField_current k) (isField_current k)) (-n - 2)
  rw [Lvir]
  rfl

/-! ## §3  VOA1 — the Virasoro relation for `Y(ω)` -/

/-- **VOA1 (conformal symmetry)** in the exact `VertexOperatorAlgebra.virasoro` shape, with
`centralCharge = 1`: writing `Lₙ := mode (Y ω)(n+1)`,
`⁅Lₘ,Lₙ⁆ = (m-n)Lₘ₊ₙ + δ_{m+n,0}((m³-m)/12·1)·1`.  Reduces to `L_virasoro` (free-boson `c=1`)
through the bridge `Lvir = mode (Y ω)(·+1)`. -/
theorem conf_virasoro (k : ℂ) (hk : k ≠ 0) (m n : ℤ) :
    ⁅mode (Y k (ω k)) (m + 1), mode (Y k (ω k)) (n + 1)⁆
      = ((m : ℂ) - n) • mode (Y k (ω k)) (m + n + 1)
        + (if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * (1 : ℂ)) • (1 : End ℂ Fock)
           else 0) := by
  rw [← Lvir_eq_mode_Y_omega, ← Lvir_eq_mode_Y_omega,
    show m + n + 1 = (m + n) + 1 from by ring, ← Lvir_eq_mode_Y_omega]
  rw [Ring.lie_def, L_virasoro k hk m n]
  rw [show ((m : ℂ) ^ 3 - m) / 12 * (1 : ℂ) = ((m : ℂ) ^ 3 - m) / 12 from by ring]
  rw [show (1 : End ℂ Fock) = (LinearMap.id : End ℂ Fock) from rfl]
  by_cases hmn : m + n = 0
  · rw [if_pos hmn, if_pos hmn]
  · rw [if_neg hmn, if_neg hmn, zero_smul]

/-! ## §4  VOA2 — `L₀ = mode (Y ω) 1` acts as the conformal weight on each graded piece -/

/-- `osc k (-(i:ℤ)-1) p = X i * p`: the creation oscillator `a₋(i+1)` is multiplication by `Xᵢ`. -/
theorem osc_neg_eq_mulX (k : ℂ) (i : ℕ) (p : Fock) :
    osc k (-(i : ℤ) - 1) p = X i * p := by
  rw [osc_apply_neg k (by omega : -(i : ℤ) - 1 < 0)]
  congr 2
  omega

/-- The **Euler step** for `L₀`: `L₀(Xᵢ·p) = (i+1)·(Xᵢ·p) + Xᵢ·(L₀ p)`.  (The commutator
`[L₀, a₋(i+1)] = (i+1)a₋(i+1)` from `L_comm_osc`, with `a₋(i+1)` multiplication by `Xᵢ`.) -/
theorem Lvir_zero_mulX (k : ℂ) (hk : k ≠ 0) (i : ℕ) (p : Fock) :
    Lvir k 0 (X i * p) = ((i : ℂ) + 1) • (X i * p) + X i * Lvir k 0 p := by
  rw [← osc_neg_eq_mulX k i p, Lvir_osc k hk 0 (-(i : ℤ) - 1) p]
  rw [show (0 : ℤ) + (-(i : ℤ) - 1) = -(i : ℤ) - 1 from by ring]
  rw [osc_neg_eq_mulX k i p, osc_neg_eq_mulX k i (Lvir k 0 p)]
  congr 2
  push_cast; ring

/-- `L₀` kills constants: `L₀ (C a) = 0` (a constant is `a • 1`, and `L₀ 1 = 0`). -/
theorem Lvir_zero_C (k : ℂ) (a : ℂ) : Lvir k 0 (MvPolynomial.C a : Fock) = 0 := by
  rw [show (MvPolynomial.C a : Fock) = a • (vacuum : Fock) from by
        rw [vacuum, MvPolynomial.smul_eq_C_mul, mul_one],
    map_smul, Lvir_vacuum k (by norm_num : (-1 : ℤ) ≤ 0), smul_zero]

/-- The Euler step iterated over a power of one variable:
`L₀(Xᵢ^e · q) = (e·(i+1))·(Xᵢ^e·q) + Xᵢ^e·(L₀ q)`. -/
theorem Lvir_zero_mulX_pow (k : ℂ) (hk : k ≠ 0) (i : ℕ) (e : ℕ) (q : Fock) :
    Lvir k 0 (X i ^ e * q) = ((e : ℂ) * ((i : ℂ) + 1)) • (X i ^ e * q) + X i ^ e * Lvir k 0 q := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hpow : (X i : Fock) ^ (e + 1) * q = X i * (X i ^ e * q) := by rw [pow_succ]; ring
    have hpowL : (X i : Fock) * (X i ^ e * Lvir k 0 q) = X i ^ (e + 1) * Lvir k 0 q := by
      rw [pow_succ]; ring
    rw [hpow, Lvir_zero_mulX k hk i (X i ^ e * q), ih, mul_add]
    rw [mul_smul_comm, ← hpow, hpowL]
    -- goal: (i+1)•P + ((e(i+1))•P + R) = ((e+1)(i+1))•P + R, P = X^(e+1) q, R = X^(e+1) Lq
    push_cast
    module

/-- **`L₀` acts as the weighted degree on every monomial**:
`L₀ (monomial m c) = (weight weightFn m) • monomial m c`.  Proved by peeling each variable `Xᵢ`
off `monomial m c` and accumulating its weight `i+1` via the Euler step `Lvir_zero_mulX`. -/
theorem Lvir_zero_monomial (k : ℂ) (hk : k ≠ 0) (c : ℂ) (m : ℕ →₀ ℕ) :
    Lvir k 0 (monomial m c) = ((Finsupp.weight weightFn m : ℕ) : ℂ) • (monomial m c : Fock) := by
  classical
  induction m using Finsupp.induction with
  | zero =>
    rw [monomial_zero', Lvir_zero_C k,
      show (Finsupp.weight weightFn (0 : ℕ →₀ ℕ) : ℕ) = 0 from map_zero _,
      Nat.cast_zero, zero_smul]
  | single_add i e m hmi he ih =>
    -- monomial (single i e + m) c = X i ^ e * monomial m c
    rw [monomial_single_add, Lvir_zero_mulX_pow k hk i e (monomial m c), ih]
    -- weight (single i e + m) = e*(i+1) + weight m
    rw [show (Finsupp.weight weightFn (Finsupp.single i e + m) : ℕ)
          = e * (i + 1) + (Finsupp.weight weightFn m : ℕ) from by
        rw [map_add, Finsupp.weight_single, weightFn_apply, smul_eq_mul]]
    rw [mul_smul_comm]
    push_cast
    module
/-- **`L₀` acts as the weighted degree on every homogeneous piece** `gradingW w`:
`L₀ p = w • p` for `p ∈ F_w`.  (`p = ∑_{a∈supp} monomial a (coeff a p)`, each monomial of weight
`w` since `p` is weighted-homogeneous, and `Lvir_zero_monomial` gives `w` on each.) -/
theorem Lvir_zero_gradingW (k : ℂ) (hk : k ≠ 0) {w : ℕ} {p : Fock} (hp : p ∈ gradingW w) :
    Lvir k 0 p = (w : ℂ) • p := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  conv_rhs => rw [p.as_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  -- weight a = w since p is weighted-homogeneous and coeff a p ≠ 0
  have hwa : Finsupp.weight weightFn a = w := by
    rw [mem_gradingW] at hp
    exact hp (MvPolynomial.mem_support_iff.mp ha)
  rw [Lvir_zero_monomial k hk (MvPolynomial.coeff a p) a, hwa]

/-- **VOA2 (conformal weight)** in the exact `VertexOperatorAlgebra.L0_grading` shape:
`L₀ = mode (Y ω) 1` acts on each graded piece `gradingZ n` as multiplication by `n`,
`L₀ v = n • v` for `v ∈ F_n`.  (Bridge `mode (Y ω) 1 = Lvir k 0`, then `Lvir_zero_gradingW`;
the negative-degree pieces are `⊥`, where both sides vanish.) -/
theorem conf_L0_grading (k : ℂ) (hk : k ≠ 0) {n : ℤ} (v : Fock) (hv : v ∈ gradingZ n) :
    mode (Y k (ω k)) 1 v = (n : ℂ) • v := by
  rw [show (1 : ℤ) = (0 : ℤ) + 1 from rfl, ← Lvir_eq_mode_Y_omega]
  rcases lt_or_ge n 0 with hn | hn
  · rw [gradingZ_of_neg hn, Submodule.mem_bot] at hv
    rw [hv, map_zero, smul_zero]
  · rw [gradingZ_of_nonneg hn] at hv
    rw [Lvir_zero_gradingW k hk hv]
    congr 1
    have : ((n.toNat : ℤ) : ℂ) = (n : ℂ) := by rw [Int.toNat_of_nonneg hn]
    rwa [Int.cast_natCast] at this

/-! ## §5  VOA3 — translation: `Y(L₋₁ v) = ∂_z Y(v)` with `L₋₁ = mode (Y ω) 0` -/

/-- `L₋₁ = mode (Y ω) 0 = Lvir k (-1)` (the bridge at `n = -1`). -/
theorem Lvir_neg_one_eq_mode (k : ℂ) : Lvir k (-1) = mode (Y k (ω k)) 0 := by
  have := Lvir_eq_mode_Y_omega k (-1)
  rwa [show (-1 : ℤ) + 1 = 0 from by ring] at this

/-- `L₋₁(a₋₁1) = a₋₂1`: the translation generator turns the lowest creation state into the
next.  (`[L₋₁,a₋₁] = a₋₂` from `L_comm_osc`, and `L₋₁ 1 = 0`.) -/
theorem Lvir_neg_one_current_state (k : ℂ) (hk : k ≠ 0) :
    Lvir k (-1) (osc k (-1) vacuum) = osc k (-2) vacuum := by
  rw [Lvir_osc k hk (-1) (-1) vacuum, Lvir_vacuum k (by norm_num : (-1 : ℤ) ≤ -1)]
  simp only [map_zero, add_zero]
  rw [show (-1 : ℤ) + -1 = -2 from by ring,
    show (-((-1 : ℤ) : ℂ)) = 1 from by push_cast; ring, one_smul]

/-- `Y(a₋₂1, z) = ∂_z α(z)`: the field of the second creation state is the derivative current
`genField k 1 = ∂α`. -/
theorem Y_osc_neg_two (k : ℂ) :
    Y k (osc k (-2) vacuum) = deriv (current k) := by
  rw [osc_apply_neg k (by norm_num : (-2 : ℤ) < 0), vacuum, mul_one,
    show (-(-2 : ℤ) - 1).toNat = (1 : ℕ) from by norm_num, X,
    Y_monomial_one, Ymon]
  rw [show monoWord (Finsupp.single 1 1) = [1] from by
        unfold monoWord
        rw [show (Finsupp.single 1 1 : ℕ →₀ ℕ).support = {1} from
          Finsupp.support_single 1 (by norm_num : (1 : ℕ) ≠ 0)]
        simp [Finsupp.single_eq_same]]
  rw [Yword_cons]
  show nprod (genField_isField k 1) (idField_isField) = deriv (current k)
  rw [nprod_idField (genField_isField k 1),
    genField, dcurrent_succ, dcurrent_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_smul]

/-- **VOA3 at the basic current state** (Gannon 5.1.8, the generator instance): the translation
covariance `Y(L₋₁ v, z) = ∂_z Y(v, z)` holds for `v = a₋₁1` (the basic current).
`Y(L₋₁ a₋₁1) = Y(a₋₂1) = ∂α = ∂ Y(a₋₁1)`.  The full VOA3 (all states) lifts this through the
Leibniz/derivation structure of `L₋₁` on the iterated `nprod` words. -/
theorem translation_current_state (k : ℂ) (hk : k ≠ 0) :
    Y k (Lvir k (-1) (osc k (-1) vacuum)) = deriv (Y k (osc k (-1) vacuum)) := by
  rw [Lvir_neg_one_current_state k hk, Y_osc_neg_two, Y_current]

/-! ## §6  `conformal_mem` : `ω ∈ gradingZ 2`  (weight 2) -/

/-- The conformal vector `ω = (1/2k)a₋₁a₋₁1 = (1/2k)X₀²` lies in degree `2`: `ω ∈ F₂`.  (The two
creation operators `a₋₁` each carry weight `1`.) -/
theorem omega_mem_gradingW (k : ℂ) : ω k ∈ gradingW 2 := by
  rw [ω, osc_neg_one_sq_vacuum]
  refine (gradingW 2).smul_mem _ ?_
  -- X₀² is weighted-homogeneous of weight 2
  rw [mem_gradingW, X_zero_sq_eq_monomial]
  exact isWeightedHomogeneous_monomial weightFn (Finsupp.single 0 2) (1 : ℂ)
    (show Finsupp.weight weightFn (Finsupp.single (0 : ℕ) 2) = 2 from by
      rw [Finsupp.weight_single, weightFn_apply, smul_eq_mul])

/-- `ω ∈ gradingZ 2` (the `ℤ`-extended grading), the `VertexOperatorAlgebra.conformal_mem`
form. -/
theorem omega_mem_gradingZ (k : ℂ) : ω k ∈ gradingZ 2 := by
  have h := mem_gradingZ_of_gradingW (omega_mem_gradingW k)
  rwa [show ((2 : ℕ) : ℤ) = (2 : ℤ) from rfl] at h

end VOA

namespace VOA
end VOA
