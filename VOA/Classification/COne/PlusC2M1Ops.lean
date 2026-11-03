/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.PlusC2M1Pair
import VOA.Core.WeakAssoc

/-!
# `L(−1)` and `W⁴₍₁₎` act on the neutral Fock space as derivations

On the charge-`0` sector of `V_{2m}` (rank-one Fock space, variables `x_k = h(−k−1)`):

* `T_latStateGen` — `T = L(−1)` is the derivation `x_k ↦ (k+1)·x_{k+1}` (`Dop`);
* `W1_latStateGen` — `W⁴₍₁₎` is the derivation `x_k ↦ 10(k+1)(k+2)²·x_{k+2}` (`DWop`).

The second is proved from the commutator formula
`[W₍₁₎, h₍ₙ₎] = (W₍₀₎h)₍ₙ₊₁₎ + (W₍₁₎h)₍ₙ₎` with `W₍₀₎h = 60·x₃`, `W₍₁₎h = 40·x₂` (kernel-checked
with the evaluator of `PlusC2Eval.lean`), and the mode formula for one-particle states.  Both are
the inputs of the quadratic step of the strong-generation argument (`PlusC2M1Gen.lean`).

Also: `smul_one_comm` (any VOA) — `u₍₁₎v₍ᵦ₎x = v₍ᵦ₎u₍₁₎x + (u₍₀₎v)₍₁₊ᵦ₎x + (u₍₁₎v)₍ᵦ₎x`,
the `a = 1` commutator formula with no side condition on the locality bound.
-/

set_option linter.style.longLine false

namespace VOA

open Module (End)

namespace VertexOperatorAlgebra

variable {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- The commutator formula with one locality bound for all modes. -/
theorem mode_commutator_unif (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    ∃ N : ℕ, ∀ a b : ℤ, ⁅mode (W.Y u) a, mode (W.Y v) b⁆
      = ∑ j : Fin N, gBinom a (j : ℕ) • mode (W.Y (W.smul u (j : ℕ) v)) (a + b - (j : ℕ)) := by
  obtain ⟨N, c, hdecomp⟩ := bracket_deltaSum W.toPreVertexAlgebra u v
  refine ⟨N, fun a b => ?_⟩
  rw [mode_bracket_ope W.toPreVertexAlgebra u v hdecomp a b]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hne : ((j : ℕ).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hcj : c j = (((j : ℕ).factorial : ℂ)⁻¹) • W.Y (W.smul u (j : ℕ) v) := by
    have hrec := cCoeff_deltaSum c j
    rw [← hdecomp, nth_product] at hrec
    rw [hrec, ← Int.cast_smul_eq_zsmul ℂ ((j : ℕ).factorial : ℤ), Int.cast_natCast, smul_smul,
      inv_mul_cancel₀ hne, one_smul]
  rw [hcj, mode_smul,
    ← Int.cast_smul_eq_zsmul ℂ (∏ i ∈ Finset.range (j : ℕ), (a - (i : ℤ))), smul_smul]
  congr 1
  rw [gBinom, div_eq_mul_inv]
  congr 1
  push_cast
  rfl

theorem smul_comm_apply (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    ∃ N : ℕ, ∀ (a b : ℤ) (x : 𝒱), W.smul u a (W.smul v b x) - W.smul v b (W.smul u a x) =
      ∑ j ∈ Finset.range N, gBinom a j • W.smul (W.smul u j v) (a + b - j) x := by
  obtain ⟨N, hN⟩ := mode_commutator_unif W u v
  refine ⟨N, fun a b x => ?_⟩
  have h := DFunLike.congr_fun (hN a b) x
  rw [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply] at h
  simp only [← PreVertexAlgebra.smul_def] at h
  rw [h, LinearMap.sum_apply, ← Fin.sum_univ_eq_sum_range
    (fun j => gBinom a j • W.smul (W.smul u j v) (a + b - j) x) N]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [PreVertexAlgebra.smul_def, LinearMap.smul_apply]

theorem gBinom_one_ge_two (j : ℕ) : gBinom 1 (j + 1 + 1) = 0 := by
  rw [gBinom, Finset.prod_eq_zero (i := 1) (Finset.mem_range.2 (by omega)) (by simp), zero_div]

/-- **The `a = 1` commutator formula.** -/
theorem smul_one_comm (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (b : ℤ) :
    W.smul u 1 (W.smul v b x) = W.smul v b (W.smul u 1 x) + W.smul (W.smul u 0 v) (1 + b) x +
      W.smul (W.smul u 1 v) b x := by
  obtain ⟨N, hN⟩ := smul_comm_apply W u v
  have hv0 := hN 0 (-1) W.vacuum
  have hv1 := hN 1 (-1) W.vacuum
  have hx := hN 1 b x
  have e1 : W.smul v (-1) W.vacuum = v := W.toPreVertexAlgebra.smul_vacuum_neg_one v
  have e2 : W.smul u 0 W.vacuum = 0 := W.toPreVertexAlgebra.smul_vacuum_nonneg u le_rfl
  have e3 : W.smul u 1 W.vacuum = 0 := W.toPreVertexAlgebra.smul_vacuum_nonneg u zero_le_one
  rw [e1, e2, PreVertexAlgebra.smul_zero_right, sub_zero] at hv0
  rw [e1, e3, PreVertexAlgebra.smul_zero_right, sub_zero] at hv1
  suffices hs : W.smul u 1 (W.smul v b x) - W.smul v b (W.smul u 1 x) =
      W.smul (W.smul u 0 v) (1 + b) x + W.smul (W.smul u 1 v) b x by
    rw [add_assoc, ← hs]; abel
  rw [hx]
  rcases N with _ | _ | N
  · rw [Finset.sum_range_zero] at hv0 hv1 ⊢
    rw [hv0, hv1, PreVertexAlgebra.smul_zero_left, PreVertexAlgebra.smul_zero_left, add_zero]
  · rw [Finset.sum_range_one] at hv1 ⊢
    simp only [Nat.cast_zero, sub_zero, gBinom_zero, one_smul] at hv1 ⊢
    rw [show (1 : ℤ) + -1 = 0 by norm_num, W.toPreVertexAlgebra.smul_vacuum_nonneg _ le_rfl] at hv1
    rw [hv1, PreVertexAlgebra.smul_zero_left, add_zero]
  · rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [gBinom_one_ge_two, zero_smul, Finset.sum_const_zero, zero_add, gBinom_zero,
      one_smul, Nat.cast_zero, sub_zero]
    have hb1 : gBinom 1 (0 + 1) = 1 := by simp [gBinom]
    rw [hb1, one_smul, show (1 : ℤ) + b - ((0 + 1 : ℕ) : ℤ) = b by push_cast; ring,
      show ((0 + 1 : ℕ) : ℤ) = 1 by norm_num]
    abel

end VertexOperatorAlgebra

end VOA

namespace VOA.Classification.COne

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN VOA.Moonshine LatMod
  MvPolynomial VOA.TripletNilp VOA.SparseRational PlusC2Eval

namespace PlusC2

variable (m : ℕ) (hm : 1 ≤ m)

/-! ## §1  The derivations -/

/-- `L(−1)` on the Fock space: `x_k ↦ (k+1)x_{k+1}`. -/
noncomputable def Dop : Derivation ℂ (FockN (rank (latP m))) (FockN (rank (latP m))) :=
  MvPolynomial.mkDerivation ℂ fun v => (((v.1 : ℂ) + 1)) • X (v.1 + 1, v.2)

/-- `W⁴₍₁₎` on the Fock space: `x_k ↦ 10(k+1)(k+2)²x_{k+2}`. -/
noncomputable def DWop : Derivation ℂ (FockN (rank (latP m))) (FockN (rank (latP m))) :=
  MvPolynomial.mkDerivation ℂ fun v => (10 * ((v.1 : ℂ) + 1) * ((v.1 : ℂ) + 2) ^ 2) • X (v.1 + 2, v.2)

theorem Dop_X (k : ℕ) (a : Fin (rank (latP m))) :
    Dop m (X (k, a)) = (((k : ℂ) + 1)) • X (k + 1, a) := by
  rw [Dop, mkDerivation_X]

theorem DWop_X (k : ℕ) (a : Fin (rank (latP m))) :
    DWop m (X (k, a)) = (10 * ((k : ℂ) + 1) * ((k : ℂ) + 2) ^ 2) • X (k + 2, a) := by
  rw [DWop, mkDerivation_X]

/-! ## §2  `T = L(−1)` -/

/-- `h = h(−1)𝟙` creates `x_k`. -/
theorem H_smul (k : ℕ) (p : FockN (rank (latP m))) :
    (V2m m hm).smul (bosonState (latP m) (a0 m)) (-(k : ℤ) - 1) (latStateGen (latP m) p 0) =
      latStateGen (latP m) (X (k, a0 m) * p) 0 := by
  unfold V2m
  exact smul_bosonState_neg_latStateGen (latP m) (latP_even m) (latP_posDef m hm) (a0 m) k p 0

theorem vac_eq : (V2m m hm).vacuum = latStateGen (latP m) 1 0 := rfl

theorem latStateGen_sub' (p q : FockN (rank (latP m))) :
    latStateGen (latP m) (p - q) 0 = latStateGen (latP m) p 0 - latStateGen (latP m) q 0 := by
  simp only [latStateGen, TensorProduct.sub_tmul]

/-- **`T` is the derivation `Dop` on the charge-`0` sector.** -/
theorem T_latStateGen (q : FockN (rank (latP m))) :
    (V2m m hm).toPreVertexAlgebra.T (latStateGen (latP m) q 0) = latStateGen (latP m) (Dop m q) 0 := by
  induction q using MvPolynomial.induction_on with
  | C c =>
    rw [show (MvPolynomial.C c : FockN (rank (latP m))) = c • (1 : FockN (rank (latP m))) by
      rw [smul_eq_C_mul, mul_one], latStateGen_csmul, map_smul, ← vac_eq m hm, PreVertexAlgebra.T_vacuum,
      smul_zero, Derivation.map_smul, Derivation.map_one_eq_zero, smul_zero]
    simp [latStateGen]
  | add p q hp hq => rw [latStateGen_add_boson, map_add, hp, hq, map_add, latStateGen_add_boson]
  | mul_X p v hp =>
    obtain ⟨k, a⟩ := v
    have ha := a0_unique m a
    subst ha
    rw [mul_comm]
    have h := VertexOperatorAlgebra.smul_comm_T (V2m m hm) (bosonState (latP m) (a0 m))
      (latStateGen (latP m) p 0) (-(k : ℤ) - 1)
    rw [hp, H_smul, H_smul] at h
    have h2 : (V2m m hm).smul (bosonState (latP m) (a0 m)) (-(k : ℤ) - 1 - 1)
        (latStateGen (latP m) p 0) = latStateGen (latP m) (X (k + 1, a0 m) * p) 0 := by
      rw [show -(k : ℤ) - 1 - 1 = -((k + 1 : ℕ) : ℤ) - 1 by push_cast; ring, H_smul]
    rw [h2] at h
    have h3 : (V2m m hm).toPreVertexAlgebra.T (latStateGen (latP m) (X (k, a0 m) * p) 0) =
        latStateGen (latP m) (X (k, a0 m) * Dop m p) 0 -
          ((-(k : ℤ) - 1) • latStateGen (latP m) (X (k + 1, a0 m) * p) 0) := by
      rw [h]; abel
    rw [h3, ← Int.cast_smul_eq_zsmul ℂ, ← latStateGen_csmul, ← latStateGen_sub']
    congr 1
    rw [Derivation.leibniz, Dop_X, smul_eq_mul, smul_eq_mul,
      show (((-(k : ℤ) - 1 : ℤ)) : ℂ) = -((k : ℂ) + 1) by push_cast; ring, neg_smul,
      sub_neg_eq_add, mul_smul_comm, mul_comm p]

/-! ## §3  `W⁴₍₁₎` -/

/-- `W⁴` as a lattice state. -/
noncomputable abbrev Wlat : LatModuleGen (latP m) := latStateGen (latP m) (W4poly m) 0

include hm in
theorem Wlat_eq : Wlat m = latStateGen (latP m) (evR (a0 m) WR) 0 := hasPoly_W m hm

theorem bosonState_eq_evR :
    bosonState (latP m) (a0 m) = latStateGen (latP m) (evR (a0 m) [(1, [0])]) 0 := by
  rw [bosonState]
  congr 1
  simp [evalRaw, evalWord]

theorem W0H_cert : normR (polyAct WR (-1) 1 [(1, [0])]) = [(60, [3])] := by decide +kernel
theorem W1H_cert : normR (polyAct WR (-2) 1 [(1, [0])]) = [(40, [2])] := by decide +kernel

theorem W_smul_H (n : ℕ) :
    (V2m m hm).smul (Wlat m) n (bosonState (latP m) (a0 m)) =
      latStateGen (latP m) (evR (a0 m) (normR (polyAct WR (-(n : ℤ) - 1) 1 [(1, [0])]))) 0 := by
  rw [Wlat_eq m hm, bosonState_eq_evR, V2m_smul_evR m hm WR [(1, [0])] n 1 (by decide), evR_normR]

theorem W0H_lat : (V2m m hm).smul (Wlat m) 0 (bosonState (latP m) (a0 m)) =
    latStateGen (latP m) (evR (a0 m) [(60, [3])]) 0 := by
  have := W_smul_H m hm 0
  rw [show (-((0 : ℕ) : ℤ) - 1) = -1 by norm_num, W0H_cert] at this
  simpa using this

theorem W1H_lat : (V2m m hm).smul (Wlat m) 1 (bosonState (latP m) (a0 m)) =
    latStateGen (latP m) (evR (a0 m) [(40, [2])]) 0 := by
  have := W_smul_H m hm 1
  rw [show (-((1 : ℕ) : ℤ) - 1) = -2 by norm_num, W1H_cert] at this
  simpa using this

/-- Modes of the one-particle state `c·x_j` on charge-`0` states. -/
theorem onePart_smul (c : ℚ) (j : ℕ) (n : ℤ) (p : FockN (rank (latP m))) :
    (V2m m hm).smul (latStateGen (latP m) (evR (a0 m) [(c, [j])]) 0) n (latStateGen (latP m) p 0) =
      latStateGen (latP m) ((((c : ℚ) : ℂ) * ((((∏ l ∈ Finset.range j, ((-n - 1 : ℤ) + 1 + l) : ℤ) : ℂ)) *
        (j.factorial : ℂ)⁻¹)) • oscN (rank (latP m)) 1 (a0 m) (-((-n - 1) + j) - 1) p) 0 := by
  rw [PlusC2Eval.V2m_smul_sec0]
  have : evR (a0 m) [(c, [j])] = ((c : ℂ)) • X (j, a0 m) := by
    simp [evalRaw, evalWord, smul_eq_C_mul]
  rw [this, map_smul, YN_X']
  rw [show ((((c : ℚ) : ℂ)) • genFieldN (rank (latP m)) 1 (a0 m) j) (-n - 1) =
      (((c : ℚ) : ℂ)) • genFieldN (rank (latP m)) 1 (a0 m) j (-n - 1) from rfl,
    LinearMap.smul_apply, genFieldN_coeff, LinearMap.smul_apply, smul_smul]

/-- One-particle modes in creation form. -/
theorem onePart_smul' (c : ℚ) (j : ℕ) (n : ℤ) (t : ℕ) (ht : n - j = -(t : ℤ) - 1)
    (p : FockN (rank (latP m))) :
    (V2m m hm).smul (latStateGen (latP m) (evR (a0 m) [(c, [j])]) 0) n (latStateGen (latP m) p 0) =
      latStateGen (latP m) ((((c : ℚ) : ℂ) * ((((∏ l ∈ Finset.range j, ((-n - 1 : ℤ) + 1 + l) : ℤ) : ℂ)) *
        (j.factorial : ℂ)⁻¹)) • (X (t, a0 m) * p)) 0 := by
  rw [onePart_smul, show -((-n - 1) + (j : ℤ)) - 1 = -(t : ℤ) - 1 by omega,
    oscN_apply_neg _ _ _ (by omega), show (-(-(t : ℤ) - 1) - 1).toNat = t by omega]

/-- **`W⁴₍₁₎` is the derivation `DWop` on the charge-`0` sector.** -/
theorem W1_latStateGen (q : FockN (rank (latP m))) :
    (V2m m hm).smul (Wlat m) 1 (latStateGen (latP m) q 0) = latStateGen (latP m) (DWop m q) 0 := by
  induction q using MvPolynomial.induction_on with
  | C c =>
    rw [show (MvPolynomial.C c : FockN (rank (latP m))) = c • (1 : FockN (rank (latP m))) by
      rw [smul_eq_C_mul, mul_one], latStateGen_csmul, PreVertexAlgebra.smul_smul_right, ← vac_eq m hm,
      (V2m m hm).toPreVertexAlgebra.smul_vacuum_nonneg _ zero_le_one, smul_zero, Derivation.map_smul,
      Derivation.map_one_eq_zero, smul_zero]
    simp [latStateGen]
  | add p q hp hq =>
    rw [latStateGen_add_boson, PreVertexAlgebra.smul_add_right, hp, hq, map_add, latStateGen_add_boson]
  | mul_X p v hp =>
    obtain ⟨k, a⟩ := v
    have ha := a0_unique m a
    subst ha
    rw [mul_comm, ← H_smul m hm k p, VertexOperatorAlgebra.smul_one_comm, hp, H_smul,
      W0H_lat, W1H_lat, onePart_smul' m hm 60 3 _ (k + 2) (by push_cast; ring),
      onePart_smul' m hm 40 2 _ (k + 2) (by push_cast; ring), ← latStateGen_add_boson,
      ← latStateGen_add_boson]
    congr 1
    rw [Derivation.leibniz, DWop_X, smul_eq_mul, smul_eq_mul, mul_smul_comm, mul_comm p]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, Nat.factorial]
    push_cast
    module

end PlusC2

end VOA.Classification.COne
