/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.HeisenbergTwistedModuleL0
import VOA.Moonshine.HeisenbergTwistedModuleProductFormula
import VOA.Moonshine.LatticeTwistedGrading
import VOA.Moonshine.SigmaTopTarget
import VOA.Moonshine.AutVnat
import VOA.Moonshine.AutZeroModes

/-!
# Zero modes of `h_a(−1)h_b(−1)𝟙` on the twisted sector `T⁺`
(Aut(V♮) campaign, step 3, route C, node C2 of `Notes/MONSTER_AUT_PLAN.md`)

For the twisted Heisenberg module `S[θ] = FockT r = ℂ[X_{(k,c)}]` (`X_{(k,c)} ↔ h_c(−k−½)`,
`h_c(k+½) = (k+½) ∂/∂X_{(k,c)}`), the zero mode `o(q_ab) = q_ab₍₁₎` of the quadratic state
`q_ab = h_a(−1)h_b(−1)𝟙` is

  `o(q_ab) = N^tw_ab + (δ_ab/8)·1`,
  `N^tw_ab p = Σ_{k ≥ 0} (k+½) (X_{(k,a)} ∂_{(k,b)} p + X_{(k,b)} ∂_{(k,a)} p)`.

The constant is produced by the `Δ_z` corrections of the inverse twisted product formula (the
library's `Ywt`): `Y^T(q_ab)` is `Σ_i C(−½,i) z^{−i} Fgen_a ₍₋₁₊ᵢ₎ Fgen_b`, and in mode `0` the
contractions `Fgen_a ₍₀₎ Fgen_b = ½δ_ab` and `Fgen_a ₍₁₎ Fgen_b = δ_ab z` contribute
`C(−½,1)·½δ_ab + C(−½,2)·δ_ab = (−¼ + ⅜) δ_ab = δ_ab/8`.  This is consistent with
`L₀ = Σ h(−n−½)h(n+½) + r/16` (`YT_omega_two`, where `ω = ½ Σ_a q_aa`); the diagonal case
`a = b` of `mode_Ywt_quad_zero` is `mode_Ywt_pair_zero` of `HeisenbergTwistedModuleL0`.

On the Leech twisted module `V_Λ^T = S[θ] ⊗ T_Λ` the charge-zero states act through the
Heisenberg twisted module tensored with the identity of `T_Λ` (`FL_charge_zero`, here
`YML_charge_zero`), so `o(q_ab) = (N^tw_ab + δ_ab/8) ⊗ 1` on `V_Λ^T`, hence on `T⁺` and on the
twisted block of `V♮`.

## Coordinates
The twisted Heisenberg field `h_c` of the twisted module is the image of the same generator
`h_c(−1)𝟙 = X_{(0,c)} ⊗ e^0` whose untwisted current is `α^c` (`chargeCoord`'s frame): the basis
change between the untwisted Fock frame and the twisted one is the identity.  For the Leech
lattice the only bookkeeping is `Fin.cast leech_rank : Fin (rank Λ) → Fin 24`
(`SigmaTop.cc`), the same transport used for `SigmaTop.leechYM_quad`.

## Main results
* `quadNT r a b` — the twisted quadratic operator `N^tw_ab = :Fgen_a Fgen_b:₍₀₎`;
  ⭐ `quadNT_apply` — its closed form
  `Σ_{k<K} (k+½)(X_{(k,a)}∂_{(k,b)} + X_{(k,b)}∂_{(k,a)})` for any level bound `K` of the
  argument (`exists_levelBound`).  The right side is definitionally
  `HeisenbergN.quadOp (fun k => (k : ℂ) + 1/2) K a b x` of `AutFockEigen` (not imported here).
* ⭐ `mode_Ywt_quad_zero` — `mode (Ywt [(0,a),(0,b)]) 0 = N^tw_ab + (δ_ab/8)·1`.
* ⭐ `YT_quad_two` — `Y^T(h_a(−1)h_b(−1)𝟙)₍2/2₎ = N^tw_ab + (δ_ab/8)·1` on `FockT r`.
* ⭐ `YML_charge_zero` — the restriction lemma: `Y^T_L(p ⊗ e^0)₍k/2₎ = Y^T(p)₍k/2₎ ⊗ 1`.
* ⭐ `YML_quadSt_two` — `o(q_ab) = (N^tw_ab + δ_ab/8) ⊗ 1` on `V_L^T` (any even unimodular
  positive-definite `L`); `cast_YM_quadSt_two` along `rank L = r`.
* ⭐ `leechYM_quad_two`, `leechYM_quad_two_tmul` — the Leech twisted module.
* ⭐ `plusModule_quad_one`, `plusModule_qP_one` — `q_ab₍₁₎` on `T⁺` through `plusModule`.
* ⭐ `VnatVOA_smul_quad_one`, `VnatVOA_smul_quad_one_snd` — the twisted block of `V♮`:
  `(q_ab, 0)₍₁₎ (0, t) = (0, ((N^tw_ab + δ_ab/8) ⊗ 1) t)`.
* `quadState_eq_quadSt` — the C1 state `LatGen.quadState` is `SigmaTop.quadSt`.

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`
for every theorem (checked with `lake build VOA.Moonshine.AutZeroModesTwisted` green,
9,102 jobs).  Unconditional: the only inputs are the library's twisted module
`leechTwistedModule`, its `+`-part `plusModule`, and `VnatVOA`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.AutZeroTw

open VOA VOA.Moonshine MvPolynomial TwistedHeisenberg HeisenbergN TwistedReduction
open VOA.IntegralLattice VOA.LatGen VOA.Moonshine.LatticeTwisted VOA.Moonshine.Extraspecial
open Module (End)
open scoped BigOperators TensorProduct

/-! ## §1  The twisted Heisenberg module `FockT r` -/

section Heisenberg

variable (r : ℕ)

/-- **The twisted quadratic operator** `N^tw_ab = :Fgen_a Fgen_b:₍₀₎` on `S[θ] = FockT r`. -/
noncomputable def quadNT (a b : Fin r) : End ℂ (FockT r) :=
  mode (nprod (FgenFld r a).2 (FgenFld r b).2) 0

/-- Every vector of `FockT r` has a level bound. -/
theorem exists_levelBound (x : FockT r) : ∃ K : ℕ, ∀ v ∈ x.vars, v.1 < K :=
  ⟨x.vars.sup Prod.fst + 1, fun _ hv => Nat.lt_succ_of_le (Finset.le_sup (f := Prod.fst) hv)⟩

/-- ⭐ **`N^tw_ab` in closed form**: for `x` whose variables all have level `< K`,
`N^tw_ab x = Σ_{k<K} (k+½)(X_{(k,a)} ∂_{(k,b)} x + X_{(k,b)} ∂_{(k,a)} x)`. -/
theorem quadNT_apply (a b : Fin r) (x : FockT r) (K : ℕ) (hK : ∀ v ∈ x.vars, v.1 < K) :
    quadNT r a b x
      = ∑ k ∈ Finset.range K, ((k : ℂ) + 1 / 2) •
          (X (k, a) * pderiv (k, b) x + X (k, b) * pderiv (k, a) x) := by
  classical
  rw [quadNT, mode_apply, show -(0 : ℤ) - 1 = -1 by norm_num, nprod_apply]
  set f : ℤ → FockT r := fun m => normalOrdered (Fgen r a) (Fgen r b) m (-1 - m) x with hf
  change ∑ᶠ m : ℤ, f m = _
  -- creation on the left: `m = k ≥ 0`
  have hpos : ∀ k : ℕ, f (k : ℤ) = ((k : ℂ) + 1 / 2) • (X (k, a) * pderiv (k, b) x) := by
    intro k
    rw [hf]
    simp only
    rw [normalOrdered_apply, if_pos (by positivity), Module.End.mul_apply, Fgen_apply, Fgen_apply,
      show -2 * (k : ℤ) - 1 = -(2 * (k : ℤ) + 1) by ring,
      show -2 * (-1 - (k : ℤ)) - 1 = 2 * (k : ℤ) + 1 by ring, modeT_annihilation, modeT_creation,
      mul_smul_comm]
    congr 1
    push_cast
    ring
  -- creation on the right: `m = −k−1`
  have hneg : ∀ k : ℕ, f (-(k : ℤ) - 1) = ((k : ℂ) + 1 / 2) • (X (k, b) * pderiv (k, a) x) := by
    intro k
    rw [hf]
    simp only
    rw [normalOrdered_apply, if_neg (by omega), Module.End.mul_apply, Fgen_apply, Fgen_apply,
      show -2 * (-(k : ℤ) - 1) - 1 = 2 * (k : ℤ) + 1 by ring,
      show -2 * (-1 - (-(k : ℤ) - 1)) - 1 = -(2 * (k : ℤ) + 1) by ring, modeT_annihilation,
      modeT_creation, mul_smul_comm]
    congr 1
    push_cast
    ring
  -- levels `≥ K` do not occur
  have hpd : ∀ (k : ℕ) (c : Fin r), K ≤ k → pderiv (k, c) x = 0 := fun k c hk =>
    pderiv_eq_zero_of_notMem_vars fun hv => absurd (hK _ hv) (by simp only; omega)
  let eP : ℕ ↪ ℤ := ⟨fun k => (k : ℤ), fun x y h => by simpa using h⟩
  let eN : ℕ ↪ ℤ := ⟨fun k => -(k : ℤ) - 1, fun x y h => by simp only at h; omega⟩
  have hdisj : Disjoint ((Finset.range K).map eP) ((Finset.range K).map eN) := by
    rw [Finset.disjoint_left]
    intro m hm hm'
    simp only [Finset.mem_map, Finset.mem_range, eP, eN, Function.Embedding.coeFn_mk] at hm hm'
    obtain ⟨x, -, rfl⟩ := hm
    obtain ⟨y, -, hy⟩ := hm'
    omega
  have hsupp : Function.support f ⊆ ↑((Finset.range K).map eP ∪ (Finset.range K).map eN) := by
    intro m hm
    rw [Function.mem_support] at hm
    simp only [Finset.coe_union, Finset.coe_map, Set.mem_union, Set.mem_image, Finset.mem_coe,
      Finset.mem_range, eP, eN, Function.Embedding.coeFn_mk]
    rcases lt_or_ge m 0 with hlt | hge
    · refine Or.inr ⟨(-m - 1).toNat, ?_, by omega⟩
      by_contra hk
      apply hm
      have hm' : m = -(((-m - 1).toNat : ℕ) : ℤ) - 1 := by omega
      rw [hm', hneg, hpd _ _ (by omega), mul_zero, smul_zero]
    · refine Or.inl ⟨m.toNat, ?_, by omega⟩
      by_contra hk
      apply hm
      have hm' : m = ((m.toNat : ℕ) : ℤ) := by omega
      rw [hm', hpos, hpd _ _ (by omega), mul_zero, smul_zero]
  rw [finsum_eq_sum_of_support_subset f hsupp, Finset.sum_union hdisj, Finset.sum_map,
    Finset.sum_map, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [eP, eN, Function.Embedding.coeFn_mk]
  rw [hpos, hneg, smul_add]

/-- `N^tw_ab` is symmetric in `a, b`. -/
theorem quadNT_comm (a b : Fin r) : quadNT r a b = quadNT r b a := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨K, hK⟩ := exists_levelBound r x
  rw [quadNT_apply r a b x K hK, quadNT_apply r b a x K hK]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  exact add_comm _ _

/-- ⭐ **Mode `0` of the twisted word field of `h_a(−1)h_b(−1)𝟙`**: the normal-ordered product
plus the `Δ_z` constant `δ_ab/8`. -/
theorem mode_Ywt_quad_zero (a b : Fin r) :
    mode (Ywt r [((0 : ℕ), a), ((0 : ℕ), b)]).1 0
      = quadNT r a b + (if a = b then (1 / 8 : ℂ) else 0) • (1 : End ℂ (FockT r)) := by
  rw [Ywt_cons, Ywt_single]
  have hb : ((0 : ℕ), a).1 + 3 + 2 * wordWeightNN [((0 : ℕ), b)] = 5 := by
    simp [wordWeightNN]
  rw [hb, fld_sum_val, mode_finset_sum]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Fld.smul_val, fzmul_val,
    mode_smul, mode_zmul]
  -- the five products `Fgen_a ₍₋₁₊ᵢ₎ Fgen_b`
  have e0 : (Fld.prod (-(((0 : ℕ), a).1 : ℤ) - 1 + ((0 : ℕ) : ℤ)) (FgenFld r a) (FgenFld r b)).1
      = nprod (FgenFld r a).2 (FgenFld r b).2 := by
    rw [show -(((0 : ℕ), a).1 : ℤ) - 1 + ((0 : ℕ) : ℤ) = -1 by simp, Fld.prod_of_neg (by norm_num),
      show (-(-1 : ℤ) - 1).toNat = 0 by norm_num, negProd_zero]
    rfl
  have e1 : (Fld.prod (-(((0 : ℕ), a).1 : ℤ) - 1 + ((1 : ℕ) : ℤ)) (FgenFld r a) (FgenFld r b)).1
      = opeZero r a b := by
    rw [show -(((0 : ℕ), a).1 : ℤ) - 1 + ((1 : ℕ) : ℤ) = 0 by simp, prod_Fgen_zero]
  have e2 : (Fld.prod (-(((0 : ℕ), a).1 : ℤ) - 1 + ((2 : ℕ) : ℤ)) (FgenFld r a) (FgenFld r b)).1
      = opeOne r a b := by
    rw [show -(((0 : ℕ), a).1 : ℤ) - 1 + ((2 : ℕ) : ℤ) = 1 by simp, prod_Fgen_one]
  have e3 : (Fld.prod (-(((0 : ℕ), a).1 : ℤ) - 1 + ((3 : ℕ) : ℤ)) (FgenFld r a) (FgenFld r b)).1
      = 0 := prod_Fgen_of_two_le r a b (by simp)
  have e4 : (Fld.prod (-(((0 : ℕ), a).1 : ℤ) - 1 + ((4 : ℕ) : ℤ)) (FgenFld r a) (FgenFld r b)).1
      = 0 := prod_Fgen_of_two_le r a b (by simp)
  rw [e0, e1, e2, e3, e4]
  have hz : mode (opeZero r a b) (-((1 : ℕ) : ℤ))
      = (if a = b then (1 / 2 : ℂ) else 0) • (1 : End ℂ (FockT r)) := by
    rw [mode_apply, opeZero]
    simp only [Nat.cast_one, neg_neg, sub_self, if_true]
    rfl
  have ho : mode (opeOne r a b) (-((2 : ℕ) : ℤ))
      = (if a = b then (1 : ℂ) else 0) • (1 : End ℂ (FockT r)) := by
    rw [mode_apply, opeOne]
    simp only [Nat.cast_ofNat, neg_neg, show (2 : ℤ) - 1 = 1 by norm_num, if_true]
    rfl
  have c1 : cbinom (-1 / 2) 1 = -1 / 2 := by norm_num [cbinom]
  have c2 : cbinom (-1 / 2) 2 = 3 / 8 := by norm_num [cbinom, Finset.prod_range_succ]
  rw [hz, ho, c1, c2]
  simp only [mode_zero, smul_zero, add_zero, cbinom_zero, one_smul, Nat.cast_zero, neg_zero]
  rw [quadNT, smul_smul, smul_smul, add_assoc, ← add_smul]
  congr 2
  split_ifs <;> norm_num

/-- `Y^T(u)₍k/2₎` is mode `0` of the rescaled field `F_k(u)`. -/
theorem YT_eq_mode_FT (u : FockN r) (k : ℤ) : YT r u k = mode (FT r k u).1 0 := by
  rw [FT_val, mode_resc, show ((2 : ℕ) : ℤ) * 0 + k = k by ring]

/-- The rescaled field of `h_a(−1)h_b(−1)𝟙` on the class `2` is the word field of `[(0,a),(0,b)]`. -/
theorem FT_quad_two (a b : Fin r) :
    FT r 2 ((X ((0 : ℕ), a) : FockN r) * X ((0 : ℕ), b)) = Ywt r [((0 : ℕ), a), ((0 : ℕ), b)] := by
  have h := FT_mul_X r 1 ((0 : ℕ), a) (X ((0 : ℕ), b))
  rw [show (1 : ℤ) + 1 = 2 by norm_num, FT_one_X] at h
  rw [h, Ywt_cons_star, Ywt_single]

/-- ⭐ **The twisted zero mode of `q_ab` on the Heisenberg twisted module**:
`Y^T(h_a(−1)h_b(−1)𝟙)₍2/2₎ = N^tw_ab + (δ_ab/8)·1`. -/
theorem YT_quad_two (a b : Fin r) :
    YT r ((X ((0 : ℕ), a) : FockN r) * X ((0 : ℕ), b)) 2
      = quadNT r a b + (if a = b then (1 / 8 : ℂ) else 0) • (1 : End ℂ (FockT r)) := by
  rw [YT_eq_mode_FT, FT_quad_two, mode_Ywt_quad_zero]

/-- The closed form of `YT_quad_two` on a vector with level bound `K`. -/
theorem YT_quad_two_apply (a b : Fin r) (x : FockT r) (K : ℕ) (hK : ∀ v ∈ x.vars, v.1 < K) :
    YT r ((X ((0 : ℕ), a) : FockN r) * X ((0 : ℕ), b)) 2 x
      = ∑ k ∈ Finset.range K, ((k : ℂ) + 1 / 2) •
          (X (k, a) * pderiv (k, b) x + X (k, b) * pderiv (k, a) x)
        + (if a = b then (1 / 8 : ℂ) else 0) • x := by
  rw [YT_quad_two, LinearMap.add_apply, quadNT_apply r a b x K hK, LinearMap.smul_apply,
    Module.End.one_apply]

end Heisenberg

/-! ## §2  The lattice twisted module: restriction to charge zero -/

section Lattice

variable (L : IntegralLattice.{0}) (hEven : L.Even) (hU : IsUnit (gramMat L).det) (hPos : L.PosDef)

include hPos in
/-- ⭐ **The restriction lemma**: on charge-zero states the lattice twisted vertex operator is the
Heisenberg one tensored with the identity of `T_L`: `Y^T_L(p ⊗ e^0)₍k/2₎ = Y^T(p)₍k/2₎ ⊗ 1`. -/
theorem YML_charge_zero (p : FockN (rank L)) (k : ℤ) :
    YML L hEven hU (p ⊗ₜ[ℂ] eGen L 0) k
      = (YT (rank L) p k).rTensor (Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) := by
  rw [YML_apply, FL_charge_zero L hEven hU hPos, mode_rTFld, FT_val, mode_resc,
    show ((2 : ℕ) : ℤ) * 0 + k = k by ring]

/-- The C1 quadratic state `LatGen.quadState` (a word state) is `SigmaTop.quadSt`. -/
theorem quadState_eq_quadSt (a b : Fin (rank L)) :
    LatGen.quadState L a b = SigmaTop.quadSt L hEven hPos a b := by
  rw [SigmaTop.quadSt_eq, LatGen.quadState, wordStateLatGen_eq, wordStateN_cons, wordStateN_cons,
    wordStateN_nil, mul_one]

/-- ⭐ **The twisted zero mode of `q_ab` on `V_L^T`**: `o(q_ab) = (N^tw_ab + δ_ab/8) ⊗ 1`. -/
theorem YML_quadSt_two (a b : Fin (rank L)) :
    YML L hEven hU (SigmaTop.quadSt L hEven hPos a b) 2
      = (quadNT (rank L) a b + (if a = b then (1 / 8 : ℂ) else 0) • (1 : End ℂ (FockT (rank L)))).rTensor
          (Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) := by
  rw [SigmaTop.quadSt_eq, YML_charge_zero L hEven hU hPos, YT_quad_two]

/-- The closed form of `YML_quadSt_two` on a pure tensor `p ⊗ τ`. -/
theorem YML_quadSt_two_tmul (a b : Fin (rank L)) (p : FockT (rank L))
    (τ : Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) (K : ℕ) (hK : ∀ v ∈ p.vars, v.1 < K) :
    YML L hEven hU (SigmaTop.quadSt L hEven hPos a b) 2 (p ⊗ₜ[ℂ] τ)
      = (∑ k ∈ Finset.range K, ((k : ℂ) + 1 / 2) •
            (X (k, a) * pderiv (k, b) p + X (k, b) * pderiv (k, a) p)
          + (if a = b then (1 / 8 : ℂ) else 0) • p) ⊗ₜ[ℂ] τ := by
  rw [YML_quadSt_two L hEven hU hPos, LinearMap.rTensor_tmul, LinearMap.add_apply,
    quadNT_apply _ a b p K hK, LinearMap.smul_apply, Module.End.one_apply]

/-- Transport of `YML_quadSt_two` along `rank L = r`. -/
theorem cast_YM_quadSt_two {r : ℕ} (h : rank L = r) (a b : Fin (rank L)) :
    (h ▸ latticeTwistedModule L hEven hU hPos :
        TwistedModule (thetaAut L hEven hPos) 2
          (FockT r ⊗[ℂ] Rep (cocMat L) (isUnit_det_cocMat L hEven hU))).YM
        (SigmaTop.quadSt L hEven hPos a b) 2
      = (quadNT r (Fin.cast h a) (Fin.cast h b)
          + (if a = b then (1 / 8 : ℂ) else 0) • (1 : End ℂ (FockT r))).rTensor
          (Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) := by
  subst h
  simp only [Fin.cast_eq_self]
  exact YML_quadSt_two L hEven hU hPos a b

end Lattice

/-! ## §3  The Leech twisted module, `T⁺`, and the twisted block of `V♮` -/

section Leech

open VOA.Moonshine.SigmaTop VOA.Moonshine.AutMonster

/-- ⭐ **`o(q_ab)` on the Leech twisted module** `S[θ] ⊗ T_Λ` (coordinates transported by
`cc = Fin.cast leech_rank`). -/
theorem leechYM_quad_two (a b : Fin (rank leech)) :
    leechTwistedModule.YM (qL a b) 2
      = (quadNT 24 (cc a) (cc b)
          + (if a = b then (1 / 8 : ℂ) else 0) • (1 : End ℂ (FockT 24))).rTensor leechT :=
  cast_YM_quadSt_two leech leech_even leech_isUnit_det_gramMat leech_posDef leech_rank a b

/-- ⭐ The closed form on a pure tensor `p ⊗ τ` of the Leech twisted module. -/
theorem leechYM_quad_two_tmul (a b : Fin (rank leech)) (p : FockT 24) (τ : leechT) (K : ℕ)
    (hK : ∀ v ∈ p.vars, v.1 < K) :
    leechTwistedModule.YM (qL a b) 2 (p ⊗ₜ[ℂ] τ)
      = (∑ k ∈ Finset.range K, ((k : ℂ) + 1 / 2) •
            (X (k, cc a) * pderiv (k, cc b) p + X (k, cc b) * pderiv (k, cc a) p)
          + (if a = b then (1 / 8 : ℂ) else 0) • p) ⊗ₜ[ℂ] τ := by
  rw [leechYM_quad_two, LinearMap.rTensor_tmul, LinearMap.add_apply,
    quadNT_apply _ _ _ p K hK, LinearMap.smul_apply, Module.End.one_apply]

/-- ⭐ **`q_ab₍₁₎` on `T⁺ = (V_Λ^T)⁺`** for any `u ∈ V_Λ⁺` whose underlying state is
`h_a(−1)h_b(−1)𝟙` (`LatGen.quadState`). -/
theorem plusModule_quad_one (a b : Fin (rank leech)) (u : SkewVP)
    (hu : (u : LatModuleGen leech) = LatGen.quadState leech a b) (t : TP) :
    ((mode (plusModule.YM u) 1 t : TP) : Tw)
      = (quadNT 24 (cc a) (cc b)
          + (if a = b then (1 / 8 : ℂ) else 0) • (1 : End ℂ (FockT 24))).rTensor leechT (t : Tw) := by
  rw [mode_plusModule, show (2 : ℤ) * 1 = 2 by norm_num, hu,
    quadState_eq_quadSt leech leech_even leech_posDef]
  exact congrArg (fun f => f (t : Tw)) (leechYM_quad_two a b)

/-- `q_ab₍₁₎` on `T⁺` for the library's `qP a b ∈ V_Λ⁺`. -/
theorem plusModule_qP_one (a b : Fin (rank leech)) (t : TP) :
    ((mode (plusModule.YM (qP a b)) 1 t : TP) : Tw)
      = (quadNT 24 (cc a) (cc b)
          + (if a = b then (1 / 8 : ℂ) else 0) • (1 : End ℂ (FockT 24))).rTensor leechT (t : Tw) :=
  plusModule_quad_one a b (qP a b) (quadState_eq_quadSt leech leech_even leech_posDef a b).symm t

/-- The `V♮` action of an untwisted state on a twisted one is the `plusModule` action. -/
theorem VnatVOA_smul_inl_inr (u : SkewVP) (n : ℤ) (t : TP) :
    VnatVOA.smul ((u, 0) : Vnat) n ((0, t) : Vnat) = (0, mode (plusModule.YM u) n t) := by
  change mode (VnatAxioms.YN (u, 0)) n (0, t) = _
  have hW : leechWbar (0 : TP) = 0 := map_zero VnatAxioms.wbarL
  rw [VnatAxioms.mode_YN]
  simp only [map_zero, hW, mode_zero, LinearMap.zero_apply, zero_add]

/-- ⭐ **The twisted block of `V♮`**: `(q_ab, 0)₍₁₎ (0, t) = (0, q_ab₍₁₎ t)` with
`q_ab₍₁₎ = (N^tw_ab + δ_ab/8) ⊗ 1` on `T⁺ ⊆ S[θ] ⊗ T_Λ`. -/
theorem VnatVOA_smul_quad_one (a b : Fin (rank leech)) (u : SkewVP)
    (hu : (u : LatModuleGen leech) = LatGen.quadState leech a b) (t : TP) :
    VnatVOA.smul ((u, 0) : Vnat) 1 ((0, t) : Vnat) = (0, mode (plusModule.YM u) 1 t) ∧
      ((mode (plusModule.YM u) 1 t : TP) : Tw)
        = (quadNT 24 (cc a) (cc b)
            + (if a = b then (1 / 8 : ℂ) else 0) • (1 : End ℂ (FockT 24))).rTensor leechT (t : Tw) :=
  ⟨VnatVOA_smul_inl_inr u 1 t, plusModule_quad_one a b u hu t⟩

/-- The `T⁺`-component of `(q_ab, 0)₍₁₎ (0, t)` in `S[θ] ⊗ T_Λ`. -/
theorem VnatVOA_smul_quad_one_snd (a b : Fin (rank leech)) (u : SkewVP)
    (hu : (u : LatModuleGen leech) = LatGen.quadState leech a b) (t : TP) :
    (VnatVOA.smul ((u, 0) : Vnat) 1 ((0, t) : Vnat)).1 = 0 ∧
      (((VnatVOA.smul ((u, 0) : Vnat) 1 ((0, t) : Vnat)).2 : TP) : Tw)
        = (quadNT 24 (cc a) (cc b)
            + (if a = b then (1 / 8 : ℂ) else 0) • (1 : End ℂ (FockT 24))).rTensor leechT (t : Tw) := by
  rw [VnatVOA_smul_inl_inr]
  exact ⟨rfl, plusModule_quad_one a b u hu t⟩

end Leech

end VOA.Moonshine.AutZeroTw
