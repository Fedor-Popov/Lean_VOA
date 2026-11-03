/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LatticeMorphRigid
import VOA.Examples.LatticeGenVOAInstance

/-!
# Fock-space inputs for the generation theorem of `V_L^+`  (Moonshine step M8c, `hgen`, part 1)

Lattice-general (any `L : IntegralLattice`) Fock-space facts used by
`Moonshine/Generation.lean`:

* `EEVec_eq_zero_of_lt` — the boson dressing `EE(α)_t = (E⁻(α)E⁺(α))_t` kills a weight-`w` state
  when `t < -w` (`E⁺` lowers weight by at most `w`);
* `EEVec_expand` — for `d ≥ 0` and `p` of weight `w`,
  `EE(α)_d p = ∑_{r ≤ w} S_{d+r}(α) · E⁺(α)_{-r} p` (the leading `r = 0` term is `S_d(α)·p`);
* `schurPoly`, `vSchur_nsmul_eq_sum` — `S_d(kα)` is a polynomial in `k` with vector coefficients,
  whose linear coefficient is `S_d(α)`'s linear part `d⁻¹·α(-d)` (`schurPoly_coeff_one`);
* `mem_of_forall_sum_pow_smul_mem` — a polynomial in `k ∈ ℕ` with vector coefficients lying in a
  subspace for all large `k` has all coefficients in the subspace;
* `X_mem_span_vVar` — every oscillator `h_b(-m-1)` is a combination of the `α(-m-1)`,
  `α` running over a lattice basis;
* `wordStateN_mem_gradingWN`, `gradingWN_le_span_words` — the Fock weight space is spanned by
  creation words of that weight.

## Status
`sorry`-free, no axioms beyond Lean's three.  Unconditional.
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN MvPolynomial Matrix

variable (L : IntegralLattice)

/-! ## §1  The boson dressing on a homogeneous state -/

theorem aExpVec_eq_zero_of_lt (α : L.carrier) {w N : ℕ} {p : FockN (rank L)}
    (hp : p ∈ gradingWN (rank L) w) (hN : w < N) : aExpVec L α N p = 0 := by
  have h := aExpVec_mem_gradingZN L α N hp
  rwa [gradingZN_of_neg (by omega), Submodule.mem_bot] at h

/-- `EE(α)_t p = 0` for `p` of weight `w` and `t < -w`. -/
theorem EEVec_eq_zero_of_lt (α : L.carrier) {w : ℕ} {p : FockN (rank L)}
    (hp : p ∈ gradingWN (rank L) w) {t : ℤ} (ht : t < -(w : ℤ)) : EEVec L α t p = 0 := by
  rw [EEVec, nprod_apply]
  refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
  rw [normalOrdered_apply]
  split_ifs with h0
  · rw [Module.End.mul_apply, EplusVecField_apply]
    split_ifs with h1
    · rw [aExpVec_eq_zero_of_lt L α hp (by omega), map_zero]
    · rw [LinearMap.zero_apply, map_zero]
  · rw [Module.End.mul_apply, EminusVecField_neg L α (by omega), LinearMap.zero_apply, map_zero]

/-- The expansion `EE(α)_d p = ∑_{r ≤ w} S_{d+r}(α) · E⁺(α)_{-r} p` for `p` of weight `w`. -/
theorem EEVec_expand (α : L.carrier) {w : ℕ} {p : FockN (rank L)}
    (hp : p ∈ gradingWN (rank L) w) (d : ℕ) :
    EEVec L α (d : ℤ) p
      = ∑ r ∈ Finset.range (w + 1), vSchur L α (d + r) * aExpVec L α r p := by
  rw [EEVec, nprod_apply]
  set f : ℤ → FockN (rank L) := fun m =>
    normalOrdered (EminusVecField L α) (EplusVecField L α) m ((d : ℤ) - m) p with hf
  have hval : ∀ r : ℕ, f ((d : ℤ) + r) = vSchur L α (d + r) * aExpVec L α r p := by
    intro r
    rw [hf]
    simp only
    rw [normalOrdered_apply, if_pos (by omega), Module.End.mul_apply,
      EplusVecField_nonpos L α (by omega), EminusVecField_apply, if_pos (by omega),
      show (-((d : ℤ) - ((d : ℤ) + r))).toNat = r by omega,
      show ((d : ℤ) + r).toNat = d + r by omega, EminusVec, LinearMap.mulLeft_apply]
  set emb : ℕ ↪ ℤ := ⟨fun r => (d : ℤ) + r, fun a b h => by simpa using h⟩
  have hsupp : Function.support f ⊆ ((Finset.range (w + 1)).map emb : Set ℤ) := by
    intro m hm
    rw [Function.mem_support] at hm
    have hdm : (d : ℤ) ≤ m ∧ m ≤ (d : ℤ) + w := by
      by_contra hcon
      apply hm
      rw [hf]
      simp only
      rw [normalOrdered_apply]
      split_ifs with h0
      · rw [Module.End.mul_apply, EplusVecField_apply]
        split_ifs with h1
        · rw [aExpVec_eq_zero_of_lt L α hp (by omega), map_zero]
        · rw [LinearMap.zero_apply, map_zero]
      · rw [Module.End.mul_apply, EminusVecField_neg L α (by omega), LinearMap.zero_apply,
          map_zero]
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Finset.mem_range]
    exact ⟨(m - d).toNat, by omega, by simp [emb]; omega⟩
  rw [finsum_eq_sum_of_support_subset f hsupp, Finset.sum_map]
  exact Finset.sum_congr rfl fun r _ => hval r

/-! ## §2  Scaling the charge: `S_d(kα)` as a polynomial in `k` -/

theorem chargeCoord_nsmul (k : ℕ) (α : L.carrier) (b : Fin (rank L)) :
    chargeCoord L (k • α) b = (k : ℂ) * chargeCoord L α b := by
  induction k with
  | zero => rw [zero_smul, chargeCoord_zero, Nat.cast_zero, zero_mul]
  | succ k ih => rw [succ_nsmul, chargeCoord_add, ih, Nat.cast_succ]; ring

theorem vVar_nsmul (k : ℕ) (α : L.carrier) (m : ℕ) :
    vVar L (k • α) m = (k : ℂ) • vVar L α m := by
  simp only [vVar, Finset.smul_sum, smul_smul, chargeCoord_nsmul]

/-- The polynomial (in an auxiliary variable `T`) with `S_N(kα) = schurPoly α N (k)`. -/
noncomputable def schurPoly (α : L.carrier) : ℕ → Polynomial (FockN (rank L))
  | 0 => 1
  | (N + 1) => ((N + 1 : ℂ))⁻¹ • ∑ m ∈ Finset.range (N + 1),
      Polynomial.C (vVar L α m) * (Polynomial.X * schurPoly α (N - m))

theorem schurPoly_succ (α : L.carrier) (N : ℕ) :
    schurPoly L α (N + 1) = ((N + 1 : ℂ))⁻¹ • ∑ m ∈ Finset.range (N + 1),
      Polynomial.C (vVar L α m) * (Polynomial.X * schurPoly L α (N - m)) := by
  rw [schurPoly]

theorem schurPoly_eval (α : L.carrier) (k : ℕ) (N : ℕ) :
    (schurPoly L α N).eval (algebraMap ℂ (FockN (rank L)) (k : ℂ)) = vSchur L (k • α) N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => rw [schurPoly, vSchur_zero, Polynomial.eval_one]
    | (M + 1) =>
      rw [schurPoly_succ, vSchur_succ, Polynomial.eval_smul, Polynomial.eval_finsetSum]
      congr 1
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        ih (M - m) (by omega), vVar_nsmul, Algebra.smul_def, ← mul_assoc,
        mul_comm (vVar L α m)]

theorem schurPoly_coeff_zero (α : L.carrier) (N : ℕ) :
    (schurPoly L α N).coeff 0 = if N = 0 then 1 else 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  have h := schurPoly_eval L α 0 N
  rw [Nat.cast_zero, map_zero, zero_smul] at h
  rw [h]
  rcases N with _ | N
  · rw [vSchur_zero, if_pos rfl]
  · rw [vSchur_zero_charge, if_neg (by omega)]

/-- The linear coefficient of `S_{N+1}(kα)` in `k`: `(N+1)⁻¹ · α(-N-1)`. -/
theorem schurPoly_coeff_one (α : L.carrier) (N : ℕ) :
    (schurPoly L α (N + 1)).coeff 1 = ((N + 1 : ℂ))⁻¹ • vVar L α N := by
  rw [schurPoly_succ, Polynomial.coeff_smul, Polynomial.finsetSum_coeff]
  congr 1
  rw [Finset.sum_eq_single N]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_mul, Nat.sub_self, schurPoly_coeff_zero,
      if_pos rfl, mul_one]
  · intro m hm hmN
    simp only [Finset.mem_range] at hm
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_mul, schurPoly_coeff_zero, if_neg (by omega),
      mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self N)) h

theorem vSchur_nsmul_eq_sum (α : L.carrier) (k N : ℕ) :
    vSchur L (k • α) N = ∑ i ∈ Finset.range ((schurPoly L α N).natDegree + 1),
      ((k : ℂ) ^ i) • (schurPoly L α N).coeff i := by
  rw [← schurPoly_eval, Polynomial.eval_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_pow, ← Algebra.commutes, ← Algebra.smul_def]

/-! ## §3  Polynomial interpolation in a subspace -/

/-- If `∑_{i ≤ D} kⁱ • v i ∈ G` for every natural `k ≥ K`, then every `v i` (`i ≤ D`) lies in `G`. -/
theorem mem_of_forall_sum_pow_smul_mem {M : Type*} [AddCommGroup M] [Module ℂ M]
    (G : Submodule ℂ M) (v : ℕ → M) (D K : ℕ)
    (h : ∀ k : ℕ, K ≤ k → ∑ i ∈ Finset.range (D + 1), ((k : ℂ) ^ i) • v i ∈ G) :
    ∀ i ∈ Finset.range (D + 1), v i ∈ G := by
  intro i hi
  rw [← Submodule.Quotient.mk_eq_zero]
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  set Q : Polynomial ℂ := ∑ j ∈ Finset.range (D + 1),
    Polynomial.C (φ (Submodule.Quotient.mk (v j))) * Polynomial.X ^ j with hQ
  have hroot : ∀ k : ℕ, K ≤ k → Q.IsRoot (k : ℂ) := by
    intro k hk
    have h0 := (Submodule.Quotient.mk_eq_zero G).mpr (h k hk)
    have h1 := congrArg φ h0
    rw [map_zero, ← Submodule.mkQ_apply, map_sum, map_sum] at h1
    rw [Polynomial.IsRoot, hQ, Polynomial.eval_finsetSum, ← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      Submodule.mkQ_apply, Submodule.Quotient.mk_smul, map_smul, smul_eq_mul, mul_comm]
  have hinf : Set.Infinite {x : ℂ | Q.IsRoot x} := by
    have hS : Set.Infinite ((fun k : ℕ => (k : ℂ)) '' {k : ℕ | K ≤ k}) :=
      (Set.Ici_infinite K).image (fun a _ b _ hab => by exact_mod_cast hab)
    refine hS.mono ?_
    rintro _ ⟨k, hk, rfl⟩
    exact hroot k hk
  have hQ0 : Q = 0 := Polynomial.eq_zero_of_infinite_isRoot Q hinf
  have hc := congrArg (fun P : Polynomial ℂ => P.coeff i) hQ0
  simp only [hQ, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at hc
  rwa [Finset.sum_ite_eq, if_pos hi] at hc

/-! ## §4  The oscillators are combinations of lattice oscillators -/

include L in
/-- `h_b(-m-1) = X(m,b)` lies in the span of the `α(-m-1) = vVar α m`, `α` a lattice basis vector. -/
theorem X_mem_span_vVar (hPos : L.PosDef) (m : ℕ) (b : Fin (rank L)) :
    (X (m, b) : FockN (rank L)) ∈
      Submodule.span ℂ (Set.range fun i : Fin (latRank L) => vVar L (latticeBasis L i) m) := by
  classical
  set F : Matrix (Fin (latRank L)) (Fin (latRank L)) ℂ := (frame L).map Complex.ofRealHom
  have hF : IsUnit F.det := by
    rw [show F.det = Complex.ofRealHom (frame L).det from (RingHom.map_det _ _).symm]
    exact (frame_det_isUnit L hPos).map _
  set t : Fin (latRank L) → ℂ := Pi.single (rankEquiv L b) 1
  set u : Fin (latRank L) → ℂ := F⁻¹ *ᵥ t
  have hu : F *ᵥ u = t := by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hF, Matrix.one_mulVec]
  have hcc : ∀ (i : Fin (latRank L)) (a : Fin (rank L)),
      chargeCoord L (latticeBasis L i) a = F (rankEquiv L a) i := by
    intro i a
    rw [chargeCoord, orthCoord, coordR_basis]
    simp [F, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hsum : ∑ i, u i • vVar L (latticeBasis L i) m = (X (m, b) : FockN (rank L)) := by
    simp only [vVar, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single b]
    · rw [← Finset.sum_smul]
      have h := congrFun hu (rankEquiv L b)
      simp only [Matrix.mulVec, dotProduct, t, Pi.single_eq_same] at h
      rw [show ∑ i, u i * chargeCoord L (latticeBasis L i) b = 1 by
        rw [← h]; exact Finset.sum_congr rfl fun i _ => by rw [hcc, mul_comm]]
      rw [one_smul]
    · intro a _ ha
      rw [← Finset.sum_smul]
      have h := congrFun hu (rankEquiv L a)
      simp only [Matrix.mulVec, dotProduct, t] at h
      rw [Pi.single_apply, if_neg ((rankEquiv L).injective.ne ha)] at h
      rw [show ∑ i, u i * chargeCoord L (latticeBasis L i) a = 0 by
        rw [← h]; exact Finset.sum_congr rfl fun i _ => by rw [hcc, mul_comm]]
      rw [zero_smul]
    · intro h; exact absurd (Finset.mem_univ b) h
  rw [← hsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-! ## §5  Creation words span each weight space -/

/-- The weight of a creation word: `∑ (iₜ + 1)`. -/
def wordWt {r : ℕ} (l : List (ℕ × Fin r)) : ℕ := (l.map fun ia => ia.1 + 1).sum

@[simp] theorem wordWt_nil {r : ℕ} : wordWt ([] : List (ℕ × Fin r)) = 0 := rfl

@[simp] theorem wordWt_cons {r : ℕ} (ia : ℕ × Fin r) (l : List (ℕ × Fin r)) :
    wordWt (ia :: l) = ia.1 + 1 + wordWt l := by
  simp [wordWt]

theorem wordStateN_mem_gradingWN {r : ℕ} (l : List (ℕ × Fin r)) :
    wordStateN l ∈ gradingWN r (wordWt l) := by
  induction l with
  | nil => exact vacuumN_mem_gradingWN r
  | cons ia rest ih =>
    rw [wordStateN_cons, wordWt_cons, mem_gradingWN]
    have hX : (X ia : FockN r).IsWeightedHomogeneous weightFnN (ia.1 + 1) := by
      have := isWeightedHomogeneous_X ℂ (weightFnN (r := r)) ia
      rwa [weightFnN_apply] at this
    exact hX.mul ih

/-- Every weight-`w` Fock state is a combination of creation words of weight `w`. -/
theorem gradingWN_le_span_words (r w : ℕ) :
    gradingWN r w ≤ Submodule.span ℂ {p | ∃ l : List (ℕ × Fin r), wordWt l = w ∧ p = wordStateN l} := by
  refine (gradingWN_le_span r w).trans (Submodule.span_le.mpr ?_)
  rintro _ ⟨d, hd, rfl⟩
  refine Submodule.subset_span ⟨monoWordN d, ?_, (wordStateN_monoWordN d).symm⟩
  have h1 := wordStateN_mem_gradingWN (monoWordN d)
  rw [wordStateN_monoWordN] at h1
  have h2 : (monomial d (1 : ℂ) : FockN r).IsWeightedHomogeneous weightFnN w := by
    have := isWeightedHomogeneous_monomial (R := ℂ) weightFnN d (1 : ℂ) rfl
    rwa [show Finsupp.weight weightFnN d = w from hd] at this
  exact (IsWeightedHomogeneous.inj_right (by simp) h1 h2)

end VOA.LatGen
