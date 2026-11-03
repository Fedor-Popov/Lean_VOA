/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2SectorFiberModule
import VOA.DeligneAudit.A2SectorB5
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# The local Weyl and fusion relations on the fibre generator (A₂)

For `sl₃` (`bracketTable`, generator `δ_{f₁₂}`, index `5`), the class `w` of `δ_{f₁₂}` in the fibre
`W_m / B₊ W_m` satisfies the local Weyl relations of `W_loc(mθ)` and the fusion relations
`(f_α ⊗ t^m) w = 0`:

* `e_α ⊗ t^r` kill `δ_{f₁₂}` (no bracket `[e_α, x]` has an `f₁₂` component);
* `h ⊗ t^r δ_{f₁₂} = p_r(z) δ_{f₁₂}` (power sums), so `h ⊗ 1` acts by `m` and `h ⊗ t^r` (`r ≥ 1`)
  lands in `B₊ W`;
* `(f_i ⊗ 1)^{m+1} δ_{f₁₂} = 0` by weights;
* `f_α ⊗ t^m δ_{f₁₂} ∈ B₊ W` by Vieta: `Σ_j e_j(z)(-z_k)^{m-j} = ∏_i (z_i - z_k) = 0`.
-/

namespace VOA.DeligneAudit.A2

open MvPolynomial VOA.AffineSl3 VOA.DeligneAuxiliaryCollision VOA.QuadraticCurrentFunctionalCarrier
open VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.SectorGraded VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.SectorFiber VOA.DeligneAudit.SectorFiberModule

noncomputable section

/-- **The `sl₃` structure constants satisfy the Jacobi identity in coordinates.** -/
theorem jacobiCoord : JacobiCoord bracketTable := by
  intro a b x c
  have hL := leibniz_lie (generator a) (generator b) (generator x)
  have hc := congrArg (fun y => coordinatesLinear y c) hL
  simp only [generator_bracket, lie_sum, sum_lie, lie_smul, smul_lie, map_add, map_sum,
    map_smul] at hc
  simp only [coordinatesLinear, LinearMap.coe_mk, AddHom.coe_mk, coordinates_generator,
    Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    structureConstant_eq_table] at hc
  linear_combination -hc

/-! ## Loop operators on the generator -/

theorem deltaVec_update (m : ℕ) (t : Fin m → Fin 8) (i : Fin m) (c c₀ : Fin 8) :
    deltaVec (K := ℂ) m c₀ (Function.update t i c) =
      if c = c₀ ∧ ∀ j, j ≠ i → t j = c₀ then 1 else 0 := by
  simp only [deltaVec]
  congr 1
  apply propext
  constructor
  · intro h
    refine ⟨by simpa using congrFun h i, fun j hj => ?_⟩
    have := congrFun h j
    rwa [Function.update_of_ne hj] at this
  · rintro ⟨rfl, h⟩
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · rw [Function.update_of_ne hj, h j hj]

theorem loopOp_deltaVec_apply (m : ℕ) (x : Fin 8) (r : ℕ) (c₀ : Fin 8) (t : Fin m → Fin 8) :
    loopOp bracketTable m x r (deltaVec m c₀) t =
      -∑ i, if ∀ j, j ≠ i → t j = c₀ then zr i ^ r * MvPolynomial.C (bracketTable x (t i) c₀) else 0 := by
  simp only [loopOp, LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [deltaVec_update, mul_ite, mul_one, mul_zero]
  by_cases h : ∀ j, ¬ j = i → t j = c₀
  · rw [if_pos h]
    have h' : ∀ j, j ≠ i → t j = c₀ := h
    simp only [show (∀ j, j ≠ i → t j = c₀) ↔ True from iff_true_intro h', and_true]
    rw [Finset.sum_ite_eq' Finset.univ c₀, if_pos (Finset.mem_univ _)]
  · rw [if_neg h]
    simp only [h, and_false, if_false, Finset.sum_const_zero, mul_zero]

theorem raising_table (e : Fin 8) (he : e.val < 3) (y : Fin 8) : bracketTable e y 5 = 0 := by
  fin_cases e <;> fin_cases y <;> simp_all [bracketTable]

theorem loopOp_raising_deltaVec (m : ℕ) (e : Fin 8) (he : e.val < 3) (r : ℕ) :
    loopOp bracketTable m e r (deltaVec m 5) = 0 := by
  funext t
  rw [loopOp_deltaVec_apply]
  simp [raising_table e he]

theorem cartan_table (h : Fin 8) (hh : 6 ≤ h.val) (y : Fin 8) :
    bracketTable h y 5 = if y = 5 then -1 else 0 := by
  fin_cases h <;> fin_cases y <;> simp_all [bracketTable]

/-- The power sum `p_r(z)` as a symmetric polynomial. -/
def psumS (m r : ℕ) : SymAlg (K := ℂ) m :=
  ⟨psum (Fin (m + 0)) ℂ r, psum_isSymmetric _ _ r⟩

theorem psumS_mem (m r : ℕ) : psumS m r ∈ symDeg (K := ℂ) m r := by
  change psum (Fin (m + 0)) ℂ r ∈ homogeneousSubmodule _ ℂ r
  rw [mem_homogeneousSubmodule, psum]
  exact IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i r

theorem loopOp_cartan_deltaVec (m : ℕ) (h : Fin 8) (hh : 6 ≤ h.val) (r : ℕ) :
    loopOp bracketTable m h r (deltaVec m 5) = psumS m r • deltaVec m 5 := by
  funext t
  rw [loopOp_deltaVec_apply, SectorFiberModule.smul_apply_sym]
  simp only [cartan_table h hh]
  by_cases ht : t = fun _ => 5
  · subst ht
    simp [deltaVec, psumS, psum, zr]
  · have hd : deltaVec (K := ℂ) m 5 t = 0 := by simp [deltaVec, ht]
    rw [hd, mul_zero, neg_eq_zero]
    refine Finset.sum_eq_zero fun i _ => ?_
    split_ifs with h1 h2
    · exfalso; apply ht; funext j
      by_cases hj : j = i
      · subst hj; exact h2
      · exact h1 j hj
    · simp
    · rfl

/-! ## Vieta and the fusion relation -/

theorem vieta_zero (m : ℕ) (k : Fin m) :
    ∑ j ∈ Finset.range (m + 1),
      (-1) ^ j * (esymm (Fin (m + 0)) ℂ j * zr (K := ℂ) k ^ (m - j)) = 0 := by
  have h := Multiset.prod_X_sub_X_eq_sum_esymm
    (Finset.univ.val.map (fun i : Fin (m + 0) => (X i : MvPolynomial (Fin (m + 0)) ℂ)))
  have he := congrArg (Polynomial.eval (zr (K := ℂ) k)) h
  rw [Polynomial.eval_multiset_prod] at he
  simp only [Multiset.map_map, Function.comp_apply, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg,
    Polynomial.eval_one] at he
  rw [← esymm_eq_multiset_esymm] at he
  change ∑ j ∈ Finset.range (m + 0 + 1),
    (-1) ^ j * (esymm (Fin (m + 0)) ℂ j * zr (K := ℂ) k ^ (m + 0 - j)) = 0
  rw [← he]
  apply Multiset.prod_eq_zero
  rw [Multiset.mem_map]
  exact ⟨Fin.castAdd 0 k, Finset.mem_univ_val _, sub_self _⟩

/-- The elementary symmetric polynomial as an element of `SymAlg`. -/
def esymmS (m j : ℕ) : SymAlg (K := ℂ) m :=
  ⟨esymm (Fin (m + 0)) ℂ j, esymm_isSymmetric _ _ j⟩

theorem esymmS_mem (m j : ℕ) : esymmS m j ∈ symDeg (K := ℂ) m j := by
  change esymm (Fin (m + 0)) ℂ j ∈ homogeneousSubmodule _ ℂ j
  rw [mem_homogeneousSubmodule, esymm]
  refine IsHomogeneous.sum _ _ _ fun u hu => ?_
  have h := IsHomogeneous.prod u (fun i => (X i : MvPolynomial (Fin (m + 0)) ℂ)) (fun _ => 1)
    (fun i _ => isHomogeneous_X ℂ i)
  rwa [Finset.sum_const, smul_eq_mul, mul_one, (Finset.mem_powersetCard.mp hu).2] at h

/-- **Vieta on the generator**: `f ⊗ t^m δ = -Σ_{j=1}^m (-1)^j e_j(z) (f ⊗ t^{m-j}) δ`. -/
theorem loopOp_vieta (m : ℕ) (x : Fin 8) :
    loopOp bracketTable m x m (deltaVec m 5) =
      -∑ j ∈ Finset.Ico 1 (m + 1), ((-1 : ℂ) ^ j) •
        (esymmS m j • loopOp bracketTable m x (m - j) (deltaVec m 5)) := by
  funext t
  simp only [Finset.sum_apply, Pi.neg_apply, Pi.smul_apply, SectorFiberModule.smul_apply_sym,
    loopOp_deltaVec_apply]
  simp only [smul_neg, mul_neg, Finset.sum_neg_distrib, neg_neg, Finset.mul_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  rw [neg_eq_iff_eq_neg, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hc
  · have hv := vieta_zero m i
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)] at hv
    simp only [pow_zero, one_mul, Nat.sub_zero, esymm_zero] at hv
    have : zr (K := ℂ) i ^ m = -∑ j ∈ Finset.Ico 1 (m + 1),
        (-1) ^ j * (esymm (Fin (m + 0)) ℂ j * zr i ^ (m - j)) := by
      rw [eq_neg_iff_add_eq_zero]; exact hv
    rw [this, neg_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Subalgebra.smul_def, smul_eq_mul, smul_eq_C_mul]
    simp only [esymmS, map_pow, map_neg, map_one]
    ring
  · simp

/-! ## Weights and the integrability relations `(f_i ⊗ 1)^{m+1} w = 0` -/

/-- The `sl₃` weights of the basis, in simple-root coordinates. -/
def wt : Fin 8 → ℤ × ℤ := ![(1, 0), (0, 1), (1, 1), (-1, 0), (0, -1), (-1, -1), (0, 0), (0, 0)]

set_option maxHeartbeats 4000000 in -- 512 table entries
theorem table_wt (x y c : Fin 8) (h : wt c ≠ wt x + wt y) : bracketTable x y c = 0 := by
  fin_cases x <;> fin_cases y <;> fin_cases c <;> simp_all [wt, bracketTable]

/-- `p` is supported on tensor indices of total weight `μ`. -/
def SuppW {m : ℕ} (μ : ℤ × ℤ) (p : TensorPolynomial (K := ℂ) (σ := Fin 8) m 0) : Prop :=
  ∀ t, ∑ i, wt (t i) ≠ μ → p t = 0

theorem sum_wt_update {m : ℕ} (t : Fin m → Fin 8) (i : Fin m) (c : Fin 8) :
    ∑ j, wt (Function.update t i c j) = (∑ j, wt (t j)) - wt (t i) + wt c := by
  have h1 : ∀ g : Fin m → ℤ × ℤ, ∑ j, g j = g i + ∑ j ∈ Finset.univ.erase i, g j := fun g =>
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  rw [h1, h1 (fun j => wt (t j))]
  simp only [Function.update_self]
  have h2 : ∑ j ∈ Finset.univ.erase i, wt (Function.update t i c j) =
      ∑ j ∈ Finset.univ.erase i, wt (t j) :=
    Finset.sum_congr rfl fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [h2]
  abel

theorem loopOp_suppW {m : ℕ} {μ : ℤ × ℤ} {p : TensorPolynomial (K := ℂ) (σ := Fin 8) m 0}
    (hp : SuppW μ p) (x : Fin 8) (r : ℕ) : SuppW (μ - wt x) (loopOp bracketTable m x r p) := by
  intro t ht
  simp only [loopOp, LinearMap.coe_mk, AddHom.coe_mk, neg_eq_zero]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Finset.sum_eq_zero, mul_zero]
  intro c _
  by_cases hc : wt c = wt x + wt (t i)
  · rw [hp (Function.update t i c) (by
      rw [sum_wt_update, hc]
      intro h; apply ht; rw [← h]; abel), mul_zero]
  · rw [table_wt x (t i) c hc, map_zero, zero_mul]

theorem deltaVec_suppW (m : ℕ) : SuppW (m • wt 5) (deltaVec (K := ℂ) m 5) := by
  intro t ht
  simp only [deltaVec]
  rw [if_neg]
  rintro rfl
  apply ht
  simp

theorem applyWord_replicate (m k : ℕ) (x : Fin 8) :
    applyWord bracketTable m (List.replicate k (x, 0)) (deltaVec (K := ℂ) m 5) =
      (loopOp bracketTable m x 0)^[k] (deltaVec m 5) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, Function.iterate_succ_apply', ← ih]
      rfl

theorem iterate_suppW (m k : ℕ) (x : Fin 8) :
    SuppW (m • wt 5 - k • wt x) ((loopOp bracketTable m x 0)^[k] (deltaVec (K := ℂ) m 5)) := by
  induction k with
  | zero => simpa using deltaVec_suppW m
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      have h := loopOp_suppW ih x 0
      rwa [show m • wt 5 - k • wt x - wt x = m • wt 5 - (k + 1) • wt x by
        rw [add_smul, one_smul]; abel] at h

theorem suppW_eq_zero {m : ℕ} {μ : ℤ × ℤ} {p : TensorPolynomial (K := ℂ) (σ := Fin 8) m 0}
    (hp : SuppW μ p) (hμ : ∀ t : Fin m → Fin 8, ∑ i, wt (t i) ≠ μ) : p = 0 :=
  funext fun t => hp t (hμ t)

theorem wt_ineq1 (c : Fin 8) : (wt c).1 ≤ (wt c).2 + 1 := by fin_cases c <;> decide
theorem wt_ineq2 (c : Fin 8) : (wt c).2 ≤ (wt c).1 + 1 := by fin_cases c <;> decide
theorem wt_lb2 (c : Fin 8) : -1 ≤ (wt c).2 := by fin_cases c <;> decide
theorem wt_lb1 (c : Fin 8) : -1 ≤ (wt c).1 := by fin_cases c <;> decide

theorem no_weight_f1 (m : ℕ) (t : Fin m → Fin 8) :
    ∑ i, wt (t i) ≠ m • wt 5 - (m + 1) • wt 3 := by
  intro h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [Prod.fst_sum, Prod.snd_sum, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, wt] at h1 h2
  simp at h1 h2
  have hle : ∑ i, (wt (t i)).1 ≤ ∑ i, ((wt (t i)).2 + 1) :=
    Finset.sum_le_sum fun i _ => wt_ineq1 (t i)
  rw [Finset.sum_add_distrib] at hle
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hle
  simp only [wt, smul_eq_mul, nsmul_eq_mul, mul_one] at hle h1 h2
  omega

theorem no_weight_f2 (m : ℕ) (t : Fin m → Fin 8) :
    ∑ i, wt (t i) ≠ m • wt 5 - (m + 1) • wt 4 := by
  intro h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [Prod.fst_sum, Prod.snd_sum, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, wt] at h1 h2
  simp at h1 h2
  have hle : ∑ i, (wt (t i)).2 ≤ ∑ i, ((wt (t i)).1 + 1) :=
    Finset.sum_le_sum fun i _ => wt_ineq2 (t i)
  rw [Finset.sum_add_distrib] at hle
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hle
  simp only [wt, smul_eq_mul, nsmul_eq_mul, mul_one] at hle h1 h2
  omega

/-! ## The relations on the fibre generator -/

/-- The fibre of `W_m` as an `sl₃[t]`-module. -/
abbrev fibRep (m : ℕ) := fiberRep bracketTable m relationsStable jacobiCoord

/-- The fibre generator, the class of `δ_{f₁₂}`. -/
abbrev wGen (m : ℕ) : Fib fullMatrix m := wF m (5 : Fin 8) fullMatrix_diag

theorem mk_eq_zero_of_mem_augT (m : ℕ) {v : TensorPolynomial (K := ℂ) (σ := Fin 8) m 0}
    (hv : v ∈ currentCarrier fullMatrix m 0) (ha : v ∈ augT fullMatrix m) :
    (Submodule.Quotient.mk ⟨v, hv⟩ : Fib fullMatrix m) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr ha

theorem opGen (m : ℕ) (x : Fin 8) (r : ℕ) :
    (fibRep m).op x r (wGen m) = Submodule.Quotient.mk
      ⟨loopOp bracketTable m x r (deltaVec m 5),
        loopOp_mem bracketTable relationsStable (deltaVec_mem 5 fullMatrix_diag) x r⟩ := rfl

theorem iterate_opGen (m k : ℕ) (x : Fin 8) :
    ((fibRep m).op x 0)^[k] (wGen m) = Submodule.Quotient.mk
      ⟨applyWord bracketTable m (List.replicate k (x, 0)) (deltaVec m 5),
        applyWord_mem bracketTable m relationsStable 5 fullMatrix_diag _⟩ := by
  rw [← wordOp_wF bracketTable m relationsStable jacobiCoord 5 fullMatrix_diag]
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, List.replicate_succ]
      rfl

/-- **The fibre generator satisfies the local Weyl and fusion relations for `mθ`.** -/
theorem localWeylRel (m : ℕ) : LocalWeylRel (fibRep m) (wGen m) m where
  raising e he r := by
    rw [opGen]
    apply mk_eq_zero_of_mem_augT
    rw [loopOp_raising_deltaVec m e he r]
    exact Submodule.zero_mem _
  cartan_pos h hh r hr := by
    rw [opGen]
    apply mk_eq_zero_of_mem_augT
    rw [loopOp_cartan_deltaVec m h hh r]
    exact Submodule.subset_span ⟨r, hr, psumS m r, psumS_mem m r, deltaVec m 5,
      deltaVec_mem 5 fullMatrix_diag, rfl⟩
  cartan_zero h hh := by
    rw [opGen]
    change _ = (m : ℂ) • Submodule.Quotient.mk _
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    apply Subtype.ext
    change loopOp bracketTable m h 0 (deltaVec m 5) = (m : ℂ) • deltaVec m 5
    rw [loopOp_cartan_deltaVec m h hh 0]
    funext t
    rw [SectorFiberModule.smul_apply_sym, Pi.smul_apply, smul_eq_C_mul]
    congr 1
    simp [psumS, psum]
  lowering_f1 := by
    rw [iterate_opGen]
    apply mk_eq_zero_of_mem_augT
    rw [applyWord_replicate, suppW_eq_zero (iterate_suppW m (m + 1) 3) (no_weight_f1 m)]
    exact Submodule.zero_mem _
  lowering_f2 := by
    rw [iterate_opGen]
    apply mk_eq_zero_of_mem_augT
    rw [applyWord_replicate, suppW_eq_zero (iterate_suppW m (m + 1) 4) (no_weight_f2 m)]
    exact Submodule.zero_mem _
  fusion fα _ _ := by
    rw [opGen]
    apply mk_eq_zero_of_mem_augT
    rw [loopOp_vieta]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_)
    exact Submodule.subset_span ⟨j, (Finset.mem_Ico.mp hj).1, esymmS m j, esymmS_mem m j, _,
      loopOp_mem bracketTable relationsStable (deltaVec_mem 5 fullMatrix_diag) fα (m - j), rfl⟩

end

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.jacobiCoord
#print axioms VOA.DeligneAudit.A2.localWeylRel
end AxiomAudit
