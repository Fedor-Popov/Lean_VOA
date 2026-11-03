/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LatticeTwistedProduct

/-!
# Translation covariance of the twisted exponential fields  (Moonshine step M6)

The derivative of `Y^T(e^α, z) = 2^{−⟨α,α⟩} z^{−⟨α,α⟩/2} E⁻(−α,z)E⁺(−α,z) ⊗ e_α` is
`∂Y^T(e^α) = :α(z) Y^T(e^α, z): − (⟨α,α⟩/2) z⁻¹ Y^T(e^α, z)`.  In the rescaled language this is

  `Dα (e/2) F_e(e^α) = F_e(T e^α) = Σ_b α_b · star ½ (Fgen_b) (−1) F_{e−1}(e^α)`   (`FL_T_echg`),

with `Dα c X = ∂X − c z⁻¹ X`.  The input is the **Euler identity of the dressing**
(`DD_euler`): `a · DD v a = 2 Σ_{k odd > 0} (v(−k/2) DD v (a−k) + DD v (a+k) v(k/2))`, the
coefficient form of `w ∂_w (E⁻E⁺) = (Σ 2 v(−k/2) wᵏ) E⁻E⁺ + E⁻E⁺ (Σ 2 v(k/2) w⁻ᵏ)`, assembled from
the Newton recursion of `E⁻` (`sMz_euler`) and the Euler identity of the translation `E⁺`
(`EpC_euler`).

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
-/

namespace VOA.Moonshine.LatticeTwisted

open MvPolynomial TwistedHeisenberg TwistedReduction HeisenbergN
open Module (End)
open scoped BigOperators TensorProduct

section Euler

variable {r : ℕ}

theorem oscT_creation (v : Fin r → ℂ) (n : ℕ) (y : FockT r) :
    oscT v (-(2 * n + 1)) y = vVarT v n * y := by
  rw [oscT, LinearMap.sum_apply, vVarT, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, modeT_creation, smul_mul_assoc]

theorem oscT_annihilation (v : Fin r → ℂ) (n : ℕ) (y : FockT r) :
    oscT v (2 * n + 1) y = (((2 * n + 1 : ℤ) : ℂ) / 2) • ∑ i, v i • pderiv (n, i) y := by
  rw [oscT, LinearMap.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, modeT_annihilation, smul_comm]

/-- **The Newton recursion of `E⁻`**: `p · E⁻_p = Σ_n 2 v(−n−½) E⁻_{p−(2n+1)}`. -/
theorem sMz_euler (v : Fin r → ℂ) (p : ℤ) (P : ℕ) (hP : p ≤ 2 * P) :
    (p : ℂ) • sMz v p = ∑ n ∈ Finset.range P, (2 : ℂ) • (vVarT v n * sMz v (p - (2 * n + 1))) := by
  by_cases hp : p ≤ 0
  · rcases eq_or_lt_of_le hp with h0 | hneg
    · subst h0
      rw [Int.cast_zero, zero_smul]
      refine (Finset.sum_eq_zero fun n _ => ?_).symm
      rw [sMz_of_neg v (by omega), mul_zero, smul_zero]
    · rw [sMz_of_neg v hneg, smul_zero]
      refine (Finset.sum_eq_zero fun n _ => ?_).symm
      rw [sMz_of_neg v (by omega), mul_zero, smul_zero]
  obtain ⟨q, hq⟩ : ∃ q : ℕ, p = q + 1 := ⟨(p - 1).toNat, by omega⟩
  subst hq
  rw [show ((q : ℤ) + 1) = ((q + 1 : ℕ) : ℤ) by push_cast; ring, sMz_natCast]
  have h := nexp_rec (dM v) q
  rw [show ((q : ℂ) + 1) = (((q + 1 : ℕ) : ℤ) : ℂ) by push_cast; ring] at h
  change (((q + 1 : ℕ) : ℤ) : ℂ) • sM v (q + 1) = _ at h
  rw [h]
  -- reindex: `k + 1 = 2n + 1` odd
  have hterm : ∀ k ∈ Finset.range (q + 1), dM v (k + 1) * nexp (dM v) (q - k)
      = if k % 2 = 0 then (2 : ℂ) • (vVarT v (k / 2) * sMz v ((q + 1 : ℕ) - (2 * (k / 2 : ℕ) + 1)))
        else 0 := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [dM]
    split_ifs with h1 h2 h2
    · rw [show (k + 1) / 2 = k / 2 by omega, smul_mul_assoc,
        show ((q + 1 : ℕ) : ℤ) - (2 * ((k / 2 : ℕ) : ℤ) + 1) = ((q - k : ℕ) : ℤ) by omega,
        sMz_natCast]
      rfl
    · omega
    · omega
    · rw [zero_mul]
  rw [Finset.sum_congr rfl hterm]
  -- both sides are sums over the odd numbers `2n + 1 ≤ q + 1`
  rw [← Finset.sum_filter]
  symm
  rw [Finset.sum_range_eq_of_vanish' (q / 2 + 1) P (by omega) (fun n hn1 hn2 => by
    rw [sMz_of_neg v (by push_cast; omega), mul_zero, smul_zero])]
  refine Finset.sum_bij (fun n _ => 2 * n) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_range] at hn
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  · intro a _ b _ h
    simp only at h
    omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    exact ⟨k / 2, by simp only [Finset.mem_range]; omega, by simp only; omega⟩
  · intro n _
    rw [show 2 * n / 2 = n by omega]

/-- The summand of the Euler identity of `E⁺`. -/
noncomputable def epcTerm (v : Fin r → ℂ) (q : ℕ) (y : FockT r) (x : ℕ × Fin r) : FockT r :=
  if 2 * x.1 + 1 ≤ q then ((2 * x.1 + 1 : ℂ) * v x.2) • EpC v (q - (2 * x.1 + 1)) (pderiv x y)
  else 0

/-- The box of variables `(n, i)` with `n < Q`. -/
def boxV (r Q : ℕ) : Finset (ℕ × Fin r) := Finset.range Q ×ˢ Finset.univ

theorem epcTerm_add (v : Fin r → ℂ) (q : ℕ) (a b : FockT r) (x : ℕ × Fin r) :
    epcTerm v q (a + b) x = epcTerm v q a x + epcTerm v q b x := by
  unfold epcTerm; split_ifs <;> simp [map_add, smul_add]

/-- **The Euler identity of `E⁺`**: `q · E⁺_q y = −Σ_{(n,i)} (2n+1) vᵢ E⁺_{q−(2n+1)} ∂_{(n,i)} y`. -/
theorem EpC_euler (v : Fin r → ℂ) (y : FockT r) :
    ∀ (q Q : ℕ), q ≤ Q → (q : ℂ) • EpC v q y = -∑ x ∈ boxV r Q, epcTerm v q y x := by
  induction y using MvPolynomial.induction_on with
  | C c =>
      intro q Q _
      rw [EpC_C]
      have h0 : ∀ x ∈ boxV r Q, epcTerm v q (MvPolynomial.C c) x = 0 := fun x _ => by
        unfold epcTerm; split_ifs <;> simp
      rw [Finset.sum_eq_zero h0, neg_zero]
      split_ifs with h
      · subst h; simp
      · rw [smul_zero]
  | add a b ha hb =>
      intro q Q hq
      rw [map_add, smul_add, ha q Q hq, hb q Q hq]
      simp only [epcTerm_add, Finset.sum_add_distrib, neg_add]
  | mul_X a x0 ha =>
      intro q Q hq
      set k0 := 2 * x0.1 + 1 with hk0
      have hsplit : ∀ x ∈ boxV r Q, epcTerm v q (a * X x0) x
          = epcTerm v q a x * X x0
            - (if 2 * x.1 + 1 + k0 ≤ q then
                (v x0.2 * ((2 * x.1 + 1 : ℂ) * v x.2)) •
                  EpC v (q - k0 - (2 * x.1 + 1)) (pderiv x a) else 0)
            + (if x = x0 ∧ k0 ≤ q then ((k0 : ℂ) * v x0.2) • EpC v (q - k0) a else 0) := by
        intro x _
        have hl : pderiv x (a * X x0) = pderiv x a * X x0 + (if x = x0 then a else 0) := by
          rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]
          by_cases hxx : x = x0
          · subst hxx; rw [Pi.single_eq_same, if_pos rfl, mul_one, mul_comm, add_comm]
          · rw [Pi.single_eq_of_ne (Ne.symm hxx), if_neg hxx, mul_zero, zero_add, mul_comm,
              add_zero]
        unfold epcTerm
        rw [hl, map_add]
        by_cases hx : 2 * x.1 + 1 ≤ q
        · rw [if_pos hx, if_pos hx, EpC_mul_X, smul_add, smul_sub, smul_mul_assoc]
          congr 1
          · congr 1
            split_ifs with h1 h2 h2
            · rw [smul_smul, show q - (2 * x.1 + 1) - (2 * x0.1 + 1) = q - k0 - (2 * x.1 + 1) by
                omega]
              ring_nf
            · omega
            · omega
            · rw [smul_zero]
          · by_cases hxx : x = x0
            · subst hxx
              rw [if_pos rfl, if_pos ⟨rfl, hx⟩, hk0]
              push_cast
              rfl
            · rw [if_neg hxx, map_zero, smul_zero, if_neg (by tauto)]
        · rw [if_neg hx, if_neg hx, if_neg (by omega), zero_mul, sub_zero, zero_add]
          by_cases hxx : x = x0
          · rw [if_neg (by rintro ⟨-, h⟩; subst hxx; omega)]
          · rw [if_neg (by tauto)]
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_mul]
      -- the `x = x0` term
      have hx0 : ∑ x ∈ boxV r Q, (if x = x0 ∧ k0 ≤ q then ((k0 : ℂ) * v x0.2) • EpC v (q - k0) a
          else 0) = if k0 ≤ q then ((k0 : ℂ) * v x0.2) • EpC v (q - k0) a else 0 := by
        split_ifs with hk
        · rw [Finset.sum_eq_single x0 (fun x _ hx => by rw [if_neg (by tauto)])
            (fun h => absurd (by simp [boxV]; omega) h), if_pos ⟨rfl, hk⟩]
        · exact Finset.sum_eq_zero fun x _ => by rw [if_neg (by tauto)]
      -- the shifted sum is the Euler sum at `q − k0`
      have hshift : ∑ x ∈ boxV r Q, (if 2 * x.1 + 1 + k0 ≤ q then
            (v x0.2 * ((2 * x.1 + 1 : ℂ) * v x.2)) •
              EpC v (q - k0 - (2 * x.1 + 1)) (pderiv x a) else 0)
          = if k0 ≤ q then v x0.2 • ∑ x ∈ boxV r Q, epcTerm v (q - k0) a x else 0 := by
        split_ifs with hk
        · rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          unfold epcTerm
          split_ifs with h1 h2 h2
          · rw [smul_smul]
          · omega
          · omega
          · rw [smul_zero]
        · exact Finset.sum_eq_zero fun x _ => by rw [if_neg (by omega)]
      rw [hx0, hshift, show ∑ x ∈ boxV r Q, epcTerm v q a x = -((q : ℂ) • EpC v q a) by
        rw [ha q Q hq, neg_neg], EpC_mul_X]
      split_ifs with hk
      · rw [show ∑ x ∈ boxV r Q, epcTerm v (q - k0) a x = -(((q - k0 : ℕ) : ℂ) • EpC v (q - k0) a) by
          rw [ha (q - k0) Q (by omega), neg_neg]]
        simp only [hk0]
        rw [Nat.cast_sub hk]
        simp only [smul_sub, neg_mul, smul_mul_assoc]
        push_cast
        module
      · simp only [sub_zero, add_zero, neg_mul, smul_mul_assoc, neg_neg]

theorem exists_pderiv_bound (y : FockT r) : ∃ V : ℕ, ∀ x : ℕ × Fin r, V ≤ x.1 → pderiv x y = 0 := by
  classical
  refine ⟨y.vars.sup (fun x => x.1 + 1), fun x hx => pderiv_eq_zero_of_notMem_vars fun hm => ?_⟩
  have := Finset.le_sup (f := fun x : ℕ × Fin r => x.1 + 1) hm
  simp only at this
  omega

/-- **The Euler identity of the dressing**:
`a · DD v a y = 2 Σ_n v(−n−½) DD v (a−(2n+1)) y + 2 Σ_n DD v (a+2n+1) (v(n+½) y)`. -/
theorem DD_euler (v : Fin r → ℂ) (a : ℤ) (y : FockT r) (P : ℕ)
    (hP1 : ∀ n : ℕ, P ≤ n → DD v (a - (2 * n + 1)) y = 0)
    (hP2 : ∀ n : ℕ, P ≤ n → oscT v (2 * n + 1) y = 0) :
    (a : ℂ) • DD v a y
      = ∑ n ∈ Finset.range P, (2 : ℂ) • (vVarT v n * DD v (a - (2 * n + 1)) y)
        + ∑ n ∈ Finset.range P, (2 : ℂ) • DD v (a + (2 * n + 1)) (oscT v (2 * n + 1) y) := by
  obtain ⟨Q, hQ⟩ := EpC_eventually_zero v y
  obtain ⟨V, hV⟩ := exists_pderiv_bound y
  set Q' : ℕ := Q + 2 * V + 2 * P + 1 + (a.natAbs) with hQ'
  have hQd : ∀ (x : ℕ × Fin r) (q : ℕ), Q ≤ q → EpC v q (pderiv x y) = 0 := fun x q hq => by
    rw [← pderiv_EpC, hQ q hq, map_zero]
  rw [DD_apply_range v a y Q' (fun q hq => hQ q (by omega))]
  -- split `a = (a + q) − q`
  have hsplit : ∀ q ∈ Finset.range Q', (a : ℂ) • (sMz v (a + q) * EpC v q y)
      = ((a + q : ℤ) : ℂ) • sMz v (a + q) * EpC v q y - sMz v (a + q) * ((q : ℂ) • EpC v q y) := by
    intro q _
    rw [smul_mul_assoc, mul_smul_comm, ← sub_smul]
    push_cast
    ring_nf
  rw [Finset.smul_sum, Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, sub_eq_add_neg]
  congr 1
  · -- the `E⁻` part
    set P' : ℕ := P + Q' + a.natAbs with hP'
    have h1 : ∀ q ∈ Finset.range Q', ((a + q : ℤ) : ℂ) • sMz v (a + q) * EpC v q y
        = ∑ n ∈ Finset.range P', (2 : ℂ) • (vVarT v n * (sMz v (a + q - (2 * n + 1)) * EpC v q y)) := by
      intro q hq
      rw [Finset.mem_range] at hq
      rw [sMz_euler v (a + q) P' (by omega), Finset.sum_mul]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [smul_mul_assoc, mul_assoc]
    have hDD : ∀ n : ℕ, ∑ q ∈ Finset.range Q', sMz v (a + q - (2 * n + 1)) * EpC v q y
        = DD v (a - (2 * n + 1)) y := by
      intro n
      rw [DD_apply_range v _ y Q' (fun q hq => hQ q (by omega))]
      exact Finset.sum_congr rfl fun q _ => by rw [show a + q - (2 * n + 1) = a - (2 * n + 1) + q by
        ring]
    have hvan : ∀ n : ℕ, P ≤ n → ∑ q ∈ Finset.range Q',
        (2 : ℂ) • (vVarT v n * (sMz v (a + q - (2 * n + 1)) * EpC v q y)) = 0 := by
      intro n hn
      rw [← Finset.smul_sum, ← Finset.mul_sum, hDD, hP1 n hn, mul_zero, smul_zero]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm,
      Finset.sum_range_eq_of_vanish' P P' (by omega) (fun n _ hn => hvan n hn)]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.smul_sum, ← Finset.mul_sum, hDD]
  · -- the `E⁺` part
    have h2 : ∀ q ∈ Finset.range Q', -(sMz v (a + q) * ((q : ℂ) • EpC v q y))
        = ∑ x ∈ boxV r Q', sMz v (a + q) * epcTerm v q y x := by
      intro q hq
      rw [Finset.mem_range] at hq
      rw [EpC_euler v y q Q' hq.le, mul_neg, neg_neg, Finset.mul_sum]
    rw [← Finset.sum_neg_distrib, Finset.sum_congr rfl h2, Finset.sum_comm]
    have hx : ∀ x ∈ boxV r Q', ∑ q ∈ Finset.range Q', sMz v (a + q) * epcTerm v q y x
        = ((2 * x.1 + 1 : ℂ) * v x.2) • DD v (a + (2 * x.1 + 1)) (pderiv x y) := by
      intro x _
      by_cases hxV : V ≤ x.1
      · rw [hV x hxV, map_zero, smul_zero]
        refine Finset.sum_eq_zero fun q _ => ?_
        unfold epcTerm
        split_ifs <;> simp [hV x hxV]
      rw [sum_range_shift _ (2 * x.1 + 1) Q' (fun q hq => by
          unfold epcTerm; rw [if_neg (by omega), mul_zero])
        (fun i' hi' => by
          unfold epcTerm
          rw [if_pos (by omega), Nat.add_sub_cancel_left, hQd x i' (by omega), smul_zero,
            mul_zero]),
        DD_apply_range v _ _ Q' (fun q hq => hQd x q (by omega)), Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      unfold epcTerm
      rw [if_pos (by omega), Nat.add_sub_cancel_left, mul_smul_comm]
      congr 2
      push_cast
      ring_nf
    rw [Finset.sum_congr rfl hx, boxV, Finset.sum_product]
    have hn : ∀ n ∈ Finset.range Q', ∑ i : Fin r, ((2 * ((n, i) : ℕ × Fin r).1 + 1 : ℂ) *
          v ((n, i) : ℕ × Fin r).2) • DD v (a + (2 * ((n, i) : ℕ × Fin r).1 + 1))
            (pderiv ((n, i) : ℕ × Fin r) y)
        = (2 : ℂ) • DD v (a + (2 * n + 1)) (oscT v (2 * n + 1) y) := by
      intro n _
      rw [oscT_annihilation, map_smul, map_sum, smul_smul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_smul]
      push_cast
      congr 1
      ring
    rw [Finset.sum_congr rfl hn, Finset.sum_range_eq_of_vanish' P Q' (by omega) (fun n _ hnP => by
      rw [hP2 n hnP, map_zero, smul_zero])]

end Euler

/-! ## The normal-ordered product -/

section NormalOrdered

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem gBinom_neg_one (i : ℕ) : gBinom (-1) i = (-1 : ℂ) ^ i := by
  rw [gBinom]
  have hf : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  rw [div_eq_iff hf]
  induction i with
  | zero => simp
  | succ i ih =>
      rw [Finset.prod_range_succ, ih (by exact_mod_cast Nat.factorial_ne_zero i),
        Nat.factorial_succ]
      push_cast
      ring

/-- The `(−1)`-st product (normal-ordered product) in modes:
`(A₍₋₁₎B)_N x = Σᶠ_i (A_{−1−i} B_{N+i} x + B_{N−1−i} A_i x)`. -/
theorem mode_prod_neg_one (A B : Fld M) (N : ℤ) (x : M) :
    mode (Fld.prod (-1) A B).1 N x
      = ∑ᶠ i : ℕ, (mode A.1 (-1 - i) (mode B.1 (N + i) x) + mode B.1 (N - 1 - i) (mode A.1 i x)) := by
  rw [Fld.mode_prod_iterate]
  refine finsum_congr fun i => ?_
  rw [gBinom_neg_one, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul,
    show (-1 : ℂ) ^ (-1 : ℤ) = -1 by norm_num, neg_one_smul, sub_neg_eq_add,
    show -1 + N - (i : ℤ) = N - 1 - i by ring]

end NormalOrdered

/-! ## Translation covariance of `Y^T(e^α)` -/

section Lattice

open IntegralLattice LatGen Extraspecial

variable (L : IntegralLattice) (hEven : L.Even) (hU : IsUnit (gramMat L).det) (hPos : L.PosDef)

theorem mode_FgT (b : Fin (rank L)) (m : ℤ) :
    mode (FgT (Tm := Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) b).1 m
      = (modeT (rank L) b (2 * m + 1)).rTensor _ := by
  rw [FgT_val, FgenT, mode_resc]
  push_cast
  rfl

theorem mode_YTLFld (α : L.carrier) (e m : ℤ) :
    mode (YTLFld L hEven hU α e).1 m = YTL L hEven hU α (2 * m + e) := by
  change mode (resc (YTL L hEven hU α) 2 e) m = _
  rw [mode_resc]
  push_cast
  rfl

theorem YTL_tmul (α : L.carrier) (k : ℤ) (y : FockT (rank L))
    (t : Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) :
    YTL L hEven hU α k (y ⊗ₜ[ℂ] t)
      = ((2 : ℂ) ^ (-(L.form α α))) • (DD (chargeCoord L α) (-k - 2 + L.form α α) y
          ⊗ₜ[ℂ] eT L hEven hU α t) :=
  YTg_tmul _ _ _ _ _ _ _

include hPos in
/-- **Translation covariance of the twisted exponential field**:
`∂F_e(e^α) − (e/2) z⁻¹ F_e(e^α) = Σ_b α_b · star ½ (Fgen_b) (−1) F_{e−1}(e^α)`. -/
theorem YTLFld_translation (α : L.carrier) (e : ℤ) :
    Dα ((e : ℂ) / 2) (YTLFld L hEven hU α e)
      = ∑ b, chargeCoord L α b • star (1 / 2) (FgT b) (-1) (YTLFld L hEven hU α (e - 1)) := by
  -- the twisted product with the generator
  have hstar : ∀ b, star (1 / 2) (FgT b) (-1) (YTLFld L hEven hU α (e - 1))
      = Fld.prod (-1) (FgT b) (YTLFld L hEven hU α (e - 1))
        + (-(1 / 2 : ℂ) * chargeCoord L α b) • fzmul (-1) (YTLFld L hEven hU α e) := by
    intro b
    rw [star_eq_sum_range _ _ _ _ 2 (fun i hi => by
      rw [← FgenTFld_eq_FgT]; exact prod_FgenTFld_YTLFld_pos L hEven hU b α _ (by omega)),
      Finset.sum_range_succ, Finset.sum_range_one]
    simp only [Nat.cast_zero, add_zero, cbinom_zero, one_smul, neg_zero, fzmul_zero_shift,
      Nat.cast_one]
    rw [show (-1 : ℤ) + 1 = 0 by norm_num, ← FgenTFld_eq_FgT, prod_FgenTFld_YTLFld_zero,
      FgenTFld_eq_FgT, show e - 1 + 1 = e by ring, fzmul_smul, smul_smul,
      show cbinom (-(1 / 2)) 1 = -(1 / 2) by simp [cbinom]]
  simp only [hstar, smul_add, Finset.sum_add_distrib]
  apply fld_ext_mode
  intro p x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x₁ x₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | tmul y t =>
      obtain ⟨Q, hQ⟩ := EpC_eventually_zero (chargeCoord L α) y
      obtain ⟨V, hV⟩ := exists_pderiv_bound y
      obtain ⟨a, ha⟩ : ∃ a : ℤ, a = L.form α α - 2 * p - e := ⟨_, rfl⟩
      obtain ⟨P, hP⟩ : ∃ P : ℕ, P = V + (a + Q).toNat + 1 := ⟨_, rfl⟩
      have hP1 : ∀ n : ℕ, P ≤ n → DD (chargeCoord L α) (a - (2 * n + 1)) y = 0 := fun n hn =>
        DD_eq_zero_of_le _ y hQ (by omega)
      have hP2 : ∀ n : ℕ, P ≤ n → oscT (chargeCoord L α) (2 * n + 1) y = 0 := fun n hn => by
        rw [oscT_annihilation]
        rw [Finset.sum_eq_zero fun i _ => by rw [hV (n, i) (by simp; omega), smul_zero], smul_zero]
      have hE := DD_euler (chargeCoord L α) a y P hP1 hP2
      -- the left side
      have hL : mode (Dα ((e : ℂ) / 2) (YTLFld L hEven hU α e)).1 p (y ⊗ₜ[ℂ] t)
          = (-(p : ℂ) - (e : ℂ) / 2) • ((2 : ℂ) ^ (-(L.form α α)) •
              (DD (chargeCoord L α) a y ⊗ₜ[ℂ] eT L hEven hU α t)) := by
        rw [Dα, mode_fld_sub, mode_fld_smul, mode_fld_deriv, fzmul_val, mode_zmul,
          show p + -1 = p - 1 by ring, mode_YTLFld, YTL_tmul,
          show -(2 * (p - 1) + e) - 2 + L.form α α = a by rw [ha]; ring, sub_smul]
      -- the normal-ordered part
      have hterm : ∀ (b : Fin (rank L)) (n : ℕ),
          mode (FgT b).1 (-1 - n) (mode (YTLFld L hEven hU α (e - 1)).1 (p + n) (y ⊗ₜ[ℂ] t))
            + mode (YTLFld L hEven hU α (e - 1)).1 (p - 1 - n) (mode (FgT b).1 n (y ⊗ₜ[ℂ] t))
          = (2 : ℂ) ^ (-(L.form α α)) • ((modeT (rank L) b (-(2 * n + 1))
              (DD (chargeCoord L α) (a - (2 * n + 1)) y)
              + DD (chargeCoord L α) (a + (2 * n + 1)) (modeT (rank L) b (2 * n + 1) y))
                ⊗ₜ[ℂ] eT L hEven hU α t) := by
        intro b n
        rw [mode_YTLFld, YTL_tmul, mode_FgT L hEven hU, mode_FgT L hEven hU, map_smul,
          LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, mode_YTLFld, YTL_tmul,
          show -(2 * (p + n) + (e - 1)) - 2 + L.form α α = a - (2 * n + 1) by rw [ha]; ring,
          show -(2 * (p - 1 - n) + (e - 1)) - 2 + L.form α α = a + (2 * n + 1) by rw [ha]; ring,
          show 2 * (-1 - (n : ℤ)) + 1 = -(2 * n + 1) by ring, ← smul_add,
          ← TensorProduct.add_tmul]
      have hN : ∀ b, mode (Fld.prod (-1) (FgT b) (YTLFld L hEven hU α (e - 1))).1 p (y ⊗ₜ[ℂ] t)
          = ∑ n ∈ Finset.range P, (2 : ℂ) ^ (-(L.form α α)) • ((modeT (rank L) b (-(2 * n + 1))
              (DD (chargeCoord L α) (a - (2 * n + 1)) y)
              + DD (chargeCoord L α) (a + (2 * n + 1)) (modeT (rank L) b (2 * n + 1) y))
                ⊗ₜ[ℂ] eT L hEven hU α t) := by
        intro b
        rw [mode_prod_neg_one, finsum_eq_sum_of_support_subset _ (s := Finset.range P) (by
          intro n hn
          rw [Function.mem_support] at hn
          by_contra hc
          rw [Finset.coe_range, Set.mem_Iio, not_lt] at hc
          apply hn
          rw [hterm, hP1 n hc, map_zero, zero_add, modeT_annihilation,
            hV (n, b) (by simp; omega), smul_zero, map_zero, TensorProduct.zero_tmul, smul_zero])]
        exact Finset.sum_congr rfl fun n _ => hterm b n
      rw [hL, mode_fld_add, mode_fld_sum, mode_fld_sum]
      simp only [mode_fld_smul, hN, fzmul_val, mode_zmul,
        show p + -1 = p - 1 by ring, mode_YTLFld, YTL_tmul,
        show -(2 * (p - 1) + e) - 2 + L.form α α = a by rw [ha]; ring]
      -- the oscillator sums
      have hosc : ∀ (K : ℤ) (z : FockT (rank L)),
          ∑ b, chargeCoord L α b • modeT (rank L) b K z = oscT (chargeCoord L α) K z := by
        intro K z
        rw [oscT, LinearMap.sum_apply]
        rfl
      have h1n : ∀ n : ℕ, ∑ b, chargeCoord L α b • ((2 : ℂ) ^ (-(L.form α α)) •
            ((modeT (rank L) b (-(2 * n + 1)) (DD (chargeCoord L α) (a - (2 * n + 1)) y)
              + DD (chargeCoord L α) (a + (2 * n + 1)) (modeT (rank L) b (2 * n + 1) y))
                ⊗ₜ[ℂ] eT L hEven hU α t))
          = (2 : ℂ) ^ (-(L.form α α)) • ((vVarT (chargeCoord L α) n
              * DD (chargeCoord L α) (a - (2 * n + 1)) y
                + DD (chargeCoord L α) (a + (2 * n + 1)) (oscT (chargeCoord L α) (2 * n + 1) y))
                  ⊗ₜ[ℂ] eT L hEven hU α t) := by
        intro n
        have hgen : ∀ (F : Fin (rank L) → FockT (rank L)),
            ∑ b, chargeCoord L α b • ((2 : ℂ) ^ (-(L.form α α)) • (F b ⊗ₜ[ℂ] eT L hEven hU α t))
              = (2 : ℂ) ^ (-(L.form α α)) • ((∑ b, chargeCoord L α b • F b)
                  ⊗ₜ[ℂ] eT L hEven hU α t) := by
          intro F
          rw [TensorProduct.sum_tmul, Finset.smul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_comm,
            ← TensorProduct.smul_tmul']
        rw [hgen]
        congr 2
        rw [← oscT_creation, ← hosc, ← hosc, map_sum]
        simp only [smul_add, Finset.sum_add_distrib, map_smul]
      have h1 : ∑ b, chargeCoord L α b • ∑ n ∈ Finset.range P, (2 : ℂ) ^ (-(L.form α α)) •
            ((modeT (rank L) b (-(2 * n + 1)) (DD (chargeCoord L α) (a - (2 * n + 1)) y)
              + DD (chargeCoord L α) (a + (2 * n + 1)) (modeT (rank L) b (2 * n + 1) y))
                ⊗ₜ[ℂ] eT L hEven hU α t)
          = (2 : ℂ) ^ (-(L.form α α)) • (((a : ℂ) / 2) • DD (chargeCoord L α) a y
              ⊗ₜ[ℂ] eT L hEven hU α t) := by
        simp only [Finset.smul_sum]
        rw [Finset.sum_comm, Finset.sum_congr rfl fun n _ => h1n n, ← Finset.smul_sum,
          ← TensorProduct.sum_tmul]
        congr 2
        rw [Finset.sum_add_distrib]
        have := congrArg (fun z => (1 / 2 : ℂ) • z) hE
        simp only [smul_add, Finset.smul_sum, smul_smul] at this
        rw [show (1 / 2 : ℂ) * (a : ℂ) = (a : ℂ) / 2 by ring] at this
        rw [this]
        norm_num
      have h2 : ∑ b, chargeCoord L α b • (-(1 / 2 : ℂ) * chargeCoord L α b) •
            (2 : ℂ) ^ (-(L.form α α)) • (DD (chargeCoord L α) a y ⊗ₜ[ℂ] eT L hEven hU α t)
          = (-(1 / 2 : ℂ) * (L.form α α : ℂ)) • (2 : ℂ) ^ (-(L.form α α)) •
              (DD (chargeCoord L α) a y ⊗ₜ[ℂ] eT L hEven hU α t) := by
        simp only [smul_smul, ← Finset.sum_smul]
        congr 1
        rw [← sum_chargeCoord L hPos α α, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ => by ring
      rw [h1, h2, ha]
      push_cast
      module

include hPos in
/-- **Translation covariance at the exponentials**: `F_e(T e^α) = Dα (e/2) F_e(e^α)`. -/
theorem FL_T_echg (e : ℤ) (α : L.carrier) :
    FL L hEven hU e ((latticeVOAGen L hEven hPos).toPreVertexAlgebra.T (echg L α))
      = Dα ((e : ℂ) / 2) (FL L hEven hU e (echg L α)) := by
  rw [T_echg, map_sum, FL_echg L hEven hU hPos, YTLFld_translation L hEven hU hPos]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, show e = e - 1 + 1 by ring,
    show (-1 : ℤ) = -((0 : ℕ) : ℤ) - 1 by norm_num, FL_smul_hgen_neg L hEven hU hPos,
    FL_echg L hEven hU hPos, show e - 1 + 1 - 1 = e - 1 by ring]

end Lattice

end VOA.Moonshine.LatticeTwisted
