/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LatticeTwistedEOps
import Mathlib.Data.Int.Interval

/-!
# The two-point function of twisted lattice vertex operators and their locality  (Moonshine step M6c)

For charge vectors `v, u` with `⟨v, u⟩ = n ∈ ℤ`, the dressings `DD v a` (coefficient of `wᵃ` in
`E⁻(−v,w)E⁺(−v,w)`, `LatticeTwistedEOps`) satisfy

  `DD v A ∘ DD u B = Σ_j fco(n)_j · NN(A + j, B − j)`        (`DD_DD_eq`)

where `NN` is the normal-ordered product `E⁻(−v)E⁻(−u)E⁺(−v)E⁺(−u)`, symmetric under
`(v, A) ↔ (u, B)` (`NN_symm`), and `fco(n)` are the coefficients of `((1 − x)/(1 + x))ⁿ`.
Hence, for `N ≥ |n|` (`DD_bracket_local`):

  `Σ_{r ≤ N} (−1)^{N−r} C(N,r) [DD v (A − 2r) DD u (B − 2(N−r))
      − (−1)ⁿ DD u (B − 2(N−r)) DD v (A − 2r)] = 0`,

the coefficient form of `(w₁² − w₂²)ᴺ (Y_v(w₁) Y_u(w₂) − (−1)ⁿ Y_u(w₂) Y_v(w₁)) = 0`, i.e. of
`(z₁ − z₂)ᴺ`-locality up to the sign `(−1)ⁿ` that the extraspecial factor `T` cancels.  The
proof regroups both sides as `Σ_t h(t) φ(t)` with `φ(t) = NN(A − 2N + t, B − t)` and applies the
palindromic identity `LatticeTwistedExp.sum_binom_fz_symm`.

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
-/

namespace VOA.Moonshine.LatticeTwisted

open MvPolynomial TwistedHeisenberg
open Module (End)
open scoped BigOperators

variable {r : ℕ}

/-! ## Good bounds -/

/-- `Q` bounds all `E⁺` coefficients relevant for the pair `(v, u)` on `x`. -/
def GoodB (v u : Fin r → ℂ) (x : FockT r) (Q : ℕ) : Prop :=
  (∀ q, Q ≤ q → EpC v q x = 0) ∧ (∀ q, Q ≤ q → EpC u q x = 0) ∧
    (∀ q q', Q ≤ q → EpC v q (EpC u q' x) = 0) ∧ (∀ q q', Q ≤ q' → EpC v q (EpC u q' x) = 0)

theorem GoodB.symm {v u : Fin r → ℂ} {x : FockT r} {Q : ℕ} (h : GoodB v u x Q) :
    GoodB u v x Q :=
  ⟨h.2.1, h.1, fun q q' hq => by rw [← EpC_comm]; exact h.2.2.2 q' q hq,
    fun q q' hq' => by rw [← EpC_comm]; exact h.2.2.1 q' q hq'⟩

theorem exists_goodB (v u : Fin r → ℂ) (x : FockT r) : ∃ Q, GoodB v u x Q := by
  obtain ⟨Q0, hQ0⟩ := EpC_eventually_zero u x
  obtain ⟨Qv, hQv⟩ := EpC_eventually_zero v x
  set B : ℕ → ℕ := fun q' => (Ep v (EpC u q' x)).natDegree + 1 with hB
  refine ⟨Q0 + Qv + ∑ q' ∈ Finset.range Q0, B q', fun q hq => hQv q (by omega),
    fun q hq => hQ0 q (by omega), fun q q' hq => ?_, fun q q' hq' => ?_⟩
  · by_cases hq' : q' < Q0
    · have hle : B q' ≤ ∑ q' ∈ Finset.range Q0, B q' :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hq')
      rw [EpC_apply]
      have hBq : B q' = (Ep v (EpC u q' x)).natDegree + 1 := rfl
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    · rw [hQ0 q' (by omega), map_zero]
  · rw [hQ0 q' (by omega), map_zero]

/-! ## The normal-ordered product -/

/-- The normal-ordered product `E⁻(−v)E⁻(−u)E⁺(−v)E⁺(−u)` at `w₁ᴬ w₂ᴮ`, with bound `Q`. -/
noncomputable def NN (v u : Fin r → ℂ) (Q : ℕ) (A B : ℤ) (x : FockT r) : FockT r :=
  ∑ q ∈ Finset.range Q, ∑ q' ∈ Finset.range Q,
    sMz v (A + q) * sMz u (B + q') * EpC v q (EpC u q' x)

theorem NN_symm (v u : Fin r → ℂ) (Q : ℕ) (A B : ℤ) (x : FockT r) :
    NN v u Q A B x = NN u v Q B A x := by
  unfold NN
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ => ?_
  rw [EpC_comm, mul_comm (sMz v _)]

theorem NN_eq_zero_right (v u : Fin r → ℂ) (Q : ℕ) (A B : ℤ) (x : FockT r) (h : B + Q ≤ 0) :
    NN v u Q A B x = 0 := by
  unfold NN
  refine Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun q' hq' => ?_
  rw [Finset.mem_range] at hq'
  rw [sMz_of_neg u (by omega), mul_zero, zero_mul]

theorem NN_eq_zero_left (v u : Fin r → ℂ) (Q : ℕ) (A B : ℤ) (x : FockT r) (h : A + Q ≤ 0) :
    NN v u Q A B x = 0 := by
  rw [NN_symm]; exact NN_eq_zero_right u v Q B A x h

/-! ## The two-point function -/

/-- One `E⁻` factor pushed through a dressing. -/
theorem DD_sMz_mul (v u : Fin r → ℂ) (A p : ℤ) (y : FockT r) (Q : ℕ)
    (hy : ∀ q, Q ≤ q → EpC v q y = 0) (J : ℕ) (hJ : p < J) :
    DD v A (sMz u p * y) = ∑ j ∈ Finset.range J, fco (pair v u) j •
      ∑ m ∈ Finset.range Q, sMz v (A + j + m) * (sMz u (p - j) * EpC v m y) := by
  set F : ℕ → ℕ → FockT r := fun j m =>
    fco (pair v u) j • (sMz v (A + j + m) * (sMz u (p - j) * EpC v m y)) with hF
  have hF0 : ∀ j m, J ≤ j → F j m = 0 := fun j m hj => by
    simp only [hF]; rw [sMz_of_neg u (by omega), zero_mul, mul_zero, smul_zero]
  have hF1 : ∀ j m, Q ≤ m → F j m = 0 := fun j m hm => by
    simp only [hF]; rw [hy m hm, mul_zero, mul_zero, smul_zero]
  have hQ2 : ∀ q, Q + J ≤ q → EpC v q (sMz u p * y) = 0 := by
    intro q hq
    rw [EpC_sMz_mul]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_range] at hj
    by_cases hjq : Q ≤ q - j
    · rw [hy _ hjq, mul_zero, smul_zero]
    · rw [sMz_of_neg u (by omega), zero_mul, smul_zero]
  rw [DD_apply_range v A _ (Q + J) hQ2]
  have h1 : ∀ q ∈ Finset.range (Q + J), sMz v (A + q) * EpC v q (sMz u p * y)
      = ∑ j ∈ Finset.range (q + 1), F j (q - j) := by
    intro q _
    rw [EpC_sMz_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    simp only [hF]
    rw [mul_smul_comm, show A + ((j : ℕ) : ℤ) + ((q - j : ℕ) : ℤ) = A + q by omega]
  rw [Finset.sum_congr rfl h1, Finset.sum_range_diag_flip]
  rw [Finset.sum_range_eq_of_vanish' J (Q + J) (by omega)
    (fun j _ hj => Finset.sum_eq_zero fun m _ => hF0 j m hj)]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [Finset.smul_sum, Finset.sum_range_eq_of_vanish' Q (Q + J - j) (by omega)
    (fun m _ hm => hF1 j m hm)]

/-- **The two-point function**: `DD v A (DD u B x) = Σ_j fco(⟨v,u⟩)_j · NN(A+j, B−j) x`. -/
theorem DD_DD_eq (v u : Fin r → ℂ) {x : FockT r} {Q : ℕ} (hQ : GoodB v u x Q) (A B : ℤ) (J : ℕ)
    (hJ : B + Q ≤ J) :
    DD v A (DD u B x) = ∑ j ∈ Finset.range J, fco (pair v u) j • NN v u Q (A + j) (B - j) x := by
  rw [DD_apply_range u B x Q hQ.2.1, map_sum]
  have h2 : ∀ q' ∈ Finset.range Q, DD v A (sMz u (B + q') * EpC u q' x)
      = ∑ j ∈ Finset.range J, fco (pair v u) j • ∑ m ∈ Finset.range Q,
          sMz v (A + j + m) * (sMz u (B + q' - j) * EpC v m (EpC u q' x)) := by
    intro q' hq'
    rw [Finset.mem_range] at hq'
    exact DD_sMz_mul v u A (B + q') _ Q (fun q hq => hQ.2.2.1 q q' hq) J (by omega)
  rw [Finset.sum_congr rfl h2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.smul_sum, NN, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun q' _ => ?_
  rw [← mul_assoc, show B + (q' : ℤ) - j = B - j + q' by ring]

/-! ## Regrouping by the total shift -/

section Window

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem window_P (φ : ℤ → M) (L : ℕ) (hφ : ∀ t, φ t ≠ 0 → -(L : ℤ) ≤ t ∧ t < L) (f : ℤ → ℂ)
    (hf : ∀ t, t < 0 → f t = 0) (s : ℤ) (hs : -(L : ℤ) ≤ s) (J : ℕ) (hJ : 2 * L ≤ J) :
    ∑ j ∈ Finset.range J, f j • φ (s + j)
      = ∑ t ∈ Finset.Ico (-(L : ℤ)) L, f (t - s) • φ t := by
  refine Finset.sum_bij_ne_zero (fun j _ _ => s + j) ?_ ?_ ?_ ?_
  · intro j _ hne
    have := hφ _ (fun h => hne (by rw [h, smul_zero]))
    simp only [Finset.mem_Ico]; omega
  · intro j₁ _ _ j₂ _ _ h
    exact_mod_cast (add_left_cancel h : (j₁ : ℤ) = j₂)
  · intro t ht hne
    have h1 : f (t - s) ≠ 0 := fun h => hne (by rw [h, zero_smul])
    have h2 : 0 ≤ t - s := by
      by_contra hc; exact h1 (hf _ (by omega))
    simp only [Finset.mem_Ico] at ht
    have e1 : s + (((t - s).toNat : ℕ) : ℤ) = t := by omega
    have e2 : (((t - s).toNat : ℕ) : ℤ) = t - s := by omega
    refine ⟨(t - s).toNat, Finset.mem_range.mpr (by omega), ?_, e1⟩
    rw [e1, e2]; exact hne
  · intro j _ _
    rw [show s + (j : ℤ) - s = j by ring]

theorem window_Q (φ : ℤ → M) (L : ℕ) (hφ : ∀ t, φ t ≠ 0 → -(L : ℤ) ≤ t ∧ t < L) (f : ℤ → ℂ)
    (hf : ∀ t, t < 0 → f t = 0) (s : ℤ) (hs : s < L) (J : ℕ) (hJ : 2 * L ≤ J) :
    ∑ j ∈ Finset.range J, f j • φ (s - j)
      = ∑ t ∈ Finset.Ico (-(L : ℤ)) L, f (s - t) • φ t := by
  refine Finset.sum_bij_ne_zero (fun j _ _ => s - j) ?_ ?_ ?_ ?_
  · intro j _ hne
    have := hφ _ (fun h => hne (by rw [h, smul_zero]))
    simp only [Finset.mem_Ico]; omega
  · intro j₁ _ _ j₂ _ _ h
    have : (j₁ : ℤ) = j₂ := by linarith
    exact_mod_cast this
  · intro t ht hne
    have h1 : f (s - t) ≠ 0 := fun h => hne (by rw [h, zero_smul])
    have h2 : 0 ≤ s - t := by
      by_contra hc; exact h1 (hf _ (by omega))
    simp only [Finset.mem_Ico] at ht
    have e1 : s - (((s - t).toNat : ℕ) : ℤ) = t := by omega
    have e2 : (((s - t).toNat : ℕ) : ℤ) = s - t := by omega
    refine ⟨(s - t).toNat, Finset.mem_range.mpr (by omega), ?_, e1⟩
    rw [e1, e2]; exact hne
  · intro j _ _
    rw [show s - (s - (j : ℤ)) = j by ring]

end Window

/-! ## Locality of the dressings -/

/-- **Twisted lattice locality, coefficient form.**  For `⟨v,u⟩ = n ∈ ℤ` and `N ≥ |n|`,
`Σ_{r ≤ N} (−1)^{N−r} C(N,r) (DD v (A−2r) DD u (B−2(N−r))
  − (−1)^{|n|} DD u (B−2(N−r)) DD v (A−2r)) = 0`. -/
theorem DD_bracket_local (v u : Fin r → ℂ) (n : ℤ) (hn : pair v u = n) (N : ℕ)
    (h1 : -(N : ℤ) ≤ n) (h2 : n ≤ N) (A B : ℤ) (x : FockT r) :
    ∑ r ∈ Finset.range (N + 1), ((-1 : ℂ) ^ (N - r) * (N.choose r : ℂ)) •
      (DD v (A - 2 * r) (DD u (B - 2 * (N - r : ℕ)) x)
        - (-1 : ℂ) ^ n.natAbs • DD u (B - 2 * (N - r : ℕ)) (DD v (A - 2 * r) x)) = 0 := by
  obtain ⟨Q, hQ⟩ := exists_goodB v u x
  set L : ℕ := A.natAbs + B.natAbs + 2 * N + Q + 1 with hL
  set φ : ℤ → FockT r := fun t => NN v u Q (A - 2 * N + t) (B - t) x with hφ
  have hφs : ∀ t, φ t ≠ 0 → -(L : ℤ) ≤ t ∧ t < L := by
    intro t ht
    by_contra hc
    apply ht
    simp only [hφ]
    rcases not_and_or.mp hc with h | h
    · exact NN_eq_zero_left v u Q _ _ x (by omega)
    · exact NN_eq_zero_right v u Q _ _ x (by omega)
  have hfz : ∀ t : ℤ, t < 0 → fz (n : ℂ) t = 0 := fun t ht => by rw [fz, if_neg (by omega)]
  have hfz' : ∀ j : ℕ, fco (pair v u) j = fz (n : ℂ) j := fun j => by
    rw [fz, if_pos (by omega), Int.toNat_natCast, hn]
  have hu : pair u v = n := by rw [pair_comm, hn]
  have hfz'' : ∀ j : ℕ, fco (pair u v) j = fz (n : ℂ) j := fun j => by
    rw [fz, if_pos (by omega), Int.toNat_natCast, hu]
  -- the `P`-side
  have hP : ∀ r ∈ Finset.range (N + 1), DD v (A - 2 * r) (DD u (B - 2 * (N - r : ℕ)) x)
      = ∑ t ∈ Finset.Ico (-(L : ℤ)) L, fz (n : ℂ) (t - 2 * (N - r : ℕ)) • φ t := by
    intro r hr
    rw [Finset.mem_range] at hr
    rw [DD_DD_eq v u hQ _ _ (2 * L) (by omega)]
    rw [← window_P φ L hφs (fz (n : ℂ)) hfz (2 * (N - r : ℕ)) (by omega) (2 * L) le_rfl]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hfz']
    simp only [hφ]
    congr 2 <;> push_cast [Nat.cast_sub (show r ≤ N by omega)] <;> ring
  -- the `Q`-side
  have hQs : ∀ r ∈ Finset.range (N + 1), DD u (B - 2 * (N - r : ℕ)) (DD v (A - 2 * r) x)
      = ∑ t ∈ Finset.Ico (-(L : ℤ)) L, fz (n : ℂ) (2 * (N - r : ℕ) - t) • φ t := by
    intro r hr
    rw [Finset.mem_range] at hr
    rw [DD_DD_eq u v hQ.symm _ _ (2 * L) (by omega)]
    rw [← window_Q φ L hφs (fz (n : ℂ)) hfz (2 * (N - r : ℕ)) (by omega) (2 * L) le_rfl]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hfz'', NN_symm]
    simp only [hφ]
    congr 2 <;> push_cast [Nat.cast_sub (show r ≤ N by omega)] <;> ring
  set c : ℕ → ℂ := fun r => (-1 : ℂ) ^ (N - r) * (N.choose r : ℂ) with hc
  set W := Finset.Ico (-(L : ℤ)) L with hW
  simp only [smul_sub, Finset.sum_sub_distrib]
  have eP : ∑ r ∈ Finset.range (N + 1), c r • DD v (A - 2 * r) (DD u (B - 2 * (N - r : ℕ)) x)
      = ∑ r ∈ Finset.range (N + 1), c r • ∑ t ∈ W, fz (n : ℂ) (t - 2 * (N - r : ℕ)) • φ t :=
    Finset.sum_congr rfl fun r hr => by rw [hP r hr]
  have eQ : ∑ r ∈ Finset.range (N + 1),
        c r • (-1 : ℂ) ^ n.natAbs • DD u (B - 2 * (N - r : ℕ)) (DD v (A - 2 * r) x)
      = ∑ r ∈ Finset.range (N + 1),
        c r • (-1 : ℂ) ^ n.natAbs • ∑ t ∈ W, fz (n : ℂ) (2 * (N - r : ℕ) - t) • φ t :=
    Finset.sum_congr rfl fun r hr => by rw [hQs r hr]
  rw [eP, eQ]
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm (s := Finset.range (N + 1)), Finset.sum_comm (s := Finset.range (N + 1)),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [← Finset.sum_smul, ← Finset.sum_smul, ← sub_smul]
  have hs := sum_binom_fz_symm N n h1 h2 t
  simp only [hc] at hs ⊢
  rw [hs, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_eq_zero, zero_smul]
  intro r _
  ring

end VOA.Moonshine.LatticeTwisted
