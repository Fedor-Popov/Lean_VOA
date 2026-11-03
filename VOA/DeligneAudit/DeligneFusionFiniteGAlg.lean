/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneSectorWeyl

/-!
# Commutator algebra for the finiteness clause

Ring identities for the commutator derivation `adR X : Z ↦ XZ - ZX` of a ring `R`, and the two
operator lemmas behind local nilpotency in `Module.End ℂ V`.

* `adR_iterate_mul`: the general Leibniz rule.
* `adR_iterate_eq_sum`: `(ad X)^n Z = Σ_m C(n,m) X^m Z (-X)^(n-m)`.
* `pow_mul_eq_sum`: `A^n B = Σ_m C(n,m) ((ad A)^(n-m) B) A^m`.
* `adR_iterate_pow`: if `(ad X)^(q+1) Y = 0` then `(ad X)^(qN) (Y^N) = c • ((ad X)^q Y)^N` with
  `c ≠ 0`, and `(ad X)^j (Y^N) = 0` for `j > qN`.
* `pow_kill_of_ad` (Kac's lemma, one letter): if `(ad A)^K B = 0` and `A^N u = 0`, then
  `A^(N+K) (B u) = 0`.
* `top_nil` (top of an `ad`-string): if `(ad X)^(q+1) Y = 0`, `X^p v = 0` and `Y^N` kills
  `X^b v` for every `b < p`, then `((ad X)^q Y)^N v = 0`. This is the coefficient of `t^(qN)` in
  `e^{tX} Y^N e^{-tX} = (e^{tX} Y e^{-tX})^N` applied to `v`, with no exponential needed.
-/

namespace VOA.DeligneAudit.FiniteG

open Finset

section Ring

variable {R : Type*} [Ring R]

/-- The commutator derivation `Z ↦ XZ - ZX`. -/
def adR (X : R) : AddMonoid.End R := AddMonoidHom.mulLeft X - AddMonoidHom.mulRight X

@[simp] theorem adR_apply (X Z : R) : adR X Z = X * Z - Z * X := rfl

theorem adR_mul (X Y Z : R) : adR X (Y * Z) = Y * adR X Z + adR X Y * Z := by
  simp only [adR_apply]; noncomm_ring

theorem adR_iterate_zero (X : R) (n : ℕ) : (adR X)^[n] 0 = 0 := iterate_map_zero (adR X) n

theorem adR_iterate_of_le {X Y : R} {k : ℕ} (h : (adR X)^[k] Y = 0) {j : ℕ} (hj : k ≤ j) :
    (adR X)^[j] Y = 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, j = t + k := ⟨j - k, by omega⟩
  rw [Function.iterate_add_apply, h, adR_iterate_zero]

/-- **The general Leibniz rule** for `adR`. -/
theorem adR_iterate_mul (X Y Z : R) (n : ℕ) :
    (adR X)^[n] (Y * Z) =
      ∑ ij ∈ antidiagonal n, n.choose ij.1 • ((adR X)^[ij.1] Y * (adR X)^[ij.2] Z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_antidiagonal_choose_succ_nsmul (M := R)
      (fun i j => (adR X)^[i] Y * (adR X)^[j] Z) n]
    simp only [Function.iterate_succ_apply', ih, map_sum, map_nsmul, adR_mul, smul_add,
      sum_add_distrib, add_right_inj]
    refine sum_congr rfl fun ⟨i, j⟩ hij => ?_
    rw [n.choose_symm_of_eq_add (mem_antidiagonal.1 hij).symm]

/-- `(ad X)^n Z = Σ_m C(n,m) X^m Z (-X)^(n-m)`. -/
theorem adR_iterate_eq_sum (X Z : R) (n : ℕ) :
    (adR X)^[n] Z = ∑ m ∈ range (n + 1), n.choose m • (X ^ m * Z * (-X) ^ (n - m)) := by
  set L : AddMonoid.End R := AddMonoidHom.mulLeft X
  set Rr : AddMonoid.End R := AddMonoidHom.mulRight (-X)
  have hLf : (⇑L : R → R) = (X * ·) := rfl
  have hRf : (⇑Rr : R → R) = (· * -X) := rfl
  have hc : Commute L Rr := by
    ext Z
    change L (Rr Z) = Rr (L Z)
    rw [hLf, hRf]
    exact (mul_assoc X Z (-X)).symm
  have hs : adR X = L + Rr := by
    ext Z
    change X * Z - Z * X = L Z + Rr Z
    rw [hLf, hRf]
    simp only [mul_neg, sub_eq_add_neg]
  have h := congrArg (fun T : AddMonoid.End R => T Z) (hc.add_pow n)
  simp only at h
  rw [← AddMonoid.End.coe_pow, hs, h]
  erw [AddMonoidHom.finsetSum_apply]
  refine sum_congr rfl fun m _ => ?_
  change (L ^ m) ((Rr ^ (n - m)) (((n.choose m : ℕ) : AddMonoid.End R) Z)) = _
  rw [AddMonoid.End.natCast_apply, AddMonoid.End.coe_pow, AddMonoid.End.coe_pow, hLf, hRf,
    mul_left_iterate_apply, mul_right_iterate_apply, smul_mul_assoc, mul_smul_comm, mul_assoc]

/-- `A^n B = Σ_m C(n,m) ((ad A)^(n-m) B) A^m`. -/
theorem pow_mul_eq_sum (A B : R) (n : ℕ) :
    A ^ n * B = ∑ m ∈ range (n + 1), n.choose m • ((adR A)^[n - m] B * A ^ m) := by
  set Rr : AddMonoid.End R := AddMonoidHom.mulRight A
  set L : AddMonoid.End R := AddMonoidHom.mulLeft A
  have hLf : (⇑L : R → R) = (A * ·) := rfl
  have hRf : (⇑Rr : R → R) = (· * A) := rfl
  have hc : Commute Rr (adR A) := by
    ext Z
    change Rr (adR A Z) = adR A (Rr Z)
    rw [hRf]
    simp only [adR_apply]
    noncomm_ring
  have hs : L = Rr + adR A := by
    ext Z
    change L Z = Rr Z + adR A Z
    rw [hLf, hRf, adR_apply]
    abel
  have h := congrArg (fun T : AddMonoid.End R => T B) (hc.add_pow n)
  simp only at h
  have hL : A ^ n * B = (L ^ n) B := by
    rw [AddMonoid.End.coe_pow, hLf, mul_left_iterate_apply]
  rw [hL, hs, h]
  erw [AddMonoidHom.finsetSum_apply]
  refine sum_congr rfl fun m _ => ?_
  change (Rr ^ m) (((adR A) ^ (n - m)) (((n.choose m : ℕ) : AddMonoid.End R) B)) = _
  rw [AddMonoid.End.natCast_apply, AddMonoid.End.coe_pow, AddMonoid.End.coe_pow, hRf,
    mul_right_iterate_apply, ← AddMonoid.End.coe_pow, map_nsmul, smul_mul_assoc]

/-- If `(ad X)^(q+1) Y = 0`: `(ad X)^(qN) (Y^N) = c • ((ad X)^q Y)^N` with `c ≠ 0`, and
`(ad X)^j (Y^N) = 0` for `j > qN`. -/
theorem adR_iterate_pow {X Y : R} {q : ℕ} (hq : (adR X)^[q + 1] Y = 0) :
    ∀ N : ℕ, (∃ c : ℕ, c ≠ 0 ∧ (adR X)^[q * N] (Y ^ N) = c • ((adR X)^[q] Y) ^ N) ∧
      ∀ j, q * N < j → (adR X)^[j] (Y ^ N) = 0
  | 0 => by
      refine ⟨⟨1, one_ne_zero, by simp⟩, fun j hj => ?_⟩
      obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
      rw [pow_zero, Function.iterate_succ_apply]
      have : adR X (1 : R) = 0 := by simp
      rw [this, adR_iterate_zero]
  | N + 1 => by
      obtain ⟨⟨c, hc0, hc⟩, hz⟩ := adR_iterate_pow hq N
      have hY : ∀ i, q < i → (adR X)^[i] Y = 0 := fun i hi => adR_iterate_of_le hq (by omega)
      have hzero : ∀ j, ∀ ij ∈ antidiagonal j, (q < ij.1 ∨ q * N < ij.2) →
          j.choose ij.1 • ((adR X)^[ij.1] Y * (adR X)^[ij.2] (Y ^ N)) = 0 := by
        rintro j ⟨i, k⟩ _ (h | h)
        · rw [hY i h, zero_mul, smul_zero]
        · rw [hz k h, mul_zero, smul_zero]
      refine ⟨⟨(q * (N + 1)).choose q * c, ?_, ?_⟩, fun j hj => ?_⟩
      · exact Nat.mul_ne_zero (Nat.choose_pos (by nlinarith)).ne' hc0
      · rw [pow_succ', adR_iterate_mul, sum_eq_single (q, q * N)]
        · rw [hc, mul_smul_comm, ← pow_succ', mul_smul]
        · rintro ⟨i, k⟩ hik hne
          refine hzero _ _ hik ?_
          have := mem_antidiagonal.1 hik
          by_contra hcon
          push Not at hcon
          exact hne (Prod.ext (by simp only at this hcon ⊢; nlinarith)
            (by simp only at this hcon ⊢; nlinarith))
        · intro h
          exact absurd (mem_antidiagonal.2 (by ring)) h
      · rw [pow_succ', adR_iterate_mul]
        refine sum_eq_zero fun ik hik => hzero _ _ hik ?_
        have := mem_antidiagonal.1 hik
        by_contra hcon
        push Not at hcon
        nlinarith

end Ring

/-! ## Operator lemmas -/

section Op

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- **Kac's lemma, one letter**: if `(ad A)^K B = 0` and `A^N u = 0`, then `A^(N+K) (B u) = 0`. -/
theorem pow_kill_of_ad (A B : Module.End ℂ V) (K N : ℕ) (u : V) (hK : (adR A)^[K] B = 0)
    (hu : (A ^ N) u = 0) : (A ^ (N + K)) (B u) = 0 := by
  rw [← Module.End.mul_apply, pow_mul_eq_sum, LinearMap.coe_sum, Finset.sum_apply]
  refine sum_eq_zero fun m hm => ?_
  rw [LinearMap.smul_apply, Module.End.mul_apply]
  by_cases hmN : N ≤ m
  · obtain ⟨t, rfl⟩ : ∃ t, m = t + N := ⟨m - N, by omega⟩
    rw [pow_add, Module.End.mul_apply, hu, map_zero, map_zero, smul_zero]
  · rw [adR_iterate_of_le hK (by omega), LinearMap.zero_apply, smul_zero]

theorem pow_kill_mono (A : Module.End ℂ V) {N M : ℕ} {u : V} (hu : (A ^ N) u = 0) (h : N ≤ M) :
    (A ^ M) u = 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, M = t + N := ⟨M - N, by omega⟩
  rw [pow_add, Module.End.mul_apply, hu, map_zero]

/-- **Top of an `ad`-string**: if `(ad X)^(q+1) Y = 0`, `X^p v = 0` and `Y^N` kills `X^b v` for
`b < p`, then `((ad X)^q Y)^N v = 0`. -/
theorem top_nil (X Y : Module.End ℂ V) (q p N : ℕ) (v : V) (hq : (adR X)^[q + 1] Y = 0)
    (hp : (X ^ p) v = 0) (hY : ∀ b < p, (Y ^ N) ((X ^ b) v) = 0) :
    (((adR X)^[q] Y) ^ N) v = 0 := by
  obtain ⟨⟨c, hc0, hc⟩, -⟩ := adR_iterate_pow hq N
  have hv : ((adR X)^[q * N] (Y ^ N)) v = 0 := by
    rw [adR_iterate_eq_sum, LinearMap.coe_sum, Finset.sum_apply]
    refine sum_eq_zero fun m _ => ?_
    rw [LinearMap.smul_apply, Module.End.mul_apply, Module.End.mul_apply]
    set k := q * N - m
    have hneg : ((-X) ^ k) v = ((-1 : ℂ) ^ k) • (X ^ k) v := by
      rw [show -X = (-1 : ℂ) • X by simp, smul_pow, LinearMap.smul_apply]
    rw [hneg, map_smul, map_smul]
    by_cases hk : p ≤ k
    · simp [pow_kill_mono X hp hk]
    · rw [hY k (by omega), map_zero, smul_zero, smul_zero]
  rw [hc, LinearMap.smul_apply, ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at hv
  exact hv.resolve_left (by exact_mod_cast hc0)

end Op

end VOA.DeligneAudit.FiniteG

section AxiomAudit
#print axioms VOA.DeligneAudit.FiniteG.adR_iterate_mul
#print axioms VOA.DeligneAudit.FiniteG.pow_kill_of_ad
#print axioms VOA.DeligneAudit.FiniteG.top_nil
end AxiomAudit
