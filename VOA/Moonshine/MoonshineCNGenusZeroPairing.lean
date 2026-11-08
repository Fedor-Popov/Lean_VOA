/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGenusZeroInterface

/-!
# Genus zero on the abstract interface: the Hecke pairing at a prime

Blueprint: `Notes/moonshine/MOON_M8_LEAN.md`. Conditional on the prime Hecke identity
`PrimeHeckeIdentityAt F k p hp` (proved on the LR side).

* `forall_poly_of_monic_basis`: a predicate on `ℂ[X]` closed under sums and scalar multiples,
  true for `1` and for some monic polynomial of each positive degree, holds everywhere.
* `exists_poly_heckeValueSum` (polynomial Hecke sums): for every polynomial `P`,
  `Σ_{β ∈ Δ(p)} P(f(β τ)) = R(f τ)` for a polynomial `R`, where `Δ(p)` acts by
  `τ ↦ (τ + j)/p` (`j < p`) and `τ ↦ p τ`. Proof: the Faber polynomials `P_m` of the
  replication formula span `ℂ[X]`, and for them the sum is `H_{mp} + [p ∣ m] p H_{m/p}` by the
  prime Hecke identity.
* `mem_of_forall_sum_eval_eq` (multisets with equal polynomial sums): two multisets of complex
  numbers on which every polynomial has the same sum have the same members (one test
  polynomial; no Newton identities).
* `heckeValues_pairing` (pointwise Hecke pairing): if `f z = f w`, every value `f(β z)`,
  `β ∈ Δ(p)`, is a value `f(β′ w)`, `β′ ∈ Δ(p)`; explicit forms `hecke_pairing_shift`,
  `hecke_pairing_scale`.
-/

namespace VOA.Moonshine.ConwayNorton

open UpperHalfPlane Polynomial
open scoped MatrixGroups

/-! ### Polynomials spanned by a monic family -/

/-- A predicate on `ℂ[X]` closed under sums and scalar multiples, true for `1` and for a monic
polynomial of every positive degree, holds for every polynomial. -/
theorem forall_poly_of_monic_basis {S : ℂ[X] → Prop}
    (hadd : ∀ P Q, S P → S Q → S (P + Q)) (hsmul : ∀ (a : ℂ) P, S P → S (a • P))
    (hone : S 1) (hmonic : ∀ m : ℕ, 0 < m → ∃ Q : ℂ[X], Q.Monic ∧ Q.natDegree = m ∧ S Q)
    (P : ℂ[X]) : S P := by
  suffices h : ∀ d : ℕ, ∀ P : ℂ[X], P.natDegree ≤ d → S P from h _ P le_rfl
  intro d
  induction d with
  | zero =>
    intro P hP
    rw [eq_C_of_natDegree_le_zero hP, ← mul_one (Polynomial.C (P.coeff 0)), ← smul_eq_C_mul]
    exact hsmul _ _ hone
  | succ d ih =>
    intro P hP
    obtain ⟨Q, hQm, hQd, hQ⟩ := hmonic (d + 1) (Nat.succ_pos d)
    have hQ1 : Q.coeff (d + 1) = 1 := by
      rw [← hQd]
      exact hQm.coeff_natDegree
    have hdeg : (P - P.coeff (d + 1) • Q).natDegree ≤ d := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro n hn
      rw [coeff_sub, coeff_smul, smul_eq_mul]
      rcases (show d + 1 ≤ n from hn).eq_or_lt with h | h
      · rw [← h, hQ1, mul_one, sub_self]
      · have h1 : P.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (hP.trans_lt h)
        have h2 : Q.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (by rw [hQd]; exact h)
        rw [h1, h2, mul_zero, sub_zero]
    have h := hadd _ _ (ih _ hdeg) (hsmul (P.coeff (d + 1)) Q hQ)
    rwa [sub_add_cancel] at h

/-! ### Multisets with equal polynomial sums -/

lemma eval_prod_X_sub_C (u : Multiset ℂ) (z : ℂ) :
    ((u.map fun y => X - Polynomial.C y).prod).eval z = (u.map fun y => z - y).prod := by
  rw [eval_multiset_prod, Multiset.map_map]
  congr 1
  exact Multiset.map_congr rfl fun y _ => by simp

/-- **Membership from polynomial sums.** If every polynomial has the same sum over `s` and over
`t`, every member of `s` is a member of `t`. -/
theorem mem_of_forall_sum_eval_eq {s t : Multiset ℂ}
    (h : ∀ P : ℂ[X], (s.map P.eval).sum = (t.map P.eval).sum) {x : ℂ} (hx : x ∈ s) :
    x ∈ t := by
  classical
  set P : ℂ[X] :=
    (t.map fun y => X - Polynomial.C y).prod *
      ((s.dedup.erase x).map fun y => X - Polynomial.C y).prod with hPdef
  have hPeval : ∀ z : ℂ, P.eval z =
      (t.map fun y => z - y).prod * ((s.dedup.erase x).map fun y => z - y).prod := by
    intro z
    rw [hPdef, eval_mul, eval_prod_X_sub_C, eval_prod_X_sub_C]
  have hPt : ∀ y ∈ t, P.eval y = 0 := by
    intro y hy
    rw [hPeval]
    exact mul_eq_zero_of_left (Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨y, hy, sub_self y⟩)) _
  have hPs : ∀ y ≠ x, y ∈ s → P.eval y = 0 := by
    intro y hyx hy
    rw [hPeval]
    refine mul_eq_zero_of_right _ (Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨y, ?_, sub_self y⟩))
    exact (Multiset.mem_erase_of_ne hyx).mpr (Multiset.mem_dedup.mpr hy)
  have ht0 : (t.map P.eval).sum = 0 := Multiset.sum_eq_zero fun z hz => by
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hz
    exact hPt y hy
  have hs : (s.map P.eval).sum = s.count x • P.eval x :=
    Multiset.sum_map_eq_nsmul_single x fun y hyx hy => hPs y hyx hy
  have hsum := h P
  rw [hs, ht0, nsmul_eq_mul] at hsum
  have hcount : (s.count x : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Multiset.count_ne_zero.mpr hx)
  have hPx : P.eval x = 0 := (mul_eq_zero.mp hsum).resolve_left hcount
  rw [hPeval] at hPx
  rcases mul_eq_zero.mp hPx with h1 | h2
  · obtain ⟨z, hz, hz0⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp h1)
    rwa [sub_eq_zero.mp hz0]
  · exfalso
    obtain ⟨z, hz, hz0⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp h2)
    rw [← sub_eq_zero.mp hz0] at hz
    exact (Multiset.nodup_dedup s).notMem_erase hz

/-! ### Sums over `Δ(p)` -/

variable {N : ℕ} (F : ReplicableFamily N) (k p : ℕ) (hp : 0 < p)

/-- `Σ_{β ∈ Δ(p)} P(f(β τ))` for `f = qSeriesFun (F.c k)`: the `p` points `(τ + j)/p` and `p τ`. -/
noncomputable def heckeValueSum (P : ℂ[X]) (τ : ℍ) : ℂ :=
  (∑ j ∈ Finset.range p, P.eval (qSeriesFun (F.c k) (heckePoint 1 p j one_pos hp τ))) +
    P.eval (qSeriesFun (F.c k) (heckePoint p 1 0 hp one_pos τ))

/-- The multiset `{f(β τ) : β ∈ Δ(p)}`. -/
noncomputable def heckeValues (τ : ℍ) : Multiset ℂ :=
  (Finset.range p).val.map (fun j => qSeriesFun (F.c k) (heckePoint 1 p j one_pos hp τ)) +
    {qSeriesFun (F.c k) (heckePoint p 1 0 hp one_pos τ)}

lemma sum_map_eval_heckeValues (P : ℂ[X]) (τ : ℍ) :
    ((heckeValues F k p hp τ).map P.eval).sum = heckeValueSum F k p hp P τ := by
  rw [heckeValues, Multiset.map_add, Multiset.sum_add, Multiset.map_map, Multiset.map_singleton,
    Multiset.sum_singleton]
  rfl

/-- **Polynomial Hecke sums are polynomials in `f`**, given the prime Hecke identity
at `p`. -/
theorem exists_poly_heckeValueSum (hB1 : PrimeHeckeIdentityAt F k p hp) (P : ℂ[X]) :
    ∃ R : ℂ[X], ∀ τ : ℍ, heckeValueSum F k p hp P τ = R.eval (qSeriesFun (F.c k) τ) := by
  refine forall_poly_of_monic_basis
    (S := fun P => ∃ R : ℂ[X], ∀ τ : ℍ, heckeValueSum F k p hp P τ = R.eval (qSeriesFun (F.c k) τ))
    ?_ ?_ ?_ ?_ P
  · rintro P Q ⟨R₁, hR₁⟩ ⟨R₂, hR₂⟩
    refine ⟨R₁ + R₂, fun τ => ?_⟩
    rw [eval_add, ← hR₁, ← hR₂]
    simp only [heckeValueSum, eval_add, Finset.sum_add_distrib]
    ring
  · rintro a P ⟨R, hR⟩
    refine ⟨a • R, fun τ => ?_⟩
    rw [eval_smul, ← hR]
    simp only [heckeValueSum, eval_smul, smul_eq_mul, ← Finset.mul_sum]
    ring
  · refine ⟨Polynomial.C ((p : ℂ) + 1), fun τ => ?_⟩
    simp [heckeValueSum]
  · intro m hm
    obtain ⟨Q, hQm, hQd, hQ⟩ := F.exists_monic_eval_eq_heckeOrbitSum k m hm
    obtain ⟨R₁, -, -, hR₁⟩ := F.exists_monic_eval_eq_heckeOrbitSum k (m * p) (Nat.mul_pos hm hp)
    refine ⟨Q, hQm, hQd, ?_⟩
    by_cases hpm : p ∣ m
    · obtain ⟨R₂, -, -, hR₂⟩ := F.exists_monic_eval_eq_heckeOrbitSum k (m / p)
        (Nat.div_pos (Nat.le_of_dvd hm hpm) hp)
      refine ⟨R₁ + Polynomial.C (p : ℂ) * R₂, fun τ => ?_⟩
      simp only [heckeValueSum, hQ]
      rw [hB1 m hm τ, if_pos hpm, ← hR₁, ← hR₂]
      simp
    · refine ⟨R₁, fun τ => ?_⟩
      simp only [heckeValueSum, hQ]
      rw [hB1 m hm τ, if_neg hpm, ← hR₁, add_zero]

/-- **The Hecke pairing**: if `f z = f w`, every member of `{f(β z) : β ∈ Δ(p)}` is a
member of `{f(β w) : β ∈ Δ(p)}`. -/
theorem heckeValues_pairing (hB1 : PrimeHeckeIdentityAt F k p hp) {z w : ℍ}
    (h : qSeriesFun (F.c k) z = qSeriesFun (F.c k) w) {x : ℂ}
    (hx : x ∈ heckeValues F k p hp z) : x ∈ heckeValues F k p hp w := by
  refine mem_of_forall_sum_eval_eq (fun P => ?_) hx
  obtain ⟨R, hR⟩ := exists_poly_heckeValueSum F k p hp hB1 P
  rw [sum_map_eval_heckeValues, sum_map_eval_heckeValues, hR, hR, h]

lemma mem_heckeValues_iff {x : ℂ} {τ : ℍ} :
    x ∈ heckeValues F k p hp τ ↔
      (∃ j < p, qSeriesFun (F.c k) (heckePoint 1 p j one_pos hp τ) = x) ∨
        x = qSeriesFun (F.c k) (heckePoint p 1 0 hp one_pos τ) := by
  simp only [heckeValues, Multiset.mem_add, Multiset.mem_map, Finset.mem_val, Finset.mem_range,
    Multiset.mem_singleton]

/-- Pairing for a shifted point `(z + j)/p`. -/
theorem hecke_pairing_shift (hB1 : PrimeHeckeIdentityAt F k p hp) {z w : ℍ}
    (h : qSeriesFun (F.c k) z = qSeriesFun (F.c k) w) {j : ℕ} (hj : j < p) :
    (∃ j' < p, qSeriesFun (F.c k) (heckePoint 1 p j one_pos hp z) =
        qSeriesFun (F.c k) (heckePoint 1 p j' one_pos hp w)) ∨
      qSeriesFun (F.c k) (heckePoint 1 p j one_pos hp z) =
        qSeriesFun (F.c k) (heckePoint p 1 0 hp one_pos w) := by
  have hx : qSeriesFun (F.c k) (heckePoint 1 p j one_pos hp z) ∈ heckeValues F k p hp z :=
    (mem_heckeValues_iff F k p hp).mpr (Or.inl ⟨j, hj, rfl⟩)
  rcases (mem_heckeValues_iff F k p hp).mp (heckeValues_pairing F k p hp hB1 h hx) with
    ⟨j', hj', he⟩ | he
  · exact Or.inl ⟨j', hj', he.symm⟩
  · exact Or.inr he

/-- Pairing for the scaled point `p z`. -/
theorem hecke_pairing_scale (hB1 : PrimeHeckeIdentityAt F k p hp) {z w : ℍ}
    (h : qSeriesFun (F.c k) z = qSeriesFun (F.c k) w) :
    (∃ j' < p, qSeriesFun (F.c k) (heckePoint p 1 0 hp one_pos z) =
        qSeriesFun (F.c k) (heckePoint 1 p j' one_pos hp w)) ∨
      qSeriesFun (F.c k) (heckePoint p 1 0 hp one_pos z) =
        qSeriesFun (F.c k) (heckePoint p 1 0 hp one_pos w) := by
  have hx : qSeriesFun (F.c k) (heckePoint p 1 0 hp one_pos z) ∈ heckeValues F k p hp z :=
    (mem_heckeValues_iff F k p hp).mpr (Or.inr rfl)
  rcases (mem_heckeValues_iff F k p hp).mp (heckeValues_pairing F k p hp hB1 h hx) with
    ⟨j', hj', he⟩ | he
  · exact Or.inl ⟨j', hj', he.symm⟩
  · exact Or.inr he

end VOA.Moonshine.ConwayNorton
