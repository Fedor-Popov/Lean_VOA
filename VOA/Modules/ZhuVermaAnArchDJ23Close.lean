/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchResSkew
import VOA.Modules.ZhuVermaAnArchDJ23

/-!
# Dong–Jiang Lemma 2.3 from the residue skew relation + Appendix Prop 5.1

With `resHom_skew_mod_Onm` (`ZhuVermaAnArchResSkew`) in hand — the residue form of skew symmetry
modulo `O'_{N,m}`, which was the analytic content of DJ Lemma 2.3 — the lemma itself becomes a
**purely scalar** obligation: Dong–Jiang's Appendix Proposition 5.1 (`A_{p₁,p₂}(z) = 1`), read off
coefficientwise and convolved with `(1+z)^D`.  That obligation is isolated here as `DJ51CoeffD`.

## The reduction

Write `D = wt a − 1 + m − p₂` and use `N = p₁ + p₂ − m` (so `m+N−p₁ = p₂` and `m+N−p₂ = p₁`):

* `a ∗^N_{m,p₁} b = ∑_{i≤p₁} (−1)ⁱ C(p₂+i,i) · Res_z (1+z)^{wt a+m}/z^{p₂+i+1} Y(a,z)b`
  — a `resFull` at exponent `wt a + m = D + p₂ + 1`;
* `b ∗^N_{m,p₂} a = ∑_{i≤p₂} (−1)ⁱ C(p₁+i,i) · Res_z (1+z)^{wt b+m}/z^{p₁+i+1} Y(b,z)a`
  `≡ (−1)^{p₁} ∑_{i≤p₂} C(p₁+i,i) · Res_z (1+z)^{D+i}/z^{p₁+i+1} Y(a,z)b`
  by `resHom_skew_mod_Onm` (the sign `sgn(p₁+i+2) = (−1)^{p₁+i}` absorbs the `(−1)ⁱ`, and the
  exponent shift is `wt a + (p₁+i+1) − N − 2 = D + i`);
* `Res_z (1+z)^D Y(a,z)b` — a `resFull` at exponent `D`, pole `0`.

So all three terms are `resFull`s in `(a,b)`, and comparing coefficients of `a₍ℓ₎b` leaves exactly
`DJ51CoeffD` — engine-verified (`0` failures for `−8 ≤ D ≤ 8`, `0 ≤ p₁,p₂ ≤ 5`, `−6 ≤ ℓ ≤ 10`).

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References
Dong–Jiang math/0601626 §2 (Lemma 2.3), Appendix (Prop 5.1); `ZhuVermaAnArchResSkew`
(`resHom_skew_mod_Onm`, `resHom_eq_resFull`, `finsetSum_smul_resFull`), `ZhuVermaAnArchDJ23`
(`DJ23Comm`, `resExp`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Sign helpers. -/

theorem sgn_add_two (x : ℤ) : sgn (x + 2) = sgn x := by
  rw [show (x + 2 : ℤ) = (x + 1) + 1 from by ring, sgn_succ, sgn_succ, neg_neg]

theorem sgn_natCast_add_two (k : ℕ) : sgn ((k : ℤ) + 2) = (-1 : ℂ) ^ k := by
  rw [sgn_add_two, sgn_natCast]

/-! ## The remaining scalar obligation: DJ Appendix Prop 5.1, convolved form. -/

/-- **Dong–Jiang Appendix Proposition 5.1, in convolved coefficient form.**

`A_{p₁,p₂}(z) = 1` says exactly that, for every exponent `D` and every mode index `ℓ`,

  `∑_{i≤p₁} (−1)ⁱ C(p₂+i,i)·C(D+p₂+1, ℓ+p₂+i+1) − (−1)^{p₁} ∑_{i≤p₂} C(p₁+i,i)·C(D+i, ℓ+p₁+i+1)`
  `= C(D, ℓ)`,

i.e. `Res_z A_{p₁,p₂}(z)(1+z)^D Y(a,z)b = Res_z (1+z)^D Y(a,z)b`.  A carried `Prop` — never an
axiom.  Engine-verified: `0` failures for `−8 ≤ D ≤ 8`, `0 ≤ p₁,p₂ ≤ 5`, `−6 ≤ ℓ ≤ 10`. -/
def DJ51CoeffD : Prop :=
  ∀ (D : ℤ) (p₁ p₂ : ℕ) (ℓ : ℤ),
    (∑ i ∈ Finset.range (p₁ + 1),
        (-1 : ℂ) ^ i * cbz ((p₂ : ℤ) + (i : ℤ)) (i : ℤ)
          * cbz (D + (p₂ : ℤ) + 1) (ℓ + ((p₂ : ℤ) + (i : ℤ) + 1)))
      - (-1 : ℂ) ^ p₁ * (∑ i ∈ Finset.range (p₂ + 1),
          cbz ((p₁ : ℤ) + (i : ℤ)) (i : ℤ) * cbz (D + (i : ℤ)) (ℓ + ((p₁ : ℤ) + (i : ℤ) + 1)))
    = cbz D ℓ

/-! ## `resExp` is a `resFull` at pole `0`. -/

theorem resExp_eq_resFull (W : VertexOperatorAlgebra 𝒱) (E : ℤ) (a b : 𝒱) :
    resExp W E a b = resFull W E 0 a b := by
  rw [resExp, resFull]
  refine finsum_nat_to_int (fun i : ℕ => gBinom E i • W.smul a (i : ℤ) b)
    (fun p : ℤ => cbz E (p + 0) • W.smul a p b) (fun p hp => ?_) (fun j => ?_)
  · show cbz E (p + 0) • W.smul a p b = 0
    rw [show (p + 0 : ℤ) = p from by ring, cbz_apply_neg E hp, zero_smul]
  · show cbz E ((j : ℤ) + 0) • W.smul a (j : ℤ) b = gBinom E j • W.smul a (j : ℤ) b
    rw [show ((j : ℤ) + 0) = (j : ℤ) from by ring, cbz_apply_nonneg E (by positivity),
      Int.toNat_natCast]

/-- A mode family whose coefficients vanish below a bound has finite support. -/
theorem modeFam_support_finite (W : VertexOperatorAlgebra 𝒱) (a b : 𝒱) (g : ℤ → ℂ) {B : ℤ}
    (hg : ∀ ℓ : ℤ, ℓ < B → g ℓ = 0) :
    (Function.support fun ℓ : ℤ => g ℓ • W.smul a ℓ b).Finite := by
  obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero a b
  refine Set.Finite.subset (Set.finite_Icc B Nz) ?_
  intro ℓ hℓ
  rw [Function.mem_support] at hℓ
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · by_contra h
    push_neg at h
    exact hℓ (by rw [hg ℓ h, zero_smul])
  · by_contra h
    push_neg at h
    exact hℓ (by rw [hNz ℓ (by omega), smul_zero])

/-! ## The three coefficient families of DJ Lemma 2.3. -/

/-- Coefficient of `a₍ℓ₎b` in `a ∗^N_{m,p₁} b`. -/
noncomputable def dj23c1 (D : ℤ) (p₁ p₂ : ℕ) (ℓ : ℤ) : ℂ :=
  ∑ i ∈ Finset.range (p₁ + 1),
    ((-1 : ℂ) ^ i * cbz ((p₂ : ℤ) + (i : ℤ)) (i : ℤ))
      * cbz (D + (p₂ : ℤ) + 1) (ℓ + ((p₂ : ℤ) + (i : ℤ) + 1))

/-- Coefficient of `a₍ℓ₎b` in the skew-rewritten `b ∗^N_{m,p₂} a`. -/
noncomputable def dj23c2 (D : ℤ) (p₁ p₂ : ℕ) (ℓ : ℤ) : ℂ :=
  ∑ i ∈ Finset.range (p₂ + 1),
    ((-1 : ℂ) ^ p₁ * cbz ((p₁ : ℤ) + (i : ℤ)) (i : ℤ))
      * cbz (D + (i : ℤ)) (ℓ + ((p₁ : ℤ) + (i : ℤ) + 1))

theorem dj23c1_vanish (D : ℤ) (p₁ p₂ : ℕ) (ℓ : ℤ)
    (hℓ : ℓ < -((p₁ : ℤ) + (p₂ : ℤ) + 2)) : dj23c1 D p₁ p₂ ℓ = 0 := by
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hlt : ℓ + ((p₂ : ℤ) + (i : ℤ) + 1) < 0 := by
    have : (i : ℤ) ≤ (p₁ : ℤ) := by exact_mod_cast Nat.lt_succ_iff.mp hi
    omega
  rw [cbz_apply_neg _ hlt, mul_zero]

theorem dj23c2_vanish (D : ℤ) (p₁ p₂ : ℕ) (ℓ : ℤ)
    (hℓ : ℓ < -((p₁ : ℤ) + (p₂ : ℤ) + 2)) : dj23c2 D p₁ p₂ ℓ = 0 := by
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hlt : ℓ + ((p₁ : ℤ) + (i : ℤ) + 1) < 0 := by
    have : (i : ℤ) ≤ (p₂ : ℤ) := by exact_mod_cast Nat.lt_succ_iff.mp hi
    omega
  rw [cbz_apply_neg _ hlt, mul_zero]

theorem dj23c3_vanish (D : ℤ) (p₁ p₂ : ℕ) (ℓ : ℤ)
    (hℓ : ℓ < -((p₁ : ℤ) + (p₂ : ℤ) + 2)) : cbz D (ℓ + 0) = 0 :=
  cbz_apply_neg _ (by omega)

/-- `DJ51CoeffD` says exactly that the three coefficient families cancel. -/
theorem dj23_coeff_cancel (h51 : DJ51CoeffD) (D : ℤ) (p₁ p₂ : ℕ) (ℓ : ℤ) :
    dj23c1 D p₁ p₂ ℓ - dj23c2 D p₁ p₂ ℓ - cbz D (ℓ + 0) = 0 := by
  have h := h51 D p₁ p₂ ℓ
  rw [dj23c1, dj23c2, show (ℓ + 0 : ℤ) = ℓ from by ring, Finset.mul_sum] at *
  simp only [mul_assoc] at h ⊢
  linear_combination h

/-! ## Dong–Jiang Lemma 2.3, for homogeneous arguments. -/

/-- **DJ Lemma 2.3 for homogeneous `a, b`**, from the residue skew relation and `DJ51CoeffD`. -/
theorem dj23_homog (W : VertexOperatorAlgebra 𝒱) (h51 : DJ51CoeffD) {K M : ℕ} {a b : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (hb : b ∈ W.grading (M : ℤ)) (m p₁ p₂ N : ℕ)
    (hN : (N : ℤ) = (p₁ : ℤ) + (p₂ : ℤ) - (m : ℤ)) :
    anmGen W N m p₁ a b - anmGen W N m p₂ b a
        - resExp W ((K : ℤ) - 1 + (m : ℤ) - (p₂ : ℤ)) a b
      ∈ Onm W N m := by
  have he1 : ((m : ℤ) + (N : ℤ) - (p₁ : ℤ)) = (p₂ : ℤ) := by omega
  have he2 : ((m : ℤ) + (N : ℤ) - (p₂ : ℤ)) = (p₁ : ℤ) := by omega
  set D : ℤ := (K : ℤ) - 1 + (m : ℤ) - (p₂ : ℤ) with hD
  -- (1) the `p₁` product, exactly, as a combination of `resFull`s
  have hT1 : anmGen W N m p₁ a b
      = ∑ i ∈ Finset.range (p₁ + 1),
          ((-1 : ℂ) ^ i * cbz ((p₂ : ℤ) + (i : ℤ)) (i : ℤ)) •
            resFull W ((K : ℤ) + (m : ℤ)) ((p₂ : ℤ) + (i : ℤ) + 1) a b := by
    rw [anmGen]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [he1, resHom_eq_resFull W ha _ b]
  -- (2) the `p₂` product, modulo `O'`, as a combination of `resFull`s in the swapped order
  have hT2 : anmGen W N m p₂ b a
      - ∑ i ∈ Finset.range (p₂ + 1),
          ((-1 : ℂ) ^ p₁ * cbz ((p₁ : ℤ) + (i : ℤ)) (i : ℤ)) •
            resFull W (D + (i : ℤ)) ((p₁ : ℤ) + (i : ℤ) + 1) a b ∈ Onm W N m := by
    rw [anmGen, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [he2]
    have hsk := Submodule.smul_mem (Onm W N m)
      ((-1 : ℂ) ^ i * cbz ((p₁ : ℤ) + (i : ℤ)) (i : ℤ))
      (resHom_skew_mod_Onm W N m ha hb ((p₁ : ℤ) + (i : ℤ) + 1))
    rw [smul_sub, smul_smul] at hsk
    have hcoef : (-1 : ℂ) ^ i * cbz ((p₁ : ℤ) + (i : ℤ)) (i : ℤ)
          * sgn (((p₁ : ℤ) + (i : ℤ) + 1) + 1)
        = (-1 : ℂ) ^ p₁ * cbz ((p₁ : ℤ) + (i : ℤ)) (i : ℤ) := by
      rw [show (((p₁ : ℤ) + (i : ℤ) + 1) + 1) = (((p₁ + i : ℕ) : ℤ) + 2) from by push_cast; ring,
        sgn_natCast_add_two, pow_add]
      have h2 : ((-1 : ℂ) ^ i) * ((-1 : ℂ) ^ i) = 1 := by
        rw [← pow_add, show i + i = 2 * i from by ring, pow_mul]; norm_num
      calc (-1 : ℂ) ^ i * cbz ((p₁ : ℤ) + (i : ℤ)) (i : ℤ) * ((-1 : ℂ) ^ p₁ * (-1 : ℂ) ^ i)
          = ((-1 : ℂ) ^ i * (-1 : ℂ) ^ i) * ((-1 : ℂ) ^ p₁ * cbz ((p₁ : ℤ) + (i : ℤ)) (i : ℤ)) := by
            ring
        _ = (-1 : ℂ) ^ p₁ * cbz ((p₁ : ℤ) + (i : ℤ)) (i : ℤ) := by rw [h2, one_mul]
    have hexp : ((K : ℤ) + ((p₁ : ℤ) + (i : ℤ) + 1) - (N : ℤ) - 2) = D + (i : ℤ) := by
      rw [hD]; omega
    rwa [hcoef, hexp] at hsk
  -- (3) assemble: everything is a `resFull`, so compare coefficients of `a₍ℓ₎b`
  have hE1 : ((K : ℤ) + (m : ℤ)) = D + (p₂ : ℤ) + 1 := by rw [hD]; ring
  have hf₁ := modeFam_support_finite W a b (dj23c1 D p₁ p₂)
    (fun ℓ hℓ => dj23c1_vanish D p₁ p₂ ℓ hℓ)
  have hf₂ := modeFam_support_finite W a b (dj23c2 D p₁ p₂)
    (fun ℓ hℓ => dj23c2_vanish D p₁ p₂ ℓ hℓ)
  have hf₁₂ := modeFam_support_finite W a b (fun ℓ => dj23c1 D p₁ p₂ ℓ - dj23c2 D p₁ p₂ ℓ)
    (fun ℓ hℓ => by
      show dj23c1 D p₁ p₂ ℓ - dj23c2 D p₁ p₂ ℓ = 0
      rw [dj23c1_vanish D p₁ p₂ ℓ hℓ, dj23c2_vanish D p₁ p₂ ℓ hℓ, sub_zero])
  have hf₃ := modeFam_support_finite W a b (fun ℓ => cbz D (ℓ + 0))
    (fun ℓ hℓ => by
      show cbz D (ℓ + 0) = 0
      exact dj23c3_vanish D p₁ p₂ ℓ hℓ)
  have hkey : (∑ i ∈ Finset.range (p₁ + 1),
        ((-1 : ℂ) ^ i * cbz ((p₂ : ℤ) + (i : ℤ)) (i : ℤ)) •
          resFull W ((K : ℤ) + (m : ℤ)) ((p₂ : ℤ) + (i : ℤ) + 1) a b)
      - (∑ i ∈ Finset.range (p₂ + 1),
        ((-1 : ℂ) ^ p₁ * cbz ((p₁ : ℤ) + (i : ℤ)) (i : ℤ)) •
          resFull W (D + (i : ℤ)) ((p₁ : ℤ) + (i : ℤ) + 1) a b)
      - resFull W D 0 a b = 0 := by
    rw [finsetSum_smul_resFull W _ _ _ _ a b, finsetSum_smul_resFull W _ _ _ _ a b, resFull, hE1]
    rw [show (∑ᶠ ℓ : ℤ, (∑ i ∈ Finset.range (p₁ + 1),
          (-1 : ℂ) ^ i * cbz ((p₂ : ℤ) + (i : ℤ)) (i : ℤ) *
            cbz (D + (p₂ : ℤ) + 1) (ℓ + ((p₂ : ℤ) + (i : ℤ) + 1))) • W.smul a ℓ b)
        = ∑ᶠ ℓ : ℤ, dj23c1 D p₁ p₂ ℓ • W.smul a ℓ b from rfl]
    rw [show (∑ᶠ ℓ : ℤ, (∑ i ∈ Finset.range (p₂ + 1),
          (-1 : ℂ) ^ p₁ * cbz ((p₁ : ℤ) + (i : ℤ)) (i : ℤ) *
            cbz (D + (i : ℤ)) (ℓ + ((p₁ : ℤ) + (i : ℤ) + 1))) • W.smul a ℓ b)
        = ∑ᶠ ℓ : ℤ, dj23c2 D p₁ p₂ ℓ • W.smul a ℓ b from rfl]
    rw [← finsum_sub_distrib hf₁ hf₂]
    rw [finsum_congr (fun ℓ : ℤ =>
      (sub_smul (dj23c1 D p₁ p₂ ℓ) (dj23c2 D p₁ p₂ ℓ) (W.smul a ℓ b)).symm)]
    rw [← finsum_sub_distrib hf₁₂ hf₃]
    refine finsum_eq_zero_of_forall_eq_zero fun ℓ => ?_
    show (dj23c1 D p₁ p₂ ℓ - dj23c2 D p₁ p₂ ℓ) • W.smul a ℓ b
      - cbz D (ℓ + 0) • W.smul a ℓ b = 0
    rw [← sub_smul, dj23_coeff_cancel h51 D p₁ p₂ ℓ, zero_smul]
  rw [hT1, resExp_eq_resFull]
  set T1 : 𝒱 := ∑ i ∈ Finset.range (p₁ + 1),
    ((-1 : ℂ) ^ i * cbz ((p₂ : ℤ) + (i : ℤ)) (i : ℤ)) •
      resFull W ((K : ℤ) + (m : ℤ)) ((p₂ : ℤ) + (i : ℤ) + 1) a b with hT1def
  set T2 : 𝒱 := ∑ i ∈ Finset.range (p₂ + 1),
    ((-1 : ℂ) ^ p₁ * cbz ((p₁ : ℤ) + (i : ℤ)) (i : ℤ)) •
      resFull W (D + (i : ℤ)) ((p₁ : ℤ) + (i : ℤ) + 1) a b with hT2def
  set R : 𝒱 := resFull W D 0 a b with hRdef
  set Q : 𝒱 := anmGen W N m p₂ b a with hQdef
  have hfinal : T1 - Q - R = -(Q - T2) := by
    rw [← sub_eq_zero, show T1 - Q - R - -(Q - T2) = T1 - T2 - R from by abel]
    exact hkey
  rw [hfinal]
  exact (Onm W N m).neg_mem hT2

/-! ## Dong–Jiang Lemma 2.3 in full: `DJ23Comm`. -/

theorem anmGen_zero_left (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (v : 𝒱) :
    anmGen W n m p 0 v = 0 := by
  have := anmGen_smul_left W n m p (0 : ℂ) 0 v
  simpa using this

theorem anmGen_zero_right (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (u : 𝒱) :
    anmGen W n m p u 0 = 0 := by
  have := anmGen_smul_right W n m p (0 : ℂ) u 0
  simpa using this

theorem resExp_zero_left (W : VertexOperatorAlgebra 𝒱) (E : ℤ) (b : 𝒱) :
    resExp W E 0 b = 0 := by
  rw [resExp]
  exact finsum_eq_zero_of_forall_eq_zero fun i => by
    rw [show W.smul 0 (i : ℤ) b = 0 from W.smul_zero_left _ _, smul_zero]

theorem resExp_zero_right (W : VertexOperatorAlgebra 𝒱) (E : ℤ) (a : 𝒱) :
    resExp W E a 0 = 0 := by
  rw [resExp]
  exact finsum_eq_zero_of_forall_eq_zero fun i => by
    rw [show W.smul a (i : ℤ) 0 = 0 from W.smul_zero_right _ _, smul_zero]

theorem resExp_add_right (W : VertexOperatorAlgebra 𝒱) (E : ℤ) (a b₁ b₂ : 𝒱) :
    resExp W E a (b₁ + b₂) = resExp W E a b₁ + resExp W E a b₂ := by
  rw [resExp, resExp, resExp, ← finsum_add_distrib (resExp_support_finite W E a b₁)
    (resExp_support_finite W E a b₂)]
  exact finsum_congr fun i => by
    rw [show W.smul a (i : ℤ) (b₁ + b₂) = W.smul a (i : ℤ) b₁ + W.smul a (i : ℤ) b₂ from
      PreVertexAlgebra.smul_add_right _ _ _ _ _, smul_add]

/-- **Dong–Jiang Lemma 2.3, in full** (`DJ23Comm`), from the residue skew relation
`resHom_skew_mod_Onm` and Appendix Prop 5.1 in coefficient form (`DJ51CoeffD`).

The homogeneous case is `dj23_homog`; the general case follows because every term is `ℂ`-linear in
`b` (`reduce_homogeneous`), and because a vector of negative weight is `0` (VOA `positivity`). -/
theorem dj23Comm_of_dj51 (W : VertexOperatorAlgebra 𝒱) (h51 : DJ51CoeffD) : DJ23Comm W := by
  intro K a ha b m p₁ p₂ N hN
  -- negative weight ⟹ `a = 0`
  rcases lt_or_ge K 0 with hKneg | hKpos
  · have ha0 : a = 0 := by
      have := W.positivity K hKneg
      rw [this, Submodule.mem_bot] at ha
      exact ha
    subst ha0
    rw [anmGen_zero_left, anmGen_zero_right, resExp_zero_left, sub_zero, sub_zero]
    exact (Onm W N m).zero_mem
  · obtain ⟨Kn, rfl⟩ := Int.eq_ofNat_of_zero_le hKpos
    -- reduce `b` to homogeneous
    refine reduce_homogeneous W (P := fun b =>
      anmGen W N m p₁ a b - anmGen W N m p₂ b a
        - resExp W ((Kn : ℤ) - 1 + (m : ℤ) - (p₂ : ℤ)) a b ∈ Onm W N m) ?_ ?_ ?_ b
    · intro Mb b hb
      rcases lt_or_ge Mb 0 with hMneg | hMpos
      · have hb0 : b = 0 := by
          have := W.positivity Mb hMneg
          rw [this, Submodule.mem_bot] at hb
          exact hb
        subst hb0
        rw [anmGen_zero_right, anmGen_zero_left, resExp_zero_right, sub_zero, sub_zero]
        exact (Onm W N m).zero_mem
      · obtain ⟨Mn, rfl⟩ := Int.eq_ofNat_of_zero_le hMpos
        show anmGen W N m p₁ a b - anmGen W N m p₂ b a
            - resExp W ((Kn : ℤ) - 1 + (m : ℤ) - (p₂ : ℤ)) a b ∈ Onm W N m
        exact dj23_homog W h51 ha hb m p₁ p₂ N hN
    · show anmGen W N m p₁ a 0 - anmGen W N m p₂ 0 a
          - resExp W ((Kn : ℤ) - 1 + (m : ℤ) - (p₂ : ℤ)) a 0 ∈ Onm W N m
      rw [anmGen_zero_right, anmGen_zero_left, resExp_zero_right, sub_zero, sub_zero]
      exact (Onm W N m).zero_mem
    · intro x y hx hy
      show anmGen W N m p₁ a (x + y) - anmGen W N m p₂ (x + y) a
          - resExp W ((Kn : ℤ) - 1 + (m : ℤ) - (p₂ : ℤ)) a (x + y) ∈ Onm W N m
      simp only at hx hy
      rw [anmGen_add_right, anmGen_add_left, resExp_add_right]
      have : anmGen W N m p₁ a x + anmGen W N m p₁ a y
          - (anmGen W N m p₂ x a + anmGen W N m p₂ y a)
          - (resExp W ((Kn : ℤ) - 1 + (m : ℤ) - (p₂ : ℤ)) a x
              + resExp W ((Kn : ℤ) - 1 + (m : ℤ) - (p₂ : ℤ)) a y)
        = (anmGen W N m p₁ a x - anmGen W N m p₂ x a
            - resExp W ((Kn : ℤ) - 1 + (m : ℤ) - (p₂ : ℤ)) a x)
          + (anmGen W N m p₁ a y - anmGen W N m p₂ y a
            - resExp W ((Kn : ℤ) - 1 + (m : ℤ) - (p₂ : ℤ)) a y) := by abel
      rw [this]
      exact (Onm W N m).add_mem hx hy

end VOA

/-
`#print axioms` check (each of the following prints `[propext, Classical.choice, Quot.sound]`,
NO `pbw`, NO `sorryAx`):

  #print axioms VOA.resExp_eq_resFull
  #print axioms VOA.dj23_homog
  #print axioms VOA.dj23Comm_of_dj51
-/
