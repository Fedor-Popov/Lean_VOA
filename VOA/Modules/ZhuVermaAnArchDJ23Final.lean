/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDJ23Close
import VOA.Modules.ZhuVermaAnArchDJ51

/-!
# Dong–Jiang Lemma 2.3, unconditional

`ZhuVermaAnArchDJ23Close` reduces DJ Lemma 2.3 to `DJ51CoeffD` — Appendix Proposition 5.1
(`A_{p₁,p₂}(z) = 1`) read coefficientwise *and convolved with `(1+z)^D`*.
`ZhuVermaAnArchDJ51` proves the *unconvolved* form `dj51_coeff` (the coefficient of `z^r` in
`A_{p₁,p₂}(z)` is `δ_{r,0}`).  This file supplies the bridge — a shifted Vandermonde convolution —
and thereby discharges `DJ23Comm` outright:

* `cbz_shift_convol` — `C(D+A, ℓ+σ) = ∑_r C(A, r+σ)·C(D, ℓ−r)` (`cbz_vandermonde`, reindexed);
* `finsetSum_cbz_shift_convol` — the same for a finite combination;
* `dj51CoeffD_holds : DJ51CoeffD` — `dj51_coeff` convolved with `C(D, ·)`;
* **`dj23Comm_holds : DJ23Comm W`** — Dong–Jiang Lemma 2.3, unconditional;
* **`anmGen_commutator_interior_uncond`**, **`oFullU_commutator_interior_tmul_uncond`** — the
  representative- and operator-level `M(U)` commutator (DJ Lemma 4.7, interior regime), free of
  every carried hypothesis.

Multiplying `A_{p₁,p₂}(z) = 1` by `(1+z)^D` is, coefficientwise, exactly this convolution: the
`z^r`-coefficient of `A` pairs with the `z^{ℓ−r}`-coefficient of `(1+z)^D`, and only `r = 0`
survives.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References
Dong–Jiang math/0601626 §2 (Lemma 2.3), Appendix (Prop 5.1), §4 (Lemma 4.7);
`ZhuVermaAnArchDJ23Close` (`DJ51CoeffD`, `dj23Comm_of_dj51`), `ZhuVermaAnArchDJ51` (`dj51_coeff`),
`Foundations/IotaZExpansion` (`cbz_vandermonde`, `cbzConvol`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The shifted Vandermonde convolution. -/

/-- The convolution family `r ↦ C(A, r+σ)·C(D, ℓ−r)` is supported in `Set.Icc (−σ) ℓ`. -/
theorem convolFam_finite (A D ℓ σ : ℤ) :
    (Function.support fun r : ℤ => cbz A (r + σ) * cbz D (ℓ - r)).Finite := by
  refine Set.Finite.subset (Set.finite_Icc (-σ) ℓ) ?_
  intro r hr
  rw [Function.mem_support] at hr
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · by_contra h
    push_neg at h
    exact hr (by rw [cbz_apply_neg A (by omega), zero_mul])
  · by_contra h
    push_neg at h
    exact hr (by rw [cbz_apply_neg D (by omega), mul_zero])

/-- **Shifted Vandermonde**: `C(D+A, ℓ+σ) = ∑_r C(A, r+σ)·C(D, ℓ−r)`. -/
theorem cbz_shift_convol (A D ℓ σ : ℤ) :
    cbz (D + A) (ℓ + σ) = ∑ᶠ r : ℤ, cbz A (r + σ) * cbz D (ℓ - r) := by
  have h := cbz_vandermonde A D (ℓ + σ)
  rw [cbzConvol] at h
  calc cbz (D + A) (ℓ + σ) = cbz (A + D) (ℓ + σ) := by rw [add_comm]
    _ = ∑ᶠ ρ : ℤ, cbz A ρ * cbz D ((ℓ + σ) - ρ) := h.symm
    _ = ∑ᶠ r : ℤ, (fun ρ : ℤ => cbz A ρ * cbz D ((ℓ + σ) - ρ)) (Equiv.addRight σ r) :=
        (finsum_comp_equiv (Equiv.addRight σ)
          (f := fun ρ : ℤ => cbz A ρ * cbz D ((ℓ + σ) - ρ))).symm
    _ = ∑ᶠ r : ℤ, cbz A (r + σ) * cbz D (ℓ - r) := by
        refine finsum_congr fun r => ?_
        show cbz A (r + σ) * cbz D ((ℓ + σ) - (r + σ)) = _
        rw [show ((ℓ + σ) - (r + σ) : ℤ) = ℓ - r from by ring]

/-- A finite `ℂ`-combination of shifted Vandermondes, read as a single convolution. -/
theorem finsetSum_cbz_shift_convol {ι : Type*} (S : Finset ι) (c : ι → ℂ) (A σ : ι → ℤ)
    (D ℓ : ℤ) :
    (∑ i ∈ S, c i * cbz (D + A i) (ℓ + σ i))
      = ∑ᶠ r : ℤ, (∑ i ∈ S, c i * cbz (A i) (r + σ i)) * cbz D (ℓ - r) := by
  have hterm : ∀ i : ι, c i * cbz (D + A i) (ℓ + σ i)
      = ∑ᶠ r : ℤ, (c i * cbz (A i) (r + σ i)) * cbz D (ℓ - r) := by
    intro i
    rw [cbz_shift_convol (A i) D ℓ (σ i), ← smul_eq_mul,
      smul_finsum' _ (convolFam_finite (A i) D ℓ (σ i))]
    exact finsum_congr fun r => by rw [smul_eq_mul, mul_assoc]
  have hfin : ∀ i ∈ S, (Function.support fun r : ℤ =>
      (c i * cbz (A i) (r + σ i)) * cbz D (ℓ - r)).Finite := by
    intro i _
    refine Set.Finite.subset (convolFam_finite (A i) D ℓ (σ i)) ?_
    intro r hr
    rw [Function.mem_support] at hr ⊢
    intro hz
    exact hr (by rw [mul_assoc, hz, mul_zero])
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← finsum_finsetSum_comm' (𝒱 := ℂ) S _ hfin]
  exact finsum_congr fun r => by rw [Finset.sum_mul]

/-- The outer convolution family is finitely supported, given an upper bound on the shifts. -/
theorem convolSum_finite {ι : Type*} (S : Finset ι) (c : ι → ℂ) (A σ : ι → ℤ) (D ℓ Sb : ℤ)
    (hSb : ∀ i ∈ S, σ i ≤ Sb) :
    (Function.support fun r : ℤ =>
      (∑ i ∈ S, c i * cbz (A i) (r + σ i)) * cbz D (ℓ - r)).Finite := by
  refine Set.Finite.subset (Set.finite_Icc (-Sb) ℓ) ?_
  intro r hr
  rw [Function.mem_support] at hr
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · by_contra h
    push_neg at h
    refine hr ?_
    rw [Finset.sum_eq_zero, zero_mul]
    intro i hi
    rw [cbz_apply_neg (A i) (by have := hSb i hi; omega), mul_zero]
  · by_contra h
    push_neg at h
    exact hr (by rw [cbz_apply_neg D (by omega), mul_zero])

/-! ## `DJ51CoeffD` from `dj51_coeff`. -/

/-- **Appendix Prop 5.1 in convolved coefficient form** — `dj51_coeff` convolved with
`C(D, ·)`. -/
theorem dj51CoeffD_holds : DJ51CoeffD := by
  intro D p₁ p₂ ℓ
  -- the two convolved sums
  have hg1 : (∑ i ∈ Finset.range (p₁ + 1),
        (-1 : ℂ) ^ i * cbz ((p₂ : ℤ) + (i : ℤ)) (i : ℤ)
          * cbz (D + (p₂ : ℤ) + 1) (ℓ + ((p₂ : ℤ) + (i : ℤ) + 1)))
      = ∑ᶠ r : ℤ, (∑ i ∈ Finset.range (p₁ + 1),
          ((-1 : ℂ) ^ i * cbz ((p₂ : ℤ) + (i : ℤ)) (i : ℤ))
            * cbz ((p₂ : ℤ) + 1) (r + ((p₂ : ℤ) + (i : ℤ) + 1))) * cbz D (ℓ - r) := by
    rw [← finsetSum_cbz_shift_convol (Finset.range (p₁ + 1))
      (fun i => (-1 : ℂ) ^ i * cbz ((p₂ : ℤ) + (i : ℤ)) (i : ℤ))
      (fun _ => (p₂ : ℤ) + 1) (fun i => (p₂ : ℤ) + (i : ℤ) + 1) D ℓ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (D + (p₂ : ℤ) + 1) = D + ((p₂ : ℤ) + 1) from by ring]
  have hg2 : (∑ i ∈ Finset.range (p₂ + 1),
        cbz ((p₁ : ℤ) + (i : ℤ)) (i : ℤ) * cbz (D + (i : ℤ)) (ℓ + ((p₁ : ℤ) + (i : ℤ) + 1)))
      = ∑ᶠ r : ℤ, (∑ i ∈ Finset.range (p₂ + 1),
          cbz ((p₁ : ℤ) + (i : ℤ)) (i : ℤ) * cbz (i : ℤ) (r + ((p₁ : ℤ) + (i : ℤ) + 1)))
            * cbz D (ℓ - r) :=
    finsetSum_cbz_shift_convol (Finset.range (p₂ + 1))
      (fun i => cbz ((p₁ : ℤ) + (i : ℤ)) (i : ℤ)) (fun i => (i : ℤ))
      (fun i => (p₁ : ℤ) + (i : ℤ) + 1) D ℓ
  -- finiteness of both outer families
  have hf1 := convolSum_finite (Finset.range (p₁ + 1))
    (fun i => (-1 : ℂ) ^ i * cbz ((p₂ : ℤ) + (i : ℤ)) (i : ℤ))
    (fun _ => (p₂ : ℤ) + 1) (fun i => (p₂ : ℤ) + (i : ℤ) + 1) D ℓ
    ((p₂ : ℤ) + (p₁ : ℤ) + 1)
    (fun i hi => by
      rw [Finset.mem_range] at hi
      have hle : (i : ℤ) ≤ (p₁ : ℤ) := by exact_mod_cast Nat.lt_succ_iff.mp hi
      show ((p₂ : ℤ) + (i : ℤ) + 1) ≤ (p₂ : ℤ) + (p₁ : ℤ) + 1
      omega)
  have hf2 := convolSum_finite (Finset.range (p₂ + 1))
    (fun i => cbz ((p₁ : ℤ) + (i : ℤ)) (i : ℤ)) (fun i => (i : ℤ))
    (fun i => (p₁ : ℤ) + (i : ℤ) + 1) D ℓ ((p₁ : ℤ) + (p₂ : ℤ) + 1)
    (fun i hi => by
      rw [Finset.mem_range] at hi
      have hle : (i : ℤ) ≤ (p₂ : ℤ) := by exact_mod_cast Nat.lt_succ_iff.mp hi
      show ((p₁ : ℤ) + (i : ℤ) + 1) ≤ (p₁ : ℤ) + (p₂ : ℤ) + 1
      omega)
  -- pull the outer sign inside
  have hscale : ((-1 : ℂ) ^ p₁) * (∑ᶠ r : ℤ, (∑ i ∈ Finset.range (p₂ + 1),
        cbz ((p₁ : ℤ) + (i : ℤ)) (i : ℤ) * cbz (i : ℤ) (r + ((p₁ : ℤ) + (i : ℤ) + 1)))
          * cbz D (ℓ - r))
      = ∑ᶠ r : ℤ, ((-1 : ℂ) ^ p₁ * ∑ i ∈ Finset.range (p₂ + 1),
        cbz ((p₁ : ℤ) + (i : ℤ)) (i : ℤ) * cbz (i : ℤ) (r + ((p₁ : ℤ) + (i : ℤ) + 1)))
          * cbz D (ℓ - r) := by
    rw [← smul_eq_mul, smul_finsum' _ hf2]
    exact finsum_congr fun r => by rw [smul_eq_mul, mul_assoc]
  have hf2' : (Function.support fun r : ℤ =>
      ((-1 : ℂ) ^ p₁ * ∑ i ∈ Finset.range (p₂ + 1),
        cbz ((p₁ : ℤ) + (i : ℤ)) (i : ℤ) * cbz (i : ℤ) (r + ((p₁ : ℤ) + (i : ℤ) + 1)))
          * cbz D (ℓ - r)).Finite := by
    refine Set.Finite.subset hf2 ?_
    intro r hr
    rw [Function.mem_support] at hr ⊢
    intro hz
    exact hr (by rw [mul_assoc, hz, mul_zero])
  rw [hg1, hg2, hscale, ← finsum_sub_distrib hf1 hf2']
  -- the coefficientwise cancellation is `dj51_coeff`
  have hδ : ∀ r : ℤ, (∑ i ∈ Finset.range (p₁ + 1),
        ((-1 : ℂ) ^ i * cbz ((p₂ : ℤ) + (i : ℤ)) (i : ℤ))
          * cbz ((p₂ : ℤ) + 1) (r + ((p₂ : ℤ) + (i : ℤ) + 1))) * cbz D (ℓ - r)
      - ((-1 : ℂ) ^ p₁ * ∑ i ∈ Finset.range (p₂ + 1),
          cbz ((p₁ : ℤ) + (i : ℤ)) (i : ℤ) * cbz (i : ℤ) (r + ((p₁ : ℤ) + (i : ℤ) + 1)))
            * cbz D (ℓ - r)
      = (if r = 0 then (1 : ℂ) else 0) * cbz D (ℓ - r) := by
    intro r
    rw [← sub_mul]
    congr 1
    have e1 : (∑ i ∈ Finset.range (p₁ + 1),
        ((-1 : ℂ) ^ i * cbz ((p₂ : ℤ) + (i : ℤ)) (i : ℤ))
          * cbz ((p₂ : ℤ) + 1) (r + ((p₂ : ℤ) + (i : ℤ) + 1)))
      = ∑ i ∈ Finset.range (p₁ + 1),
        (-1 : ℂ) ^ i * cbz ((p₂ : ℤ) + (i : ℤ)) (i : ℤ)
          * cbz ((p₂ : ℤ) + 1) (r + (p₂ : ℤ) + (i : ℤ) + 1) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show (r + ((p₂ : ℤ) + (i : ℤ) + 1)) = r + (p₂ : ℤ) + (i : ℤ) + 1 from by ring]
    have e2 : ((-1 : ℂ) ^ p₁ * ∑ i ∈ Finset.range (p₂ + 1),
        cbz ((p₁ : ℤ) + (i : ℤ)) (i : ℤ) * cbz (i : ℤ) (r + ((p₁ : ℤ) + (i : ℤ) + 1)))
      = ∑ i ∈ Finset.range (p₂ + 1),
        (-1 : ℂ) ^ p₁ * cbz ((p₁ : ℤ) + (i : ℤ)) (i : ℤ)
          * cbz (i : ℤ) (r + (p₁ : ℤ) + (i : ℤ) + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show (r + ((p₁ : ℤ) + (i : ℤ) + 1)) = r + (p₁ : ℤ) + (i : ℤ) + 1 from by ring,
        ← mul_assoc]
    rw [e1, e2]
    exact dj51_coeff p₁ p₂ r
  rw [finsum_congr hδ]
  rw [finsum_eq_single _ 0 (fun r hr => by rw [if_neg hr, zero_mul])]
  rw [if_pos rfl, one_mul, sub_zero]

/-! ## Dong–Jiang Lemma 2.3, unconditional. -/

/-- **DONG–JIANG LEMMA 2.3, unconditional.**  For homogeneous `a` of weight `K` and
`p₁ + p₂ − m = N ≥ 0`,

  `a ∗^N_{m,p₁} b − b ∗^N_{m,p₂} a − Res_z (1+z)^{K−1+m−p₂} Y(a,z)b ∈ O'_{N,m}(𝒱)`.

Proved from the residue form of skew symmetry modulo the ideal (`resHom_skew_mod_Onm`, itself from
the `L₋₁`-tower collapse of VOA skew symmetry) together with Appendix Prop 5.1 (`dj51_coeff`).
**No Möbius substitution `z ↦ −z/(1+z)` is used anywhere.** -/
theorem dj23Comm_holds (W : VertexOperatorAlgebra 𝒱) : DJ23Comm W :=
  dj23Comm_of_dj51 W dj51CoeffD_holds

/-! ## The `M(U)` commutator (DJ Lemma 4.7, interior regime), unconditional. -/

/-- **The representative-level `M(U)` commutator, unconditional** (interior regime). -/
theorem anmGen_commutator_interior_uncond (W : VertexOperatorAlgebra 𝒱)
    {K : ℤ} {a : 𝒱} (ha : a ∈ W.grading K) (b : 𝒱) {n n₁ n₂ N : ℕ} {p : ℤ}
    (hN : (N : ℤ) = (n₁ : ℤ) + (n₂ : ℤ) - (n : ℤ)) (hp : p = K - 1 + (n : ℤ) - (n₂ : ℤ)) (g : 𝒱) :
    anmGen W N 0 n₁ a (anmGen W n₁ 0 n b g) - anmGen W N 0 n₂ b (anmGen W n₂ 0 n a g)
        - ∑ᶠ i : ℕ, gBinom p i • anmGen W N 0 n (W.smul a i b) g
      ∈ OnmFull W N 0 :=
  anmGen_commutator_interior W (dj23Comm_holds W) ha b hN hp g

/-- **The operator-level `M(U)` commutator on generators, unconditional** (interior regime):
`a_p b_q ([g]⊗w) − b_q a_p ([g]⊗w) = ∑ᵢ C(p,i)·(a₍ᵢ₎b)_{p+q−i}([g]⊗w)`. -/
theorem oFullU_commutator_interior_tmul_uncond (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    {K : ℤ} {a : 𝒱} (ha : a ∈ W.grading K) (b : 𝒱) {n n₁ n₂ N : ℕ} {p : ℤ}
    (hN : (N : ℤ) = (n₁ : ℤ) + (n₂ : ℤ) - (n : ℤ)) (hp : p = K - 1 + (n : ℤ) - (n₂ : ℤ))
    (g : 𝒱) (w : U.carrier) :
    oFullU W U N n₁ a (oFullU W U n₁ n b (mkAnmFull W n 0 g ⊗ₜ[ℂ] w))
        - oFullU W U N n₂ b (oFullU W U n₂ n a (mkAnmFull W n 0 g ⊗ₜ[ℂ] w))
      = ∑ᶠ i : ℕ, gBinom p i • oFullU W U N n (W.smul a i b) (mkAnmFull W n 0 g ⊗ₜ[ℂ] w) :=
  oFullU_commutator_interior_tmul W U (dj23Comm_holds W) ha b hN hp g w

end VOA

/-
`#print axioms` check (each of the following prints `[propext, Classical.choice, Quot.sound]`,
NO `pbw`, NO `sorryAx`):

  #print axioms VOA.cbz_shift_convol
  #print axioms VOA.dj51CoeffD_holds
  #print axioms VOA.dj23Comm_holds
  #print axioms VOA.anmGen_commutator_interior_uncond
  #print axioms VOA.oFullU_commutator_interior_tmul_uncond
-/
