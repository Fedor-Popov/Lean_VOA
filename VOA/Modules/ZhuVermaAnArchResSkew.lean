/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchSkewModOnm
import VOA.Modules.ZhuVermaAnArchAltVandermonde
import VOA.Modules.ZhuVermaAnBimodule

/-!
# The **residue form** of skew symmetry modulo the Dong–Jiang ideal

`ZhuVermaAnArchSkewModOnm` proves the *mode* form of Dong–Jiang's skew relation,
`v₍t₎u ≡ sgn(t+1)·∑ⱼ C(E,j)·u₍t+j₎v (mod O'_{N,m})`.  This file packages it into the *residue*
form that Dong–Jiang's Lemma 2.3 actually consumes:

  **`resHom_skew_mod_Onm`** :
  `Res_z (1+z)^{wt v+m}/z^P Y(v,z)u  ≡  (−1)^{P+1} · Res_z (1+z)^{wt u+P−N−2}/z^P Y(u,z)v`
  `(mod O'_{N,m})`,

i.e. **swapping the two arguments of a residue costs only a sign and a shift of the `(1+z)`
exponent** — no `p₁`, `p₂` appear.  This is the whole content of DJ's `−z/(1+z)` contour move.

Because the shifted exponent `wt u + P − N − 2` can be negative, the right-hand side is written with
`resFull` (the honest `Res_z (1+z)^E/z^P Y(u,z)v = ∑_ℓ C(E, ℓ+P)·u₍ℓ₎v`, a `ℤ`-indexed `finsum`)
rather than the repo's `resHom`, whose summation range `Finset.range ((wt u + s).toNat + 1)` is only
correct for nonnegative total exponent.  `resHom_eq_resFull` identifies the two whenever the total
exponent is nonnegative (always the case for `resHom W m …`, `m : ℕ`).

The scalar engine is `cbz_alt_vandermonde` (`ZhuVermaAnArchAltVandermonde`); the whole computation
was engine-verified before formalizing (`0` failures over `0 ≤ wt u, wt v ≤ 4`, `0 ≤ m, N ≤ 3/4`,
`−4 ≤ P ≤ 8`, `−4 ≤ ℓ ≤ 8`).

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References
Dong–Jiang math/0601626 §2 (Lemma 2.3); `ZhuVermaAnArchSkewModOnm` (`skew_mod_Onm`),
`ZhuVermaAnArchAltVandermonde` (`cbz_alt_vandermonde`), `ZhuVermaAnBimodule` (`resHom`,
`resHom_homogeneous`), `Core/WeakAssoc` (`finsum_nat_to_int`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## `sgn` is a parity character. -/

theorem sgn_add (a b : ℤ) : sgn (a + b) = sgn a * sgn b := by
  unfold sgn
  by_cases ha : Even a <;> by_cases hb : Even b
  · rw [if_pos ha, if_pos hb, if_pos (ha.add hb)]; ring
  · rw [if_pos ha, if_neg hb, if_neg (fun h => hb (by simpa using h.sub ha))]; ring
  · rw [if_neg ha, if_pos hb, if_neg (fun h => ha (by simpa using h.sub hb))]; ring
  · rw [if_neg ha, if_neg hb, if_pos (Int.even_add.mpr (by simp [ha, hb]))]; ring

/-! ## The honest residue `resFull`. -/

/-- **The full residue** `Res_z (1+z)^E/z^P Y(u,z)v = ∑_{ℓ∈ℤ} C(E, ℓ+P)·u₍ℓ₎v`.

Unlike `resHom W s P u v`, whose summation range `Finset.range ((wt u + s).toNat + 1)` truncates
correctly only when `wt u + s ≥ 0`, this is valid for every integer exponent `E`; the sum is finite
because `C(E, ℓ+P) = 0` for `ℓ < −P` and `u₍ℓ₎v = 0` for `ℓ` large (VOA regularity). -/
noncomputable def resFull (W : VertexOperatorAlgebra 𝒱) (E P : ℤ) (u v : 𝒱) : 𝒱 :=
  ∑ᶠ ℓ : ℤ, cbz E (ℓ + P) • W.smul u ℓ v

theorem resFull_support_finite (W : VertexOperatorAlgebra 𝒱) (E P : ℤ) (u v : 𝒱) :
    (Function.support fun ℓ : ℤ => cbz E (ℓ + P) • W.smul u ℓ v).Finite := by
  obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero u v
  refine Set.Finite.subset (Set.finite_Icc (-P) Nz) ?_
  intro ℓ hℓ
  rw [Function.mem_support] at hℓ
  rw [Set.mem_Icc]
  constructor
  · by_contra hlt
    push_neg at hlt
    exact hℓ (by rw [cbz_apply_neg E (by omega), zero_smul])
  · by_contra hgt
    push_neg at hgt
    exact hℓ (by rw [hNz ℓ (by omega), smul_zero])

/-- On a nonnegative total exponent, `resHom` **is** `resFull`. -/
theorem resHom_eq_resFull (W : VertexOperatorAlgebra 𝒱) {K s : ℕ} {u : 𝒱}
    (hu : u ∈ W.grading (K : ℤ)) (P : ℤ) (v : 𝒱) :
    resHom W (s : ℤ) P u v = resFull W ((K : ℤ) + (s : ℤ)) P u v := by
  rw [resHom_homogeneous W (s : ℤ) P hu v]
  have hsub : (Function.support fun i : ℕ =>
      cbz ((K : ℤ) + (s : ℤ)) (i : ℤ) • W.smul u ((i : ℤ) - P) v)
      ⊆ ↑(Finset.range (((K : ℤ) + (s : ℤ)).toNat + 1)) := by
    intro i hi
    rw [Function.mem_support] at hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hcon
    push_neg at hcon
    refine hi ?_
    rw [cbz_lt (by positivity) (by omega), zero_smul]
  calc ∑ i ∈ Finset.range (((K : ℤ) + (s : ℤ)).toNat + 1),
        cbz ((K : ℤ) + (s : ℤ)) (i : ℤ) • W.smul u ((i : ℤ) - P) v
      = ∑ᶠ i : ℕ, cbz ((K : ℤ) + (s : ℤ)) (i : ℤ) • W.smul u ((i : ℤ) - P) v :=
        (finsum_eq_sum_of_support_subset _ hsub).symm
    _ = ∑ᶠ p : ℤ, cbz ((K : ℤ) + (s : ℤ)) p • W.smul u (p - P) v :=
        finsum_nat_to_int _ _ (fun p hp => by rw [cbz_apply_neg _ hp, zero_smul]) (fun _ => rfl)
    _ = ∑ᶠ p : ℤ, (fun ℓ : ℤ => cbz ((K : ℤ) + (s : ℤ)) (ℓ + P) • W.smul u ℓ v)
          (Equiv.subRight P p) := by
        refine finsum_congr fun p => ?_
        show _ = cbz ((K : ℤ) + (s : ℤ)) ((p - P) + P) • W.smul u (p - P) v
        rw [show ((p - P) + P : ℤ) = p from by ring]
    _ = ∑ᶠ ℓ : ℤ, cbz ((K : ℤ) + (s : ℤ)) (ℓ + P) • W.smul u ℓ v :=
        finsum_comp_equiv (Equiv.subRight P)
          (f := fun ℓ : ℤ => cbz ((K : ℤ) + (s : ℤ)) (ℓ + P) • W.smul u ℓ v)
    _ = resFull W ((K : ℤ) + (s : ℤ)) P u v := rfl

/-! ## The mode-form skew, restated with `resFull`. -/

/-- `skew_mod_Onm` with the `ℕ`-indexed tail rewritten as the `ℤ`-indexed `resFull`. -/
theorem skew_mod_Onm_resFull (W : VertexOperatorAlgebra 𝒱) (N m : ℕ) {K M : ℕ} {u v : 𝒱}
    (hu : u ∈ W.grading (K : ℤ)) (hv : v ∈ W.grading (M : ℤ)) (t : ℤ) :
    W.smul v t u
        - sgn (t + 1) •
            resFull W ((K : ℤ) + (M : ℤ) - 2 + (m : ℤ) - (N : ℤ) - t) (-t) u v
      ∈ Onm W N m := by
  have h := skew_mod_Onm W N m hu hv t
  set E : ℤ := (K : ℤ) + (M : ℤ) - 2 + (m : ℤ) - (N : ℤ) - t with hE
  have hconv : (∑ᶠ j : ℕ, cbz E (j : ℤ) • W.smul u (t + (j : ℤ)) v)
      = resFull W E (-t) u v := by
    calc (∑ᶠ j : ℕ, cbz E (j : ℤ) • W.smul u (t + (j : ℤ)) v)
        = ∑ᶠ p : ℤ, cbz E p • W.smul u (t + p) v :=
          finsum_nat_to_int _ _ (fun p hp => by rw [cbz_apply_neg _ hp, zero_smul]) (fun _ => rfl)
      _ = ∑ᶠ p : ℤ, (fun ℓ : ℤ => cbz E (ℓ + -t) • W.smul u ℓ v) (Equiv.addLeft t p) := by
          refine finsum_congr fun p => ?_
          show _ = cbz E ((t + p) + -t) • W.smul u (t + p) v
          rw [show ((t + p) + -t : ℤ) = p from by ring]
      _ = ∑ᶠ ℓ : ℤ, cbz E (ℓ + -t) • W.smul u ℓ v :=
          finsum_comp_equiv (Equiv.addLeft t)
            (f := fun ℓ : ℤ => cbz E (ℓ + -t) • W.smul u ℓ v)
      _ = resFull W E (-t) u v := rfl
  rwa [hconv] at h

/-! ## Interchange of a `Finset.sum` with a `finsum`. -/

theorem finsum_finsetSum_comm' {ι : Type*} (S : Finset ι) (g : ι → ℤ → 𝒱)
    (hg : ∀ i ∈ S, (Function.support (g i)).Finite) :
    (∑ᶠ q : ℤ, ∑ i ∈ S, g i q) = ∑ i ∈ S, ∑ᶠ q : ℤ, g i q := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a S ha ih =>
      have hga : (Function.support (g a)).Finite := hg a (Finset.mem_insert_self a S)
      have hgs : ∀ i ∈ S, (Function.support (g i)).Finite :=
        fun i hi => hg i (Finset.mem_insert_of_mem hi)
      have hsum_fin : (Function.support (fun q => ∑ i ∈ S, g i q)).Finite := by
        refine Set.Finite.subset (Set.Finite.biUnion (Finset.finite_toSet S)
          (fun i _ => hgs i (by simpa using ‹i ∈ S›))) ?_
        intro q hq
        rw [Function.mem_support] at hq
        by_contra hcon
        refine hq (Finset.sum_eq_zero fun i hi => ?_)
        by_contra hne
        exact hcon (Set.mem_biUnion (by simpa using hi) (Function.mem_support.mpr hne))
      rw [Finset.sum_insert ha, ← ih hgs]
      rw [← finsum_add_distrib hga hsum_fin]
      exact finsum_congr fun q => by rw [Finset.sum_insert ha]

/-! ## Sign helper. -/

theorem sgn_one_sub (P : ℤ) : sgn (1 - P) = sgn (P + 1) := by
  have h : sgn (P + 1) = sgn ((1 - P) + (P + P)) := by
    congr 1
    ring
  rw [h, sgn_add, sgn_add P P, sgn_mul_self, mul_one]

/-! ## The headline: the residue form of skew symmetry modulo `O'_{N,m}`. -/

/-- **The residue form of skew symmetry modulo `O'_{N,m}`** (Dong–Jiang's Lemma 2.3 skew step):

  `Res_z (1+z)^{wt v+m}/z^P Y(v,z)u ≡ (−1)^{P+1}·Res_z (1+z)^{wt u+P−N−2}/z^P Y(u,z)v`
  `(mod O'_{N,m})`.

Swapping the two arguments of a residue costs exactly a sign `(−1)^{P+1}` and the exponent shift
`wt v + m ↝ wt u + P − N − 2`.  Proved from `skew_mod_Onm_resFull` (the `L₋₁`-tower collapse of VOA
skew symmetry) together with `cbz_alt_vandermonde`; **no Möbius substitution is used**. -/
theorem resHom_skew_mod_Onm (W : VertexOperatorAlgebra 𝒱) (N m : ℕ) {K M : ℕ} {u v : 𝒱}
    (hu : u ∈ W.grading (K : ℤ)) (hv : v ∈ W.grading (M : ℤ)) (P : ℤ) :
    resHom W (m : ℤ) P v u
        - sgn (P + 1) • resFull W ((K : ℤ) + P - (N : ℤ) - 2) P u v
      ∈ Onm W N m := by
  classical
  set A : ℤ := (M : ℤ) + (m : ℤ) with hA
  set S : Finset ℕ := Finset.range (A.toNat + 1) with hS
  -- the per-`s` skew congruence, scaled by the residue binomial
  have hmem : ∀ s ∈ S,
      cbz A (s : ℤ) • W.smul v ((s : ℤ) - P) u
        - (cbz A (s : ℤ) * sgn (((s : ℤ) - P) + 1)) •
            resFull W ((K : ℤ) + (M : ℤ) - 2 + (m : ℤ) - (N : ℤ) - ((s : ℤ) - P))
              (-((s : ℤ) - P)) u v ∈ Onm W N m := by
    intro s _
    have h := Submodule.smul_mem (Onm W N m) (cbz A (s : ℤ))
      (skew_mod_Onm_resFull W N m hu hv ((s : ℤ) - P))
    rwa [smul_sub, smul_smul] at h
  -- sum the congruences over the residue's finite range
  have hsum : resHom W (m : ℤ) P v u
      - ∑ s ∈ S, (cbz A (s : ℤ) * sgn (((s : ℤ) - P) + 1)) •
          resFull W ((K : ℤ) + (M : ℤ) - 2 + (m : ℤ) - (N : ℤ) - ((s : ℤ) - P))
            (-((s : ℤ) - P)) u v ∈ Onm W N m := by
    rw [resHom_homogeneous W (m : ℤ) P hv u, ← Finset.sum_sub_distrib]
    exact Submodule.sum_mem _ hmem
  -- the remaining identity is pure scalar combinatorics
  have hid : (∑ s ∈ S, (cbz A (s : ℤ) * sgn (((s : ℤ) - P) + 1)) •
        resFull W ((K : ℤ) + (M : ℤ) - 2 + (m : ℤ) - (N : ℤ) - ((s : ℤ) - P))
          (-((s : ℤ) - P)) u v)
      = sgn (P + 1) • resFull W ((K : ℤ) + P - (N : ℤ) - 2) P u v := by
    -- expand every `resFull` and interchange
    have hexp : ∀ s : ℕ,
        (cbz A (s : ℤ) * sgn (((s : ℤ) - P) + 1)) •
          resFull W ((K : ℤ) + (M : ℤ) - 2 + (m : ℤ) - (N : ℤ) - ((s : ℤ) - P))
            (-((s : ℤ) - P)) u v
        = ∑ᶠ ℓ : ℤ, (cbz A (s : ℤ) * sgn (((s : ℤ) - P) + 1) *
            cbz ((K : ℤ) + (M : ℤ) - 2 + (m : ℤ) - (N : ℤ) - ((s : ℤ) - P))
              (ℓ + -((s : ℤ) - P))) • W.smul u ℓ v := by
      intro s
      rw [resFull, smul_finsum' _ (resFull_support_finite W _ _ u v)]
      exact finsum_congr fun ℓ => by rw [smul_smul]
    have hfin : ∀ s ∈ S, (Function.support fun ℓ : ℤ =>
        (cbz A (s : ℤ) * sgn (((s : ℤ) - P) + 1) *
          cbz ((K : ℤ) + (M : ℤ) - 2 + (m : ℤ) - (N : ℤ) - ((s : ℤ) - P))
            (ℓ + -((s : ℤ) - P))) • W.smul u ℓ v).Finite := by
      intro s _
      refine Set.Finite.subset (resFull_support_finite W
        ((K : ℤ) + (M : ℤ) - 2 + (m : ℤ) - (N : ℤ) - ((s : ℤ) - P)) (-((s : ℤ) - P)) u v) ?_
      intro ℓ hℓ
      rw [Function.mem_support] at hℓ ⊢
      intro hz
      exact hℓ (by rw [← smul_smul, hz, smul_zero])
    rw [Finset.sum_congr rfl (fun s _ => hexp s), ← finsum_finsetSum_comm' S _ hfin]
    rw [resFull, smul_finsum' _ (resFull_support_finite W _ _ u v)]
    refine finsum_congr fun ℓ => ?_
    rw [← Finset.sum_smul, smul_smul]
    congr 1
    -- the scalar identity: alternating Vandermonde
    have hcoe : ∀ s : ℕ, cbz A (s : ℤ) * sgn (((s : ℤ) - P) + 1) *
          cbz ((K : ℤ) + (M : ℤ) - 2 + (m : ℤ) - (N : ℤ) - ((s : ℤ) - P))
            (ℓ + -((s : ℤ) - P))
        = sgn (P + 1) * (sgn (s : ℤ) * cbz A (s : ℤ) *
            cbz (((K : ℤ) + (M : ℤ) - 2 + (m : ℤ) - (N : ℤ) + P) - (s : ℤ))
              ((ℓ + P) - (s : ℤ))) := by
      intro s
      rw [show (((s : ℤ) - P) + 1) = (s : ℤ) + (1 - P) from by ring, sgn_add, sgn_one_sub,
        show ((K : ℤ) + (M : ℤ) - 2 + (m : ℤ) - (N : ℤ) - ((s : ℤ) - P))
          = (((K : ℤ) + (M : ℤ) - 2 + (m : ℤ) - (N : ℤ) + P) - (s : ℤ)) from by ring,
        show (ℓ + -((s : ℤ) - P)) = ((ℓ + P) - (s : ℤ)) from by ring]
      ring
    rw [Finset.sum_congr rfl (fun s _ => hcoe s), ← Finset.mul_sum]
    -- extend the `Finset.range` sum to a `ℤ`-`finsum` and apply the Vandermonde
    have hsub : (Function.support fun s : ℕ => sgn (s : ℤ) * cbz A (s : ℤ) *
        cbz (((K : ℤ) + (M : ℤ) - 2 + (m : ℤ) - (N : ℤ) + P) - (s : ℤ))
          ((ℓ + P) - (s : ℤ))) ⊆ ↑S := by
      intro s hs
      rw [Function.mem_support] at hs
      simp only [hS, Finset.coe_range, Set.mem_Iio]
      by_contra hcon
      push_neg at hcon
      refine hs ?_
      rw [cbz_lt (by rw [hA]; positivity) (by omega), mul_zero, zero_mul]
    have hstep : (∑ s ∈ S, sgn (s : ℤ) * cbz A (s : ℤ) *
          cbz (((K : ℤ) + (M : ℤ) - 2 + (m : ℤ) - (N : ℤ) + P) - (s : ℤ)) ((ℓ + P) - (s : ℤ)))
        = ∑ᶠ σ : ℤ, sgn σ * cbz A σ *
            cbz (((K : ℤ) + (M : ℤ) - 2 + (m : ℤ) - (N : ℤ) + P) - σ) ((ℓ + P) - σ) := by
      rw [← finsum_eq_sum_of_support_subset _ hsub]
      exact finsum_nat_to_int _ _
        (fun q hq => by rw [cbz_apply_neg A hq, mul_zero, zero_mul]) (fun _ => rfl)
    rw [hstep]
    have hvan := cbz_alt_vandermonde (M + m)
      ((K : ℤ) + (M : ℤ) - 2 + (m : ℤ) - (N : ℤ) + P) (ℓ + P)
    rw [show ((M + m : ℕ) : ℤ) = A from by rw [hA]; push_cast; ring] at hvan
    rw [hvan, show (((K : ℤ) + (M : ℤ) - 2 + (m : ℤ) - (N : ℤ) + P) - A)
      = ((K : ℤ) + P - (N : ℤ) - 2) from by rw [hA]; ring]
  rwa [hid] at hsum

/-- **A finite combination of `resFull`s, read coefficientwise.**  The workhorse for assembling
Dong–Jiang's Lemma 2.3 out of residues. -/
theorem finsetSum_smul_resFull {ι : Type*} (W : VertexOperatorAlgebra 𝒱) (S : Finset ι)
    (c : ι → ℂ) (E P : ι → ℤ) (u v : 𝒱) :
    (∑ i ∈ S, c i • resFull W (E i) (P i) u v)
      = ∑ᶠ ℓ : ℤ, (∑ i ∈ S, c i * cbz (E i) (ℓ + P i)) • W.smul u ℓ v := by
  have hexp : ∀ i : ι, c i • resFull W (E i) (P i) u v
      = ∑ᶠ ℓ : ℤ, (c i * cbz (E i) (ℓ + P i)) • W.smul u ℓ v := by
    intro i
    rw [resFull, smul_finsum' _ (resFull_support_finite W (E i) (P i) u v)]
    exact finsum_congr fun ℓ => by rw [smul_smul]
  have hfin : ∀ i ∈ S, (Function.support fun ℓ : ℤ =>
      (c i * cbz (E i) (ℓ + P i)) • W.smul u ℓ v).Finite := by
    intro i _
    refine Set.Finite.subset (resFull_support_finite W (E i) (P i) u v) ?_
    intro ℓ hℓ
    rw [Function.mem_support] at hℓ ⊢
    intro hz
    exact hℓ (by rw [← smul_smul, hz, smul_zero])
  rw [Finset.sum_congr rfl (fun i _ => hexp i), ← finsum_finsetSum_comm' S _ hfin]
  exact finsum_congr fun ℓ => by rw [← Finset.sum_smul]

end VOA

/-
`#print axioms` check (each of the following prints `[propext, Classical.choice, Quot.sound]`,
NO `pbw`, NO `sorryAx`):

  #print axioms VOA.resFull
  #print axioms VOA.resHom_eq_resFull
  #print axioms VOA.skew_mod_Onm_resFull
  #print axioms VOA.resHom_skew_mod_Onm
-/
