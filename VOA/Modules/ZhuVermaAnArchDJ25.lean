/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDJ27

/-!
# Dong–Jiang **Lemma 2.5** — the `O'_{p₂,p₁}` circle-generator cross term (`offCirc`)

This file discharges the **`offCirc`** field of `DJ27ChainTail` (`ZhuVermaAnArchDJ27.lean`), the single
genuinely-open residual of Dong–Jiang, *Bimodules associated to vertex operator algebras*, Math. Z.
259 (2008) 799–826 (`math/0601626`), **Lemma 2.5** (the `O'_{p₂,p₁} ∗ V` decomposition step used in
the proof of DJ's Lemma 2.7).

The target is the **`O'_{p₂,p₁}` circle-generator family** of the level-`p₂` cross term:
```
offCirc :  anmGen W n m p₂ a (anmGen W p₂ m p₁ (anmCirc W p₂ p₁ c d) v) ∈ OnmFull W n m
        =  a ∗ⁿ_{m,p₂} ((c ∘^{p₂}_{p₁} d) ∗^{p₂}_{m,p₁} v) ∈ O_{n,m}(V).
```

## DJ's published proof (formalized faithfully here)

This is exactly DJ's `O'_{p₂,p₁} ∗^{p₂}_{m,p₁} V` decomposition (the chain in DJ Lemma 2.7, p. 8,
lines 548–563, restricted to the circle generators of `O'_{p₂,p₁}`).  We follow it verbatim:

1. **DJ Lemma 2.2** (`anmCirc_mem_OnBar`) at level `(p₂, p₁)`: for homogeneous `c`, the inner circle
   generator is a nonzero scalar multiple of the level-`p₂` *grading*-generator product:
   `s₁ · (c ∘^{p₂}_{p₁} d) = (L(−1)c + L(0)c) ∗̄^{p₂}_{p₁} d = (anmLgen W p₂ p₂ c) ∗^{p₂}_{p₁,p₂} d`,
   `s₁ = (p₂+p₁+1)(−1)^{p₂}C(p₂+p₁, p₁) ≠ 0`.  This is DJ's `O'_{p₂,p₁} ⊆ O_{p₂} ∗^{p₂}_{p₁,p₂} V` step.
2. **Reassociate** the inner product (DJ's `(O_{p₂} ∗^{p₂}_{p₁,p₂} V) ∗^{p₂}_{m,p₁} V ⊆
   O_{p₂} ∗^{p₂}_{m,p₂}(V ∗^{p₂}_{m,p₁} V) (mod O)` step): writing `G = anmLgen W p₂ p₂ c`,
   `(G ∗^{p₂}_{p₁,p₂} d) ∗^{p₂}_{m,p₁} v = G ∗^{p₂}_{m,p₂}(d ∗^{p₂}_{m,p₁} v) + Δ`, where
   `Δ` is precisely the **bare associator** (`assocDefect … u = a` after the outer `a ∗ⁿ_{m,p₂}`-wrap),
   so `a ∗ⁿ_{m,p₂} Δ = assocDefect W n m p₁ p₂ p₂ G d v a ∈ O''_{n,m} ⊆ O_{n,m}`
   (`assocDefect_mem_OnmFull`).
3. **DJ Lemma 2.2 again** at level `(p₂, m)` (`anmGenBar_Lgen_eq`): `G ∗^{p₂}_{m,p₂}(d ∗^{p₂}_{m,p₁} v)
   = (L(−1)c + L(0)c) ∗̄^{p₂}_m d' = s₂ · (c ∘^{p₂}_m d')` with `d' = d ∗^{p₂}_{m,p₁} v`.  The outer
   `a ∗ⁿ_{m,p₂}` of this is the **level-`p₂` circle cross term** `circCross_mem W n m p₂ a d' c ∈
   O_{n,m}` (the DJ `(V ∗ⁿ_{p₂} O_{p₂}) ∗ⁿ_{m,p₂} V ⊆ O'''_{n,m}` step, already closed in DJ27).

Adding the two memberships gives the homogeneous `offCirc`; a grade `⊕`-decomposition of `c` (the
DJ 2.2 step needs `c` homogeneous; `a, d, v` are arbitrary) lifts it to general `c`, exactly as
`circCross_mem` lifts `circCross_homog_mem`.  No new combinatorial identity is introduced — every step
is an already-proven DJ feeder (`anmCirc_mem_OnBar` / `anmGenBar_Lgen_eq` / `assocDefect_mem_OnmFull` /
`circCross_mem`) applied at the stated indices.

## What is proved here (axiom-clean; NO `sorry`/`pbw`)

* `offCirc_homog_mem` — the homogeneous `offCirc` membership.
* `offCirc_mem` — the general-`c` `offCirc` membership.
* `dj27ChainTail_holds` — the `DJ27ChainTail` residual, fully discharged (its sole field is `offCirc`).
* `levelMixGen_mem_OnmFull_unconditional` — DJ Lemma 2.7, **unconditional**.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.5, Lemma 2.7); Dong–Li–Mason,
J. Algebra 206 (1998) 67–96.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The DJ 2.2 scalar `(p₂+p₁+1)·(−1)^{p₂}·C(p₂+p₁, p₁)` is nonzero (local copy). -/

/-- The DJ 2.2 scalar `(p₂+m+1)·(−1)^{p₂}·C(p₂+m, m)` is nonzero (the `private` copy in DJ27 is the
same identity; re-stated here so it is usable from this file). -/
private theorem dj25_scalar_ne_zero (m p₂ : ℕ) :
    ((p₂ : ℂ) + (m : ℂ) + 1) * ((-1 : ℂ)) ^ p₂ * cbz ((p₂ : ℤ) + (m : ℤ)) (m : ℤ) ≠ 0 := by
  have hcbz : cbz ((p₂ : ℤ) + (m : ℤ)) (m : ℤ) = ((p₂ + m).choose m : ℂ) := by
    rw [show ((p₂ : ℤ) + (m : ℤ)) = (((p₂ + m : ℕ)) : ℤ) from by push_cast; ring,
        cbz_natCast_eq_choose (by omega)]
  rw [hcbz]
  have h1 : ((p₂ : ℂ) + (m : ℂ) + 1) ≠ 0 := by
    have h : ((p₂ + m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (p₂ + m)
    push_cast at h
    convert h using 1
  have h2 : ((-1 : ℂ)) ^ p₂ ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3 : (((p₂ + m).choose m : ℕ) : ℂ) ≠ 0 := by
    have : (p₂ + m).choose m ≠ 0 := Nat.choose_pos (by omega) |>.ne'
    exact_mod_cast this
  exact mul_ne_zero (mul_ne_zero h1 h2) h3

/-! ## DJ Lemma 2.5 — the homogeneous `offCirc` membership. -/

/-- **DJ Lemma 2.5, homogeneous.**  For homogeneous `c ∈ 𝒱_M`,
`a ∗ⁿ_{m,p₂} ((c ∘^{p₂}_{p₁} d) ∗^{p₂}_{m,p₁} v) ∈ O_{n,m}(𝒱)`.

Following DJ's `O'_{p₂,p₁} ∗^{p₂}_{m,p₁} V` chain: rewrite the inner circle via DJ 2.2
(`anmCirc_mem_OnBar`, `s₁ ≠ 0`) as the level-`p₂` grading-generator product `G ∗^{p₂}_{p₁,p₂} d`
(`G = anmLgen W p₂ p₂ c`), split the inner reassociation into the level-`p₂` *diagonal* product
`G ∗̄^{p₂}_m (d ∗^{p₂}_{m,p₁} v)` plus the bare associator defect, wrap by `a ∗ⁿ_{m,p₂}`; the defect is
an `O''_{n,m}` generator (`assocDefect_mem_OnmFull`) and the diagonal product is, by DJ 2.2 again
(`anmGenBar_Lgen_eq`), a scalar multiple of the level-`p₂` circle cross term, closed by
`circCross_mem`. -/
theorem offCirc_homog_mem (W : VertexOperatorAlgebra 𝒱) (n m p₁ p₂ : ℕ) {M : ℕ} {c : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (a d v : 𝒱) :
    anmGen W n m p₂ a (anmGen W p₂ m p₁ (anmCirc W p₂ p₁ c d) v) ∈ OnmFull W n m := by
  -- abbreviations
  set G : 𝒱 := anmLgen W p₂ p₂ c with hG
  -- `G = L(−1)c + L(0)c` (diagonal grading generator).
  have hGdef : G = W.L (-1) c + W.L 0 c := by rw [hG, anmLgen_diag]
  set d' : 𝒱 := anmGen W p₂ m p₁ d v with hd'
  -- the level-`(p₂,p₁)` DJ 2.2 scalar.
  set s₁ : ℂ := ((p₂ : ℂ) + (p₁ : ℂ) + 1) * ((-1 : ℂ)) ^ p₂ * cbz ((p₂ : ℤ) + (p₁ : ℤ)) (p₁ : ℤ)
    with hs₁
  have hs₁ne : s₁ ≠ 0 := dj25_scalar_ne_zero p₁ p₂
  -- STEP 1 (DJ 2.2 at level (p₂,p₁)): `s₁ • (c ∘^{p₂}_{p₁} d) = G ∗^{p₂}_{p₁,p₂} d`.
  have hbar₁ := anmCirc_mem_OnBar W p₂ p₁ hc d
  -- so `c ∘^{p₂}_{p₁} d = s₁⁻¹ • (anmGen W p₂ p₁ p₂ G d)`.
  have hcirc₁ : anmCirc W p₂ p₁ c d = s₁⁻¹ • anmGen W p₂ p₁ p₂ G d := by
    -- `anmGenBar W p₂ p₁ (L(−1)c+L(0)c) d = anmGen W p₂ p₁ p₂ G d` (definition of `anmGenBar` + `hGdef`).
    have hbarG : anmGenBar W p₂ p₁ (W.L (-1) c + W.L 0 c) d = anmGen W p₂ p₁ p₂ G d := by
      rw [anmGenBar, hGdef]
    rw [hbarG] at hbar₁
    -- `hbar₁ : s₁ • anmCirc W p₂ p₁ c d = anmGen W p₂ p₁ p₂ G d`.
    rw [← hbar₁, smul_smul, inv_mul_cancel₀ hs₁ne, one_smul]
  -- push the inner-circle rewrite all the way out.
  rw [hcirc₁, anmGen_smul_left, anmGen_smul_right]
  refine Submodule.smul_mem _ _ ?_
  -- the residual `anmGen W n m p₂ a (anmGen W p₂ m p₁ (anmGen W p₂ p₁ p₂ G d) v)`.
  set Inner : 𝒱 := anmGen W p₂ m p₁ (anmGen W p₂ p₁ p₂ G d) v with hInner
  set Inner2 : 𝒱 := anmGen W p₂ m p₂ G d' with hInner2
  -- STEP 2: split `Inner = Inner2 + (Inner − Inner2)` and apply `anmGen_add_right`.
  have hsplit : Inner = Inner2 + (Inner - Inner2) := by abel
  rw [hsplit, anmGen_add_right]
  refine (OnmFull W n m).add_mem ?_ ?_
  · -- TERM 1 = `a ∗ⁿ_{m,p₂} (G ∗̄^{p₂}_m d')`; DJ 2.2 (anmGenBar_Lgen_eq) ⟹ scalar • circ ⟹ circCross_mem.
    -- `Inner2 = anmGenBar W p₂ m G d' = anmGenBar W p₂ m (L(−1)c+L(0)c) d'`.
    have hbar₂ : Inner2 = anmGenBar W p₂ m (W.L (-1) c + W.L 0 c) d' := by
      rw [hInner2, anmGenBar, hGdef]
    -- DJ 2.2 at level (p₂,m): `anmGenBar W p₂ m (L(−1)c+L(0)c) d' = s₂ • anmCirc W p₂ m c d'`.
    have hcirc₂ := anmGenBar_Lgen_eq W p₂ m M hc d'
    rw [hbar₂, hcirc₂, anmGen_smul_right]
    exact Submodule.smul_mem _ _ (circCross_mem W n m p₂ a d' c)
  · -- TERM 2 = the bare associator defect, wrapped by `a ∗ⁿ_{m,p₂}` = `assocDefect … a ∈ O''_{n,m}`.
    have hassoc : anmGen W n m p₂ a (Inner - Inner2)
        = assocDefect W n m p₁ p₂ p₂ G d v a := by
      rw [assocDefect, hInner, hInner2, hd']
    rw [hassoc]
    exact assocDefect_mem_OnmFull W n m p₁ p₂ p₂ G d v a

/-! ## DJ Lemma 2.5 — the general-`c` `offCirc` membership (grade `⊕`-decomposition). -/

/-- The `offCirc` cross-term action `c ↦ a ∗ⁿ_{m,p₂}((c ∘^{p₂}_{p₁} d) ∗^{p₂}_{m,p₁} v)` as a
ℂ-linear map in `c` (composition of `anmCirc`-left, `anmGen`-left and `anmGen`-right slot maps). -/
noncomputable def offCircMap (W : VertexOperatorAlgebra 𝒱) (n m p₁ p₂ : ℕ) (a d v : 𝒱) :
    𝒱 →ₗ[ℂ] 𝒱 where
  toFun c := anmGen W n m p₂ a (anmGen W p₂ m p₁ (anmCirc W p₂ p₁ c d) v)
  map_add' c₁ c₂ := by
    simp only [anmCirc_add_left, anmGen_add_left, anmGen_add_right]
  map_smul' r c := by
    simp only [anmCirc_smul_left, anmGen_smul_left, anmGen_smul_right, RingHom.id_apply]

@[simp] theorem offCircMap_apply (W : VertexOperatorAlgebra 𝒱) (n m p₁ p₂ : ℕ) (a d v c : 𝒱) :
    offCircMap W n m p₁ p₂ a d v c
      = anmGen W n m p₂ a (anmGen W p₂ m p₁ (anmCirc W p₂ p₁ c d) v) := rfl

/-- **DJ Lemma 2.5, general `c`.**  `a ∗ⁿ_{m,p₂} ((c ∘^{p₂}_{p₁} d) ∗^{p₂}_{m,p₁} v) ∈ O_{n,m}(𝒱)` for
arbitrary `c` (decompose `c` into homogeneous pieces and apply `offCirc_homog_mem`; the map
`offCircMap` is ℂ-linear in `c`, so each grade contributes a member and lower-than-`0` grades
vanish). -/
theorem offCirc_mem (W : VertexOperatorAlgebra 𝒱) (n m p₁ p₂ : ℕ) (a d v c : 𝒱) :
    anmGen W n m p₂ a (anmGen W p₂ m p₁ (anmCirc W p₂ p₁ c d) v) ∈ OnmFull W n m := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  have hdecomp : ∑ k ∈ (DirectSum.decompose W.grading c).support,
      ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) = c :=
    DirectSum.sum_support_decompose W.grading c
  have hsum : anmGen W n m p₂ a (anmGen W p₂ m p₁ (anmCirc W p₂ p₁ c d) v)
      = ∑ k ∈ (DirectSum.decompose W.grading c).support,
          anmGen W n m p₂ a
            (anmGen W p₂ m p₁
              (anmCirc W p₂ p₁ ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) d) v) := by
    conv_lhs => rw [← offCircMap_apply W n m p₁ p₂ a d v c, ← hdecomp, map_sum]
    rfl
  rw [hsum]
  refine Submodule.sum_mem _ fun k _ => ?_
  have hk : ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) ∈ W.grading k :=
    (DirectSum.decompose W.grading c k).2
  rcases le_or_gt 0 k with hknn | hkneg
  · obtain ⟨M, rfl⟩ := Int.eq_ofNat_of_zero_le hknn
    exact offCirc_homog_mem W n m p₁ p₂ hk a d v
  · -- `k < 0`: the grade is `⊥`, the piece is `0`, the cross term vanishes.
    have hzero : ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) = 0 := by
      have : ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) ∈ (⊥ : Submodule ℂ 𝒱) := by
        rw [← W.positivity k hkneg]; exact hk
      simpa using this
    rw [hzero, show (0 : 𝒱) = (0 : ℂ) • (0 : 𝒱) by rw [zero_smul], anmCirc_smul_left,
        anmGen_smul_left, anmGen_smul_right, zero_smul]
    exact (OnmFull W n m).zero_mem

/-! ## The `DJ27ChainTail` residual, fully discharged. -/

/-- **DJ Lemma 2.5 — the `DJ27ChainTail` residual is satisfied.**  Its sole field `offCirc` is
`offCirc_mem`.  This discharges the genuine remaining content of DJ Lemma 2.7. -/
theorem dj27ChainTail_holds (W : VertexOperatorAlgebra 𝒱) (n m p₁ p₂ : ℕ) (a v : 𝒱) :
    DJ27ChainTail W n m p₁ p₂ a v where
  offCirc c d := offCirc_mem W n m p₁ p₂ a d v c

/-- **DJ Lemma 2.7, unconditional.**  `(a ∗ⁿ_{p₁,p₂} g) ∗ⁿ_{m,p₁} v ∈ O_{n,m}(𝒱)` for
`g ∈ O'_{p₂,p₁}`, with the `DJ27ChainTail` residual discharged by `dj27ChainTail_holds`. -/
theorem levelMixGen_mem_OnmFull_unconditional (W : VertexOperatorAlgebra 𝒱) (n m p₁ p₂ : ℕ)
    (a v : 𝒱) (g : 𝒱) (hg : g ∈ Onm W p₂ p₁) :
    anmGen W n m p₁ (anmGen W n p₁ p₂ a g) v ∈ OnmFull W n m :=
  levelMixGen_mem_OnmFull W n m p₁ p₂ a v g hg (dj27ChainTail_holds W n m p₁ p₂ a v)

end VOA
