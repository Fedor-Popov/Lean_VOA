/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDJ28

/-!
# Dong–Jiang **Lemma 2.8** — the three RIGHT generator branches of `O_{n,p} ∗ⁿ_{m,p} V ⊆ O_{n,m}`

This file discharges the three **right-inclusion** generator families of `DJ28Residual`
(`ZhuVermaAnArchDJ28.lean`), i.e. the `O_{n,p}(V) ∗ⁿ_{m,p} V ⊆ O_{n,m}(V)` half of Dong–Jiang,
*Bimodules associated to vertex operator algebras*, Math. Z. 259 (2008) 799–826 (`math/0601626`),
**Lemma 2.8**.  The generator sits in the **left slot** of `anmGen W n m p · v`.  The three families
are exactly the `O'_{n,p}`, `O''_{n,p}`, `O'''_{n,p}` generators:

* `anmRight_O'Circ_mem` — the `O'_{n,p}` circle generator `(c ∘ⁿ_p d) ∗ⁿ_{m,p} v`;
* `anmRight_O''_mem`    — the `O''_{n,p}` associator generator `(assocDefect …) ∗ⁿ_{m,p} v`;
* `anmRight_O'''_mem`   — the `O'''_{n,p}` level-mixing generator `(levelMix …) ∗ⁿ_{m,p} v`
  (with `g ∈ O_q`).

## Dong–Jiang's published proof (`math/0601626`, p. 9, the `(2.2)` computation), formalized verbatim

The headline reduction `O_{n,p} = O'_{n,p} + O''_{n,p} + O'''_{n,p}` makes the three families
exactly DJ's `(2.2)` sub-inclusions.  Every reassociation step is the **bare associator**
`bareAssoc_mem_OnmFull` (DJ's `u = 𝟙` step, `ZhuVermaAnArchDJ27.lean`), and—crucially—**every (2.1)
type step in DJ's `(2.2)` argument is applied to a bare associator, which under the outer
`w ∗ⁿ_{m,q} ·` is itself an `O''_{n,m}` generator** (`assocDefect`).  So no separate left-inclusion
hypothesis is consumed; the entire chain closes from the proven feeders.

* **`anmRight_O'''_mem`** (DJ `(2.2)`, first display line):
  `((b ∗ⁿ_q g) ∗ⁿ_{p,q} w) ∗ⁿ_{m,p} v ≡ (b ∗ⁿ_q g) ∗ⁿ_{m,q} (w ∗^q_{m,p} v)  (mod O_{n,m})`,
  and the right side is a `levelMix` generator (`levelMix_mem_OnmFull`).  One `bareAssoc`.

* **`anmRight_O'Circ_mem`** (DJ Lemma 2.5 second statement, lifted to the general product):
  by DJ Lemma 2.2 (`anmCirc_mem_OnBar`) the circle `c ∘ⁿ_p d` is a nonzero scalar multiple of the
  bar product `(L(-1)c + L(0)c) ∗̄ⁿ_p d`, so `(c ∘ⁿ_p d) ∗ⁿ_{m,p} v` is a scalar multiple of
  `((L(-1)c+L(0)c) ∗̄ⁿ_p d) ∗ⁿ_{m,p} v`; one `bareAssoc` reassociates this to
  `(L(-1)c+L(0)c) ∗̄ⁿ_m (d ∗ⁿ_{m,p} v)`, a member by the DJ 2.2 conclusion
  `anmGenBar_Lgen_mem_OnmFull`.

* **`anmRight_O''_mem`** (DJ `(2.2)`, the long `eqnarray*`): four rounds of `bareAssoc`.  After the
  outer reassociation the inner triple-product difference is reassociated; the two surviving terms
  cancel exactly (DJ's `≡ 0`), and every `bareAssoc` remainder, fed into the outer `w ∗ⁿ_{m,q₃} ·`
  (resp. `(w ∗ⁿ b₁) ∗ⁿ_{m,q₂} ·`), is precisely an `assocDefect` generator of `O''_{n,m}`.

## What is proved here (axiom-clean; NO `sorry`/`pbw`)

* `anmRight_O'''_mem` / `anmRight_O'Circ_mem` / `anmRight_O''_mem` — the three RIGHT generator
  families, each a member of `OnmFull W n m` (the three `right*` fields of `DJ28Residual`).
* `DJ28Residual_right` — the three right fields packaged into a ready-to-plug record.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.5, Lemma 2.8).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Subtraction in each slot of `anmGen` (from the ℂ-linear slot maps). -/

theorem anmGen_sub_left (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (u₁ u₂ v : 𝒱) :
    anmGen W n m p (u₁ - u₂) v = anmGen W n m p u₁ v - anmGen W n m p u₂ v := by
  rw [← anmGenLeftMap_apply W n m p v, map_sub, anmGenLeftMap_apply, anmGenLeftMap_apply]

theorem anmGen_sub_right (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (u v₁ v₂ : 𝒱) :
    anmGen W n m p u (v₁ - v₂) = anmGen W n m p u v₁ - anmGen W n m p u v₂ := by
  rw [← anmGenRightMap_apply W n m p u, map_sub, anmGenRightMap_apply, anmGenRightMap_apply]

/-! ## The bare-associator membership, in the outer-product (`assocDefect`) form.

For the RIGHT inclusion every (2.1)-type reassociation lands on a **bare associator**
`(A ∗^{p₃}_{m,r₁} B-applied) − (A ∗^{p₃}_{m,r₂} B-applied)`.  Fed into the outer free element `w`
via `w ∗ⁿ_{m,p₃} ·` (resp. into a fixed left factor via `· ∗ⁿ_{m,p₃} ·`), it is **definitionally** an
`assocDefect` generator of `O''_{n,m}`, so it is a member by `assocDefect_mem_OnmFull`. -/

/-- `w ∗ⁿ_{m,p₃} (bare associator) ∈ O_{n,m}` — the inner bare associator under the outer free
element `w`, which is definitionally `assocDefect W n m r₁ r₂ p₃ A B C w`. -/
theorem outer_bareAssoc_mem (W : VertexOperatorAlgebra 𝒱) (n m p₃ r₁ r₂ : ℕ) (A B C w : 𝒱) :
    anmGen W n m p₃ w
        (anmGen W p₃ m r₁ (anmGen W p₃ r₁ r₂ A B) C - anmGen W p₃ m r₂ A (anmGen W r₂ m r₁ B C))
      ∈ OnmFull W n m :=
  assocDefect_mem_OnmFull W n m r₁ r₂ p₃ A B C w

/-! ## RIGHT `O'''` branch — the level-mixing generator (DJ (2.2), first display line). -/

/-- **RIGHT `O'''_{n,p}` level-mixing generator (DJ (2.2), first line).**
`(levelMix W n p q b g w) ∗ⁿ_{m,p} v ∈ O_{n,m}(V)` for `g ∈ O_q = Onm W q q`.

`levelMix W n p q b g w = (b ∗ⁿ_q g) ∗ⁿ_{p,q} w`, so the generator is
`((b ∗ⁿ_q g) ∗ⁿ_{p,q} w) ∗ⁿ_{m,p} v`.  The bare associator (DJ's `u = 𝟙` step) reassociates it,
modulo `O_{n,m}`, to `(b ∗ⁿ_q g) ∗ⁿ_{m,q} (w ∗^q_{m,p} v) = levelMix W n m q b g (w ∗^q_{m,p} v)`,
which is an `O'''_{n,m}` generator (`levelMix_mem_OnmFull`). -/
theorem anmRight_O'''_mem (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (v : 𝒱) (q : ℕ) (b w g : 𝒱)
    (hg : g ∈ Onm W q q) :
    anmGen W n m p (levelMix W n p q b g w) v ∈ OnmFull W n m := by
  rw [levelMix]
  -- bareAssoc at outer `(p, q)` with `a = b ∗ⁿ_q g`, `b = w`, `c = v`:
  --   `((b∗ⁿ_q g) ∗ⁿ_{p,q} w) ∗ⁿ_{m,p} v − (b∗ⁿ_q g) ∗ⁿ_{m,q} (w ∗^q_{m,p} v) ∈ O_{n,m}`.
  have hassoc := bareAssoc_mem_OnmFull W n m p q (anmGen W n q q b g) w v
  -- the second term is a `levelMix W n m q` generator, hence in `O_{n,m}`.
  have hlevel : anmGen W n m q (anmGen W n q q b g) (anmGen W q m p w v) ∈ OnmFull W n m :=
    levelMix_mem_OnmFull W n m q b (anmGen W q m p w v) g hg
  -- `F = (F − G) + G ∈ O_{n,m}`.
  have := (OnmFull W n m).add_mem hassoc hlevel
  rwa [sub_add_cancel] at this

/-! ## RIGHT `O'` branch — the circle generator (DJ Lemma 2.5, lifted). -/

/-- The DJ 2.2 scalar `(n+p+1)·(−1)ⁿ·C(n+p, p)` (for the `(n,p)`-bar product) is nonzero. -/
private theorem dj22_scalar_np_ne_zero (n p : ℕ) :
    ((n : ℂ) + (p : ℂ) + 1) * ((-1 : ℂ)) ^ n * cbz ((n : ℤ) + (p : ℤ)) (p : ℤ) ≠ 0 := by
  have hcbz : cbz ((n : ℤ) + (p : ℤ)) (p : ℤ) = ((n + p).choose p : ℂ) := by
    rw [show ((n : ℤ) + (p : ℤ)) = (((n + p : ℕ)) : ℤ) from by push_cast; ring,
        cbz_natCast_eq_choose (by omega)]
  rw [hcbz]
  have h1 : ((n : ℂ) + (p : ℂ) + 1) ≠ 0 := by
    have h : ((n + p + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + p)
    push_cast at h
    convert h using 1
  have h2 : ((-1 : ℂ)) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3 : (((n + p).choose p : ℕ) : ℂ) ≠ 0 := by
    have : (n + p).choose p ≠ 0 := Nat.choose_pos (by omega) |>.ne'
    exact_mod_cast this
  exact mul_ne_zero (mul_ne_zero h1 h2) h3

/-- **RIGHT `O'_{n,p}` circle generator, homogeneous `c` (DJ Lemma 2.5).**
`(c ∘ⁿ_p d) ∗ⁿ_{m,p} v ∈ O_{n,m}(V)` for homogeneous `c ∈ 𝒱_M`.

By DJ Lemma 2.2 (`anmCirc_mem_OnBar`), `c ∘ⁿ_p d = s⁻¹ • ((L(-1)c+L(0)c) ∗̄ⁿ_p d)` for the nonzero
grade-free scalar `s = (n+p+1)(−1)ⁿ C(n+p,p)`, so the generator is `s⁻¹ • ((g ∗̄ⁿ_p d) ∗ⁿ_{m,p} v)`
with `g = L(-1)c+L(0)c`.  One `bareAssoc` reassociates `(g ∗̄ⁿ_p d) ∗ⁿ_{m,p} v` to
`g ∗̄ⁿ_m (d ∗ⁿ_{m,p} v)` modulo `O_{n,m}`, and the latter is an `O_{n,m}` member by the DJ 2.2
conclusion `anmGenBar_Lgen_mem_OnmFull`. -/
theorem anmRight_O'Circ_homog_mem (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) {M : ℕ} {c : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (d v : 𝒱) :
    anmGen W n m p (anmCirc W n p c d) v ∈ OnmFull W n m := by
  set s : ℂ := ((n : ℂ) + (p : ℂ) + 1) * ((-1 : ℂ)) ^ n * cbz ((n : ℤ) + (p : ℤ)) (p : ℤ) with hs
  have hsne : s ≠ 0 := dj22_scalar_np_ne_zero n p
  -- DJ 2.2: `s • (c ∘ⁿ_p d) = (L(-1)c+L(0)c) ∗̄ⁿ_p d`.
  have hbar := anmCirc_mem_OnBar W n p hc d
  -- so `c ∘ⁿ_p d = s⁻¹ • ((L(-1)c+L(0)c) ∗̄ⁿ_p d)`.
  have hcirc : anmCirc W n p c d
      = s⁻¹ • anmGen W n p n (W.L (-1) c + W.L 0 c) d := by
    rw [show anmGen W n p n (W.L (-1) c + W.L 0 c) d
          = anmGenBar W n p (W.L (-1) c + W.L 0 c) d from rfl, ← hbar,
        smul_smul, inv_mul_cancel₀ hsne, one_smul]
  rw [hcirc, anmGen_smul_left]
  refine Submodule.smul_mem _ _ ?_
  -- bareAssoc at `(p, n)` on the outer product:
  --   `((g ∗̄ⁿ_p d) ∗ⁿ_{m,p} v) − g ∗̄ⁿ_m (d ∗ⁿ_{m,p} v) ∈ O_{n,m}`,  `g = L(-1)c+L(0)c`.
  have hassoc := bareAssoc_mem_OnmFull W n m p n (W.L (-1) c + W.L 0 c) d v
  -- the second term `g ∗̄ⁿ_m (d ∗ⁿ_{m,p} v)` is a DJ 2.2 member.
  have hbarmem : anmGen W n m n (W.L (-1) c + W.L 0 c) (anmGen W n m p d v) ∈ OnmFull W n m := by
    rw [show anmGen W n m n (W.L (-1) c + W.L 0 c) (anmGen W n m p d v)
          = anmGenBar W n m (W.L (-1) c + W.L 0 c) (anmGen W n m p d v) from rfl]
    exact anmGenBar_Lgen_mem_OnmFull W n m c (anmGen W n m p d v)
  have := (OnmFull W n m).add_mem hassoc hbarmem
  rwa [sub_add_cancel] at this

/-- The RIGHT `O'_{n,p}` circle action `c ↦ (c ∘ⁿ_p d) ∗ⁿ_{m,p} v` as a ℂ-linear map in `c`
(composition of `anmCirc`-left and `anmGen`-left slot maps). -/
noncomputable def rightCircMap (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (d v : 𝒱) :
    𝒱 →ₗ[ℂ] 𝒱 where
  toFun c := anmGen W n m p (anmCirc W n p c d) v
  map_add' c₁ c₂ := by simp only [anmCirc_add_left, anmGen_add_left]
  map_smul' r c := by simp only [anmCirc_smul_left, anmGen_smul_left, RingHom.id_apply]

@[simp] theorem rightCircMap_apply (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (d v c : 𝒱) :
    rightCircMap W n m p d v c = anmGen W n m p (anmCirc W n p c d) v := rfl

/-- **RIGHT `O'_{n,p}` circle generator, general `c` (DJ Lemma 2.5).**
`(c ∘ⁿ_p d) ∗ⁿ_{m,p} v ∈ O_{n,m}(V)` for arbitrary `c` (decompose `c` into homogeneous pieces and
apply `anmRight_O'Circ_homog_mem`; the DJ 2.2 scalar is grade-free). -/
theorem anmRight_O'Circ_mem (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (c d v : 𝒱) :
    anmGen W n m p (anmCirc W n p c d) v ∈ OnmFull W n m := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  have hdecomp : ∑ k ∈ (DirectSum.decompose W.grading c).support,
      ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) = c :=
    DirectSum.sum_support_decompose W.grading c
  have hsum : anmGen W n m p (anmCirc W n p c d) v
      = ∑ k ∈ (DirectSum.decompose W.grading c).support,
          anmGen W n m p
            (anmCirc W n p ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) d) v := by
    conv_lhs => rw [← hdecomp]
    rw [← rightCircMap_apply, map_sum]
    rfl
  rw [hsum]
  refine Submodule.sum_mem _ fun k _ => ?_
  have hk : ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) ∈ W.grading k :=
    (DirectSum.decompose W.grading c k).2
  rcases le_or_gt 0 k with hknn | hkneg
  · obtain ⟨M, rfl⟩ := Int.eq_ofNat_of_zero_le hknn
    exact anmRight_O'Circ_homog_mem W n m p hk d v
  · have hzero : ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) = 0 := by
      have : ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) ∈ (⊥ : Submodule ℂ 𝒱) := by
        rw [← W.positivity k hkneg]; exact hk
      simpa using this
    rw [hzero, show (0 : 𝒱) = (0 : ℂ) • (0 : 𝒱) by rw [zero_smul], anmCirc_smul_left,
        anmGen_smul_left, zero_smul]
    exact (OnmFull W n m).zero_mem

/-! ## RIGHT `O''` branch — the associator generator (DJ (2.2), the long `eqnarray*`). -/

/-- **RIGHT `O''_{n,p}` associator generator (DJ (2.2)).**
`(assocDefect W n p q₁ q₂ q₃ b₁ b₂ b₃ w) ∗ⁿ_{m,p} v ∈ O_{n,m}(V)`.

DJ's chain.  Write `P := b₁ ∗^{q₃}_{q₁,q₂} b₂`, `Q := b₂ ∗^{q₂}_{p,q₁} b₃`, and
`db := b₃ ∗^{q₁}_{m,p} v`, so
`assocDefect … = w ∗ⁿ_{p,q₃} (P ∗^{q₃}_{p,q₁} b₃ − b₁ ∗^{q₃}_{p,q₂} Q)`.

1. Outer `bareAssoc` `(p,q₃)`: `G ≡ w ∗ⁿ_{m,q₃} ((P∗b₃ − b₁∗Q) ∗^{q₃}_{m,p} v)`.
2. `bareAssoc` on each inner triple (`(p,q₁)` on the `P`-triple, `(p,q₂)` on the `b₁`-triple): the
   two remainders, under `w ∗ⁿ_{m,q₃} ·`, are `assocDefect` generators of `O''_{n,m}`; what is left is
   `w ∗ⁿ_{m,q₃} (P ∗^{q₃}_{m,q₁} db − b₁ ∗^{q₃}_{m,q₂} (Q ∗^{q₂}_{m,p} v))`.
3. `bareAssoc` `(q₁,q₂)` on `P ∗ db` and `(p,q₁)` on `Q ∗ v`: the two main `b₁ ∗^{q₃}_{m,q₂}
   (b₂ ∗^{q₂}_{m,q₁} db)` terms cancel (DJ's `≡ 0`); the remainders are `C1 ∈ O_{q₃,m}` /
   `C2 ∈ O_{q₂,m}`.  `w ∗ⁿ_{m,q₃} C1` is an `assocDefect` generator; `w ∗ⁿ_{m,q₃} (b₁ ∗^{q₃}_{m,q₂}
   C2)` needs
4. one more `bareAssoc` `(q₃,q₂)`, after which `(w ∗ⁿ_{q₂,q₃} b₁) ∗ⁿ_{m,q₂} C2` is an `assocDefect`
   generator. -/
theorem anmRight_O''_mem (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (v : 𝒱)
    (q₁ q₂ q₃ : ℕ) (b₁ b₂ b₃ w : 𝒱) :
    anmGen W n m p (assocDefect W n p q₁ q₂ q₃ b₁ b₂ b₃ w) v ∈ OnmFull W n m := by
  -- abbreviations.
  set P : 𝒱 := anmGen W q₃ q₁ q₂ b₁ b₂ with hP
  set Q : 𝒱 := anmGen W q₂ p q₁ b₂ b₃ with hQ
  set db : 𝒱 := anmGen W q₁ m p b₃ v with hdb
  rw [assocDefect]
  -- STEP A (outer bareAssoc `(p,q₃)`):  G ≡ G₁ := w ∗ⁿ_{m,q₃} ((P∗b₃ − b₁∗Q) ∗^{q₃}_{m,p} v).
  have hA := bareAssoc_mem_OnmFull W n m p q₃ w
    (anmGen W q₃ p q₁ P b₃ - anmGen W q₃ p q₂ b₁ Q) v
  suffices hG1 : anmGen W n m q₃ w
      (anmGen W q₃ m p (anmGen W q₃ p q₁ P b₃ - anmGen W q₃ p q₂ b₁ Q) v) ∈ OnmFull W n m by
    have := (OnmFull W n m).add_mem hA hG1
    rwa [sub_add_cancel] at this
  -- STEP B/C/D members (each bareAssoc remainder under an outer product is an `assocDefect`):
  -- `mB1 = w ∗ⁿ_{m,q₃}((P∗^{q₃}_{p,q₁}b₃)∗^{q₃}_{m,p}v − P∗^{q₃}_{m,q₁}db)`  [assocDefect, A=P,B=b₃,C=v].
  have mB1 : anmGen W n m q₃ w
      (anmGen W q₃ m p (anmGen W q₃ p q₁ P b₃) v - anmGen W q₃ m q₁ P db) ∈ OnmFull W n m := by
    rw [hdb]; exact outer_bareAssoc_mem W n m q₃ p q₁ P b₃ v w
  -- `mB2 = w ∗ⁿ_{m,q₃}((b₁∗^{q₃}_{p,q₂}Q)∗^{q₃}_{m,p}v − b₁∗^{q₃}_{m,q₂}(Q∗^{q₂}_{m,p}v))`.
  have mB2 : anmGen W n m q₃ w
      (anmGen W q₃ m p (anmGen W q₃ p q₂ b₁ Q) v
        - anmGen W q₃ m q₂ b₁ (anmGen W q₂ m p Q v)) ∈ OnmFull W n m :=
    outer_bareAssoc_mem W n m q₃ p q₂ b₁ Q v w
  -- `mC1 = w ∗ⁿ_{m,q₃}(P∗^{q₃}_{m,q₁}db − b₁∗^{q₃}_{m,q₂}(b₂∗^{q₂}_{m,q₁}db))`  [assocDefect].
  have mC1 : anmGen W n m q₃ w
      (anmGen W q₃ m q₁ P db - anmGen W q₃ m q₂ b₁ (anmGen W q₂ m q₁ b₂ db))
        ∈ OnmFull W n m := by
    rw [hP]; exact outer_bareAssoc_mem W n m q₃ q₁ q₂ b₁ b₂ db w
  -- `C2 = (Q∗^{q₂}_{m,p}v) − b₂∗^{q₂}_{m,q₁}db ∈ O_{q₂,m}` (bareAssoc inner, level q₂).
  set C2 : 𝒱 := anmGen W q₂ m p Q v - anmGen W q₂ m q₁ b₂ db with hC2
  -- `mD = (w ∗ⁿ_{q₂,q₃} b₁) ∗ⁿ_{m,q₂} C2`  [assocDefect, outer = (w ∗ⁿ_{q₂,q₃} b₁)].
  have mD : anmGen W n m q₂ (anmGen W n q₂ q₃ w b₁) C2 ∈ OnmFull W n m := by
    rw [hC2, hQ, hdb]
    exact outer_bareAssoc_mem W n m q₂ p q₁ b₂ b₃ v (anmGen W n q₂ q₃ w b₁)
  -- STEP D bareAssoc remainder: `(w ∗ⁿ_{q₂,q₃} b₁)∗ⁿ_{m,q₂}C2 − w∗ⁿ_{m,q₃}(b₁∗^{q₃}_{m,q₂}C2) ∈ O`.
  have hDbar := bareAssoc_mem_OnmFull W n m q₂ q₃ w b₁ C2
  -- The MASTER linear identity: G₁ = mB1 − mB2 + mC1 − (mD − hDbar).  Pure linearity (`abel`).
  have hmaster : anmGen W n m q₃ w
        (anmGen W q₃ m p (anmGen W q₃ p q₁ P b₃ - anmGen W q₃ p q₂ b₁ Q) v)
      = anmGen W n m q₃ w
          (anmGen W q₃ m p (anmGen W q₃ p q₁ P b₃) v - anmGen W q₃ m q₁ P db)
        - anmGen W n m q₃ w
            (anmGen W q₃ m p (anmGen W q₃ p q₂ b₁ Q) v
              - anmGen W q₃ m q₂ b₁ (anmGen W q₂ m p Q v))
        + anmGen W n m q₃ w
            (anmGen W q₃ m q₁ P db - anmGen W q₃ m q₂ b₁ (anmGen W q₂ m q₁ b₂ db))
        - (anmGen W n m q₂ (anmGen W n q₂ q₃ w b₁) C2
            - (anmGen W n m q₂ (anmGen W n q₂ q₃ w b₁) C2
                - anmGen W n m q₃ w (anmGen W q₃ m q₂ b₁ C2))) := by
    -- push `anmGen W n m q₃ w ·` through all the subtractions; then `abel`.
    rw [hC2]
    simp only [anmGen_sub_left, anmGen_sub_right]
    abel
  rw [hmaster]
  -- assemble: (mB1 − mB2 + mC1) − (mD − hDbar) ∈ O_{n,m}.
  refine (OnmFull W n m).sub_mem
    ((OnmFull W n m).add_mem ((OnmFull W n m).sub_mem mB1 mB2) mC1) ?_
  exact (OnmFull W n m).sub_mem mD hDbar

/-! ## The three right fields packaged. -/

/-- The three RIGHT generator families of `DJ28Residual`, packaged as a record (drop-in for the
`right*` fields). -/
structure DJ28Residual_right (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) : Prop where
  rightO'Circ : ∀ c d v : 𝒱, anmGen W n m p (anmCirc W n p c d) v ∈ OnmFull W n m
  rightO'' : ∀ v : 𝒱, ∀ q₁ q₂ q₃ : ℕ, ∀ b₁ b₂ b₃ w : 𝒱,
    anmGen W n m p (assocDefect W n p q₁ q₂ q₃ b₁ b₂ b₃ w) v ∈ OnmFull W n m
  rightO''' : ∀ v : 𝒱, ∀ q : ℕ, ∀ b w : 𝒱, ∀ g : 𝒱, g ∈ Onm W q q →
    anmGen W n m p (levelMix W n p q b g w) v ∈ OnmFull W n m

/-- The three RIGHT branches hold unconditionally. -/
theorem dj28Residual_right (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) :
    DJ28Residual_right W n m p where
  rightO'Circ c d v := anmRight_O'Circ_mem W n m p c d v
  rightO'' v q₁ q₂ q₃ b₁ b₂ b₃ w := anmRight_O''_mem W n m p v q₁ q₂ q₃ b₁ b₂ b₃ w
  rightO''' v q b w g hg := anmRight_O'''_mem W n m p v q b w g hg

end VOA
