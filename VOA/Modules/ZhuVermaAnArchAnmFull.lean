/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchAnm
import VOA.Modules.ZhuVermaAnArch

/-!
# The FULL Dong–Jiang ideal `O_{n,m}(𝒱) = O'_{n,m} + O''_{n,m} + O'''_{n,m}`

This file pins, **verbatim from the primary source**, the genuine Dong–Jiang ideal (Dong–Jiang,
*Bimodules associated to vertex operator algebras*, Math. Z. 259 (2008) 799–826, `math/0601626`, §2)
and the general three-index residue product `*^n_{m,p}` that the bimodule composition (DJ Prop. 3.4)
actually uses.

The repo's existing `Onm` (`ZhuVermaAnArchAnm.lean`) is **only the `O'_{n,m}` summand** (the linear
span of `u ∘^n_m v` and the shifted grading generator).  The full DJ ideal additionally contains the
**associator-defect** summand `O''_{n,m}` and the **level-mixing** summand `O'''_{n,m}`.  Both are
needed for `A_{n,m}(𝒱) = 𝒱 / O_{n,m}(𝒱)` to be a genuine `(A_n, A_m)`-bimodule (DJ Thm 2.9) and for
the composition `ψ : A_{p,n} ⊗_{A_n} A_{n,m} → A_{p,m}` (DJ Prop 3.4) to be well defined.

## The exact Dong–Jiang formulas (`math/0601626`, §2, verbatim)

**General three-index product** `*^n_{m,p}` (DJ §2, the displayed formula before Lemma 2.2): for
homogeneous `u ∈ 𝒱` of weight `wt u`,
```
  u *^n_{m,p} v = ∑_{i=0}^{p} (-1)^i C(m+n-p+i, i) Res_z (1+z)^{wt u + m} / z^{m+n-p+i+1} Y(u,z) v.
```
Special cases (DJ, immediately after the displayed formula):
* `n = p` ⟹ `*^n_{m,n}` is written `∗̄^n_m` (left `A_n`-action):
  `u ∗̄^n_m v = ∑_{i=0}^n (-1)^i C(m+i, i) Res_z (1+z)^{wt u + m}/z^{m+i+1} Y(u,z) v`.
* `m = p` ⟹ `*^n_{m,m}` is written `*^n_m` (right `A_m`-action) = the repo `anmRight`:
  `u *^n_m v = ∑_{i=0}^m (-1)^i C(n+i, i) Res_z (1+z)^{wt u + m}/z^{n+i+1} Y(u,z) v`.
* `m = n` ⟹ `∗̄` and `*` coincide and equal the DLM `*_n`.

**`O'_{n,m}(𝒱)`** (DJ, before Lemma 2.2): the linear span of all
`u ∘^n_m v = Res_z (1+z)^{wt u + m}/z^{n+m+2} Y(u,z) v`  and  `L(-1)u + (L(0) + m − n)u`.
(This is exactly the repo `Onm`.)

**`O''_{n,m}(𝒱)`** (DJ, before Lemma 2.7): the linear span of all
```
  u *^n_{m,p₃} ( (a *^{p₃}_{p₁,p₂} b) *^{p₃}_{m,p₁} c  −  a *^{p₃}_{m,p₂} (b *^{p₂}_{m,p₁} c) ),
    for  a, b, c, u ∈ 𝒱,  p₁, p₂, p₃ ∈ ℤ₊.
```
This is the **associator defect** of the family of products `*` (the obstruction to associativity at
the chain level); it is precisely what Lemma 2.6 controls (`(a∗̄b)∗c − a∗̄(b∗c) ∈ O'`).

**`O'''_{n,m}(𝒱)`** (DJ, before Lemma 2.7): `∑_{p ∈ ℤ₊} (𝒱 *^n_p O_p(𝒱)) *^n_{m,p} 𝒱`, where
`O_p(𝒱) = O'_{p,p}(𝒱)` is the level-`p` DLM ideal, and `𝒱 *^n_p O_p(𝒱)` means the span of
`a *^n_p g` for `a ∈ 𝒱, g ∈ O_p(𝒱)` (here `*^n_p = *^n_{p,p}` is the diagonal product), then the
outer `*^n_{m,p}`-product against an arbitrary `𝒱`-element on the right.  This is the **level-mixing**
summand carrying the lower-level ideals up the tower.

**The full ideal** (DJ, before Lemma 2.7, displayed):
```
  O_{n,m}(𝒱) = O'_{n,m}(𝒱) + O''_{n,m}(𝒱) + O'''_{n,m}(𝒱).
```

## What is proved here (axiom-clean)

* `anmGen W n m p u v` — the general three-index product `*^n_{m,p}` via the generic `resHom`
  (shift `s = m`, weights `(-1)^i C(m+n-p+i, i)`, poles `m+n-p+i+1`, range `p+1`).
* `anmGen_eq_anmRight` — `*^n_{m,m} = *^n_m` (the repo right action `anmRight`).
* `anmGenBar W n m u v := anmGen W n m n u v` — the left action `∗̄^n_m`.
* `anmGen_diag_eq` — at `m = n`, `∗̄^n_m = *^n_m` (DLM `*_n`).
* Full ℂ-bilinearity of `anmGen` in both slots.
* `OnmFull W n m` — the ENLARGED ideal `O' ⊔ O'' ⊔ O'''`, with `Onm ≤ OnmFull` (`Onm_le_OnmFull`)
  and the generator memberships `anmCirc/anmLgen/assocDefect/levelMix ∈ OnmFull`.
  **Fidelity** (checked verbatim against the arXiv source of math/0601626; the line numbers below
  refer to that source): `OnmFull` IS Dong–Jiang's genuine ideal.  DJ define (line 1013–1015)
  `O_{n,m}(V) = O'_{n,m}(V) + O''_{n,m}(V) + O'''_{n,m}(V)` and (line 1257) `A_{n,m}(V) = V/O_{n,m}(V)`;
  Thm 2.9 proves the `A_n`-`A_m`-bimodule property INTO this full ideal ("both actions well defined from
  the definition of `O_{n,m}(V)` and Lemma 2.8; the ... module structures follow from the fact that
  `O''_{n,m}(V)` is a subspace of `O_{n,m}(V)`").  So `OnmFull` = DJ's `O_{n,m}` and `AnmFull = 𝒱 ⧸ OnmFull`
  = DJ's GENUINE bimodule `A_{n,m}`.  The repo's `Onm` (= `O'_{n,m}`, prime) is the NON-STANDARD
  (bigger-quotient) target: `𝒱 ⧸ Onm` is a valid bimodule ONLY IF `O_{n,m} = O'_{n,m}` (DJ Remark 2.10 —
  DJ's own "very difficult problem" for `m ≠ n`).  The Half-A graded-action closure into `OnmFull` is DJ
  Lemma 2.8 = `mUGradedActionFull_holds` (PROVEN, unconditional); into the prime `Onm` it is the OPEN
  Rmk 2.10-adjacent `CrossCircCore` wall.
* `AnmFull W n m := 𝒱 ⧸ OnmFull W n m` — DJ's GENUINE bimodule `A_{n,m}(V) = V/O_{n,m}(V)` (line 1257,
  full ideal).  The repo's `𝒱 ⧸ Onm` (prime `O'`) is the bigger-quotient variant, a valid bimodule only
  under DJ Rmk 2.10.

## Engine validation (rank-1 free boson, `certificates/mathematica/anmfull_check.wl`)

* `anmGen W n m m = anmRight W n m` and `anmGen W n n n = anmGen W n n m|_{m=n}` (product collapses).
* At `m = n`, `OnmFull W n n = OnFull W n` (the DLM `A_n` ideal), so `A_{n,n} = A_n` (DJ Prop 4.6 /
  Remark 2.10).  [target check]

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (general product, `O'/O''/O'''`,
Lemmas 2.2–2.8, Thm 2.9), §3 (Prop. 3.4); Dong–Li–Mason, J. Algebra 206 (1998) 67–96.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The general three-index Dong–Jiang product `*^n_{m,p}`. -/

/-- **Dong–Jiang general three-index product** `u *^n_{m,p} v`
`= ∑_{i=0}^{p} (-1)^i C(m+n-p+i, i) Res_z (1+z)^{wt u + m}/z^{m+n-p+i+1} Y(u,z)v`, expressed through
the generic FZ residue `resHom W m (m+n-p+i+1)` (shift `s = m`, pole `m+n-p+i+1`), with the external
weight `(-1)^i C(m+n-p+i, i)`.  Specializes: `p = m` ⟹ `anmRight` (`*^n_m`); `p = n` ⟹ `anmGenBar`
(`∗̄^n_m`). -/
noncomputable def anmGen (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (u v : 𝒱) : 𝒱 :=
  ∑ i ∈ Finset.range (p + 1),
    ((-1 : ℂ) ^ i * cbz ((m : ℤ) + (n : ℤ) - (p : ℤ) + i) (i : ℤ))
      • resHom W (m : ℤ) ((m : ℤ) + (n : ℤ) - (p : ℤ) + (i : ℤ) + 1) u v

/-- **`*^n_{m,m} = *^n_m`** — at `p = m` the general product is exactly the repo right action
`anmRight` (DJ: `*^n_{m,m}` is denoted `*^n_m`). -/
theorem anmGen_eq_anmRight (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (u v : 𝒱) :
    anmGen W n m m u v = anmRight W n m u v := by
  simp only [anmGen, anmRight]
  refine Finset.sum_congr rfl fun i _ => ?_
  have he : ((m : ℤ) + (n : ℤ) - (m : ℤ)) = (n : ℤ) := by ring
  rw [he]

/-- **Dong–Jiang left `A_n`-action `∗̄^n_m`** `= *^n_{m,n}`
`= ∑_{i=0}^n (-1)^i C(m+i, i) Res_z (1+z)^{wt u + m}/z^{m+i+1} Y(u,z)v`. -/
noncomputable def anmGenBar (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (u v : 𝒱) : 𝒱 :=
  anmGen W n m n u v

/-- The left action written out (DJ `∗̄^n_m`): shift `m`, binomial `C(m+i,i)`, pole `m+i+1`. -/
theorem anmGenBar_eq (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (u v : 𝒱) :
    anmGenBar W n m u v
      = ∑ i ∈ Finset.range (n + 1),
          ((-1 : ℂ) ^ i * cbz ((m : ℤ) + i) (i : ℤ))
            • resHom W (m : ℤ) ((m : ℤ) + (i : ℤ) + 1) u v := by
  simp only [anmGenBar, anmGen]
  refine Finset.sum_congr rfl fun i _ => ?_
  have he : ((m : ℤ) + (n : ℤ) - (n : ℤ)) = (m : ℤ) := by ring
  rw [he]

/-- At the diagonal `m = n`, `∗̄^n_n = *^n_n` (= DLM `*_n`). -/
theorem anmGen_diag_eq (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (u v : 𝒱) :
    anmGenBar W n n u v = anmRight W n n u v := by
  rw [anmGenBar, anmGen_eq_anmRight]

/-! ## Bilinearity of the general product `*^n_{m,p}`. -/

theorem anmGen_add_left (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (u₁ u₂ v : 𝒱) :
    anmGen W n m p (u₁ + u₂) v = anmGen W n m p u₁ v + anmGen W n m p u₂ v := by
  simp only [anmGen, resHom_add_left, smul_add, Finset.sum_add_distrib]

theorem anmGen_smul_left (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (c : ℂ) (u v : 𝒱) :
    anmGen W n m p (c • u) v = c • anmGen W n m p u v := by
  simp only [anmGen, resHom_smul_left, Finset.smul_sum, smul_comm c]

theorem anmGen_add_right (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (u v₁ v₂ : 𝒱) :
    anmGen W n m p u (v₁ + v₂) = anmGen W n m p u v₁ + anmGen W n m p u v₂ := by
  simp only [anmGen, resHom_add_right, smul_add, Finset.sum_add_distrib]

theorem anmGen_smul_right (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (c : ℂ) (u v : 𝒱) :
    anmGen W n m p u (c • v) = c • anmGen W n m p u v := by
  simp only [anmGen, resHom_smul_right, Finset.smul_sum, smul_comm c]

/-! ## The associator-defect summand `O''_{n,m}` and the level-mixing summand `O'''_{n,m}`. -/

/-- The **associator-defect element** (the seed of `O''_{n,m}`):
`u *^n_{m,p₃} ( (a *^{p₃}_{p₁,p₂} b) *^{p₃}_{m,p₁} c − a *^{p₃}_{m,p₂} (b *^{p₂}_{m,p₁} c) )`. -/
noncomputable def assocDefect (W : VertexOperatorAlgebra 𝒱) (n m p₁ p₂ p₃ : ℕ) (a b c u : 𝒱) : 𝒱 :=
  anmGen W n m p₃ u
    (anmGen W p₃ m p₁ (anmGen W p₃ p₁ p₂ a b) c
      - anmGen W p₃ m p₂ a (anmGen W p₂ m p₁ b c))

/-- **`O''_{n,m}(𝒱)`** — the associator-defect span. -/
def OnmAssoc (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) : Submodule ℂ 𝒱 :=
  Submodule.span ℂ
    {x | ∃ (p₁ p₂ p₃ : ℕ) (a b c u : 𝒱), x = assocDefect W n m p₁ p₂ p₃ a b c u}

/-- The **level-mixing element** (the seed of `O'''_{n,m}`):
`a *^n_{m,p} g` where `g = b *^p_p w₀ ∈ O_p(𝒱)`-generator lifted by the outer product.  We take the
generator set to be the image, under `x ↦ anmGen W n m p a x`, of the level-`p` ideal `Onm W p p`
(`= O'_{p,p} = O_p(𝒱)`) right-multiplied into `𝒱` — i.e. `(𝒱 *^n_p O_p) *^n_{m,p} 𝒱`.  Concretely a
generator is `anmGen W n m p (anmGen W n p p a g) v` for `a v : 𝒱`, `g ∈ Onm W p p`. -/
noncomputable def levelMix (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (a g v : 𝒱) : 𝒱 :=
  anmGen W n m p (anmGen W n p p a g) v

/-- **`O'''_{n,m}(𝒱)`** — the level-mixing span `∑_p (𝒱 *^n_p O_p) *^n_{m,p} 𝒱`. -/
def OnmLevel (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) : Submodule ℂ 𝒱 :=
  Submodule.span ℂ
    {x | ∃ (p : ℕ) (a v : 𝒱) (g : 𝒱), g ∈ Onm W p p ∧ x = levelMix W n m p a g v}

/-- **The full Dong–Jiang ideal** `O_{n,m}(𝒱) = O'_{n,m} + O''_{n,m} + O'''_{n,m}`. -/
def OnmFull (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) : Submodule ℂ 𝒱 :=
  Onm W n m ⊔ OnmAssoc W n m ⊔ OnmLevel W n m

/-- The partial (repo) ideal sits inside the full DJ ideal. -/
theorem Onm_le_OnmFull (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) :
    Onm W n m ≤ OnmFull W n m :=
  le_sup_of_le_left le_sup_left

/-- Circle generators land in the full ideal. -/
theorem anmCirc_mem_OnmFull (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (u v : 𝒱) :
    anmCirc W n m u v ∈ OnmFull W n m :=
  Onm_le_OnmFull W n m (anmCirc_mem_Onm W n m u v)

/-- Grading generators land in the full ideal. -/
theorem anmLgen_mem_OnmFull (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (u : 𝒱) :
    anmLgen W n m u ∈ OnmFull W n m :=
  Onm_le_OnmFull W n m (anmLgen_mem_Onm W n m u)

/-- Associator-defect generators land in the full ideal. -/
theorem assocDefect_mem_OnmFull (W : VertexOperatorAlgebra 𝒱) (n m p₁ p₂ p₃ : ℕ) (a b c u : 𝒱) :
    assocDefect W n m p₁ p₂ p₃ a b c u ∈ OnmFull W n m := by
  have hmem : assocDefect W n m p₁ p₂ p₃ a b c u ∈ OnmAssoc W n m :=
    Submodule.subset_span ⟨p₁, p₂, p₃, a, b, c, u, rfl⟩
  have hle : OnmAssoc W n m ≤ OnmFull W n m :=
    le_sup_of_le_left le_sup_right
  exact hle hmem

/-- Level-mixing generators land in the full ideal. -/
theorem levelMix_mem_OnmFull (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (a v g : 𝒱)
    (hg : g ∈ Onm W p p) :
    levelMix W n m p a g v ∈ OnmFull W n m := by
  have hmem : levelMix W n m p a g v ∈ OnmLevel W n m :=
    Submodule.subset_span ⟨p, a, v, g, hg, rfl⟩
  have hle : OnmLevel W n m ≤ OnmFull W n m := le_sup_right
  exact hle hmem

/-- **`A_{n,m}(𝒱) := 𝒱 / O_{n,m}(𝒱)`** — the genuine Dong–Jiang bimodule carrier (full ideal). -/
abbrev AnmFull (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) : Type u := 𝒱 ⧸ OnmFull W n m

/-- The quotient map `𝒱 →ₗ A_{n,m}(𝒱)`. -/
def mkAnmFull (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) : 𝒱 →ₗ[ℂ] AnmFull W n m :=
  (OnmFull W n m).mkQ

end VOA
