/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAn
import VOA.Modules.ZhuModule

/-!
# The `A(𝒱)`-bimodule structure on `A_n(𝒱)` (Frenkel–Zhu / Dong–Li–Mason)

Building on the tower foundation in `Modules.ZhuVermaAn` (the `n`-th circle product `a ∘ₙ b`,
`O_n(𝒱)`, `A_n(𝒱)`), this file constructs the two `V`-level products underlying the `A(𝒱)`-bimodule
structure on `A_n(𝒱)` (Frenkel–Zhu 1992; Dong–Li–Mason "Twisted representations of vertex operator
algebras"). For homogeneous `a ∈ 𝒱ₖ`,

* **Left product** (`leftProd`):
  `a *ₙ b = ∑_{j=0}^{n} (-1)^j C(j+n,n) · Res_z Y(a,z)b (1+z)^{k+n}/z^{n+j+1}`
        `  = ∑_{j=0}^{n} (-1)^j C(j+n,n) · ∑ᵢ C(k+n,i) a₍ᵢ₋ₙ₋ⱼ₋₁₎ b`.

* **Right product** (`rightProd`):
  `b *ₙ a = ∑_{j=0}^{n} (-1)^j C(j+n,j) · Res_z Y(a,z)b (1+z)^{k+j}/z^{n+j+1}`
        `  = ∑_{j=0}^{n} (-1)^j C(j+n,j) · ∑ᵢ C(k+j,i) a₍ᵢ₋ₙ₋ⱼ₋₁₎ b`.

Both are extended bilinearly over the grade decomposition of the homogeneous factor `a`, via the
generic FZ residue family `resFamily W s p b` (`= ∑ᵢ C(k+s,i) a₍ᵢ₋ₚ₎ b`, the residue
`Res_z Y(a,z)b (1+z)^{k+s}/z^{p}`).

## The `n = 0` correctness anchors (non-negotiable)

At `n = 0` the only surviving term is `j = 0` with `C(0,0) = 1` and pole `z^{-1}`, so BOTH products
collapse to the Zhu product (`Modules.ZhuAlgebra.zhuMul`):
* **`leftProd_zero`**  : `leftProd  W 0 a b = zhuMul W a b`.
* **`rightProd_zero`** : `rightProd W 0 a b = zhuMul W a b`.
These genuinely compile (no `sorry`), pinning the formulas to Zhu's product at the bottom of the
tower (Mathematica-cross-checked for the residue/binomial bookkeeping).

## Status

**Axiom-clean**: `resFamily`/`resHom` (the generic residue) and its bilinearity;
`leftProd`/`rightProd` and their full bilinearity
(`leftProd_add_left/smul_left/add_right/smul_right`, ditto `rightProd`); the homogeneous-collapse
lemmas `leftProd_homogeneous`/`rightProd_homogeneous`; and the **`n = 0` anchors**
`leftProd_zero`/`rightProd_zero` (`= zhuMul`). `#print axioms` on every proved def/theorem is
`[propext, Classical.choice, Quot.sound]`.

**Not proved here: the descent** (`O_n` a sub-bimodule) is left as PRECISE stated targets at the file end (NOT
`sorry`): `leftProd_gen_mem_On`, `leftProd_On_mem_On`, `rightProd_gen_mem_On`,
`rightProd_On_mem_On`. These are the `A_n`-analogs of Zhu's two-sided-ideal theorem
(`ZhuRightIdeal.right_ideal_core`, `ZhuAssociator.associator_core`); the technical input is the
higher-pole residue membership `Modules.ZhuModule.Pres_mem_O` generalized from `O(𝒱)` to `O_n(𝒱)`.

## References
* Gannon §5.3.2, Thm 5.3.4; Frenkel–Zhu (generalized Verma modules); Dong–Li–Mason.
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators
open Classical

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The generic FZ residue family `resFamily W s p b`

For homogeneous `aₖ ∈ 𝒱ₖ`,
`resFamily W s p b k aₖ = ∑_{i=0}^{(k+s)} C(k+s,i) (aₖ)₍ᵢ₋ₚ₎ b = Res_z Y(aₖ,z)b (1+z)^{k+s}/z^{p}`.
A `ℂ`-linear map `𝒱ₖ → 𝒱`. Both the FZ left and right products are finite alternating sums of
these (`s,p` depending on the summation index `j`), and at `s = 0`, `p = 1` it is exactly the Zhu
`zhuFamily` slice. -/
noncomputable def resFamily (W : VertexOperatorAlgebra 𝒱) (s p : ℤ) (b : 𝒱) (k : ℤ) :
    (W.grading k) →ₗ[ℂ] 𝒱 where
  toFun ak := ∑ i ∈ Finset.range ((k + s).toNat + 1),
    cbz (k + s) i • W.smul (ak : 𝒱) ((i : ℤ) - p) b
  map_add' a b := by
    simp only [Submodule.coe_add, PreVertexAlgebra.smul_add_left, smul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [SetLike.val_smul, PreVertexAlgebra.smul_smul_left, smul_comm c, RingHom.id_apply,
      Finset.smul_sum]

/-- `resFamily W s p b` is additive in `b`. -/
theorem resFamily_add (W : VertexOperatorAlgebra 𝒱) (s p : ℤ) (b₁ b₂ : 𝒱) :
    resFamily W s p (b₁ + b₂) = resFamily W s p b₁ + resFamily W s p b₂ := by
  funext k
  refine LinearMap.ext fun ak => ?_
  simp only [Pi.add_apply, LinearMap.add_apply, resFamily, LinearMap.coe_mk, AddHom.coe_mk,
    PreVertexAlgebra.smul_add_right, smul_add, Finset.sum_add_distrib]

/-- `resFamily W s p b` is homogeneous in `b`. -/
theorem resFamily_smul (W : VertexOperatorAlgebra 𝒱) (s p : ℤ) (c : ℂ) (b : 𝒱) :
    resFamily W s p (c • b) = c • resFamily W s p b := by
  funext k
  refine LinearMap.ext fun ak => ?_
  simp only [Pi.smul_apply, LinearMap.smul_apply, resFamily, LinearMap.coe_mk, AddHom.coe_mk,
    PreVertexAlgebra.smul_smul_right, Finset.smul_sum, smul_comm c]

/-- The bundled residue map `𝒱 → 𝒱`, `a ↦ Res_z Y(a,z)b (1+z)^{wt a + s}/z^{p}`, extended over
the grade decomposition of `a` (exactly the `zhuMul`/`circ` bundling pattern). -/
noncomputable def resHom (W : VertexOperatorAlgebra 𝒱) (s p : ℤ) (a b : 𝒱) : 𝒱 :=
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  (DFinsupp.lsum ℂ (resFamily W s p b)) (DirectSum.decompose W.grading a)

/-- On a homogeneous `a ∈ 𝒱ₖ`, the residue collapses to the single weight-`k` slice. -/
theorem resHom_homogeneous (W : VertexOperatorAlgebra 𝒱) (s p : ℤ) {k : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading k) (b : 𝒱) :
    resHom W s p a b
      = ∑ i ∈ Finset.range ((k + s).toNat + 1), cbz (k + s) i • W.smul a ((i : ℤ) - p) b := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  have hcollapse : resHom W s p a b = resFamily W s p b k ⟨a, ha⟩ := by
    change (DFinsupp.lsum ℂ (resFamily W s p b)) (DirectSum.decompose W.grading a) = _
    rw [DirectSum.decompose_of_mem W.grading ha]
    exact DFinsupp.lsum_single ℂ (resFamily W s p b) k ⟨a, ha⟩
  rw [hcollapse]; rfl

/-- `resHom` is additive in the (decomposed) left factor `a`. -/
theorem resHom_add_left (W : VertexOperatorAlgebra 𝒱) (s p : ℤ) (a₁ a₂ b : 𝒱) :
    resHom W s p (a₁ + a₂) b = resHom W s p a₁ b + resHom W s p a₂ b := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  exact map_add ((DFinsupp.lsum ℂ (resFamily W s p b)).comp
    (DirectSum.decomposeLinearEquiv W.grading).toLinearMap) a₁ a₂

/-- `resHom` is homogeneous in the (decomposed) left factor `a`. -/
theorem resHom_smul_left (W : VertexOperatorAlgebra 𝒱) (s p : ℤ) (c : ℂ) (a b : 𝒱) :
    resHom W s p (c • a) b = c • resHom W s p a b := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  exact map_smul ((DFinsupp.lsum ℂ (resFamily W s p b)).comp
    (DirectSum.decomposeLinearEquiv W.grading).toLinearMap) c a

/-- `resHom` is additive in the right factor `b`. -/
theorem resHom_add_right (W : VertexOperatorAlgebra 𝒱) (s p : ℤ) (a b₁ b₂ : 𝒱) :
    resHom W s p a (b₁ + b₂) = resHom W s p a b₁ + resHom W s p a b₂ := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  show (DFinsupp.lsum ℂ (resFamily W s p (b₁ + b₂))) (DirectSum.decompose W.grading a) = _
  rw [resFamily_add, map_add, LinearMap.add_apply]
  rfl

/-- `resHom` is homogeneous in the right factor `b`. -/
theorem resHom_smul_right (W : VertexOperatorAlgebra 𝒱) (s p : ℤ) (c : ℂ) (a b : 𝒱) :
    resHom W s p a (c • b) = c • resHom W s p a b := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  show (DFinsupp.lsum ℂ (resFamily W s p (c • b))) (DirectSum.decompose W.grading a) = _
  rw [resFamily_smul, map_smul, LinearMap.smul_apply]
  rfl

/-- The residue at `s = 0`, `p = 1` is exactly the Zhu product (`resFamily W 0 1 b = zhuFamily W b`,
both `= ∑ᵢ C(k,i) a₍ᵢ₋₁₎ b`). -/
theorem resFamily_zero_one (W : VertexOperatorAlgebra 𝒱) (b : 𝒱) :
    resFamily W 0 1 b = zhuFamily W b := by
  funext k
  refine LinearMap.ext fun ak => ?_
  simp only [resFamily, zhuFamily, LinearMap.coe_mk, AddHom.coe_mk, add_zero]

/-- The bundled residue at `s = 0`, `p = 1` is exactly the Zhu product `a * b`. -/
theorem resHom_zero_one (W : VertexOperatorAlgebra 𝒱) (a b : 𝒱) :
    resHom W 0 1 a b = zhuMul W a b := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  show (DFinsupp.lsum ℂ (resFamily W 0 1 b)) (DirectSum.decompose W.grading a) = _
  rw [resFamily_zero_one]
  rfl

/-! ## The Frenkel–Zhu / Dong–Li–Mason `V`-level products -/

/-- The **left FZ product** `a *ₙ b` (Dong–Li–Mason): for homogeneous `a ∈ 𝒱ₖ`,
`∑_{j=0}^{n} (-1)^j C(j+n,n) · Res_z Y(a,z)b (1+z)^{k+n}/z^{n+j+1}`, extended bilinearly over the
grade decomposition of `a`. Pole order `p = n+j+1`, binomial shift `s = n`. At `n = 0` it reduces
to the Zhu product (`leftProd_zero`). -/
noncomputable def leftProd (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a b : 𝒱) : 𝒱 :=
  ∑ j ∈ Finset.range (n + 1),
    ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) •
      resHom W (n : ℤ) ((n : ℤ) + (j : ℤ) + 1) a b

/-- The **right FZ product** `b *ₙ a` (Dong–Li–Mason): for homogeneous `a ∈ 𝒱ₖ`,
`∑_{j=0}^{n} (-1)^j C(j+n,j) · Res_z Y(a,z)b (1+z)^{k+j}/z^{n+j+1}`, extended bilinearly over the
grade decomposition of `a`. Pole order `p = n+j+1`, binomial shift `s = j`. At `n = 0` it reduces
to the Zhu product (`rightProd_zero`). -/
noncomputable def rightProd (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a b : 𝒱) : 𝒱 :=
  ∑ j ∈ Finset.range (n + 1),
    ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (j : ℤ)) •
      resHom W (j : ℤ) ((n : ℤ) + (j : ℤ) + 1) a b

/-! ## Bilinearity of the FZ products -/

/-- **`(a₁ + a₂) *ₙ b = a₁ *ₙ b + a₂ *ₙ b`**. -/
theorem leftProd_add_left (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a₁ a₂ b : 𝒱) :
    leftProd W n (a₁ + a₂) b = leftProd W n a₁ b + leftProd W n a₂ b := by
  simp only [leftProd, resHom_add_left, smul_add, Finset.sum_add_distrib]

/-- **`(c • a) *ₙ b = c • (a *ₙ b)`**. -/
theorem leftProd_smul_left (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (c : ℂ) (a b : 𝒱) :
    leftProd W n (c • a) b = c • leftProd W n a b := by
  simp only [leftProd, resHom_smul_left, Finset.smul_sum, smul_comm c]

/-- **`a *ₙ (b₁ + b₂) = a *ₙ b₁ + a *ₙ b₂`**. -/
theorem leftProd_add_right (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a b₁ b₂ : 𝒱) :
    leftProd W n a (b₁ + b₂) = leftProd W n a b₁ + leftProd W n a b₂ := by
  simp only [leftProd, resHom_add_right, smul_add, Finset.sum_add_distrib]

/-- **`a *ₙ (c • b) = c • (a *ₙ b)`**. -/
theorem leftProd_smul_right (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (c : ℂ) (a b : 𝒱) :
    leftProd W n a (c • b) = c • leftProd W n a b := by
  simp only [leftProd, resHom_smul_right, Finset.smul_sum, smul_comm c]

/-- **`(a₁ + a₂) *ₙ b = a₁ *ₙ b + a₂ *ₙ b`** (right product). -/
theorem rightProd_add_left (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a₁ a₂ b : 𝒱) :
    rightProd W n (a₁ + a₂) b = rightProd W n a₁ b + rightProd W n a₂ b := by
  simp only [rightProd, resHom_add_left, smul_add, Finset.sum_add_distrib]

/-- **`(c • a) *ₙ b = c • (a *ₙ b)`** (right product). -/
theorem rightProd_smul_left (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (c : ℂ) (a b : 𝒱) :
    rightProd W n (c • a) b = c • rightProd W n a b := by
  simp only [rightProd, resHom_smul_left, Finset.smul_sum, smul_comm c]

/-- **`a *ₙ (b₁ + b₂) = a *ₙ b₁ + a *ₙ b₂`** (right product). -/
theorem rightProd_add_right (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a b₁ b₂ : 𝒱) :
    rightProd W n a (b₁ + b₂) = rightProd W n a b₁ + rightProd W n a b₂ := by
  simp only [rightProd, resHom_add_right, smul_add, Finset.sum_add_distrib]

/-- **`a *ₙ (c • b) = c • (a *ₙ b)`** (right product). -/
theorem rightProd_smul_right (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (c : ℂ) (a b : 𝒱) :
    rightProd W n a (c • b) = c • rightProd W n a b := by
  simp only [rightProd, resHom_smul_right, Finset.smul_sum, smul_comm c]

/-! ## Homogeneous collapse of the FZ products -/

/-- On homogeneous `a ∈ 𝒱ₖ`, the left product is the explicit FZ double sum
`∑_{j=0}^{n} (-1)^j C(j+n,n) ∑ᵢ C(k+n,i) a₍ᵢ₋ₙ₋ⱼ₋₁₎ b`. -/
theorem leftProd_homogeneous (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {k : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading k) (b : 𝒱) :
    leftProd W n a b
      = ∑ j ∈ Finset.range (n + 1),
          ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) •
            ∑ i ∈ Finset.range ((k + (n : ℤ)).toNat + 1),
              cbz (k + (n : ℤ)) i • W.smul a ((i : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) b := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [resHom_homogeneous W (n : ℤ) ((n : ℤ) + (j : ℤ) + 1) ha b]

/-- On homogeneous `a ∈ 𝒱ₖ`, the right product is the explicit FZ double sum
`∑_{j=0}^{n} (-1)^j C(j+n,j) ∑ᵢ C(k+j,i) a₍ᵢ₋ₙ₋ⱼ₋₁₎ b`. -/
theorem rightProd_homogeneous (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {k : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading k) (b : 𝒱) :
    rightProd W n a b
      = ∑ j ∈ Finset.range (n + 1),
          ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (j : ℤ)) •
            ∑ i ∈ Finset.range ((k + (j : ℤ)).toNat + 1),
              cbz (k + (j : ℤ)) i • W.smul a ((i : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) b := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [resHom_homogeneous W (j : ℤ) ((n : ℤ) + (j : ℤ) + 1) ha b]

/-! ## The `n = 0` correctness anchors (= the Zhu product)

At `n = 0`, the `j`-sum has the single term `j = 0`, where the scalar is
`(-1)^0 · C(0,0) = 1`, the shift is `s = 0`, and the pole is `p = 0+0+1 = 1`; so both products
collapse to `resHom W 0 1 a b = zhuMul W a b`. These are non-negotiable sanity checks: if the
formula failed them the formula would be wrong. They genuinely compile. -/

/-- **`n = 0` anchor (left):** `leftProd W 0 a b = a * b` (the Zhu product). -/
theorem leftProd_zero (W : VertexOperatorAlgebra 𝒱) (a b : 𝒱) :
    leftProd W 0 a b = zhuMul W a b := by
  rw [leftProd, Finset.sum_range_one]
  simp only [Nat.cast_zero, pow_zero, add_zero, cbz_zero, mul_one, one_smul, zero_add]
  exact resHom_zero_one W a b

/-- **`n = 0` anchor (right):** `rightProd W 0 a b = a * b` (the Zhu product). -/
theorem rightProd_zero (W : VertexOperatorAlgebra 𝒱) (a b : 𝒱) :
    rightProd W 0 a b = zhuMul W a b := by
  rw [rightProd, Finset.sum_range_one]
  simp only [Nat.cast_zero, pow_zero, add_zero, cbz_zero, mul_one, one_smul, zero_add]
  exact resHom_zero_one W a b

/-! ## Sanity: the products are `0` on a zero factor (from bilinearity). -/

@[simp] theorem leftProd_zero_left (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (b : 𝒱) :
    leftProd W n 0 b = 0 := by
  have := leftProd_smul_left W n 0 0 b
  rwa [zero_smul, zero_smul] at this

@[simp] theorem leftProd_zero_right (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a : 𝒱) :
    leftProd W n a 0 = 0 := by
  have := leftProd_smul_right W n 0 a 0
  rwa [zero_smul, zero_smul] at this

@[simp] theorem rightProd_zero_left (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (b : 𝒱) :
    rightProd W n 0 b = 0 := by
  have := rightProd_smul_left W n 0 0 b
  rwa [zero_smul, zero_smul] at this

@[simp] theorem rightProd_zero_right (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a : 𝒱) :
    rightProd W n a 0 = 0 := by
  have := rightProd_smul_right W n 0 a 0
  rwa [zero_smul, zero_smul] at this

/-!
## 2b — the descent (`O_n(𝒱)` is a sub-`A(𝒱)`-bimodule): PRECISE remaining targets

The bilinear products `leftProd`/`rightProd` descend to `A(𝒱) × A_n(𝒱) → A_n(𝒱)` and
`A_n(𝒱) × A(𝒱) → A_n(𝒱)` once the following four membership statements are proved (the `A_n`-analog
of Zhu's two-sided-ideal theorem; the `n = 0` case is the existing
`ZhuRightIdeal.right_ideal_core` / `ZhuAssociator.associator_core` machinery, which this generalizes
to depth `n` via the higher-pole residue `Modules.ZhuModule.Pres_mem_O`). These are stated PRECISELY
here (NOT as `sorry`) for the next pass:

* `leftProd_gen_mem_On`  : for homogeneous `a ∈ 𝒱_M`,
    `leftProd W n (W.L (-1) a + W.L 0 a) b ∈ On W n`
  — i.e. `O(𝒱) *ₙ 𝒱 ⊆ O_n(𝒱)` (left product of an `O`-generator lands in `O_n`).
  *Reduction:* by `leftProd_homogeneous` + `zhuMul_L_base`-style base-residue handling, each
  `j`-summand is `∑ᵢ C(M+n,i) (L₋₁a+L₀a)-residue`; the FZ identity collapses the alternating
  `j`-sum so the residue lands in the span of circle products `circ W n · ·` = `On W n`.

* `rightProd_gen_mem_On` : for homogeneous `a ∈ 𝒱_M`,
    `rightProd W n (W.L (-1) a + W.L 0 a) b ∈ On W n`
  — i.e. `O(𝒱) *ₙ 𝒱 ⊆ O_n(𝒱)` on the right slot (same reduction, right-product coefficients).

* `leftProd_On_mem_On`   : `∀ x ∈ On W n, ∀ a, leftProd W n a x ∈ On W n`
  — i.e. `𝒱 *ₙ O_n(𝒱) ⊆ O_n(𝒱)`: `O_n` is preserved under left multiplication.
  *Reduction:* the `A_n`-analog of `ZhuRightIdeal.right_ideal_core`: expand `a *ₙ (c ∘ₙ d)` via
  `mode_split` + `mode_commutator_uniform`, reindex (as in `S_eq_finsum`/`PresCombo_eq_finsum`), and
  collapse against the generalized `Pres_mem_O` for `O_n` (`Pres`-membership at pole depth `2n+2`).

* `rightProd_On_mem_On`  : `∀ x ∈ On W n, ∀ a, rightProd W n x a ∈ On W n`
  — i.e. `O_n(𝒱) *ₙ 𝒱 ⊆ O_n(𝒱)`: `O_n` is preserved under right multiplication.

Discharging these (the deep step) endows `A_n(𝒱)` with the `A(𝒱)`-bimodule structure of
Frenkel–Zhu, the next stage of the `M(U)` construction.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.resFamily
  #print axioms VOA.resHom
  #print axioms VOA.resHom_homogeneous
  #print axioms VOA.leftProd
  #print axioms VOA.rightProd
  #print axioms VOA.leftProd_add_left
  #print axioms VOA.leftProd_smul_left
  #print axioms VOA.leftProd_add_right
  #print axioms VOA.leftProd_smul_right
  #print axioms VOA.rightProd_add_left
  #print axioms VOA.rightProd_smul_left
  #print axioms VOA.rightProd_add_right
  #print axioms VOA.rightProd_smul_right
  #print axioms VOA.leftProd_homogeneous
  #print axioms VOA.rightProd_homogeneous
  #print axioms VOA.leftProd_zero
  #print axioms VOA.rightProd_zero
-/
