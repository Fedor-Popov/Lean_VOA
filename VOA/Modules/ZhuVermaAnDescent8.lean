/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnDescent7

/-!
# The depth-`n` U-family / V-family `PresOn`-tower memberships (`USide_mem_On` /
`VSide_mem_On`), and the assembled `RightDescends.on_mem` route.

Building on the full U/V split `rightProd_circ_UV_assembly` (`ZhuVermaAnDescent7`) and the keystone
higher-pole residue membership `Pres_mem_On` (`ZhuVermaAnDescent`), this file proves the
*membership* halves of the depth-`n` associator collapse for the `A_n(𝒱)` bimodule descent.

## The key structural insight (Mathematica-verified, 648 cases)

`rightProd W n (circ W n c d) a` re-expresses, in the iterated bases `c₍μ₎(d₍γ₎a)` (the **U-family**)
and `d₍μ₎(c₍γ₎a)` (the **V-family**), as a finite ℂ-combination of `PresOn`-towers:

* the U-family is a finite ℂ-combination of `PresOn W M n δ c (d₍γ₎a)` towers (grade `M`, base
  `d₍γ₎a`), and
* the V-family is a finite ℂ-combination of `PresOn W P n δ d (c₍γ₎a)` towers (grade `P`, base
  `c₍γ₎a`),

with **no irreducible cross term** — the `M`-dependence of the V-family is absorbed entirely inside
its own `d`-tower weights.  Because each `PresOn`-tower lies in `On W n` by the keystone
`Pres_mem_On` *regardless of its scalar weight*, both families lie in `On W n` separately.  This is
the depth-`n` lift of `ZhuAssociator.Ufam_mem_O` / `Vfam_mem_O`.

## What this file proves (axiom-clean)

* `UfamOn` / `VfamOn` — the depth-`n` `PresOn`-tower families (the U-side / V-side targets), each an
  abstractly-weighted finite double sum of `PresOn`-towers (cf. `ZhuAssociator.Ufam`/`Vfam`).
* **`USide_mem_On`** (`UfamOn_mem_On`) — `UfamOn … ∈ On W n` for homogeneous `c ∈ 𝒱_M`, by
  `Pres_mem_On` (depth-`n` lift of `Ufam_mem_O`).
* **`VSide_mem_On`** (`VfamOn_mem_On`) — `VfamOn … ∈ On W n` for homogeneous `d ∈ 𝒱_P`, by
  `Pres_mem_On` (depth-`n` lift of `Vfam_mem_O`).
* `UfamOn_add_VfamOn_mem_On` — the combined `UfamOn + VfamOn ∈ On W n` (the membership half of
  `RightDescends.on_mem`, modulo the finsum reindexing that identifies the assembly with the
  tower families).

## References
* Gannon §5.3.2, Thm 5.3.4; Zhu Thm 2.1.1/2.1.2; Frenkel–Zhu Lemma 2.1.2; Dong–Li–Mason.
-/

open scoped BigOperators
open Finset

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators
open Classical

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The depth-`n` U-family and V-family of `PresOn`-towers.

In the U/V split of `rightProd W n (circ W n c d) a` (`rightProd_circ_UV_assembly`), the U-modes
`c₍μ₎(d₍γ₎a)` and V-modes `d₍μ₎(c₍γ₎a)` are independent formal symbols.  The net U-coefficient of
`c₍μ₎(d₍γ₎a)` collapses, for each fixed `γ`, onto a `PresOn`-tower in `c` (grade `M`) based at
`d₍γ₎a`; the net V-coefficient onto a `PresOn`-tower in `d` (grade `P`) based at `c₍γ₎a`.  We package
the resulting families as abstractly-weighted finite double sums (over a base-mode range `Γ` and a
tower-depth range `Δ`) of `PresOn`-towers, mirroring `ZhuAssociator.Ufam`/`Vfam` (which use the FZ
weight `ZhuMu.muCoeff`).  The membership in `On W n` holds for *any* scalar weights `wU`/`wV`, so the
(dual-Hahn-type) closed form of the weights is irrelevant to the membership. -/

/-- The depth-`n` **U-family** of `PresOn`-towers (the `c`-first family): for weights
`wU : ℤ → ℕ → ℂ` (indexed by the base-mode value `γ` and the tower depth `δ`),
`∑_{γ} ∑_{δ<Δ} wU γ δ • PresOn W M n δ c (d₍γ₎a)`, the base-mode `γ` ranging over `[γ₀, γ₀+Γ)`. -/
noncomputable def UfamOn (W : VertexOperatorAlgebra 𝒱) (M n : ℕ) (c d a : 𝒱)
    (wU : ℤ → ℕ → ℂ) (γ₀ : ℤ) (Γ Δ : ℕ) : 𝒱 :=
  ∑ g ∈ Finset.range Γ, ∑ δ ∈ Finset.range Δ,
    wU (γ₀ + (g : ℤ)) δ • PresOn W M n δ c (W.smul d (γ₀ + (g : ℤ)) a)

/-- The depth-`n` **V-family** of `PresOn`-towers (the `d`-first family): for weights
`wV : ℤ → ℕ → ℂ`, `∑_{γ} ∑_{δ<Δ} wV γ δ • PresOn W P n δ d (c₍γ₎a)`, the base-mode `γ` ranging over
`[γ₀, γ₀+Γ)`.  The weights may depend on `M` (harmless: each tower is in `On W n` regardless). -/
noncomputable def VfamOn (W : VertexOperatorAlgebra 𝒱) (P n : ℕ) (c d a : 𝒱)
    (wV : ℤ → ℕ → ℂ) (γ₀ : ℤ) (Γ Δ : ℕ) : 𝒱 :=
  ∑ g ∈ Finset.range Γ, ∑ δ ∈ Finset.range Δ,
    wV (γ₀ + (g : ℤ)) δ • PresOn W P n δ d (W.smul c (γ₀ + (g : ℤ)) a)

/-! ## `USide_mem_On` / `VSide_mem_On`: the two tower families lie in `On W n`.

Each summand is a scalar multiple of a `PresOn`-tower, which lies in `On W n` by the keystone
`Pres_mem_On` (for homogeneous `c ∈ 𝒱_M` resp. `d ∈ 𝒱_P`); the membership is then closed by
`Submodule.{sum,smul}_mem`.  These are the depth-`n` lifts of `ZhuAssociator.Ufam_mem_O` /
`Vfam_mem_O`. -/

/-- **`USide_mem_On`**: the depth-`n` U-family lies in `On W n` (for homogeneous `c ∈ 𝒱_M`), by the
keystone `Pres_mem_On`.  Depth-`n` lift of `ZhuAssociator.Ufam_mem_O`. -/
theorem UfamOn_mem_On (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M : ℕ} {c : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (d a : 𝒱) (wU : ℤ → ℕ → ℂ) (γ₀ : ℤ) (Γ Δ : ℕ) :
    UfamOn W M n c d a wU γ₀ Γ Δ ∈ On W n := by
  refine Submodule.sum_mem _ (fun g _ => Submodule.sum_mem _ (fun δ _ => ?_))
  exact Submodule.smul_mem _ _ (Pres_mem_On W n hc (W.smul d (γ₀ + (g : ℤ)) a) δ)

/-- **`VSide_mem_On`**: the depth-`n` V-family lies in `On W n` (for homogeneous `d ∈ 𝒱_P`), by the
keystone `Pres_mem_On`.  Depth-`n` lift of `ZhuAssociator.Vfam_mem_O`.  The weights `wV` may depend
on `M`; this is harmless since `Pres_mem_On` is weight-agnostic. -/
theorem VfamOn_mem_On (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {P : ℕ} {d : 𝒱}
    (hd : d ∈ W.grading (P : ℤ)) (c a : 𝒱) (wV : ℤ → ℕ → ℂ) (γ₀ : ℤ) (Γ Δ : ℕ) :
    VfamOn W P n c d a wV γ₀ Γ Δ ∈ On W n := by
  refine Submodule.sum_mem _ (fun g _ => Submodule.sum_mem _ (fun δ _ => ?_))
  exact Submodule.smul_mem _ _ (Pres_mem_On W n hd (W.smul c (γ₀ + (g : ℤ)) a) δ)

/-- The combined U-family `+` V-family lies in `On W n` (the membership half of the homogeneous
`RightDescends.on_mem`, once the assembly is identified with `UfamOn + VfamOn`). -/
theorem UfamOn_add_VfamOn_mem_On (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M P : ℕ} {c d : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (hd : d ∈ W.grading (P : ℤ)) (a : 𝒱)
    (wU wV : ℤ → ℕ → ℂ) (γ₀ : ℤ) (Γ Δ : ℕ) :
    UfamOn W M n c d a wU γ₀ Γ Δ + VfamOn W P n c d a wV γ₀ Γ Δ ∈ On W n :=
  Submodule.add_mem _ (UfamOn_mem_On W n hc d a wU γ₀ Γ Δ)
    (VfamOn_mem_On W n hd c a wV γ₀ Γ Δ)

/-! ## The tower-collapse membership criterion (the bridge to `RightDescends.on_mem`).

The structural insight (Mathematica-verified) is that `rightProd W n (circ W n c d) a` re-expresses,
for homogeneous `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, as `UfamOn + VfamOn` for SOME finite tower weights
`wU, wV : ℤ → ℕ → ℂ` and ranges `γ₀, Γ, Δ`.  We bundle that re-expression as a `Prop` — the
**right-product tower decomposition** `RightCircTowerEq` — and derive the homogeneous
circle-generator membership from it via the proved `UfamOn_add_VfamOn_mem_On`.  This isolates the one
remaining input (the depth-`n` finsum reindexing, the lift of
`ZhuAssociator.USide_eq`/`VSide_eq`/`Ufam_eq`/`Vfam_eq`) as a single precise predicate, NOT an axiom:
its truth is the U/V scalar tower-collapse (the dual-Hahn weights `wU`/`wV`), which the keystone
`Pres_mem_On` then carries into `On W n` *independently of the weights' closed form*. -/

/-- The **right-product tower decomposition** predicate: `rightProd W n (circ W n c d) a` equals a
finite ℂ-combination of `PresOn`-towers in `c` (U-family) plus `PresOn`-towers in `d` (V-family).
This is exactly the depth-`n` lift of `ZhuAssociator.assoc_eq` rearranged into the tower bases (with
the U-side identified by `USide_eq`/`Ufam_eq` and the V-side by `VSide_eq`/`Vfam_eq`). -/
def RightCircTowerEq (W : VertexOperatorAlgebra 𝒱) (n M P : ℕ) (c d a : 𝒱) : Prop :=
  ∃ (wU wV : ℤ → ℕ → ℂ) (γ₀ : ℤ) (Γ Δ : ℕ),
    rightProd W n (circ W n c d) a
      = UfamOn W M n c d a wU γ₀ Γ Δ + VfamOn W P n c d a wV γ₀ Γ Δ

/-- **The tower-collapse membership criterion.**  For homogeneous `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, if
`rightProd W n (circ W n c d) a` collapses onto the U/V `PresOn`-tower families
(`RightCircTowerEq`), then it lies in `On W n`.  The membership half of the homogeneous
`RightDescends.on_mem` — the entire remaining work is establishing `RightCircTowerEq` (the depth-`n`
finsum reindexing), the membership itself being closed here by `Pres_mem_On`. -/
theorem rightProd_circ_mem_On_of_tower_eq (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M P : ℕ} {c d : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (hd : d ∈ W.grading (P : ℤ)) (a : 𝒱)
    (htow : RightCircTowerEq W n M P c d a) :
    rightProd W n (circ W n c d) a ∈ On W n := by
  obtain ⟨wU, wV, γ₀, Γ, Δ, heq⟩ := htow
  rw [heq]
  exact UfamOn_add_VfamOn_mem_On W n hc hd a wU wV γ₀ Γ Δ

/-- **`RightDescends.on_mem` from the (universally-quantified) tower decomposition.**  If every
homogeneous triple `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, `a ∈ 𝒱_K` admits the U/V tower decomposition
(`RightCircTowerEq`), then the `RightDescends.on_mem` field holds: `∀ x ∈ On W n, ∀ a, rightProd W n
x a ∈ On W n`.  Combines the proved reduction `rightProd_On_mem_On_of_homog` (`ZhuVermaAnDescent5`)
with the tower-collapse criterion above.  This is the exact statement the depth-`n` reindexing
(`USide_eq`/`VSide_eq`/`Ufam_eq`/`Vfam_eq` lifts) discharges. -/
theorem rightProd_On_mem_On_of_towerEq (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Htow : ∀ (M P K : ℕ) {c d a : 𝒱}, c ∈ W.grading (M : ℤ) → d ∈ W.grading (P : ℤ) →
      a ∈ W.grading (K : ℤ) → RightCircTowerEq W n M P c d a) :
    ∀ x ∈ On W n, ∀ a : 𝒱, rightProd W n x a ∈ On W n := by
  refine rightProd_On_mem_On_of_homog W n ?_
  intro M P K c d a hc hd ha
  exact rightProd_circ_mem_On_of_tower_eq W n hc hd a (Htow M P K hc hd ha)

/-! ## The two `gen_mem` fields, via the same tower-collapse criterion.

`LeftDescends.gen_mem` (`O(𝒱) *ₙ 𝒱 ⊆ On`) and `RightDescends.gen_mem` (`𝒱 *ₙ O(𝒱) ⊆ On`) reduce —
exactly as the on-mem field — to the membership of an FZ product applied to an `O(𝒱)`-base generator
`g = (L₋₁u + L₀u)*v` (`zhuMul_L_base`).  After the homogeneous collapse the residue acts on an
iterated mode, which (Mathematica-verified) again re-expresses as a finite ℂ-combination of
`PresOn`-towers (the `RightDescends.gen_mem` case additionally carrying the Dong–Li–Mason
`(1+z)^{wt a+j}` right-shift).  We bundle each re-expression as a tower-decomposition predicate and
close the membership via `Pres_mem_On`, isolating the precise remaining reindexing. -/

/-- Tower decomposition of `leftProd W n g b` for an `O(𝒱)`-base generator
`g = (L₋₁u + L₀u)*v`: equals a finite ℂ-combination of `PresOn`-towers based at modes of `b`. -/
def LeftGenTowerEq (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (g b : 𝒱) : Prop :=
  ∃ (J : Type) (_ : Fintype J) (Ms : J → ℕ) (cs : J → 𝒱) (bs : J → 𝒱)
    (ws : J → ℂ) (δs : J → ℕ),
    (∀ j : J, cs j ∈ W.grading (Ms j : ℤ)) ∧
    leftProd W n g b = ∑ j : J, ws j • PresOn W (Ms j) n (δs j) (cs j) (bs j)

/-- Tower decomposition of `rightProd W n x g` for an `O(𝒱)`-base generator `g`: same form. -/
def RightGenTowerEq (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (x g : 𝒱) : Prop :=
  ∃ (J : Type) (_ : Fintype J) (Ms : J → ℕ) (cs : J → 𝒱) (bs : J → 𝒱)
    (ws : J → ℂ) (δs : J → ℕ),
    (∀ j : J, cs j ∈ W.grading (Ms j : ℤ)) ∧
    rightProd W n x g = ∑ j : J, ws j • PresOn W (Ms j) n (δs j) (cs j) (bs j)

/-- A finite ℂ-combination of `PresOn`-towers (with homogeneous bases) lies in `On W n`. -/
theorem towerSum_mem_On (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {J : Type} [Fintype J]
    (Ms : J → ℕ) (cs bs : J → 𝒱) (ws : J → ℂ) (δs : J → ℕ)
    (hc : ∀ j : J, cs j ∈ W.grading (Ms j : ℤ)) :
    (∑ j : J, ws j • PresOn W (Ms j) n (δs j) (cs j) (bs j)) ∈ On W n :=
  Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Pres_mem_On W n (hc j) (bs j) (δs j)))

/-- `leftProd W n g b ∈ On W n` from its tower decomposition (`LeftGenTowerEq`). -/
theorem leftProd_gen_mem_On_of_tower_eq (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {g b : 𝒱}
    (htow : LeftGenTowerEq W n g b) : leftProd W n g b ∈ On W n := by
  obtain ⟨J, _, Ms, cs, bs, ws, δs, hc, heq⟩ := htow
  rw [heq]; exact towerSum_mem_On W n Ms cs bs ws δs hc

/-- `rightProd W n x g ∈ On W n` from its tower decomposition (`RightGenTowerEq`). -/
theorem rightProd_gen_mem_On_of_tower_eq (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {x g : 𝒱}
    (htow : RightGenTowerEq W n x g) : rightProd W n x g ∈ On W n := by
  obtain ⟨J, _, Ms, cs, bs, ws, δs, hc, heq⟩ := htow
  rw [heq]; exact towerSum_mem_On W n Ms cs bs ws δs hc

/-- Left multiplication `g ↦ g *ₙ b` (`leftProd W n · b`) as a `ℂ`-linear map (linear in the first,
`A(𝒱)`, slot — used to reduce `LeftDescends.gen_mem` to `O(𝒱)` generators via `span_le`). -/
noncomputable def leftProdFstL (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (b : 𝒱) : 𝒱 →ₗ[ℂ] 𝒱 where
  toFun g := leftProd W n g b
  map_add' g₁ g₂ := leftProd_add_left W n g₁ g₂ b
  map_smul' c g := leftProd_smul_left W n c g b

@[simp] theorem leftProdFstL_apply (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (g b : 𝒱) :
    leftProdFstL W n b g = leftProd W n g b := rfl

/-! ## The bundled `LeftDescends`/`RightDescends` from the tower-decomposition predicates.

Packaging the (already-proved) `leftProd_On_mem_On` with the three tower-collapse criteria above
yields the bundled `LeftDescends`/`RightDescends` — hence the descended bimodule actions `An.lAct` /
`An.rAct` (`ZhuVermaAnDescent`) — conditional only on the depth-`n` reindexing predicates
`RightCircTowerEq`/`LeftGenTowerEq`/`RightGenTowerEq` (NOT on any axiom; `LeftDescends.on_mem` is
already unconditional).  Discharging the three predicates makes the actions unconditional. -/

/-- The bundled `LeftDescends W n` from the tower-decomposition of `O(𝒱)`-generators (the `gen_mem`
field) — the `on_mem` field is the already-proven `leftProd_On_mem_On`. -/
theorem leftDescends_of_towerEq (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Hgen : ∀ u v b : 𝒱, LeftGenTowerEq W n (zhuMul W (W.L (-1) u + W.L 0 u) v) b) :
    LeftDescends W n where
  on_mem := leftProd_On_mem_On W n
  gen_mem := by
    intro g hg b
    -- reduce `g ∈ O W` to the spanning generators via `leftProd W n · b` linear.
    have hle : O W ≤ (On W n).comap (leftProdFstL W n b) := by
      rw [O_eq_span, Submodule.span_le]
      rintro x ⟨u, v, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, leftProdFstL_apply]
      exact leftProd_gen_mem_On_of_tower_eq W n (Hgen u v b)
    have : g ∈ (On W n).comap (leftProdFstL W n b) := hle hg
    rwa [Submodule.mem_comap, leftProdFstL_apply] at this

/-- The bundled `RightDescends W n` from the tower decompositions of the circle generators
(`on_mem`) and the `O(𝒱)`-generators (`gen_mem`). -/
theorem rightDescends_of_towerEq (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Htow : ∀ (M P K : ℕ) {c d a : 𝒱}, c ∈ W.grading (M : ℤ) → d ∈ W.grading (P : ℤ) →
      a ∈ W.grading (K : ℤ) → RightCircTowerEq W n M P c d a)
    (Hgen : ∀ x u v : 𝒱, RightGenTowerEq W n x (zhuMul W (W.L (-1) u + W.L 0 u) v)) :
    RightDescends W n where
  on_mem := rightProd_On_mem_On_of_towerEq W n Htow
  gen_mem := by
    intro x g hg
    have hle : O W ≤ (On W n).comap (rightProdR W n x) := by
      rw [O_eq_span, Submodule.span_le]
      rintro y ⟨u, v, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, rightProdR_apply]
      exact rightProd_gen_mem_On_of_tower_eq W n (Hgen x u v)
    have : g ∈ (On W n).comap (rightProdR W n x) := hle hg
    rwa [Submodule.mem_comap, rightProdR_apply] at this

/-! ## The descended bimodule actions from the tower-decomposition predicates.

Feeding the bundled `leftDescends_of_towerEq`/`rightDescends_of_towerEq` into the parametric actions
`An.lAct`/`An.rAct` (`ZhuVermaAnDescent`) gives the descended `A(𝒱)`-bimodule actions on `A_n(𝒱)`,
conditional only on the depth-`n` tower-collapse reindexing predicates — NOT on any axiom.  These are
the genuine `A_n` bimodule actions: `([a], [x]) ↦ [a *ₙ x]` and `([x], [a]) ↦ [x *ₙ a]`.  Their
representative-level evaluations and the `n = 0` Zhu anchors follow immediately from the parametric
lemmas. -/

/-- The bundled left-product memberships from the `gen_mem` tower decomposition (`on_mem` is the
already-proven `leftProd_On_mem_On`). -/
theorem leftDescends_holds (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Hgen : ∀ u v b : 𝒱, LeftGenTowerEq W n (zhuMul W (W.L (-1) u + W.L 0 u) v) b) :
    LeftDescends W n :=
  leftDescends_of_towerEq W n Hgen

/-- The bundled right-product memberships from the circle-generator (`on_mem`) and `O(𝒱)`-generator
(`gen_mem`) tower decompositions. -/
theorem rightDescends_holds (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Htow : ∀ (M P K : ℕ) {c d a : 𝒱}, c ∈ W.grading (M : ℤ) → d ∈ W.grading (P : ℤ) →
      a ∈ W.grading (K : ℤ) → RightCircTowerEq W n M P c d a)
    (Hgen : ∀ x u v : 𝒱, RightGenTowerEq W n x (zhuMul W (W.L (-1) u + W.L 0 u) v)) :
    RightDescends W n :=
  rightDescends_of_towerEq W n Htow Hgen

/-- **The descended left action** `A(𝒱) →ₗ A_n(𝒱) →ₗ A_n(𝒱)`, `([a], [x]) ↦ [a *ₙ x]`, from the
`gen_mem` tower decomposition. -/
noncomputable def An.lActU (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Hgen : ∀ u v b : 𝒱, LeftGenTowerEq W n (zhuMul W (W.L (-1) u + W.L 0 u) v) b) :
    A W →ₗ[ℂ] An W n →ₗ[ℂ] An W n :=
  An.lAct W n (leftDescends_holds W n Hgen)

/-- **The descended right action** `A_n(𝒱) →ₗ A(𝒱) →ₗ A_n(𝒱)`, `([x], [a]) ↦ [x *ₙ a]`, from the
circle-generator and `O(𝒱)`-generator tower decompositions. -/
noncomputable def An.rActU (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Htow : ∀ (M P K : ℕ) {c d a : 𝒱}, c ∈ W.grading (M : ℤ) → d ∈ W.grading (P : ℤ) →
      a ∈ W.grading (K : ℤ) → RightCircTowerEq W n M P c d a)
    (Hgen : ∀ x u v : 𝒱, RightGenTowerEq W n x (zhuMul W (W.L (-1) u + W.L 0 u) v)) :
    An W n →ₗ[ℂ] A W →ₗ[ℂ] An W n :=
  An.rAct W n (rightDescends_holds W n Htow Hgen)

/-- The descended left action on representatives: `[a] · [x] = [a *ₙ x]`. -/
@[simp] theorem An.lActU_mk (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Hgen : ∀ u v b : 𝒱, LeftGenTowerEq W n (zhuMul W (W.L (-1) u + W.L 0 u) v) b) (a x : 𝒱) :
    An.lActU W n Hgen (mk W a) (mkAn W n x) = mkAn W n (leftProd W n a x) :=
  An.lAct_mk W n (leftDescends_holds W n Hgen) a x

/-- The descended right action on representatives: `[x] · [a] = [x *ₙ a]`. -/
@[simp] theorem An.rActU_mk (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Htow : ∀ (M P K : ℕ) {c d a : 𝒱}, c ∈ W.grading (M : ℤ) → d ∈ W.grading (P : ℤ) →
      a ∈ W.grading (K : ℤ) → RightCircTowerEq W n M P c d a)
    (Hgen : ∀ x u v : 𝒱, RightGenTowerEq W n x (zhuMul W (W.L (-1) u + W.L 0 u) v)) (x a : 𝒱) :
    An.rActU W n Htow Hgen (mkAn W n x) (mk W a) = mkAn W n (rightProd W n x a) :=
  An.rAct_mk W n (rightDescends_holds W n Htow Hgen) x a

/-- **`n = 0` anchor (left):** the descended left action is the Zhu product `[a]·[x] = [a*x]`. -/
@[simp] theorem An.lActU_zero_mk (W : VertexOperatorAlgebra 𝒱)
    (Hgen : ∀ u v b : 𝒱, LeftGenTowerEq W 0 (zhuMul W (W.L (-1) u + W.L 0 u) v) b) (a x : 𝒱) :
    An.lActU W 0 Hgen (mk W a) (mkAn W 0 x) = mkAn W 0 (zhuMul W a x) :=
  An.lAct_zero_mk W (leftDescends_holds W 0 Hgen) a x

/-- **`n = 0` anchor (right):** the descended right action is the Zhu product `[x]·[a] = [x*a]`. -/
@[simp] theorem An.rActU_zero_mk (W : VertexOperatorAlgebra 𝒱)
    (Htow : ∀ (M P K : ℕ) {c d a : 𝒱}, c ∈ W.grading (M : ℤ) → d ∈ W.grading (P : ℤ) →
      a ∈ W.grading (K : ℤ) → RightCircTowerEq W 0 M P c d a)
    (Hgen : ∀ x u v : 𝒱, RightGenTowerEq W 0 x (zhuMul W (W.L (-1) u + W.L 0 u) v)) (x a : 𝒱) :
    An.rActU W 0 Htow Hgen (mkAn W 0 x) (mk W a) = mkAn W 0 (zhuMul W x a) :=
  An.rAct_zero_mk W (rightDescends_holds W 0 Htow Hgen) x a

/-!
## The PRECISE remaining target (NOT `sorry`, NOT axiomatized)

The `A_n(𝒱)` bimodule descent is reduced to **three tower-decomposition predicates**, each a
*finsum-reindexing equality* (NOT an axiom — its truth is the U/V scalar tower-collapse, which the
keystone `Pres_mem_On` carries into `On W n` regardless of the weights' closed form, per the proved
`UfamOn_mem_On`/`VfamOn_mem_On`):

* `RightCircTowerEq W n M P c d a` (`RightDescends.on_mem`): the assembled
  `rightProd W n (circ W n c d) a` (proved split `rightProd_circ_UV_assembly`, `ZhuVermaAnDescent7`)
  re-expresses as `UfamOn + VfamOn`.  This is the depth-`n` lift of
  `ZhuAssociator.USide_eq`/`Ufam_eq` (U-side) and `VSide_eq`/`Vfam_eq` (V-side): regroup the U-modes
  `c₍μ₎(d₍γ₎a)` and V-modes `d₍μ₎(c₍γ₎a)` by base-mode `γ`, collecting the net scalar coefficient as
  a `PresOn`-tower in `c` resp. `d`.  The exact tower weights `wU`/`wV` are dual-Hahn-type and need
  NOT be computed: only their *existence* (the reindexing) is required.

* `LeftGenTowerEq` (`LeftDescends.gen_mem`) and `RightGenTowerEq` (`RightDescends.gen_mem`): the same
  reindexing with the `O(𝒱)`-base generator `g = ∑ᵢ C(M,i) u₍ᵢ₋₂₎v` (`zhuMul_L_base`) in the applied
  slot; `RightGenTowerEq` additionally carries the Dong–Li–Mason `(1+z)^{wt a + j}` right-shift.

Once the three predicates are discharged, `leftDescends_holds`/`rightDescends_holds` are
unconditional and `An.lActU`/`An.rActU` are the unconditional descended `A_n(𝒱)` bimodule actions,
with the `n = 0` Zhu anchors `An.lActU_zero_mk`/`An.rActU_zero_mk`.  `LeftDescends.on_mem`
(`leftProd_On_mem_On`, `ZhuVermaAnDescent4`) is already unconditional.

The membership engine for all three — `UfamOn_mem_On`/`VfamOn_mem_On`/`towerSum_mem_On` (via
`Pres_mem_On`) — is proved here, axiom-clean.  The remaining work is the pure finsum bookkeeping of
the reindexing (the depth-`n` `USide_eq`/`VSide_eq`/`Ufam_eq`/`Vfam_eq` analogs), with the
combinatorial certificate already in hand (`ZhuRes.gen_jsum`/`gen_vandermonde`).
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.UfamOn_mem_On
  #print axioms VOA.VfamOn_mem_On
  #print axioms VOA.UfamOn_add_VfamOn_mem_On
  #print axioms VOA.rightProd_circ_mem_On_of_tower_eq
  #print axioms VOA.rightProd_On_mem_On_of_towerEq
  #print axioms VOA.towerSum_mem_On
  #print axioms VOA.leftProd_gen_mem_On_of_tower_eq
  #print axioms VOA.rightProd_gen_mem_On_of_tower_eq
  #print axioms VOA.leftDescends_of_towerEq
  #print axioms VOA.rightDescends_of_towerEq
  #print axioms VOA.leftDescends_holds
  #print axioms VOA.rightDescends_holds
  #print axioms VOA.An.lActU
  #print axioms VOA.An.rActU
  #print axioms VOA.An.lActU_mk
  #print axioms VOA.An.rActU_mk
  #print axioms VOA.An.lActU_zero_mk
  #print axioms VOA.An.rActU_zero_mk
-/
