/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnDescent12

/-!
# The `PresOn`-tower-decomposition predicate as plain `Oₙ(𝒱)`-membership.

This file continues `Modules.ZhuVermaAnDescent12` (the homogeneous-iterate routing of the two
`O(𝒱)`-generator predicates `LeftGenTowerEq_holds`/`RightGenTowerEq_holds`).

The two `gen_mem` tower-decomposition predicates `LeftGenTowerEq`/`RightGenTowerEq`
(`ZhuVermaAnDescent8`) are *existentials* over an abstract finite `PresOn`-tower index `J`:

  `∃ (J : Type) [Fintype J] (Ms : J → ℕ) (cs bs : J → 𝒱) (ws : J → ℂ) (δs : J → ℕ),
     (∀ j, cs j ∈ 𝒱_{Ms j}) ∧ leftProd W n g b = ∑ j, ws j • PresOn W (Ms j) n (δs j) (cs j) (bs j)`

(resp. `rightProd W n x g`).  We isolate the *shape* of that RHS as a free-standing predicate
`TowerDecomp W n x` ("`x` admits a finite ℂ-combination of homogeneous-based `PresOn`-towers"), and
prove the **exact characterization**

  `TowerDecomp W n x ↔ x ∈ Oₙ(𝒱)`     (`TowerDecomp_iff_mem_On`).

* `(⟹)` is the proved `towerSum_mem_On` (`ZhuVermaAnDescent8`): every `PresOn`-tower lies in `Oₙ` by
  the keystone `Pres_mem_On`.
* `(⟸)` is a `Submodule.span_induction` on `Oₙ = span {circ W n a b}` (`On_eq_span`): the predicate
  `TowerDecomp` is closed under `0`/`+`/`• c`, and every circle generator `circ W n a b` is itself a
  finite homogeneous-`PresOn`-tower combination (`circ_TowerDecomp`, via `reduce_homogeneous` +
  `PresOn_zero` — a homogeneous `circ` IS a single depth-`0` `PresOn`).

Since `LeftGenTowerEq W n g b` is *definitionally* `TowerDecomp W n (leftProd W n g b)` and
`RightGenTowerEq W n x g` is `TowerDecomp W n (rightProd W n x g)`, this yields the clean
equivalences

  `LeftGenTowerEq W n g b ↔ leftProd W n g b ∈ Oₙ(𝒱)`     (`LeftGenTowerEq_iff_mem_On`),
  `RightGenTowerEq W n x g ↔ rightProd W n x g ∈ Oₙ(𝒱)`   (`RightGenTowerEq_iff_mem_On`),

replacing the two abstract existential reindexing predicates by concrete `Oₙ`-membership goals — the
genuine FZ `gen_mem` memberships `O(𝒱) *ₙ 𝒱 ⊆ Oₙ` and `𝒱 *ₙ O(𝒱) ⊆ Oₙ`.  We record the conditional
closures `LeftGenTowerEq_holds_of_mem`/`RightGenTowerEq_holds_of_mem`: supplying those memberships
(for the `O(𝒱)`-base generator `g = (L₋₁u+L₀u)*v`) discharges `LeftGenTowerEq_holds`/
`RightGenTowerEq_holds` outright — NO dual-Hahn weight, NO `UfamOn`/`VfamOn` matching, NO finsum
reindexing required for the *gen* predicates.

## References
* Gannon §5.3.2, Thm 5.3.4; Zhu Thm 2.1.1/2.1.2; Frenkel–Zhu Lemma 2.1.1/2.1.2; Dong–Li–Mason.
-/

open scoped BigOperators
open Finset

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators
open Classical

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The `PresOn`-tower-decomposition predicate. -/

/-- **`x` admits a finite homogeneous-`PresOn`-tower decomposition.**  This is exactly the RHS shape
of the `gen_mem` predicates `LeftGenTowerEq`/`RightGenTowerEq` (`ZhuVermaAnDescent8`), abstracted
away from the specific element being decomposed:
`x = ∑_j ws j • PresOn W (Ms j) n (δs j) (cs j) (bs j)` for some finite tower index `J`, with each
acting vector `cs j` homogeneous of grade `Ms j`. -/
def TowerDecomp (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (x : 𝒱) : Prop :=
  ∃ (J : Type) (_ : Fintype J) (Ms : J → ℕ) (cs : J → 𝒱) (bs : J → 𝒱)
    (ws : J → ℂ) (δs : J → ℕ),
    (∀ j : J, cs j ∈ W.grading (Ms j : ℤ)) ∧
    x = ∑ j : J, ws j • PresOn W (Ms j) n (δs j) (cs j) (bs j)

/-- By definition, `LeftGenTowerEq W n g b` is `TowerDecomp W n (leftProd W n g b)`. -/
theorem leftGenTowerEq_eq_towerDecomp (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (g b : 𝒱) :
    LeftGenTowerEq W n g b = TowerDecomp W n (leftProd W n g b) := rfl

/-- By definition, `RightGenTowerEq W n x g` is `TowerDecomp W n (rightProd W n x g)`. -/
theorem rightGenTowerEq_eq_towerDecomp (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (x g : 𝒱) :
    RightGenTowerEq W n x g = TowerDecomp W n (rightProd W n x g) := rfl

/-! ## Closure of `TowerDecomp` under the `Submodule` operations. -/

/-- `0` admits a (empty) tower decomposition. -/
theorem TowerDecomp_zero (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : TowerDecomp W n (0 : 𝒱) :=
  ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, PEmpty.elim, PEmpty.elim, PEmpty.elim,
    (fun j => j.elim), by simp only [Finset.univ_eq_empty, Finset.sum_empty]⟩

/-- `TowerDecomp` is closed under scalar multiplication (scale every tower weight). -/
theorem TowerDecomp_smul (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (c : ℂ) {x : 𝒱}
    (hx : TowerDecomp W n x) : TowerDecomp W n (c • x) := by
  obtain ⟨J, _, Ms, cs, bs, ws, δs, hc, heq⟩ := hx
  refine ⟨J, ‹_›, Ms, cs, bs, fun j => c * ws j, δs, hc, ?_⟩
  rw [heq, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [mul_smul]

/-- `TowerDecomp` is closed under addition (concatenate the two tower indices as `J₁ ⊕ J₂`). -/
theorem TowerDecomp_add (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {x y : 𝒱}
    (hx : TowerDecomp W n x) (hy : TowerDecomp W n y) : TowerDecomp W n (x + y) := by
  obtain ⟨J₁, _, Ms₁, cs₁, bs₁, ws₁, δs₁, hc₁, heq₁⟩ := hx
  obtain ⟨J₂, _, Ms₂, cs₂, bs₂, ws₂, δs₂, hc₂, heq₂⟩ := hy
  refine ⟨J₁ ⊕ J₂, inferInstance,
    Sum.elim Ms₁ Ms₂, Sum.elim cs₁ cs₂, Sum.elim bs₁ bs₂, Sum.elim ws₁ ws₂, Sum.elim δs₁ δs₂,
    ?_, ?_⟩
  · rintro (j | j)
    · exact hc₁ j
    · exact hc₂ j
  · rw [heq₁, heq₂, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]

/-! ## Each circle generator admits a tower decomposition. -/

/-- A *homogeneous* circle product is a single depth-`0` `PresOn`-tower (`PresOn_zero`). -/
theorem circ_homog_TowerDecomp (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M : ℕ} {a : 𝒱}
    (ha : a ∈ W.grading (M : ℤ)) (b : 𝒱) : TowerDecomp W n (circ W n a b) := by
  refine ⟨PUnit, inferInstance, fun _ => M, fun _ => a, fun _ => b, fun _ => 1, fun _ => 0,
    fun _ => ha, ?_⟩
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_punit, one_smul, one_smul,
    PresOn_zero W ha b]

/-- **Every circle generator `circ W n a b` admits a tower decomposition** (arbitrary `a`, `b`):
reduce `a` to homogeneous slices (`reduce_homogeneous`); each homogeneous slice is a depth-`0`
`PresOn`-tower (`circ_homog_TowerDecomp`); closure under `0`/`+` (`TowerDecomp_zero`/`_add`). -/
theorem circ_TowerDecomp (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a b : 𝒱) :
    TowerDecomp W n (circ W n a b) := by
  refine reduce_homogeneous W (P := fun a => TowerDecomp W n (circ W n a b)) ?_ ?_ ?_ a
  · intro k a ha
    rcases lt_or_ge k 0 with hk | hk
    · rw [W.positivity k hk, Submodule.mem_bot] at ha
      subst ha; change TowerDecomp W n (circ W n 0 b)
      rw [circ_zero_left]; exact TowerDecomp_zero W n
    · obtain ⟨M, rfl⟩ : ∃ M : ℕ, k = (M : ℤ) := ⟨k.toNat, by omega⟩
      exact circ_homog_TowerDecomp W n ha b
  · change TowerDecomp W n (circ W n 0 b)
    rw [circ_zero_left]; exact TowerDecomp_zero W n
  · intro x y hx hy
    change TowerDecomp W n (circ W n (x + y) b)
    rw [circ_add_left]; exact TowerDecomp_add W n hx hy

/-! ## The exact characterization `TowerDecomp ↔ Oₙ`-membership. -/

/-- A tower decomposition lands in `Oₙ(𝒱)` (the proved `towerSum_mem_On`). -/
theorem TowerDecomp.mem_On (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {x : 𝒱}
    (hx : TowerDecomp W n x) : x ∈ On W n := by
  obtain ⟨J, _, Ms, cs, bs, ws, δs, hc, heq⟩ := hx
  rw [heq]; exact towerSum_mem_On W n Ms cs bs ws δs hc

/-- **The exact characterization.**  An element admits a `PresOn`-tower decomposition iff it lies in
`Oₙ(𝒱)`.  `(⟹)` is `TowerDecomp.mem_On` (`Pres_mem_On`); `(⟸)` is a `Submodule.span_induction` over
`Oₙ = span {circ W n a b}` (`On_eq_span`), closed by `circ_TowerDecomp`/`TowerDecomp_zero`/`_add`/
`_smul`. -/
theorem TowerDecomp_iff_mem_On (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (x : 𝒱) :
    TowerDecomp W n x ↔ x ∈ On W n := by
  refine ⟨TowerDecomp.mem_On W n, fun hx => ?_⟩
  rw [On_eq_span] at hx
  refine Submodule.span_induction
    (p := fun x _ => TowerDecomp W n x) ?_ ?_ ?_ ?_ hx
  · rintro x ⟨a, b, rfl⟩; exact circ_TowerDecomp W n a b
  · exact TowerDecomp_zero W n
  · intro y z _ _ hy hz; exact TowerDecomp_add W n hy hz
  · intro c y _ hy; exact TowerDecomp_smul W n c hy

/-! ## The `gen_mem` predicates as plain `Oₙ`-membership, and the conditional `_holds`. -/

/-- **`LeftGenTowerEq` is plain `Oₙ`-membership of `leftProd`.** -/
theorem LeftGenTowerEq_iff_mem_On (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (g b : 𝒱) :
    LeftGenTowerEq W n g b ↔ leftProd W n g b ∈ On W n :=
  TowerDecomp_iff_mem_On W n (leftProd W n g b)

/-- **`RightGenTowerEq` is plain `Oₙ`-membership of `rightProd`.** -/
theorem RightGenTowerEq_iff_mem_On (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (x g : 𝒱) :
    RightGenTowerEq W n x g ↔ rightProd W n x g ∈ On W n :=
  TowerDecomp_iff_mem_On W n (rightProd W n x g)

/-- **`LeftGenTowerEq_holds` from the genuine FZ `gen_mem` membership** `O(𝒱) *ₙ 𝒱 ⊆ Oₙ`.  If, for
every `u v b`, `leftProd W n ((L₋₁u+L₀u)*v) b ∈ Oₙ`, then the `O(𝒱)`-generator tower-decomposition
predicate holds for every `u v b`.  (The membership is the `LeftDescends.gen_mem` field; the tower
decomposition is then automatic by `TowerDecomp_iff_mem_On`.) -/
theorem LeftGenTowerEq_holds_of_mem (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Hmem : ∀ u v b : 𝒱, leftProd W n (zhuMul W (W.L (-1) u + W.L 0 u) v) b ∈ On W n)
    (u v b : 𝒱) : LeftGenTowerEq W n (zhuMul W (W.L (-1) u + W.L 0 u) v) b :=
  (LeftGenTowerEq_iff_mem_On W n _ b).mpr (Hmem u v b)

/-- **`RightGenTowerEq_holds` from the genuine FZ `gen_mem` membership** `𝒱 *ₙ O(𝒱) ⊆ Oₙ`. -/
theorem RightGenTowerEq_holds_of_mem (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Hmem : ∀ x u v : 𝒱, rightProd W n x (zhuMul W (W.L (-1) u + W.L 0 u) v) ∈ On W n)
    (x u v : 𝒱) : RightGenTowerEq W n x (zhuMul W (W.L (-1) u + W.L 0 u) v) :=
  (RightGenTowerEq_iff_mem_On W n x _).mpr (Hmem x u v)

/-!
## What this proves and the PRECISE remaining target (NOT `sorry`, NOT axiomatized)

Proved here (axiom-clean: `[propext, Classical.choice, Quot.sound]`):

* `TowerDecomp` — the `PresOn`-tower-decomposition predicate (the RHS shape of the `gen_mem`
  predicates), with `leftGenTowerEq_eq_towerDecomp`/`rightGenTowerEq_eq_towerDecomp` identifying the
  two `gen_mem` predicates as `TowerDecomp` of `leftProd`/`rightProd`.
* `TowerDecomp_zero` / `TowerDecomp_smul` / `TowerDecomp_add` — closure under the `Submodule`
  operations (empty / scaled / `J₁ ⊕ J₂` tower indices).
* `circ_homog_TowerDecomp` / `circ_TowerDecomp` — every circle generator is a tower combination
  (homogeneous slice = depth-`0` `PresOn` via `PresOn_zero`; arbitrary `a` by `reduce_homogeneous`).
* **`TowerDecomp.mem_On`** / **`TowerDecomp_iff_mem_On`** — the exact characterization
  `TowerDecomp W n x ↔ x ∈ Oₙ(𝒱)` (`towerSum_mem_On` for `⟹`; `Submodule.span_induction` over
  `On_eq_span` for `⟸`).
* **`LeftGenTowerEq_iff_mem_On`** / **`RightGenTowerEq_iff_mem_On`** — the two `gen_mem`
  tower-decomposition predicates ARE plain `Oₙ`-membership of `leftProd`/`rightProd`.
* **`LeftGenTowerEq_holds_of_mem`** / **`RightGenTowerEq_holds_of_mem`** — the routing of the full
  `∀-args` `O(𝒱)`-generator predicates through the genuine FZ `gen_mem` memberships.

So the two `O(𝒱)`-generator predicates `LeftGenTowerEq_holds`/`RightGenTowerEq_holds` are reduced —
WITHOUT any dual-Hahn weight, `UfamOn`/`VfamOn` matching, or finsum reindexing — to the two FZ
`gen_mem` memberships (Frenkel–Zhu Lemma 2.1.2, the `O(𝒱)`-generator direction):

  (L-mem)  `∀ u v b, leftProd W n ((L₋₁u+L₀u)*v) b ∈ Oₙ(𝒱)`   (`O(𝒱) *ₙ 𝒱 ⊆ Oₙ`),
  (R-mem)  `∀ x u v, rightProd W n x ((L₋₁u+L₀u)*v) ∈ Oₙ(𝒱)`   (`𝒱 *ₙ O(𝒱) ⊆ Oₙ`).

These are the depth-`n` lifts of the `n = 0` two-sided-ideal memberships
`gen_mem_O`/`right_ideal_core` (`ZhuModule`/`ZhuRightIdeal`).  They are genuine VOA memberships
(NOT axioms, NOT `sorry`'d): the `O(𝒱)`-base generator `g = ∑ᵢ C(M,i) u₍ᵢ₋₂₎v` is fed into the FZ
product, and the resulting iterated residue is shown to be a span of circle products via the
associator/iterate machinery (the same engine as membership 1 `leftProd_circ_mem_On`,
`ZhuVermaAnDescent4`).  Left here as the precise stated targets; supplying either via
`LeftGenTowerEq_holds_of_mem`/`RightGenTowerEq_holds_of_mem` discharges the corresponding `_holds`
outright.

NOTE — this supersedes the homogeneous-iterate routing
`LeftGenTowerEq_holds_of_homogIterate` / `RightGenTowerEq_holds_of_homogIterate`
(`ZhuVermaAnDescent12`) as the *intended* discharge path for the gen predicates: that path's
hypothesis (`∀ K, ∀ w ∈ 𝒱_K,
LeftGenTowerEq W n w b`) is too strong (by `TowerDecomp_iff_mem_On` it would force `w *ₙ b ∈ Oₙ` for
every homogeneous `w` and every `b`, hence `Oₙ = 𝒱`), so it cannot be discharged; the membership
route `(L-mem)`/`(R-mem)` here uses the *whole* `O(𝒱)`-generator `g`, which genuinely lands in `Oₙ`.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `sorryAx`, NO `pbw`):

  #print axioms VOA.TowerDecomp_zero
  #print axioms VOA.TowerDecomp_smul
  #print axioms VOA.TowerDecomp_add
  #print axioms VOA.circ_homog_TowerDecomp
  #print axioms VOA.circ_TowerDecomp
  #print axioms VOA.TowerDecomp.mem_On
  #print axioms VOA.TowerDecomp_iff_mem_On
  #print axioms VOA.LeftGenTowerEq_iff_mem_On
  #print axioms VOA.RightGenTowerEq_iff_mem_On
  #print axioms VOA.LeftGenTowerEq_holds_of_mem
  #print axioms VOA.RightGenTowerEq_holds_of_mem
-/
