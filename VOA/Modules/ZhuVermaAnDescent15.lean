/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnDescent14

/-!
# The two `O(𝒱)`-generator `Oₙ(𝒱)`-memberships (L-mem)/(R-mem).

This file targets the two genuine FZ `gen_mem` memberships that, via `LeftGenTowerEq_holds_of_mem` /
`RightGenTowerEq_holds_of_mem` (`ZhuVermaAnDescent13`), discharge the `O(𝒱)`-generator predicates
`LeftGenTowerEq_holds` / `RightGenTowerEq_holds` (`ZhuVermaAnDescent8`):

* **(L-mem)** `∀ u v b, leftProd W n ((L₋₁u+L₀u)*v) b ∈ Oₙ(𝒱)`   (`O(𝒱) *ₙ 𝒱 ⊆ Oₙ`);
* **(R-mem)** `∀ x u v, rightProd W n x ((L₋₁u+L₀u)*v) ∈ Oₙ(𝒱)`  (`𝒱 *ₙ O(𝒱) ⊆ Oₙ`).

These are the depth-`n` lifts of the `n = 0` two-sided-ideal cores `ZhuRingResidue.left_ideal_gen_of_assoc`
(left, via `associator_core`) and `ZhuHR.right_ideal_core` (right).

## The `n = 0` collapse `Oₙ(𝒱) = O(𝒱)` and the `n = 0` anchors (proved here)

At `n = 0` both FZ products collapse to the Zhu product (`leftProd_zero`/`rightProd_zero`) and the
FZ `Oₙ` space collapses to Zhu's `O(𝒱)`.  We prove this last fact outright:

* `circ_zero_eq_gen` — for homogeneous `u ∈ 𝒱_M`, the depth-`0` circle product equals the
  `O(𝒱)`-generator: `circ W 0 u v = (L₋₁u + L₀u) * v`  (both equal `∑ᵢ C(M,i) u₍ᵢ₋₂₎v`, by
  `circ_homogeneous` at `n = 0` and `zhuMul_L_base`);
* `On_zero_eq_O` — hence `Oₙ(𝒱)` at `n = 0` is exactly Zhu's `O(𝒱)` (both `≤`-directions reduce a
  generator to homogeneous and use `circ_zero_eq_gen`).

This identifies the `n = 0` anchors of (L-mem)/(R-mem) with Zhu's two-sided-ideal theorem, fully
proved upstream (`associator_core` + `right_ideal_core`).  We package the latter unconditionally
(`O_assoc` / `O_right_ideal_gen` / `O_left_ideal_gen`) and record the anchors:

* `leftProd_genL_mem_On_zero` — (L-mem) at `n = 0` (Zhu left ideal: `O(𝒱) * 𝒱 ⊆ O(𝒱)`);
* `rightProd_genR_mem_On_zero` — (R-mem) at `n = 0` (Zhu right ideal: `𝒱 * O(𝒱) ⊆ O(𝒱)`).

## The homogeneous reduction (proved here)

Both products are *bilinear* in the slot carrying the `O(𝒱)`-base generator
`g = zhuMul W (L₋₁u + L₀u) v`, and the conformal pieces `L₋₁`, `L₀` are linear in `u`.  So the
membership statement is closed under `u = 0` and `u₁ + u₂`, and `reduce_homogeneous`
(`ZhuRingResidue`) reduces each of (L-mem)/(R-mem) to its **homogeneous-`u`** form (and, for (R-mem),
the acting factor `x` is reduced to homogeneous `x ∈ 𝒱_K` as well):

* `leftProd_genL_mem_On_of_homog` — (L-mem) for all `u v b` follows from the homogeneous-`u` version;
* `rightProd_genR_mem_On_of_homog` — (R-mem) for all `x u v` follows from the homogeneous-`x`,
  homogeneous-`u` version.

## What remains (the genuine depth-`n` FZ collapse — NOT `sorry`, NOT axiomatized)

After the homogeneous reduction, the irreducible content of each membership for `n ≥ 1` is the
depth-`n` FZ collapse for HOMOGENEOUS factors.  Via the generator entry points
`leftGenProd_homogeneous_expand` / `rightGenProd_homogeneous_expand` (`ZhuVermaAnDescent11`,
`zhuMul_L_base` + FZ bilinearity), each homogeneous membership is the finite `i`-sum

  `leftProd W n g b  = ∑_{i≤M} C(M,i) • leftProd W n (u₍ᵢ₋₂₎v) b`,
  `rightProd W n x g = ∑_{i≤M} C(M,i) • rightProd W n x (u₍ᵢ₋₂₎v)`.

The *individual* per-iterate terms `leftProd W n (u₍ᵢ₋₂₎v) b` / `rightProd W n x (u₍ᵢ₋₂₎v)` do NOT
each lie in `Oₙ` for `n ≥ 1`; expanding by `mode_split_gen` and reassembling the inner `i`-residue
gives the `O(𝒱)`-generator `(L₋₁u+L₀u) * (…)`, which lands in `O(𝒱) = Oₙ` ONLY at `n = 0`
(`On_zero_eq_O`).  For `n ≥ 1` `O(𝒱) ⊄ Oₙ(𝒱)`, so only the WHOLE `i`-sum lands in `Oₙ`, after the
Dong–Li–Mason alternating `j`-sum collapses the iterate residue onto `PresOn`-towers (each `∈ Oₙ` by
the keystone `Pres_mem_On`).  This is the SAME genuine depth-`n` U/V iterate-collapse content as the
circle case `RightCircTowerEq_holds` (`ZhuVermaAnDescent10`: `UgammaModeColl = towerCoeff`,
`VgammaModeColl = towerCoeff`, via `ZhuRes.gen_vandermonde` per FZ index `j` + `ZhuRes.gen_jsum`).
The `n ≥ 1` homogeneous targets `(L-hom)`/`(R-hom)` are left as PRECISE stated targets below, NOT
`sorry`'d and NOT axiomatized; supplying them (in the homogeneous form) discharges (L-mem)/(R-mem)
outright through the reductions proved here, and then `LeftGenTowerEq_holds` / `RightGenTowerEq_holds`
through `ZhuVermaAnDescent13`.

## References
* Gannon §5.3.2, Thm 5.3.4; Zhu Thm 2.1.1/2.1.2; Frenkel–Zhu Lemma 2.1.1/2.1.2; Dong–Li–Mason.
-/

open scoped BigOperators
open Finset

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The `n = 0` collapse `Oₙ(𝒱) = O(𝒱)`. -/

/-- **The depth-`0` circle product IS the `O(𝒱)`-generator** (homogeneous `u ∈ 𝒱_M`):
`circ W 0 u v = (L₋₁u + L₀u) * v`.  Both equal the finite residue `∑ᵢ C(M,i) u₍ᵢ₋₂₎v`
(`circ_homogeneous` at `n = 0` has weight `C(M,i)` and mode `i - 2·0 - 2 = i - 2`; `zhuMul_L_base`
expands the generator identically). -/
theorem circ_zero_eq_gen (W : VertexOperatorAlgebra 𝒱) {M : ℕ} {u : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (v : 𝒱) :
    circ W 0 u v = zhuMul W (W.L (-1) u + W.L 0 u) v := by
  rw [circ_homogeneous W 0 hu v, zhuMul_L_base W hu v]
  rw [show ((M : ℤ) + ((0 : ℕ) : ℤ)).toNat + 1 = M + 1 from by push_cast; simp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show ((M : ℤ) + ((0 : ℕ) : ℤ)) = (M : ℤ) from by push_cast; ring,
      show ((i : ℤ) - 2 * ((0 : ℕ) : ℤ) - 2) = (i : ℤ) - 2 from by push_cast; ring]

/-- Every depth-`0` circle product lies in Zhu's `O(𝒱)`: reduce `a` to homogeneous slices
(`reduce_homogeneous`); each homogeneous slice equals an `O(𝒱)`-generator (`circ_zero_eq_gen`),
which lies in `O(𝒱)` (`gen_mem_O`). -/
theorem circ_zero_mem_O (W : VertexOperatorAlgebra 𝒱) (a b : 𝒱) : circ W 0 a b ∈ O W := by
  refine reduce_homogeneous W (P := fun a => circ W 0 a b ∈ O W) ?_ ?_ ?_ a
  · intro K a ha
    rcases lt_or_ge K 0 with hK | hK
    · rw [W.positivity K hK, Submodule.mem_bot] at ha
      subst ha; rw [circ_zero_left]; exact (O W).zero_mem
    · obtain ⟨M, rfl⟩ : ∃ M : ℕ, K = (M : ℤ) := ⟨K.toNat, by omega⟩
      rw [circ_zero_eq_gen W ha b]; exact gen_mem_O W a b
  · change circ W 0 0 b ∈ O W; rw [circ_zero_left]; exact (O W).zero_mem
  · intro x y hx hy; change circ W 0 (x + y) b ∈ O W
    rw [circ_add_left]; exact (O W).add_mem hx hy

/-- Every `O(𝒱)`-generator lies in `Oₙ(𝒱)` at `n = 0`: reduce `u` to homogeneous slices; each
homogeneous slice equals a depth-`0` circle product (`circ_zero_eq_gen`), which lies in `On W 0`
(`circ_mem_On`). -/
theorem gen_mem_On_zero (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    zhuMul W (W.L (-1) u + W.L 0 u) v ∈ On W 0 := by
  refine reduce_homogeneous W (P := fun u => zhuMul W (W.L (-1) u + W.L 0 u) v ∈ On W 0) ?_ ?_ ?_ u
  · intro M u hu
    rcases lt_or_ge M 0 with hM | hM
    · rw [W.positivity M hM, Submodule.mem_bot] at hu
      subst hu
      change zhuMul W (W.L (-1) 0 + W.L 0 0) v ∈ On W 0
      simp only [map_zero, add_zero, zhuMul_zero_left]; exact (On W 0).zero_mem
    · obtain ⟨M', rfl⟩ : ∃ M' : ℕ, M = (M' : ℤ) := ⟨M.toNat, by omega⟩
      change zhuMul W (W.L (-1) u + W.L 0 u) v ∈ On W 0
      rw [← circ_zero_eq_gen W hu v]; exact circ_mem_On W 0 u v
  · change zhuMul W (W.L (-1) 0 + W.L 0 0) v ∈ On W 0
    simp only [map_zero, add_zero, zhuMul_zero_left]; exact (On W 0).zero_mem
  · intro x y hx hy
    change zhuMul W (W.L (-1) (x + y) + W.L 0 (x + y)) v ∈ On W 0
    rw [show (W.L (-1)) (x + y) + (W.L 0) (x + y)
        = ((W.L (-1)) x + (W.L 0) x) + ((W.L (-1)) y + (W.L 0) y) from by simp only [map_add]; abel,
      zhuMul_add_left]
    exact (On W 0).add_mem hx hy

/-- **`Oₙ(𝒱)` at `n = 0` is Zhu's `O(𝒱)`.**  Both `≤`-directions reduce a generator to homogeneous
slices and use the generator/circle identification `circ_zero_eq_gen`. -/
theorem On_zero_eq_O (W : VertexOperatorAlgebra 𝒱) : On W 0 = O W := by
  apply le_antisymm
  · rw [On_eq_span, Submodule.span_le]; rintro x ⟨a, b, rfl⟩; exact circ_zero_mem_O W a b
  · rw [O_eq_span, Submodule.span_le]; rintro x ⟨u, v, rfl⟩; exact gen_mem_On_zero W u v

/-! ## The `n = 0` two-sided ideal of `O(𝒱)` (Zhu Thm 2.1.1/2.1.2), packaged unconditionally. -/

/-- **Associativity mod `O(𝒱)`**, unconditional: `(u*v)*w - u*(v*w) ∈ O(𝒱)` for all `u v w`.
Reduce `u`,`v` to homogeneous (`assoc_of_homogeneous`); the homogeneous core is `associator_core`. -/
theorem O_assoc (W : VertexOperatorAlgebra 𝒱) (u v w : 𝒱) :
    zhuMul W (zhuMul W u v) w - zhuMul W u (zhuMul W v w) ∈ O W := by
  refine assoc_of_homogeneous W (fun K u hu L v hv J w _ => ?_) u v w
  rcases lt_or_ge K 0 with hK | hK
  · rw [W.positivity K hK, Submodule.mem_bot] at hu
    subst hu; simp only [zhuMul_zero_left, sub_self]; exact (O W).zero_mem
  rcases lt_or_ge L 0 with hL | hL
  · rw [W.positivity L hL, Submodule.mem_bot] at hv
    subst hv; simp only [zhuMul_zero_right, zhuMul_zero_left, sub_self]; exact (O W).zero_mem
  · obtain ⟨K', rfl⟩ : ∃ K' : ℕ, K = (K' : ℤ) := ⟨K.toNat, by omega⟩
    obtain ⟨L', rfl⟩ : ∃ L' : ℕ, L = (L' : ℤ) := ⟨L.toNat, by omega⟩
    exact associator_core W hu hv w

/-- **Right ideal generator**, unconditional: `u * ((L₋₁a+L₀a)*b) ∈ O(𝒱)` for all `u a b`.
Reduce `u`,`a` to homogeneous (`right_ideal_gen_of_homogeneous`); the homogeneous core is
`ZhuHR.right_ideal_core`. -/
theorem O_right_ideal_gen (W : VertexOperatorAlgebra 𝒱) (u a b : 𝒱) :
    zhuMul W u (zhuMul W (W.L (-1) a + W.L 0 a) b) ∈ O W := by
  refine right_ideal_gen_of_homogeneous W (fun K u hu M a ha b => ?_) u a b
  rcases lt_or_ge K 0 with hK | hK
  · rw [W.positivity K hK, Submodule.mem_bot] at hu
    subst hu; rw [zhuMul_zero_left]; exact (O W).zero_mem
  rcases lt_or_ge M 0 with hM | hM
  · rw [W.positivity M hM, Submodule.mem_bot] at ha
    subst ha; simp only [map_zero, add_zero, zhuMul_zero_left, zhuMul_zero_right]
    exact (O W).zero_mem
  · obtain ⟨K', rfl⟩ : ∃ K' : ℕ, K = (K' : ℤ) := ⟨K.toNat, by omega⟩
    obtain ⟨M', rfl⟩ : ∃ M' : ℕ, M = (M' : ℤ) := ⟨M.toNat, by omega⟩
    exact ZhuHR.right_ideal_core W hu ha b

/-- **Left ideal generator**, unconditional: `((L₋₁u+L₀u)*v) * b ∈ O(𝒱)` for all `u v b`.
The left ideal is free from associativity (`left_ideal_gen_of_assoc`, fed by `O_assoc`). -/
theorem O_left_ideal_gen (W : VertexOperatorAlgebra 𝒱) (u v b : 𝒱) :
    zhuMul W (zhuMul W (W.L (-1) u + W.L 0 u) v) b ∈ O W :=
  left_ideal_gen_of_assoc W (O_assoc W) _ ⟨u, v, rfl⟩ b

/-! ## The `n = 0` anchors of (L-mem)/(R-mem). -/

/-- **(L-mem) at `n = 0`** (Zhu's left ideal `O(𝒱) * 𝒱 ⊆ O(𝒱)`): `leftProd W 0 g b ∈ On W 0` for the
`O(𝒱)`-generator `g = (L₋₁u+L₀u)*v`.  `leftProd W 0 = zhuMul` (`leftProd_zero`), `On W 0 = O W`
(`On_zero_eq_O`), and `g * b ∈ O(𝒱)` (`O_left_ideal_gen`). -/
theorem leftProd_genL_mem_On_zero (W : VertexOperatorAlgebra 𝒱) (u v b : 𝒱) :
    leftProd W 0 (zhuMul W (W.L (-1) u + W.L 0 u) v) b ∈ On W 0 := by
  rw [leftProd_zero, On_zero_eq_O]; exact O_left_ideal_gen W u v b

/-- **(R-mem) at `n = 0`** (Zhu's right ideal `𝒱 * O(𝒱) ⊆ O(𝒱)`): `rightProd W 0 x g ∈ On W 0` for
the `O(𝒱)`-generator `g`.  `rightProd W 0 = zhuMul` (`rightProd_zero`), `On W 0 = O W`
(`On_zero_eq_O`), and `x * g ∈ O(𝒱)` (`O_right_ideal_gen`). -/
theorem rightProd_genR_mem_On_zero (W : VertexOperatorAlgebra 𝒱) (x u v : 𝒱) :
    rightProd W 0 x (zhuMul W (W.L (-1) u + W.L 0 u) v) ∈ On W 0 := by
  rw [rightProd_zero, On_zero_eq_O]; exact O_right_ideal_gen W x u v

/-! ## The `n = 0` left descent, assembled from the `n = 0` anchor. -/

/-- **`LeftDescends W 0`, unconditional.**  The `n = 0` left bimodule-descent structure is assembled
outright: its `gen_mem` field is the `n = 0` anchor (L-mem) `leftProd_genL_mem_On_zero` (Zhu's left
ideal `O(𝒱) * 𝒱 ⊆ O(𝒱)`), routed through `leftDescends_of_genMem` (`ZhuVermaAnDescent14`); the
`on_mem` field is the already-unconditional `leftProd_On_mem_On`.  (The corresponding `RightDescends`
at `n = 0` additionally needs the circle predicate `RightCircTowerEq W 0` — the (P1) target of
`ZhuVermaAnDescent10` — so it is not assembled here.) -/
theorem leftDescends_zero (W : VertexOperatorAlgebra 𝒱) : LeftDescends W 0 :=
  leftDescends_of_genMem W 0 (leftProd_genL_mem_On_zero W)

/-! ## (L-mem): the homogeneous reduction `O(𝒱) *ₙ 𝒱 ⊆ Oₙ`. -/

/-- **(L-mem) reduces to homogeneous `u`.**  The left FZ product `leftProd W n g b` of the
`O(𝒱)`-base generator `g = (L₋₁u + L₀u) * v` lands in `Oₙ(𝒱)` for ALL `u v b`, provided it does for
homogeneous `u ∈ 𝒱_M` (all `M : ℤ`).  The map `u ↦ (L₋₁u + L₀u)` is linear and `leftProd`/`zhuMul`
are bilinear, so the predicate is closed under `u = 0` / `u₁ + u₂` (`reduce_homogeneous`).  Depth-`n`
analog of `ZhuRingResidue.left_ideal_gen_of_homogeneous`. -/
theorem leftProd_genL_mem_On_of_homog (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Hhom : ∀ M : ℤ, ∀ u ∈ W.grading M, ∀ v b : 𝒱,
      leftProd W n (zhuMul W (W.L (-1) u + W.L 0 u) v) b ∈ On W n) :
    ∀ u v b : 𝒱, leftProd W n (zhuMul W (W.L (-1) u + W.L 0 u) v) b ∈ On W n := by
  intro u v b
  refine reduce_homogeneous W (P := fun u =>
    leftProd W n (zhuMul W (W.L (-1) u + W.L 0 u) v) b ∈ On W n) ?_ ?_ ?_ u
  · intro M u hu; exact Hhom M u hu v b
  · simp only [map_zero, add_zero, zhuMul_zero_left, leftProd_zero_left]
    exact (On W n).zero_mem
  · intro x y hx hy
    rw [show (W.L (-1)) (x + y) + (W.L 0) (x + y)
        = ((W.L (-1)) x + (W.L 0) x) + ((W.L (-1)) y + (W.L 0) y) from by
      simp only [map_add]; abel, zhuMul_add_left, leftProd_add_left]
    exact (On W n).add_mem hx hy

/-! ## (R-mem): the homogeneous reduction `𝒱 *ₙ O(𝒱) ⊆ Oₙ`. -/

/-- **(R-mem) reduces to homogeneous `x` and `u`.**  The right FZ product `rightProd W n x g` of the
`O(𝒱)`-base generator `g = (L₋₁u + L₀u) * v` (in the base slot) lands in `Oₙ(𝒱)` for ALL `x u v`,
provided it does for homogeneous acting factor `x ∈ 𝒱_K` and homogeneous `u ∈ 𝒱_M`.  `rightProd` is
bilinear (linear in `x`; the generator slot is linear in `u` via `zhuMul`/`L`), so the predicate is
closed under `0` / `+` in both `x` and `u` (`reduce_homogeneous`, twice).  Depth-`n` analog of
`ZhuRes.right_ideal_gen_of_homogeneous`. -/
theorem rightProd_genR_mem_On_of_homog (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Hhom : ∀ K : ℤ, ∀ x ∈ W.grading K, ∀ M : ℤ, ∀ u ∈ W.grading M, ∀ v : 𝒱,
      rightProd W n x (zhuMul W (W.L (-1) u + W.L 0 u) v) ∈ On W n) :
    ∀ x u v : 𝒱, rightProd W n x (zhuMul W (W.L (-1) u + W.L 0 u) v) ∈ On W n := by
  intro x u v
  refine reduce_homogeneous W (P := fun x =>
    rightProd W n x (zhuMul W (W.L (-1) u + W.L 0 u) v) ∈ On W n) ?_ ?_ ?_ x
  · intro K x hx
    refine reduce_homogeneous W (P := fun u =>
      rightProd W n x (zhuMul W (W.L (-1) u + W.L 0 u) v) ∈ On W n) ?_ ?_ ?_ u
    · intro M u hu; exact Hhom K x hx M u hu v
    · simp only [map_zero, add_zero, zhuMul_zero_left, rightProd_zero_right]
      exact (On W n).zero_mem
    · intro u₁ u₂ hu₁ hu₂
      rw [show (W.L (-1)) (u₁ + u₂) + (W.L 0) (u₁ + u₂)
          = ((W.L (-1)) u₁ + (W.L 0) u₁) + ((W.L (-1)) u₂ + (W.L 0) u₂) from by
        simp only [map_add]; abel, zhuMul_add_left, rightProd_add_right]
      exact (On W n).add_mem hu₁ hu₂
  · change rightProd W n 0 (zhuMul W (W.L (-1) u + W.L 0 u) v) ∈ On W n
    rw [rightProd_zero_left]; exact (On W n).zero_mem
  · intro x₁ x₂ hx₁ hx₂
    change rightProd W n (x₁ + x₂) (zhuMul W (W.L (-1) u + W.L 0 u) v) ∈ On W n
    rw [rightProd_add_left]
    exact (On W n).add_mem hx₁ hx₂

/-!
## What this proves and the PRECISE remaining homogeneous target (NOT `sorry`)

Proved here (axiom-clean: `[propext, Classical.choice, Quot.sound]`):

* **`circ_zero_eq_gen`** — the depth-`0` circle product equals the `O(𝒱)`-generator (homogeneous `u`).
* **`circ_zero_mem_O`** / **`gen_mem_On_zero`** / **`On_zero_eq_O`** — `Oₙ(𝒱)` at `n = 0` is Zhu's
  `O(𝒱)`.
* **`O_assoc`** / **`O_right_ideal_gen`** / **`O_left_ideal_gen`** — Zhu's two-sided-ideal theorem
  packaged unconditionally (from `associator_core` + `right_ideal_core`).
* **`leftProd_genL_mem_On_zero`** / **`rightProd_genR_mem_On_zero`** — the `n = 0` anchors of
  (L-mem)/(R-mem): they ARE Zhu's two-sided ideal `O(𝒱) * 𝒱 ⊆ O(𝒱)` / `𝒱 * O(𝒱) ⊆ O(𝒱)`, carried
  across `On W 0 = O W`.
* **`leftDescends_zero`** — the `n = 0` left bimodule-descent structure `LeftDescends W 0`, assembled
  unconditionally from the (L-mem) anchor via `leftDescends_of_genMem`.
* **`leftProd_genL_mem_On_of_homog`** / **`rightProd_genR_mem_On_of_homog`** — (L-mem)/(R-mem) for ALL
  arguments reduced to the homogeneous form via `reduce_homogeneous` (`L₋₁ + L₀` linear,
  `leftProd`/`rightProd`/`zhuMul` bilinear).

So (L-mem)/(R-mem) — hence (via `LeftGenTowerEq_holds_of_mem`/`RightGenTowerEq_holds_of_mem`,
`ZhuVermaAnDescent13`) `LeftGenTowerEq_holds`/`RightGenTowerEq_holds`, hence (via
`leftDescends_holds`/`rightDescends_holds` + `RightCircTowerEq_holds`, `ZhuVermaAnDescent8`/`14`) the
unconditional `An.lActU'`/`An.rActU'` — are, for `n ≥ 1`, reduced to the following two HOMOGENEOUS
targets (the depth-`n` FZ Lemma 2.1.2 collapses; the `n = 0` instances are the proved anchors above):

  **(L-hom)**  `∀ M : ℤ, ∀ u ∈ 𝒱_M, ∀ v b, leftProd W n ((L₋₁u+L₀u)*v) b ∈ Oₙ`,
  **(R-hom)**  `∀ K M : ℤ, ∀ x ∈ 𝒱_K, ∀ u ∈ 𝒱_M, ∀ v, rightProd W n x ((L₋₁u+L₀u)*v) ∈ Oₙ`.

By the generator entry points `leftGenProd_homogeneous_expand`/`rightGenProd_homogeneous_expand`
(`ZhuVermaAnDescent11`, `zhuMul_L_base` + FZ bilinearity), each homogeneous membership is the finite
iterate `i`-sum

  `leftProd W n g b  = ∑_{i≤M} C(M,i) • leftProd W n (u₍ᵢ₋₂₎v) b`,
  `rightProd W n x g = ∑_{i≤M} C(M,i) • rightProd W n x (u₍ᵢ₋₂₎v)`.

The per-iterate terms do NOT lie in `Oₙ` individually for `n ≥ 1`: expanding by `mode_split_gen` and
reassembling the inner `i`-residue yields the `O(𝒱)`-generator `(L₋₁u+L₀u)*(…)`, which lands in
`O(𝒱)`; by `On_zero_eq_O` that is `Oₙ` ONLY at `n = 0`.  For `n ≥ 1` `O(𝒱) ⊄ Oₙ(𝒱)`, so only the
WHOLE `i`-sum lands in `Oₙ`, after the Dong–Li–Mason `(1+z)^{…}` alternating `j`-sum collapses the
iterate residue onto `PresOn`-towers (each `∈ Oₙ` by the keystone `Pres_mem_On`).  This is the SAME
genuine depth-`n` U/V iterate-collapse content as the circle-case `RightCircTowerEq_holds`
(`ZhuVermaAnDescent10`: `UgammaModeColl = towerCoeff`, `VgammaModeColl = towerCoeff`, via
`ZhuRes.gen_vandermonde` per FZ index `j` + `ZhuRes.gen_jsum`).  These two homogeneous targets are
left as PRECISE stated targets for `n ≥ 1`, NOT `sorry`'d and NOT axiomatized.  Supplying
(L-hom)/(R-hom) discharges (L-mem)/(R-mem) through the reductions proved above, and thence the full
`gen_mem` predicates of the `A_n(𝒱)` bimodule descent.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.circ_zero_eq_gen
  #print axioms VOA.On_zero_eq_O
  #print axioms VOA.O_assoc
  #print axioms VOA.O_right_ideal_gen
  #print axioms VOA.O_left_ideal_gen
  #print axioms VOA.leftProd_genL_mem_On_zero
  #print axioms VOA.rightProd_genR_mem_On_zero
  #print axioms VOA.leftDescends_zero
  #print axioms VOA.leftProd_genL_mem_On_of_homog
  #print axioms VOA.rightProd_genR_mem_On_of_homog
-/
