/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnDescent21
import VOA.Modules.ZhuVermaAnDescent15

/-!
# The two `O(𝒱)`-generator memberships reduced to the **circle-0** memberships.

The two `gen_mem` fields (L-mem) `O(𝒱) *ₙ 𝒱 ⊆ Oₙ` and (R-mem) `𝒱 *ₙ O(𝒱) ⊆ Oₙ` are reduced —
axiom-clean — to the fully-homogeneous **circle-0 memberships** (the `n = 0` circle product fed into
the depth-`n` FZ product):

* **(L-circ0)** `∀ M P, ∀ u ∈ 𝒱_M, ∀ v ∈ 𝒱_P, ∀ b, leftProd W n (circ W 0 u v) b ∈ Oₙ`,
* **(R-circ0)** `∀ K M P, ∀ x ∈ 𝒱_K, ∀ u ∈ 𝒱_M, ∀ v ∈ 𝒱_P, rightProd W n x (circ W 0 u v) ∈ Oₙ`.

Route: for homogeneous `u`, the `O(𝒱)`-generator IS the depth-`0` circle product
`(L₋₁u+L₀u)*v = circ W 0 u v` (`circ_zero_eq_gen`, `ZhuVermaAnDescent15`); the generator slot is
linear in `v`, so `v` reduces to homogeneous (`leftProd_genL_homog_v`/`rightProd_genR_homog_v`).
Supplying (L-circ0)/(R-circ0) discharges (L-mem)/(R-mem) for ALL arguments
(`leftProd_genL_mem_On_of_circ0`/`rightProd_genR_mem_On_of_circ0`), and hence the full `gen_mem`
predicates `LeftGenTowerEq_holds`/`RightGenTowerEq_holds`
(`LeftGenTowerEq_holds_of_circ0`/`RightGenTowerEq_holds_of_circ0`, via `ZhuVermaAnDescent13`).

The `n = 0` instances are the proved Zhu two-sided-ideal anchors; the `n ≥ 1` circle-0 collapses are
the depth-`n` generator-analogues of the U-core/V-core (`ZhuVermaAnDescent19`/`20`), with the
depth-`0` circle weight `cbz M i` in place of the depth-`n` circle weight — the same
`gen_vandermonde`/`gen_jsum`/`tower_swap` engine, applied to `leftProd`/`rightProd` of a depth-`0`
circle.  Left here as the precise stated targets (NOT `sorry`'d, NOT axiomatized).

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

/-! ## Step A — reduce the base slot `v` to homogeneous as well.

In the Descent15 reductions, (L-mem)/(R-mem) are reduced to homogeneous `u ∈ 𝒱_M` (and homogeneous
`x ∈ 𝒱_K` for (R-mem)).  The base slot `v` of the generator `g = (L₋₁u+L₀u)*v = zhuMul W _ v` is the
SECOND, linear slot of `zhuMul`, and `leftProd`/`rightProd` are linear in their generator slot, so
the membership predicate is closed under `v = 0` and `v = v₁+v₂`.  Hence we may reduce `v` to
homogeneous `v ∈ 𝒱_P` too. -/

/-- **(L-hom) reduces to homogeneous `v`.**  Given the membership for homogeneous `u ∈ 𝒱_M`,
`v ∈ 𝒱_P` (all `b`), it holds for homogeneous `u` and arbitrary `v`. -/
theorem leftProd_genL_homog_v (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M : ℕ} {u : 𝒱}
    (hu : u ∈ W.grading (M : ℤ))
    (Hv : ∀ P : ℕ, ∀ v ∈ W.grading (P : ℤ), ∀ b : 𝒱,
      leftProd W n (zhuMul W (W.L (-1) u + W.L 0 u) v) b ∈ On W n)
    (v b : 𝒱) :
    leftProd W n (zhuMul W (W.L (-1) u + W.L 0 u) v) b ∈ On W n := by
  refine reduce_homogeneous W (P := fun v =>
    leftProd W n (zhuMul W (W.L (-1) u + W.L 0 u) v) b ∈ On W n) ?_ ?_ ?_ v
  · intro P v hv
    rcases lt_or_ge P 0 with hP | hP
    · rw [W.positivity P hP, Submodule.mem_bot] at hv
      subst hv
      rw [zhuMul_zero_right, leftProd_zero_left]; exact (On W n).zero_mem
    · obtain ⟨P', rfl⟩ : ∃ P' : ℕ, P = (P' : ℤ) := ⟨P.toNat, by omega⟩
      exact Hv P' v hv b
  · show leftProd W n (zhuMul W (W.L (-1) u + W.L 0 u) 0) b ∈ On W n
    rw [zhuMul_zero_right, leftProd_zero_left]; exact (On W n).zero_mem
  · intro x y hx hy
    show leftProd W n (zhuMul W (W.L (-1) u + W.L 0 u) (x + y)) b ∈ On W n
    rw [zhuMul_add_right, leftProd_add_left]
    exact (On W n).add_mem hx hy

/-- **(R-hom) reduces to homogeneous `v`.**  Given the membership for homogeneous `x ∈ 𝒱_K`,
`u ∈ 𝒱_M`, `v ∈ 𝒱_P`, it holds for homogeneous `x`, `u` and arbitrary `v`. -/
theorem rightProd_genR_homog_v (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ} {x u : 𝒱}
    (hx : x ∈ W.grading (K : ℤ)) (hu : u ∈ W.grading (M : ℤ))
    (Hv : ∀ P : ℕ, ∀ v ∈ W.grading (P : ℤ),
      rightProd W n x (zhuMul W (W.L (-1) u + W.L 0 u) v) ∈ On W n)
    (v : 𝒱) :
    rightProd W n x (zhuMul W (W.L (-1) u + W.L 0 u) v) ∈ On W n := by
  refine reduce_homogeneous W (P := fun v =>
    rightProd W n x (zhuMul W (W.L (-1) u + W.L 0 u) v) ∈ On W n) ?_ ?_ ?_ v
  · intro P v hv
    rcases lt_or_ge P 0 with hP | hP
    · rw [W.positivity P hP, Submodule.mem_bot] at hv
      subst hv
      rw [zhuMul_zero_right, rightProd_zero_right]; exact (On W n).zero_mem
    · obtain ⟨P', rfl⟩ : ∃ P' : ℕ, P = (P' : ℤ) := ⟨P.toNat, by omega⟩
      exact Hv P' v hv
  · show rightProd W n x (zhuMul W (W.L (-1) u + W.L 0 u) 0) ∈ On W n
    rw [zhuMul_zero_right, rightProd_zero_right]; exact (On W n).zero_mem
  · intro a b ha hb
    show rightProd W n x (zhuMul W (W.L (-1) u + W.L 0 u) (a + b)) ∈ On W n
    rw [zhuMul_add_right, rightProd_add_right]
    exact (On W n).add_mem ha hb

/-! ## Step B — the generator IS the depth-`0` circle product (full homogeneity).

For homogeneous `u ∈ 𝒱_M`, `circ_zero_eq_gen` gives `circ W 0 u v = (L₋₁u+L₀u)*v`. -/

/-- (L-hom), homogeneous `u`, rewritten with the generator as `circ W 0 u v`. -/
theorem leftProd_genL_eq_circ0 (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M : ℕ} {u : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (v b : 𝒱) :
    leftProd W n (zhuMul W (W.L (-1) u + W.L 0 u) v) b = leftProd W n (circ W 0 u v) b := by
  rw [circ_zero_eq_gen W hu v]

/-- (R-hom), homogeneous `u`, rewritten with the generator as `circ W 0 u v`. -/
theorem rightProd_genR_eq_circ0 (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M : ℕ} {u : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (v x : 𝒱) :
    rightProd W n x (zhuMul W (W.L (-1) u + W.L 0 u) v) = rightProd W n x (circ W 0 u v) := by
  rw [circ_zero_eq_gen W hu v]

/-! ## Step C — the PRECISE remaining target, and the full conditional chain.

Combining Step A (reduce `v` to homogeneous) and Step B (`generator = circ W 0 u v` for homogeneous
`u`), the two depth-`n` FZ `O(𝒱)`-generator memberships are reduced to the following two FULLY
HOMOGENEOUS circle-`0` memberships (the precise remaining content; `n ≥ 1` is the genuine case, the
`n = 0` instances being the proved Zhu two-sided-ideal anchors):

  **(L-circ0)** `∀ M P : ℕ, ∀ u ∈ 𝒱_M, ∀ v ∈ 𝒱_P, ∀ b, leftProd W n (circ W 0 u v) b ∈ Oₙ`,
  **(R-circ0)** `∀ K M P : ℕ, ∀ x ∈ 𝒱_K, ∀ u ∈ 𝒱_M, ∀ v ∈ 𝒱_P, rightProd W n x (circ W 0 u v) ∈ Oₙ`.

We record the conditional discharge: supplying (L-circ0)/(R-circ0) gives (L-mem)/(R-mem) for ALL
arguments, hence (via `LeftGenTowerEq_holds_of_mem`/`RightGenTowerEq_holds_of_mem`,
`ZhuVermaAnDescent13`) the `O(𝒱)`-generator tower predicates outright. -/

/-- **(L-mem) for ALL arguments from (L-circ0).**  Routes the fully-homogeneous circle-`0`
left-membership through Step A (`leftProd_genL_homog_v`), Step B (`leftProd_genL_eq_circ0`), and the
Descent15 homogeneous-`u` reduction (`leftProd_genL_mem_On_of_homog`). -/
theorem leftProd_genL_mem_On_of_circ0 (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Hcirc0 : ∀ M P : ℕ, ∀ u ∈ W.grading (M : ℤ), ∀ v ∈ W.grading (P : ℤ), ∀ b : 𝒱,
      leftProd W n (circ W 0 u v) b ∈ On W n) :
    ∀ u v b : 𝒱, leftProd W n (zhuMul W (W.L (-1) u + W.L 0 u) v) b ∈ On W n := by
  refine leftProd_genL_mem_On_of_homog W n ?_
  intro M' u hu v b
  rcases lt_or_ge M' 0 with hM | hM
  · rw [W.positivity M' hM, Submodule.mem_bot] at hu
    subst hu
    simp only [map_zero, add_zero, zhuMul_zero_left, leftProd_zero_left]
    exact (On W n).zero_mem
  · obtain ⟨M, rfl⟩ : ∃ M : ℕ, M' = (M : ℤ) := ⟨M'.toNat, by omega⟩
    refine leftProd_genL_homog_v W n hu ?_ v b
    intro P v hv b
    rw [leftProd_genL_eq_circ0 W n hu v b]
    exact Hcirc0 M P u hu v hv b

/-- **(R-mem) for ALL arguments from (R-circ0).**  Routes the fully-homogeneous circle-`0`
right-membership through Step A (`rightProd_genR_homog_v`), Step B (`rightProd_genR_eq_circ0`), and
the Descent15 homogeneous-`x`,`u` reduction (`rightProd_genR_mem_On_of_homog`). -/
theorem rightProd_genR_mem_On_of_circ0 (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Hcirc0 : ∀ K M P : ℕ, ∀ x ∈ W.grading (K : ℤ), ∀ u ∈ W.grading (M : ℤ), ∀ v ∈ W.grading (P : ℤ),
      rightProd W n x (circ W 0 u v) ∈ On W n) :
    ∀ x u v : 𝒱, rightProd W n x (zhuMul W (W.L (-1) u + W.L 0 u) v) ∈ On W n := by
  refine rightProd_genR_mem_On_of_homog W n ?_
  intro K' x hx M' u hu v
  rcases lt_or_ge K' 0 with hK | hK
  · rw [W.positivity K' hK, Submodule.mem_bot] at hx
    subst hx
    rw [rightProd_zero_left]; exact (On W n).zero_mem
  rcases lt_or_ge M' 0 with hM | hM
  · rw [W.positivity M' hM, Submodule.mem_bot] at hu
    subst hu
    simp only [map_zero, add_zero, zhuMul_zero_left, rightProd_zero_right]
    exact (On W n).zero_mem
  · obtain ⟨K, rfl⟩ : ∃ K : ℕ, K' = (K : ℤ) := ⟨K'.toNat, by omega⟩
    obtain ⟨M, rfl⟩ : ∃ M : ℕ, M' = (M : ℤ) := ⟨M'.toNat, by omega⟩
    refine rightProd_genR_homog_v W n hx hu ?_ v
    intro P v hv
    rw [rightProd_genR_eq_circ0 W n hu v x]
    exact Hcirc0 K M P x hx u hu v hv

/-! ## The full predicate discharge (conditional on (L-circ0)/(R-circ0)).

These show that the two circle-`0` memberships discharge the `LeftGenTowerEq_holds` /
`RightGenTowerEq_holds` predicates of `ZhuVermaAnDescent8` outright, via the Descent13 routings
`LeftGenTowerEq_holds_of_mem` / `RightGenTowerEq_holds_of_mem`. -/

/-- `LeftGenTowerEq_holds` from (L-circ0). -/
theorem LeftGenTowerEq_holds_of_circ0 (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Hcirc0 : ∀ M P : ℕ, ∀ u ∈ W.grading (M : ℤ), ∀ v ∈ W.grading (P : ℤ), ∀ b : 𝒱,
      leftProd W n (circ W 0 u v) b ∈ On W n)
    (u v b : 𝒱) : LeftGenTowerEq W n (zhuMul W (W.L (-1) u + W.L 0 u) v) b :=
  LeftGenTowerEq_holds_of_mem W n (leftProd_genL_mem_On_of_circ0 W n Hcirc0) u v b

/-- `RightGenTowerEq_holds` from (R-circ0). -/
theorem RightGenTowerEq_holds_of_circ0 (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Hcirc0 : ∀ K M P : ℕ, ∀ x ∈ W.grading (K : ℤ), ∀ u ∈ W.grading (M : ℤ), ∀ v ∈ W.grading (P : ℤ),
      rightProd W n x (circ W 0 u v) ∈ On W n)
    (x u v : 𝒱) : RightGenTowerEq W n x (zhuMul W (W.L (-1) u + W.L 0 u) v) :=
  RightGenTowerEq_holds_of_mem W n (rightProd_genR_mem_On_of_circ0 W n Hcirc0) x u v

/-! ## Step D — the honest forward decomposition of (R-circ0) (the overshoot, made explicit).

For homogeneous `u ∈ 𝒱_M`, `circ W 0 u w = ∑ᵢ C(M,i) u₍ᵢ₋₂₎ w` (`circ_homogeneous` at `n = 0`).  We
record this depth-`0` collapse cleanly (the `(M+0).toNat+1 = M+1` and grade-`0` normalizations), the
exact entry point for any future U/V assembly of (R-circ0)/(L-circ0). -/

/-- The depth-`0` circle collapse for homogeneous `u ∈ 𝒱_M`: `circ W 0 u w = ∑ᵢ C(M,i) u₍ᵢ₋₂₎ w`. -/
theorem circ0_homog (W : VertexOperatorAlgebra 𝒱) {M : ℕ} {u : 𝒱} (hu : u ∈ W.grading (M : ℤ))
    (w : 𝒱) :
    circ W 0 u w = ∑ i ∈ Finset.range (M + 1), cbz (M : ℤ) (i : ℤ) • W.smul u ((i : ℤ) - 2) w := by
  rw [circ_homogeneous W 0 hu w,
    show ((M : ℤ) + ((0 : ℕ) : ℤ)).toNat + 1 = M + 1 from by push_cast; simp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show ((M : ℤ) + ((0 : ℕ) : ℤ)) = (M : ℤ) from by push_cast; ring,
    show ((i : ℤ) - 2 * ((0 : ℕ) : ℤ) - 2) = (i : ℤ) - 2 from by push_cast; ring]

end VOA
