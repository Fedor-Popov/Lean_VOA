/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuRing
import VOA.Modules.ZhuRightIdeal
import VOA.Modules.ZhuAssociator

/-!
# The unconditional `Ring (A 𝒱)` — Zhu Thm 2.1.1/2.1.2, fully discharged (Gannon §5.3.2)

This is the main theorem of Zhu's algebra: assembling the proved residue cores into the genuine
associative `Ring`/`ℂ`-Algebra structure on `A(𝒱) = 𝒱 ⧸ O(𝒱)`, with no remaining hypothesis.

The two genuine analytic cores of Zhu Thm 2.1.1/2.1.2 are **proved axiom-free**:
* `ZhuHR.right_ideal_core` (`Modules.ZhuRightIdeal`) — the right-ideal residue collapse
  `u * ((L₋₁a+L₀a)*b) ∈ O` (off the linchpin `ZhuRes.zhu_right_binom`);
* `associator_core` (`Modules.ZhuAssociator`) — the associativity residue decomposition
  `(u*v)*w − u*(v*w) ∈ O` (off `u_core`/`v_core`/`mu_identity` + the `mode_iterate` two-family
  bookkeeping).
The left-ideal direction is **free** from the associator (`ZhuRes.left_ideal_gen_of_assoc`).

* **`zhuRingData_of_cores`** — assembles `ZhuRingData W` from the two cores (the ℤ-graded
  homogeneity reductions bridge to the ℕ-indexed cores; negative grades vanish by `positivity`).
* **`zhuRingData_holds : ZhuRingData W`** — the unconditional crux, a theorem.
* **`instRingA : Ring (A 𝒱)`**, **`instAlgebraA : Algebra ℂ (A 𝒱)`** — the unconditional Zhu
  algebra (Zhu Thm 2.1.1/2.1.2).
* **`moduleMh : Module (A 𝒱) M_h`** — Theorem 5.3.4 *easy direction* completes for free: the
  descended action `actA` (`Modules.ZhuModule`) is a genuine `A(𝒱)`-module on the
  lowest-weight space.

## Status
`sorry`-free, with no project axioms.  `zhuRingData_holds`, `instRingA`, `instAlgebraA`,
`moduleMh` are all `[propext, Classical.choice, Quot.sound]` — the associative algebra `A(𝒱)` and
the easy direction of Theorem 5.3.4 do not use `VOA.pbw`.

## References
* Gannon §5.3.2, Thm 5.3.4, eqs. (5.3.8)–(5.3.10); Zhu [574] Thm 2.1.1–2.1.2; Frenkel–Zhu.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators
open Classical

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **The `ZhuRingData` glue.**  From the right-ideal core (`hRcore`, homogeneous `u,a`) and the
associator core (`hAcore`, homogeneous `u,v`), assemble `ZhuRingData W`.  The left-ideal
direction is free from `hA` (`left_ideal_gen_of_assoc`); the ℤ-graded reductions bridge to the
ℕ-indexed cores (negative grades vanish by `positivity`). -/
theorem zhuRingData_of_cores (W : VertexOperatorAlgebra 𝒱)
    (hRcore : ∀ (K M : ℕ) (u a : 𝒱), u ∈ W.grading (K : ℤ) → a ∈ W.grading (M : ℤ) → ∀ b : 𝒱,
       zhuMul W u (zhuMul W (W.L (-1) a + W.L 0 a) b) ∈ O W)
    (hAcore : ∀ (K L : ℕ) (u v : 𝒱), u ∈ W.grading (K : ℤ) → v ∈ W.grading (L : ℤ) → ∀ w : 𝒱,
       zhuMul W (zhuMul W u v) w - zhuMul W u (zhuMul W v w) ∈ O W) :
    ZhuRingData W := by
  have hA : ∀ u v w : 𝒱, zhuMul W (zhuMul W u v) w - zhuMul W u (zhuMul W v w) ∈ O W := by
    refine assoc_of_homogeneous W (fun K u hu L v hv J w _ => ?_)
    rcases lt_or_ge K 0 with hK | hK
    · rw [W.positivity K hK, Submodule.mem_bot] at hu
      subst hu; simp only [zhuMul_zero_left, zhuMul_zero_right, sub_self]; exact (O W).zero_mem
    rcases lt_or_ge L 0 with hL | hL
    · rw [W.positivity L hL, Submodule.mem_bot] at hv
      subst hv; simp only [zhuMul_zero_right, zhuMul_zero_left, sub_self]; exact (O W).zero_mem
    · obtain ⟨K', rfl⟩ : ∃ K' : ℕ, K = (K' : ℤ) := ⟨K.toNat, by omega⟩
      obtain ⟨L', rfl⟩ : ∃ L' : ℕ, L = (L' : ℤ) := ⟨L.toNat, by omega⟩
      exact hAcore K' L' u v hu hv w
  have hR : ∀ u a b : 𝒱, zhuMul W u (zhuMul W (W.L (-1) a + W.L 0 a) b) ∈ O W := by
    refine right_ideal_gen_of_homogeneous W (fun K u hu M a ha b => ?_)
    rcases lt_or_ge K 0 with hK | hK
    · rw [W.positivity K hK, Submodule.mem_bot] at hu
      subst hu; rw [zhuMul_zero_left]; exact (O W).zero_mem
    rcases lt_or_ge M 0 with hM | hM
    · rw [W.positivity M hM, Submodule.mem_bot] at ha
      subst ha; simp only [map_zero, add_zero, zhuMul_zero_left, zhuMul_zero_right]
      exact (O W).zero_mem
    · obtain ⟨K', rfl⟩ : ∃ K' : ℕ, K = (K' : ℤ) := ⟨K.toNat, by omega⟩
      obtain ⟨M', rfl⟩ : ∃ M' : ℕ, M = (M' : ℤ) := ⟨M.toNat, by omega⟩
      exact hRcore K' M' u a hu ha b
  exact zhuRingData_of_gens W (left_ideal_gen_of_assoc W hA)
    (fun u g hg => by obtain ⟨a, b, rfl⟩ := hg; exact hR u a b) hA

/-- **Zhu Thm 2.1.1/2.1.2, unconditional** (the lone remaining hypothesis is a theorem):
`O(𝒱)` is a two-sided ideal for the Zhu product and `*` is associative mod `O(𝒱)`.  Discharged
from `ZhuHR.right_ideal_core` + `associator_core`. -/
theorem zhuRingData_holds (W : VertexOperatorAlgebra 𝒱) : ZhuRingData W :=
  zhuRingData_of_cores W
    (fun _ _ _ _ hu ha b => ZhuHR.right_ideal_core W hu ha b)
    (fun _ _ _ _ hu hv w => associator_core W hu hv w)

/-- **Zhu's algebra `A(𝒱)` is an associative `Ring`** (Zhu Thm 2.1.1/2.1.2), unconditionally. -/
@[reducible] noncomputable def instRingA (W : VertexOperatorAlgebra 𝒱) : Ring (A W) :=
  AsRing (zhuRingData_holds W)

/-- **`A(𝒱)` is a `ℂ`-algebra**, unconditionally. -/
@[reducible] noncomputable def instAlgebraA (W : VertexOperatorAlgebra 𝒱) :
    @Algebra ℂ (A W) _ (instRingA W).toSemiring :=
  AsAlgebra (zhuRingData_holds W)

section Module
variable {Mod : Type u} [AddCommGroup Mod] [Module ℂ Mod]

/-- **Theorem 5.3.4, easy direction.**  The lowest-weight space `M_h` of a graded
`𝒱`-module `N` is a bona-fide `A(𝒱)`-module (the descended zero-mode action `actA`), unconditionally. -/
@[reducible] noncomputable def moduleMh (W : VertexOperatorAlgebra 𝒱) {N : OrdVModule W Mod} {h : ℂ}
    (hcw : IsLowestWeight N h) :
    letI := instRingA W; letI := instAlgebraA W; Module (A W) (N.weight h) :=
  AsModule (zhuRingData_holds W) hcw

end Module

end VOA
