/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDJ28Term2Identity
import VOA.Modules.ZhuVermaAnArchDWeightPoleShift

/-!
# `Term1Level` reduced to the pole-deficient alternating tail (Term₂ absorbs the main term).

`Term1Level W n` is `anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0` — the **level-0-inner** cross
membership (DJ Lemma 2.8), the sole open half of the `MUGradedAction` keystone, given that
`Term2Level_holds` (the level-`n`-inner half) is proved unconditionally.

The Dong–Jiang Prop 5.2 **uniform pole-shift** (`resHom_poleShift`) rewrites the inner level-`0` circle
of `Term₁` as an alternating combination of the shifted pole-`(n+2)` residues:

  `anmCirc W 0 0 c d = resHom W 0 2 c d = ∑_{r=0}^{n} asgn n r · resHom W r (n+2) c d`.

Pushing the outer `anmRight W n 0 a (·)` through (it is ℂ-linear in the acted-on slot), the **`r = 0`
term** is exactly

  `anmRight W n 0 a (resHom W 0 (n+2) c d) = anmRight W n 0 a (anmCirc W n 0 c d)`,

which is `Term₂` — **`∈ Onm W n 0` by the proved `Term2Level_holds`**.  So `Term1Level W n` reduces to
the membership of the pole-deficient **`r ≥ 1` alternating tail**

  `∑_{i<n} asgn n (i+1) · anmRight W n 0 a (resHom W (i+1) (n+2) c d) ∈ Onm W n 0`

(`Term1TailResidual`).  This is the genuine DJ Prop 5.2 D-weight residual: each `resHom W r (n+2)` with
`r ≥ 1` is pole-deficient (shift `r > 0 =` pole-excess), and closure is the cancellation *across* the
alternating `asgn`-weights (`asgn_pascal` + the D-weight IBP `resHom_Lneg1_ibp`), not a term-by-term
raise.  With it, `MUGradedAction W` follows (`MUGradedAction_of_Term1Tail`): the whole Half-A keystone
rests on this single alternating tail.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 5.2 (D-weight) + Lemma 2.8; Gannon §5.3.2.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **The pole-deficient `r ≥ 1` alternating tail of `Term₁`.**  After `Term2Level` absorbs the `r = 0`
level-`n` circle term of the `resHom_poleShift` expansion, `Term1Level W n` reduces to the membership of
this tail (indexed `i < n`, so `r = i+1` runs `1 … n`) for homogeneous `c`. -/
def Term1TailResidual (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Prop :=
  ∀ (M : ℕ) (a c d : 𝒱), c ∈ W.grading (M : ℤ) →
    (∑ i ∈ Finset.range n,
      (asgn n (i + 1) : ℂ)
        • anmRight W n 0 a (resHom W ((i + 1 : ℕ) : ℤ) ((n : ℤ) + 2) c d)) ∈ Onm W n 0

/-- **`Term1Level W n` from the tail residual** (Term₂ absorbs the level-`n` main term).  Reducing `c`
to homogeneous (`reduce_homogeneous`; negative grade / `c = 0` give `anmCirc W 0 0 c d = 0`), the
`resHom_poleShift` expansion + outer ℂ-linearity split off the `r = 0` term
(`anmRight W n 0 a (anmCirc W n 0 c d) ∈ Onm` by `hT2`), leaving exactly `Term1TailResidual`. -/
theorem Term1Level_of_tailResidual (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hT2 : Term2Level W n) (htail : Term1TailResidual W n) : Term1Level W n := by
  intro a c d
  refine reduce_homogeneous W
    (P := fun c => anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0) ?_ ?_ ?_ c
  · intro kC c hcC
    rcases lt_or_ge kC 0 with hkC | hkC
    · rw [W.positivity _ hkC, Submodule.mem_bot] at hcC
      rw [hcC, anmCirc_zero_left, anmRight_zero_right']; exact (Onm W n 0).zero_mem
    · obtain ⟨M, rfl⟩ : ∃ M : ℕ, (M : ℤ) = kC := ⟨kC.toNat, by omega⟩
      rw [anmCirc_zero_zero, resHom_poleShift W hcC d n, ← anmRightR_apply W n 0 a, map_sum]
      simp only [map_smul, anmRightR_apply]
      rw [Finset.sum_range_succ']
      refine Submodule.add_mem _ (htail M a c d hcC) (Submodule.smul_mem _ _ ?_)
      rw [Nat.cast_zero, ← anmCirc_zero]
      exact hT2 a c d
  · show anmRight W n 0 a (anmCirc W 0 0 0 d) ∈ Onm W n 0
    rw [anmCirc_zero_left, anmRight_zero_right']; exact (Onm W n 0).zero_mem
  · intro x y hx hy
    rw [anmCirc_add_left, anmRight_add_right]; exact Submodule.add_mem _ hx hy

/-- **`MUGradedAction W` from the single alternating tail residual.**  With `Term2Level_holds` proved
unconditionally, the whole Dong–Jiang `M(U)` graded-action keystone rests on `Term1TailResidual W n`
alone (for every `n`) — the DJ Prop 5.2 D-weight pole-deficient tail. -/
theorem MUGradedAction_of_Term1Tail (W : VertexOperatorAlgebra 𝒱)
    (htail : ∀ n, Term1TailResidual W n) : MUGradedAction W :=
  MUGradedAction_of_TermLevels W
    (fun n => Term1Level_of_tailResidual W n (Term2Level_holds W n) (htail n))
    (fun n => Term2Level_holds W n)

/-! ## The sharper **per-term** residual (engine finding: the tail is term-by-term in `Onm`).

Engine verification (rank-1 free boson, `certificates/mathematica/term1_n1b.wl`/`certificates/mathematica/term1_n2b.wl`, SMAX-stable at
SMAX ≥ target grade) shows that **each** pole-shift term `anmRight W n 0 a (resHom W r (n+2) c d)` lies in
`Onm W n 0` *individually* for every `r`, `0 ≤ r ≤ n` — NOT merely their alternating sum.  (This refutes
the earlier "cancellation only across the alternating `asgn`-weights" reading.)  The `r = 0` term is
`Term₂` (`Term2Level_holds`); the `r ≥ 1` terms are `Term1PerTermResidual` — a clean shift-`r`
generalization of `Term₂` (inner numerator shift `r` instead of `0`), the sharpest form of the wall. -/

/-- **The per-term residual** — each pole-shift term `anmRight W n 0 a (resHom W r (n+2) c d)` with
`1 ≤ r ≤ n` lies in `Onm W n 0` (homogeneous `c`).  Engine-verified term-by-term (`n = 1, 2`,
SMAX-stable); a shift-`r` generalization of `Term2Level`.  Stronger than `Term1TailResidual` (which is
the `asgn`-weighted sum of these terms). -/
def Term1PerTermResidual (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Prop :=
  ∀ (M : ℕ) (a c d : 𝒱), c ∈ W.grading (M : ℤ) → ∀ r ∈ Finset.Icc 1 n,
    anmRight W n 0 a (resHom W (r : ℤ) ((n : ℤ) + 2) c d) ∈ Onm W n 0

/-- **`Term1Level W n` from the per-term residual** (the cleanest reduction).  `resHom_poleShift`
expands `Term₁` as `∑_{r=0}^n asgn(n,r) · anmRight W n 0 a (resHom W r (n+2) c d)`; the `r = 0` term is
`Term₂` (`hT2`), the `r ≥ 1` terms are the per-term residual (`hpt`).  Every summand `∈ Onm`, so the
whole sum is. -/
theorem Term1Level_of_perTermResidual (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hT2 : Term2Level W n) (hpt : Term1PerTermResidual W n) : Term1Level W n := by
  intro a c d
  refine reduce_homogeneous W
    (P := fun c => anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0) ?_ ?_ ?_ c
  · intro kC c hcC
    rcases lt_or_ge kC 0 with hkC | hkC
    · rw [W.positivity _ hkC, Submodule.mem_bot] at hcC
      rw [hcC, anmCirc_zero_left, anmRight_zero_right']; exact (Onm W n 0).zero_mem
    · obtain ⟨M, rfl⟩ : ∃ M : ℕ, (M : ℤ) = kC := ⟨kC.toNat, by omega⟩
      rw [anmCirc_zero_zero, resHom_poleShift W hcC d n, ← anmRightR_apply W n 0 a, map_sum]
      simp only [map_smul, anmRightR_apply]
      refine Submodule.sum_mem _ fun r hr => Submodule.smul_mem _ _ ?_
      rw [Finset.mem_range] at hr
      rcases Nat.eq_zero_or_pos r with rfl | hrpos
      · rw [Nat.cast_zero, ← anmCirc_zero]; exact hT2 a c d
      · exact hpt M a c d hcC r (Finset.mem_Icc.mpr ⟨hrpos, by omega⟩)
  · show anmRight W n 0 a (anmCirc W 0 0 0 d) ∈ Onm W n 0
    rw [anmCirc_zero_left, anmRight_zero_right']; exact (Onm W n 0).zero_mem
  · intro x y hx hy
    rw [anmCirc_add_left, anmRight_add_right]; exact Submodule.add_mem _ hx hy

/-- **`MUGradedAction W` from the per-term residual.**  With `Term2Level_holds` proved, the whole
Half-A keystone rests on `Term1PerTermResidual W n` — the shift-`r` per-term memberships (`1 ≤ r ≤ n`),
each engine-verified in `Onm`, the sharpest form of the remaining Dong–Jiang Lemma 2.8 obstruction. -/
theorem MUGradedAction_of_Term1PerTerm (W : VertexOperatorAlgebra 𝒱)
    (hpt : ∀ n, Term1PerTermResidual W n) : MUGradedAction W :=
  MUGradedAction_of_TermLevels W
    (fun n => Term1Level_of_perTermResidual W n (Term2Level_holds W n) (hpt n))
    (fun n => Term2Level_holds W n)

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.Term1Level_of_tailResidual
  #print axioms VOA.MUGradedAction_of_Term1Tail
-/
