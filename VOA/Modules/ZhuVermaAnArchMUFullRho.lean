/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUFullMode
import VOA.Modules.ZhuVermaAnArchVHatModeData
import VOA.Core.InvariantFormPStep

/-!
# `M(U)` as a `V̂`-representation — the translation relation, unconditional

Dong–Jiang's proof that `M(U)` is an admissible `𝒱`-module (`math/0601626` Thm 4.10) runs through
exactly the repo's `VHatRep` pipeline:

| DJ §4 | repo |
| --- | --- |
| Lemma 4.6(1) (truncation) | `ActModeTruncated` — `muFullMode_truncation` (proved) |
| Lemma 4.6(2) (`Y(𝟙,z) = id`) | `VacuumCreation` — `muFullMode_vacuum` (proved) |
| the mode translation relation | `hderiv` — `muFullActGen_hderiv` (proved, **this file**) |
| Lemma 4.7 (commutator formula) | `hbracket` — `MUFullBracket` (named leaf) |
| Cor. after Lemma 4.9 (associativity) | `ModuleIterate` — `isModuleJacobi_of_iterate` |

This file closes the third row and packages the first three, so that `M(U)` is a `VHatRep`, and
hence a `WeakModule`, modulo exactly the two remaining Dong–Jiang leaves.

## The translation relation is free

`hderiv` asks `(L₋₁a)_m + m·a_{m−1} = 0`.  Both sides move `M(U)(n)` to the *same* level
`N = wt a − m + n`, and on representatives the sum is

  `(L₋₁a) ∗^N_{0,n} g + m·(a ∗^N_{0,n} g) = (L₋₁a + L₀a + (n − N)·a) ∗^N_{0,n} g`

(using `m = wt a − N + n` and `L₀a = wt a · a`), i.e. `anmLgen W N n a ∗^N_{0,n} g` — the DJ grading
generator in the *left* slot.  DJ Lemma 2.8's right inclusion `O_{N,n} ∗^N_{0,n} 𝒱 ⊆ O_{N,0}`
(`anmGen_OnmFull_right_unconditional`, proved) kills it.  So the translation relation costs nothing
beyond what is already proved — it is the `oFull` analogue of DJ's own remark
`o_{n,m}(L₋₁v) = −(wt v + m − n)·o_{n,m}(v)`.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References
Dong–Jiang math/0601626 §4 (Lemmas 4.6–4.9, Thm 4.10), §2 (Lemma 2.8);
`ZhuVermaAnArchMUFullMode` (`muFullMode`, `muFullMode_truncation`, `muFullMode_vacuum`),
`ZhuVermaAnArchVHatModeData` (`assembleModeData`, `assembleAct`),
`ZhuVermaAnArchDJ28Final` (`anmGen_OnmFull_right_unconditional`).
-/

namespace VOA

open VertexOperatorAlgebra
open VHat
open Finsupp
open scoped TensorProduct DirectSum BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The mode family as a `ℤ`-indexed family of linear maps. -/

/-- **The `M(U)` mode family** `m ↦ (a ↦ a_m)`, the input of the `V̂`-representation assembler. -/
noncomputable def muFullActGen (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (m : ℤ) :
    𝒱 →ₗ[ℂ] Module.End ℂ (MUFull W U) where
  toFun a := muFullMode W U m a
  map_add' a b := muFullMode_add_acting W U m a b
  map_smul' c a := muFullMode_smul_acting W U m c a

@[simp] theorem muFullActGen_apply (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (m : ℤ) (a : 𝒱) :
    muFullActGen W U m a = muFullMode W U m a := rfl

/-! ## The translation relation `(L₋₁a)_m = −m·a_{m−1}`. -/

/-- **The DJ grading generator in the acting slot is killed** — the representative-level content of
the translation relation: for `a` homogeneous of weight `K` and `m = K − N + n`,

  `(L₋₁a) ∗^N_{0,n} g + m·(a ∗^N_{0,n} g) = anmLgen W N n a ∗^N_{0,n} g ∈ O_{N,0}`.

This is DJ Lemma 2.8's right inclusion applied to the grading generator. -/
theorem anmGen_Lgen_acting_mem (W : VertexOperatorAlgebra 𝒱) {K : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading K) {N n : ℕ} {m : ℤ} (hm : m = K - (N : ℤ) + (n : ℤ)) (g : 𝒱) :
    anmGen W N 0 n (W.L (-1) a) g + (m : ℂ) • anmGen W N 0 n a g ∈ OnmFull W N 0 := by
  have hL0 : W.L 0 a = (K : ℂ) • a := W.L0_grading a ha
  have hrepr : W.L (-1) a + (m : ℂ) • a = anmLgen W N n a := by
    rw [anmLgen, hL0, hm]
    push_cast
    module
  have hmem : anmGen W N 0 n (anmLgen W N n a) g ∈ OnmFull W N 0 :=
    anmGen_OnmFull_right_unconditional W N 0 n g _ (anmLgen_mem_OnmFull W N n a)
  rwa [← hrepr, anmGen_add_left, anmGen_smul_left] at hmem

/-- The `M(U)` mode operators satisfy the translation relation at a fixed target level. -/
theorem oFullU_Lgen_zero (W : VertexOperatorAlgebra 𝒱) (U : AMod W) {K : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading K) {N n : ℕ} {m : ℤ} (hm : m = K - (N : ℤ) + (n : ℤ)) :
    oFullU W U N n (W.L (-1) a) + (m : ℂ) • oFullU W U N n a = 0 := by
  apply TensorProduct.ext'
  intro y w
  obtain ⟨g, rfl⟩ := (OnmFull W n 0).mkQ_surjective y
  show oFullU W U N n (W.L (-1) a) (mkAnmFull W n 0 g ⊗ₜ[ℂ] w)
      + (m : ℂ) • oFullU W U N n a (mkAnmFull W n 0 g ⊗ₜ[ℂ] w) = 0
  rw [oFullU_tmul, oFullU_tmul, TensorProduct.smul_tmul', ← map_smul, ← TensorProduct.add_tmul,
    ← map_add]
  rw [show mkAnmFull W N 0 (anmGen W N 0 n (W.L (-1) a) g + (m : ℂ) • anmGen W N 0 n a g) = 0 from by
    rw [mkAnmFull, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact anmGen_Lgen_acting_mem W ha hm g]
  exact TensorProduct.zero_tmul _ _

/-- **The translation relation `(L₋₁a)_m + m·a_{m−1} = 0` on `M(U)`, unconditional** — the `hderiv`
input of `assembleModeData`.  (DJ's `o_{n,m}(L₋₁v) = −(wt v + m − n)·o_{n,m}(v)`, in mode form.) -/
theorem muFullActGen_hderiv (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (a : 𝒱) (m : ℤ) :
    muFullActGen W U m (W.L (-1) a) + (m : ℂ) • muFullActGen W U (m - 1) a = 0 := by
  refine reduce_homogeneous W (P := fun a =>
    muFullActGen W U m (W.L (-1) a) + (m : ℂ) • muFullActGen W U (m - 1) a = 0) ?_ ?_ ?_ a
  · -- homogeneous `a ∈ 𝒱_K`
    intro K a ha
    have haL : W.L (-1) a ∈ W.grading (K + 1) := W.L_neg_one_raise ha
    simp only [muFullActGen_apply]
    refine muFull_end_ext W U (fun n x => ?_)
    rw [LinearMap.add_apply, LinearMap.smul_apply,
      muFullMode_apply_incl W U m haL n x, muFullMode_apply_incl W U (m - 1) ha n x]
    have hT₁ : muTargetLevel (K + 1) m n = K - m + (n : ℤ) := by
      simp only [muTargetLevel]; ring
    have hT₂ : muTargetLevel K (m - 1) n = K - m + (n : ℤ) := by
      simp only [muTargetLevel]; ring
    by_cases hnn : 0 ≤ K - m + (n : ℤ)
    · -- both land at the same level `N ≥ 0`
      set N : ℕ := (K - m + (n : ℤ)).toNat with hNdef
      have hN : K - m + (n : ℤ) = (N : ℤ) := (Int.toNat_of_nonneg hnn).symm
      have he₁ : muTargetLevel (K + 1) m n = (N : ℤ) := by rw [hT₁, hN]
      have he₂ : muTargetLevel K (m - 1) n = (N : ℤ) := by rw [hT₂, hN]
      rw [oLevelIncl_eq_of_target W U he₁, oLevelIncl_eq_of_target W U he₂,
        LinearMap.comp_apply, LinearMap.comp_apply, ← map_smul, ← map_add]
      have hm : m = K - (N : ℤ) + (n : ℤ) := by omega
      rw [show oFullU W U N n (W.L (-1) a) x + (m : ℂ) • oFullU W U N n a x = 0 from by
        have := oFullU_Lgen_zero W U ha hm
        have h2 := congrArg (fun f => (f : MUPieceFull W U n →ₗ[ℂ] MUPieceFull W U N) x) this
        simpa using h2]
      exact map_zero _
    · -- both components vanish
      have hneg : K - m + (n : ℤ) < 0 := not_le.mp hnn
      rw [oLevelIncl_of_neg W U (by rw [hT₁]; exact hneg),
        oLevelIncl_of_neg W U (by rw [hT₂]; exact hneg)]
      simp
  · simp
  · intro x y hx hy
    rw [map_add, map_add, map_add, smul_add]
    rw [show muFullActGen W U m (W.L (-1) x) + muFullActGen W U m (W.L (-1) y)
        + ((m : ℂ) • muFullActGen W U (m - 1) x + (m : ℂ) • muFullActGen W U (m - 1) y)
      = (muFullActGen W U m (W.L (-1) x) + (m : ℂ) • muFullActGen W U (m - 1) x)
        + (muFullActGen W U m (W.L (-1) y) + (m : ℂ) • muFullActGen W U (m - 1) y) from by abel]
    rw [hx, hy, add_zero]

/-! ## The two remaining Dong–Jiang leaves. -/

/-- **DJ Lemma 4.7 — the commutator formula for `M(U)`**, as the `hbracket` input of
`assembleModeData`: `[a_p, b_q] = ∑_{i≥0} C(p,i)·(a_i b)_{p+q−i}` on `M(U)`.

DJ prove this from Lemma 2.3 (the cross relation
`u ∗^{p₁+p₂−m}_{m,p₁} v − v ∗^{p₁+p₂−m}_{m,p₂} u ≡ Res_z (1+z)^{wt u−1+m−p₂} Y(u,z)v` mod `O'`)
together with the already-proved composition associativity (`mUFullCompAssoc_holds`) and the
boundary Lemma 4.8'.  It is a genuine residual here: **DJ Lemma 2.3 is not yet formalized in the
repo** (nor is the skew relation `∗ⁿ_m − ∗̄ⁿ_m ∈ O'` it rests on). -/
def MUFullBracket (W : VertexOperatorAlgebra 𝒱) (U : AMod W) : Prop :=
  ∀ (a b : 𝒱) (m k : ℤ),
    assembleAct (muFullActGen W U) (vloopBracket W (single m a) (single k b))
      = ⁅muFullActGen W U m a, muFullActGen W U k b⁆

/-! ## `M(U)` as a `V̂`-representation, modulo the commutator leaf. -/

/-- **The `V̂`-mode data of `M(U)`** — assembled from the unconditional translation relation
`muFullActGen_hderiv` and the DJ Lemma 4.7 commutator leaf. -/
noncomputable def muFullModeData (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hbr : MUFullBracket W U) : VHat.VHatModeData W (MUFull W U) :=
  assembleModeData (muFullActGen W U) (muFullActGen_hderiv W U) hbr

/-- **`M(U)` as a `V̂`-representation** (DJ §4), modulo the DJ Lemma 4.7 commutator leaf. -/
noncomputable def muFullRho (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hbr : MUFullBracket W U) : VHat.VHatRep W (MUFull W U) :=
  (muFullModeData W U hbr).toRep

end VOA

/-
`#print axioms` check (each of the following prints `[propext, Classical.choice, Quot.sound]`,
NO `pbw`, NO `sorryAx`):

  #print axioms VOA.muFullActGen
  #print axioms VOA.anmGen_Lgen_acting_mem
  #print axioms VOA.muFullActGen_hderiv
-/
