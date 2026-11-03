/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchGateB1
import VOA.Modules.ZhuVermaAnArchDLM3Survival
import VOA.Modules.ZhuVermaAnArchDJCarrierGraded

/-!
# B3 and the `(0,0)` gate — `OnmFull W 0 0 = O W`

The gate is Dong–Jiang Proposition 4.6 at `(n,m) = (0,0)`:

    (GATE)   OnmFull W 0 0 ≤ O W        (⟹ `A_{0,0}(𝒱) ≅ A(𝒱)`, the bottom of `M(U)` is `U`).

Dong–Jiang's proof is representation-theoretic and has three moving parts:

* **B1** (annihilation) — the zero mode of every element of `O_{0,0}(𝒱)` kills a bottom vector;
* **B2** (realization) — every `A(𝒱)`-module is the bottom of an admissible module (Zhu / DLM3
  Theorem 4.1 at `n = 0`);
* **B3** (this file) — instantiate at the **regular** module `U = A(𝒱)`, where `o(x)·[𝟙] = [x]`
  (`regularAMod_apply_one`); B1 forces `[x] = 0`, i.e. `x ∈ O(𝒱)`.

## The interface problem this file solves, and why it is not cosmetic

`ZhuVermaAnArchGateB1` states its annihilation over `OrdVModule` (Gannon 5.3.1c).  `OrdVModule` carries
`finrank : ∀ α, FiniteDimensional ℂ (weight α)`.  **The regular module `U = A(𝒱)` is infinite
dimensional in general** (already for the Heisenberg VOA, where `A(𝒱) ≅ ℂ[x]`), so a `OrdVModule`
whose bottom is `A(𝒱)` need not exist: B1's `GateAnnihilation` cannot be fed the object B2
produces, and a B3 built on it would rest on an unsatisfiable hypothesis.  Independently, B2's
output (`indBarWeakModule`, `indBarGraded`) is a **weak** module with a `ℤ`-level family, not a
`OrdVModule`.

So this file **re-proves the whole unconditional part of B1 over the interface B2 actually
produces**: a weak module together with a level family that vanishes in negative degrees
(`AdmLev`).  Nothing is assumed that `M̄_0(U)` does not have; `gateRealizationOfSurvival` verifies
this by construction.

## What is proved here, unconditionally (axiom-clean)

* `AdmLev` — the interface: a `WeakModule` plus `lev : ℤ → Submodule ℂ M` with `lev k = ⊥` for
  `k < 0` and `a₍ₚ₎ · lev k ⊆ lev (k + wt a − p − 1)`.  Strictly weaker than `OrdVModule`: no
  internality (DLM3's PBW step), no finiteness, no `L₀`-eigenvalue condition, no spanning.
* `oLevW` — the cross-level zero mode `o_{n,m}` on a weak module (`d = m − n`), with
  `oLevW N.toWeakModule d = oLev N d` (`oLevW_eq_oLev`): B1's `OrdVModule` layer is a special case.
* `admLevOfLowestWeight` — every lowest-weight `OrdVModule` **is** an `AdmLev`, so `DJCompositionLev`
  implies B1's `DJComposition` (`djComposition_of_djCompositionLev`): the new hypothesis is a
  genuine generalisation of the old one, not a different statement.
* `modeW_vanish_of_lev` — `M(m) ⊆ Ω_m(M)`: `v₍ₙ₎ w = 0` for `w ∈ lev m`, `v ∈ 𝒱_β`, `n ≥ β + m`.
* `oLevW_resHom_uOutside` — the structural expansion of B1, over `AdmLev`.
* `oLevW_resHom_vanish` — the high-pole annihilation law, over `AdmLev`.
* `OnmW_annihilates_lev` / `OnmW_annihilates_diag` — `O'_{n,m}(𝒱)` kills `M(m)` (Dong–Jiang Prop.
  4.5, `O'`-branch; the diagonal case is DJ **Theorem 4.3** on the graded pieces).
* `djCompositionLev_at_zero` — the `(n,m,p) = (0,0,0)` case of the composition law is a
  **theorem** here (Zhu's `o(u ∗ v) = o(u)o(v)` on the bottom), proved from the engine with no
  `OrdVModule` input.  This pins the normalisation of the carried hypothesis.
* `gateAnnihilationLev_of_djCompositionLev` — B1, over `AdmLev`.
* `gate_of_realization` — **B3**: a `GateRealization W (regularAMod W)` plus the annihilation
  gives `OnmFull W 0 0 ≤ O W`, hence `= O W` with the proved `Onm_zero_zero_eq_O`.
* `gateRealizationOfSurvival` — **the B2 → B3 bridge**: `M̄_0(U)` *is* a `GateRealization`,
  given the two DLM3 inputs.  On the way, `levBar_eq_bot_of_neg` (`M̄_0(U)(d) = 0` for `d < 0`),
  off the PBW-free `levCover_eq_bot_of_neg`.
* the downstream consumers, each with the gate as an explicit argument: `DJAnnEqAn W 0`,
  `OnmFull_diag_eq W 0`, `anmFullDiagEquiv W 0`, `djPieceMEquiv W 0`, `DJCarrier.degMEquiv W 0`.

## What is NOT proved — the exact residual

The gate is reduced to **three** named inputs, no more (`gate_of_dj_and_dlm3`):

1. `DJCompositionLev W` — Dong–Jiang **Lemma 4.1**,
   `o_{n,m}(a ∗ⁿ_{m,p} b)w = o_{n,p}(a)o_{p,m}(b)w`.  Anchored at `(0,0,0)` by
   `djCompositionLev_at_zero`; via `oLevW_resHom_uOutside` what remains of it is purely scalar.
2. `BottomProjection (parabolicRepOfAMod W (regularAMod W))` — DLM3's PBW step (`M_0(U)(0) = U`),
   carried as **data**, reduced by `ZhuVermaAnArchDLM3Survival` to bare directness.
3. `DefectPairsToZero Pr` — DLM3's `U(V̂)W ⊆ J` (their Propositions 4.3 + 4.6).

**The gate is NOT claimed.**  Every statement below that uses the
gate takes it as an explicit hypothesis.

## References
Dong–Jiang `math/0601626` §4 (Lemma 4.1, Thm 4.3, Prop. 4.5, Prop. 4.6);
Dong–Li–Mason `q-alg/9612010` §3–§4 (Prop. 3.1, Thm 3.2, Thm 4.1);
`ZhuVermaAnArchGateB1` (B1 over `OrdVModule`; its `resHom_vOutside_coeff_vanish` is reused verbatim),
`ZhuVermaAnArchDLM3Zero` (`parabolicRepOfAMod`, `regularAMod`), `ZhuVermaAnArchDLM3Survival` (B2),
`ZhuVermaAnArchDJCarrier`/`DJCarrierGraded` (the downstream consumers).
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## (A) `AdmLev` — the level interface -/

/-- **A non-negatively levelled weak module.**  A weak `𝒱`-module together with a family of level
subspaces `M(k)`, `k ∈ ℤ`, such that

* `M(k) = 0` for `k < 0` (Dong–Jiang's admissibility, `M = ⨁_{k ≥ 0} M(k)`), and
* a mode of a homogeneous state shifts the level by its `V̂`-degree `wt a − p − 1`.

Deliberately weaker than `OrdVModule`: no internal-direct-sum condition (that is Dong–Li–Mason's PBW
step), no finite-dimensionality of the pieces, no `L₀`-eigenvalue condition, and the family is not
even required to span.  This is exactly the structure `M̄_0(U)` carries (`indBarGraded` plus
`levCover_eq_bot_of_neg`), which is why B3 can be instantiated at the infinite-dimensional regular
module `U = A(𝒱)`. -/
structure AdmLev (W : VertexOperatorAlgebra 𝒱) {M : Type u} [AddCommGroup M] [Module ℂ M]
    (A : WeakModule W M) where
  /-- The level filtration `M(k)`, `k ∈ ℤ`. -/
  lev : ℤ → Submodule ℂ M
  /-- Admissibility: no negative levels. -/
  lev_neg : ∀ ⦃k : ℤ⦄, k < 0 → lev k = ⊥
  /-- Modes shift the level by the `V̂`-degree `wt a − p − 1`. -/
  act_lev : ∀ ⦃w p k : ℤ⦄ ⦃a : 𝒱⦄, a ∈ W.grading w → ∀ ⦃x : M⦄, x ∈ lev k →
    A.act a p x ∈ lev (k + (w - p - 1))

section Weak

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## (B) The cross-level zero mode on a weak module -/

/-- The weight-`k` slice of the level-shifted zero mode on a **weak** module: `vₖ ↦ (vₖ)₍ₖ₋₁₊d₎`. -/
noncomputable def oLevWFamily (A : WeakModule W M) (d k : ℤ) : (W.grading k) →ₗ[ℂ] End ℂ M :=
  (modeLinear (k - 1 + d)).comp (A.YM.comp (W.grading k).subtype)

/-- **The level-shifted zero mode on a weak module**, `oLevW A d v = ∑_k (v_k)₍ₖ₋₁₊d₎` —
Dong–Jiang's `o_{n,m}` with `d = m − n` (DJ §4, p. 15), defined with no grading hypothesis on the
module. -/
noncomputable def oLevW (A : WeakModule W M) (d : ℤ) : 𝒱 →ₗ[ℂ] End ℂ M :=
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  (DFinsupp.lsum ℂ (oLevWFamily A d)).comp (DirectSum.decomposeLinearEquiv W.grading).toLinearMap

/-- On a homogeneous `x ∈ 𝒱ₖ` the weak-module level mode is the single mode `x₍ₖ₋₁₊d₎`. -/
theorem oLevW_homogeneous (A : WeakModule W M) (d : ℤ) {k : ℤ} {x : 𝒱} (hx : x ∈ W.grading k) :
    oLevW A d x = mode (A.YM x) (k - 1 + d) := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  have hcollapse : oLevW A d x = oLevWFamily A d k ⟨x, hx⟩ := by
    change (DFinsupp.lsum ℂ (oLevWFamily A d)) (DirectSum.decompose W.grading x) = _
    rw [DirectSum.decompose_of_mem W.grading hx]
    exact DFinsupp.lsum_single ℂ (oLevWFamily A d) k ⟨x, hx⟩
  rw [hcollapse]; rfl

/-- **Compatibility with B1**: on a `ℂ`-graded module the weak-module level mode *is* the `OrdVModule`
level mode `oLev` of `ZhuVermaAnArchGateB1`.  Nothing is duplicated at the level of statements. -/
theorem oLevW_eq_oLev (N : OrdVModule W M) (d : ℤ) : oLevW N.toWeakModule d = oLev N d := rfl

/-- **`oLevW A 0` is the ordinary zero mode** `o(v) = ∑_k (v_k)₍ₖ₋₁₎`. -/
theorem oLevW_zero_eq_oMod (N : OrdVModule W M) : oLevW N.toWeakModule 0 = oMod N := by
  rw [oLevW_eq_oLev, oLev_zero]

/-! ## (C) Level bookkeeping and the mode truncation -/

variable {A : WeakModule W M}

/-- **Level-`m` mode truncation** (`M(m) ⊆ Ω_m(M)`, Dong–Jiang p. 17).  For homogeneous `v ∈ 𝒱_β`
and `w` in the level-`m` piece, `v₍ₙ₎ w = 0` whenever `n ≥ β + m`: the mode would land in a
negative level. -/
theorem modeW_vanish_of_lev (L : AdmLev W A) {β : ℤ} {v : 𝒱} (hv : v ∈ W.grading β) {m : ℤ}
    {x : M} (hx : x ∈ L.lev m) {n : ℤ} (hn : β + m ≤ n) : mode (A.YM v) n x = 0 := by
  have hmem := L.act_lev hv hx (p := n)
  rw [L.lev_neg (by omega), Submodule.mem_bot] at hmem
  rw [← WeakModule.act_def]
  exact hmem

/-- The level mode `oLevW A d` lowers the level by `d`, on a homogeneous `v`. -/
theorem oLevW_mem_lev_homog (L : AdmLev W A) (d : ℤ) {k : ℤ} {v : 𝒱} (hv : v ∈ W.grading k)
    {m : ℤ} {x : M} (hx : x ∈ L.lev m) : oLevW A d v x ∈ L.lev (m - d) := by
  rw [oLevW_homogeneous A d hv, ← WeakModule.act_def]
  have := L.act_lev hv hx (p := k - 1 + d)
  rwa [show m + (k - (k - 1 + d) - 1) = m - d from by ring] at this

/-- **`oLevW A d` lowers the level by `d`** for every `v` (grade decomposition). -/
theorem oLevW_mem_lev (L : AdmLev W A) (d : ℤ) (v : 𝒱) {m : ℤ} {x : M} (hx : x ∈ L.lev m) :
    oLevW A d v x ∈ L.lev (m - d) := by
  have hvtop : v ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun v => oLevW A d v x ∈ L.lev (m - d)) hvtop ?_ ?_ ?_
  · intro i y hy
    exact oLevW_mem_lev_homog L d hy hx
  · change oLevW A d 0 x ∈ _
    rw [map_zero, LinearMap.zero_apply]
    exact (L.lev _).zero_mem
  · intro y z hy hz
    change oLevW A d (y + z) x ∈ _
    rw [map_add, LinearMap.add_apply]
    exact (L.lev _).add_mem hy hz

/-- **`o_{p,m}` maps `M(m)` into `M(p)`** in the `d = m − p` normalisation. -/
theorem oLevW_mem_level (L : AdmLev W A) (m p : ℕ) (v : 𝒱) {x : M} (hx : x ∈ L.lev (m : ℤ)) :
    oLevW A ((m : ℤ) - (p : ℤ)) v x ∈ L.lev (p : ℤ) := by
  have := oLevW_mem_lev L ((m : ℤ) - (p : ℤ)) v hx
  rwa [show (m : ℤ) - ((m : ℤ) - (p : ℤ)) = (p : ℤ) from by ring] at this

/-! ## (D) The grading generator `L₋₁u + (L₀ + m − n)u` -/

/-- The level-`d` mode of `L₋₁c` on a homogeneous `c ∈ 𝒱ₖ` is `−(k+d)·c₍ₖ₋₁₊d₎`. -/
theorem oLevW_L_neg_one (A : WeakModule W M) (d : ℤ) {k : ℤ} {c : 𝒱} (hc : c ∈ W.grading k) :
    oLevW A d (W.L (-1) c) = (-((k : ℂ) + (d : ℂ))) • oLevW A d c := by
  have hmem : W.L (-1) c ∈ W.grading (k + 1) := L_neg_one_mem_grading_succ W hc
  rw [oLevW_homogeneous A d hmem, oLevW_homogeneous A d hc,
    show (k + 1 - 1 + d) = (k + d) from by ring]
  ext x
  simp only [LinearMap.smul_apply]
  have hcov := act_T_covariance A c (k + d) x
  simp only [WeakModule.act_def] at hcov
  rw [show (k - (1 : ℤ) + d) = (k + d) - 1 from by ring, hcov]
  congr 2
  push_cast; ring

/-- **The grading generator dies**, homogeneous case: `o_{n,m}(L₋₁c + (L₀ + m − n)c) = 0`. -/
theorem oLevW_anmLgen_homogeneous (A : WeakModule W M) (n m : ℕ) {k : ℤ} {c : 𝒱}
    (hc : c ∈ W.grading k) : oLevW A ((m : ℤ) - (n : ℤ)) (anmLgen W n m c) = 0 := by
  unfold anmLgen
  rw [map_add, map_add, map_smul, oLevW_L_neg_one A _ hc, W.L_zero_grading c hc, map_smul,
    ← add_smul, ← add_smul,
    show (-((k : ℂ) + ((((m : ℤ) - (n : ℤ)) : ℤ) : ℂ))) + (k : ℂ) + ((m : ℂ) - (n : ℂ)) = 0 from by
      push_cast; ring, zero_smul]

/-- **The grading generator dies, for all `c`** — no level hypothesis at all. -/
theorem oLevW_anmLgen_vanish (A : WeakModule W M) (n m : ℕ) (c : 𝒱) :
    oLevW A ((m : ℤ) - (n : ℤ)) (anmLgen W n m c) = 0 := by
  have hctop : c ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun c => oLevW A ((m : ℤ) - (n : ℤ)) (anmLgen W n m c) = 0) hctop ?_ ?_ ?_
  · intro i x hx
    exact oLevW_anmLgen_homogeneous A n m hx
  · change oLevW A ((m : ℤ) - (n : ℤ)) (anmLgen W n m (0 : 𝒱)) = 0
    have h0 : anmLgen W n m (0 : 𝒱) = 0 := by
      have := anmLgen_smul W n m (0 : ℂ) (0 : 𝒱)
      rwa [zero_smul, zero_smul] at this
    rw [h0, map_zero]
  · intro x y hx hy
    change oLevW A ((m : ℤ) - (n : ℤ)) (anmLgen W n m (x + y)) = 0
    rw [anmLgen_add, map_add, hx, hy, add_zero]

/-! ## (E) The high-pole annihilation law over `AdmLev`

The engine of B1, ported to the level interface.  The only module-theoretic input is
`modeW_vanish_of_lev`; the scalar cancellation `resHom_vOutside_coeff_vanish` is reused verbatim
from `ZhuVermaAnArchGateB1`. -/

/-- **Per-pole step, both Jacobi families kept.**  For any bound `B` past the level ceiling, the
level-`D` mode of `u₍ℓ₎v` on `M(m)` is the `u`-outside family over `Ico 0 B` minus the `v`-outside
family over `Ico 0 (k+m)`. -/
private theorem oLevW_smul_step_full (L : AdmLev W A) (D : ℤ) (m : ℤ) {k l : ℤ} {u v : 𝒱}
    (hu : u ∈ W.grading k) (hv : v ∈ W.grading l) {w : M} (hw : w ∈ L.lev m) (ℓ B : ℤ)
    (hB : m - k + ℓ + 2 - D ≤ B) :
    oLevW A D (W.smul u ℓ v) w
      = (∑ i ∈ Finset.Ico (0 : ℤ) B, (negOnePow i * cbz ℓ i) •
            mode (A.YM u) (ℓ - i) (mode (A.YM v) (k + l - ℓ - 2 + D + i) w))
        - ∑ i ∈ Finset.Ico (0 : ℤ) (k + m),
            (negOnePow i * cbz ℓ i * negOnePow ℓ) •
              mode (A.YM v) (k + l - 2 + D - i) (mode (A.YM u) i w) := by
  classical
  have hgr : W.smul u ℓ v ∈ W.grading (k + l - ℓ - 1) := W.smul_mem_grading hu hv ℓ
  rw [oLevW_homogeneous A D hgr, show k + l - ℓ - 1 - 1 + D = k + l - ℓ - 2 + D from by ring,
    module_iterate0 A u v w ℓ (k + l - ℓ - 2 + D)]
  set F : ℤ → M := fun i => (negOnePow i * cbz ℓ i) •
    mode (A.YM u) (ℓ - i) (mode (A.YM v) (k + l - ℓ - 2 + D + i) w) with hF
  set G : ℤ → M := fun i => (negOnePow i * cbz ℓ i * negOnePow ℓ) •
    mode (A.YM v) (k + l - 2 + D - i) (mode (A.YM u) i w) with hG
  have hFsupp : (Function.support F) ⊆ ↑(Finset.Ico (0 : ℤ) B) := by
    intro i hi
    simp only [hF, Function.mem_support] at hi
    simp only [Finset.coe_Ico, Set.mem_Ico]
    have h0 : 0 ≤ i := by
      by_contra hneg
      exact hi (by rw [cbz_apply_neg ℓ (by omega), mul_zero, zero_smul])
    refine ⟨h0, ?_⟩
    by_contra hge
    exact hi (by
      rw [modeW_vanish_of_lev L hv hw (n := k + l - ℓ - 2 + D + i) (by omega), map_zero,
        smul_zero])
  have hGsupp : (Function.support G) ⊆ ↑(Finset.Ico (0 : ℤ) (k + m)) := by
    intro i hi
    simp only [hG, Function.mem_support] at hi
    simp only [Finset.coe_Ico, Set.mem_Ico]
    have h0 : 0 ≤ i := by
      by_contra hneg
      exact hi (by rw [cbz_apply_neg ℓ (by omega), mul_zero, zero_mul, zero_smul])
    refine ⟨h0, ?_⟩
    by_contra hge
    exact hi (by
      rw [modeW_vanish_of_lev L hu hw (n := i) (by omega), map_zero, smul_zero])
  have hsplit : ∀ i : ℤ, (negOnePow i * cbz ℓ i) •
      (mode (A.YM u) (ℓ - i) (mode (A.YM v) (k + l - ℓ - 2 + D + i) w)
        - negOnePow ℓ • mode (A.YM v) (ℓ + (k + l - ℓ - 2 + D) - i) (mode (A.YM u) i w))
      = F i - G i := by
    intro i
    rw [hF, hG, smul_sub, smul_smul,
      show ℓ + (k + l - ℓ - 2 + D) - i = k + l - 2 + D - i from by ring]
  rw [funext hsplit, finsum_sub_distrib (Set.Finite.subset (Finset.Ico (0 : ℤ) B).finite_toSet
      hFsupp) (Set.Finite.subset (Finset.Ico (0 : ℤ) (k + m)).finite_toSet hGsupp),
    finsum_eq_sum_of_support_subset _ hFsupp, finsum_eq_sum_of_support_subset _ hGsupp]

/-- **The `u`-outside expansion over `AdmLev`** — the structural core of Dong–Jiang Lemma 4.1.
On the level-`m` piece (`0 ≤ m ≤ s`) the level-`D` mode of an arbitrary residue
`Res_z (1+z)^{wt u + s} z^{−q} Y(u,z)v` is a **pure `u`-outside** double sum; the whole `v`-outside
family cancels by `resHom_vOutside_coeff_vanish`. -/
theorem oLevW_resHom_uOutside (L : AdmLev W A) (D s : ℤ) (m : ℤ) (hm0 : 0 ≤ m) (hms : m ≤ s)
    (q : ℤ) {k l : ℤ} (hk : 0 ≤ k) {u v : 𝒱} (hu : u ∈ W.grading k) (hv : v ∈ W.grading l)
    {w : M} (hw : w ∈ L.lev m) :
    oLevW A D (resHom W s q u v) w
      = ∑ j ∈ Finset.range ((k + s).toNat + 1),
          ∑ i ∈ Finset.Ico (0 : ℤ) (m + s - q + 2 - D),
            (cbz (k + s) (j : ℤ) * (negOnePow i * cbz ((j : ℤ) - q) i)) •
              mode (A.YM u) ((j : ℤ) - q - i)
                (mode (A.YM v) (k + l - ((j : ℤ) - q) - 2 + D + i) w) := by
  classical
  have hks : (0 : ℤ) ≤ k + s := by omega
  rw [resHom_homogeneous W s q hu v, map_sum, LinearMap.coe_sum, Finset.sum_apply]
  have hstep : ∀ j ∈ Finset.range ((k + s).toNat + 1),
      (oLevW A D (cbz (k + s) (j : ℤ) • W.smul u ((j : ℤ) - q) v)) w
        = (∑ i ∈ Finset.Ico (0 : ℤ) (m + s - q + 2 - D),
              (cbz (k + s) (j : ℤ) * (negOnePow i * cbz ((j : ℤ) - q) i)) •
                mode (A.YM u) ((j : ℤ) - q - i)
                  (mode (A.YM v) (k + l - ((j : ℤ) - q) - 2 + D + i) w))
          - ∑ i ∈ Finset.Ico (0 : ℤ) (k + m),
              (cbz (k + s) (j : ℤ) *
                (negOnePow i * cbz ((j : ℤ) - q) i * negOnePow ((j : ℤ) - q))) •
                mode (A.YM v) (k + l - 2 + D - i) (mode (A.YM u) i w) := by
    intro j hj
    have hjle : (j : ℤ) ≤ k + s := by
      have hj' : j ≤ (k + s).toNat := by
        simp only [Finset.mem_range] at hj; omega
      omega
    have hB : m - k + ((j : ℤ) - q) + 2 - D ≤ m + s - q + 2 - D := by omega
    rw [map_smul, LinearMap.smul_apply,
      oLevW_smul_step_full L D m hu hv hw ((j : ℤ) - q) (m + s - q + 2 - D) hB,
      smul_sub, Finset.smul_sum, Finset.smul_sum]
    congr 1 <;> exact Finset.sum_congr rfl (fun i _ => by rw [smul_smul])
  rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib]
  have hY : ∑ j ∈ Finset.range ((k + s).toNat + 1),
      ∑ i ∈ Finset.Ico (0 : ℤ) (k + m),
        (cbz (k + s) (j : ℤ) *
          (negOnePow i * cbz ((j : ℤ) - q) i * negOnePow ((j : ℤ) - q))) •
          mode (A.YM v) (k + l - 2 + D - i) (mode (A.YM u) i w) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    simp only [Finset.mem_Ico] at hi
    rw [← Finset.sum_smul, resHom_vOutside_coeff_vanish (k + s) q hks hi.1 (by omega), zero_smul]
  rw [hY, sub_zero]

/-- **High-pole annihilation, homogeneous slots.** -/
theorem oLevW_resHom_vanish_homog (L : AdmLev W A) (D s : ℤ) (m : ℤ) (hm0 : 0 ≤ m) (hms : m ≤ s)
    (q : ℤ) (hq : s + m - D + 2 ≤ q) {k l : ℤ} (hk : 0 ≤ k) {u v : 𝒱} (hu : u ∈ W.grading k)
    (hv : v ∈ W.grading l) {w : M} (hw : w ∈ L.lev m) :
    oLevW A D (resHom W s q u v) w = 0 := by
  rw [oLevW_resHom_uOutside L D s m hm0 hms q hk hu hv hw]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [show Finset.Ico (0 : ℤ) (m + s - q + 2 - D) = (∅ : Finset ℤ) from
    Finset.Ico_eq_empty (by omega), Finset.sum_empty]

/-- **High-pole annihilation, right slot arbitrary.** -/
theorem oLevW_resHom_vanish_homogL (L : AdmLev W A) (D s : ℤ) (m : ℤ) (hm0 : 0 ≤ m) (hms : m ≤ s)
    (q : ℤ) (hq : s + m - D + 2 ≤ q) {k : ℤ} (hk : 0 ≤ k) {u : 𝒱} (hu : u ∈ W.grading k) (v : 𝒱)
    {w : M} (hw : w ∈ L.lev m) : oLevW A D (resHom W s q u v) w = 0 := by
  have hvtop : v ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun v => oLevW A D (resHom W s q u v) w = 0) hvtop ?_ ?_ ?_
  · intro i y hy
    exact oLevW_resHom_vanish_homog L D s m hm0 hms q hq hk hu hy hw
  · change oLevW A D (resHom W s q u 0) w = 0
    have h0 : resHom W s q u (0 : 𝒱) = 0 := by
      have := resHom_smul_right W s q (0 : ℂ) u (0 : 𝒱)
      rwa [zero_smul, zero_smul] at this
    rw [h0, map_zero, LinearMap.zero_apply]
  · intro y z hy hz
    change oLevW A D (resHom W s q u (y + z)) w = 0
    rw [resHom_add_right, map_add, LinearMap.add_apply, hy, hz, add_zero]

/-- **The high-pole annihilation law over `AdmLev`** (all slots).  For `0 ≤ m ≤ s` and
`q ≥ s + m − D + 2`, the level-`D` mode of `Res_z (1+z)^{wt u + s} z^{−q} Y(u,z)v` annihilates the
level-`m` piece.  Unconditional. -/
theorem oLevW_resHom_vanish (L : AdmLev W A) (D s : ℤ) (m : ℤ) (hm0 : 0 ≤ m) (hms : m ≤ s) (q : ℤ)
    (hq : s + m - D + 2 ≤ q) (u v : 𝒱) {w : M} (hw : w ∈ L.lev m) :
    oLevW A D (resHom W s q u v) w = 0 := by
  have hutop : u ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun u => oLevW A D (resHom W s q u v) w = 0) hutop ?_ ?_ ?_
  · intro i y hy
    rcases lt_or_ge i 0 with hneg | hpos
    · rw [W.positivity i hneg, Submodule.mem_bot] at hy
      subst hy
      have h0 : resHom W s q (0 : 𝒱) v = 0 := by
        have := resHom_smul_left W s q (0 : ℂ) (0 : 𝒱) v
        rwa [zero_smul, zero_smul] at this
      rw [h0, map_zero, LinearMap.zero_apply]
    · exact oLevW_resHom_vanish_homogL L D s m hm0 hms q hq hpos hy v hw
  · change oLevW A D (resHom W s q 0 v) w = 0
    have h0 : resHom W s q (0 : 𝒱) v = 0 := by
      have := resHom_smul_left W s q (0 : ℂ) (0 : 𝒱) v
      rwa [zero_smul, zero_smul] at this
    rw [h0, map_zero, LinearMap.zero_apply]
  · intro y z hy hz
    change oLevW A D (resHom W s q (y + z) v) w = 0
    rw [resHom_add_left, map_add, LinearMap.add_apply, hy, hz, add_zero]

/-! ## (F) `O'_{n,m}(𝒱)` annihilates `M(m)` -/

/-- The **level-`d` annihilator** of `w`: the subspace `{x | oLevW A d x w = 0}`. -/
def levAnnW (A : WeakModule W M) (d : ℤ) (w : M) : Submodule ℂ 𝒱 where
  carrier := {x : 𝒱 | oLevW A d x w = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    rw [map_zero, LinearMap.zero_apply]
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_smul, LinearMap.smul_apply, ha, smul_zero]

@[simp] theorem mem_levAnnW (A : WeakModule W M) (d : ℤ) (w : M) (x : 𝒱) :
    x ∈ levAnnW A d w ↔ oLevW A d x w = 0 := Iff.rfl

/-- **The circle generator annihilates `M(m)`**: `o_{n,m}(u ∘ⁿ_m v) w = 0`. -/
theorem oLevW_anmCirc_vanish (L : AdmLev W A) (n m : ℕ) (c d : 𝒱) {w : M}
    (hw : w ∈ L.lev (m : ℤ)) : oLevW A ((m : ℤ) - (n : ℤ)) (anmCirc W n m c d) w = 0 := by
  rw [anmCirc]
  exact oLevW_resHom_vanish L ((m : ℤ) - (n : ℤ)) (m : ℤ) (m : ℤ) (Int.natCast_nonneg m) le_rfl
    ((n : ℤ) + (m : ℤ) + 2) (by omega) c d hw

/-- **`O'_{n,m}(𝒱)` annihilates `M(m)`** (Dong–Jiang Prop. 4.5, `O'`-branch), over `AdmLev`. -/
theorem OnmW_annihilates_lev (L : AdmLev W A) (n m : ℕ) {x : 𝒱} (hx : x ∈ Onm W n m) {w : M}
    (hw : w ∈ L.lev (m : ℤ)) : oLevW A ((m : ℤ) - (n : ℤ)) x w = 0 := by
  have hle : Onm W n m ≤ levAnnW A ((m : ℤ) - (n : ℤ)) w := by
    simp only [Onm, OnmL]
    refine sup_le (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
    · rintro y ⟨c, d, rfl⟩
      exact oLevW_anmCirc_vanish L n m c d hw
    · rintro y ⟨c, rfl⟩
      change oLevW A ((m : ℤ) - (n : ℤ)) (anmLgen W n m c) w = 0
      rw [oLevW_anmLgen_vanish A n m c, LinearMap.zero_apply]
  exact hle hx

/-- **`O_p(𝒱) = O'_{p,p}(𝒱)` annihilates `M(p)`** — Dong–Jiang **Theorem 4.3** on the graded
pieces, over `AdmLev`.  This is what the `O'''` branch of the gate consumes. -/
theorem OnmW_annihilates_diag (L : AdmLev W A) (p : ℕ) {x : 𝒱} (hx : x ∈ Onm W p p) {w : M}
    (hw : w ∈ L.lev (p : ℤ)) : oLevW A ((p : ℤ) - (p : ℤ)) x w = 0 :=
  OnmW_annihilates_lev L p p hx hw

/-- **Zhu's classical bottom annihilation over `AdmLev`**: `o(x) w = 0` for `x ∈ O(𝒱)` and `w` in
the bottom level. -/
theorem O_annihilates_lev_zero (L : AdmLev W A) {x : 𝒱} (hx : x ∈ O W) {w : M}
    (hw : w ∈ L.lev 0) : oLevW A 0 x w = 0 := by
  have hx' : x ∈ Onm W 0 0 := by rwa [Onm_zero_zero_eq_O]
  have hw' : w ∈ L.lev ((0 : ℕ) : ℤ) := by simpa using hw
  have := OnmW_annihilates_lev L 0 0 hx' hw'
  simpa using this

/-! ## (F′) Every lowest-weight `OrdVModule` is an `AdmLev` -/

/-- **A lowest-weight `ℂ`-graded module is a non-negatively levelled weak module**, with
`M(k) = M_{h+k}` for `k ≥ 0` and `⊥` below.  This is the bridge that makes `DJCompositionLev` a
*generalisation* of B1's `DJComposition`, not a different statement. -/
noncomputable def admLevOfLowestWeight (N : OrdVModule W M) {h : ℂ} (hcw : IsLowestWeight N h) :
    AdmLev W N.toWeakModule where
  lev k := if 0 ≤ k then N.weight (h + (k : ℂ)) else ⊥
  lev_neg k hk := if_neg (by omega)
  act_lev := by
    intro w p k a ha x hx
    by_cases hk : 0 ≤ k
    · rw [if_pos hk] at hx
      by_cases hk' : 0 ≤ k + (w - p - 1)
      · rw [if_pos hk', WeakModule.act_def]
        have := mode_mem_weight N ha hx p
        rwa [show h + (k : ℂ) + (w : ℂ) - (p : ℂ) - 1 = h + (((k + (w - p - 1) : ℤ)) : ℂ) from by
          push_cast; ring] at this
      · rw [if_neg hk', Submodule.mem_bot, WeakModule.act_def]
        have hmem := mode_mem_weight N ha hx p
        have hbot : N.weight (h + (k : ℂ) + (w : ℂ) - (p : ℂ) - 1) = ⊥ := by
          by_contra hne
          obtain ⟨r, hr⟩ := hcw _ hne
          have hkeq : ((k : ℂ) + (w : ℂ) - (p : ℂ) - 1) = (r : ℂ) := by
            have hh : h + ((k : ℂ) + (w : ℂ) - (p : ℂ) - 1) = h + (r : ℂ) := by rw [← hr]; ring
            exact add_left_cancel hh
          have hzz : k + w - p - 1 = (r : ℤ) := by exact_mod_cast hkeq
          omega
        rw [hbot, Submodule.mem_bot] at hmem
        exact hmem
    · rw [if_neg hk, Submodule.mem_bot] at hx
      subst hx
      rw [WeakModule.act_zero_right]
      exact Submodule.zero_mem _

@[simp] theorem admLevOfLowestWeight_lev (N : OrdVModule W M) {h : ℂ} (hcw : IsLowestWeight N h)
    (m : ℕ) : (admLevOfLowestWeight N hcw).lev (m : ℤ) = N.weight (h + (m : ℂ)) := by
  rw [admLevOfLowestWeight]
  simp

end Weak

/-! ## (G) The composition law and the annihilation half of the gate -/

/-- **Dong–Jiang Lemma 4.1** over the level interface (`math/0601626`, p. 15):
`o_{n,m}(a ∗ⁿ_{m,p} b) w = o_{n,p}(a) o_{p,m}(b) w` for `w ∈ M(m)`.

This is `ZhuVermaAnArchGateB1.DJComposition` restated for `AdmLev`; the restatement is exactly what
makes it applicable to `M̄_0(A(𝒱))`, which is not a `OrdVModule`.  It **implies** B1's version
(`djComposition_of_djCompositionLev`) and is anchored at `(0,0,0)` by
`djCompositionLev_at_zero`. -/
def DJCompositionLev (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ {M : Type u} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M) (L : AdmLev W A)
    (n m p : ℕ) (a b : 𝒱) {w : M}, w ∈ L.lev (m : ℤ) →
      oLevW A ((m : ℤ) - (n : ℤ)) (anmGen W n m p a b) w
        = oLevW A ((p : ℤ) - (n : ℤ)) a (oLevW A ((m : ℤ) - (p : ℤ)) b w)

/-- **B1 over the level interface**: the zero mode of every element of the full Dong–Jiang ideal
`O_{0,0}(𝒱)` annihilates the bottom level `M(0)` of any non-negatively levelled weak module. -/
def GateAnnihilationLev (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ {M : Type u} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M) (L : AdmLev W A),
    ∀ x ∈ OnmFull W 0 0, ∀ {w : M}, w ∈ L.lev 0 → oLevW A 0 x w = 0

section Reduction

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {A : WeakModule W M}

/-- **`DJCompositionLev` implies B1's `DJComposition`** — every lowest-weight `OrdVModule` is an
`AdmLev` (`admLevOfLowestWeight`) and the two zero modes agree (`oLevW_eq_oLev`). -/
theorem djComposition_of_djCompositionLev (hdj : DJCompositionLev W) : DJComposition W := by
  intro M _ _ N h hcw n m p a b w hw
  have hw' : w ∈ (admLevOfLowestWeight N hcw).lev (m : ℤ) := by
    rw [admLevOfLowestWeight_lev]; exact hw
  exact hdj N.toWeakModule (admLevOfLowestWeight N hcw) n m p a b hw'

/-- **Zhu's `o(u ∗ v) = o(u)o(v)` on the bottom level** (homogeneous slots).  Obtained
directly from `oLevW_resHom_uOutside` at `(D,s,m,q) = (0,0,0,1)`: only `i = 0` survives, and every
`j < k` term dies because its inner `v`-mode overshoots the level ceiling. -/
theorem oLevW_zhuMul_lev_zero_homog (L : AdmLev W A) {k l : ℤ} (hk : 0 ≤ k) {u v : 𝒱}
    (hu : u ∈ W.grading k) (hv : v ∈ W.grading l) {w : M} (hw : w ∈ L.lev 0) :
    oLevW A 0 (zhuMul W u v) w = oLevW A 0 u (oLevW A 0 v w) := by
  classical
  have hIco : Finset.Ico (0 : ℤ) ((0 : ℤ) + 0 - 1 + 2 - 0) = {(0 : ℤ)} := by
    ext i; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
  have hzm : zhuMul W u v = resHom W 0 1 u v := (resHom_zero_one W u v).symm
  rw [hzm, oLevW_resHom_uOutside L 0 0 0 le_rfl le_rfl 1 hk hu hv hw]
  have hstep : ∀ j ∈ Finset.range ((k + 0).toNat + 1),
      (∑ i ∈ Finset.Ico (0 : ℤ) ((0 : ℤ) + 0 - 1 + 2 - 0),
        (cbz (k + 0) (j : ℤ) * (negOnePow i * cbz ((j : ℤ) - 1) i)) •
          mode (A.YM u) ((j : ℤ) - 1 - i)
            (mode (A.YM v) (k + l - ((j : ℤ) - 1) - 2 + 0 + i) w))
      = if (j : ℤ) = k then oLevW A 0 u (oLevW A 0 v w) else 0 := by
    intro j hj
    rw [hIco, Finset.sum_singleton]
    have hn0 : negOnePow (0 : ℤ) = 1 := by
      have := negOnePow_natCast 0
      simpa using this
    rw [hn0, cbz_zero, one_mul, mul_one]
    by_cases hjk : (j : ℤ) = k
    · rw [if_pos hjk, hjk, show (k : ℤ) + 0 = k from by ring]
      have hcs : cbz k k = 1 := by
        rw [show k = ((k.toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg hk).symm,
          cbz_natCast_eq_choose (le_refl k.toNat), Nat.choose_self, Nat.cast_one]
      rw [hcs, one_smul, show (k : ℤ) - 1 - 0 = k - 1 + 0 from by ring,
        show k + l - ((k : ℤ) - 1) - 2 + 0 + 0 = l - 1 + 0 from by ring,
        ← oLevW_homogeneous A 0 hu, ← oLevW_homogeneous A 0 hv]
    · rw [if_neg hjk]
      have hjle : (j : ℤ) ≤ k := by
        have hj' : j ≤ (k + 0).toNat := by
          simp only [Finset.mem_range] at hj; omega
        omega
      rw [modeW_vanish_of_lev L hv hw (n := k + l - ((j : ℤ) - 1) - 2 + 0 + 0) (by omega),
        map_zero, smul_zero]
  rw [Finset.sum_congr rfl hstep, add_zero]
  rw [Finset.sum_eq_single k.toNat]
  · rw [if_pos (by omega : ((k.toNat : ℕ) : ℤ) = k)]
  · intro b _ hb
    exact if_neg (fun hbk => hb (by omega))
  · intro hmem
    exact absurd (Finset.self_mem_range_succ k.toNat) hmem

/-- **Zhu's `o(u ∗ v) = o(u)o(v)` on the bottom level** (all slots). -/
theorem oLevW_zhuMul_lev_zero (L : AdmLev W A) (u v : 𝒱) {w : M} (hw : w ∈ L.lev 0) :
    oLevW A 0 (zhuMul W u v) w = oLevW A 0 u (oLevW A 0 v w) := by
  have key : ∀ (k : ℤ) (u' : 𝒱), u' ∈ W.grading k → ∀ v' : 𝒱,
      oLevW A 0 (zhuMul W u' v') w = oLevW A 0 u' (oLevW A 0 v' w) := by
    intro k u' hu' v'
    rcases lt_or_ge k 0 with hneg | hpos
    · rw [W.positivity k hneg, Submodule.mem_bot] at hu'
      subst hu'
      have h0 : zhuMul W (0 : 𝒱) v' = 0 := by
        have := zhuMul_smul_left W (0 : ℂ) (0 : 𝒱) v'
        rwa [zero_smul, zero_smul] at this
      simp only [h0, map_zero, LinearMap.zero_apply]
    · have hvtop : v' ∈ ⨆ i, W.grading i := by
        rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
      refine Submodule.iSup_induction W.grading
        (motive := fun v' => oLevW A 0 (zhuMul W u' v') w = oLevW A 0 u' (oLevW A 0 v' w))
        hvtop ?_ ?_ ?_
      · intro i y hy
        exact oLevW_zhuMul_lev_zero_homog L hpos hu' hy hw
      · change oLevW A 0 (zhuMul W u' 0) w = oLevW A 0 u' (oLevW A 0 0 w)
        have h0 : zhuMul W u' (0 : 𝒱) = 0 := by
          have := zhuMul_smul_right W (0 : ℂ) u' (0 : 𝒱)
          rwa [zero_smul, zero_smul] at this
        simp only [h0, map_zero, LinearMap.zero_apply]
      · intro y z hy hz
        change oLevW A 0 (zhuMul W u' (y + z)) w = oLevW A 0 u' (oLevW A 0 (y + z) w)
        rw [zhuMul_add_right, map_add, LinearMap.add_apply, hy, hz, map_add,
          LinearMap.add_apply, map_add]
  have hutop : u ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun u => oLevW A 0 (zhuMul W u v) w = oLevW A 0 u (oLevW A 0 v w)) hutop ?_ ?_ ?_
  · intro i y hy
    exact key i y hy v
  · change oLevW A 0 (zhuMul W 0 v) w = oLevW A 0 0 (oLevW A 0 v w)
    have h0 : zhuMul W (0 : 𝒱) v = 0 := by
      have := zhuMul_smul_left W (0 : ℂ) (0 : 𝒱) v
      rwa [zero_smul, zero_smul] at this
    simp only [h0, map_zero, LinearMap.zero_apply]
  · intro y z hy hz
    change oLevW A 0 (zhuMul W (y + z) v) w = oLevW A 0 (y + z) (oLevW A 0 v w)
    rw [zhuMul_add_left, map_add, LinearMap.add_apply, hy, hz, map_add, LinearMap.add_apply]

/-- **Anchor: `DJCompositionLev` at `(n,m,p) = (0,0,0)` is a THEOREM** over `AdmLev`.  At
`(0,0,0)` the Dong–Jiang product is Zhu's (`anmGen_zero_zero_zero`), so this is exactly
`o(u ∗ v) = o(u)o(v)` on the bottom.  It pins the normalisation of the carried hypothesis against
an already-proved statement — and, unlike B1's `djComposition_at_zero`, it needs no `OrdVModule`. -/
theorem djCompositionLev_at_zero (L : AdmLev W A) (u v : 𝒱) {w : M}
    (hw : w ∈ L.lev ((0 : ℕ) : ℤ)) :
    oLevW A (((0 : ℕ) : ℤ) - ((0 : ℕ) : ℤ)) (anmGen W 0 0 0 u v) w
      = oLevW A (((0 : ℕ) : ℤ) - ((0 : ℕ) : ℤ)) u
          (oLevW A (((0 : ℕ) : ℤ) - ((0 : ℕ) : ℤ)) v w) := by
  have hw' : w ∈ L.lev 0 := by simpa using hw
  have hz : ((0 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) = (0 : ℤ) := by norm_num
  rw [hz, anmGen_zero_zero_zero]
  exact oLevW_zhuMul_lev_zero L u v hw'

/-- **The `O''_{0,0}` (associator-defect) generators annihilate the bottom**, given the composition
law.  Four applications of Dong–Jiang Lemma 4.1 rewrite both halves of the associator as the same
triple composite `o_{p₃,p₂}(a) o_{p₂,p₁}(b) o_{p₁,0}(c) w`. -/
theorem oLevW_assocDefect_vanish (hdj : DJCompositionLev W) (L : AdmLev W A) (p₁ p₂ p₃ : ℕ)
    (a b c u : 𝒱) {w : M} (hw : w ∈ L.lev 0) :
    oLevW A 0 (assocDefect W 0 0 p₁ p₂ p₃ a b c u) w = 0 := by
  have hw0 : w ∈ L.lev ((0 : ℕ) : ℤ) := by simpa using hw
  set y : M := oLevW A (((0 : ℕ) : ℤ) - (p₁ : ℤ)) c w with hy
  have hyw : y ∈ L.lev (p₁ : ℤ) := oLevW_mem_level L 0 p₁ c hw0
  have e1 := hdj A L p₃ 0 p₁ (anmGen W p₃ p₁ p₂ a b) c hw0
  have e2 := hdj A L p₃ p₁ p₂ a b hyw
  have e3 := hdj A L p₃ 0 p₂ a (anmGen W p₂ 0 p₁ b c) hw0
  have e4 := hdj A L p₂ 0 p₁ b c hw0
  have hX : oLevW A (((0 : ℕ) : ℤ) - (p₃ : ℤ))
      (anmGen W p₃ 0 p₁ (anmGen W p₃ p₁ p₂ a b) c
        - anmGen W p₃ 0 p₂ a (anmGen W p₂ 0 p₁ b c)) w = 0 := by
    rw [map_sub, LinearMap.sub_apply, e1, e3, e2, e4, ← hy, sub_self]
  have e0 := hdj A L 0 0 p₃ u
      (anmGen W p₃ 0 p₁ (anmGen W p₃ p₁ p₂ a b) c
        - anmGen W p₃ 0 p₂ a (anmGen W p₂ 0 p₁ b c)) hw0
  have hz : ((0 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) = (0 : ℤ) := by norm_num
  rw [assocDefect, ← hz, e0, hX, map_zero]

/-- **The `O'''_{0,0}` (level-mixing) generators annihilate the bottom**, given the composition
law.  Two applications of Lemma 4.1 peel the generator down to
`o_{0,p}(a) o_{p,p}(g) o_{p,0}(v) w`, and the middle factor dies by the **proven**
`OnmW_annihilates_diag`. -/
theorem oLevW_levelMix_vanish (hdj : DJCompositionLev W) (L : AdmLev W A) (p : ℕ) (a v g : 𝒱)
    (hg : g ∈ Onm W p p) {w : M} (hw : w ∈ L.lev 0) :
    oLevW A 0 (levelMix W 0 0 p a g v) w = 0 := by
  have hw0 : w ∈ L.lev ((0 : ℕ) : ℤ) := by simpa using hw
  set y : M := oLevW A (((0 : ℕ) : ℤ) - (p : ℤ)) v w with hy
  have hyw : y ∈ L.lev (p : ℤ) := oLevW_mem_level L 0 p v hw0
  have e0 := hdj A L 0 0 p (anmGen W 0 p p a g) v hw0
  have e1 := hdj A L 0 p p a g hyw
  have hmid : oLevW A ((p : ℤ) - (p : ℤ)) g y = 0 := OnmW_annihilates_diag L p hg hyw
  have hz : ((0 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) = (0 : ℤ) := by norm_num
  rw [levelMix, ← hz, e0, ← hy, e1, hmid, map_zero]

/-- **B1, assembled over `AdmLev`**: the composition law (Dong–Jiang Lemma 4.1) implies the full
annihilation half of the `(0,0)` gate.  The `O'_{0,0}` summand is discharged by the **proven**
`OnmW_annihilates_lev`. -/
theorem gateAnnihilationLev_of_djCompositionLev (hdj : DJCompositionLev W) :
    GateAnnihilationLev W := by
  intro M _ _ A L x hx w hw
  have hw0 : w ∈ L.lev ((0 : ℕ) : ℤ) := by simpa using hw
  have hz : ((0 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) = (0 : ℤ) := by norm_num
  have hle : OnmFull W 0 0 ≤ levAnnW A (0 : ℤ) w := by
    simp only [OnmFull, OnmAssoc, OnmLevel]
    refine sup_le (sup_le ?_ (Submodule.span_le.mpr ?_)) (Submodule.span_le.mpr ?_)
    · intro z hz'
      have := OnmW_annihilates_lev L 0 0 hz' hw0
      rw [hz] at this
      exact this
    · rintro z ⟨q₁, q₂, q₃, aa, bb, cc, uu, rfl⟩
      exact oLevW_assocDefect_vanish hdj L q₁ q₂ q₃ aa bb cc uu hw
    · rintro z ⟨q, aa, vv, gg, hgg, rfl⟩
      exact oLevW_levelMix_vanish hdj L q aa vv gg hgg hw
  exact hle hx

/-- **The level version of B1 implies B1 itself** (`ZhuVermaAnArchGateB1.GateAnnihilation`), via
`admLevOfLowestWeight`.  So nothing proved in `ZhuVermaAnArchGateB1` is lost by moving to the
weaker interface — the `AdmLev` statement is strictly more general. -/
theorem gateAnnihilation_of_gateAnnihilationLev (hann : GateAnnihilationLev W) :
    GateAnnihilation W := by
  intro M _ _ N h hcw x hx w hw
  have hlev := admLevOfLowestWeight_lev N hcw 0
  rw [show ((0 : ℕ) : ℤ) = (0 : ℤ) from by norm_num] at hlev
  have hw0 : w ∈ (admLevOfLowestWeight N hcw).lev 0 := by
    rw [hlev]; simpa using hw
  have hz := hann N.toWeakModule (admLevOfLowestWeight N hcw) x hx hw0
  rwa [oLevW_zero_eq_oMod] at hz

end Reduction

/-! ## (H) B3 — the regular-module instantiation -/

/-- **A level-`0` realization of a bundled `A(𝒱)`-module `U`** — exactly the data step B3 needs, and
exactly the data step B2 produces.  A non-negatively levelled weak `𝒱`-module together with an
injective, `A(𝒱)`-equivariant embedding of `U` into its bottom level.

Note the deliberate absence of any finiteness: `U` is an arbitrary `ℂ`-space, which is what allows
B3 to be run at the (generally infinite-dimensional) regular module `U = A(𝒱)`. -/
structure GateRealization (W : VertexOperatorAlgebra 𝒱) (U : AMod W) where
  /-- The carrier of the realizing module. -/
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module : Module ℂ carrier]
  /-- The weak `𝒱`-module structure. -/
  weak : WeakModule W carrier
  /-- The non-negative level filtration. -/
  levels : AdmLev W weak
  /-- The embedding of `U` as the bottom. -/
  emb : U.carrier →ₗ[ℂ] carrier
  /-- The image of `U` lies in the bottom level `M(0)`. -/
  emb_lev : ∀ u : U.carrier, emb u ∈ levels.lev 0
  /-- `U` survives: the embedding is injective. -/
  emb_inj : Function.Injective emb
  /-- `A(𝒱)`-equivariance: `[1 ⊗ ρ([a])u] = o(a)·[1 ⊗ u]` for homogeneous `a ∈ 𝒱_w`. -/
  emb_act : ∀ ⦃w : ℤ⦄ ⦃a : 𝒱⦄, a ∈ W.grading w → ∀ u : U.carrier,
    emb (U.ρ (mk W a) u) = weak.act a (w - 1) (emb u)

attribute [instance] GateRealization.addCommGroup GateRealization.module

namespace GateRealization

variable {W : VertexOperatorAlgebra 𝒱} {U : AMod W}

/-- **`A(𝒱)`-equivariance for all of `𝒱`**: `emb (ρ([x])·u) = o(x)·emb u`, obtained from the
homogeneous clause by the grade decomposition of `x`. -/
theorem emb_act_all (R : GateRealization W U) (x : 𝒱) (u : U.carrier) :
    R.emb (U.ρ (_root_.VOA.mk W x) u) = oLevW R.weak 0 x (R.emb u) := by
  have hxtop : x ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun x => R.emb (U.ρ (_root_.VOA.mk W x) u) = oLevW R.weak 0 x (R.emb u))
    hxtop ?_ ?_ ?_
  · intro i y hy
    rw [R.emb_act hy u, oLevW_homogeneous R.weak 0 hy, WeakModule.act_def,
      show i - 1 + 0 = i - 1 from by ring]
  · change R.emb (U.ρ (_root_.VOA.mk W 0) u) = oLevW R.weak 0 0 (R.emb u)
    simp only [map_zero, LinearMap.zero_apply]
  · intro y z hy hz
    change R.emb (U.ρ (_root_.VOA.mk W (y + z)) u) = oLevW R.weak 0 (y + z) (R.emb u)
    rw [map_add, map_add, LinearMap.add_apply, map_add, hy, hz, map_add, LinearMap.add_apply]

end GateRealization

/-- **B3 — the gate from annihilation plus a realization of the regular module.**  For
`x ∈ O_{0,0}(𝒱)` the class `[x] ∈ A(𝒱)` is read off its zero mode:
`emb [x] = emb (ρ([x])·[𝟙]) = o(x)·emb [𝟙] = 0` (annihilation, since `emb [𝟙]` is a bottom vector),
and `emb` is injective, so `[x] = 0`, i.e. `x ∈ O(𝒱)`. -/
theorem gate_le_of_realization {W : VertexOperatorAlgebra 𝒱} (hann : GateAnnihilationLev W)
    (R : GateRealization W (regularAMod W)) : OnmFull W 0 0 ≤ O W := by
  intro x hx
  have hemb : R.emb (mk W x) = 0 := by
    have h1 : R.emb ((regularAMod W).ρ (mk W x) (one W)) = oLevW R.weak 0 x (R.emb (one W)) :=
      R.emb_act_all x (one W)
    rw [regularAMod_apply_one] at h1
    rw [h1, hann R.weak R.levels x hx (R.emb_lev (one W))]
  have h0 : mk W x = 0 := by
    have := R.emb_inj (by rw [hemb, map_zero] : R.emb (mk W x) = R.emb 0)
    exact this
  rwa [mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0

/-- **The `(0,0)` gate, from B1 + B2 + B3.**  With the proved `Onm_zero_zero_eq_O`
(`O'_{0,0}(𝒱) = O(𝒱)`) the containment upgrades to an equality of ideals. -/
theorem gate_of_realization {W : VertexOperatorAlgebra 𝒱} (hann : GateAnnihilationLev W)
    (R : GateRealization W (regularAMod W)) : OnmFull W 0 0 = O W :=
  le_antisymm (gate_le_of_realization hann R)
    (by rw [← Onm_zero_zero_eq_O]; exact Onm_le_OnmFull W 0 0)

/-! ## (I) The B2 → B3 bridge: `M̄_0(U)` is a `GateRealization` -/

section Bridge

open VHat VHat.DLM3

variable {W : VertexOperatorAlgebra 𝒱} {U : Type u} [AddCommGroup U] [Module ℂ U]

/-- **`M̄_0(U)(d) = 0` for `d < 0`** — the image of the PBW-free `levCover_eq_bot_of_neg` in the
defect quotient.  This is the admissibility clause `AdmLev.lev_neg` for `M̄_0(U)`. -/
theorem levBar_eq_bot_of_neg (Q : ParabolicRep W 0 U) {d : ℤ} (hd : d < 0) : levBar Q d = ⊥ := by
  rw [levBar, levCover_eq_bot_of_neg Q hd, Submodule.map_bot]

/-- **`M̄_0(U)` is a non-negatively levelled weak module.**  Unconditional: the weak-module
structure is `indBarWeakModule`, the levels are `levBar`, the shift is `actMode_levBar`, and the
negative levels vanish by `levBar_eq_bot_of_neg`. -/
noncomputable def admLevOfIndBar (Q : ParabolicRep W 0 U) : AdmLev W (indBarWeakModule Q) where
  lev := levBar Q
  lev_neg _ hd := levBar_eq_bot_of_neg Q hd
  act_lev := by
    intro w p k a ha x hx
    rw [indBarWeakModule_act]
    exact actMode_levBar Q ha hx

@[simp] theorem admLevOfIndBar_lev (Q : ParabolicRep W 0 U) (k : ℤ) :
    (admLevOfIndBar Q).lev k = levBar Q k := rfl

/-- **The B2 → B3 bridge.** Given the two Dong–Li–Mason inputs — the independent
bottom-injectivity datum `BottomProjection` and `DefectPairsToZero` (= their `U(V̂)W ⊆ J`) — the
`GateRealization` of the bundled `A(𝒱)`-module `U`. Concrete adjoint and Heisenberg projection
instances are proved axiom-free. The companion `voaPBWBottomProjection` supplies arbitrary
parabolic instances from the generic relative-induction field of the theorem
`VOA.pbw : PBWPrinciple`; no implication from its affine-vacuum
field alone is claimed.

Every field is discharged: the weak-module structure and levels by `admLevOfIndBar`
(unconditional), `emb_lev` by `indBarBottom_mem_levBar`, `emb_inj` by
`indBarBottom_injective_of_defectPairsToZero` (= DLM3's `J ∩ U = 0`), and `emb_act` by
`indBarBottom_zhu_equivariant` (= DLM3 Prop. 3.1 at `n = 0`). This construction is conditional on
the two inputs; it does not establish their satisfiability for the displayed `U`. There is no additional hidden
finiteness assumption. -/
noncomputable def gateRealizationOfSurvival (W : VertexOperatorAlgebra 𝒱) (V : AMod W)
    (Pr : BottomProjection (parabolicRepOfAMod W V)) (hdef : DefectPairsToZero Pr) :
    GateRealization W V where
  carrier := IndBar (parabolicRepOfAMod W V)
  weak := indBarWeakModule (parabolicRepOfAMod W V)
  levels := admLevOfIndBar (parabolicRepOfAMod W V)
  emb := indBarBottom (parabolicRepOfAMod W V)
  emb_lev u := by
    have := indBarBottom_mem_levBar (parabolicRepOfAMod W V) u
    rw [admLevOfIndBar_lev]
    simpa using this
  emb_inj := indBarBottom_injective_of_defectPairsToZero Pr hdef
  emb_act := by
    intro w a ha u
    rw [indBarWeakModule_act]
    exact indBarBottom_zhu_equivariant W V ha u

end Bridge

/-! ## (J) The gate from the three named inputs, and its downstream consumers -/

section Consumers

variable {W : VertexOperatorAlgebra 𝒱}

open VHat VHat.DLM3

/-- **The `(0,0)` gate reduced to exactly three named inputs.**

1. `DJCompositionLev W` — Dong–Jiang **Lemma 4.1** (B1's residual, over `AdmLev`);
2. `BottomProjection (parabolicRepOfAMod W (regularAMod W))` — Dong–Li–Mason's bottom-injectivity
   step, as an explicit assumption; the companion `voaPBWBottomProjection` supplies this instance
   from the generic relative-induction field of `VOA.pbw`;
3. `DefectPairsToZero Pr` — Dong–Li–Mason's `U(V̂)W ⊆ J` (their Props 4.3 + 4.6).

Nothing else is assumed.  This is **not** a proof of the gate: it is the precise reduction. -/
theorem gate_of_dj_and_dlm3 (hdj : DJCompositionLev W)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hdef : DefectPairsToZero Pr) : OnmFull W 0 0 = O W :=
  gate_of_realization (gateAnnihilationLev_of_djCompositionLev hdj)
    (gateRealizationOfSurvival W (regularAMod W) Pr hdef)

/-- **`O_0(𝒱) = O(𝒱)`** — the Frenkel–Zhu level-`0` ideal is Zhu's ideal (off the proved
`Onm_diag_eq_OnFull` and `Onm_zero_zero_eq_O`). -/
theorem onFull_zero_eq_O (W : VertexOperatorAlgebra 𝒱) : OnFull W 0 = O W := by
  rw [← Onm_diag_eq_OnFull W 0, Onm_zero_zero_eq_O]

/-- **The gate is `DJAnnEqAn W 0`** — Dong–Jiang Prop. 4.6 at the base level, in the form the
`M(U)` layer consumes. -/
theorem djAnnEqAn_zero_of_gate (hgate : OnmFull W 0 0 ≤ O W) : DJAnnEqAn W 0 := by
  intro x hx
  rw [onFull_zero_eq_O]
  exact hgate hx

/-- `A_{0,0}(𝒱) = A(𝒱)` at the level of ideals, given the gate. -/
theorem onmFull_diag_zero_eq_of_gate (hgate : OnmFull W 0 0 ≤ O W) :
    OnmFull W 0 0 = OnFull W 0 :=
  OnmFull_diag_eq W 0 (djAnnEqAn_zero_of_gate hgate)

/-- **The gate discharges the `O''` generator family of the combinatorial route.**  This is the
first hypothesis of `onmFull_zero_zero_eq_O_of_gens` (`ZhuVermaAnArchOnmCollapseZero`): the
representation-theoretic gate *implies* the generator statements that the refuted combinatorial
route was trying to prove directly, so the two routes agree on their common conclusion. -/
theorem assocDefect_zero_mem_of_gate (hgate : OnmFull W 0 0 ≤ O W) (p₁ p₂ p₃ : ℕ)
    (a b c v : 𝒱) : assocDefect W 0 0 p₁ p₂ p₃ a b c v ∈ Onm W 0 0 := by
  rw [Onm_zero_zero_eq_O]
  refine hgate ?_
  have hmem : assocDefect W 0 0 p₁ p₂ p₃ a b c v ∈ OnmAssoc W 0 0 :=
    Submodule.subset_span ⟨p₁, p₂, p₃, a, b, c, v, rfl⟩
  rw [OnmFull]
  exact Submodule.mem_sup_left (Submodule.mem_sup_right hmem)

/-- **The gate discharges the `O'''` generator family of the combinatorial route** — the second
hypothesis of `onmFull_zero_zero_eq_O_of_gens`. -/
theorem levelMix_zero_mem_of_gate (hgate : OnmFull W 0 0 ≤ O W) (p : ℕ) (a v g : 𝒱)
    (hg : g ∈ Onm W p p) : levelMix W 0 0 p a g v ∈ Onm W 0 0 := by
  rw [Onm_zero_zero_eq_O]
  refine hgate ?_
  have hmem : levelMix W 0 0 p a g v ∈ OnmLevel W 0 0 :=
    Submodule.subset_span ⟨p, a, v, g, hg, rfl⟩
  rw [OnmFull]
  exact Submodule.mem_sup_right hmem

/-- **`A_{0,0}(𝒱) ≃ A_0(𝒱)`**, given the gate — the base-level instance of `anmFullDiagEquiv`. -/
noncomputable def anmFullDiagEquivZero (hgate : OnmFull W 0 0 ≤ O W) :
    AnmFull W 0 0 ≃ₗ[ℂ] AnFull W 0 :=
  anmFullDiagEquiv W 0 (djAnnEqAn_zero_of_gate hgate)

/-- **`M(U)(0) ≅ U`** on the `DJPiece` carrier, given the gate — the base-level instance of
`djPieceMEquiv`. -/
noncomputable def djPieceMEquivZero (hgate : OnmFull W 0 0 ≤ O W) (V : AmMod W 0) :
    DJPiece W V 0 ≃ₗ[ℂ] V.carrier :=
  djPieceMEquiv W 0 (djAnnEqAn_zero_of_gate hgate) V

/-- **The bottom of `M(U)` is `U`**, given the gate — the base-level instance of
`DJCarrier.degMEquiv`.  This is the statement the Zhu bijection consumes. -/
noncomputable def djCarrierDegZeroEquiv (hgate : OnmFull W 0 0 ≤ O W) (V : AmMod W 0) :
    DJCarrier.deg W V 0 ≃ₗ[ℂ] V.carrier :=
  DJCarrier.degMEquiv W 0 (djAnnEqAn_zero_of_gate hgate) V

/-- **The whole downstream package from the three named inputs.**  Recorded as one statement so
that the exact dependency of the consumers is visible in a single place. -/
theorem downstream_of_dj_and_dlm3 (hdj : DJCompositionLev W)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hdef : DefectPairsToZero Pr) :
    OnmFull W 0 0 = O W ∧ DJAnnEqAn W 0 ∧ OnmFull W 0 0 = OnFull W 0 := by
  have hg : OnmFull W 0 0 = O W := gate_of_dj_and_dlm3 hdj Pr hdef
  have hle : OnmFull W 0 0 ≤ O W := le_of_eq hg
  exact ⟨hg, djAnnEqAn_zero_of_gate hle, onmFull_diag_zero_eq_of_gate hle⟩

end Consumers

end VOA

/-! ## Axiom audit (final gate) -/
