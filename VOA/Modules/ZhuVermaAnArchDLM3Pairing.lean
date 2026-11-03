/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchGateB3
import VOA.Modules.ZhuVermaAnArchBottomAn

/-!
# DLM3 §4 at `n = 0` — the pairing kernel, consolidated

This file is the **S0 / S1 / S2** slice of the B2 attack plan (`PHASE4_PLAN` C-11).  Its first job
is bookkeeping: S0, S1 and S2 turned out to be *already proved*, so they are re-exported here with
their exact provenance rather than re-proved.  Its second job is the genuinely new content that the
audit exposed, all of it **proved**:

* the **radical-valued** form of S1 + S2 (the proved results only give the `π₀`-valued form), and
* the **elimination of DLM3 Proposition 4.7** as a separate carried hypothesis.

## S0 — discharged, no hypothesis is carried

`ParabolicRep` (`ZhuVermaAnArchDLM3Induced`) has exactly three fields — `act`, `deep_zero`,
`vacuum_one` — and `act` is a *bundled* Lie-algebra morphism `Pn W n →ₗ⁅ℂ⁆ End ℂ U`.  So DLM3
Proposition 3.1's bracket compatibility is not a side condition at all: it is `LieHom.map_lie`, and
`parabolicRepOfAMod` discharges it outright (`ZhuVermaAnArchDLM3Zero.zhuDeg0_bracket_parabolic`).
Recorded here as `parabolicRepOfAMod_act_lie`, together with the scalar input it rests on —
Zhu's Lemma 2.1(iii) pushed into `A(𝒱)` (`mk_resFull_eq_zhuMul_sub`), from the proved
`zhu_comm_mod_O`.

## S1 / S2 — proved, and where

* **S1** = DLM3 Lemma 4.4 at `n = 0` = `indDefectVec_bottom_neg_one` (+ `_nat`, `_gen`),
  `ZhuVermaAnArchDLM3Prop43`.  Its `i = 0` case is *consumed*, not proved: it is `AMod.ρ_mul`,
  the `A(𝒱)`-module axiom on `U`.
* **S2** = DLM3 Lemma 4.5 at `n = 0` = `indDefectVec_bottom_negPole`, same file, by the
  `L(−1)`-derivation induction through `defectVec_Lneg1_left`.
* Their assembly is `proj_indDefectVec_bottom` = **DLM3 Proposition 4.3 at `n = 0`**.

⚠ **Source correction (verified against `refs/dlm3.txt:1029-1085`).**  DLM3 print Lemma 4.5 with the
exponent `(z₀+z₂)^{wt a + m + j}`, i.e. with the *running* residue index `m`.  That reading is
**false**: the identity fails exactly when `m + j < 0`.  The `m` is a typo for the fixed level `n`.
The paper's own proof forces this — it says "true for `m ≥ −1` by Lemma 4.4", whose exponent is
`wt a + n + j`, and its induction step runs at exponent `wt a + 1 + m + j`, which is
`wt (L(−1)a) + n + j`.  The proved `indDefectVec_bottom_negPole` is stated in the corrected form
(level `w + l − ℓ − N − 2 = 0`, no dependence on the pole order), so nothing in the repo is
affected.

## New here (1): S1 + S2 valued in the radical, and the bottom base case reduced

`defectPairsToZero_of_bottom_of_stable` (`ZhuVermaAnArchDLM3Survival`) wants the bottom defects in
`radical Pr`, which is strictly more than `π₀`-vanishing.  The proved
`indDefectVec_bottom_level_le` says the bottom defect is *literally zero* in every level `≤ 0`, so
that whole range is free:

* `indDefectVec_bottom_mem_radical_of_level_le` — free, no hypothesis;
* `indDefectVec_bottom_mem_radical_of_homog` — the general-slot statement follows from the
  homogeneous one **restricted to strictly positive level**;
* `defectPairsToZero_of_bottom_pos_of_stable` — hence DLM3's Prop 4.3/4.6 bottom base case has
  content only at **strictly positive level**.

## New here (2): DLM3 Proposition 4.7 is not an independent hypothesis

`defectPairsToZero_iff_proj_defectSubmodule` proves

    DefectPairsToZero Pr  ↔  defectSubmodule (indRho P) ≤ ker Pr.proj,

using the proved constructive description `defectOrbit_eq_defectSubmodule`
(`ZhuVermaAnArchBottomAn`) of the defect submodule as the `U(V̂)`-orbit span.  The
`U(V̂)`-quantifier of DLM3's radical is thereby absorbed into a submodule inclusion, and
`projKills_iff_bottomPropagates_and_orbitPropagates` shows that the **single** `Prop`
`ProjKillsDefectSubmodule` is equivalent to the **pair** (DLM3 Prop 4.6, DLM3 Prop 4.7) that
`ZhuVermaAnArchDLM3Prop43` currently carries.  Nothing is assumed: the equivalence is proved, and
the residual is named.

Also recorded: `bottomPropagates_iff` — DLM3 Proposition 4.6 as *stated* in the repo is an
implication whose antecedent is already discharged by `proj_indDefectVec_bottom`, so it is
logically just its own conclusion.

## What is still open (named, never assumed)

`ProjKillsDefectSubmodule Pr` — equivalently the pair (DLM3 Prop 4.6, DLM3 Prop 4.7) — is **not**
proved here; it is the S3 + S4 half of the C-11 decomposition. The bottom-injectivity boundary
encoded by `BottomProjection` / `PBWFreeness` remains an explicit named hypothesis; level
independence is unconditional. Concrete adjoint and Heisenberg instances exist axiom-free, while
the project-level `regularAMod` witness is supplied by `voaPBWBottomProjection`, from the generic
relative-induction field of the theorem `VOA.pbw : PBWPrinciple`.

## References
DLM3 (`q-alg/9612010v2`) §4: Lemma 4.4 (`refs/dlm3.txt:774-804`), Lemma 4.5 (`:1029-1085`),
Props 4.3 / 4.6 (`:1086-1096`) / 4.7 (`:1098-1122`); Prop 3.1 (`:489`); Zhu Lemma 2.1(iii)
(`:130`, proved in full at `refs/dlm2.txt:575-591`).
-/

namespace VOA

open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat

namespace DLM3

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## S0 — DLM3 Proposition 3.1, discharged -/

/-- **Zhu's Lemma 2.1(iii) in `A(𝒱)`** — the scalar input of DLM3 Proposition 3.1.  For homogeneous
`u ∈ 𝒱_K` and `v ∈ 𝒱_M`, the Frenkel–Zhu residue `Res_z (1+z)^{K−1} Y(u,z)v` represents the
*commutator* of `A(𝒱)`.  Immediate from the proved `zhu_comm_mod_O`. -/
theorem mk_resFull_eq_zhuMul_sub (W : VertexOperatorAlgebra 𝒱) {K M : ℕ} {u v : 𝒱}
    (hu : u ∈ W.grading (K : ℤ)) (hv : v ∈ W.grading (M : ℤ)) :
    _root_.VOA.mk W (resFull W ((K : ℤ) - 1) 0 u v)
      = _root_.VOA.mk W (zhuMul W u v)
        - _root_.VOA.mk W (zhuMul W v u) := by
  have h : _root_.VOA.mk W
      (zhuMul W u v - zhuMul W v u - resFull W ((K : ℤ) - 1) 0 u v) = 0 := by
    rw [_root_.VOA.mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact zhu_comm_mod_O W hu hv
  rw [map_sub, map_sub, sub_eq_zero] at h
  exact h.symm

/-- **S0 is not a hypothesis.**  DLM3 Proposition 3.1's bracket compatibility for the `n = 0`
parabolic representation attached to an `A(𝒱)`-module is `LieHom.map_lie`: `ParabolicRep.act` is a
*bundled* Lie morphism, and `parabolicRepOfAMod` discharges it via
`zhuDeg0_bracket_parabolic`.  Nothing is carried. -/
theorem parabolicRepOfAMod_act_lie (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (g h : Pn W 0) :
    (parabolicRepOfAMod W U).act ⁅g, h⁆
      = (parabolicRepOfAMod W U).act g * (parabolicRepOfAMod W U).act h
        - (parabolicRepOfAMod W U).act h * (parabolicRepOfAMod W U).act g := by
  rw [LieHom.map_lie, Ring.lie_def]

/-! ## The `U(V̂)`-quantifier of DLM3's radical, absorbed

`radical Pr` carries an explicit quantifier over the enveloping algebra `U(V̂)`.  The proved
`defectOrbit_eq_defectSubmodule` identifies the `U(V̂)`-orbit span of the defect set with the defect
submodule, which turns `DefectPairsToZero` into a plain submodule inclusion. -/

section General

variable {n : ℕ} {U : Type u} [AddCommGroup U] [Module ℂ U] {P : ParabolicRep W n U}

/-- The radical sits inside `ker π₀` (take `y = 1`) — DLM3's `J ⊆ ker⟨u′, ·⟩`. -/
theorem radical_le_ker_proj (Pr : BottomProjection P) :
    radical Pr ≤ LinearMap.ker Pr.proj := by
  intro v hv
  rw [LinearMap.mem_ker]
  have h1 := hv 1
  rwa [map_one, Module.End.one_apply] at h1

/-- The radical is closed under the whole enveloping algebra: `y · J ⊆ J`.  (The `U(V̂)`-quantifier
in the definition of `J` absorbs the extra factor, exactly as `radical_invariant` does for a single
mode.) -/
theorem toAlgHom_mem_radical (Pr : BottomProjection P) {v : IndMod P} (hv : v ∈ radical Pr)
    (g : UEnv W) : (indRho P).toAlgHom g v ∈ radical Pr := by
  rw [mem_radical_iff]
  intro y
  have hmul : (indRho P).toAlgHom y ((indRho P).toAlgHom g v)
      = (indRho P).toAlgHom (y * g) v := by
    rw [map_mul, Module.End.mul_apply]
  rw [hmul]
  exact hv (y * g)

/-- **DLM3's `U(V̂)W ⊆ J` is a submodule inclusion.**

    `DefectPairsToZero Pr ↔ defectSubmodule (indRho P) ≤ ker Pr.proj`.

Forward: `defectSubmodule_le_radical` then `radical_le_ker_proj`.  Backward: by the proved
`defectOrbit_eq_defectSubmodule`, every `U(V̂)`-translate `y · δ` of a defect already lies in the
defect submodule, so the `U(V̂)`-quantifier of `radical` is discharged by the inclusion.

**This is why DLM3 Proposition 4.7 is not an independent input**: its content is the invariance of
the defect submodule, which is proved. -/
theorem defectPairsToZero_iff_proj_defectSubmodule (Pr : BottomProjection P) :
    DefectPairsToZero Pr ↔ VHatRep.defectSubmodule (indRho P) ≤ LinearMap.ker Pr.proj := by
  constructor
  · intro h
    exact le_trans (defectSubmodule_le_radical Pr h) (radical_le_ker_proj Pr)
  · intro h a b z ℓ K
    rw [mem_radical_iff]
    intro y
    have hmem : (indRho P).toAlgHom y (VHatRep.defectVec (indRho P) a b z ℓ K)
        ∈ VHatRep.defectSubmodule (indRho P) := by
      rw [← VHatRep.defectOrbit_eq_defectSubmodule]
      exact Submodule.subset_span
        ⟨y, VHatRep.defectVec (indRho P) a b z ℓ K, ⟨a, b, z, ℓ, K, rfl⟩, rfl⟩
    exact LinearMap.mem_ker.mp (h hmem)

/-- **The residual of B2, as ONE named `Prop`**: the bottom projection annihilates the whole defect
submodule.  Equivalent to `DefectPairsToZero` (`defectPairsToZero_iff_proj_defectSubmodule`) and,
at `P = parabolicRepOfAMod W U`, to the *pair* of DLM3 Propositions 4.6 and 4.7
(`projKills_iff_bottomPropagates_and_orbitPropagates`).  **Carried, never assumed.** -/
def ProjKillsDefectSubmodule (Pr : BottomProjection P) : Prop :=
  VHatRep.defectSubmodule (indRho P) ≤ LinearMap.ker Pr.proj

/-- `ProjKillsDefectSubmodule ⟹ DefectPairsToZero`. -/
theorem defectPairsToZero_of_projKills (Pr : BottomProjection P)
    (h : ProjKillsDefectSubmodule Pr) : DefectPairsToZero Pr :=
  (defectPairsToZero_iff_proj_defectSubmodule Pr).mpr h

/-- `DefectPairsToZero ⟹ ProjKillsDefectSubmodule`. -/
theorem projKills_of_defectPairsToZero (Pr : BottomProjection P)
    (h : DefectPairsToZero Pr) : ProjKillsDefectSubmodule Pr :=
  (defectPairsToZero_iff_proj_defectSubmodule Pr).mp h

/-- **The invariant-cover criterion.**  Any `V̂`-invariant submodule that covers the defect set and
lies in `ker π₀` closes B2.  (`radical Pr` is the largest such; this is the useful direction.) -/
theorem defectPairsToZero_of_invariant_cover (Pr : BottomProjection P)
    {D : Submodule ℂ (IndMod P)}
    (hcov : ∀ (a b : 𝒱) (z : IndMod P) (ℓ K : ℤ),
      VHatRep.defectVec (indRho P) a b z ℓ K ∈ D)
    (hinv : VHatRep.IsInvariant (indRho P) D)
    (hker : D ≤ LinearMap.ker Pr.proj) : DefectPairsToZero Pr := by
  rw [defectPairsToZero_iff_proj_defectSubmodule]
  refine le_trans ?_ hker
  rw [← VHatRep.defectOrbit_eq_defectSubmodule]
  refine VHatRep.defectOrbit_le_of_invariant (fun d hd => ?_) hinv
  obtain ⟨a, b, z, ℓ, K, rfl⟩ := hd
  exact hcov a b z ℓ K

end General

/-! ## S1 + S2 in the radical, and the bottom base case reduced to positive level -/

section AMod

/-- **S1 + S2, radical-valued, free below the bottom level.**  The proved
`indDefectVec_bottom_level_le` makes the bottom defect *literally zero* in every level `≤ 0`, so it
lies in the radical with no hypothesis at all. -/
theorem indDefectVec_bottom_mem_radical_of_level_le (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (Pr : BottomProjection (parabolicRepOfAMod W U)) {w l : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading w) (hb : b ∈ W.grading l) (u : U.carrier) {ℓ N : ℤ}
    (hS : w + l - ℓ - N - 2 ≤ 0) :
    VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) a b
      (indBottom (parabolicRepOfAMod W U) u) ℓ N ∈ radical Pr := by
  rw [indDefectVec_bottom_level_le W U ha hb u hS]
  exact Submodule.zero_mem _

/-- **The bottom base case of B2 has content only at strictly positive level.**  Given the
homogeneous, strictly-positive-level instances, the general (non-homogeneous, all-level) statement
follows: the level `≤ 0` range is free (`indDefectVec_bottom_mem_radical_of_level_le`) and the two
`𝒱`-slots are handled by the proved bilinearity of `defectVec`. -/
theorem indDefectVec_bottom_mem_radical_of_homog (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (Pr : BottomProjection (parabolicRepOfAMod W U))
    (h : ∀ ⦃w l : ℤ⦄ ⦃a b : 𝒱⦄, a ∈ W.grading w → b ∈ W.grading l →
      ∀ (u : U.carrier) (ℓ N : ℤ), 0 < w + l - ℓ - N - 2 →
        VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) a b
          (indBottom (parabolicRepOfAMod W U) u) ℓ N ∈ radical Pr)
    (u : U.carrier) (a b : 𝒱) (ℓ N : ℤ) :
    VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) a b
      (indBottom (parabolicRepOfAMod W U) u) ℓ N ∈ radical Pr := by
  have htr := ind_actModeTruncated (parabolicRepOfAMod W U)
  -- the homogeneous–homogeneous case: split on the level
  have hhom : ∀ ⦃w l : ℤ⦄ ⦃a' b' : 𝒱⦄, a' ∈ W.grading w → b' ∈ W.grading l →
      VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) a' b'
        (indBottom (parabolicRepOfAMod W U) u) ℓ N ∈ radical Pr := by
    intro w l a' b' ha' hb'
    rcases lt_or_ge 0 (w + l - ℓ - N - 2) with hS | hS
    · exact h ha' hb' u ℓ N hS
    · exact indDefectVec_bottom_mem_radical_of_level_le W U Pr ha' hb' u hS
  -- extend in the right slot, then in the left slot
  have hkey : ∀ (w : ℤ) (a' : 𝒱), a' ∈ W.grading w → ∀ b' : 𝒱,
      VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) a' b'
        (indBottom (parabolicRepOfAMod W U) u) ℓ N ∈ radical Pr := by
    intro w a' ha' b'
    have hbtop : b' ∈ ⨆ i, W.grading i := by
      rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
    refine Submodule.iSup_induction W.grading
      (motive := fun b' => VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) a' b'
        (indBottom (parabolicRepOfAMod W U) u) ℓ N ∈ radical Pr) hbtop ?_ ?_ ?_
    · intro i y hy
      exact hhom ha' hy
    · change VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) a' 0
        (indBottom (parabolicRepOfAMod W U) u) ℓ N ∈ radical Pr
      rw [VHatRep.defectVec_zero_left₂ _ htr]
      exact Submodule.zero_mem _
    · intro y z hy hz
      change VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) a' (y + z)
        (indBottom (parabolicRepOfAMod W U) u) ℓ N ∈ radical Pr
      rw [VHatRep.defectVec_add_left₂ _ htr]
      exact Submodule.add_mem _ hy hz
  have hatop : a ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun a => VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) a b
      (indBottom (parabolicRepOfAMod W U) u) ℓ N ∈ radical Pr) hatop ?_ ?_ ?_
  · intro i y hy
    exact hkey i y hy b
  · change VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) 0 b
      (indBottom (parabolicRepOfAMod W U) u) ℓ N ∈ radical Pr
    rw [VHatRep.defectVec_zero_left₁ _ htr]
    exact Submodule.zero_mem _
  · intro y z hy hz
    change VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) (y + z) b
      (indBottom (parabolicRepOfAMod W U) u) ℓ N ∈ radical Pr
    rw [VHatRep.defectVec_add_left₁ _ htr]
    exact Submodule.add_mem _ hy hz

/-- **The sharpened generation reduction.**  `defectPairsToZero_of_bottom_of_stable` with its
bottom base case cut down to *homogeneous slots at strictly positive level* — everything else is
discharged by S1 + S2. -/
theorem defectPairsToZero_of_bottom_pos_of_stable (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (Pr : BottomProjection (parabolicRepOfAMod W U))
    (hbot : ∀ ⦃w l : ℤ⦄ ⦃a b : 𝒱⦄, a ∈ W.grading w → b ∈ W.grading l →
      ∀ (u : U.carrier) (ℓ N : ℤ), 0 < w + l - ℓ - N - 2 →
        VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) a b
          (indBottom (parabolicRepOfAMod W U) u) ℓ N ∈ radical Pr)
    (hstab : ∀ (x : VHatCarrier W) (z : IndMod (parabolicRepOfAMod W U)),
      z ∈ survSet Pr → indRho (parabolicRepOfAMod W U) x z ∈ survSet Pr) :
    DefectPairsToZero Pr :=
  defectPairsToZero_of_bottom_of_stable Pr
    (fun u a b ℓ K => indDefectVec_bottom_mem_radical_of_homog W U Pr hbot u a b ℓ K) hstab

/-! ## The two carried DLM3 propagations, consolidated into one -/

/-- **DLM3 Proposition 4.6 as stated in the repo is its own conclusion.**  Its antecedent is exactly
the proved `proj_indDefectVec_bottom` (DLM3 Proposition 4.3 at `n = 0`), so the implication carries
no extra strength. -/
theorem bottomPropagates_iff (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (Pr : BottomProjection (parabolicRepOfAMod W U)) :
    BottomPropagates Pr ↔ ∀ (a b : 𝒱) (z : IndMod (parabolicRepOfAMod W U)) (ℓ N : ℤ),
      Pr.proj (VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) a b z ℓ N) = 0 := by
  constructor
  · intro h
    exact h (fun a' b' u' ℓ' N' => proj_indDefectVec_bottom W U Pr a' b' u' ℓ' N')
  · intro h _
    exact h

/-- **The consolidation.**  The single `Prop` `ProjKillsDefectSubmodule` is *equivalent* to the
pair (DLM3 Proposition 4.6, DLM3 Proposition 4.7) that `ZhuVermaAnArchDLM3Prop43` carries.  So B2's
residual — beyond the independent `BottomProjection` assumption — is one submodule inclusion, not two
propagations. -/
theorem projKills_iff_bottomPropagates_and_orbitPropagates (W : VertexOperatorAlgebra 𝒱)
    (U : AMod W) (Pr : BottomProjection (parabolicRepOfAMod W U)) :
    ProjKillsDefectSubmodule Pr ↔ (BottomPropagates Pr ∧ OrbitPropagates Pr) := by
  constructor
  · intro h
    have hd : DefectPairsToZero Pr := defectPairsToZero_of_projKills Pr h
    refine ⟨fun _ a b z ℓ N => ?_, fun _ a b z ℓ N y => hd a b z ℓ N y⟩
    have h1 := hd a b z ℓ N 1
    rwa [map_one, Module.End.one_apply] at h1
  · rintro ⟨h46, h47⟩
    exact projKills_of_defectPairsToZero Pr (defectPairsToZero_of_prop43 W U Pr h46 h47)

/-- **`U` survives, on the consolidated residual.**  DLM3 Theorem 4.1 at `n = 0` with the two
propagations replaced by the single inclusion `defectSubmodule ≤ ker π₀`. -/
theorem indBarBottom_injective_of_projKills (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (Pr : BottomProjection (parabolicRepOfAMod W U)) (h : ProjKillsDefectSubmodule Pr) :
    Function.Injective (indBarBottom (parabolicRepOfAMod W U)) :=
  indBarBottom_injective_of_defectPairsToZero Pr (defectPairsToZero_of_projKills Pr h)

end AMod

end DLM3
end VHat

/-! ## The gate, on the consolidated residual -/

section GateConsumers

open VHat VHat.DLM3

variable {W : VertexOperatorAlgebra 𝒱}

/-- **The `(0,0)` gate on exactly two named inputs, the second consolidated.**

    (GATE)   OnmFull W 0 0 = O W

* `hP : PBWFreeness (parabolicRepOfAMod W (regularAMod W))` — an explicit bottom-injectivity
  assumption; the companion theorem `voaPBWFreeness` supplies this instance from the generic
  relative-induction field of the theorem `VOA.pbw : PBWPrinciple`;
* `h : ProjKillsDefectSubmodule hP.bottomProjection` — DLM3's `U(V̂)W ⊆ J` at `n = 0`, in its
  submodule form, *replacing* the pair (DLM3 Prop 4.6, DLM3 Prop 4.7).

Not a proof of the gate: the exact reduction, with both inputs named. -/
theorem gate_of_pbw_projKills (hP : PBWFreeness (parabolicRepOfAMod W (regularAMod W)))
    (h : ProjKillsDefectSubmodule hP.bottomProjection) : OnmFull W 0 0 = O W :=
  gate_of_pbw hP (defectPairsToZero_of_projKills hP.bottomProjection h)

/-- The downstream package on the consolidated residual. -/
theorem downstream_of_pbw_projKills (hP : PBWFreeness (parabolicRepOfAMod W (regularAMod W)))
    (h : ProjKillsDefectSubmodule hP.bottomProjection) :
    OnmFull W 0 0 = O W ∧ DJAnnEqAn W 0 ∧ OnmFull W 0 0 = OnFull W 0 ∧ OnmCollapses W 0 :=
  downstream_of_pbw hP (defectPairsToZero_of_projKills hP.bottomProjection h)

end GateConsumers

end VOA

-- Axiom check. Explicit `PBWFreeness`/`BottomProjection` parameters are not printed.
