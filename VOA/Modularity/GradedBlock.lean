/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.BlockSlash

/-!
# The slash-stable normal form of Zhu's block conditions

`Modularity.BlockSlash` put Zhu's conditions in their two `G₂`-free normal forms and proved the
`ω`-law covariant.  This file packages the normal forms as `IsGradedBlock`, builds the slashed
family `blockSlash`, and proves

  `isGradedBlock_blockSlash` — **the space of genus-one blocks is `SL₂(ℤ)`-stable.**

The `ω`-law travels by `serreDerivC_slashC` + `slashC_zhuGC`; the `[−2]`-law travels the same way,
but its weights are **carried** (`SqModeWeighted`): Zhu's grading
`a[j] : 𝒱_{[K]} ⊗ 𝒱_{[n]} → 𝒱_{[K+n−j−1]}` needs the second (square-bracket) vertex-algebra
structure, of which this repo has only the Virasoro part — which *does* supply the `ω`-case
(`Lsq_mem_sqWeightSpace`).

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  Residual: `SqModeWeighted` (Zhu's square-bracket mode
grading for a general homogeneous `a`) — a named, true, standard fact, not derivable from the
square-bracket structure currently in the repo.
-/

namespace VOA

open Complex
open scoped BigOperators MatrixGroups

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Uniqueness of the `L[0]`-weight -/

section Weight

theorem sqWeight_unique (W : VertexOperatorAlgebra 𝒱) {v : 𝒱} (hv : v ≠ 0) {m n : ℂ}
    (hm : v ∈ sqWeightSpace W m) (hn : v ∈ sqWeightSpace W n) : m = n := by
  rw [mem_sqWeightSpace_iff] at hm hn
  have hz : (m - n) • v = 0 := by rw [sub_smul, ← hm, ← hn, sub_self]
  rcases smul_eq_zero.mp hz with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hv

open Classical in
/-- **The `L[0]`-weight of `v`**, chosen; `0` when `v` is `0` or inhomogeneous (where it is
irrelevant, because every block vanishes on `0`). -/
noncomputable def sqWtOf (W : VertexOperatorAlgebra 𝒱) (v : 𝒱) : ℤ :=
  if h : ∃ n : ℤ, v ∈ sqWeightSpace W (n : ℂ) ∧ v ≠ 0 then h.choose else 0

theorem sqWtOf_eq (W : VertexOperatorAlgebra 𝒱) {n : ℤ} {v : 𝒱} (hv0 : v ≠ 0)
    (hv : v ∈ sqWeightSpace W (n : ℂ)) : sqWtOf W v = n := by
  classical
  have hex : ∃ k : ℤ, v ∈ sqWeightSpace W (k : ℂ) ∧ v ≠ 0 := ⟨n, hv, hv0⟩
  rw [sqWtOf, dif_pos hex]
  have hspec := hex.choose_spec
  have hc : ((hex.choose : ℤ) : ℂ) = (n : ℂ) := sqWeight_unique W hv0 hspec.1 hv
  exact_mod_cast hc

end Weight

/-! ## The graded block conditions -/

/-- **Zhu's genus-one conformal blocks, in slash-stable normal form.**

The conditions are those of `IsAnalyticBlock` with the anomalous `G₂`-terms resolved: the `k = 1`
term of (ii) is *killed* by (i), and the `k = 1` term of (iii) is *absorbed* into the Serre
derivative `∂_n`.  What remains has, in every slot, a coefficient that is a genuine modular form of
exactly the matching weight — which is why this is the notion `SL₂(ℤ)` acts on. -/
structure IsGradedBlock (W : VertexOperatorAlgebra 𝒱) (F : 𝒱 → ℂ → ℂ) : Prop where
  /-- Holomorphy on the upper half-plane. -/
  holo : ∀ v : 𝒱, DifferentiableOn ℂ (F v) (imGT 0)
  /-- Vanishing at `0`. -/
  zerov : ∀ z ∈ imGT 0, F 0 z = 0
  /-- Additivity inside a weight space. -/
  addv : ∀ (n : ℤ) (v w : 𝒱), v ∈ sqWeightSpace W (n : ℂ) → w ∈ sqWeightSpace W (n : ℂ) →
    ∀ z ∈ imGT 0, F (v + w) z = F v z + F w z
  /-- Homogeneity inside a weight space. -/
  smulv : ∀ (n : ℤ) (c : ℂ) (v : 𝒱), v ∈ sqWeightSpace W (n : ℂ) → ∀ z ∈ imGT 0,
    F (c • v) z = c * F v z
  /-- (i) `F(a[0]v) = 0`. -/
  vanish : ∀ (ka : ℕ), 1 ≤ ka → ∀ a ∈ W.grading (ka : ℤ), ∀ (v : 𝒱), ∀ z ∈ imGT 0,
    F (vSqZ W a ka 0 v) z = 0
  /-- (ii) Zhu's `[−2]`-identity, `G₂`-free, on homogeneous vectors. -/
  negTwo : ∀ (ka : ℕ), 1 ≤ ka → ∀ a ∈ W.grading (ka : ℤ), ∀ (K n : ℤ),
    a ∈ sqWeightSpace W (K : ℂ) → ∀ v : 𝒱, v ∈ sqWeightSpace W (n : ℂ) → ∀ z ∈ imGT 0,
    F (vSqZ W a ka (-2) v) z
      + ∑ᶠ m : ℕ, ((2 * (m + 2) - 1 : ℕ) : ℂ)
          * (zhuGC (m + 2) z * F (vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v) z) = 0
  /-- (iii) The `ω`-law as a Serre-derivative equation. -/
  omega : ∀ (n : ℤ) (v : 𝒱), v ∈ sqWeightSpace W (n : ℂ) → ∀ z ∈ imGT 0,
    F (Lsq W (-2) v) z
      = serreDerivC n (F v) z
        + ∑ᶠ m : ℕ, zhuGC (m + 2) z * F (Lsq W (2 * (m + 2) - 2 : ℤ) v) z

section ToGraded

variable {W : VertexOperatorAlgebra 𝒱} {F : 𝒱 → ℂ → ℂ}

/-- **The analytic block conditions imply the graded normal form.** -/
theorem IsAnalyticBlock.toGradedBlock (hF : IsAnalyticBlock W F) : IsGradedBlock W F where
  holo := hF.holo
  zerov := fun z _ => hF.zerov z
  addv := fun _ v w _ _ z _ => hF.addv v w z
  smulv := fun _ c v _ z _ => hF.smulv c v z
  vanish := fun ka hka a ha v z _ => by rw [hF.vanish ka hka a ha v]; rfl
  negTwo := fun ka hka a ha _ _ _ v _ z hz => hF.negTwo_tail ka hka ha v hz
  omega := fun _ _ hv _ hz => hF.omega_serre hv hz

end ToGraded

/-! ## Zhu's square-bracket mode grading (the carried datum) -/

/-- **Zhu's square-bracket mode grading**: for `a` homogeneous of ordinary weight `ka` *and* of
`L[0]`-weight `K`, and `v` of `L[0]`-weight `n`, the mode `a[j]` shifts the `L[0]`-weight by
`K − j − 1`.  Stated in exactly the two instances Zhu's `[−2]`-identity needs.

This is a theorem of the *second* vertex-algebra structure `(𝒱, Y[·,·], ω̃)`; the repo has its
Virasoro part (`Lsq_virasoro_apply'`, giving `Lsq_mem_sqWeightSpace`) but not the general mode
algebra, so it is carried. -/
def SqModeWeighted (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ (ka : ℕ), 1 ≤ ka → ∀ a ∈ W.grading (ka : ℤ), ∀ (K n : ℤ), a ∈ sqWeightSpace W (K : ℂ) →
    ∀ v : 𝒱, v ∈ sqWeightSpace W (n : ℂ) →
      vSqZ W a ka (-2) v ∈ sqWeightSpace W (((K + n + 1 : ℤ)) : ℂ) ∧
        ∀ m : ℕ, vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v
          ∈ sqWeightSpace W (((K + n - 2 * (m : ℤ) - 3 : ℤ)) : ℂ)

/-! ## The slashed family -/

section Slash

variable {W : VertexOperatorAlgebra 𝒱}

/-- Holomorphy is preserved by the slash action. -/
theorem differentiableOn_slashC (k : ℤ) (γ : SL(2, ℤ)) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (imGT 0)) : DifferentiableOn ℂ (slashC k γ f) (imGT 0) := by
  intro z hz
  have hmz := mobiusC_mem_imGT γ hz
  have hfd : DifferentiableAt ℂ f (mobiusC γ z) :=
    hf.differentiableAt ((isOpen_imGT 0).mem_nhds hmz)
  exact ((hasDerivAt_slashC k γ f hz hfd.hasDerivAt).differentiableAt).differentiableWithinAt

/-- **The slashed family** `(F ∣ γ) v = (F v) ∣[wt v] γ`. -/
noncomputable def blockSlash (W : VertexOperatorAlgebra 𝒱) (γ : SL(2, ℤ)) (F : 𝒱 → ℂ → ℂ) :
    𝒱 → ℂ → ℂ := fun v => slashC (sqWtOf W v) γ (F v)

/-- `blockSlash` really is *the* slash: on `𝒱_{[n]}` it is `∣[n] γ`. -/
theorem isSlashOf_blockSlash (W : VertexOperatorAlgebra 𝒱) (γ : SL(2, ℤ)) {F : 𝒱 → ℂ → ℂ}
    (hF0 : ∀ z ∈ imGT 0, F 0 z = 0) : IsSlashOf W γ F (blockSlash W γ F) := by
  intro n v hv z hz
  have hmz := mobiusC_mem_imGT γ hz
  rw [blockSlash]
  by_cases hv0 : v = 0
  · subst hv0
    rw [slashC, slashC, hF0 _ hmz, zero_mul, zero_mul]
  · rw [sqWtOf_eq W hv0 hv]

/-- **The block conditions are `SL₂(ℤ)`-stable.**

The `ω`-law travels by the equivariance of the Serre derivative (`serreDerivC_slashC`); the
`[−2]`-law by the modularity of `G_{2k}`, `k ≥ 2` (`slashC_zhuGC`) — the weights being supplied by
`SqModeWeighted`. -/
theorem isGradedBlock_blockSlash {F : 𝒱 → ℂ → ℂ} (hF : IsGradedBlock W F)
    (hwt : SqModeWeighted W) (γ : SL(2, ℤ)) : IsGradedBlock W (blockSlash W γ F) := by
  have hslash := isSlashOf_blockSlash W γ hF.zerov
  refine ⟨fun v => differentiableOn_slashC _ γ (hF.holo v), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- zero
    intro z hz
    rw [blockSlash, slashC, hF.zerov _ (mobiusC_mem_imGT γ hz), zero_mul]
  · -- additivity on a weight space
    intro n v w hv hw z hz
    rw [hslash n (v + w) (Submodule.add_mem _ hv hw) z hz, hslash n v hv z hz,
      hslash n w hw z hz, slashC, slashC, slashC, hF.addv n v w hv hw _ (mobiusC_mem_imGT γ hz)]
    ring
  · -- homogeneity on a weight space
    intro n c v hv z hz
    rw [hslash n (c • v) (Submodule.smul_mem _ c hv) z hz, hslash n v hv z hz, slashC, slashC,
      hF.smulv n c v hv _ (mobiusC_mem_imGT γ hz)]
    ring
  · -- (i)
    intro ka hka a ha v z hz
    rw [blockSlash, slashC, hF.vanish ka hka a ha v _ (mobiusC_mem_imGT γ hz), zero_mul]
  · -- (ii)
    intro ka hka a ha K n haK v hv z hz
    have hmz := mobiusC_mem_imGT γ hz
    have hD := denomC_ne_zero γ hz
    obtain ⟨hw0, hwm⟩ := hwt ka hka a ha K n haK v hv
    have hlaw := hF.negTwo ka hka a ha K n haK v hv _ hmz
    have htail : ∀ m : ℕ, ((2 * (m + 2) - 1 : ℕ) : ℂ)
          * (zhuGC (m + 2) (mobiusC γ z)
            * F (vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v) (mobiusC γ z))
          * denomC γ z ^ (-(K + n + 1))
        = ((2 * (m + 2) - 1 : ℕ) : ℂ)
          * (zhuGC (m + 2) z * blockSlash W γ F (vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v) z) := by
      intro m
      rw [hslash _ _ (hwm m) z hz, slashC]
      have h := slashC_zhuGC_mul (j := m + 2) (by omega) γ (K + n - 2 * (m : ℤ) - 3)
        (F (vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v)) hz
      rw [show (2 * (((m + 2 : ℕ)) : ℤ) + (K + n - 2 * (m : ℤ) - 3)) = K + n + 1 from by
        push_cast; ring] at h
      rw [← h]
      ring
    have hsum : (∑ᶠ m : ℕ, ((2 * (m + 2) - 1 : ℕ) : ℂ)
          * (zhuGC (m + 2) (mobiusC γ z)
            * F (vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v) (mobiusC γ z)))
          * denomC γ z ^ (-(K + n + 1))
        = ∑ᶠ m : ℕ, ((2 * (m + 2) - 1 : ℕ) : ℂ)
            * (zhuGC (m + 2) z * blockSlash W γ F (vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v) z) := by
      rw [finsum_mul]
      exact finsum_congr htail
    rw [hslash _ _ hw0 z hz, slashC, ← hsum, ← add_mul, hlaw, zero_mul]
  · -- (iii)
    intro n v hv z hz
    exact omega_serre_slash (F := F) (G := blockSlash W γ F) hF.holo
      (fun k u hu w hw => hF.omega k u hu w hw) hslash hv hz

end Slash

end VOA
