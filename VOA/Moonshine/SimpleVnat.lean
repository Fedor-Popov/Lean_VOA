/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.SimpleForm

/-!
# Simplicity of `V♮`  (MonsterRoadmap `moonshine_simple`, the TRAP)

For the vertex operator algebra `vnatVOA htt` on `Vnat = V_Λ^+ × (V_Λ^T)^+` (block vertex map with
the genuine adjoint `W̄ = leechWbar`), the block-diagonal form `B♮ = B_V ⊕ TPForm`
(`SimpleForm.natInvForm`) is fully FHL-invariant, normalised `(𝟙|𝟙) = 1`, and has trivial
radical.  Li's theorem in the library (`LiRadical.isSimple_iff_leftRadical_eq_bot`: for a fully
invariant normalised form, simple ⟺ radical `= 0`; the radical is the maximal proper ideal) then
gives simplicity.

## Main results
* `vnatVOA_isSimple htt : (vnatVOA htt).IsSimple` — the library's genuine notion
  (`VertexOperatorAlgebra.IsSimple`: `⊤ ≠ ⊥` and every ideal is `⊥` or `⊤`).
* `vnatVOA_invariantForm_nondegenerate` — `B♮` is fully invariant, normalised, with trivial
  radical and nondegenerate on every weight space.
* `vnatVOA_canonicalForm_eq` — the library's canonical (Li/FHL) invariant form of `V♮` **is**
  `B♮`, hence `vnatVOA_canonical_leftRadical`: the canonical form is nondegenerate.
* `vnat_isSimple_of_TPBlockLocal_frame` — the same, stated through the four-pair hypothesis of
  `M8h0.vnat_VOA_of_TPBlockLocal_frame` (DGM (4.23) on the frame cyclic vectors).

## Why this is not the TRAP
The square-zero extension `V_Λ^+ ⋉ TP` (`W̄ := 0`) is not simple (`0 × TP` is a proper ideal), and
`B♮` is not invariant for it: the `W̄`-block of invariance (`leechWbar_adj'`) is exactly the
statement that `W̄` is the `B♮`-adjoint of `W`, which `W̄ = 0` violates.  The proof here uses that
adjunction in both off-diagonal blocks (`SimpleForm.pieceD` reads it backwards through
`double_sum_cancel`).

## Status
`sorry`-free; no new axioms.  The ONLY hypothesis is `htt` (twisted × twisted locality, M8h), or
in the frame variant the four instances of `TPBlockLocal` (DGM 4.23) — the same hypotheses under
which the VOA structure itself exists.  Not proved here: `htt` itself.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.SimpleNat

open VertexOperatorAlgebra VnatAxioms SkewAdjoint InvForm

section Vnat

variable (htt : ∀ t t' : TP, Local (YnatT leechWbar t) (YnatT leechWbar t'))

/-- **`V♮` is simple** (conditional only on `htt`, the hypothesis of `vnatVOA`). -/
theorem vnatVOA_isSimple : (vnatVOA htt).IsSimple :=
  (LiRadical.isSimple_iff_leftRadical_eq_bot (natInvForm_isFullyInvariant htt)
    (natInvForm_normalized htt)).2 (natInvForm_leftRadical htt)

/-- **The invariant form of `V♮` is nondegenerate**: `B♮ = B_V ⊕ TPForm` is fully invariant,
normalised, has trivial radical, and is nondegenerate on every weight space `V♮ₙ`. -/
theorem vnatVOA_invariantForm_nondegenerate :
    (natInvForm htt).IsFullyInvariant ∧ (natInvForm htt).Normalized ∧
      InvariantForm.leftRadical (natInvForm htt) = ⊥ ∧
        GradedNondeg (vnatVOA htt) (natInvForm htt).form :=
  ⟨natInvForm_isFullyInvariant htt, natInvForm_normalized htt, natInvForm_leftRadical htt,
    gradedNondeg_of_radical _ (natInvForm_leftRadical htt)⟩

theorem vnatVOA_vacuum_ne_zero : (vnatVOA htt).vacuum ≠ 0 :=
  LiRadical.vacuum_ne_zero_of_normalized (natInvForm_normalized htt)

/-- `L₁V♮₁ = 0` (indeed `V♮₁ = 0`). -/
theorem vnatVOA_L1_one : ∀ v, v ∈ (vnatVOA htt).grading 1 → (vnatVOA htt).L 1 v = 0 := by
  intro v hv
  change v ∈ gradingNat 1 at hv
  rw [gradingNat_one, Submodule.mem_bot] at hv
  rw [hv, map_zero]

/-- The library's canonical invariant form of `V♮` is `B♮`. -/
theorem vnatVOA_canonicalForm_eq :
    (canonicalInvariantForm (vnatVOA_vacuum_ne_zero htt) (vnatVOA_L1_one htt)).form = natForm :=
  (invariantForm_unique_FHL (vnatVOA_vacuum_ne_zero htt) (vnatVOA_L1_one htt)
    (natInvForm_isFullyInvariant htt) (natInvForm_normalized htt)).symm

/-- The canonical invariant form of `V♮` is nondegenerate. -/
theorem vnatVOA_canonical_leftRadical :
    InvariantForm.leftRadical
      (canonicalInvariantForm (vnatVOA_vacuum_ne_zero htt) (vnatVOA_L1_one htt)) = ⊥ :=
  (LiRadical.isSimple_iff_canonical_nondegenerate _ _).1 (vnatVOA_isSimple htt)

end Vnat

/-- **Simplicity through the four-pair frame hypothesis** of
`M8h0.vnat_VOA_of_TPBlockLocal_frame`: there are frame cyclic vectors `x s ∈ T_s⁺` such that DGM
(4.23) on the four pairs `(x i, x j)` yields a **simple** vertex operator algebra structure on
`Vnat` with the genuine block vertex map, vacuum `(𝟙,0)`, conformal vector `(ω,0)`, `c = 24` and
grading `gradingNat`. -/
theorem vnat_isSimple_of_TPBlockLocal_frame :
    ∃ x : ZMod 2 → TP, (∀ s, x s ∈ TPframe s) ∧
      ((∀ i j, TPBlockLocal leechWbar (x i) (x j)) →
        ∃ V : VertexOperatorAlgebra Vnat,
          V.Y = Ynat wbarL ∧ V.vacuum = vacNat ∧ V.conformalVector = omegaNat ∧
            V.centralCharge = 24 ∧ V.grading = gradingNat ∧ V.IsSimple) := by
  obtain ⟨x, hx, hspan⟩ := M8h0.exists_frame_modeSpan
  refine ⟨x, hx, fun h423 => ?_⟩
  have htt0 : ∀ i j, Local (YnatT leechWbar (x i)) (YnatT leechWbar (x j)) := fun i j =>
    (YnatT_local_iff _ _ _).2 ⟨M8h0.leechWbar_VPBlockLocal _ _, h423 i j⟩
  have htt := M8h0.YnatT_local_all_of_gen hspan htt0
  exact ⟨vnatVOA htt, rfl, rfl, rfl, rfl, rfl, vnatVOA_isSimple htt⟩

end VOA.Moonshine.SimpleNat
