import VOA.Examples.VirasoroQuotientForm
import VOA.Examples.VirasoroGradedField
import VOA.Examples.LeeYangRigidity

/-!
# Weightwise uniqueness of the normalized Virasoro form

A family of bilinear forms `β n` on the weight spaces of the universal Virasoro
VOA, which is vacuum-normalized and for which every creation mode `L_{-k}`
(`k ≥ 2`) is adjoint to `L_k`, coincides with the canonical simple form
`Bsimp c` evaluated on the simple projections.

No form on the whole space, no symmetry, and no adjointness for `L_{-1}`,
`L_0`, `L_1` is assumed: only the relations used to move a PBW creation word
from the left argument to the right one. This is the weightwise refinement of
`VirFormSym.invariantForm_ext`.
-/

namespace VOA.LeeYangShortcut

open VirModule VirSimple VirQuotForm

variable {c : ℂ}

/-- Weightwise adjointness of each creation mode `L_{-i-2}` with `L_{i+2}`.
Membership of the two moved vectors is part of the data, so no index casts
appear; it holds automatically when `m = n + i + 2`. -/
def WeightwiseCreationAdjoint
    (β : ∀ n : ℤ, LinearMap.BilinForm ℂ ((virasoroVOA c).grading n)) : Prop :=
  ∀ (i : ℕ) (n m : ℤ) (x : (virasoroVOA c).grading n) (y : (virasoroVOA c).grading m)
    (hx : Lop c (-(i : ℤ) - 2) x ∈ (virasoroVOA c).grading m)
    (hy : Lop c ((i : ℤ) + 2) y ∈ (virasoroVOA c).grading n),
    β m ⟨_, hx⟩ y = β n x ⟨_, hy⟩

/-- The universal vacuum as a weight-zero vector. -/
noncomputable def vacuumWeight (c : ℂ) : (virasoroVOA c).grading 0 :=
  ⟨vacVec c, vacVec_mem_gradingVir_zero c⟩

/-- PBW-word step of the uniqueness argument. -/
theorem weightForm_word_eq_Bpull
    (β : ∀ n : ℤ, LinearMap.BilinForm ℂ ((virasoroVOA c).grading n))
    (hvac : β 0 (vacuumWeight c) (vacuumWeight c) = 1)
    (hadj : WeightwiseCreationAdjoint β) (w : List ℕ)
    (y : (virasoroVOA c).grading (energyVir w : ℤ)) :
    β _ ⟨negWordVir c w, negWord_mem_gradingVir c w⟩ y =
      (Bpull c).form (negWordVir c w) y := by
  induction w with
  | nil =>
      have hy : (y : VirUniv c) ∈ ℂ ∙ vacVec c := by
        rw [← gradingVir_zero c]; exact y.2
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hy
      have hy' : y = a • vacuumWeight c := Subtype.ext ha.symm
      subst hy'
      change β 0 (vacuumWeight c) (a • vacuumWeight c) =
        (Bpull c).form (vacVec c) (a • vacVec c)
      rw [map_smul, map_smul, hvac]
      have hn : (Bpull c).form (vacVec c) (vacVec c) = 1 := Bpull_normalized c
      rw [hn]
  | cons i w ih =>
      have hxw : negWordVir c w ∈ (virasoroVOA c).grading (energyVir w : ℤ) :=
        negWord_mem_gradingVir c w
      have hx : Lop c (-(i : ℤ) - 2) (negWordVir c w) ∈
          (virasoroVOA c).grading (energyVir (i :: w) : ℤ) :=
        negWord_mem_gradingVir c (i :: w)
      have hy : Lop c ((i : ℤ) + 2) y ∈ (virasoroVOA c).grading (energyVir w : ℤ) := by
        have h := Lop_maps_grading c ((i : ℤ) + 2) y.2
        have he : ((energyVir (i :: w) : ℕ) : ℤ) - ((i : ℤ) + 2) = (energyVir w : ℤ) := by
          rw [energyVir_cons]; push_cast; ring
        rw [he] at h
        exact h
      have h1 := hadj i (energyVir w) (energyVir (i :: w)) ⟨_, hxw⟩ y hx hy
      have h2 := ih ⟨_, hy⟩
      have h3 := (Bpull c).virasoro_adj (-(i : ℤ) - 2) (negWordVir c w) y
      rw [virasoroVOA_L_eq_Lop, virasoroVOA_L_eq_Lop,
        show -(-(i : ℤ) - 2) = (i : ℤ) + 2 by ring] at h3
      change β _ ⟨Lop c (-(i : ℤ) - 2) (negWordVir c w), hx⟩ y =
        (Bpull c).form (Lop c (-(i : ℤ) - 2) (negWordVir c w)) y
      rw [h1, h3]
      exact h2

/-- **Weightwise uniqueness.** A vacuum-normalized family of weight-space
forms, adjoint for the creation modes, is the normalized simple Virasoro form. -/
theorem weightForm_eq_Bsimp
    (β : ∀ n : ℤ, LinearMap.BilinForm ℂ ((virasoroVOA c).grading n))
    (hvac : β 0 (vacuumWeight c) (vacuumWeight c) = 1)
    (hadj : WeightwiseCreationAdjoint β) (n : ℤ)
    (x y : (virasoroVOA c).grading n) :
    β n x y = (Bsimp c).form ((maxIdealVir c).mkQ x) ((maxIdealVir c).mkQ y) := by
  change β n x y = (Bpull c).form x y
  obtain ⟨x, hx⟩ := x
  have hx' : x ∈ gradingVir c n := hx
  revert hx
  induction hx' using Submodule.span_induction with
  | mem z hz =>
      intro hx
      obtain ⟨ws, hen, rfl⟩ := hz
      subst hen
      exact weightForm_word_eq_Bpull β hvac hadj ws y
  | zero =>
      intro hx
      change β n 0 y = (Bpull c).form 0 y
      simp
  | add a b ha hb iha ihb =>
      intro hx
      change β n (⟨a, ha⟩ + ⟨b, hb⟩) y = (Bpull c).form (a + b) y
      rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, iha ha, ihb hb]
  | smul r a ha iha =>
      intro hx
      change β n (r • ⟨a, ha⟩) y = (Bpull c).form (r • a) y
      rw [map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, iha ha]

end VOA.LeeYangShortcut
