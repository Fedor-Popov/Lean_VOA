import VOA.Moonshine.AutVnat
import VOA.Core.AutFromGenerators

/-!
# Naturality of the moonshine extension

A form-preserving twisted-module intertwiner over an automorphism of the untwisted VOA
extends blockwise to an automorphism of `V♮`. Preservation of the canonical untwisted
form and commutation with translation are consequences, not additional hypotheses.
-/

namespace VOA.Moonshine.ConwayNorton.M8

open AutMonster InvForm SkewAdjoint VertexOperatorAlgebra

private theorem lrLift_pow {X : Type*} [AddCommGroup X] [Module ℂ X]
    (f : X ≃ₗ[ℂ] X) (L : Module.End ℂ X) (hf : ∀ x, f (L x) = L (f x))
    (j : ℕ) (x : X) : f ((L ^ j) x) = (L ^ j) (f x) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [pow_succ', Module.End.mul_apply, hf, ih]

/-- Every untwisted automorphism preserves the canonical normalized invariant form. -/
theorem lrLift_leechBV (h : Aut leechVOAPlus) (u v : SkewVP) :
    leechBV (h u) (h v) = leechBV u v := by
  let B : InvariantForm leechVOAPlus :=
    { form := leechBV.compl₁₂ h.toLinearEquiv.toLinearMap h.toLinearEquiv.toLinearMap
      virasoro_adj := by
        intro n a b
        change leechBV (h (leechVOAPlus.L n a)) (h b) =
          leechBV (h a) (h (leechVOAPlus.L (-n) b))
        rw [aut_comm_L, aut_comm_L, leechBVForm.virasoro_adj] }
  have hB : B.IsFullyInvariant := by
    intro wt a ha n b c
    change leechBV (h (leechVOAPlus.smul a n b)) (h c) = _
    rw [h.map_smul]
    have hi := canonicalInvariantForm_isFullyInvariant leechVOAPlus_vacuum_ne_zero
      leechVOAPlus_L1_one wt (h a) (h.map_grading ha) n (h b) (h c)
    change leechBV (leechVOAPlus.smul (h a) n (h b)) (h c) = _ at hi
    rw [hi]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    change _ = _ • leechBV (h b)
      (h (leechVOAPlus.smul ((leechVOAPlus.L 1 ^ j) a) _ c))
    rw [h.map_smul, lrLift_pow h.toLinearEquiv _ (aut_comm_L h 1)]
    rfl
  have hn : B.Normalized := by
    change leechBV (h leechVOAPlus.vacuum) (h leechVOAPlus.vacuum) = 1
    rw [h.map_vacuum, leechBV_normalized]
  exact congrArg (fun F : LinearMap.BilinForm ℂ SkewVP => F u v)
    (invariantForm_unique_FHL leechVOAPlus_vacuum_ne_zero leechVOAPlus_L1_one hB hn)

variable (h : Aut leechVOAPlus) (φ : TP ≃ₗ[ℂ] TP)
    (hφ : ∀ (u : SkewVP) (n : ℤ) (t : TP),
      φ (mode (plusModule.YM u) n t) = mode (plusModule.YM (h u)) n (φ t))

include hφ

/-- Compatibility with the conformal vector gives every twisted Virasoro mode. -/
theorem lrLift_omegaMode (n : ℤ) (t : TP) :
    φ (mode (plusModule.YM leechVOAPlus.conformalVector) n t) =
      mode (plusModule.YM leechVOAPlus.conformalVector) n (φ t) := by
  rw [hφ, h.map_omega]

/-- In particular, the twisted intertwiner commutes with translation. -/
theorem lrLift_leechLTP (t : TP) : φ (leechLTP t) = leechLTP (φ t) :=
  lrLift_omegaMode h φ hφ 0 t

/-- The twisted intertwiner preserves conformal weights. -/
theorem lrLift_weight {w : ℂ} {t : TP} (ht : t ∈ plusModule.weight w) :
    φ t ∈ plusModule.weight w := by
  apply eigenvector_mem_weight
  rw [← lrLift_omegaMode h φ hφ, plusModule.L0_weight w t ht, map_smul]

/-- Naturality of the skew field follows from module compatibility and translation. -/
theorem lrLift_leechWsk (t : TP) (n : ℤ) (u : SkewVP) :
    φ (mode (leechWsk t) n u) = mode (leechWsk (φ t)) n (h u) := by
  rw [mode_leechWsk, mode_leechWsk, AutGen.linearEquiv_finsum]
  apply finsum_congr
  intro i
  rw [map_smul, lrLift_pow φ leechLTP (lrLift_leechLTP h φ hφ), hφ]

variable (hT : ∀ t t' : TP, TPForm (φ t) (φ t') = TPForm t t')

include hT

private theorem lrLift_leechWbar_homogeneous (n : ℤ) {w : ℤ} {t : TP}
    (ht : t ∈ plusModule.weight (w : ℂ)) (a : TP) :
    h (leechWbarMode n t a) = leechWbarMode n (φ t) (φ a) := by
  have hp : ∀ j t, φ ((Lp1 plusModule ^ j) t) = (Lp1 plusModule ^ j) (φ t) :=
    lrLift_pow φ (Lp1 plusModule) (lrLift_omegaMode h φ hφ 2)
  let R := dagBound plusModule w
  have hR : ∀ j : ℕ, R ≤ j → (Lp1 plusModule ^ j) t = 0 :=
    fun j hj => Lp1_pow_eq_zero_of_dagBound plusModule ht hj
  have hRφ : ∀ j : ℕ, R ≤ j → (Lp1 plusModule ^ j) (φ t) = 0 := by
    intro j hj
    rw [← hp, hR j hj, map_zero]
  apply eq_of_form leechBV_orth leechBV_gradedNondeg
  intro v
  obtain ⟨u, rfl⟩ := h.toLinearEquiv.surjective v
  rw [lrLift_leechBV, leechWbar_adj' n ht R hR,
    leechWbar_adj' n (lrLift_weight h φ hφ ht) R hRφ]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← hp, ← lrLift_leechWsk h φ hφ, hT]

/-- Naturality of the adjoint field, using both invariant forms. -/
theorem lrLift_leechWbar (t : TP) (n : ℤ) (a : TP) :
    h (mode (leechWbar t) n a) = mode (leechWbar (φ t)) n (φ a) := by
  rw [mode_leechWbar, mode_leechWbar]
  have ht : t ∈ ⨆ w : ℤ, plusModule.weight (w : ℂ) := by
    rw [iSup_plusModule_weight_int]
    trivial
  induction ht using Submodule.iSup_induction' with
  | mem w t ht => exact lrLift_leechWbar_homogeneous h φ hφ hT n ht a
  | zero =>
    simp only [map_zero, leechWbarMode, WbarMode_zero, LinearMap.zero_apply]
  | add t s _ _ ht hs =>
    simp only [map_add, leechWbarMode_add, LinearMap.add_apply, ht, hs]

/-- A compatible pair gives an automorphism of `V♮`. -/
noncomputable def vnatAutOfPair (h : Aut leechVOAPlus) (φ : TP ≃ₗ[ℂ] TP)
    (hφ : ∀ (u : SkewVP) (n : ℤ) (t : TP),
      φ (mode (plusModule.YM u) n t) = mode (plusModule.YM (h u)) n (φ t))
    (hT : ∀ t t' : TP, TPForm (φ t) (φ t') = TPForm t t') : AutVnat where
  toLinearEquiv := h.toLinearEquiv.prodCongr φ
  map_smul' := by
    intro x n y
    change (h (mode (VnatAxioms.YN x) n y).1,
      φ (mode (VnatAxioms.YN x) n y).2) =
        mode (VnatAxioms.YN (h x.1, φ x.2)) n (h y.1, φ y.2)
    simp only [VnatAxioms.mode_YN, map_add]
    apply Prod.ext
    · change h.toLinearEquiv (leechVOAPlus.smul x.1 n y.1) + _ = _
      rw [h.map_smul, lrLift_leechWbar h φ hφ hT]
      rfl
    · rw [lrLift_leechWsk h φ hφ, hφ]
  map_vacuum := by
    change (h leechVOAPlus.vacuum, φ 0) = (leechVOAPlus.vacuum, 0)
    rw [h.map_vacuum, map_zero]
  map_omega := by
    change (h leechVOAPlus.conformalVector, φ 0) = (leechVOAPlus.conformalVector, 0)
    rw [h.map_omega, map_zero]

@[simp] theorem vnatAutOfPair_apply (u : SkewVP) (t : TP) :
    vnatAutOfPair h φ hφ hT ((u, t) : Vnat) = (h u, φ t) := rfl

end VOA.Moonshine.ConwayNorton.M8
