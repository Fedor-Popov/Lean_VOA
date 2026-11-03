/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2HorizontalReflection
import VOA.Examples.AffineSl2ParabolicModule

/-! # The exact horizontal Verma presentation of the actual parabolic module -/
namespace VOA.AffineVOA.HighestModule
open UniversalEnvelopingAlgebra
noncomputable section

/-- The full enveloping action of the actual quotient representation is left
multiplication, by the universal property of the enveloping algebra. -/
theorem lift_rho_eq_lsmul (k h : ℂ) :
    lift ℂ (rho k h) = Algebra.lsmul ℂ ℂ (Verma k h) := by
  exact ((UniversalEnvelopingAlgebra.lift_unique ℂ (rho k h)
    (Algebra.lsmul ℂ ℂ (Verma k h))).mp rfl).symm

/-- Horizontal words are literal powers of F0 in the quotient. -/
theorem horizontalState_eq_mk_power (k h : ℂ) (r : ℕ) :
    horizontalState k h r = (Submodule.Quotient.mk ((ι ℂ (modeElement 1 0))^r) : Verma k h) := by
  induction r with
  | zero => simp [horizontalState_zero,highestVector]
  | succ r ih =>
    rw [horizontalState_succ,ih]
    change rho k h (modeElement 1 0) _ = _
    rw [rho_mk,pow_succ']

/-- The reflection map acts by right multiplication by the literal horizontal
relation on enveloping representatives. -/
theorem horizontalReflection_mk (k : ℂ) (d : ℕ) (u : U) :
    horizontalReflection k d (Submodule.Quotient.mk u) =
      (Submodule.Quotient.mk (u * parabolicRelation d) : Verma k d) := by
  rw [horizontalReflection,universalMap_mk]
  unfold evaluate
  simp only [LinearMap.coe_mk,AddHom.coe_mk]
  rw [lift_rho_eq_lsmul,horizontalState_eq_mk_power]
  rfl

/-- The actual projection imposing the finite horizontal relation. -/
def parabolicProjection (k : ℂ) (d : ℕ) : Verma k d →ₗ[ℂ] Parabolic k d :=
  ((highestIdeal k (d : ℂ)).mapQ (parabolicIdeal k d) (LinearMap.id : U →ₗ[U] U)
    (by simpa using highestIdeal_le_parabolicIdeal k d)).restrictScalars ℂ

@[simp] theorem parabolicProjection_mk (k : ℂ) (d : ℕ) (u : U) :
    parabolicProjection k d (Submodule.Quotient.mk u) = Submodule.Quotient.mk u := rfl

theorem parabolicProjection_surjective (k : ℂ) (d : ℕ) :
    Function.Surjective (parabolicProjection k d) := by
  intro x
  obtain ⟨u,rfl⟩ := Submodule.Quotient.mk_surjective (parabolicIdeal k d) x
  exact ⟨Submodule.Quotient.mk u,rfl⟩

/-- Exactness is an equality of the actual reflection image and the actual
parabolic projection kernel, not a dimension or character assumption. -/
theorem horizontalReflection_range_eq_kernel (k : ℂ) (d : ℕ) :
    LinearMap.range (horizontalReflection k d) = LinearMap.ker (parabolicProjection k d) := by
  apply le_antisymm
  · rintro x ⟨v,rfl⟩
    obtain ⟨u,rfl⟩ := Submodule.Quotient.mk_surjective (highestIdeal k (-(d : ℂ)-2)) v
    rw [LinearMap.mem_ker,horizontalReflection_mk,parabolicProjection_mk,
      Submodule.Quotient.mk_eq_zero]
    apply (show Submodule.span U {parabolicRelation d} ≤ parabolicIdeal k d from le_sup_right)
    exact Submodule.mem_span_singleton.mpr ⟨u,rfl⟩
  · intro x hx
    obtain ⟨u,rfl⟩ := Submodule.Quotient.mk_surjective (highestIdeal k (d : ℂ)) x
    rw [LinearMap.mem_ker,parabolicProjection_mk,Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hb
    refine ⟨Submodule.Quotient.mk c, ?_⟩
    rw [horizontalReflection_mk]
    change (Submodule.Quotient.mk (c • parabolicRelation d) : Verma k d) = _
    rw [hc,← hab,Submodule.Quotient.mk_add,
      (Submodule.Quotient.mk_eq_zero _).mpr ha,zero_add]

end
end VOA.AffineVOA.HighestModule
