/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeO5bJacobi

/-! # O5b: the analytic bridge `TwistedJacobiBridge` holds

`twistedJacobiBridge_holds G hfg hC2 : McRaeO5.TwistedJacobiBridge G hfg hC2` for every
VOA `W`, every `G ≤ Aut W` with `W` finitely generated over `C₂`-cofinite `W^G`.

The homogeneous case is `jacobi_homog` (McRae Thm 4.14 / Creutzig–Kanade–McRae Thm 3.65 /
Huang–Kirillov–Lepowsky, in their analytic form: the product, reversed product and iterate of
the action operator on a `g`-twisted summand are three Laurent expansions of one function
holomorphic on `ℂ ∖ {0, 1}`, whose residue theorem is the Jacobi identity). The general case
follows by additivity in `u`, `v` (decomposed along the grading of `W^{⟨g⟩}`, whose homogeneous
components stay `g`-fixed) and in `x` (decomposed along the generalized `L₀`-eigenspaces of `X`,
preserved by `p`).

No `sorry`, no new axioms.
-/

set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.McRaeO5b
open CategoryTheory MonoidalCategory BraidedCategory VOA.LogTensor VOA.LogTensor.LogModuleCat
open VOA.C2Rigid.LocalInjective VOA.Classification.COne.McRaeO3 VOA.Classification.COne.McRaeO5
open VOA.Classification.COne.McRaeO4c

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {G : Subgroup (Aut W)} {hfg : FinGen (orbifold G).adjointRestrict}
  {hC2 : C2Cofinite (orbifoldVOA G)}

section Additivity
variable {X : LogModuleCat (orbifoldVOA G)} (a : tensorObject hC2 (vObj G hfg) X ⟶ X)

theorem actY_add_left' (n : ℂ) (k : ℕ) (w₁ w₂ : V) (y : X) :
    (actY hC2 a).1 n k (w₁ + w₂) y = (actY hC2 a).1 n k w₁ y + (actY hC2 a).1 n k w₂ y :=
  LinearMap.congr_fun (map_add ((actY hC2 a).1 n k) w₁ w₂) y

/-- The Jacobi identity for fixed inputs and indices. -/
def JacEq (u v : V) (y : X) (ℓ m n : ℤ) : Prop :=
  ∑ᶠ i : ℤ, famL a u v y ℓ m n i = ∑ᶠ i : ℤ, famR a u v y ℓ m n i

theorem famL_add_y (u v : V) (y₁ y₂ : X) (ℓ m n i : ℤ) :
    famL a u v (y₁ + y₂) ℓ m n i = famL a u v y₁ ℓ m n i + famL a u v y₂ ℓ m n i := by
  simp only [famL, map_add]
  module

theorem famR_add_y (u v : V) (y₁ y₂ : X) (ℓ m n i : ℤ) :
    famR a u v (y₁ + y₂) ℓ m n i = famR a u v y₁ ℓ m n i + famR a u v y₂ ℓ m n i := by
  simp only [famR, map_add, smul_add]

theorem famL_add_u (u₁ u₂ v : V) (y : X) (ℓ m n i : ℤ) :
    famL a (u₁ + u₂) v y ℓ m n i = famL a u₁ v y ℓ m n i + famL a u₂ v y ℓ m n i := by
  simp only [famL, actY_add_left', map_add]
  module

theorem famR_add_u (u₁ u₂ v : V) (y : X) (ℓ m n i : ℤ) :
    famR a (u₁ + u₂) v y ℓ m n i = famR a u₁ v y ℓ m n i + famR a u₂ v y ℓ m n i := by
  simp only [famR, PreVertexAlgebra.smul_add_left, actY_add_left', smul_add]

theorem famL_add_v (u v₁ v₂ : V) (y : X) (ℓ m n i : ℤ) :
    famL a u (v₁ + v₂) y ℓ m n i = famL a u v₁ y ℓ m n i + famL a u v₂ y ℓ m n i := by
  simp only [famL, actY_add_left', map_add]
  module

theorem famR_add_v (u v₁ v₂ : V) (y : X) (ℓ m n i : ℤ) :
    famR a u (v₁ + v₂) y ℓ m n i = famR a u v₁ y ℓ m n i + famR a u v₂ y ℓ m n i := by
  simp only [famR, PreVertexAlgebra.smul_add_right, actY_add_left', smul_add]

theorem jacEq_add_y {u v : V} {y₁ y₂ : X} {ℓ m n : ℤ} (h₁ : JacEq a u v y₁ ℓ m n)
    (h₂ : JacEq a u v y₂ ℓ m n) : JacEq a u v (y₁ + y₂) ℓ m n := by
  unfold JacEq at *
  rw [finsum_congr (famL_add_y a u v y₁ y₂ ℓ m n), finsum_congr (famR_add_y a u v y₁ y₂ ℓ m n),
    finsum_add_distrib (famL_fin a u v y₁ ℓ m n) (famL_fin a u v y₂ ℓ m n),
    finsum_add_distrib (famR_fin a u v y₁ ℓ m n) (famR_fin a u v y₂ ℓ m n), h₁, h₂]

theorem jacEq_add_u {u₁ u₂ v : V} {y : X} {ℓ m n : ℤ} (h₁ : JacEq a u₁ v y ℓ m n)
    (h₂ : JacEq a u₂ v y ℓ m n) : JacEq a (u₁ + u₂) v y ℓ m n := by
  unfold JacEq at *
  rw [finsum_congr (famL_add_u a u₁ u₂ v y ℓ m n), finsum_congr (famR_add_u a u₁ u₂ v y ℓ m n),
    finsum_add_distrib (famL_fin a u₁ v y ℓ m n) (famL_fin a u₂ v y ℓ m n),
    finsum_add_distrib (famR_fin a u₁ v y ℓ m n) (famR_fin a u₂ v y ℓ m n), h₁, h₂]

theorem jacEq_add_v {u v₁ v₂ : V} {y : X} {ℓ m n : ℤ} (h₁ : JacEq a u v₁ y ℓ m n)
    (h₂ : JacEq a u v₂ y ℓ m n) : JacEq a u (v₁ + v₂) y ℓ m n := by
  unfold JacEq at *
  rw [finsum_congr (famL_add_v a u v₁ v₂ y ℓ m n), finsum_congr (famR_add_v a u v₁ v₂ y ℓ m n),
    finsum_add_distrib (famL_fin a u v₁ y ℓ m n) (famL_fin a u v₂ y ℓ m n),
    finsum_add_distrib (famR_fin a u v₁ y ℓ m n) (famR_fin a u v₂ y ℓ m n), h₁, h₂]

theorem jacEq_zero_y (u v : V) (ℓ m n : ℤ) : JacEq a u v (0 : X) ℓ m n := by
  unfold JacEq
  rw [finsum_eq_zero_of_forall_eq_zero fun i => ?_, finsum_eq_zero_of_forall_eq_zero fun i => ?_]
  · simp only [famR, map_zero, smul_zero]
  · simp only [famL, map_zero, smul_zero, sub_zero]

theorem jacEq_zero_u (v : V) (y : X) (ℓ m n : ℤ) : JacEq a (0 : V) v y ℓ m n := by
  unfold JacEq
  rw [finsum_eq_zero_of_forall_eq_zero fun i => ?_, finsum_eq_zero_of_forall_eq_zero fun i => ?_]
  · simp only [famR, PreVertexAlgebra.smul_zero_left, actY_zero_left, smul_zero]
  · simp only [famL, actY_zero_left, map_zero, smul_zero, sub_zero]

theorem jacEq_zero_v (u : V) (y : X) (ℓ m n : ℤ) : JacEq a u (0 : V) y ℓ m n := by
  unfold JacEq
  rw [finsum_eq_zero_of_forall_eq_zero fun i => ?_, finsum_eq_zero_of_forall_eq_zero fun i => ?_]
  · simp only [famR, PreVertexAlgebra.smul_zero_right, actY_zero_left, smul_zero]
  · simp only [famL, actY_zero_left, map_zero, smul_zero, sub_zero]

end Additivity

/-! ## The general case -/

section General
variable {X : LogModuleCat (orbifoldVOA G)} {a : tensorObject hC2 (vObj G hfg) X ⟶ X}
  {p : X ⟶ X} {g : Aut W}

/-- Module endomorphisms preserve the generalized `L₀`-eigenspaces. -/
theorem hom_mem_weight (q : X ⟶ X) {c : ℂ} {x : X} (hx : x ∈ X.act.weight c) :
    q.1 x ∈ X.act.weight c := by
  obtain ⟨k, hk⟩ := X.act.L0op_locNilpotent hx
  refine X.act.maxGenEigenspace_le_weight c ((Module.End.mem_maxGenEigenspace _ _ _).mpr ⟨k, ?_⟩)
  rw [← hom_L0_pow q c k x, hk, map_zero]

/-- The homogeneous `g`-fixed vectors of `W^{⟨g⟩}` have integral weight in `V`. -/
theorem mem_weight_of_gradingS {n : ℤ} {w : (orbifold (Subgroup.zpowers g)).carrier}
    (hw : w ∈ (orbifold (Subgroup.zpowers g)).gradingS n) :
    (w : V) ∈ (vObj G hfg).act.weight (n : ℂ) := by
  change (w : V) ∈ adjWeight W (n : ℂ)
  rw [adjWeight_cast]
  exact hw

theorem jacEq_homog_uv (hX : letI := logarithmicMonoidalCategory hC2
      IsLeftModule (mulHom G hfg hC2) (unitHom G hfg) a)
    (hT : TwistFacts a p g) {A B : ℤ} {u v : V}
    (hu : u ∈ (vObj G hfg).act.weight (A : ℂ)) (hv : v ∈ (vObj G hfg).act.weight (B : ℂ))
    (hgu : g u = u) (hgv : g v = v) (x : X) (ℓ m n : ℤ) : JacEq a u v (p.1 x) ℓ m n := by
  have hx : x ∈ ⨆ c, X.act.weight c := by
    rw [X.act.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  induction hx using Submodule.iSup_induction' with
  | mem c x hxc => exact jacobi_homog hX hT hu hv hgu hgv x (hom_mem_weight p hxc) ℓ m n
  | zero => rw [map_zero]; exact jacEq_zero_y a u v ℓ m n
  | add x y _ _ hx hy => rw [map_add]; exact jacEq_add_y a hx hy

/-- **The Jacobi identity on a `g`-twisted summand, for all `g`-fixed `u, v`.** -/
theorem jacobi_twisted (hX : letI := logarithmicMonoidalCategory hC2
      IsLeftModule (mulHom G hfg hC2) (unitHom G hfg) a)
    (hT : TwistFacts a p g) (u v : V) (hgu : g u = u) (hgv : g v = v) (x : X) (ℓ m n : ℤ) :
    JacEq a u v (p.1 x) ℓ m n := by
  set S := orbifold (Subgroup.zpowers g) with hS
  have hmem : ∀ w : S.carrier, w ∈ ⨆ k, S.gradingS k := fun w => by
    rw [S.gradingS_isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  -- reduce `v` to homogeneous components, then `u`
  have hv' : ∀ v' : S.carrier, ∀ u' : S.carrier,
      (∃ A : ℤ, (u' : V) ∈ (vObj G hfg).act.weight (A : ℂ)) →
        JacEq a (u' : V) (v' : V) (p.1 x) ℓ m n := by
    intro v'
    induction hmem v' using Submodule.iSup_induction' with
    | mem k w hw =>
        rintro u' ⟨A, hA⟩
        exact jacEq_homog_uv hX hT hA (mem_weight_of_gradingS hw) (fixed_of_mem u'.2)
          (fixed_of_mem w.2) x ℓ m n
    | zero => intro u' _; exact jacEq_zero_v a _ _ ℓ m n
    | add w₁ w₂ _ _ h₁ h₂ =>
        intro u' hu'
        rw [Submodule.coe_add]
        exact jacEq_add_v a (h₁ u' hu') (h₂ u' hu')
  have hu' : ∀ u' v' : S.carrier, JacEq a (u' : V) (v' : V) (p.1 x) ℓ m n := by
    intro u'
    induction hmem u' using Submodule.iSup_induction' with
    | mem k w hw => exact fun v' => hv' v' w ⟨k, mem_weight_of_gradingS hw⟩
    | zero => intro v'; exact jacEq_zero_u a _ _ ℓ m n
    | add w₁ w₂ _ _ h₁ h₂ =>
        intro v'
        rw [Submodule.coe_add]
        exact jacEq_add_u a (h₁ v') (h₂ v')
  exact hu' ⟨u, (mem_orbifold_zpowers_iff g u).mpr hgu⟩ ⟨v, (mem_orbifold_zpowers_iff g v).mpr hgv⟩

end General

/-- **O5 (b), the analytic bridge.** -/
theorem twistedJacobiBridge_holds (G : Subgroup (Aut W)) (hfg : FinGen (orbifold G).adjointRestrict)
    (hC2 : C2Cofinite (orbifoldVOA G)) : TwistedJacobiBridge G hfg hC2 := by
  intro X a hX g p hmod htw u v hu hv x ℓ m n
  exact jacobi_twisted hX (twistFacts_of G hfg hC2 a g p hmod htw) u v hu hv x ℓ m n

end VOA.Classification.COne.McRaeO5b
