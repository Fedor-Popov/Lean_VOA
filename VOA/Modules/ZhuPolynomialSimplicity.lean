/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.OrdSubmodule
import VOA.Modules.ZhuRingInstance
import VOA.Core.SimpleImage

/-!
# A Zhu-polynomial simplicity criterion

Let `W` be a positive-energy integrally graded VOA with `W₀ = ℂ·1` (part of the repository's
`VertexOperatorAlgebra` structure) and `W₁ = 0`.  Every nonzero proper ideal has a least occupied
integral weight `n`; its least-weight space is a lowest-weight `W`-module bottom.  Zhu's algebra
therefore acts on it, and `[omega]` acts by the scalar `n`.  Consequently, if a polynomial relation
`P([omega]) = 0` in `A(W)` has no nonnegative integral roots except `0` and `1`, no such ideal can
exist: weight `0` would contain the vacuum and weight `1` is zero.

This is the reusable representation-theoretic recognition theorem needed by the lattice triplet.
It does not assert any polynomial relation for an example; that finite Zhu-algebra calculation is
the exact remaining example-specific input.
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱}

namespace VertexOperatorAlgebra

/-- An ideal, viewed as a weak submodule of the adjoint module. -/
noncomputable def idealWeakSubmodule (W : VertexOperatorAlgebra 𝒱)
    (I : Submodule ℂ 𝒱) (hI : W.IsIdeal I) :
    WeakModule.Submodule' (adjointModule W).toWeakModule where
  carrier := I
  act_mem := fun u n _ hx => hI u _ n hx

@[simp] theorem idealWeakSubmodule_carrier (W : VertexOperatorAlgebra 𝒱)
    (I : Submodule ℂ 𝒱) (hI : W.IsIdeal I) :
    (idealWeakSubmodule W I hI).carrier = I := rfl

/-- An ideal as an ordinary module on its subtype. -/
noncomputable def idealOrdModule (W : VertexOperatorAlgebra 𝒱)
    (I : Submodule ℂ 𝒱) (hI : W.IsIdeal I) : OrdVModule W I :=
  OrdVModule.submodule (adjointModule W) (idealWeakSubmodule W I hI)

@[simp] theorem idealOrdModule_weight_int (W : VertexOperatorAlgebra 𝒱)
    (I : Submodule ℂ 𝒱) (hI : W.IsIdeal I) (n : ℤ) :
    (idealOrdModule W I hI).weight (n : ℂ) = (W.grading n).comap I.subtype := by
  change (adjWeight W (n : ℂ)).comap I.subtype = _
  rw [adjWeight_cast]

@[simp] theorem idealOrdModule_act_coe (W : VertexOperatorAlgebra 𝒱)
    (I : Submodule ℂ 𝒱) (hI : W.IsIdeal I) (u : 𝒱) (n : ℤ) (x : I) :
    (((idealOrdModule W I hI).act u n x : I) : 𝒱) = W.smul u n (x : 𝒱) := rfl

/-- A nonzero ideal occupies some nonnegative integral conformal weight. -/
theorem exists_nat_weight_ne_bot_of_ideal_ne_bot (hI : W.IsIdeal I) (hne : I ≠ ⊥) :
    ∃ n : ℕ, (idealOrdModule W I hI).weight (n : ℂ) ≠ ⊥ := by
  have hgr := QuotVOA.isGradedIdeal_of_isIdeal hI
  have hex : ∃ n : ℤ, I ⊓ W.grading n ≠ ⊥ := by
    by_contra h
    push_neg at h
    apply hne
    rw [hgr]
    exact iSup_eq_bot.mpr h
  obtain ⟨n, hn⟩ := hex
  have hn0 : 0 ≤ n := by
    by_contra hneg
    apply hn
    rw [W.positivity n (not_le.mp hneg), inf_bot_eq]
  refine ⟨n.toNat, ?_⟩
  have hcast : ((n.toNat : ℕ) : ℂ) = (n : ℂ) := by
    exact_mod_cast (Int.toNat_of_nonneg hn0)
  change (adjWeight W ((n.toNat : ℕ) : ℂ)).comap I.subtype ≠ ⊥
  rw [hcast, adjWeight_cast]
  intro hbot
  apply hn
  rw [eq_bot_iff]
  intro x hx
  have hx' : (⟨x, hx.1⟩ : I) ∈ (W.grading n).comap I.subtype := hx.2
  rw [hbot, Submodule.mem_bot] at hx'
  rw [Submodule.mem_bot]
  exact congrArg Subtype.val hx'

/-- The least occupied weight of a nonzero ideal. -/
noncomputable def idealBottomWeight (hI : W.IsIdeal I) (hne : I ≠ ⊥) : ℕ :=
  Nat.find (exists_nat_weight_ne_bot_of_ideal_ne_bot hI hne)

theorem idealBottomWeight_ne_bot (hI : W.IsIdeal I) (hne : I ≠ ⊥) :
    (idealOrdModule W I hI).weight (idealBottomWeight hI hne : ℂ) ≠ ⊥ :=
  Nat.find_spec (exists_nat_weight_ne_bot_of_ideal_ne_bot hI hne)

theorem idealBottomWeight_min (hI : W.IsIdeal I) (hne : I ≠ ⊥) {m : ℕ}
    (hm : (idealOrdModule W I hI).weight (m : ℂ) ≠ ⊥) :
    idealBottomWeight hI hne ≤ m :=
  Nat.find_min' (exists_nat_weight_ne_bot_of_ideal_ne_bot hI hne) hm

/-- The ideal subtype has lowest weight equal to its least occupied integral grade. -/
theorem idealOrdModule_isLowestWeight (hI : W.IsIdeal I) (hne : I ≠ ⊥) :
    IsLowestWeight (idealOrdModule W I hI) (idealBottomWeight hI hne : ℂ) := by
  intro a ha
  have ha' : (adjointModule W).weight a ≠ ⊥ := by
    intro hbot
    apply ha
    change ((adjointModule W).weight a).comap I.subtype = ⊥
    rw [hbot, Submodule.comap_bot]
    exact LinearMap.ker_eq_bot.mpr I.subtype_injective
  by_cases hex : ∃ m : ℤ, (m : ℂ) = a
  · obtain ⟨m, rfl⟩ := hex
    have hm0 : 0 ≤ m := by
      by_contra hneg
      apply ha'
      change adjWeight W (m : ℂ) = ⊥
      rw [adjWeight_cast, W.positivity m (not_le.mp hneg)]
    let mn : ℕ := m.toNat
    have hmcast : ((mn : ℕ) : ℤ) = m := by dsimp [mn]; omega
    have hmcastC : (mn : ℂ) = (m : ℂ) := by exact_mod_cast hmcast
    have hm : (idealOrdModule W I hI).weight (mn : ℂ) ≠ ⊥ := by
      rw [hmcastC]
      exact ha
    have hle := idealBottomWeight_min hI hne hm
    refine ⟨mn - idealBottomWeight hI hne, ?_⟩
    calc
      (m : ℂ) = (mn : ℂ) := hmcastC.symm
      _ = (idealBottomWeight hI hne : ℂ) +
          (mn - idealBottomWeight hI hne : ℕ) := by
        rw [Nat.cast_sub hle]
        ring
  · exact absurd (adjWeight_eq_bot W (fun m hm => hex ⟨m, hm⟩)) ha'

/-- A proper ideal cannot have bottom weight zero: its degree-zero line is the vacuum line. -/
theorem idealBottomWeight_ne_zero (hI : W.IsIdeal I) (hne : I ≠ ⊥)
    (hvac : W.vacuum ∉ I) : idealBottomWeight hI hne ≠ 0 := by
  intro hn
  have hbot := idealBottomWeight_ne_bot hI hne
  rw [hn] at hbot
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hbot
  have hxgr : (x : 𝒱) ∈ W.grading 0 := by
    have hx' : x ∈ (W.grading (0 : ℤ)).comap I.subtype := by
      rw [← idealOrdModule_weight_int W I hI 0]
      simpa using hx
    exact hx'
  rw [W.vacuum_grade, Submodule.mem_span_singleton] at hxgr
  obtain ⟨c, hc⟩ := hxgr
  have hc0 : c ≠ 0 := by
    intro hc'
    apply hx0
    apply Subtype.ext
    rw [← hc, hc', zero_smul]
    simp
  apply hvac
  have hxI : (x : 𝒱) ∈ I := x.property
  have := I.smul_mem c⁻¹ hxI
  have heq : c⁻¹ • (x : 𝒱) = W.vacuum := by
    rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rwa [heq] at this

/-- If `W₁ = 0`, the bottom weight of a nonzero ideal cannot be one. -/
theorem idealBottomWeight_ne_one (hI : W.IsIdeal I) (hne : I ≠ ⊥)
    (hV1 : W.grading 1 = ⊥) : idealBottomWeight hI hne ≠ 1 := by
  intro hn
  have hbot := idealBottomWeight_ne_bot hI hne
  rw [hn] at hbot
  have hbot' : (W.grading (1 : ℤ)).comap I.subtype ≠ ⊥ := by
    rw [← idealOrdModule_weight_int W I hI 1]
    simpa using hbot
  rw [hV1] at hbot'
  apply hbot'
  rw [Submodule.comap_bot]
  exact LinearMap.ker_eq_bot.mpr I.subtype_injective

end VertexOperatorAlgebra

/-! ## Polynomial action on an ideal bottom -/

namespace ZhuPolynomialSimplicity

variable (W)

/-- A polynomial relation for the conformal class `[omega]` in Zhu's algebra.  Packaging the
local ring instances in a predicate keeps the public simplicity theorem easy to instantiate. -/
def ZhuPolynomialRelation (P : Polynomial ℂ) : Prop :=
  letI := instRingA W
  letI := instAlgebraA W
  Polynomial.aeval (mk W W.conformalVector) P = 0

/-- On the least-weight space of an ideal, `[omega]` acts by the least weight. -/
theorem omega_acts_by_bottom (I : Submodule ℂ 𝒱) (hI : W.IsIdeal I) (hne : I ≠ ⊥)
    (x : (W.idealOrdModule I hI).weight (W.idealBottomWeight hI hne : ℂ)) :
    actA (W.idealOrdModule I hI) (W.idealOrdModule_isLowestWeight hI hne)
        (mk W W.conformalVector) x = (W.idealBottomWeight hI hne : ℂ) • x := by
  apply Subtype.ext
  rw [actA_mk_apply_coe, oMod_homogeneous _ W.conformalVector_mem_grading_two]
  exact (W.idealOrdModule I hI).L0_weight _ _ x.property

/-- The Zhu action on a lowest-weight space as a complex-algebra homomorphism.  The underlying
ring hom is `actARingHom`; complex-linearity is inherited from the linear map `actA`. -/
noncomputable def actAAlgHom {Mod : Type u} [AddCommGroup Mod] [Module ℂ Mod]
    (N : OrdVModule W Mod) {h : ℂ} (hcw : IsLowestWeight N h) :
    letI := instRingA W
    letI := instAlgebraA W
    A W →ₐ[ℂ] End ℂ (N.weight h) := by
  letI : Ring (A W) := instRingA W
  letI : Algebra ℂ (A W) := instAlgebraA W
  exact
    { toRingHom := actARingHom (zhuRingData_holds W) hcw
      commutes' := fun c => by
        change actA N hcw (c • mk W W.vacuum) = c • (1 : End ℂ (N.weight h))
        rw [map_smul, show mk W W.vacuum = one W from rfl, actA_one] }

/-- **Zhu-polynomial simplicity criterion.**  If `W₁ = 0` and a polynomial annihilating
`[omega] ∈ A(W)` has no nonnegative integral roots other than `0` and `1`, then every ideal is
zero or the whole VOA.  The separate `top ≠ bot` hypothesis excludes the zero VOA.

For an example, the only representation-theoretic input is `ZhuPolynomialRelation W P`; all
least-weight, Zhu-action, and ideal arguments are discharged here. -/
theorem isSimple_of_zhuPolynomial
    (hneW : (⊤ : Submodule ℂ 𝒱) ≠ ⊥)
    (hV1 : W.grading 1 = ⊥)
    (P : Polynomial ℂ)
    (hpoly : ZhuPolynomialRelation W P)
    (hroots : ∀ n : ℕ, P.eval (n : ℂ) = 0 → n = 0 ∨ n = 1) :
    W.IsSimple := by
  classical
  refine ⟨hneW, fun I hI => ?_⟩
  by_cases hne : I = ⊥
  · exact Or.inl hne
  by_cases htop : I = ⊤
  · exact Or.inr htop
  exfalso
  have hvac : W.vacuum ∉ I := fun hv => htop (QuotVOA.eq_top_of_vacuum_mem hI hv)
  let N : OrdVModule W I := W.idealOrdModule I hI
  let n : ℕ := W.idealBottomWeight hI hne
  have hcw : IsLowestWeight N (n : ℂ) := W.idealOrdModule_isLowestWeight hI hne
  have hspace : N.weight (n : ℂ) ≠ ⊥ := W.idealBottomWeight_ne_bot hI hne
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hspace
  let xb : N.weight (n : ℂ) := ⟨x, hx⟩
  have hxb0 : xb ≠ 0 := by
    intro h
    apply hx0
    exact congrArg Subtype.val h
  letI : Ring (A W) := instRingA W
  letI : Algebra ℂ (A W) := instAlgebraA W
  let rho : A W →ₐ[ℂ] End ℂ (N.weight (n : ℂ)) :=
    actAAlgHom W N hcw
  have homega : rho (mk W W.conformalVector) xb = (n : ℂ) • xb := by
    change actA N hcw (mk W W.conformalVector) xb = (n : ℂ) • xb
    exact omega_acts_by_bottom W I hI hne xb
  have hpoly' : Polynomial.aeval (mk W W.conformalVector) P = 0 := hpoly
  have hpEnd : Polynomial.aeval (rho (mk W W.conformalVector)) P = 0 := by
    calc
      Polynomial.aeval (rho (mk W W.conformalVector)) P =
          rho (Polynomial.aeval (mk W W.conformalVector) P) :=
        Polynomial.aeval_algHom_apply rho (mk W W.conformalVector) P
      _ = 0 := by rw [hpoly']; exact map_zero rho
  have happ : Polynomial.aeval (rho (mk W W.conformalVector)) P xb = 0 := by
    rw [hpEnd, LinearMap.zero_apply]
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul homega] at happ
  have hroot : P.eval (n : ℂ) = 0 := (smul_eq_zero.mp happ).resolve_right hxb0
  rcases hroots n hroot with hn | hn
  · exact (W.idealBottomWeight_ne_zero hI hne hvac) hn
  · exact (W.idealBottomWeight_ne_one hI hne hV1) hn

end ZhuPolynomialSimplicity

end VOA

#print axioms VOA.VertexOperatorAlgebra.idealOrdModule_isLowestWeight
#print axioms VOA.ZhuPolynomialSimplicity.omega_acts_by_bottom
#print axioms VOA.ZhuPolynomialSimplicity.isSimple_of_zhuPolynomial
