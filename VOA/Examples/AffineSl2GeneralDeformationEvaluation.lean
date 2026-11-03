/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2GeneralRigidityBasis
import VOA.Examples.AffineSl2DeformationRepresentation

/-!
# Actual lifted vacuum evaluation at arbitrary nonzero noncritical level

Regular graded deformations yield genuine fixed-level affine representations.
Universal evaluation preserves the quotient projection and energy, and its
cyclic image cannot contain the pure tangent vacuum. No singular relation or
admissibility assumption is needed for this construction.
-/
namespace VOA.AffineSl2GeneralRigidity
open AffineVOA AffineVOA.Inst AffineLie Deform Sl2Whitehead LQ43
variable (k : ℂ) (hk : k + 2 ≠ 0) (hk0 : k ≠ 0)
local notation "I" => QuotVOA.maxGradedIdeal (universal k hk)

/-- Embed the concrete coordinate sl₂, ordered (e,f,h), into the actual
weight-one space, whose proved basis is ordered (e,h,f). -/
noncomputable def affineCurrent : Sl2 →ₗ[ℂ] (simple k hk).grading 1 where
  toFun x := x 0 • (simple_weightOneBasis k hk hk0) 0 + x 1 • (simple_weightOneBasis k hk hk0) 2 +
    x 2 • (simple_weightOneBasis k hk hk0) 1
  map_add' x y := by simp only [Pi.add_apply, add_smul]; abel
  map_smul' r x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, smul_smul]

/-- The embedding preserves the Lie bracket. This verifies all current
combinations by bilinearity and the explicit sl₂ triple, including its signs. -/
theorem affineCurrent_lie (x y : Sl2) :
    (affineCurrent k hk hk0) ⁅x, y⁆ = ⁅(affineCurrent k hk hk0) x, (affineCurrent k hk hk0) y⁆ := by
  change (⁅x, y⁆ 0) • (simple_weightOneBasis k hk hk0) 0 + (⁅x, y⁆ 1) • (simple_weightOneBasis k hk hk0) 2 +
    (⁅x, y⁆ 2) • (simple_weightOneBasis k hk hk0) 1 =
    ⁅x 0 • (simple_weightOneBasis k hk hk0) 0 + x 1 • (simple_weightOneBasis k hk hk0) 2 + x 2 • (simple_weightOneBasis k hk hk0) 1,
      y 0 • (simple_weightOneBasis k hk hk0) 0 + y 1 • (simple_weightOneBasis k hk hk0) 2 + y 2 • (simple_weightOneBasis k hk hk0) 1⁆
  simp only [bracket_apply, Fin.sum_univ_three, fabc,
    add_lie, lie_add, smul_lie, lie_smul, lie_self,
    br_he (simple_weightOneBasis k hk hk0) (simple_weightOneTriple k hk hk0),
    br_hf (simple_weightOneBasis k hk hk0) (simple_weightOneTriple k hk hk0),
    br_ef (simple_weightOneBasis k hk hk0) (simple_weightOneTriple k hk hk0),
    br_eh (simple_weightOneBasis k hk hk0) (simple_weightOneTriple k hk hk0),
    br_fh (simple_weightOneBasis k hk hk0) (simple_weightOneTriple k hk hk0),
    br_fe (simple_weightOneBasis k hk hk0) (simple_weightOneTriple k hk hk0)]
  module

/-- The first positive product has the exact original level k and normalized
Killing form. The proof checks it on the already independent quotient currents. -/
theorem affineCurrent_pole (x y : Sl2) :
    (simple k hk).smul ((affineCurrent k hk hk0) x) 1 ((affineCurrent k hk hk0) y) =
      (k * kappaForm x y) • (simple k hk).vacuum := by
  change (simple k hk).smul
    (x 0 • ((simple_weightOneBasis k hk hk0) 0 : _) + x 1 • ((simple_weightOneBasis k hk hk0) 2 : _) +
      x 2 • ((simple_weightOneBasis k hk hk0) 1 : _)) 1
    (y 0 • ((simple_weightOneBasis k hk hk0) 0 : _) + y 1 • ((simple_weightOneBasis k hk hk0) 2 : _) +
      y 2 • ((simple_weightOneBasis k hk hk0) 1 : _)) = _
  simp only [(simple_weightOneBasis_apply k hk hk0)]
  simp only [PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_right,
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right]
  simp only [(quotientCurrent_pole k hk)]
  simp only [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
    show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
    and_false, and_true, or_false, false_or,
    ite_true, ite_false, kappaForm_apply, Fin.sum_univ_three, kappa]
  module

/-- A regular graded deformation of the actual simple affine algebra produces
an affine current representation on its first-order state space at the same level. -/
noncomputable def simple_deformationCurrentData (D : FirstOrderDeformation (simple k hk))
    (hD : D.IsGraded) (hreg : D.Regular) :
    AffineCurrentData k
      ((AffineVOA.WakModule k ⧸ QuotVOA.maxGradedIdeal (universal k hk)) ×
       (AffineVOA.WakModule k ⧸ QuotVOA.maxGradedIdeal (universal k hk))) :=
  regularDeformationCurrentData D hD hreg (((simple k hk).grading 1).subtype.comp (affineCurrent k hk hk0))
    (fun x => ((affineCurrent k hk hk0) x).property)
    (fun x y => congrArg (fun v : (simple k hk).grading 1 => (v : WakModule k ⧸
      QuotVOA.maxGradedIdeal (universal k hk))) ((affineCurrent_lie k hk hk0) x y).symm)
    (affineCurrent_pole k hk hk0)

/-- The current embedding agrees with the original quotient on each of the
three colour basis vectors; this fixes the change of basis order explicitly. -/
theorem affineCurrent_basis (a : Fin 3) :
    ((affineCurrent k hk hk0) (basis a) : WakModule k ⧸ I) =
      (I).mkQ (currentState k a) := by
  fin_cases a <;> simp [affineCurrent, basis, (simple_weightOneBasis_apply k hk hk0)] <;> rfl

/-- Evaluate a universal vacuum state by its lifted currents acting on the pure
vacuum. This is an actual map into the first-order extension, constructed from D. -/
noncomputable def simple_deformationEval (D : FirstOrderDeformation (simple k hk))
    (hD : D.IsGraded) (hreg : D.Regular) :
    WakModule k →ₗ[ℂ] ((WakModule k ⧸ I) × (WakModule k ⧸ I)) :=
  ((simple_deformationCurrentData k hk hk0) D hD hreg).toVacuumCurrentRealization.eval

/-- Universal evaluation sends the vacuum to its pure lift, with no correction. -/
theorem simple_deformationEval_vacuum (D : FirstOrderDeformation (simple k hk))
    (hD : D.IsGraded) (hreg : D.Regular) :
    (simple_deformationEval k hk hk0) D hD hreg (vacuumA k) = ((simple k hk).vacuum, 0) := by
  exact ((simple_deformationCurrentData k hk hk0) D hD hreg).toVacuumCurrentRealization.eval_vacuum

/-- Universal evaluation intertwines every current mode, including negative,
zero and positive modes, with the explicit first-order lifted operator. -/
theorem simple_deformationEval_J (D : FirstOrderDeformation (simple k hk))
    (hD : D.IsGraded) (hreg : D.Regular) (a : Fin 3) (n : ℤ) (v : WakModule k) :
    (simple_deformationEval k hk hk0) D hD hreg (J k a n v) =
      liftedMode D ((I).mkQ (currentState k a)) n ((simple_deformationEval k hk hk0) D hD hreg v) := by
  unfold simple_deformationEval
  rw [VacuumCurrentRealization.eval_J, AffineCurrentData.toVacuumCurrentRealization_current]
  change liftedMode D ((affineCurrent k hk hk0) (basis a)) n _ = _
  rw [(affineCurrent_basis k hk hk0)]

/-- Forgetting the first-order correction recovers exactly the original simple
quotient map. Creation-word spanning proves equality on every universal state. -/
theorem simple_deformationEval_fst (D : FirstOrderDeformation (simple k hk))
    (hD : D.IsGraded) (hreg : D.Regular) (v : WakModule k) :
    ((simple_deformationEval k hk hk0) D hD hreg v).1 = (I).mkQ v := by
  let F := (LinearMap.fst ℂ (WakModule k ⧸ I) (WakModule k ⧸ I)).comp
    ((simple_deformationEval k hk hk0) D hD hreg)
  have hword (l : List (Fin 3 × ℕ)) : F (wordStateA k l) = (I).mkQ (wordStateA k l) := by
    induction l with
    | nil =>
      change ((simple_deformationEval k hk hk0) D hD hreg (vacuumA k)).1 = _
      rw [(simple_deformationEval_vacuum k hk hk0)]
      rfl
    | cons an l ih =>
      change ((simple_deformationEval k hk hk0) D hD hreg (wordStateA k (an :: l))).1 = _
      rw [wordStateA_cons, (simple_deformationEval_J k hk hk0)]
      change (simple k hk).smul ((I).mkQ (currentState k an.1)) (-(an.2 : ℤ) - 1)
        (F (wordStateA k l)) = _
      rw [ih]
      change (QuotVOA.quotientVOA (universal k hk) (I)
        (QuotVOA.maxGradedIdeal_isIdeal (universal k hk))
        (QuotVOA.maxGradedIdeal_isGradedIdeal (universal k hk))).smul _ _ _ = _
      rw [QuotVOA.quotientVOA_mkQ_smul (QuotVOA.maxGradedIdeal_isIdeal (universal k hk))
        (QuotVOA.maxGradedIdeal_isGradedIdeal (universal k hk)), smul_currentState_eq_J]
  have hv : v ∈ Submodule.span ℂ (Set.range (wordStateA k)) := by
    rw [wordStateA_span k]
    trivial
  change F v = (I).mkQ v
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨l, rfl⟩ := hx; exact hword l
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, map_smul, hx]

/-- The degree derivation also intertwines. Both coordinates of an evaluated
homogeneous state therefore have the expected energy. -/
theorem simple_deformationEval_degree (D : FirstOrderDeformation (simple k hk))
    (hD : D.IsGraded) (hreg : D.Regular) (v : WakModule k) :
    (simple_deformationEval k hk hk0) D hD hreg (ell0OpA k v) =
      liftedDegree (W := (simple k hk)) ((simple_deformationEval k hk hk0) D hD hreg v) := by
  have h := ((simple_deformationCurrentData k hk hk0) D hD hreg).toVacuumCurrentRealization.eval_action
    (ell0 kappaForm kappaForm_isInvariant) v
  rw [show ((simple_deformationCurrentData k hk hk0) D hD hreg).toVacuumCurrentRealization.rho
    (ell0 kappaForm kappaForm_isInvariant) = ((simple_deformationCurrentData k hk hk0) D hD hreg).degree from
      ((simple_deformationCurrentData k hk hk0) D hD hreg).rho_ell0] at h
  exact h

/-- The cyclic image contains no pure first-order vacuum. Evaluation respects
energy, so a weight-zero vector in its image comes from the universal weight-zero
line. That line evaluates to multiples of (vacuum,0), never to (0,vacuum).
Closure of this image under arbitrary deformed state products remains separate. -/
theorem simple_deformationEval_separation (D : FirstOrderDeformation (simple k hk))
    (hD : D.IsGraded) (hreg : D.Regular) :
    (0, (simple k hk).vacuum) ∉ LinearMap.range ((simple_deformationEval k hk hk0) D hD hreg) := by
  let F := (simple_deformationEval k hk hk0) D hD hreg
  let p := fun n : ℤ => (gradingZA k n).map F
  let q := fun n : ℤ => Module.End.eigenspace (liftedDegree (W := (simple k hk))) (-(n : ℂ))
  have hpq : ∀ n, p n ≤ q n := by
    intro n x hx
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hx
    rw [gradingZA_def, Module.End.mem_eigenspace_iff] at hv
    change F v ∈ Module.End.eigenspace (liftedDegree (W := (simple k hk))) (-(n : ℂ))
    rw [Module.End.mem_eigenspace_iff]
    rw [← (simple_deformationEval_degree k hk hk0) D hD hreg, hv, map_smul]
  have hi : iSupIndep q :=
    (Module.End.eigenspaces_iSupIndep (liftedDegree (W := (simple k hk)))).comp negCast_injective
  have hs : (⨆ n, p n) = LinearMap.range F := by
    dsimp [p]
    rw [← Submodule.map_iSup, gradingZA_iSup_eq_top, Submodule.map_top]
  have hpart := iSup_inf_eq_of_le_independent hpq hi 0
  rw [hs] at hpart
  intro h
  have hz : (0, (simple k hk).vacuum) ∈ q 0 := by
    change (0, (simple k hk).vacuum) ∈
      Module.End.eigenspace (liftedDegree (W := (simple k hk))) (-((0 : ℤ) : ℂ))
    rw [Module.End.mem_eigenspace_iff]
    simp [liftedDegree, (simple k hk).L_zero_grading (simple k hk).vacuum (simple k hk).vacuum_mem]
  have hm : (0, (simple k hk).vacuum) ∈ p 0 := by
    rw [← hpart]
    exact ⟨h, hz⟩
  obtain ⟨v, hv, he⟩ := Submodule.mem_map.mp hm
  rw [gradingZA_zero_eq_span_vacuum, Submodule.mem_span_singleton] at hv
  obtain ⟨c, rfl⟩ := hv
  change F (c • vacuumA k) = (0, (simple k hk).vacuum) at he
  rw [map_smul, (simple_deformationEval_vacuum k hk hk0)] at he
  have hsecond := congrArg Prod.snd he
  simp only [Prod.smul_snd, smul_zero] at hsecond
  exact simple_vacuum_ne_zero k hk hsecond.symm

end VOA.AffineSl2GeneralRigidity
