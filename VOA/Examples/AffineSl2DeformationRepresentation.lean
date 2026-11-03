/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2CurrentRealization
import VOA.Examples.AffineSl2RigidityBasis
import VOA.Core.DeformationLiftedModes

/-!
# An affine vacuum representation from a regular deformation

The lifted current operators act on V × V. Their commutators, degree covariance
and vacuum conditions construct `AffineCurrentData`, rather than postulating a
representation or imposing a one-dimensional weight-zero space on the extension.
The concrete current embedding at level −4/3 is verified from the proved sl₂
basis and current pairing. Universal vacuum evaluation then supplies an actual
map from the universal affine vacuum module into the first-order extension.
Identifying its cyclic image with the mode-closed reconstruction carrier remains
a separate step; no full rigidity assertion is made here.
-/
namespace VOA.AffineVOA
open Deform
open Module (End)
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {W : VertexOperatorAlgebra V} {k : ℂ}

/-- Lift a verified affine current embedding through a regular graded deformation.
Every representation law is derived from the actual first-order mode operators. -/
noncomputable def regularDeformationCurrentData (D : FirstOrderDeformation W)
    (hD : D.IsGraded) (hreg : D.Regular) (j : Sl2 →ₗ[ℂ] V)
    (hj : ∀ x, j x ∈ W.grading 1)
    (hbr : ∀ x y, W.smul (j x) 0 (j y) = j ⁅x, y⁆)
    (hp : ∀ x y, W.smul (j x) 1 (j y) = (k * kappaForm x y) • W.vacuum) :
    AffineCurrentData k (V × V) where
  loopMode n := (liftedModeLinear D n).comp j
  degree := liftedDegree (W := W)
  vacuum := (W.vacuum, 0)
  loop_comm x y m n := by
    change ⁅liftedMode D (j x) m, liftedMode D (j y) n⁆ = _
    rw [liftedMode_comm_of_regular D hreg (hj x) (hj y) _ (hp x y), hbr]
    change liftedMode D (j ⁅x, y⁆) (m + n) + _ =
      liftedMode D (j ⁅x, y⁆) (m + n) + _
    by_cases hmn : m + n = 0
    · simp only [hmn, if_true]
      module
    · simp only [hmn, if_false]
  degree_comm x n := liftedDegree_comm D hD (hj x) n
  pos_annihilate _ n hn := liftedMode_vacuum D n hn
  degree_vacuum := liftedDegree_vacuum

end VOA.AffineVOA

namespace VOA.LQ43
open AffineVOA AffineVOA.Inst AffineLie Deform Sl2Whitehead
local notation "kk" => (-4 / 3 : ℂ)
local notation "I" => QuotVOA.maxGradedIdeal voaSl2Adm

/-- Embed the concrete coordinate sl₂, ordered (e,f,h), into the actual
weight-one space, whose proved basis is ordered (e,h,f). -/
noncomputable def affineCurrent : Sl2 →ₗ[ℂ] L43.grading 1 where
  toFun x := x 0 • L43_weightOneBasis 0 + x 1 • L43_weightOneBasis 2 +
    x 2 • L43_weightOneBasis 1
  map_add' x y := by simp only [Pi.add_apply, add_smul]; abel
  map_smul' r x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, smul_smul]

/-- The embedding preserves the Lie bracket. This verifies all current
combinations by bilinearity and the explicit sl₂ triple, including its signs. -/
theorem affineCurrent_lie (x y : Sl2) :
    affineCurrent ⁅x, y⁆ = ⁅affineCurrent x, affineCurrent y⁆ := by
  change (⁅x, y⁆ 0) • L43_weightOneBasis 0 + (⁅x, y⁆ 1) • L43_weightOneBasis 2 +
    (⁅x, y⁆ 2) • L43_weightOneBasis 1 =
    ⁅x 0 • L43_weightOneBasis 0 + x 1 • L43_weightOneBasis 2 + x 2 • L43_weightOneBasis 1,
      y 0 • L43_weightOneBasis 0 + y 1 • L43_weightOneBasis 2 + y 2 • L43_weightOneBasis 1⁆
  simp only [bracket_apply, Fin.sum_univ_three, fabc,
    add_lie, lie_add, smul_lie, lie_smul, lie_self,
    br_he L43_weightOneBasis L43_weightOneTriple,
    br_hf L43_weightOneBasis L43_weightOneTriple,
    br_ef L43_weightOneBasis L43_weightOneTriple,
    br_eh L43_weightOneBasis L43_weightOneTriple,
    br_fh L43_weightOneBasis L43_weightOneTriple,
    br_fe L43_weightOneBasis L43_weightOneTriple]
  module

/-- The first positive product has the exact original level −4/3 and normalized
Killing form. The proof checks it on the already independent quotient currents. -/
theorem affineCurrent_pole (x y : Sl2) :
    L43.smul (affineCurrent x) 1 (affineCurrent y) =
      ((-4 / 3 : ℂ) * kappaForm x y) • L43.vacuum := by
  change L43.smul
    (x 0 • (L43_weightOneBasis 0 : _) + x 1 • (L43_weightOneBasis 2 : _) +
      x 2 • (L43_weightOneBasis 1 : _)) 1
    (y 0 • (L43_weightOneBasis 0 : _) + y 1 • (L43_weightOneBasis 2 : _) +
      y 2 • (L43_weightOneBasis 1 : _)) = _
  simp only [L43_weightOneBasis_apply]
  simp only [PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_right,
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right]
  simp only [quotientCurrent_pole]
  simp only [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
    show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
    and_false, and_true, or_false, false_or,
    ite_true, ite_false, kappaForm_apply, Fin.sum_univ_three, kappa]
  module

/-- A regular graded deformation of the actual simple affine algebra produces
an affine current representation on its first-order state space at the same level. -/
noncomputable def L43_deformationCurrentData (D : FirstOrderDeformation L43)
    (hD : D.IsGraded) (hreg : D.Regular) :
    AffineCurrentData (-4 / 3 : ℂ)
      ((AffineVOA.WakModule (-4 / 3 : ℂ) ⧸ QuotVOA.maxGradedIdeal voaSl2Adm) ×
       (AffineVOA.WakModule (-4 / 3 : ℂ) ⧸ QuotVOA.maxGradedIdeal voaSl2Adm)) :=
  regularDeformationCurrentData D hD hreg ((L43.grading 1).subtype.comp affineCurrent)
    (fun x => (affineCurrent x).property)
    (fun x y => congrArg (fun v : L43.grading 1 => (v : WakModule (-4 / 3 : ℂ) ⧸
      QuotVOA.maxGradedIdeal voaSl2Adm)) (affineCurrent_lie x y).symm)
    affineCurrent_pole

/-- The current embedding agrees with the original quotient on each of the
three colour basis vectors; this fixes the change of basis order explicitly. -/
theorem affineCurrent_basis (a : Fin 3) :
    (affineCurrent (basis a) : WakModule kk ⧸ I) =
      (I).mkQ (currentState kk a) := by
  fin_cases a <;> simp [affineCurrent, basis, L43_weightOneBasis_apply] <;> rfl

/-- Evaluate a universal vacuum state by its lifted currents acting on the pure
vacuum. This is an actual map into the first-order extension, constructed from D. -/
noncomputable def L43_deformationEval (D : FirstOrderDeformation L43)
    (hD : D.IsGraded) (hreg : D.Regular) :
    WakModule kk →ₗ[ℂ] ((WakModule kk ⧸ I) × (WakModule kk ⧸ I)) :=
  (L43_deformationCurrentData D hD hreg).toVacuumCurrentRealization.eval

/-- Universal evaluation sends the vacuum to its pure lift, with no correction. -/
theorem L43_deformationEval_vacuum (D : FirstOrderDeformation L43)
    (hD : D.IsGraded) (hreg : D.Regular) :
    L43_deformationEval D hD hreg (vacuumA kk) = (L43.vacuum, 0) := by
  exact (L43_deformationCurrentData D hD hreg).toVacuumCurrentRealization.eval_vacuum

/-- Universal evaluation intertwines every current mode, including negative,
zero and positive modes, with the explicit first-order lifted operator. -/
theorem L43_deformationEval_J (D : FirstOrderDeformation L43)
    (hD : D.IsGraded) (hreg : D.Regular) (a : Fin 3) (n : ℤ) (v : WakModule kk) :
    L43_deformationEval D hD hreg (J kk a n v) =
      liftedMode D ((I).mkQ (currentState kk a)) n (L43_deformationEval D hD hreg v) := by
  unfold L43_deformationEval
  rw [VacuumCurrentRealization.eval_J, AffineCurrentData.toVacuumCurrentRealization_current]
  change liftedMode D (affineCurrent (basis a)) n _ = _
  rw [affineCurrent_basis]

/-- Forgetting the first-order correction recovers exactly the original simple
quotient map. Creation-word spanning proves equality on every universal state. -/
theorem L43_deformationEval_fst (D : FirstOrderDeformation L43)
    (hD : D.IsGraded) (hreg : D.Regular) (v : WakModule kk) :
    (L43_deformationEval D hD hreg v).1 = (I).mkQ v := by
  let F := (LinearMap.fst ℂ (WakModule kk ⧸ I) (WakModule kk ⧸ I)).comp
    (L43_deformationEval D hD hreg)
  have hword (l : List (Fin 3 × ℕ)) : F (wordStateA kk l) = (I).mkQ (wordStateA kk l) := by
    induction l with
    | nil =>
      change (L43_deformationEval D hD hreg (vacuumA kk)).1 = _
      rw [L43_deformationEval_vacuum]
      rfl
    | cons an l ih =>
      change (L43_deformationEval D hD hreg (wordStateA kk (an :: l))).1 = _
      rw [wordStateA_cons, L43_deformationEval_J]
      change L43.smul ((I).mkQ (currentState kk an.1)) (-(an.2 : ℤ) - 1)
        (F (wordStateA kk l)) = _
      rw [ih]
      change (QuotVOA.quotientVOA voaSl2Adm (I)
        (QuotVOA.maxGradedIdeal_isIdeal voaSl2Adm)
        (QuotVOA.maxGradedIdeal_isGradedIdeal voaSl2Adm)).smul _ _ _ = _
      rw [QuotVOA.quotientVOA_mkQ_smul (QuotVOA.maxGradedIdeal_isIdeal voaSl2Adm)
        (QuotVOA.maxGradedIdeal_isGradedIdeal voaSl2Adm), smul_currentState_adm]
  have hv : v ∈ Submodule.span ℂ (Set.range (wordStateA kk)) := by
    rw [wordStateA_span kk]
    trivial
  change F v = (I).mkQ v
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨l, rfl⟩ := hx; exact hword l
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, map_smul, hx]

/-- The degree derivation also intertwines. Both coordinates of an evaluated
homogeneous state therefore have the expected energy. -/
theorem L43_deformationEval_degree (D : FirstOrderDeformation L43)
    (hD : D.IsGraded) (hreg : D.Regular) (v : WakModule kk) :
    L43_deformationEval D hD hreg (ell0OpA kk v) =
      liftedDegree (W := L43) (L43_deformationEval D hD hreg v) := by
  have h := (L43_deformationCurrentData D hD hreg).toVacuumCurrentRealization.eval_action
    (ell0 kappaForm kappaForm_isInvariant) v
  rw [show (L43_deformationCurrentData D hD hreg).toVacuumCurrentRealization.rho
    (ell0 kappaForm kappaForm_isInvariant) = (L43_deformationCurrentData D hD hreg).degree from
      (L43_deformationCurrentData D hD hreg).rho_ell0] at h
  exact h

/-- The cyclic image contains no pure first-order vacuum. Evaluation respects
energy, so a weight-zero vector in its image comes from the universal weight-zero
line. That line evaluates to multiples of (vacuum,0), never to (0,vacuum).
Closure of this image under arbitrary deformed state products remains separate. -/
theorem L43_deformationEval_separation (D : FirstOrderDeformation L43)
    (hD : D.IsGraded) (hreg : D.Regular) :
    (0, L43.vacuum) ∉ LinearMap.range (L43_deformationEval D hD hreg) := by
  let F := L43_deformationEval D hD hreg
  let p := fun n : ℤ => (gradingZA kk n).map F
  let q := fun n : ℤ => Module.End.eigenspace (liftedDegree (W := L43)) (-(n : ℂ))
  have hpq : ∀ n, p n ≤ q n := by
    intro n x hx
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hx
    rw [gradingZA_def, Module.End.mem_eigenspace_iff] at hv
    change F v ∈ Module.End.eigenspace (liftedDegree (W := L43)) (-(n : ℂ))
    rw [Module.End.mem_eigenspace_iff]
    rw [← L43_deformationEval_degree D hD hreg, hv, map_smul]
  have hi : iSupIndep q :=
    (Module.End.eigenspaces_iSupIndep (liftedDegree (W := L43))).comp negCast_injective
  have hs : (⨆ n, p n) = LinearMap.range F := by
    dsimp [p]
    rw [← Submodule.map_iSup, gradingZA_iSup_eq_top, Submodule.map_top]
  have hpart := iSup_inf_eq_of_le_independent hpq hi 0
  rw [hs] at hpart
  intro h
  have hz : (0, L43.vacuum) ∈ q 0 := by
    change (0, L43.vacuum) ∈
      Module.End.eigenspace (liftedDegree (W := L43)) (-((0 : ℤ) : ℂ))
    rw [Module.End.mem_eigenspace_iff]
    simp [liftedDegree, L43.L_zero_grading L43.vacuum L43.vacuum_mem]
  have hm : (0, L43.vacuum) ∈ p 0 := by
    rw [← hpart]
    exact ⟨h, hz⟩
  obtain ⟨v, hv, he⟩ := Submodule.mem_map.mp hm
  rw [gradingZA_zero_eq_span_vacuum, Submodule.mem_span_singleton] at hv
  obtain ⟨c, rfl⟩ := hv
  change F (c • vacuumA kk) = (0, L43.vacuum) at he
  rw [map_smul, L43_deformationEval_vacuum] at he
  have hsecond := congrArg Prod.snd he
  simp only [Prod.smul_snd, smul_zero] at hsecond
  exact L43_vacuum_ne_zero hsecond.symm

end VOA.LQ43
