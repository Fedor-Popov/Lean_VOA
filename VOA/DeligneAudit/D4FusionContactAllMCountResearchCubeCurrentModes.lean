import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeCurrent
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeModes

/-! The arbitrary-mode cube is the actual D4 current action on the pure-A
polynomial image. Commutation is proved before any projection or reduction. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

theorem any_modeX (m : ℕ) (g : Fin 10) (k : ℕ) (i : Fin 9) (r : ℕ) :
    g0Deriv m g k (modeX m i r) =
      ∑ j : Fin 9, contactF (zeroIndex g) (radIndex i) (radIndex j) • modeX m j (k+r) := by
  by_cases hr : r < m
  · rw [modeX,dif_pos hr]
    simp only [g0Deriv,MvPolynomial.mkDerivation_X,g0Image]
  · have hkr : ¬ k+r < m := by omega
    simp only [modeX,dif_neg hr,dif_neg hkr,map_zero,smul_zero,Finset.sum_const_zero]

theorem actualMode_lower_mode (m r : ℕ) (d : Fin 3) (k : ℕ) (i : Fin 8) :
    g0Deriv m (cubeDirection d) k (actualMode m r i) =
      match cubeNext d i with
      | none => 0
      | some j => actualMode m (k+r) j := by
  simp only [actualMode,Derivation.map_smul,any_modeX,Finset.smul_sum,smul_smul]
  simp_rw [actual_cube_coeff]
  cases ht : cubeNext d i <;> simp [expectedCubeCoeffC,ht]

def modesMap (m : ℕ) : ModePoly ℂ m →ₐ[ℂ] MvPolynomial (Vars m) ℂ :=
  MvPolynomial.aeval (fun x => actualMode m x.2.val x.1)

theorem modesMap_X (m : ℕ) (x : Fin 8 × Fin m) :
    modesMap m (MvPolynomial.X x) = actualMode m x.2.val x.1 := MvPolynomial.aeval_X _ _

theorem modesMap_shiftedX (m : ℕ) (i : Fin 8) (r : ℕ) :
    modesMap m (shiftedX ℂ m i r) = actualMode m r i := by
  by_cases hr : r < m
  · simp only [shiftedX,dif_pos hr,modesMap_X]
  · simp only [shiftedX,map_zero,actualMode,modeX,dif_neg hr,smul_zero]

def actualStepMode (m : ℕ) (t : Option (Fin 8)) (r : ℕ) : MvPolynomial (Vars m) ℂ :=
  match t with
  | none => 0
  | some i => actualMode m r i

theorem modesMap_step (m : ℕ) (t : Option (Fin 8)) (r : ℕ) :
    modesMap m (stepMode ℂ m t r) = actualStepMode m t r := by
  cases t with
  | none => exact map_zero _
  | some i => exact modesMap_shiftedX m i r

/-- Whole-polynomial intertwining for every current mode. -/
theorem modesMap_lower (m : ℕ) (d : Fin 3) (k : ℕ) (p : ModePoly ℂ m) :
    modesMap m (shiftedLower ℂ m d k p) = g0Deriv m (cubeDirection d) k (modesMap m p) := by
  apply map_derivation_to
  intro x
  rw [shiftedLower_X,modesMap_step,modesMap_X,actualMode_lower_mode]
  rfl

/-- Actual arbitrary negative currents commute on the complete pure-A image. -/
theorem actual_lower_modes_commute (m : ℕ) (d e : Fin 3) (k l : ℕ) (p : ModePoly ℂ m) :
    g0Deriv m (cubeDirection d) k (g0Deriv m (cubeDirection e) l (modesMap m p)) =
      g0Deriv m (cubeDirection e) l (g0Deriv m (cubeDirection d) k (modesMap m p)) := by
  rw [← modesMap_lower m e l p,← modesMap_lower m d k _,
    ← modesMap_lower m d k p,← modesMap_lower m e l _]
  exact congrArg (modesMap m) (shiftedLower_commute ℂ m d e k l p)

theorem modesMap_lower_mem (m : ℕ) (d : Fin 3) (k : ℕ) (p : ModePoly ℂ m)
    (hp : modesMap m p ∈ AllM.candidateIdeal m) :
    modesMap m (shiftedLower ℂ m d k p) ∈ AllM.candidateIdeal m := by
  rw [modesMap_lower]
  exact AllMNormal.g0_closed m k (cubeDirection d) hp

end
#print axioms actualMode_lower_mode
#print axioms modesMap_lower
#print axioms actual_lower_modes_commute
#print axioms modesMap_lower_mem
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
