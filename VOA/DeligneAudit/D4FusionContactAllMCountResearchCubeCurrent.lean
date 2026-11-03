import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeLeading
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeCurrentData
import VOA.DeligneAudit.D4FusionContactAllMCountResearchColorCoefficient
import VOA.DeligneAudit.D4FusionContactAllMNormalCubic

/-! The normalized cube orbit is the actual whole D4 current-source orbit.
Only coefficientwise derivations and whole Garland coefficients are used. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
open VOA.DeligneAudit.D4FusionContact.Polynomial
open VOA.DeligneAudit.D4FusionContact.M2Certificate
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneSector.D4 (br)
noncomputable section

/-- Generic variable-wise intertwining, with an arbitrary target algebra. -/
theorem map_derivation_to {σ A : Type*} [CommRing A] [Algebra ℂ A]
    (f : MvPolynomial σ ℂ →ₐ[ℂ] A)
    (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (E : Derivation ℂ A A)
    (hX : ∀ i, f (D (MvPolynomial.X i)) = E (f (MvPolynomial.X i)))
    (p : MvPolynomial σ ℂ) : f (D p) = E (f p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algHom_C]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p i hp =>
      rw [D.leibniz,map_mul f p (MvPolynomial.X i),E.leibniz]
      simp only [smul_eq_mul,map_add,map_mul,hp,hX]

def lower (K : Type*) [CommRing K] : Fin 3 → Derivation K (P8 K) (P8 K) :=
  ![d1 K,d2 K,d3 K]

theorem lower_X (K : Type*) [CommRing K] (d : Fin 3) (i : Fin 8) :
    lower K d (MvPolynomial.X i) =
      match cubeNext d i with
      | none => 0
      | some j => MvPolynomial.X j := by
  fin_cases d <;> fin_cases i <;> simp [lower,cubeNext,d1,d2,d3]

def expectedCubeCoeffC (d : Fin 3) (i : Fin 8) (j : Fin 9) : ℂ :=
  match cubeNext d i with
  | none => 0
  | some k => if j=cubeColor k then (cubeSign k:ℂ) else 0

theorem actual_cube_coeff (d : Fin 3) (i : Fin 8) (j : Fin 9) :
    (cubeSign i:ℂ) * contactF (zeroIndex (cubeDirection d))
      (radIndex (cubeColor i)) (radIndex j) = expectedCubeCoeffC d i j := by
  change (cubeSign i:ℂ) * (fZ br (zeroIndex (cubeDirection d))
    (radIndex (cubeColor i)) (radIndex j):ℂ) = _
  rw [show zeroIndex (cubeDirection d) = derivRoot (cubeDirection d) from rfl,
    root_images_Z]
  have hh := signed_cube_images d i j
  cases ht : cubeNext d i with
  | none =>
      simp only [expectedCubeCoeff,ht] at hh
      simp only [expectedCubeCoeffC,ht]
      exact_mod_cast hh
  | some k =>
      by_cases hj : j=cubeColor k
      · simp only [expectedCubeCoeff,ht,if_pos hj] at hh
        simp only [expectedCubeCoeffC,ht,if_pos hj]
        exact_mod_cast hh
      · simp only [expectedCubeCoeff,ht,if_neg hj] at hh
        simp only [expectedCubeCoeffC,ht,if_neg hj]
        exact_mod_cast hh

def actualMode (m r : ℕ) (i : Fin 8) : MvPolynomial (Vars m) ℂ :=
  (cubeSign i:ℂ) • modeX m (cubeColor i) r

theorem actualMode_lower (m r : ℕ) (d : Fin 3) (i : Fin 8) :
    g0Deriv m (cubeDirection d) 0 (actualMode m r i) =
      match cubeNext d i with
      | none => 0
      | some j => actualMode m r j := by
  simp only [actualMode,Derivation.map_smul,constant_modeX,Finset.smul_sum,smul_smul]
  simp_rw [actual_cube_coeff]
  cases ht : cubeNext d i <;> simp [expectedCubeCoeffC,ht]

def actualCurrent (m : ℕ) (i : Fin 8) : PowerSeries (MvPolynomial (Vars m) ℂ) :=
  (cubeSign i:ℂ) • Polynomial.AllM.current m (cubeColor i)

@[simp] theorem actualCurrent_coeff (m r : ℕ) (i : Fin 8) :
    PowerSeries.coeff r (actualCurrent m i) = actualMode m r i := by
  simp [actualCurrent,actualMode,Polynomial.AllM.current]

theorem actualCurrent_lower (m : ℕ) (d : Fin 3) (i : Fin 8) :
    seriesDerivation (g0Deriv m (cubeDirection d) 0) (actualCurrent m i) =
      match cubeNext d i with
      | none => 0
      | some j => actualCurrent m j := by
  apply PowerSeries.ext
  intro r
  rw [seriesDerivation_coeff,actualCurrent_coeff,actualMode_lower]
  cases ht : cubeNext d i <;> simp

def currentMap (m : ℕ) : P8 ℂ →ₐ[ℂ] PowerSeries (MvPolynomial (Vars m) ℂ) :=
  MvPolynomial.aeval (actualCurrent m)

@[simp] theorem currentMap_X (m : ℕ) (i : Fin 8) :
    currentMap m (MvPolynomial.X i) = actualCurrent m i := MvPolynomial.aeval_X _ _

theorem currentMap_lower_X (m : ℕ) (d : Fin 3) (i : Fin 8) :
    currentMap m (lower ℂ d (MvPolynomial.X i)) =
      seriesDerivation (g0Deriv m (cubeDirection d) 0) (currentMap m (MvPolynomial.X i)) := by
  rw [lower_X,currentMap_X,actualCurrent_lower]
  cases ht : cubeNext d i <;> simp

/-- Intertwining holds on whole polynomials, before coefficient extraction. -/
theorem currentMap_lower (m : ℕ) (d : Fin 3) (p : P8 ℂ) :
    currentMap m (lower ℂ d p) =
      seriesDerivation (g0Deriv m (cubeDirection d) 0) (currentMap m p) :=
  map_derivation_to (currentMap m) (lower ℂ d)
    (seriesDerivation (g0Deriv m (cubeDirection d) 0)) (currentMap_lower_X m d) p

theorem currentMap_orbit (m r a b c : ℕ) :
    currentMap m (orbit ℂ r a b c) =
      ((seriesDerivation (g0Deriv m 9 0) : _ → _)^[c])
        (((seriesDerivation (g0Deriv m 8 0) : _ → _)^[b])
          (((seriesDerivation (g0Deriv m 7 0) : _ → _)^[a])
            (Polynomial.AllM.current m 0 ^ r))) := by
  rw [orbit,map_iterate_deriv (currentMap m) (d3 ℂ) _
    (fun p => currentMap_lower m 2 p)]
  rw [map_iterate_deriv (currentMap m) (d2 ℂ) _
    (fun p => currentMap_lower m 1 p)]
  rw [map_iterate_deriv (currentMap m) (d1 ℂ) _
    (fun p => currentMap_lower m 0 p)]
  simp only [map_pow,currentMap_X,actualCurrent,cubeSign,cubeColor]
  norm_num
  rfl

theorem coeff_current_iterate {A : Type*} [CommRing A] [Algebra ℂ A]
    (D : Derivation ℂ A A) (k s : ℕ) (f : PowerSeries A) :
    PowerSeries.coeff s (((seriesDerivation D : PowerSeries A → PowerSeries A)^[k]) f) =
      ((D : A → A)^[k]) (PowerSeries.coeff s f) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',seriesDerivation_coeff,ih,
      Function.iterate_succ_apply']

/-- Every admissible whole normalized cube orbit is an actual source relation. -/
theorem current_orbit_coeff_mem (m r a b c s : ℕ) (hr : 1 ≤ r) (hs : m < r + s) :
    PowerSeries.coeff s (currentMap m (orbit ℂ r a b c)) ∈ Polynomial.AllM.candidateIdeal m := by
  rw [currentMap_orbit,coeff_current_iterate,coeff_current_iterate,coeff_current_iterate]
  apply Polynomial.AllMNormal.iterate_g0_mem m 9 c
  apply Polynomial.AllMNormal.iterate_g0_mem m 8 b
  apply Polynomial.AllMNormal.iterate_g0_mem m 7 a
  exact Polynomial.AllM.seed_mem_candidate m ⟨(false,r,s),by exact ⟨hr,hs⟩⟩

end
#print axioms actual_cube_coeff
#print axioms currentMap_orbit
#print axioms current_orbit_coeff_mem
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
