import VOA.Classification.COne.OrbIcoZMatrix
import VOA.Classification.COne.OrbIcoZEigenfunctional

/-! Actual conformal eigenfunctionals turn the genuine Zhu rows into matrix kernels. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA OrbOdd OrbZhu Polynomial OrbIco OrbB5
open scoped Matrix

def scalarRel (h : ℂ) (f : A Wi →ₗ[ℂ] ℂ) : ModeRel → ℂ
  | [] => 0
  | p :: r => (zp p.2).eval h * f (selfMode p.1) + scalarRel h f r

theorem scalarRel_sound (h : ℂ) (f : A Wi →ₗ[ℂ] ℂ)
    (hf : ∀ z, f (omegaL Wi z) = h * f z) (r : ModeRel) :
    f (evalRel Wi selfMode r) = scalarRel h f r := by
  induction r with
  | nil => simp [evalRel, scalarRel]
  | cons p r ih =>
    rw [evalRel, map_add, eigenfunctional_aeval h f hf, ih, scalarRel]

def topVector (f : A Wi →ₗ[ℂ] ℂ) : Fin 4 → ℂ :=
  ![f (selfMode 71), f (selfMode 55), f (selfMode 35), f (selfMode 7)]

def scalarMatrix (m : Fin 4 → Fin 4 → PL) (h : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (Polynomial.evalRingHom h).mapMatrix (fun i j => zp (m i j))

theorem scalarMatrixFirst_kernel (h : ℂ) (f : A Wi →ₗ[ℂ] ℂ)
    (hf : ∀ z, f (omegaL Wi z) = h * f z) :
    scalarMatrix matrixFirst h *ᵥ topVector f = 0 := by
  have hs : (2 : Fin 3).succ = (3 : Fin 4) := by decide
  funext i
  fin_cases i
  · have hh : scalarRel h f matrixRow1 = 0 := by
      rw [← scalarRel_sound h f hf, matrixRow1_holds, map_zero]
    simpa [scalarMatrix, Matrix.map, matrixFirst, topVector, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, hs,
      scalarRel, matrixRow1, add_assoc] using hh
  · have hh : scalarRel h f matrixRow3 = 0 := by
      rw [← scalarRel_sound h f hf, matrixRow3_holds, map_zero]
    simpa [scalarMatrix, Matrix.map, matrixFirst, topVector, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, hs,
      scalarRel, matrixRow3, add_assoc] using hh
  · have hh : scalarRel h f matrixRow5 = 0 := by
      rw [← scalarRel_sound h f hf, matrixRow5_holds, map_zero]
    simpa [scalarMatrix, Matrix.map, matrixFirst, topVector, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, hs,
      scalarRel, matrixRow5, add_assoc] using hh
  · have hh : scalarRel h f matrixRow7 = 0 := by
      rw [← scalarRel_sound h f hf, matrixRow7_holds, map_zero]
    simpa [scalarMatrix, Matrix.map, matrixFirst, topVector, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, hs,
      scalarRel, matrixRow7, add_assoc] using hh

theorem scalarMatrixSecond_kernel (h : ℂ) (f : A Wi →ₗ[ℂ] ℂ)
    (hf : ∀ z, f (omegaL Wi z) = h * f z) :
    scalarMatrix matrixSecond h *ᵥ topVector f = 0 := by
  have hs : (2 : Fin 3).succ = (3 : Fin 4) := by decide
  funext i
  fin_cases i
  · have hh : scalarRel h f matrixRow1 = 0 := by
      rw [← scalarRel_sound h f hf, matrixRow1_holds, map_zero]
    simpa [scalarMatrix, Matrix.map, matrixSecond, topVector, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, hs,
      scalarRel, matrixRow1, add_assoc] using hh
  · have hh : scalarRel h f matrixRow3 = 0 := by
      rw [← scalarRel_sound h f hf, matrixRow3_holds, map_zero]
    simpa [scalarMatrix, Matrix.map, matrixSecond, topVector, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, hs,
      scalarRel, matrixRow3, add_assoc] using hh
  · have hh : scalarRel h f matrixRow5 = 0 := by
      rw [← scalarRel_sound h f hf, matrixRow5_holds, map_zero]
    simpa [scalarMatrix, Matrix.map, matrixSecond, topVector, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, hs,
      scalarRel, matrixRow5, add_assoc] using hh
  · have hh : scalarRel h f matrixRow9 = 0 := by
      rw [← scalarRel_sound h f hf, matrixRow9_holds, map_zero]
    simpa [scalarMatrix, Matrix.map, matrixSecond, topVector, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, hs,
      scalarRel, matrixRow9, add_assoc] using hh


end VOA.Classification.COne.OrbIcoZ
