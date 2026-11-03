/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl3CurrentBilinear
import Mathlib.RingTheory.Derivation.Lie

/-!
# Energy of the actual free oscillators

The weighted Euler derivation gives beta and boson creation variables
energy j+1 and gamma variables energy j. In particular gamma zero modes
remain energy-zero creation operators. The affine degree derivation
will act as the negative of this positive energy operator.
-/
namespace VOA.AffineSl3.FreeField
noncomputable section
open Classical MvPolynomial

/-- Weighted Euler operator on the actual multicolour polynomial space. -/
def weightedEuler (w : Colour × ℕ → ℂ) : Module.End ℂ Fock :=
  (mkDerivation ℂ (fun v => w v • (X v : Fock))).toLinearMap

/-- Weighted Euler acts on a generator with its assigned scalar weight. -/
theorem weightedEuler_X (w : Colour × ℕ → ℂ) (v : Colour × ℕ) :
    weightedEuler w (X v)=w v • X v := mkDerivation_X ℂ _ v

/-- The vacuum has zero Euler weight. -/
theorem weightedEuler_one (w : Colour × ℕ → ℂ) : weightedEuler w 1=0 :=
  (mkDerivation ℂ (fun v => w v • (X v : Fock))).map_one_eq_zero

/-- Creation raises weighted Euler degree by the variable weight. -/
theorem weightedEuler_create (w : Colour × ℕ → ℂ) (v : Colour × ℕ) :
    ⁅weightedEuler w,create v⁆=w v • create v := by
  refine LinearMap.ext fun P => ?_
  change weightedEuler w (X v*P)-X v*weightedEuler w P=w v • (X v*P)
  have h := (mkDerivation ℂ (fun u => w u • (X u : Fock))).leibniz (X v) P
  change weightedEuler w (X v*P)=X v*weightedEuler w P+P*weightedEuler w (X v) at h
  rw [h,weightedEuler_X]
  simp [smul_eq_C_mul]; ring

/-- Formal partial differentiation lowers weighted Euler degree by the
same weight. Derivation extensionality reduces the commutator to variables. -/
theorem weightedEuler_deriv (w : Colour × ℕ → ℂ) (v : Colour × ℕ) :
    ⁅weightedEuler w,deriv v⁆= -(w v) • deriv v := by
  have h : ⁅mkDerivation ℂ (fun u => w u • (X u : Fock)),pderiv v⁆=
      -(w v) • (pderiv v : Derivation ℂ Fock Fock) := by
    apply derivation_ext
    intro u
    rw [Derivation.commutator_apply,mkDerivation_X]
    by_cases hu : u=v
    · subst u
      simp [pderiv_X_self,map_smul]
    · simp [pderiv_X_of_ne hu,map_smul]
  exact congrArg Derivation.toLinearMap h

/-- Oscillator energies, including energy zero for gamma creation at index zero. -/
def oscillatorWeight (v : Colour × ℕ) : ℂ :=
  match v.1 with
  | .gamma _ => (v.2 : ℂ)
  | _ => (v.2 : ℂ)+1

/-- Positive energy on the polynomial Fock space. -/
def energy : Module.End ℂ Fock := weightedEuler oscillatorWeight

/-- The polynomial vacuum has energy zero. -/
theorem energy_vacuum : energy 1=0 := weightedEuler_one _

/-- The cast of the natural index of a negative beta or boson mode. -/
theorem negative_mode_index {m : ℤ} (hm : m<0) :
    (((-m-1).toNat : ℕ) : ℂ)+1= -(m : ℂ) := by
  have h : (((-m-1).toNat : ℕ) : ℤ)= -m-1 := Int.toNat_of_nonneg (by omega)
  have hc : (((-m-1).toNat : ℕ) : ℂ)= -(m : ℂ)-1 := by exact_mod_cast h
  rw [hc]; ring

/-- The cast of the natural index of a positive annihilation mode. -/
theorem positive_mode_index {m : ℤ} (hm : 0<m) :
    (((m-1).toNat : ℕ) : ℂ)+1=(m : ℂ) := by
  have h : (((m-1).toNat : ℕ) : ℤ)=m-1 := Int.toNat_of_nonneg (by omega)
  have hc : (((m-1).toNat : ℕ) : ℂ)=(m : ℂ)-1 := by exact_mod_cast h
  rw [hc]; ring

/-- Every beta mode has energy shift minus its Fourier index. -/
theorem energy_beta (i : Fin 3) (m : ℤ) : ⁅energy,beta i m⁆= -(m : ℂ) • beta i m := by
  unfold beta energy
  split_ifs with hm
  · rw [weightedEuler_create]
    simp only [oscillatorWeight]
    rw [negative_mode_index hm]
  · rw [weightedEuler_deriv]
    simp only [oscillatorWeight]
    have h : ((m.toNat : ℕ) : ℂ)=(m : ℂ) := by
      exact_mod_cast (Int.toNat_of_nonneg (show 0 ≤ m by omega))
    rw [h]

/-- Every gamma mode has the same energy shift, including its zero mode. -/
theorem energy_gamma (i : Fin 3) (m : ℤ) : ⁅energy,gamma i m⁆= -(m : ℂ) • gamma i m := by
  unfold gamma energy
  split_ifs with hm
  · rw [weightedEuler_create]
    simp only [oscillatorWeight]
    have h : (((-m).toNat : ℕ) : ℂ)= -(m : ℂ) := by
      exact_mod_cast (Int.toNat_of_nonneg (show 0 ≤ -m by omega))
    rw [h]
  · rw [lie_neg,weightedEuler_deriv]
    simp only [oscillatorWeight]
    rw [positive_mode_index (by omega)]
    module

/-- A Cartan row of annihilation derivatives has the common oscillator degree. -/
theorem energy_cartanDeriv (i : Fin 2) (j : ℕ) :
    ⁅energy,cartanDeriv i j⁆= -((j : ℂ)+1) • cartanDeriv i j := by
  simp only [energy,cartanDeriv,lie_sum,comm_smul_right,weightedEuler_deriv,
    oscillatorWeight,Finset.smul_sum,smul_smul]
  congr 1; funext a
  congr 1; ring

/-- Every Cartan boson mode lowers energy by its Fourier index. -/
theorem energy_boson (k : ℂ) (i : Fin 2) (m : ℤ) :
    ⁅energy,boson k i m⁆= -(m : ℂ) • boson k i m := by
  unfold boson
  split_ifs with hm
  · rw [energy,weightedEuler_create]
    simp only [oscillatorWeight]
    rw [negative_mode_index hm]
  · by_cases hz : m=0
    · subst m; simp
    · rw [comm_smul_right,energy_cartanDeriv,positive_mode_index (by omega)]
      module

end
end VOA.AffineSl3.FreeField
