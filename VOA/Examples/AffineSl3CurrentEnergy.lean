/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl3Energy

/-!
# Energy covariance of all eight currents

The Euler commutator passes through each actual locally finite normal
product. Every current mode therefore lowers energy by its Fourier index,
including the highest lowering defined through a commutator.
-/
namespace VOA.AffineSl3.FreeField
noncomputable section
open Classical

/-- The actual BG normal product has energy shift minus its total mode index. -/
theorem energy_BG (i j : Fin 3) (n : ℤ) :
    ⁅energy,BG i j n⁆= -(n : ℂ) • BG i j n := by
  have hf : (fun p => ⁅energy,bgFam i j n p⁆) =
      fun p => -(n : ℂ) • bgFam i j n p := by
    funext p
    unfold bgFam
    split_ifs <;> simp only [lie_mul_right,energy_beta,energy_gamma,Int.cast_sub,
      mul_smul_comm,smul_mul_assoc] <;> module
  change ⁅energy,opSum (bgFam i j n)⁆= -(n : ℂ) • opSum (bgFam i j n)
  rw [lie_opSum (bgFam_locFin i j n) _ (by rw [hf]; exact (bgFam_locFin i j n).smul _),
    hf,opSum_smul _ (bgFam_locFin i j n)]

/-- The actual GG normal product has energy shift minus its total mode index. -/
theorem energy_GG (i j : Fin 3) (n : ℤ) :
    ⁅energy,GG i j n⁆= -(n : ℂ) • GG i j n := by
  have hf : (fun p => ⁅energy,ggFam i j n p⁆) =
      fun p => -(n : ℂ) • ggFam i j n p := by
    funext p
    unfold ggFam
    split_ifs <;> simp only [lie_mul_right,energy_gamma,Int.cast_sub,
      mul_smul_comm,smul_mul_assoc] <;> module
  change ⁅energy,opSum (ggFam i j n)⁆= -(n : ℂ) • opSum (ggFam i j n)
  rw [lie_opSum (ggFam_locFin i j n) _ (by rw [hf]; exact (ggFam_locFin i j n).smul _),
    hf,opSum_smul _ (ggFam_locFin i j n)]

/-- The actual AG normal product has energy shift minus its total mode index. -/
theorem energy_AG (k : ℂ) (i : Fin 2) (j : Fin 3) (n : ℤ) :
    ⁅energy,AG k i j n⁆= -(n : ℂ) • AG k i j n := by
  have hf : (fun p => ⁅energy,agFam k i j n p⁆) =
      fun p => -(n : ℂ) • agFam k i j n p := by
    funext p
    unfold agFam
    split_ifs <;> simp only [lie_mul_right,energy_boson,energy_gamma,Int.cast_sub,
      mul_smul_comm,smul_mul_assoc] <;> module
  change ⁅energy,opSum (agFam k i j n)⁆= -(n : ℂ) • opSum (agFam k i j n)
  rw [lie_opSum (agFam_locFin k i j n) _ (by rw [hf]; exact (agFam_locFin k i j n).smul _),
    hf,opSum_smul _ (agFam_locFin k i j n)]

/-- The actual BGG normal product has energy shift minus its total mode index. -/
theorem energy_BGG (i j l : Fin 3) (n : ℤ) :
    ⁅energy,BGG i j l n⁆= -(n : ℂ) • BGG i j l n := by
  have hf : (fun p => ⁅energy,bggFam i j l n p⁆) =
      fun p => -(n : ℂ) • bggFam i j l n p := by
    funext p
    unfold bggFam
    split_ifs <;> simp only [lie_mul_right,energy_beta,energy_GG,Int.cast_sub,
      mul_smul_comm,smul_mul_assoc] <;> module
  change ⁅energy,opSum (bggFam i j l n)⁆= -(n : ℂ) • opSum (bggFam i j l n)
  rw [lie_opSum (bggFam_locFin i j l n) _ (by rw [hf]; exact (bggFam_locFin i j l n).smul _),
    hf,opSum_smul _ (bggFam_locFin i j l n)]

/-- The E1 current mode has the expected energy shift. -/
theorem energy_E1 (n : ℤ) : ⁅energy,E1 n⁆= -(n : ℂ) • E1 n := by
  simp only [E1,lie_add,lie_sub,lie_neg,comm_smul_right,
    energy_beta,energy_gamma,energy_boson,energy_BG,energy_AG,energy_BGG] <;> module

/-- The E2 current mode has the expected energy shift. -/
theorem energy_E2 (n : ℤ) : ⁅energy,E2 n⁆= -(n : ℂ) • E2 n := by
  simp only [E2,lie_add,lie_sub,lie_neg,comm_smul_right,
    energy_beta,energy_gamma,energy_boson,energy_BG,energy_AG,energy_BGG] <;> module

/-- The E12 current mode has the expected energy shift. -/
theorem energy_E12 (n : ℤ) : ⁅energy,E12 n⁆= -(n : ℂ) • E12 n := by
  simp only [E12,lie_add,lie_sub,lie_neg,comm_smul_right,
    energy_beta,energy_gamma,energy_boson,energy_BG,energy_AG,energy_BGG] <;> module

/-- The H1 current mode has the expected energy shift. -/
theorem energy_H1 (k : ℂ) (n : ℤ) : ⁅energy,H1 k n⁆= -(n : ℂ) • H1 k n := by
  simp only [H1,lie_add,lie_sub,lie_neg,comm_smul_right,
    energy_beta,energy_gamma,energy_boson,energy_BG,energy_AG,energy_BGG] <;> module

/-- The H2 current mode has the expected energy shift. -/
theorem energy_H2 (k : ℂ) (n : ℤ) : ⁅energy,H2 k n⁆= -(n : ℂ) • H2 k n := by
  simp only [H2,lie_add,lie_sub,lie_neg,comm_smul_right,
    energy_beta,energy_gamma,energy_boson,energy_BG,energy_AG,energy_BGG] <;> module

/-- The F1 current mode has the expected energy shift. -/
theorem energy_F1 (k : ℂ) (n : ℤ) : ⁅energy,F1 k n⁆= -(n : ℂ) • F1 k n := by
  simp only [F1,lie_add,lie_sub,lie_neg,comm_smul_right,
    energy_beta,energy_gamma,energy_boson,energy_BG,energy_AG,energy_BGG] <;> module

/-- The F2 current mode has the expected energy shift. -/
theorem energy_F2 (k : ℂ) (n : ℤ) : ⁅energy,F2 k n⁆= -(n : ℂ) • F2 k n := by
  simp only [F2,lie_add,lie_sub,lie_neg,comm_smul_right,
    energy_beta,energy_gamma,energy_boson,energy_BG,energy_AG,energy_BGG] <;> module

/-- The highest lowering inherits energy covariance from the mixed bracket. -/
theorem energy_F12 (k : ℂ) (n : ℤ) : ⁅energy,F12 k n⁆= -(n : ℂ) • F12 k n := by
  rw [F12,leibniz_lie,energy_F2,energy_F1,comm_smul_left,comm_smul_right]
  simp

/-- Every Chevalley-basis current has the same mode-energy convention. -/
theorem energy_currentBasis (k : ℂ) (i : Fin 8) (n : ℤ) :
    ⁅energy,currentBasis k i n⁆= -(n : ℂ) • currentBasis k i n := by
  fin_cases i <;> simp only [currentBasis,Matrix.cons_val_zero',Matrix.cons_val_succ',
    energy_E1,energy_E2,energy_E12,energy_H1,energy_H2,energy_F1,energy_F2,energy_F12]

/-- Energy covariance extends linearly to every actual matrix current. -/
theorem energy_currentAction (k : ℂ) (x : Sl3) (n : ℤ) :
    ⁅energy,currentAction k n x⁆= -(n : ℂ) • currentAction k n x := by
  change ⁅energy,∑ i,coordinatesLinear x i • currentBasis k i n⁆ =
    -(n : ℂ) • ∑ i,coordinatesLinear x i • currentBasis k i n
  simp only [lie_sum,comm_smul_right,energy_currentBasis,Finset.smul_sum,smul_smul]
  congr 1; funext i
  congr 1; ring

end
end VOA.AffineSl3.FreeField
