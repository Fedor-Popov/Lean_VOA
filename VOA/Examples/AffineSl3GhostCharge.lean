/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl3CartanComposites

/-!
# Ghost charge and detection of zero operators

The sum of the two zero Cartan modes is a weighted ghost number operator.
An operator commuting with every ghost oscillator commutes with this charge.
Consequently such an operator cannot have a nonzero charge. This argument
uses the actual locally finite normal products, without irreducibility or
any restriction on the level.
-/
namespace VOA.AffineSl3.FreeField
noncomputable section
open Classical

/-- Root-height weights of the three beta colours; gamma has the opposite charge. -/
def ghostWeight (i : Fin 3) : ℂ := if i=2 then 2 else 1

/-- Total root-height charge, formed from the three diagonal ghost currents. -/
def ghostCharge : Module.End ℂ Fock := -BG 0 0 0-BG 1 1 0-(2 : ℂ) • BG 2 2 0

/-- The ghost charge is the sum of the actual Cartan zero modes. -/
theorem ghostCharge_eq (k : ℂ) : ghostCharge = H1 k 0+H2 k 0 := by
  simp [ghostCharge,H1,H2,boson] <;> module

/-- Beta oscillators carry positive root-height charge. -/
theorem ghostCharge_beta (i : Fin 3) (n : ℤ) :
    ⁅ghostCharge,beta i n⁆ = ghostWeight i • beta i n := by
  fin_cases i <;> simp [ghostCharge,ghostWeight,sub_lie,neg_lie,comm_smul_left,D_beta,colourDelta] <;> module

/-- Gamma oscillators carry negative root-height charge. -/
theorem ghostCharge_gamma (i : Fin 3) (n : ℤ) :
    ⁅ghostCharge,gamma i n⁆ = -ghostWeight i • gamma i n := by
  fin_cases i <;> simp [ghostCharge,ghostWeight,sub_lie,neg_lie,comm_smul_left,D_gamma,colourDelta] <;> module

/-- The charge of a gamma pair is the sum of its two negative charges. -/
theorem ghostCharge_GG (i j : Fin 3) (n : ℤ) :
    ⁅ghostCharge,GG i j n⁆ = -(ghostWeight i+ghostWeight j) • GG i j n := by
  fin_cases i <;> fin_cases j <;>
    simp [ghostCharge,ghostWeight,sub_lie,neg_lie,comm_smul_left,D_GG,colourDelta] <;> module

/-- The first lowering current has root-height charge minus one. -/
theorem ghostCharge_F1 (k : ℂ) (n : ℤ) :
    ⁅ghostCharge,F1 k n⁆ = (-1 : ℂ) • F1 k n := by
  rw [ghostCharge_eq k,add_lie,H1_F1,H2_F1]
  simp only [zero_add]; module

/-- The second lowering current also has root-height charge minus one. -/
theorem ghostCharge_F2 (k : ℂ) (n : ℤ) :
    ⁅ghostCharge,F2 k n⁆ = (-1 : ℂ) • F2 k n := by
  rw [ghostCharge_eq k,add_lie,H1_F2,H2_F2]
  simp only [zero_add]; module

/-- Commutation with the two oscillator factors implies commutation with
an actual beta-gamma normal product. -/
theorem commuting_BG (D : Module.End ℂ Fock) (i j : Fin 3) (n : ℤ)
    (hb : ∀ m, ⁅D,beta i m⁆=0) (hg : ∀ m, ⁅D,gamma j m⁆=0) :
    ⁅D,BG i j n⁆=0 := by
  have hf : (fun p => ⁅D,bgFam i j n p⁆) = fun _ => (0 : Module.End ℂ Fock) := by
    funext p; unfold bgFam; split_ifs <;> simp [lie_mul_right,hb,hg]
  rw [BG,lie_opSum (bgFam_locFin i j n) _ (by rw [hf]; exact locFin_zero),hf,opSum_zero]

/-- A nonzero charge excludes an operator from the commutant of all ghost
oscillators. No assertion about the bosonic commutant is needed. -/
theorem zero_of_ghost_commuting_weight (D : Module.End ℂ Fock) (c : ℂ)
    (hb : ∀ i m, ⁅D,beta i m⁆=0) (hg : ∀ i m, ⁅D,gamma i m⁆=0)
    (hc : c≠0) (hw : ⁅ghostCharge,D⁆=c • D) : D=0 := by
  have hq : ⁅D,ghostCharge⁆=0 := by
    simp [ghostCharge,lie_sub,lie_neg,comm_smul_right,
      commuting_BG D 0 0 0 (hb 0) (hg 0),
      commuting_BG D 1 1 0 (hb 1) (hg 1),
      commuting_BG D 2 2 0 (hb 2) (hg 2)]
  have hz : c • D=0 := by rw [← hw,← lie_skew ghostCharge D,hq,neg_zero]
  exact (smul_eq_zero.mp hz).resolve_left hc

/-- Gamma-pair normal products commute, since their oscillator factors commute. -/
theorem GG_GG (i j a b : Fin 3) (m n : ℤ) : ⁅GG i j m,GG a b n⁆=0 := by
  have hf : (fun p => ⁅GG i j m,ggFam a b n p⁆) = fun _ => (0 : Module.End ℂ Fock) := by
    funext p; simp [ggFam_eq,lie_mul_right,GG_gamma]
  change ⁅GG i j m,opSum (ggFam a b n)⁆=0
  rw [lie_opSum (ggFam_locFin a b n) _ (by rw [hf]; exact locFin_zero),hf,opSum_zero]

/-- Boson-gamma products commute with gamma oscillators. -/
theorem AG_gamma (k : ℂ) (i : Fin 2) (j a : Fin 3) (m n : ℤ) :
    ⁅AG k i j m,gamma a n⁆=0 := by
  have hf : (fun p => ⁅agFam k i j m p,gamma a n⁆) = fun _ => (0 : Module.End ℂ Fock) := by
    funext p; unfold agFam; split_ifs <;> simp [lie_mul_left,boson_gamma,gamma_gamma]
  rw [AG,opSum_lie (agFam_locFin k i j m) _ (by rw [hf]; exact locFin_zero),hf,opSum_zero]

/-- Explicit first-lowering action on each gamma colour. -/
theorem F1_gamma (k : ℂ) (i : Fin 3) (m n : ℤ) :
    ⁅F1 k m,gamma i n⁆ =
      if i=0 then -GG 0 0 (m+n) else if i=1 then -gamma 2 (m+n) else 0 := by
  fin_cases i <;> simp [F1,sub_lie,neg_lie,add_lie,comm_smul_left,
    BGG_gamma,BG_lie_gamma,gamma_gamma,AG_gamma]

/-- Explicit second-lowering action on each gamma colour. -/
theorem F2_gamma (k : ℂ) (i : Fin 3) (m n : ℤ) :
    ⁅F2 k m,gamma i n⁆ = if i=0 then GG 0 1 (m+n)+gamma 2 (m+n)
      else if i=1 then -GG 1 1 (m+n) else -GG 1 2 (m+n) := by
  fin_cases i <;> simp [F2,sub_lie,neg_lie,add_lie,comm_smul_left,
    BGG_gamma,BG_lie_gamma,gamma_gamma,AG_gamma]

end
end VOA.AffineSl3.FreeField
