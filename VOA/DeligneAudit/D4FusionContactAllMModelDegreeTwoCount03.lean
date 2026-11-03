import VOA.DeligneAudit.D4FusionContactAllMModelDegreeTwoCount02
import Mathlib.Tactic.FinCases

/-! Current-degree counts of the m=2 normal-word stems 210..279, reusing the
kernel-checked stem flags of the length cascade (generated certificate). -/
namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

set_option maxRecDepth 100000

def stem210Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem210_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [6, 8, 12]) b.val = stem210Deg b := by
  rw [degCount_fuel_one leaders 12 [6, 8, 12] stem210Flags stem210_flags b]
  fin_cases b <;> decide +kernel

def stem211Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem211_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 14 [6, 8, 14]) b.val = stem211Deg b := by
  rw [degCount_fuel_one leaders 14 [6, 8, 14] stem211Flags stem211_flags b]
  fin_cases b <;> decide +kernel

def stem212Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem212_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [6, 8, 16]) b.val = stem212Deg b := by
  rw [degCount_fuel_one leaders 16 [6, 8, 16] stem212Flags stem212_flags b]
  fin_cases b <;> decide +kernel

def stem213Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem213_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [6, 8, 17]) b.val = stem213Deg b := by
  rw [degCount_fuel_one leaders 17 [6, 8, 17] stem213Flags stem213_flags b]
  fin_cases b <;> decide +kernel

def stem214Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem214_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 10 [6, 9, 10]) b.val = stem214Deg b := by
  rw [degCount_fuel_one leaders 10 [6, 9, 10] stem214Flags stem214_flags b]
  fin_cases b <;> decide +kernel

def stem215Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem215_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [6, 9, 12]) b.val = stem215Deg b := by
  rw [degCount_fuel_one leaders 12 [6, 9, 12] stem215Flags stem215_flags b]
  fin_cases b <;> decide +kernel

def stem216Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem216_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [6, 9, 16]) b.val = stem216Deg b := by
  rw [degCount_fuel_one leaders 16 [6, 9, 16] stem216Flags stem216_flags b]
  fin_cases b <;> decide +kernel

def stem217Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem217_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [6, 10, 12]) b.val = stem217Deg b := by
  rw [degCount_fuel_one leaders 12 [6, 10, 12] stem217Flags stem217_flags b]
  fin_cases b <;> decide +kernel

def stem218Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem218_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [6, 10, 16]) b.val = stem218Deg b := by
  rw [degCount_fuel_one leaders 16 [6, 10, 16] stem218Flags stem218_flags b]
  fin_cases b <;> decide +kernel

def stem219Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem219_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [6, 10, 17]) b.val = stem219Deg b := by
  rw [degCount_fuel_one leaders 17 [6, 10, 17] stem219Flags stem219_flags b]
  fin_cases b <;> decide +kernel

def stem220Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem220_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [6, 12, 16]) b.val = stem220Deg b := by
  rw [degCount_fuel_one leaders 16 [6, 12, 16] stem220Flags stem220_flags b]
  fin_cases b <;> decide +kernel

def stem221Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem221_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [6, 12, 17]) b.val = stem221Deg b := by
  rw [degCount_fuel_one leaders 17 [6, 12, 17] stem221Flags stem221_flags b]
  fin_cases b <;> decide +kernel

def stem222Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem222_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [6, 14, 16]) b.val = stem222Deg b := by
  rw [degCount_fuel_one leaders 16 [6, 14, 16] stem222Flags stem222_flags b]
  fin_cases b <;> decide +kernel

def stem223Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem223_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [6, 14, 17]) b.val = stem223Deg b := by
  rw [degCount_fuel_one leaders 17 [6, 14, 17] stem223Flags stem223_flags b]
  fin_cases b <;> decide +kernel

def stem224Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem224_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [6, 16, 16]) b.val = stem224Deg b := by
  rw [degCount_fuel_one leaders 16 [6, 16, 16] stem224Flags stem224_flags b]
  fin_cases b <;> decide +kernel

def stem225Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem225_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [6, 16, 17]) b.val = stem225Deg b := by
  rw [degCount_fuel_one leaders 17 [6, 16, 17] stem225Flags stem225_flags b]
  fin_cases b <;> decide +kernel

def stem226Deg (b : Fin 5) : ℕ := [0, 4, 0, 0, 0].getD b.val 0

theorem stem226_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 8 [7, 8, 8]) b.val = stem226Deg b := by
  rw [degCount_fuel_one leaders 8 [7, 8, 8] stem226Flags stem226_flags b]
  fin_cases b <;> decide +kernel

def stem227Deg (b : Fin 5) : ℕ := [0, 3, 0, 0, 0].getD b.val 0

theorem stem227_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 10 [7, 8, 10]) b.val = stem227Deg b := by
  rw [degCount_fuel_one leaders 10 [7, 8, 10] stem227Flags stem227_flags b]
  fin_cases b <;> decide +kernel

def stem228Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem228_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [7, 8, 12]) b.val = stem228Deg b := by
  rw [degCount_fuel_one leaders 12 [7, 8, 12] stem228Flags stem228_flags b]
  fin_cases b <;> decide +kernel

def stem229Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem229_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 14 [7, 8, 14]) b.val = stem229Deg b := by
  rw [degCount_fuel_one leaders 14 [7, 8, 14] stem229Flags stem229_flags b]
  fin_cases b <;> decide +kernel

def stem230Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem230_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [7, 8, 16]) b.val = stem230Deg b := by
  rw [degCount_fuel_one leaders 16 [7, 8, 16] stem230Flags stem230_flags b]
  fin_cases b <;> decide +kernel

def stem231Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem231_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [7, 8, 17]) b.val = stem231Deg b := by
  rw [degCount_fuel_one leaders 17 [7, 8, 17] stem231Flags stem231_flags b]
  fin_cases b <;> decide +kernel

def stem232Deg (b : Fin 5) : ℕ := [0, 0, 2, 0, 0].getD b.val 0

theorem stem232_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 10 [7, 9, 10]) b.val = stem232Deg b := by
  rw [degCount_fuel_one leaders 10 [7, 9, 10] stem232Flags stem232_flags b]
  fin_cases b <;> decide +kernel

def stem233Deg (b : Fin 5) : ℕ := [0, 0, 2, 0, 0].getD b.val 0

theorem stem233_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [7, 9, 12]) b.val = stem233Deg b := by
  rw [degCount_fuel_one leaders 12 [7, 9, 12] stem233Flags stem233_flags b]
  fin_cases b <;> decide +kernel

def stem234Deg (b : Fin 5) : ℕ := [0, 0, 2, 0, 0].getD b.val 0

theorem stem234_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [7, 9, 16]) b.val = stem234Deg b := by
  rw [degCount_fuel_one leaders 16 [7, 9, 16] stem234Flags stem234_flags b]
  fin_cases b <;> decide +kernel

def stem235Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem235_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [7, 10, 12]) b.val = stem235Deg b := by
  rw [degCount_fuel_one leaders 12 [7, 10, 12] stem235Flags stem235_flags b]
  fin_cases b <;> decide +kernel

def stem236Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem236_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [7, 10, 16]) b.val = stem236Deg b := by
  rw [degCount_fuel_one leaders 16 [7, 10, 16] stem236Flags stem236_flags b]
  fin_cases b <;> decide +kernel

def stem237Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem237_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [7, 10, 17]) b.val = stem237Deg b := by
  rw [degCount_fuel_one leaders 17 [7, 10, 17] stem237Flags stem237_flags b]
  fin_cases b <;> decide +kernel

def stem238Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem238_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [7, 12, 16]) b.val = stem238Deg b := by
  rw [degCount_fuel_one leaders 16 [7, 12, 16] stem238Flags stem238_flags b]
  fin_cases b <;> decide +kernel

def stem239Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem239_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [7, 12, 17]) b.val = stem239Deg b := by
  rw [degCount_fuel_one leaders 17 [7, 12, 17] stem239Flags stem239_flags b]
  fin_cases b <;> decide +kernel

def stem240Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem240_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [7, 14, 16]) b.val = stem240Deg b := by
  rw [degCount_fuel_one leaders 16 [7, 14, 16] stem240Flags stem240_flags b]
  fin_cases b <;> decide +kernel

def stem241Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem241_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [7, 14, 17]) b.val = stem241Deg b := by
  rw [degCount_fuel_one leaders 17 [7, 14, 17] stem241Flags stem241_flags b]
  fin_cases b <;> decide +kernel

def stem242Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem242_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [7, 16, 16]) b.val = stem242Deg b := by
  rw [degCount_fuel_one leaders 16 [7, 16, 16] stem242Flags stem242_flags b]
  fin_cases b <;> decide +kernel

def stem243Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem243_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [7, 16, 17]) b.val = stem243Deg b := by
  rw [degCount_fuel_one leaders 17 [7, 16, 17] stem243Flags stem243_flags b]
  fin_cases b <;> decide +kernel

def stem244Deg (b : Fin 5) : ℕ := [4, 0, 0, 0, 0].getD b.val 0

theorem stem244_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 10 [8, 8, 10]) b.val = stem244Deg b := by
  rw [degCount_fuel_one leaders 10 [8, 8, 10] stem244Flags stem244_flags b]
  fin_cases b <;> decide +kernel

def stem245Deg (b : Fin 5) : ℕ := [0, 3, 0, 0, 0].getD b.val 0

theorem stem245_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 11 [8, 8, 11]) b.val = stem245Deg b := by
  rw [degCount_fuel_one leaders 11 [8, 8, 11] stem245Flags stem245_flags b]
  fin_cases b <;> decide +kernel

def stem246Deg (b : Fin 5) : ℕ := [3, 0, 0, 0, 0].getD b.val 0

theorem stem246_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [8, 8, 12]) b.val = stem246Deg b := by
  rw [degCount_fuel_one leaders 12 [8, 8, 12] stem246Flags stem246_flags b]
  fin_cases b <;> decide +kernel

def stem247Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem247_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 13 [8, 8, 13]) b.val = stem247Deg b := by
  rw [degCount_fuel_one leaders 13 [8, 8, 13] stem247Flags stem247_flags b]
  fin_cases b <;> decide +kernel

def stem248Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem248_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [8, 8, 16]) b.val = stem248Deg b := by
  rw [degCount_fuel_one leaders 16 [8, 8, 16] stem248Flags stem248_flags b]
  fin_cases b <;> decide +kernel

def stem249Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem249_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [8, 8, 17]) b.val = stem249Deg b := by
  rw [degCount_fuel_one leaders 17 [8, 8, 17] stem249Flags stem249_flags b]
  fin_cases b <;> decide +kernel

def stem250Deg (b : Fin 5) : ℕ := [3, 0, 0, 0, 0].getD b.val 0

theorem stem250_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 10 [8, 10, 10]) b.val = stem250Deg b := by
  rw [degCount_fuel_one leaders 10 [8, 10, 10] stem250Flags stem250_flags b]
  fin_cases b <;> decide +kernel

def stem251Deg (b : Fin 5) : ℕ := [3, 0, 0, 0, 0].getD b.val 0

theorem stem251_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [8, 10, 12]) b.val = stem251Deg b := by
  rw [degCount_fuel_one leaders 12 [8, 10, 12] stem251Flags stem251_flags b]
  fin_cases b <;> decide +kernel

def stem252Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem252_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 13 [8, 10, 13]) b.val = stem252Deg b := by
  rw [degCount_fuel_one leaders 13 [8, 10, 13] stem252Flags stem252_flags b]
  fin_cases b <;> decide +kernel

def stem253Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem253_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 14 [8, 10, 14]) b.val = stem253Deg b := by
  rw [degCount_fuel_one leaders 14 [8, 10, 14] stem253Flags stem253_flags b]
  fin_cases b <;> decide +kernel

def stem254Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem254_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [8, 10, 16]) b.val = stem254Deg b := by
  rw [degCount_fuel_one leaders 16 [8, 10, 16] stem254Flags stem254_flags b]
  fin_cases b <;> decide +kernel

def stem255Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem255_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [8, 10, 17]) b.val = stem255Deg b := by
  rw [degCount_fuel_one leaders 17 [8, 10, 17] stem255Flags stem255_flags b]
  fin_cases b <;> decide +kernel

def stem256Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem256_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [8, 11, 12]) b.val = stem256Deg b := by
  rw [degCount_fuel_one leaders 12 [8, 11, 12] stem256Flags stem256_flags b]
  fin_cases b <;> decide +kernel

def stem257Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem257_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [8, 11, 16]) b.val = stem257Deg b := by
  rw [degCount_fuel_one leaders 16 [8, 11, 16] stem257Flags stem257_flags b]
  fin_cases b <;> decide +kernel

def stem258Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem258_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [8, 12, 12]) b.val = stem258Deg b := by
  rw [degCount_fuel_one leaders 12 [8, 12, 12] stem258Flags stem258_flags b]
  fin_cases b <;> decide +kernel

def stem259Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem259_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 14 [8, 12, 14]) b.val = stem259Deg b := by
  rw [degCount_fuel_one leaders 14 [8, 12, 14] stem259Flags stem259_flags b]
  fin_cases b <;> decide +kernel

def stem260Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem260_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [8, 12, 16]) b.val = stem260Deg b := by
  rw [degCount_fuel_one leaders 16 [8, 12, 16] stem260Flags stem260_flags b]
  fin_cases b <;> decide +kernel

def stem261Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem261_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [8, 12, 17]) b.val = stem261Deg b := by
  rw [degCount_fuel_one leaders 17 [8, 12, 17] stem261Flags stem261_flags b]
  fin_cases b <;> decide +kernel

def stem262Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem262_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [8, 13, 16]) b.val = stem262Deg b := by
  rw [degCount_fuel_one leaders 16 [8, 13, 16] stem262Flags stem262_flags b]
  fin_cases b <;> decide +kernel

def stem263Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem263_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [8, 14, 16]) b.val = stem263Deg b := by
  rw [degCount_fuel_one leaders 16 [8, 14, 16] stem263Flags stem263_flags b]
  fin_cases b <;> decide +kernel

def stem264Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem264_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [8, 14, 17]) b.val = stem264Deg b := by
  rw [degCount_fuel_one leaders 17 [8, 14, 17] stem264Flags stem264_flags b]
  fin_cases b <;> decide +kernel

def stem265Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem265_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [8, 16, 16]) b.val = stem265Deg b := by
  rw [degCount_fuel_one leaders 16 [8, 16, 16] stem265Flags stem265_flags b]
  fin_cases b <;> decide +kernel

def stem266Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem266_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [8, 16, 17]) b.val = stem266Deg b := by
  rw [degCount_fuel_one leaders 17 [8, 16, 17] stem266Flags stem266_flags b]
  fin_cases b <;> decide +kernel

def stem267Deg (b : Fin 5) : ℕ := [0, 3, 0, 0, 0].getD b.val 0

theorem stem267_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 10 [9, 10, 10]) b.val = stem267Deg b := by
  rw [degCount_fuel_one leaders 10 [9, 10, 10] stem267Flags stem267_flags b]
  fin_cases b <;> decide +kernel

def stem268Deg (b : Fin 5) : ℕ := [0, 3, 0, 0, 0].getD b.val 0

theorem stem268_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [9, 10, 12]) b.val = stem268Deg b := by
  rw [degCount_fuel_one leaders 12 [9, 10, 12] stem268Flags stem268_flags b]
  fin_cases b <;> decide +kernel

def stem269Deg (b : Fin 5) : ℕ := [0, 0, 2, 0, 0].getD b.val 0

theorem stem269_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 13 [9, 10, 13]) b.val = stem269Deg b := by
  rw [degCount_fuel_one leaders 13 [9, 10, 13] stem269Flags stem269_flags b]
  fin_cases b <;> decide +kernel

def stem270Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem270_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 14 [9, 10, 14]) b.val = stem270Deg b := by
  rw [degCount_fuel_one leaders 14 [9, 10, 14] stem270Flags stem270_flags b]
  fin_cases b <;> decide +kernel

def stem271Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem271_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [9, 10, 16]) b.val = stem271Deg b := by
  rw [degCount_fuel_one leaders 16 [9, 10, 16] stem271Flags stem271_flags b]
  fin_cases b <;> decide +kernel

def stem272Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem272_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [9, 10, 17]) b.val = stem272Deg b := by
  rw [degCount_fuel_one leaders 17 [9, 10, 17] stem272Flags stem272_flags b]
  fin_cases b <;> decide +kernel

def stem273Deg (b : Fin 5) : ℕ := [0, 0, 2, 0, 0].getD b.val 0

theorem stem273_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [9, 11, 12]) b.val = stem273Deg b := by
  rw [degCount_fuel_one leaders 12 [9, 11, 12] stem273Flags stem273_flags b]
  fin_cases b <;> decide +kernel

def stem274Deg (b : Fin 5) : ℕ := [0, 0, 2, 0, 0].getD b.val 0

theorem stem274_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [9, 11, 16]) b.val = stem274Deg b := by
  rw [degCount_fuel_one leaders 16 [9, 11, 16] stem274Flags stem274_flags b]
  fin_cases b <;> decide +kernel

def stem275Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem275_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [9, 12, 12]) b.val = stem275Deg b := by
  rw [degCount_fuel_one leaders 12 [9, 12, 12] stem275Flags stem275_flags b]
  fin_cases b <;> decide +kernel

def stem276Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem276_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 14 [9, 12, 14]) b.val = stem276Deg b := by
  rw [degCount_fuel_one leaders 14 [9, 12, 14] stem276Flags stem276_flags b]
  fin_cases b <;> decide +kernel

def stem277Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem277_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [9, 12, 16]) b.val = stem277Deg b := by
  rw [degCount_fuel_one leaders 16 [9, 12, 16] stem277Flags stem277_flags b]
  fin_cases b <;> decide +kernel

def stem278Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem278_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [9, 12, 17]) b.val = stem278Deg b := by
  rw [degCount_fuel_one leaders 17 [9, 12, 17] stem278Flags stem278_flags b]
  fin_cases b <;> decide +kernel

def stem279Deg (b : Fin 5) : ℕ := [0, 0, 2, 0, 0].getD b.val 0

theorem stem279_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [9, 13, 16]) b.val = stem279Deg b := by
  rw [degCount_fuel_one leaders 16 [9, 13, 16] stem279Flags stem279_flags b]
  fin_cases b <;> decide +kernel

end VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Count.stem279_dcount
