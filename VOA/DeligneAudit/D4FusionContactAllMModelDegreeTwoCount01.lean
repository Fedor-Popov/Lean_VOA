import VOA.DeligneAudit.D4FusionContactAllMModelDegreeTwoCount00
import Mathlib.Tactic.FinCases

/-! Current-degree counts of the m=2 normal-word stems 70..139, reusing the
kernel-checked stem flags of the length cascade (generated certificate). -/
namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

set_option maxRecDepth 100000

def stem070Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem070_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 10 [2, 5, 10]) b.val = stem070Deg b := by
  rw [degCount_fuel_one leaders 10 [2, 5, 10] stem070Flags stem070_flags b]
  fin_cases b <;> decide +kernel

def stem071Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem071_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [2, 5, 12]) b.val = stem071Deg b := by
  rw [degCount_fuel_one leaders 12 [2, 5, 12] stem071Flags stem071_flags b]
  fin_cases b <;> decide +kernel

def stem072Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem072_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [2, 5, 16]) b.val = stem072Deg b := by
  rw [degCount_fuel_one leaders 16 [2, 5, 16] stem072Flags stem072_flags b]
  fin_cases b <;> decide +kernel

def stem073Deg (b : Fin 5) : ℕ := [3, 0, 0, 0, 0].getD b.val 0

theorem stem073_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 6 [2, 6, 6]) b.val = stem073Deg b := by
  rw [degCount_fuel_one leaders 6 [2, 6, 6] stem073Flags stem073_flags b]
  fin_cases b <;> decide +kernel

def stem074Deg (b : Fin 5) : ℕ := [4, 0, 0, 0, 0].getD b.val 0

theorem stem074_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 8 [2, 6, 8]) b.val = stem074Deg b := by
  rw [degCount_fuel_one leaders 8 [2, 6, 8] stem074Flags stem074_flags b]
  fin_cases b <;> decide +kernel

def stem075Deg (b : Fin 5) : ℕ := [3, 0, 0, 0, 0].getD b.val 0

theorem stem075_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 10 [2, 6, 10]) b.val = stem075Deg b := by
  rw [degCount_fuel_one leaders 10 [2, 6, 10] stem075Flags stem075_flags b]
  fin_cases b <;> decide +kernel

def stem076Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem076_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [2, 6, 12]) b.val = stem076Deg b := by
  rw [degCount_fuel_one leaders 12 [2, 6, 12] stem076Flags stem076_flags b]
  fin_cases b <;> decide +kernel

def stem077Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem077_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 14 [2, 6, 14]) b.val = stem077Deg b := by
  rw [degCount_fuel_one leaders 14 [2, 6, 14] stem077Flags stem077_flags b]
  fin_cases b <;> decide +kernel

def stem078Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem078_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [2, 6, 16]) b.val = stem078Deg b := by
  rw [degCount_fuel_one leaders 16 [2, 6, 16] stem078Flags stem078_flags b]
  fin_cases b <;> decide +kernel

def stem079Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem079_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [2, 6, 17]) b.val = stem079Deg b := by
  rw [degCount_fuel_one leaders 17 [2, 6, 17] stem079Flags stem079_flags b]
  fin_cases b <;> decide +kernel

def stem080Deg (b : Fin 5) : ℕ := [0, 3, 0, 0, 0].getD b.val 0

theorem stem080_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 8 [2, 7, 8]) b.val = stem080Deg b := by
  rw [degCount_fuel_one leaders 8 [2, 7, 8] stem080Flags stem080_flags b]
  fin_cases b <;> decide +kernel

def stem081Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem081_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [2, 7, 12]) b.val = stem081Deg b := by
  rw [degCount_fuel_one leaders 12 [2, 7, 12] stem081Flags stem081_flags b]
  fin_cases b <;> decide +kernel

def stem082Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem082_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [2, 7, 16]) b.val = stem082Deg b := by
  rw [degCount_fuel_one leaders 16 [2, 7, 16] stem082Flags stem082_flags b]
  fin_cases b <;> decide +kernel

def stem083Deg (b : Fin 5) : ℕ := [3, 0, 0, 0, 0].getD b.val 0

theorem stem083_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 10 [2, 8, 10]) b.val = stem083Deg b := by
  rw [degCount_fuel_one leaders 10 [2, 8, 10] stem083Flags stem083_flags b]
  fin_cases b <;> decide +kernel

def stem084Deg (b : Fin 5) : ℕ := [3, 0, 0, 0, 0].getD b.val 0

theorem stem084_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [2, 8, 12]) b.val = stem084Deg b := by
  rw [degCount_fuel_one leaders 12 [2, 8, 12] stem084Flags stem084_flags b]
  fin_cases b <;> decide +kernel

def stem085Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem085_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 13 [2, 8, 13]) b.val = stem085Deg b := by
  rw [degCount_fuel_one leaders 13 [2, 8, 13] stem085Flags stem085_flags b]
  fin_cases b <;> decide +kernel

def stem086Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem086_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [2, 8, 16]) b.val = stem086Deg b := by
  rw [degCount_fuel_one leaders 16 [2, 8, 16] stem086Flags stem086_flags b]
  fin_cases b <;> decide +kernel

def stem087Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem087_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [2, 8, 17]) b.val = stem087Deg b := by
  rw [degCount_fuel_one leaders 17 [2, 8, 17] stem087Flags stem087_flags b]
  fin_cases b <;> decide +kernel

def stem088Deg (b : Fin 5) : ℕ := [3, 0, 0, 0, 0].getD b.val 0

theorem stem088_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [2, 10, 12]) b.val = stem088Deg b := by
  rw [degCount_fuel_one leaders 12 [2, 10, 12] stem088Flags stem088_flags b]
  fin_cases b <;> decide +kernel

def stem089Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem089_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 13 [2, 10, 13]) b.val = stem089Deg b := by
  rw [degCount_fuel_one leaders 13 [2, 10, 13] stem089Flags stem089_flags b]
  fin_cases b <;> decide +kernel

def stem090Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem090_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [2, 10, 16]) b.val = stem090Deg b := by
  rw [degCount_fuel_one leaders 16 [2, 10, 16] stem090Flags stem090_flags b]
  fin_cases b <;> decide +kernel

def stem091Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem091_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [2, 10, 17]) b.val = stem091Deg b := by
  rw [degCount_fuel_one leaders 17 [2, 10, 17] stem091Flags stem091_flags b]
  fin_cases b <;> decide +kernel

def stem092Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem092_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [2, 12, 12]) b.val = stem092Deg b := by
  rw [degCount_fuel_one leaders 12 [2, 12, 12] stem092Flags stem092_flags b]
  fin_cases b <;> decide +kernel

def stem093Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem093_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 14 [2, 12, 14]) b.val = stem093Deg b := by
  rw [degCount_fuel_one leaders 14 [2, 12, 14] stem093Flags stem093_flags b]
  fin_cases b <;> decide +kernel

def stem094Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem094_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [2, 12, 16]) b.val = stem094Deg b := by
  rw [degCount_fuel_one leaders 16 [2, 12, 16] stem094Flags stem094_flags b]
  fin_cases b <;> decide +kernel

def stem095Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem095_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [2, 12, 17]) b.val = stem095Deg b := by
  rw [degCount_fuel_one leaders 17 [2, 12, 17] stem095Flags stem095_flags b]
  fin_cases b <;> decide +kernel

def stem096Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem096_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [2, 13, 16]) b.val = stem096Deg b := by
  rw [degCount_fuel_one leaders 16 [2, 13, 16] stem096Flags stem096_flags b]
  fin_cases b <;> decide +kernel

def stem097Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem097_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [2, 14, 16]) b.val = stem097Deg b := by
  rw [degCount_fuel_one leaders 16 [2, 14, 16] stem097Flags stem097_flags b]
  fin_cases b <;> decide +kernel

def stem098Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem098_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [2, 14, 17]) b.val = stem098Deg b := by
  rw [degCount_fuel_one leaders 17 [2, 14, 17] stem098Flags stem098_flags b]
  fin_cases b <;> decide +kernel

def stem099Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem099_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [2, 16, 16]) b.val = stem099Deg b := by
  rw [degCount_fuel_one leaders 16 [2, 16, 16] stem099Flags stem099_flags b]
  fin_cases b <;> decide +kernel

def stem100Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem100_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [2, 16, 17]) b.val = stem100Deg b := by
  rw [degCount_fuel_one leaders 17 [2, 16, 17] stem100Flags stem100_flags b]
  fin_cases b <;> decide +kernel

def stem101Deg (b : Fin 5) : ℕ := [0, 4, 0, 0, 0].getD b.val 0

theorem stem101_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 4 [3, 4, 4]) b.val = stem101Deg b := by
  rw [degCount_fuel_one leaders 4 [3, 4, 4] stem101Flags stem101_flags b]
  fin_cases b <;> decide +kernel

def stem102Deg (b : Fin 5) : ℕ := [0, 7, 0, 0, 0].getD b.val 0

theorem stem102_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 6 [3, 4, 6]) b.val = stem102Deg b := by
  rw [degCount_fuel_one leaders 6 [3, 4, 6] stem102Flags stem102_flags b]
  fin_cases b <;> decide +kernel

def stem103Deg (b : Fin 5) : ℕ := [0, 0, 2, 0, 0].getD b.val 0

theorem stem103_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 7 [3, 4, 7]) b.val = stem103Deg b := by
  rw [degCount_fuel_one leaders 7 [3, 4, 7] stem103Flags stem103_flags b]
  fin_cases b <;> decide +kernel

def stem104Deg (b : Fin 5) : ℕ := [0, 4, 0, 0, 0].getD b.val 0

theorem stem104_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 8 [3, 4, 8]) b.val = stem104Deg b := by
  rw [degCount_fuel_one leaders 8 [3, 4, 8] stem104Flags stem104_flags b]
  fin_cases b <;> decide +kernel

def stem105Deg (b : Fin 5) : ℕ := [0, 3, 0, 0, 0].getD b.val 0

theorem stem105_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 10 [3, 4, 10]) b.val = stem105Deg b := by
  rw [degCount_fuel_one leaders 10 [3, 4, 10] stem105Flags stem105_flags b]
  fin_cases b <;> decide +kernel

def stem106Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem106_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [3, 4, 12]) b.val = stem106Deg b := by
  rw [degCount_fuel_one leaders 12 [3, 4, 12] stem106Flags stem106_flags b]
  fin_cases b <;> decide +kernel

def stem107Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem107_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 14 [3, 4, 14]) b.val = stem107Deg b := by
  rw [degCount_fuel_one leaders 14 [3, 4, 14] stem107Flags stem107_flags b]
  fin_cases b <;> decide +kernel

def stem108Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem108_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [3, 4, 16]) b.val = stem108Deg b := by
  rw [degCount_fuel_one leaders 16 [3, 4, 16] stem108Flags stem108_flags b]
  fin_cases b <;> decide +kernel

def stem109Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem109_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [3, 4, 17]) b.val = stem109Deg b := by
  rw [degCount_fuel_one leaders 17 [3, 4, 17] stem109Flags stem109_flags b]
  fin_cases b <;> decide +kernel

def stem110Deg (b : Fin 5) : ℕ := [0, 0, 2, 0, 0].getD b.val 0

theorem stem110_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 6 [3, 5, 6]) b.val = stem110Deg b := by
  rw [degCount_fuel_one leaders 6 [3, 5, 6] stem110Flags stem110_flags b]
  fin_cases b <;> decide +kernel

def stem111Deg (b : Fin 5) : ℕ := [0, 0, 2, 0, 0].getD b.val 0

theorem stem111_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 10 [3, 5, 10]) b.val = stem111Deg b := by
  rw [degCount_fuel_one leaders 10 [3, 5, 10] stem111Flags stem111_flags b]
  fin_cases b <;> decide +kernel

def stem112Deg (b : Fin 5) : ℕ := [0, 0, 2, 0, 0].getD b.val 0

theorem stem112_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [3, 5, 12]) b.val = stem112Deg b := by
  rw [degCount_fuel_one leaders 12 [3, 5, 12] stem112Flags stem112_flags b]
  fin_cases b <;> decide +kernel

def stem113Deg (b : Fin 5) : ℕ := [0, 0, 2, 0, 0].getD b.val 0

theorem stem113_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [3, 5, 16]) b.val = stem113Deg b := by
  rw [degCount_fuel_one leaders 16 [3, 5, 16] stem113Flags stem113_flags b]
  fin_cases b <;> decide +kernel

def stem114Deg (b : Fin 5) : ℕ := [0, 3, 0, 0, 0].getD b.val 0

theorem stem114_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 6 [3, 6, 6]) b.val = stem114Deg b := by
  rw [degCount_fuel_one leaders 6 [3, 6, 6] stem114Flags stem114_flags b]
  fin_cases b <;> decide +kernel

def stem115Deg (b : Fin 5) : ℕ := [0, 4, 0, 0, 0].getD b.val 0

theorem stem115_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 8 [3, 6, 8]) b.val = stem115Deg b := by
  rw [degCount_fuel_one leaders 8 [3, 6, 8] stem115Flags stem115_flags b]
  fin_cases b <;> decide +kernel

def stem116Deg (b : Fin 5) : ℕ := [0, 3, 0, 0, 0].getD b.val 0

theorem stem116_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 10 [3, 6, 10]) b.val = stem116Deg b := by
  rw [degCount_fuel_one leaders 10 [3, 6, 10] stem116Flags stem116_flags b]
  fin_cases b <;> decide +kernel

def stem117Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem117_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [3, 6, 12]) b.val = stem117Deg b := by
  rw [degCount_fuel_one leaders 12 [3, 6, 12] stem117Flags stem117_flags b]
  fin_cases b <;> decide +kernel

def stem118Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem118_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 14 [3, 6, 14]) b.val = stem118Deg b := by
  rw [degCount_fuel_one leaders 14 [3, 6, 14] stem118Flags stem118_flags b]
  fin_cases b <;> decide +kernel

def stem119Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem119_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [3, 6, 16]) b.val = stem119Deg b := by
  rw [degCount_fuel_one leaders 16 [3, 6, 16] stem119Flags stem119_flags b]
  fin_cases b <;> decide +kernel

def stem120Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem120_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [3, 6, 17]) b.val = stem120Deg b := by
  rw [degCount_fuel_one leaders 17 [3, 6, 17] stem120Flags stem120_flags b]
  fin_cases b <;> decide +kernel

def stem121Deg (b : Fin 5) : ℕ := [0, 0, 3, 0, 0].getD b.val 0

theorem stem121_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 8 [3, 7, 8]) b.val = stem121Deg b := by
  rw [degCount_fuel_one leaders 8 [3, 7, 8] stem121Flags stem121_flags b]
  fin_cases b <;> decide +kernel

def stem122Deg (b : Fin 5) : ℕ := [0, 0, 2, 0, 0].getD b.val 0

theorem stem122_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [3, 7, 12]) b.val = stem122Deg b := by
  rw [degCount_fuel_one leaders 12 [3, 7, 12] stem122Flags stem122_flags b]
  fin_cases b <;> decide +kernel

def stem123Deg (b : Fin 5) : ℕ := [0, 0, 2, 0, 0].getD b.val 0

theorem stem123_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [3, 7, 16]) b.val = stem123Deg b := by
  rw [degCount_fuel_one leaders 16 [3, 7, 16] stem123Flags stem123_flags b]
  fin_cases b <;> decide +kernel

def stem124Deg (b : Fin 5) : ℕ := [0, 3, 0, 0, 0].getD b.val 0

theorem stem124_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 10 [3, 8, 10]) b.val = stem124Deg b := by
  rw [degCount_fuel_one leaders 10 [3, 8, 10] stem124Flags stem124_flags b]
  fin_cases b <;> decide +kernel

def stem125Deg (b : Fin 5) : ℕ := [0, 3, 0, 0, 0].getD b.val 0

theorem stem125_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [3, 8, 12]) b.val = stem125Deg b := by
  rw [degCount_fuel_one leaders 12 [3, 8, 12] stem125Flags stem125_flags b]
  fin_cases b <;> decide +kernel

def stem126Deg (b : Fin 5) : ℕ := [0, 0, 2, 0, 0].getD b.val 0

theorem stem126_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 13 [3, 8, 13]) b.val = stem126Deg b := by
  rw [degCount_fuel_one leaders 13 [3, 8, 13] stem126Flags stem126_flags b]
  fin_cases b <;> decide +kernel

def stem127Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem127_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [3, 8, 16]) b.val = stem127Deg b := by
  rw [degCount_fuel_one leaders 16 [3, 8, 16] stem127Flags stem127_flags b]
  fin_cases b <;> decide +kernel

def stem128Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem128_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [3, 8, 17]) b.val = stem128Deg b := by
  rw [degCount_fuel_one leaders 17 [3, 8, 17] stem128Flags stem128_flags b]
  fin_cases b <;> decide +kernel

def stem129Deg (b : Fin 5) : ℕ := [0, 3, 0, 0, 0].getD b.val 0

theorem stem129_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [3, 10, 12]) b.val = stem129Deg b := by
  rw [degCount_fuel_one leaders 12 [3, 10, 12] stem129Flags stem129_flags b]
  fin_cases b <;> decide +kernel

def stem130Deg (b : Fin 5) : ℕ := [0, 0, 2, 0, 0].getD b.val 0

theorem stem130_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 13 [3, 10, 13]) b.val = stem130Deg b := by
  rw [degCount_fuel_one leaders 13 [3, 10, 13] stem130Flags stem130_flags b]
  fin_cases b <;> decide +kernel

def stem131Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem131_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [3, 10, 16]) b.val = stem131Deg b := by
  rw [degCount_fuel_one leaders 16 [3, 10, 16] stem131Flags stem131_flags b]
  fin_cases b <;> decide +kernel

def stem132Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem132_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [3, 10, 17]) b.val = stem132Deg b := by
  rw [degCount_fuel_one leaders 17 [3, 10, 17] stem132Flags stem132_flags b]
  fin_cases b <;> decide +kernel

def stem133Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem133_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [3, 12, 12]) b.val = stem133Deg b := by
  rw [degCount_fuel_one leaders 12 [3, 12, 12] stem133Flags stem133_flags b]
  fin_cases b <;> decide +kernel

def stem134Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem134_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 14 [3, 12, 14]) b.val = stem134Deg b := by
  rw [degCount_fuel_one leaders 14 [3, 12, 14] stem134Flags stem134_flags b]
  fin_cases b <;> decide +kernel

def stem135Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem135_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [3, 12, 16]) b.val = stem135Deg b := by
  rw [degCount_fuel_one leaders 16 [3, 12, 16] stem135Flags stem135_flags b]
  fin_cases b <;> decide +kernel

def stem136Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem136_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [3, 12, 17]) b.val = stem136Deg b := by
  rw [degCount_fuel_one leaders 17 [3, 12, 17] stem136Flags stem136_flags b]
  fin_cases b <;> decide +kernel

def stem137Deg (b : Fin 5) : ℕ := [0, 0, 2, 0, 0].getD b.val 0

theorem stem137_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [3, 13, 16]) b.val = stem137Deg b := by
  rw [degCount_fuel_one leaders 16 [3, 13, 16] stem137Flags stem137_flags b]
  fin_cases b <;> decide +kernel

def stem138Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem138_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [3, 14, 16]) b.val = stem138Deg b := by
  rw [degCount_fuel_one leaders 16 [3, 14, 16] stem138Flags stem138_flags b]
  fin_cases b <;> decide +kernel

def stem139Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem139_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [3, 14, 17]) b.val = stem139Deg b := by
  rw [degCount_fuel_one leaders 17 [3, 14, 17] stem139Flags stem139_flags b]
  fin_cases b <;> decide +kernel

end VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Count.stem139_dcount
