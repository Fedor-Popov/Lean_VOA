import VOA.DeligneAudit.D4FusionContactAllMModelDegreeTwoCountCore
import Mathlib.Tactic.FinCases

/-! Current-degree counts of the m=2 normal-word stems 0..69, reusing the
kernel-checked stem flags of the length cascade (generated certificate). -/
namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

set_option maxRecDepth 100000

def stem000Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem000_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [0, 0, 16]) b.val = stem000Deg b := by
  rw [degCount_fuel_one leaders 16 [0, 0, 16] stem000Flags stem000_flags b]
  fin_cases b <;> decide +kernel

def stem001Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem001_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [0, 0, 17]) b.val = stem001Deg b := by
  rw [degCount_fuel_one leaders 17 [0, 0, 17] stem001Flags stem001_flags b]
  fin_cases b <;> decide +kernel

def stem002Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem002_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 4 [0, 2, 4]) b.val = stem002Deg b := by
  rw [degCount_fuel_one leaders 4 [0, 2, 4] stem002Flags stem002_flags b]
  fin_cases b <;> decide +kernel

def stem003Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem003_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 6 [0, 2, 6]) b.val = stem003Deg b := by
  rw [degCount_fuel_one leaders 6 [0, 2, 6] stem003Flags stem003_flags b]
  fin_cases b <;> decide +kernel

def stem004Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem004_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [0, 2, 12]) b.val = stem004Deg b := by
  rw [degCount_fuel_one leaders 12 [0, 2, 12] stem004Flags stem004_flags b]
  fin_cases b <;> decide +kernel

def stem005Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem005_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [0, 2, 16]) b.val = stem005Deg b := by
  rw [degCount_fuel_one leaders 16 [0, 2, 16] stem005Flags stem005_flags b]
  fin_cases b <;> decide +kernel

def stem006Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem006_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [0, 2, 17]) b.val = stem006Deg b := by
  rw [degCount_fuel_one leaders 17 [0, 2, 17] stem006Flags stem006_flags b]
  fin_cases b <;> decide +kernel

def stem007Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem007_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 6 [0, 4, 6]) b.val = stem007Deg b := by
  rw [degCount_fuel_one leaders 6 [0, 4, 6] stem007Flags stem007_flags b]
  fin_cases b <;> decide +kernel

def stem008Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem008_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 10 [0, 4, 10]) b.val = stem008Deg b := by
  rw [degCount_fuel_one leaders 10 [0, 4, 10] stem008Flags stem008_flags b]
  fin_cases b <;> decide +kernel

def stem009Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem009_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [0, 4, 16]) b.val = stem009Deg b := by
  rw [degCount_fuel_one leaders 16 [0, 4, 16] stem009Flags stem009_flags b]
  fin_cases b <;> decide +kernel

def stem010Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem010_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [0, 4, 17]) b.val = stem010Deg b := by
  rw [degCount_fuel_one leaders 17 [0, 4, 17] stem010Flags stem010_flags b]
  fin_cases b <;> decide +kernel

def stem011Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem011_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 8 [0, 6, 8]) b.val = stem011Deg b := by
  rw [degCount_fuel_one leaders 8 [0, 6, 8] stem011Flags stem011_flags b]
  fin_cases b <;> decide +kernel

def stem012Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem012_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [0, 6, 16]) b.val = stem012Deg b := by
  rw [degCount_fuel_one leaders 16 [0, 6, 16] stem012Flags stem012_flags b]
  fin_cases b <;> decide +kernel

def stem013Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem013_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [0, 6, 17]) b.val = stem013Deg b := by
  rw [degCount_fuel_one leaders 17 [0, 6, 17] stem013Flags stem013_flags b]
  fin_cases b <;> decide +kernel

def stem014Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem014_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 10 [0, 8, 10]) b.val = stem014Deg b := by
  rw [degCount_fuel_one leaders 10 [0, 8, 10] stem014Flags stem014_flags b]
  fin_cases b <;> decide +kernel

def stem015Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem015_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [0, 8, 12]) b.val = stem015Deg b := by
  rw [degCount_fuel_one leaders 12 [0, 8, 12] stem015Flags stem015_flags b]
  fin_cases b <;> decide +kernel

def stem016Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem016_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [0, 8, 16]) b.val = stem016Deg b := by
  rw [degCount_fuel_one leaders 16 [0, 8, 16] stem016Flags stem016_flags b]
  fin_cases b <;> decide +kernel

def stem017Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem017_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [0, 8, 17]) b.val = stem017Deg b := by
  rw [degCount_fuel_one leaders 17 [0, 8, 17] stem017Flags stem017_flags b]
  fin_cases b <;> decide +kernel

def stem018Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem018_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [0, 10, 12]) b.val = stem018Deg b := by
  rw [degCount_fuel_one leaders 12 [0, 10, 12] stem018Flags stem018_flags b]
  fin_cases b <;> decide +kernel

def stem019Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem019_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [0, 10, 16]) b.val = stem019Deg b := by
  rw [degCount_fuel_one leaders 16 [0, 10, 16] stem019Flags stem019_flags b]
  fin_cases b <;> decide +kernel

def stem020Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem020_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [0, 10, 17]) b.val = stem020Deg b := by
  rw [degCount_fuel_one leaders 17 [0, 10, 17] stem020Flags stem020_flags b]
  fin_cases b <;> decide +kernel

def stem021Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem021_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [0, 12, 16]) b.val = stem021Deg b := by
  rw [degCount_fuel_one leaders 16 [0, 12, 16] stem021Flags stem021_flags b]
  fin_cases b <;> decide +kernel

def stem022Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem022_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [0, 12, 17]) b.val = stem022Deg b := by
  rw [degCount_fuel_one leaders 17 [0, 12, 17] stem022Flags stem022_flags b]
  fin_cases b <;> decide +kernel

def stem023Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem023_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [0, 14, 16]) b.val = stem023Deg b := by
  rw [degCount_fuel_one leaders 16 [0, 14, 16] stem023Flags stem023_flags b]
  fin_cases b <;> decide +kernel

def stem024Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem024_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [0, 14, 17]) b.val = stem024Deg b := by
  rw [degCount_fuel_one leaders 17 [0, 14, 17] stem024Flags stem024_flags b]
  fin_cases b <;> decide +kernel

def stem025Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem025_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [0, 16, 16]) b.val = stem025Deg b := by
  rw [degCount_fuel_one leaders 16 [0, 16, 16] stem025Flags stem025_flags b]
  fin_cases b <;> decide +kernel

def stem026Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem026_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [0, 16, 17]) b.val = stem026Deg b := by
  rw [degCount_fuel_one leaders 17 [0, 16, 17] stem026Flags stem026_flags b]
  fin_cases b <;> decide +kernel

def stem027Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem027_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 4 [1, 2, 4]) b.val = stem027Deg b := by
  rw [degCount_fuel_one leaders 4 [1, 2, 4] stem027Flags stem027_flags b]
  fin_cases b <;> decide +kernel

def stem028Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem028_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 6 [1, 2, 6]) b.val = stem028Deg b := by
  rw [degCount_fuel_one leaders 6 [1, 2, 6] stem028Flags stem028_flags b]
  fin_cases b <;> decide +kernel

def stem029Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem029_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [1, 2, 12]) b.val = stem029Deg b := by
  rw [degCount_fuel_one leaders 12 [1, 2, 12] stem029Flags stem029_flags b]
  fin_cases b <;> decide +kernel

def stem030Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem030_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [1, 2, 16]) b.val = stem030Deg b := by
  rw [degCount_fuel_one leaders 16 [1, 2, 16] stem030Flags stem030_flags b]
  fin_cases b <;> decide +kernel

def stem031Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem031_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [1, 2, 17]) b.val = stem031Deg b := by
  rw [degCount_fuel_one leaders 17 [1, 2, 17] stem031Flags stem031_flags b]
  fin_cases b <;> decide +kernel

def stem032Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem032_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 6 [1, 4, 6]) b.val = stem032Deg b := by
  rw [degCount_fuel_one leaders 6 [1, 4, 6] stem032Flags stem032_flags b]
  fin_cases b <;> decide +kernel

def stem033Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem033_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 10 [1, 4, 10]) b.val = stem033Deg b := by
  rw [degCount_fuel_one leaders 10 [1, 4, 10] stem033Flags stem033_flags b]
  fin_cases b <;> decide +kernel

def stem034Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem034_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [1, 4, 16]) b.val = stem034Deg b := by
  rw [degCount_fuel_one leaders 16 [1, 4, 16] stem034Flags stem034_flags b]
  fin_cases b <;> decide +kernel

def stem035Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem035_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [1, 4, 17]) b.val = stem035Deg b := by
  rw [degCount_fuel_one leaders 17 [1, 4, 17] stem035Flags stem035_flags b]
  fin_cases b <;> decide +kernel

def stem036Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem036_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 8 [1, 6, 8]) b.val = stem036Deg b := by
  rw [degCount_fuel_one leaders 8 [1, 6, 8] stem036Flags stem036_flags b]
  fin_cases b <;> decide +kernel

def stem037Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem037_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [1, 6, 16]) b.val = stem037Deg b := by
  rw [degCount_fuel_one leaders 16 [1, 6, 16] stem037Flags stem037_flags b]
  fin_cases b <;> decide +kernel

def stem038Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem038_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [1, 6, 17]) b.val = stem038Deg b := by
  rw [degCount_fuel_one leaders 17 [1, 6, 17] stem038Flags stem038_flags b]
  fin_cases b <;> decide +kernel

def stem039Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem039_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 10 [1, 8, 10]) b.val = stem039Deg b := by
  rw [degCount_fuel_one leaders 10 [1, 8, 10] stem039Flags stem039_flags b]
  fin_cases b <;> decide +kernel

def stem040Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem040_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [1, 8, 12]) b.val = stem040Deg b := by
  rw [degCount_fuel_one leaders 12 [1, 8, 12] stem040Flags stem040_flags b]
  fin_cases b <;> decide +kernel

def stem041Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem041_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [1, 8, 16]) b.val = stem041Deg b := by
  rw [degCount_fuel_one leaders 16 [1, 8, 16] stem041Flags stem041_flags b]
  fin_cases b <;> decide +kernel

def stem042Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem042_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [1, 8, 17]) b.val = stem042Deg b := by
  rw [degCount_fuel_one leaders 17 [1, 8, 17] stem042Flags stem042_flags b]
  fin_cases b <;> decide +kernel

def stem043Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem043_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [1, 10, 12]) b.val = stem043Deg b := by
  rw [degCount_fuel_one leaders 12 [1, 10, 12] stem043Flags stem043_flags b]
  fin_cases b <;> decide +kernel

def stem044Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem044_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [1, 10, 16]) b.val = stem044Deg b := by
  rw [degCount_fuel_one leaders 16 [1, 10, 16] stem044Flags stem044_flags b]
  fin_cases b <;> decide +kernel

def stem045Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem045_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [1, 10, 17]) b.val = stem045Deg b := by
  rw [degCount_fuel_one leaders 17 [1, 10, 17] stem045Flags stem045_flags b]
  fin_cases b <;> decide +kernel

def stem046Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem046_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [1, 12, 16]) b.val = stem046Deg b := by
  rw [degCount_fuel_one leaders 16 [1, 12, 16] stem046Flags stem046_flags b]
  fin_cases b <;> decide +kernel

def stem047Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem047_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [1, 12, 17]) b.val = stem047Deg b := by
  rw [degCount_fuel_one leaders 17 [1, 12, 17] stem047Flags stem047_flags b]
  fin_cases b <;> decide +kernel

def stem048Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem048_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [1, 14, 16]) b.val = stem048Deg b := by
  rw [degCount_fuel_one leaders 16 [1, 14, 16] stem048Flags stem048_flags b]
  fin_cases b <;> decide +kernel

def stem049Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem049_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [1, 14, 17]) b.val = stem049Deg b := by
  rw [degCount_fuel_one leaders 17 [1, 14, 17] stem049Flags stem049_flags b]
  fin_cases b <;> decide +kernel

def stem050Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem050_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [1, 16, 16]) b.val = stem050Deg b := by
  rw [degCount_fuel_one leaders 16 [1, 16, 16] stem050Flags stem050_flags b]
  fin_cases b <;> decide +kernel

def stem051Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem051_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [1, 16, 17]) b.val = stem051Deg b := by
  rw [degCount_fuel_one leaders 17 [1, 16, 17] stem051Flags stem051_flags b]
  fin_cases b <;> decide +kernel

def stem052Deg (b : Fin 5) : ℕ := [5, 0, 0, 0, 0].getD b.val 0

theorem stem052_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 4 [2, 2, 4]) b.val = stem052Deg b := by
  rw [degCount_fuel_one leaders 4 [2, 2, 4] stem052Flags stem052_flags b]
  fin_cases b <;> decide +kernel

def stem053Deg (b : Fin 5) : ℕ := [0, 4, 0, 0, 0].getD b.val 0

theorem stem053_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 5 [2, 2, 5]) b.val = stem053Deg b := by
  rw [degCount_fuel_one leaders 5 [2, 2, 5] stem053Flags stem053_flags b]
  fin_cases b <;> decide +kernel

def stem054Deg (b : Fin 5) : ℕ := [4, 0, 0, 0, 0].getD b.val 0

theorem stem054_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 6 [2, 2, 6]) b.val = stem054Deg b := by
  rw [degCount_fuel_one leaders 6 [2, 2, 6] stem054Flags stem054_flags b]
  fin_cases b <;> decide +kernel

def stem055Deg (b : Fin 5) : ℕ := [0, 3, 0, 0, 0].getD b.val 0

theorem stem055_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 7 [2, 2, 7]) b.val = stem055Deg b := by
  rw [degCount_fuel_one leaders 7 [2, 2, 7] stem055Flags stem055_flags b]
  fin_cases b <;> decide +kernel

def stem056Deg (b : Fin 5) : ℕ := [3, 0, 0, 0, 0].getD b.val 0

theorem stem056_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [2, 2, 12]) b.val = stem056Deg b := by
  rw [degCount_fuel_one leaders 12 [2, 2, 12] stem056Flags stem056_flags b]
  fin_cases b <;> decide +kernel

def stem057Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem057_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 13 [2, 2, 13]) b.val = stem057Deg b := by
  rw [degCount_fuel_one leaders 13 [2, 2, 13] stem057Flags stem057_flags b]
  fin_cases b <;> decide +kernel

def stem058Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem058_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [2, 2, 16]) b.val = stem058Deg b := by
  rw [degCount_fuel_one leaders 16 [2, 2, 16] stem058Flags stem058_flags b]
  fin_cases b <;> decide +kernel

def stem059Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem059_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [2, 2, 17]) b.val = stem059Deg b := by
  rw [degCount_fuel_one leaders 17 [2, 2, 17] stem059Flags stem059_flags b]
  fin_cases b <;> decide +kernel

def stem060Deg (b : Fin 5) : ℕ := [4, 0, 0, 0, 0].getD b.val 0

theorem stem060_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 4 [2, 4, 4]) b.val = stem060Deg b := by
  rw [degCount_fuel_one leaders 4 [2, 4, 4] stem060Flags stem060_flags b]
  fin_cases b <;> decide +kernel

def stem061Deg (b : Fin 5) : ℕ := [7, 0, 0, 0, 0].getD b.val 0

theorem stem061_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 6 [2, 4, 6]) b.val = stem061Deg b := by
  rw [degCount_fuel_one leaders 6 [2, 4, 6] stem061Flags stem061_flags b]
  fin_cases b <;> decide +kernel

def stem062Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem062_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 7 [2, 4, 7]) b.val = stem062Deg b := by
  rw [degCount_fuel_one leaders 7 [2, 4, 7] stem062Flags stem062_flags b]
  fin_cases b <;> decide +kernel

def stem063Deg (b : Fin 5) : ℕ := [4, 0, 0, 0, 0].getD b.val 0

theorem stem063_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 8 [2, 4, 8]) b.val = stem063Deg b := by
  rw [degCount_fuel_one leaders 8 [2, 4, 8] stem063Flags stem063_flags b]
  fin_cases b <;> decide +kernel

def stem064Deg (b : Fin 5) : ℕ := [3, 0, 0, 0, 0].getD b.val 0

theorem stem064_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 10 [2, 4, 10]) b.val = stem064Deg b := by
  rw [degCount_fuel_one leaders 10 [2, 4, 10] stem064Flags stem064_flags b]
  fin_cases b <;> decide +kernel

def stem065Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem065_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [2, 4, 12]) b.val = stem065Deg b := by
  rw [degCount_fuel_one leaders 12 [2, 4, 12] stem065Flags stem065_flags b]
  fin_cases b <;> decide +kernel

def stem066Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem066_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 14 [2, 4, 14]) b.val = stem066Deg b := by
  rw [degCount_fuel_one leaders 14 [2, 4, 14] stem066Flags stem066_flags b]
  fin_cases b <;> decide +kernel

def stem067Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem067_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [2, 4, 16]) b.val = stem067Deg b := by
  rw [degCount_fuel_one leaders 16 [2, 4, 16] stem067Flags stem067_flags b]
  fin_cases b <;> decide +kernel

def stem068Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem068_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [2, 4, 17]) b.val = stem068Deg b := by
  rw [degCount_fuel_one leaders 17 [2, 4, 17] stem068Flags stem068_flags b]
  fin_cases b <;> decide +kernel

def stem069Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem069_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 6 [2, 5, 6]) b.val = stem069Deg b := by
  rw [degCount_fuel_one leaders 6 [2, 5, 6] stem069Flags stem069_flags b]
  fin_cases b <;> decide +kernel

end VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Count.stem069_dcount
