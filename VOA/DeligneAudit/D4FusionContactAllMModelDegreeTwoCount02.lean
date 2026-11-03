import VOA.DeligneAudit.D4FusionContactAllMModelDegreeTwoCount01
import Mathlib.Tactic.FinCases

/-! Current-degree counts of the m=2 normal-word stems 140..209, reusing the
kernel-checked stem flags of the length cascade (generated certificate). -/
namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

set_option maxRecDepth 100000

def stem140Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem140_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [3, 16, 16]) b.val = stem140Deg b := by
  rw [degCount_fuel_one leaders 16 [3, 16, 16] stem140Flags stem140_flags b]
  fin_cases b <;> decide +kernel

def stem141Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem141_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [3, 16, 17]) b.val = stem141Deg b := by
  rw [degCount_fuel_one leaders 17 [3, 16, 17] stem141Flags stem141_flags b]
  fin_cases b <;> decide +kernel

def stem142Deg (b : Fin 5) : ℕ := [4, 0, 0, 0, 0].getD b.val 0

theorem stem142_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 6 [4, 4, 6]) b.val = stem142Deg b := by
  rw [degCount_fuel_one leaders 6 [4, 4, 6] stem142Flags stem142_flags b]
  fin_cases b <;> decide +kernel

def stem143Deg (b : Fin 5) : ℕ := [0, 3, 0, 0, 0].getD b.val 0

theorem stem143_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 7 [4, 4, 7]) b.val = stem143Deg b := by
  rw [degCount_fuel_one leaders 7 [4, 4, 7] stem143Flags stem143_flags b]
  fin_cases b <;> decide +kernel

def stem144Deg (b : Fin 5) : ℕ := [3, 0, 0, 0, 0].getD b.val 0

theorem stem144_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 10 [4, 4, 10]) b.val = stem144Deg b := by
  rw [degCount_fuel_one leaders 10 [4, 4, 10] stem144Flags stem144_flags b]
  fin_cases b <;> decide +kernel

def stem145Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem145_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 11 [4, 4, 11]) b.val = stem145Deg b := by
  rw [degCount_fuel_one leaders 11 [4, 4, 11] stem145Flags stem145_flags b]
  fin_cases b <;> decide +kernel

def stem146Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem146_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [4, 4, 16]) b.val = stem146Deg b := by
  rw [degCount_fuel_one leaders 16 [4, 4, 16] stem146Flags stem146_flags b]
  fin_cases b <;> decide +kernel

def stem147Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem147_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [4, 4, 17]) b.val = stem147Deg b := by
  rw [degCount_fuel_one leaders 17 [4, 4, 17] stem147Flags stem147_flags b]
  fin_cases b <;> decide +kernel

def stem148Deg (b : Fin 5) : ℕ := [3, 0, 0, 0, 0].getD b.val 0

theorem stem148_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 6 [4, 6, 6]) b.val = stem148Deg b := by
  rw [degCount_fuel_one leaders 6 [4, 6, 6] stem148Flags stem148_flags b]
  fin_cases b <;> decide +kernel

def stem149Deg (b : Fin 5) : ℕ := [4, 0, 0, 0, 0].getD b.val 0

theorem stem149_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 8 [4, 6, 8]) b.val = stem149Deg b := by
  rw [degCount_fuel_one leaders 8 [4, 6, 8] stem149Flags stem149_flags b]
  fin_cases b <;> decide +kernel

def stem150Deg (b : Fin 5) : ℕ := [3, 0, 0, 0, 0].getD b.val 0

theorem stem150_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 10 [4, 6, 10]) b.val = stem150Deg b := by
  rw [degCount_fuel_one leaders 10 [4, 6, 10] stem150Flags stem150_flags b]
  fin_cases b <;> decide +kernel

def stem151Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem151_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [4, 6, 12]) b.val = stem151Deg b := by
  rw [degCount_fuel_one leaders 12 [4, 6, 12] stem151Flags stem151_flags b]
  fin_cases b <;> decide +kernel

def stem152Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem152_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 14 [4, 6, 14]) b.val = stem152Deg b := by
  rw [degCount_fuel_one leaders 14 [4, 6, 14] stem152Flags stem152_flags b]
  fin_cases b <;> decide +kernel

def stem153Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem153_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [4, 6, 16]) b.val = stem153Deg b := by
  rw [degCount_fuel_one leaders 16 [4, 6, 16] stem153Flags stem153_flags b]
  fin_cases b <;> decide +kernel

def stem154Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem154_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [4, 6, 17]) b.val = stem154Deg b := by
  rw [degCount_fuel_one leaders 17 [4, 6, 17] stem154Flags stem154_flags b]
  fin_cases b <;> decide +kernel

def stem155Deg (b : Fin 5) : ℕ := [0, 3, 0, 0, 0].getD b.val 0

theorem stem155_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 8 [4, 7, 8]) b.val = stem155Deg b := by
  rw [degCount_fuel_one leaders 8 [4, 7, 8] stem155Flags stem155_flags b]
  fin_cases b <;> decide +kernel

def stem156Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem156_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 10 [4, 7, 10]) b.val = stem156Deg b := by
  rw [degCount_fuel_one leaders 10 [4, 7, 10] stem156Flags stem156_flags b]
  fin_cases b <;> decide +kernel

def stem157Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem157_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [4, 7, 16]) b.val = stem157Deg b := by
  rw [degCount_fuel_one leaders 16 [4, 7, 16] stem157Flags stem157_flags b]
  fin_cases b <;> decide +kernel

def stem158Deg (b : Fin 5) : ℕ := [4, 0, 0, 0, 0].getD b.val 0

theorem stem158_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 10 [4, 8, 10]) b.val = stem158Deg b := by
  rw [degCount_fuel_one leaders 10 [4, 8, 10] stem158Flags stem158_flags b]
  fin_cases b <;> decide +kernel

def stem159Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem159_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 11 [4, 8, 11]) b.val = stem159Deg b := by
  rw [degCount_fuel_one leaders 11 [4, 8, 11] stem159Flags stem159_flags b]
  fin_cases b <;> decide +kernel

def stem160Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem160_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [4, 8, 12]) b.val = stem160Deg b := by
  rw [degCount_fuel_one leaders 12 [4, 8, 12] stem160Flags stem160_flags b]
  fin_cases b <;> decide +kernel

def stem161Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem161_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [4, 8, 16]) b.val = stem161Deg b := by
  rw [degCount_fuel_one leaders 16 [4, 8, 16] stem161Flags stem161_flags b]
  fin_cases b <;> decide +kernel

def stem162Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem162_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [4, 8, 17]) b.val = stem162Deg b := by
  rw [degCount_fuel_one leaders 17 [4, 8, 17] stem162Flags stem162_flags b]
  fin_cases b <;> decide +kernel

def stem163Deg (b : Fin 5) : ℕ := [3, 0, 0, 0, 0].getD b.val 0

theorem stem163_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 10 [4, 10, 10]) b.val = stem163Deg b := by
  rw [degCount_fuel_one leaders 10 [4, 10, 10] stem163Flags stem163_flags b]
  fin_cases b <;> decide +kernel

def stem164Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem164_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [4, 10, 12]) b.val = stem164Deg b := by
  rw [degCount_fuel_one leaders 12 [4, 10, 12] stem164Flags stem164_flags b]
  fin_cases b <;> decide +kernel

def stem165Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem165_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 14 [4, 10, 14]) b.val = stem165Deg b := by
  rw [degCount_fuel_one leaders 14 [4, 10, 14] stem165Flags stem165_flags b]
  fin_cases b <;> decide +kernel

def stem166Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem166_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [4, 10, 16]) b.val = stem166Deg b := by
  rw [degCount_fuel_one leaders 16 [4, 10, 16] stem166Flags stem166_flags b]
  fin_cases b <;> decide +kernel

def stem167Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem167_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [4, 10, 17]) b.val = stem167Deg b := by
  rw [degCount_fuel_one leaders 17 [4, 10, 17] stem167Flags stem167_flags b]
  fin_cases b <;> decide +kernel

def stem168Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem168_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [4, 11, 12]) b.val = stem168Deg b := by
  rw [degCount_fuel_one leaders 12 [4, 11, 12] stem168Flags stem168_flags b]
  fin_cases b <;> decide +kernel

def stem169Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem169_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [4, 11, 16]) b.val = stem169Deg b := by
  rw [degCount_fuel_one leaders 16 [4, 11, 16] stem169Flags stem169_flags b]
  fin_cases b <;> decide +kernel

def stem170Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem170_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [4, 12, 16]) b.val = stem170Deg b := by
  rw [degCount_fuel_one leaders 16 [4, 12, 16] stem170Flags stem170_flags b]
  fin_cases b <;> decide +kernel

def stem171Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem171_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [4, 12, 17]) b.val = stem171Deg b := by
  rw [degCount_fuel_one leaders 17 [4, 12, 17] stem171Flags stem171_flags b]
  fin_cases b <;> decide +kernel

def stem172Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem172_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [4, 14, 16]) b.val = stem172Deg b := by
  rw [degCount_fuel_one leaders 16 [4, 14, 16] stem172Flags stem172_flags b]
  fin_cases b <;> decide +kernel

def stem173Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem173_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [4, 14, 17]) b.val = stem173Deg b := by
  rw [degCount_fuel_one leaders 17 [4, 14, 17] stem173Flags stem173_flags b]
  fin_cases b <;> decide +kernel

def stem174Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem174_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [4, 16, 16]) b.val = stem174Deg b := by
  rw [degCount_fuel_one leaders 16 [4, 16, 16] stem174Flags stem174_flags b]
  fin_cases b <;> decide +kernel

def stem175Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem175_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [4, 16, 17]) b.val = stem175Deg b := by
  rw [degCount_fuel_one leaders 17 [4, 16, 17] stem175Flags stem175_flags b]
  fin_cases b <;> decide +kernel

def stem176Deg (b : Fin 5) : ℕ := [0, 3, 0, 0, 0].getD b.val 0

theorem stem176_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 6 [5, 6, 6]) b.val = stem176Deg b := by
  rw [degCount_fuel_one leaders 6 [5, 6, 6] stem176Flags stem176_flags b]
  fin_cases b <;> decide +kernel

def stem177Deg (b : Fin 5) : ℕ := [0, 4, 0, 0, 0].getD b.val 0

theorem stem177_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 8 [5, 6, 8]) b.val = stem177Deg b := by
  rw [degCount_fuel_one leaders 8 [5, 6, 8] stem177Flags stem177_flags b]
  fin_cases b <;> decide +kernel

def stem178Deg (b : Fin 5) : ℕ := [0, 3, 0, 0, 0].getD b.val 0

theorem stem178_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 10 [5, 6, 10]) b.val = stem178Deg b := by
  rw [degCount_fuel_one leaders 10 [5, 6, 10] stem178Flags stem178_flags b]
  fin_cases b <;> decide +kernel

def stem179Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem179_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [5, 6, 12]) b.val = stem179Deg b := by
  rw [degCount_fuel_one leaders 12 [5, 6, 12] stem179Flags stem179_flags b]
  fin_cases b <;> decide +kernel

def stem180Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem180_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 14 [5, 6, 14]) b.val = stem180Deg b := by
  rw [degCount_fuel_one leaders 14 [5, 6, 14] stem180Flags stem180_flags b]
  fin_cases b <;> decide +kernel

def stem181Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem181_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [5, 6, 16]) b.val = stem181Deg b := by
  rw [degCount_fuel_one leaders 16 [5, 6, 16] stem181Flags stem181_flags b]
  fin_cases b <;> decide +kernel

def stem182Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem182_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [5, 6, 17]) b.val = stem182Deg b := by
  rw [degCount_fuel_one leaders 17 [5, 6, 17] stem182Flags stem182_flags b]
  fin_cases b <;> decide +kernel

def stem183Deg (b : Fin 5) : ℕ := [0, 0, 3, 0, 0].getD b.val 0

theorem stem183_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 8 [5, 7, 8]) b.val = stem183Deg b := by
  rw [degCount_fuel_one leaders 8 [5, 7, 8] stem183Flags stem183_flags b]
  fin_cases b <;> decide +kernel

def stem184Deg (b : Fin 5) : ℕ := [0, 0, 2, 0, 0].getD b.val 0

theorem stem184_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 10 [5, 7, 10]) b.val = stem184Deg b := by
  rw [degCount_fuel_one leaders 10 [5, 7, 10] stem184Flags stem184_flags b]
  fin_cases b <;> decide +kernel

def stem185Deg (b : Fin 5) : ℕ := [0, 0, 2, 0, 0].getD b.val 0

theorem stem185_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [5, 7, 16]) b.val = stem185Deg b := by
  rw [degCount_fuel_one leaders 16 [5, 7, 16] stem185Flags stem185_flags b]
  fin_cases b <;> decide +kernel

def stem186Deg (b : Fin 5) : ℕ := [0, 4, 0, 0, 0].getD b.val 0

theorem stem186_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 10 [5, 8, 10]) b.val = stem186Deg b := by
  rw [degCount_fuel_one leaders 10 [5, 8, 10] stem186Flags stem186_flags b]
  fin_cases b <;> decide +kernel

def stem187Deg (b : Fin 5) : ℕ := [0, 0, 2, 0, 0].getD b.val 0

theorem stem187_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 11 [5, 8, 11]) b.val = stem187Deg b := by
  rw [degCount_fuel_one leaders 11 [5, 8, 11] stem187Flags stem187_flags b]
  fin_cases b <;> decide +kernel

def stem188Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem188_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [5, 8, 12]) b.val = stem188Deg b := by
  rw [degCount_fuel_one leaders 12 [5, 8, 12] stem188Flags stem188_flags b]
  fin_cases b <;> decide +kernel

def stem189Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem189_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [5, 8, 16]) b.val = stem189Deg b := by
  rw [degCount_fuel_one leaders 16 [5, 8, 16] stem189Flags stem189_flags b]
  fin_cases b <;> decide +kernel

def stem190Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem190_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [5, 8, 17]) b.val = stem190Deg b := by
  rw [degCount_fuel_one leaders 17 [5, 8, 17] stem190Flags stem190_flags b]
  fin_cases b <;> decide +kernel

def stem191Deg (b : Fin 5) : ℕ := [0, 3, 0, 0, 0].getD b.val 0

theorem stem191_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 10 [5, 10, 10]) b.val = stem191Deg b := by
  rw [degCount_fuel_one leaders 10 [5, 10, 10] stem191Flags stem191_flags b]
  fin_cases b <;> decide +kernel

def stem192Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem192_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [5, 10, 12]) b.val = stem192Deg b := by
  rw [degCount_fuel_one leaders 12 [5, 10, 12] stem192Flags stem192_flags b]
  fin_cases b <;> decide +kernel

def stem193Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem193_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 14 [5, 10, 14]) b.val = stem193Deg b := by
  rw [degCount_fuel_one leaders 14 [5, 10, 14] stem193Flags stem193_flags b]
  fin_cases b <;> decide +kernel

def stem194Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem194_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [5, 10, 16]) b.val = stem194Deg b := by
  rw [degCount_fuel_one leaders 16 [5, 10, 16] stem194Flags stem194_flags b]
  fin_cases b <;> decide +kernel

def stem195Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem195_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [5, 10, 17]) b.val = stem195Deg b := by
  rw [degCount_fuel_one leaders 17 [5, 10, 17] stem195Flags stem195_flags b]
  fin_cases b <;> decide +kernel

def stem196Deg (b : Fin 5) : ℕ := [0, 0, 2, 0, 0].getD b.val 0

theorem stem196_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [5, 11, 12]) b.val = stem196Deg b := by
  rw [degCount_fuel_one leaders 12 [5, 11, 12] stem196Flags stem196_flags b]
  fin_cases b <;> decide +kernel

def stem197Deg (b : Fin 5) : ℕ := [0, 0, 2, 0, 0].getD b.val 0

theorem stem197_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [5, 11, 16]) b.val = stem197Deg b := by
  rw [degCount_fuel_one leaders 16 [5, 11, 16] stem197Flags stem197_flags b]
  fin_cases b <;> decide +kernel

def stem198Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem198_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [5, 12, 16]) b.val = stem198Deg b := by
  rw [degCount_fuel_one leaders 16 [5, 12, 16] stem198Flags stem198_flags b]
  fin_cases b <;> decide +kernel

def stem199Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem199_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [5, 12, 17]) b.val = stem199Deg b := by
  rw [degCount_fuel_one leaders 17 [5, 12, 17] stem199Flags stem199_flags b]
  fin_cases b <;> decide +kernel

def stem200Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem200_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [5, 14, 16]) b.val = stem200Deg b := by
  rw [degCount_fuel_one leaders 16 [5, 14, 16] stem200Flags stem200_flags b]
  fin_cases b <;> decide +kernel

def stem201Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem201_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [5, 14, 17]) b.val = stem201Deg b := by
  rw [degCount_fuel_one leaders 17 [5, 14, 17] stem201Flags stem201_flags b]
  fin_cases b <;> decide +kernel

def stem202Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem202_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [5, 16, 16]) b.val = stem202Deg b := by
  rw [degCount_fuel_one leaders 16 [5, 16, 16] stem202Flags stem202_flags b]
  fin_cases b <;> decide +kernel

def stem203Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem203_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [5, 16, 17]) b.val = stem203Deg b := by
  rw [degCount_fuel_one leaders 17 [5, 16, 17] stem203Flags stem203_flags b]
  fin_cases b <;> decide +kernel

def stem204Deg (b : Fin 5) : ℕ := [3, 0, 0, 0, 0].getD b.val 0

theorem stem204_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 8 [6, 6, 8]) b.val = stem204Deg b := by
  rw [degCount_fuel_one leaders 8 [6, 6, 8] stem204Flags stem204_flags b]
  fin_cases b <;> decide +kernel

def stem205Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem205_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 9 [6, 6, 9]) b.val = stem205Deg b := by
  rw [degCount_fuel_one leaders 9 [6, 6, 9] stem205Flags stem205_flags b]
  fin_cases b <;> decide +kernel

def stem206Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem206_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [6, 6, 16]) b.val = stem206Deg b := by
  rw [degCount_fuel_one leaders 16 [6, 6, 16] stem206Flags stem206_flags b]
  fin_cases b <;> decide +kernel

def stem207Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem207_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [6, 6, 17]) b.val = stem207Deg b := by
  rw [degCount_fuel_one leaders 17 [6, 6, 17] stem207Flags stem207_flags b]
  fin_cases b <;> decide +kernel

def stem208Deg (b : Fin 5) : ℕ := [4, 0, 0, 0, 0].getD b.val 0

theorem stem208_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 8 [6, 8, 8]) b.val = stem208Deg b := by
  rw [degCount_fuel_one leaders 8 [6, 8, 8] stem208Flags stem208_flags b]
  fin_cases b <;> decide +kernel

def stem209Deg (b : Fin 5) : ℕ := [3, 0, 0, 0, 0].getD b.val 0

theorem stem209_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 10 [6, 8, 10]) b.val = stem209Deg b := by
  rw [degCount_fuel_one leaders 10 [6, 8, 10] stem209Flags stem209_flags b]
  fin_cases b <;> decide +kernel

end VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Count.stem209_dcount
