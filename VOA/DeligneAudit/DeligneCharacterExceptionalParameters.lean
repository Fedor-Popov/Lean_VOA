/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterDemazure

/-! Numeric exceptional character data, with no VOA target aliases. -/
namespace VOA.DeligneAudit.DeligneCharacter

/-! ## Data -/

def cartanG2 : List (List ℤ) := [[2, -3], [-1, 2]]
def thetaG2 : List ℤ := [3, 2]
def wordG2 : List ℕ := [1, 0, 1, 0, 1]

def cartanF4 : List (List ℤ) := [[2, -1, 0, 0], [-1, 2, -1, 0], [0, -2, 2, -1], [0, 0, -1, 2]]
def thetaF4 : List ℤ := [2, 3, 4, 2]
def wordF4 : List ℕ := [0, 1, 2, 3, 1, 2, 0, 1, 2, 3, 0, 1, 2, 1, 0]

/-- `E_n` (Bourbaki: chain `1-3-4-5-…`, node `2` attached to `4`). -/
def cartanE6 : List (List ℤ) :=
  [[2, 0, -1, 0, 0, 0], [0, 2, 0, -1, 0, 0], [-1, 0, 2, -1, 0, 0], [0, -1, -1, 2, -1, 0],
   [0, 0, 0, -1, 2, -1], [0, 0, 0, 0, -1, 2]]
def thetaE6 : List ℤ := [1, 2, 2, 3, 2, 1]
def wordE6 : List ℕ := [1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2, 3, 1]

def cartanE7 : List (List ℤ) :=
  [[2, 0, -1, 0, 0, 0, 0], [0, 2, 0, -1, 0, 0, 0], [-1, 0, 2, -1, 0, 0, 0],
   [0, -1, -1, 2, -1, 0, 0],
   [0, 0, 0, -1, 2, -1, 0], [0, 0, 0, 0, -1, 2, -1], [0, 0, 0, 0, 0, -1, 2]]
def thetaE7 : List ℤ := [2, 2, 3, 4, 3, 2, 1]
def wordE7 : List ℕ := [0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5,
  0, 2, 3, 4, 1, 3, 2, 0]

def cartanE8 : List (List ℤ) :=
  [[2, 0, -1, 0, 0, 0, 0, 0], [0, 2, 0, -1, 0, 0, 0, 0], [-1, 0, 2, -1, 0, 0, 0, 0],
   [0, -1, -1, 2, -1, 0, 0, 0], [0, 0, 0, -1, 2, -1, 0, 0], [0, 0, 0, 0, -1, 2, -1, 0],
   [0, 0, 0, 0, 0, -1, 2, -1], [0, 0, 0, 0, 0, 0, -1, 2]]
def thetaE8 : List ℤ := [2, 3, 4, 6, 5, 4, 3, 2]
def wordE8 : List ℕ := [7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3,
  4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7]

def g2DemazureHilb (m N : ℕ) : ℕ := levelOneDemazureHilb cartanG2 thetaG2 wordG2 m N
def f4DemazureHilb (m N : ℕ) : ℕ := levelOneDemazureHilb cartanF4 thetaF4 wordF4 m N
def e6DemazureHilb (m N : ℕ) : ℕ := levelOneDemazureHilb cartanE6 thetaE6 wordE6 m N
def e7DemazureHilb (m N : ℕ) : ℕ := levelOneDemazureHilb cartanE7 thetaE7 wordE7 m N
def e8DemazureHilb (m N : ℕ) : ℕ := levelOneDemazureHilb cartanE8 thetaE8 wordE8 m N


end VOA.DeligneAudit.DeligneCharacter
