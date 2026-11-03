/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4Sector

/-!
# `F₄`: kernel-table data (integer checks)

Integer `decide +kernel` facts on the `f4T` for `f4KernelTable` (`F4LieKernel`). The table scan was
done outside Lean.

* Cartan basis `h₀, h₁, h₂` (`θ = 2, 1, 0`) and the `cartanN` index `h₃` (`θ = -1`):
  `τ = (2, 1, 0, -1)`.
* `e_θ = x₂₁` (`s_θ = -1`); the simple `sl₂` with `θ(h) = 1` is `x₄₇` with `e = x₂₃`, `s = -1`.
* Fourteen fusion roots `x` have `[e_β, f_θ] = κ f_x`. The other nine negative roots (the `C₃` roots
  orthogonal to `θ`) form `kill0`: the simple `x₂₆, x₁₃, x₄₆` (`θ(h) = 0`) and six brackets
  `x₁₁ = -[x₂₆, x₄₆]`, `x₃₈ = -[x₁₃, x₄₆]`, `x₂₀ = -[x₁₃, x₁₁]`, `2x₄₀ = [x₄₆, x₁₁]`,
  `x₂₉ = [x₄₆, x₂₀]`, `-2x₁₀ = [x₁₃, x₂₉]` (rank = generation depth).
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.UnivG.F4K

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.F4

/-- The signed `θ`-values on the Cartan basis. -/
def τZ (c : Fin 52) : ℤ :=
  if c.val = 0 then 2 else if c.val = 1 then 1 else if c.val = 3 then -1 else 0

def hselL : List ℕ := [
  0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
  1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1]

/-- A Cartan acting diagonally and invertibly on each negative root vector. -/
def hsel (x : Fin 52) : Fin 52 := Fin.ofNat 52 (hselL.getD x.val 0)

def bL : List ℕ := [
  0, 0, 0, 0, 0, 0, 23, 0, 0, 24, 0, 0, 25, 0, 0, 0, 0, 0, 27, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0,
  0, 19, 15, 0, 0, 0, 0, 0, 0, 8, 0, 4, 0, 7, 0, 0, 0, 30, 33, 36, 0, 42]

def kL : List ℤ := [
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1,
  -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, 1, 1]

def bsel (x : Fin 52) : Fin 52 := Fin.ofNat 52 (bL.getD x.val 0)
def ksel (x : Fin 52) : ℤ := kL.getD x.val 1

/-- The roots orthogonal to `θ`. -/
def kill0L : List ℕ := [26, 13, 46, 11, 38, 20, 40, 29, 10]

def rkL : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0,
  0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def agL : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 26, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 46,
  0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 46, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def bgL : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 46, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 20,
  0, 0, 0, 0, 0, 0, 0, 0, 46, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def kgL : List ℤ := [
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -2, -1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

def rk (x : Fin 52) : ℕ := rkL.getD x.val 0
def ag (x : Fin 52) : Fin 52 := Fin.ofNat 52 (agL.getD x.val 0)
def bg (x : Fin 52) : Fin 52 := Fin.ofNat 52 (bgL.getD x.val 0)
def kg (x : Fin 52) : ℤ := kgL.getD x.val 1

theorem truncUpZ : ∀ x : Fin 52, x.val ∈ negL →
    ((hsel x).val ∈ ([0, 1, 2] : List ℕ) ∨ (hsel x).val ∈ ([3] : List ℕ)) ∧
      fZ br (hsel x) x x ≠ 0 ∧ ∀ c : Fin 52, c ≠ x → fZ br (hsel x) x c = 0 := by decide +kernel

theorem raisThetaZ : ∀ e c : Fin 52, e.val ∈ posL → fZ br e 45 c ≠ 0 →
    (c.val ∈ ([0, 1, 2] : List ℕ) ∨ c.val ∈ ([3] : List ℕ)) ∨ (c.val ∈ negL ∧ c ≠ 45) := by
  decide +kernel

theorem cartTauZ : ∀ h c : Fin 52, (h.val ∈ ([0, 1, 2] : List ℕ) ∨ h.val ∈ ([3] : List ℕ)) →
    fZ br h 45 c = if c = 45 then -τZ h else 0 := by decide +kernel

theorem lowCommZ : ∀ x c : Fin 52, x.val ∈ negL → fZ br x 45 c = 0 := by decide +kernel

theorem simpleZ : (∀ c : Fin 52, fZ br 23 47 c ≠ 0 →
      c.val ∈ ([0, 1, 2] : List ℕ) ∨ c.val ∈ ([3] : List ℕ)) ∧
    ∑ c : Fin 52, -fZ br 23 47 c * τZ c = 1 ∧
    ∀ d : Fin 52, ∑ c : Fin 52, -fZ br 23 47 c * fZ br c 47 d = if d = 47 then -2 else 0 := by
  decide +kernel

theorem eθZ : (∀ c : Fin 52, fZ br 21 45 c ≠ 0 →
      c.val ∈ ([0, 1, 2] : List ℕ) ∨ c.val ∈ ([3] : List ℕ)) ∧
    ∑ c : Fin 52, fZ br 21 45 c * τZ c = -2 := by decide +kernel

theorem rootZ : ∀ x : Fin 52, x.val ∈ negL → x ≠ 45 → x.val ∉ kill0L →
    (bsel x).val ∈ posL ∧ ksel x ≠ 0 ∧
      ∀ c : Fin 52, fZ br (bsel x) 45 c = if c = x then ksel x else 0 := by decide +kernel

theorem kill0Z : ∀ x : Fin 52, x.val ∈ kill0L →
    (x.val ∈ ([26, 13, 46] : List ℕ)) ∨
      (kg x ≠ 0 ∧ (ag x).val ∈ kill0L ∧ (bg x).val ∈ kill0L ∧ rk (ag x) < rk x ∧
        rk (bg x) < rk x ∧ ∀ c : Fin 52, fZ br (ag x) (bg x) c = if c = x then kg x else 0) := by
  decide +kernel

theorem kill0_negL : ∀ x : Fin 52, x.val ∈ kill0L → x.val ∈ negL := by decide +kernel

theorem chainZ :
    (∀ e : Fin 52, fZ br 26 46 e = if e = 11 then -1 else 0) ∧
    (∀ e : Fin 52, fZ br 13 11 e = if e = 20 then -1 else 0) ∧
    (∀ e : Fin 52, fZ br 46 20 e = if e = 29 then 1 else 0) ∧
    (∀ e : Fin 52, fZ br 26 47 e = if e = 12 then -1 else 0) ∧
    (∀ e : Fin 52, fZ br 26 12 e = 0) ∧
    (∀ e : Fin 52, fZ br 29 47 e = if e = 48 then -1 else 0) ∧
    (∀ e : Fin 52, fZ br 29 48 e = if e = 49 then -2 else 0) ∧
    (∀ e : Fin 52, fZ br 29 49 e = 0) ∧
    (∀ e : Fin 52, fZ br 12 49 e = if e = 45 then 1 else 0) ∧
    (∀ e : Fin 52, fZ br 12 45 e = 0) ∧ (∀ e : Fin 52, fZ br 49 45 e = 0) := by
  decide +kernel

end VOA.DeligneAudit.UnivG.F4K
