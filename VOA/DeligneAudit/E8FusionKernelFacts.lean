/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8FusionKernelDefs

/-!
# `E₈` kernel table facts, as support checks on table entries

The `∀ c : Fin 248` forms of the table facts are expensive in the kernel: each `c` re-walks the entry. Here each
fact is a support check `suppIn (brK a b) P` on the sparse entry itself, together with one or two coefficients,
and the `∀ c` forms are derived by `sget_eq_zero_of_suppIn` (kept small to bound kernel memory).
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.UnivG.E8K

open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E8 (E8sector thetaH lowExpE8 fusionE8)

/-- Every entry `(c, z)` of `L` has `P c` or `z = 0`. -/
def suppIn (L : SV) (P : ℕ → Bool) : Bool := L.all fun p => P p.1 || p.2 == 0

theorem sget_eq_zero_of_suppIn {L : SV} {P : ℕ → Bool} (h : suppIn L P = true) {c : ℕ}
    (hc : P c = false) : sget L c = 0 := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp only [suppIn, List.all_cons, Bool.and_eq_true] at h
    rw [sget_cons, ih h.2]
    split_ifs with hp
    · subst hp
      simp only [hc, Bool.false_or, beq_iff_eq] at h
      rw [h.1]; rfl
    · rfl

theorem mem_of_suppIn {L : SV} {P : ℕ → Bool} (h : suppIn L P = true) {c : ℕ} (hc : sget L c ≠ 0) :
    P c = true := by
  by_contra h'
  exact hc (sget_eq_zero_of_suppIn h (by simpa using h'))

/-! ## Kernel checks -/

theorem fusion_iff : ∀ x : Fin 248, fusionE8 x ↔ x.val ∈ fusL := by
  unfold fusionE8 VOA.DeligneAudit.DeligneCarrier.E8.thetaPair; decide +kernel

theorem truncUpL : ∀ x : Fin 248, x.val ∈ fusL ∨ x.val ∈ lowL →
    (hselK x).val < 8 ∧ sget (brK (hselK x) x) x ≠ 0 ∧ suppIn (brK (hselK x) x) (· == x.val) = true := by
  decide +kernel

theorem raisL : ∀ e : Fin 248, 8 ≤ e.val → e.val < 128 →
    suppIn (brK e 247) (fun c => decide (c < 8) || (decide (c ∈ fusL) && c != 247)) = true := by
  decide +kernel

theorem cartL : ∀ h : Fin 248, h.val < 8 →
    suppIn (brK h 247) (· == 247) = true ∧ sget (brK h 247) 247 = -(thetaH h : ℤ) := by
  decide +kernel

theorem lowCommL : ∀ x : Fin 248, x.val ∈ fusL ∨ x.val ∈ lowL → suppIn (brK x 247) (fun _ => false) = true := by
  decide +kernel

theorem simpleL : suppIn (brK 8 128) (· == 7) = true ∧ sget (brK 8 128) 7 = 1 ∧
    suppIn (brK 7 128) (· == 128) = true ∧ sget (brK 7 128) 128 = -2 := by
  decide +kernel

theorem eθL : suppIn (brK 127 247) (fun c => decide (c < 8)) = true ∧ sget (brK 127 247) 7 = -2 := by
  decide +kernel

theorem rootL : ∀ x : Fin 248, x.val ∈ fusL → x ≠ 247 →
    8 ≤ (bselK x).val ∧ (bselK x).val < 128 ∧ kselK x ≠ 0 ∧
      suppIn (brK (bselK x) 247) (· == x.val) = true ∧ sget (brK (bselK x) 247) x = kselK x := by
  decide +kernel

/-! ## The `∀ c` forms used by `E8FusionKernel` -/

theorem ne_val {c x : Fin 248} (h : c ≠ x) : (c.val == x.val) = false := by
  simpa using fun h' => h (Fin.ext h')

theorem e8_truncUpZ : ∀ x : Fin 248, x.val ∈ fusL ∨ x.val ∈ lowL →
    (hselK x).val < 8 ∧ fZ brK (hselK x) x x ≠ 0 ∧
      ∀ c : Fin 248, c ≠ x → fZ brK (hselK x) x c = 0 := by
  intro x hx
  obtain ⟨h1, h2, h3⟩ := truncUpL x hx
  exact ⟨h1, h2, fun c hc => sget_eq_zero_of_suppIn h3 (ne_val hc)⟩

theorem e8_raisThetaZ : ∀ e c : Fin 248, 8 ≤ e.val → e.val < 128 → fZ brK e 247 c ≠ 0 →
    c.val < 8 ∨ (c.val ∈ fusL ∧ c ≠ 247) := by
  intro e c h1 h2 hc
  have := mem_of_suppIn (raisL e h1 h2) hc
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, bne_iff_ne, ne_eq] at this
  rcases this with h | ⟨h, h'⟩
  · exact Or.inl h
  · exact Or.inr ⟨h, fun e => h' (by rw [e]; rfl)⟩

theorem e8_cartThetaZ : ∀ h c : Fin 248, h.val < 8 →
    fZ brK h 247 c = if c = 247 then -(thetaH h : ℤ) else 0 := by
  intro h c hh
  obtain ⟨h1, h2⟩ := cartL h hh
  split_ifs with hc
  · subst hc; exact h2
  · exact sget_eq_zero_of_suppIn h1 (ne_val hc)

theorem e8_lowCommZ : ∀ x c : Fin 248, x.val ∈ fusL ∨ x.val ∈ lowL → fZ brK x 247 c = 0 :=
  fun x c hx => sget_eq_zero_of_suppIn (lowCommL x hx) rfl

theorem e8_simpleZ : (∀ c : Fin 248, fZ brK 8 128 c = if c = 7 then 1 else 0) ∧
    (∀ c : Fin 248, fZ brK 7 128 c = if c = 128 then -2 else 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := simpleL
  refine ⟨fun c => ?_, fun c => ?_⟩
  · split_ifs with hc
    · subst hc; exact h2
    · exact sget_eq_zero_of_suppIn h1 (ne_val (x := 7) hc)
  · split_ifs with hc
    · subst hc; exact h4
    · exact sget_eq_zero_of_suppIn h3 (ne_val (x := 128) hc)

theorem e8_eθZ : (∀ c : Fin 248, fZ brK 127 247 c ≠ 0 → c.val < 8) ∧ fZ brK 127 247 7 = -2 := by
  obtain ⟨h1, h2⟩ := eθL
  refine ⟨fun c hc => ?_, h2⟩
  simpa using mem_of_suppIn h1 hc

theorem e8_rootZ : ∀ x : Fin 248, x.val ∈ fusL → x ≠ 247 →
    8 ≤ (bselK x).val ∧ (bselK x).val < 128 ∧ kselK x ≠ 0 ∧
      ∀ c : Fin 248, fZ brK (bselK x) 247 c = if c = x then kselK x else 0 := by
  intro x hx hx0
  obtain ⟨h1, h2, h3, h4, h5⟩ := rootL x hx hx0
  refine ⟨h1, h2, h3, fun c => ?_⟩
  split_ifs with hc
  · subst hc; exact h5
  · exact sget_eq_zero_of_suppIn h4 (ne_val hc)

end VOA.DeligneAudit.UnivG.E8K
