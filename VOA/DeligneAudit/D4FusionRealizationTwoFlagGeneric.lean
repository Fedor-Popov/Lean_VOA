/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneFusionD1TensorGGrCore
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Finite actual basis flags and their current-degree filtration.
The finite action hypotheses will be discharged by explicit coefficient
certificates. No rank or character inequality is a hypothesis. -/
namespace VOA.DeligneAudit.D4Two

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.D1TensorG.Gr

noncomputable section

variable {ι T : Type*} [AddCommGroup T] [Module ℂ T]

/-- The flag determined by actual basis vectors and their word degrees. -/
def flag (b : Module.Basis ι ℂ T) (level : ι → ℕ) (d : ℕ) : Submodule ℂ T :=
  Submodule.span ℂ {v | ∃ i, level i ≤ d ∧ v = b i}

theorem flag_mono (b : Module.Basis ι ℂ T) (level : ι → ℕ)
    {d e : ℕ} (hde : d ≤ e) : flag b level d ≤ flag b level e :=
  Submodule.span_mono fun _ ⟨i, hi, hv⟩ => ⟨i, hi.trans hde, hv⟩

theorem flag_top (b : Module.Basis ι ℂ T) (level : ι → ℕ) (cut d : ℕ)
    (hlevel : ∀ i, level i ≤ cut) (hd : cut ≤ d) : flag b level d = ⊤ := by
  apply top_unique
  rw [← b.span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact Submodule.subset_span ⟨i, (hlevel i).trans hd, rfl⟩

variable {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ}
    (R : CurrentModule f T) (w : T)
    (b : Module.Basis ι ℂ T) (level : ι → ℕ) (cut : ℕ)
    (hlevel : ∀ i, level i ≤ cut)
    (hcritical : ∀ (c : Fin n) (k : ℕ) (i : ι), level i + k < cut →
      R.op c k (b i) ∈ flag b level (level i + k))

include cut hlevel hcritical

theorem flag_op (c : Fin n) (k d : ℕ) :
    flag b level d ≤ (flag b level (d + k)).comap (R.op c k) := by
  by_cases htop : cut ≤ d + k
  · rw [flag_top b level cut (d + k) hlevel htop]
    simp
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    have hlt : level i + k < cut := by omega
    exact flag_mono b level (Nat.add_le_add_right hi k) (hcritical c k i hlt)

/-- All source words lie in the certified finite flag at their actual degree. -/
theorem word_mem_flag (hw : w ∈ flag b level 0) :
    ∀ l : List (Fin n × ℕ), wordOp R l w ∈ flag b level (degree l) := by
  intro l
  induction l with
  | nil => exact hw
  | cons x l ih =>
      have h := flag_op R b level cut hlevel hcritical x.1 x.2 (degree l) ih
      simpa only [wordOp, degree_cons, Nat.add_comm] using h

/-- Only the finite low-level action coefficients are needed for the upper flag inclusion. -/
theorem Fbelow_le_flag (hw : w ∈ flag b level 0) (d : ℕ) :
    Fbelow R w (d + 1) ≤ flag b level d := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l, hl, rfl⟩
  have hd : degree l ≤ d := by omega
  exact flag_mono b level hd (word_mem_flag R w b level cut hlevel hcritical hw l)

omit cut hlevel hcritical

/-- Explicit source-word witnesses give the opposite flag inclusion. -/
theorem flag_le_Fbelow (hwords : ∀ i, ∃ l : List (Fin n × ℕ),
    degree l = level i ∧ b i = wordOp R l w) (d : ℕ) :
    flag b level d ≤ Fbelow R w (d + 1) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, hi, rfl⟩
  obtain ⟨l, hl, hv⟩ := hwords i
  exact Submodule.subset_span ⟨l, by omega, hv⟩

include cut hlevel hcritical

theorem Fbelow_eq_flag (hw : w ∈ flag b level 0)
    (hwords : ∀ i, ∃ l : List (Fin n × ℕ),
      degree l = level i ∧ b i = wordOp R l w) (d : ℕ) :
    Fbelow R w (d + 1) = flag b level d :=
  le_antisymm (Fbelow_le_flag R w b level cut hlevel hcritical hw d)
    (flag_le_Fbelow R w b level hwords d)

omit cut hlevel hcritical

/-- The rank of an actual basis flag is its finite index count. -/
theorem finrank_flag [Fintype ι] (d : ℕ) :
    Module.finrank ℂ (flag b level d) = Fintype.card {i : ι // level i ≤ d} := by
  let v : {i : ι // level i ≤ d} → T := fun i => b i.val
  have hrange : Set.range v = {x | ∃ i, level i ≤ d ∧ x = b i} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  rw [flag, ← hrange]
  exact finrank_span_eq_card
    (b.linearIndependent.comp (fun i : {i : ι // level i ≤ d} => i.val)
      Subtype.val_injective)

end
end VOA.DeligneAudit.D4Two

#print axioms VOA.DeligneAudit.D4Two.Fbelow_eq_flag
#print axioms VOA.DeligneAudit.D4Two.finrank_flag
