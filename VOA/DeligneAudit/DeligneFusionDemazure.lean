/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneFusionSqueeze
import VOA.DeligneAudit.DeligneFusionRel

/-!
# The `dem_le` field of the squeeze: the Demazure module as a quotient of `M_{n,0}`

the `M_{a,b}` are presented by `SectorWeyl.MabRel ρ w a b` (`DeligneFusionRel.lean`). Whatever
power series `M a b` is attached to them, the plug-in property used here is the **universal bound**
(`MabUniversalBound M`): every cyclic module whose generator satisfies the `M_{a,b}` relations has
`t`-graded dimensions at most `[q^N] M a b`. If `M a b` is the character of the universal module,
this is the statement that every such module is a graded quotient of it. At `a = 0` it is the
squeeze's `huniv` (`huniv_of_universalBound`).

**Named input (U7, realization form)** `DemazureRealization n`: there is a cyclic graded
`sl₃[t]`-module whose generator satisfies the `M_{n,0}` relations and whose degree-`N` pieces have
dimension at least `demazureHilb n N` (the Gelfand–Tsetlin polynomial). The Demazure module
`D(1,nθ)` is such a module: it satisfies the `M_{n,0}` relations (Chari–Venkatesh /
Fourier–Littelmann presentation), and by U7 (Sanderson, Ion; Fourier–Littelmann for the
identification) its graded
character is `P_{nθ}(x;q,0)`, which at `x = 1` is `demazureHilb n`. Neither fact is formalized.
`demazureRealization_zero` checks `n = 0` (the trivial module).

**Plumbing** (`dem_le_of_realization`): the universal bound plus a realization gives
`CoeffLe (demazureHilbSeries n) (M n 0)`. This is the squeeze's `dem_le` field.
`fusionModuleBound_of_realizations` assembles U5 from the universal bound,
`∀ n, DemazureRealization n`, and the `nonneg`, `rec_le`, `total_le`.
-/

namespace VOA.DeligneAudit.A2

open PowerSeries SectorWeyl VOA.AffineSl3

open scoped BigOperators

noncomputable section

/-- **Universal bound**: every cyclic module with the `M_{a,b}` relations is bounded by `M a b`. -/
def MabUniversalBound (M : ℕ → ℕ → PowerSeries ℚ) : Prop :=
  ∀ (a b : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule (bracketTable) V)
    (w : V), MabRel ρ w a b → ∀ N, (Module.finrank ℂ (cycDeg ρ w N) : ℚ) ≤ coeff N (M a b)

/-- **Named input (U7, realization form)**: a cyclic module with the `M_{n,0}` relations whose
graded
dimensions dominate `demazureHilb n` (the Demazure module `D(1,nθ)`). -/
def DemazureRealization (n : ℕ) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : CurrentModule (bracketTable) V) (w : V),
    MabRel ρ w n 0 ∧ ∀ N, demazureHilb n N ≤ Module.finrank ℂ (cycDeg ρ w N)

variable {M : ℕ → ℕ → PowerSeries ℚ}

/-- **The `dem_le` field** from the universal bound and a realization. -/
theorem dem_le_of_realization (hU : MabUniversalBound M) {n : ℕ} (hD : DemazureRealization n) :
    CoeffLe (demazureHilbSeries n) (M n 0) := by
  obtain ⟨V, _, _, ρ, w, hrel, hdim⟩ := hD
  intro N
  rw [demazureHilbSeries, coeff_mk]
  exact (Nat.cast_le.mpr (hdim N)).trans (hU n 0 V ρ w hrel N)

/-- The squeeze's `huniv` from the universal bound at `a = 0`. -/
theorem huniv_of_universalBound (hU : MabUniversalBound M) :
    ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule (bracketTable) V)
      (w : V), LocalWeylRel ρ w m →
        ∀ b, (Module.finrank ℂ (cycDeg ρ w b) : ℚ) ≤ coeff b (M 0 m) :=
  fun m V _ _ ρ w hw b => hU 0 m V ρ w ((mabRel_zero_iff ρ w m).mpr hw) b

/-- **U5 for `fusionF`** from the universal bound, the Demazure realizations (U7), and the
`nonneg`, `rec_le` (F4′) and `total_le` (F4). -/
theorem fusionModuleBound_of_realizations (hU : MabUniversalBound M)
    (hD : ∀ n, DemazureRealization n) (hnonneg : ∀ a b N, 0 ≤ coeff N (M a b))
    (hrec : ∀ a b, CoeffLe (M (a + 1) b) (M a (b + 1) + X ^ (2 * a + b + 1) * M a b))
    (htot : ∀ m B, ∑ N ∈ Finset.range B, coeff N (M 0 m) ≤ 8 ^ m) :
    FusionModuleBound fusionF :=
  fusionModuleBound_of_squeeze ⟨hnonneg, hrec, fun n => dem_le_of_realization hU (hD n), htot⟩
    (huniv_of_universalBound hU)

/-! ## Sanity check: `n = 0` -/

/-- The zero action of `sl₃[t]` on `ℂ`. -/
def trivialCurrent : CurrentModule (bracketTable) ℂ where
  op _ _ := 0
  comm _ _ _ _ _ := by simp

theorem demazureHilb_zero (N : ℕ) : demazureHilb 0 N = if N = 0 then 1 else 0 := by
  have h := coeff_demazureQPoly 0 N
  have h1 : demazureQPoly 0 = 1 := by
    simp [demazureQPoly, gl3Poly, gl2Poly]
  rw [h1, Polynomial.coeff_one] at h
  split_ifs at h ⊢ with h2
  · subst h2; exact_mod_cast h.symm
  · exact_mod_cast h.symm

/-- `DemazureRealization 0`: the trivial module. -/
theorem demazureRealization_zero : DemazureRealization 0 := by
  refine ⟨ℂ, inferInstance, inferInstance, trivialCurrent, 1, ?_, fun N => ?_⟩
  · refine ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => by simp [trivialCurrent], ?_, ?_,
      rfl, rfl, rfl⟩ <;> simp [trivialCurrent]
  · rw [demazureHilb_zero]
    split_ifs with h
    · subst h
      have hmem : (1 : ℂ) ∈ cycDeg trivialCurrent (1 : ℂ) 0 :=
        Submodule.subset_span ⟨[], rfl, rfl⟩
      have htop : cycDeg trivialCurrent (1 : ℂ) 0 = ⊤ := by
        rw [eq_top_iff]
        intro x _
        have := Submodule.smul_mem _ x hmem
        simpa using this
      rw [htop, finrank_top, Module.finrank_self]
    · exact Nat.zero_le _

end

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.dem_le_of_realization
#print axioms VOA.DeligneAudit.A2.huniv_of_universalBound
#print axioms VOA.DeligneAudit.A2.fusionModuleBound_of_realizations
#print axioms VOA.DeligneAudit.A2.demazureRealization_zero
end AxiomAudit
