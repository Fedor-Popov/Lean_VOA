/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4LieData
import VOA.DeligneAudit.F4LieSingChecksA
import VOA.DeligneAudit.F4LieSingChecksB
import VOA.DeligneAudit.F4LieSingChecksC
import VOA.DeligneAudit.F4LieSingChecksD
import VOA.DeligneAudit.F4LieSingChecksE
import VOA.DeligneAudit.F4LieSingChecksF
import VOA.DeligneAudit.F4LieSingChecksG
import VOA.DeligneAudit.F4LieSingChecksH
import VOA.DeligneAudit.F4LieSingChecksV

/-!
# The weight-two singular vector of `V^{-5/2}(𝔣₄)`

`f4sv = -J^{8}_{-1}J^{8}_{-1}|0⟩ + 4 J^{19}_{-1}J^{30}_{-1}|0⟩ + 4
J^{21}_{-1}J^{34}_{-1}|0⟩ + 4 J^{25}_{-1}J^{42}_{-1}|0⟩` (table basis of `f4CertData`).
Its symbol is the highest-weight vector of `I₂ⁿˢ = V(2ω₄)` in the positive-system
convention. It is positive-mode singular at `k = -5/2` (kernel checks `f4_q1_*`, `f4_q2`
through `quadStateQ_mem_maxIdeal`), hence **`f4sv_mem_maxIdeal`** and **`f4sv_proj`**: it
vanishes in `L_{-5/2}(𝔣₄) = f4W`.

Numerics (outside Lean, modular rank): the weight-two singular space at `k = -5/2` is
`324`-dimensional (`Sym²𝔣₄ = 1053 ⊕ 324 ⊕ 1`).
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.F4Lie

open VOA.AffineGeneral VOA.AffineGeneral.SCLie

noncomputable section

theorem f4_q1 : ∀ x g : Fin 52, q1Z f4scZ f4fZ (-5) 2 f4svTerms x g = 0 := by
  intro x g
  have hx : x.val < 52 := x.2
  rcases (show (0 ≤ x.val ∧ x.val < 7) ∨
      (7 ≤ x.val ∧ x.val < 14) ∨
      (14 ≤ x.val ∧ x.val < 21) ∨
      (21 ≤ x.val ∧ x.val < 28) ∨
      (28 ≤ x.val ∧ x.val < 35) ∨
      (35 ≤ x.val ∧ x.val < 42) ∨
      (42 ≤ x.val ∧ x.val < 49) ∨
      (49 ≤ x.val ∧ x.val < 52) by omega) with h | h | h | h | h | h | h | h
  · exact f4_q1_0 x g h.1 h.2
  · exact f4_q1_1 x g h.1 h.2
  · exact f4_q1_2 x g h.1 h.2
  · exact f4_q1_3 x g h.1 h.2
  · exact f4_q1_4 x g h.1 h.2
  · exact f4_q1_5 x g h.1 h.2
  · exact f4_q1_6 x g h.1 h.2
  · exact f4_q1_7 x g h.1 h.2

theorem f4_level_eq : ((-5 : ℤ) : ℂ) / ((2 : ℤ) : ℂ) = (-5/2 : ℂ) := by push_cast; ring

/-- The singular vector. -/
def f4sv : Vacuum f4CertData (-5/2) :=
  quadState f4CertData (-5/2) (termsZC f4svTerms)

/-- **The singular vector lies in the maximal ideal.** -/
theorem f4sv_mem_maxIdeal : f4sv ∈ maxIdeal f4CertData (-5/2) f4_level_ne := by
  have key : ∀ (k : ℂ) (hk : k + f4CertData.h ≠ 0), k = ((-5 : ℤ) : ℂ) / ((2 : ℤ) : ℂ) →
      quadState f4CertData k (termsZC f4svTerms) ∈ maxIdeal f4CertData k hk := by
    intro k hk e
    subst e
    exact quadStateQ_mem_maxIdeal (D := f4CertData) (scZ := f4scZ) (fZ := f4fZ)
      (fun a b c => f4CertData_sc a b c) (fun a b => f4CertData_form a b) (-5) 2 (by norm_num)
      hk f4svTerms f4_q1 f4_q2
  exact key _ f4_level_ne f4_level_eq.symm

/-- **The singular vector vanishes in `L_{-5/2}(𝔣₄)`.** -/
theorem f4sv_proj : simpleProjection f4CertData (-5/2) f4_level_ne f4sv = 0 := by
  rw [simpleProjection, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact f4sv_mem_maxIdeal

end

end VOA.DeligneAudit.F4Lie

section AxiomAudit
#print axioms VOA.DeligneAudit.F4Lie.f4sv_mem_maxIdeal
#print axioms VOA.DeligneAudit.F4Lie.f4sv_proj
end AxiomAudit
