import VOA.DeligneAudit.DeligneFusionCVFamily

/-!
# The A₂ Dynkin involution on current modules and auxiliary CV presentations

The simple roots are exchanged. The highest positive and negative root vectors
both change sign, as required by the chosen structure constants. The bracket
identity is checked directly from the eight-dimensional table; no automorphism
datum is assumed.
-/

namespace VOA.DeligneAudit.A2.CVSymmetry

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.CVsl2 VOA.DeligneAudit.A2.CVFamily

noncomputable section

/-- The Dynkin involution on the ordered Chevalley basis. -/
def swapIndex (e : Fin 8) : Fin 8 := ![1, 0, 2, 4, 3, 5, 7, 6] e

/-- Highest-root vectors change sign under the Dynkin involution. -/
def swapSign (e : Fin 8) : ℂ := ![1, 1, -1, 1, 1, -1, 1, 1] e

variable {V : Type} [AddCommGroup V] [Module ℂ V]

set_option maxHeartbeats 1000000 in
-- The 64 basis pairs each normalize two eight-term bracket sums; the certificate stays below 7 GB.
/-- Pull a current module back along the explicitly checked Dynkin involution. -/
def swapRep (R : CurrentModule bracketTable V) : CurrentModule bracketTable V where
  op e k := swapSign e • R.op (swapIndex e) k
  comm a b r s v := by
    simp only [LinearMap.smul_apply, map_smul, smul_smul]
    rw [mul_comm (swapSign b) (swapSign a), ← smul_sub, R.comm]
    simp only [Finset.smul_sum, smul_smul]
    fin_cases a <;> fin_cases b <;>
      simp [swapIndex, swapSign, Fin.sum_univ_eight, bracketTable] <;> module

@[simp] theorem swapRep_op0 (R : CurrentModule bracketTable V) :
    (swapRep R).op 0 = R.op 1 := by
  funext k
  simp [swapRep, swapIndex, swapSign]

@[simp] theorem swapRep_op1 (R : CurrentModule bracketTable V) :
    (swapRep R).op 1 = R.op 0 := by
  funext k
  simp [swapRep, swapIndex, swapSign]

@[simp] theorem swapRep_op2 (R : CurrentModule bracketTable V) :
    (swapRep R).op 2 = fun k => -R.op 2 k := by
  funext k
  simp [swapRep, swapIndex, swapSign]

@[simp] theorem swapRep_op3 (R : CurrentModule bracketTable V) :
    (swapRep R).op 3 = R.op 4 := by
  funext k
  simp [swapRep, swapIndex, swapSign]

@[simp] theorem swapRep_op4 (R : CurrentModule bracketTable V) :
    (swapRep R).op 4 = R.op 3 := by
  funext k
  simp [swapRep, swapIndex, swapSign]

@[simp] theorem swapRep_op5 (R : CurrentModule bracketTable V) :
    (swapRep R).op 5 = fun k => -R.op 5 k := by
  funext k
  simp [swapRep, swapIndex, swapSign]

@[simp] theorem swapRep_op6 (R : CurrentModule bracketTable V) :
    (swapRep R).op 6 = R.op 7 := by
  funext k
  simp [swapRep, swapIndex, swapSign]

@[simp] theorem swapRep_op7 (R : CurrentModule bracketTable V) :
    (swapRep R).op 7 = R.op 6 := by
  funext k
  simp [swapRep, swapIndex, swapSign]

private theorem currentModule_ext (R S : CurrentModule bracketTable V)
    (hop : R.op = S.op) : R = S := by
  cases R
  cases S
  cases hop
  rfl

/-- Applying the checked Dynkin pullback twice recovers the original module. -/
@[simp] theorem swapRep_swapRep (R : CurrentModule bracketTable V) :
    swapRep (swapRep R) = R := by
  apply currentModule_ext
  funext e k
  fin_cases e <;> simp

/-- Negating every current mode multiplies an ordinary-power coefficient by its parity sign. -/
theorem Q_neg (F : ℕ → Module.End ℂ V) (r s : ℕ) :
    Q (fun k => -F k) r s = (-1 : ℂ) ^ r • Q F r s := by
  have hseries : Garland.Fs (fun k => -F k) = (-1 : ℂ) • Garland.Fs F := by
    apply PowerSeries.ext
    intro k
    simp [Garland.Fs]
  simp only [Q, hseries, smul_pow, PowerSeries.coeff_smul]

/-- Full CV relations are unchanged when every lowering mode changes sign. -/
theorem cvrel_neg {F : ℕ → Module.End ℂ V} {ξ : List ℕ} {w : V}
    (h : CVRel F ξ w) : CVRel (fun k => -F k) ξ w := by
  intro r s k hr hrs
  rw [Q_neg, LinearMap.smul_apply, h r s k hr hrs, smul_zero]

variable {R : CurrentModule bracketTable V} {w : V} {ε ν ϱ : Weight} {j : ℕ}

/-- The actual three-root CV presentation transports through the Dynkin involution. -/
theorem cv3Rel_swap (h : CV3Rel R w ε ν ϱ j) :
    CV3Rel (swapRep R) w (ε.2, ε.1) (ν.2, ν.1) (ϱ.2, ϱ.1) j := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he k
    have he' : e = 0 ∨ e = 1 ∨ e = 2 := by omega
    rcases he' with rfl | rfl | rfl
    · simpa using h.raising 1 (by decide) k
    · simpa using h.raising 0 (by decide) k
    · simp [h.raising 2 (by decide) k]
  · intro hh hhh k hk
    have hh' : hh = 6 ∨ hh = 7 := by omega
    rcases hh' with rfl | rfl
    · simpa using h.cartan_pos 7 (by decide) k hk
    · simpa using h.cartan_pos 6 (by decide) k hk
  · simpa using h.cartan_second
  · simpa using h.cartan_first
  · simpa using h.lowering_second
  · simpa using h.lowering_first
  · simpa using h.second
  · simpa using h.first
  · simpa only [swapRep_op5, Nat.add_comm] using cvrel_neg h.highest

end

end VOA.DeligneAudit.A2.CVSymmetry

#print axioms VOA.DeligneAudit.A2.CVSymmetry.swapRep
#print axioms VOA.DeligneAudit.A2.CVSymmetry.swapRep_swapRep
#print axioms VOA.DeligneAudit.A2.CVSymmetry.Q_neg
#print axioms VOA.DeligneAudit.A2.CVSymmetry.cv3Rel_swap
