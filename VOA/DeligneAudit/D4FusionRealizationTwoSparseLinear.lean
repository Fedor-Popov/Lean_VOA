/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoCertificateSound
import VOA.DeligneAudit.D4FusionRealizationTwoMatrixBridge
import Mathlib.LinearAlgebra.Pi

/-! Sparse integer columns define a genuine complex linear endomorphism.
The support condition is explicit when applying it to sparse vectors. -/
namespace VOA.DeligneAudit.D4Two.Certificate

noncomputable section

def columnsEnd (n : ℕ) (cols : ℕ → SV) : Module.End ℂ (Fin n → ℂ) :=
  (Pi.basisFun ℂ (Fin n)).constr ℂ (fun i => vec n (cols i))

theorem columnsEnd_apply (n : ℕ) (cols : ℕ → SV) (v : Fin n → ℂ) :
    columnsEnd n cols v = ∑ i : Fin n, v i • vec n (cols i) := by
  rw [columnsEnd, Module.Basis.constr_apply_fintype, Pi.basisFun_equivFun]
  rfl

theorem columnsEnd_single (n : ℕ) (cols : ℕ → SV) (i : Fin n) :
    columnsEnd n cols (Pi.single i 1) = vec n (cols i) := by
  simpa only [Pi.basisFun_apply] using
    (Pi.basisFun ℂ (Fin n)).constr_basis ℂ (fun j => vec n (cols j)) i

/-- Every repeated sparse coordinate is included with its full integer
coefficient; no independence or dimension claim is used here. -/
theorem columnsEnd_vec (n : ℕ) (cols : ℕ → SV) (v : SV)
    (hv : rangeCheck n v = true) :
    columnsEnd n cols (vec n v) = vec n (applyColumns cols v) := by
  have hrange : ∀ p ∈ v, p.1 < n := by
    simpa only [rangeCheck, List.all_eq_true, decide_eq_true_eq] using hv
  rw [columnsEnd_apply, applyColumns, vec_flatMap]
  simp only [vec_scale]
  exact DeligneSector.Sparse.sum_sget_smul v hrange (fun j => vec n (cols j))

end
end VOA.DeligneAudit.D4Two.Certificate

#print axioms VOA.DeligneAudit.D4Two.Certificate.columnsEnd_vec
