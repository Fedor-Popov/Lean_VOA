import VOA.DeligneAudit.D4FusionToroidalFusionGrGenerator

/-!
# Zero-mode powers on the fusion graded generator

The `t`-degree-zero operator preserves the first filtration step. Its power
on the degree-zero symbol is the symbol of the corresponding source power.
-/

namespace VOA.DeligneAudit.Toroidal.FusionGr

open VOA.DeligneAudit.Toroidal

noncomputable section

variable {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ}
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (A : ToroidalAction f V) (w : V) (m : ℕ)

theorem zeroMode_pow_mem (c : Fin n) (i : ℕ) : ∀ k : ℕ,
    ((A.op c i 0) ^ k) w ∈ evalFbelow A w 1
  | 0 => by simpa using generator_mem A w
  | k + 1 => by
      rw [pow_succ', Module.End.mul_apply]
      simpa using evalFbelow_op A w c i 0 1 (zeroMode_pow_mem c i k)

theorem grZeroMode_pow (c : Fin n) (i : ℕ) (hm : 0 < m) : ∀ k : ℕ,
    ((grOp A w m c i 0) ^ k) (grGenerator A w) =
      (kernel A w).mkQ
        (single A w 0 (((A.op c i 0) ^ k) w) (zeroMode_pow_mem A w c i k))
  | 0 => by simp [grGenerator]
  | k + 1 => by
      rw [pow_succ', Module.End.mul_apply, grZeroMode_pow c i hm k]
      rw [grOp_single A w m c i 0 0 hm _ (zeroMode_pow_mem A w c i k)]
      congr 1
      apply Subtype.ext
      simp [single, pow_succ', Module.End.mul_apply]

/-- A raw zero-mode nilpotence relation passes to the graded generator. -/
theorem grZeroMode_pow_zero (c : Fin n) (i k : ℕ) (hm : 0 < m)
    (hz : ((A.op c i 0) ^ k) w = 0) :
    ((grOp A w m c i 0) ^ k) (grGenerator A w) = 0 := by
  rw [grZeroMode_pow A w m c i hm k]
  apply (Submodule.Quotient.mk_eq_zero (kernel A w)).mpr
  change (single A w 0 (((A.op c i 0) ^ k) w)
    (zeroMode_pow_mem A w c i k)).1 ∈ denominator A w
  simp [single, hz]

end

end VOA.DeligneAudit.Toroidal.FusionGr

#print axioms VOA.DeligneAudit.Toroidal.FusionGr.grZeroMode_pow_zero
