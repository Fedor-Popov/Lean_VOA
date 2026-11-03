import VOA.DeligneAudit.D4FusionToroidalFusionPolynomial

/-!
# The cyclic `t`-degree filtration of a toroidal action

The polynomial relation improves the expected shift by one for every mode
at least the number of evaluation sites. This is the filtration fact needed
to make high `t` symbols vanish in an associated graded quotient.
-/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.D1TensorG VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ}
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (A : ToroidalAction f V) (w : V)

/-- A toroidal word is applied from right to left. -/
def evalWord : List (TLtr n) → V → V
  | [], v => v
  | x :: l, v => A.op x.1 x.2.1 x.2.2 (evalWord l v)

/-- The total `t` degree of a word. -/
def tDegree : List (TLtr n) → ℕ
  | [] => 0
  | x :: l => x.2.2 + tDegree l

/-- Cyclic words of `t` degree strictly below `d`. -/
def evalFbelow (d : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ l : List (TLtr n),
    tDegree l < d ∧ v = evalWord A l w}

theorem evalFbelow_op (c : Fin n) (i s d : ℕ) :
    evalFbelow A w d ≤ (evalFbelow A w (d + s)).comap (A.op c i s) := by
  rw [evalFbelow, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  exact Submodule.subset_span ⟨(c, i, s) :: l, by
    change s + tDegree l < d + s
    omega, rfl⟩

theorem evalFbelow_mono {d e : ℕ} (h : d ≤ e) :
    evalFbelow A w d ≤ evalFbelow A w e :=
  Submodule.span_mono (fun _ ⟨l, hl, hv⟩ => ⟨l, by omega, hv⟩)

theorem evalFbelow_zero : evalFbelow A w 0 = ⊥ := by
  apply Submodule.span_eq_bot.mpr
  rintro _ ⟨l, hl, _⟩
  omega

variable {N : ℕ} (ρ : Fin N → CurrentModule f V) (z : Fin N → ℂ)
variable (wT : Tensor (K := ℂ) (ι := Fin N) (W := V))

/-- High evaluation modes act one filtration step below their apparent degree. -/
theorem evalFbelow_high (c : Fin n) (i s d : ℕ) (hs : N ≤ s) :
    evalFbelow (evalAction ρ z) wT d ≤
      (evalFbelow (evalAction ρ z) wT (d + s - 1)).comap (evalOp ρ z c i s) := by
  rw [evalFbelow, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  change evalOp ρ z c i s (evalWord (evalAction ρ z) l wT) ∈
    evalFbelow (evalAction ρ z) wT (d + s - 1)
  rw [evalOp_high_rewrite ρ z c i s hs]
  simp only [LinearMap.neg_apply, LinearMap.sum_apply, LinearMap.smul_apply]
  apply Submodule.neg_mem
  apply Submodule.sum_mem
  intro k hk
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨(c, i, k) :: l, by
    change k + tDegree l < d + s - 1
    have hks : k < s := Finset.mem_range.mp hk
    omega, rfl⟩

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.evalFbelow_op
#print axioms VOA.DeligneAudit.Toroidal.evalFbelow_high
