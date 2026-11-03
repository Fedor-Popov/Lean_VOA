import VOA.DeligneAudit.DeligneFusionCVShifted
import VOA.DeligneAudit.DeligneFusionGarlandSl3

/-!
# High-mode transport for the A₂ cross-root CV relations

The common kernel of the high `f_θ` modes is stable under `f₁` and `f₂`.
On this kernel, a sufficiently high `f₂` mode commutes with the cutoff
`f₁` current series. Consequently its square kills every coefficient of
that series when its square kills the initial vector.

These are actual current-module statements. The high highest-root
truncation and initial square annihilation remain explicit hypotheses;
no fusion dimension bound or kernel presentation is assumed or proved.
-/

namespace VOA.DeligneAudit.A2.CVCrossRoot

open VOA.DeligneAudit.CVsl2

noncomputable section

section InvariantSubmodule

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A current coefficient preserves every submodule preserved by all its modes. -/
theorem Q_mem_invariant (F : ℕ → Module.End ℂ V) (M : Submodule ℂ V)
    (hF : ∀ k v, v ∈ M → F k v ∈ M) :
    ∀ r s v, v ∈ M → Q F r s v ∈ M
  | 0, s, v, hv => by
      rw [Q_zero_r]
      split_ifs
      · simpa using hv
      · exact M.zero_mem
  | r + 1, s, v, hv => by
      rw [Q_succ, LinearMap.coe_sum, Finset.sum_apply]
      refine M.sum_mem fun x _ => ?_
      change F x.1 (Q F r x.2 v) ∈ M
      exact hF x.1 _ (Q_mem_invariant F M hF r x.2 v hv)

/-- Commutation on an invariant submodule passes to current coefficients. -/
theorem Q_commute_on (F : ℕ → Module.End ℂ V) (Y : Module.End ℂ V)
    (M : Submodule ℂ V) (hF : ∀ k v, v ∈ M → F k v ∈ M)
    (hcomm : ∀ k v, v ∈ M → Y (F k v) = F k (Y v)) :
    ∀ r s v, v ∈ M → Y (Q F r s v) = Q F r s (Y v)
  | 0, s, v, _ => by
      rw [Q_zero_r]
      split_ifs <;> simp
  | r + 1, s, v, hv => by
      simp only [Q_succ, LinearMap.coe_sum, Finset.sum_apply, map_sum,
        Module.End.mul_apply]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hcomm x.1 _ (Q_mem_invariant F M hF r x.2 v hv),
        Q_commute_on F Y M hF hcomm r x.2 v hv]

/-- Square annihilation passes to the current coefficients on such a submodule. -/
theorem square_kills_Q_of_invariant (F : ℕ → Module.End ℂ V)
    (Y : Module.End ℂ V) (M : Submodule ℂ V)
    (hF : ∀ k v, v ∈ M → F k v ∈ M)
    (hY : ∀ v, v ∈ M → Y v ∈ M)
    (hcomm : ∀ k v, v ∈ M → Y (F k v) = F k (Y v))
    {w : V} (hw : w ∈ M) (hy2 : (Y ^ 2) w = 0) (r s : ℕ) :
    (Y ^ 2) (Q F r s w) = 0 := by
  simp only [pow_two, Module.End.mul_apply] at hy2 ⊢
  rw [Q_commute_on F Y M hF hcomm r s w hw,
    Q_commute_on F Y M hF hcomm r s (Y w) (hY w hw), hy2, map_zero]

end InvariantSubmodule

section CurrentModule

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Vectors annihilated by all highest-root modes at or above `L`. -/
def thetaKernel (ρ : CurrentModule bracketTable V) (L : ℕ) : Submodule ℂ V where
  carrier := {v | ∀ k, L ≤ k → ρ.op 5 k v = 0}
  zero_mem' := by intro k _; exact map_zero _
  add_mem' := by
    intro v w hv hw k hk
    rw [map_add, hv k hk, hw k hk, add_zero]
  smul_mem' := by
    intro c v hv k hk
    rw [map_smul, hv k hk, smul_zero]

theorem thetaKernel_f1 (ρ : CurrentModule bracketTable V) (L k : ℕ)
    {v : V} (hv : v ∈ thetaKernel ρ L) : ρ.op 3 k v ∈ thetaKernel ρ L := by
  intro q hq
  rw [← op3_op5 k q v, hv q hq, map_zero]

theorem thetaKernel_f2 (ρ : CurrentModule bracketTable V) (L k : ℕ)
    {v : V} (hv : v ∈ thetaKernel ρ L) : ρ.op 4 k v ∈ thetaKernel ρ L := by
  intro q hq
  rw [← op4_op5 k q v, hv q hq, map_zero]

/-- On the high-theta kernel, `f₂(b)` commutes with `f₁(k)` once `b+k ≥ L`. -/
theorem f2_f1_commute_on (ρ : CurrentModule bracketTable V) {L b k : ℕ}
    (hk : L ≤ b + k) {v : V} (hv : v ∈ thetaKernel ρ L) :
    ρ.op 4 b (ρ.op 3 k v) = ρ.op 3 k (ρ.op 4 b v) := by
  have hc : ρ.op 4 b (ρ.op 3 k v) =
      ρ.op 3 k (ρ.op 4 b v) + ρ.op 5 (b + k) v := by
    rw [comm_apply 4 3 b k v]
    simp [Fin.sum_univ_eight, bracketTable]
  rw [hc, hv (b + k) hk, add_zero]

/-- A high enough `f₂` square kills every coefficient of the cutoff `f₁` current. -/
theorem f2_square_QFrom (ρ : CurrentModule bracketTable V) {w : V} {L b p : ℕ}
    (hbp : L ≤ b + p) (htheta : ∀ k, L ≤ k → ρ.op 5 k w = 0)
    (hy2 : (ρ.op 4 b ^ 2) w = 0) (r s : ℕ) :
    (ρ.op 4 b ^ 2) (QFrom (ρ.op 3) p r s w) = 0 := by
  apply square_kills_Q_of_invariant (fromMode (ρ.op 3) p) (ρ.op 4 b)
    (thetaKernel ρ L)
  · intro k v hv
    by_cases hk : p ≤ k
    · simpa only [fromMode, if_pos hk] using thetaKernel_f1 ρ L k hv
    · simp only [fromMode, if_neg hk, LinearMap.zero_apply]
      exact (thetaKernel ρ L).zero_mem
  · intro v hv
    exact thetaKernel_f2 ρ L b hv
  · intro k v hv
    by_cases hk : p ≤ k
    · simp only [fromMode, if_pos hk]
      exact f2_f1_commute_on ρ (by omega) hv
    · simp only [fromMode, if_neg hk, LinearMap.zero_apply, map_zero]
  · exact htheta
  · exact hy2

/-- The corresponding single-mode consequence. -/
theorem f2_square_f1 (ρ : CurrentModule bracketTable V) {w : V} {L b k : ℕ}
    (hbk : L ≤ b + k) (htheta : ∀ q, L ≤ q → ρ.op 5 q w = 0)
    (hy2 : (ρ.op 4 b ^ 2) w = 0) :
    (ρ.op 4 b ^ 2) (ρ.op 3 k w) = 0 := by
  have h := f2_square_QFrom ρ hbk htheta hy2 1 k
  simpa only [QFrom, Q_one, fromMode, if_pos le_rfl] using h

/-- The tail annihilation needed in SRK's quadratic and cubic coefficient identities. -/
theorem tail_square_kills (ρ : CurrentModule bracketTable V) {w : V} (A B j : ℕ)
    (_hj : 2 ≤ j) (htheta : ∀ k, A + B + j ≤ k → ρ.op 5 k w = 0)
    (hy2 : (ρ.op 4 (B + j - 1) ^ 2) w = 0) (r s : ℕ) :
    (ρ.op 4 (B + j - 1) ^ 2) (QFrom (ρ.op 3) (A + 1) r s w) = 0 :=
  f2_square_QFrom ρ (by omega) htheta hy2 r s

/-- The same square kills the shifted first-root kernel generator for `j ≥ 2`. -/
theorem shifted_generator_square_kills (ρ : CurrentModule bracketTable V) {w : V}
    (A B j : ℕ) (hj : 2 ≤ j)
    (htheta : ∀ k, A + B + j ≤ k → ρ.op 5 k w = 0)
    (hy2 : (ρ.op 4 (B + j - 1) ^ 2) w = 0) :
    (ρ.op 4 (B + j - 1) ^ 2) (ρ.op 3 (A + j - 1) w) = 0 :=
  f2_square_f1 ρ (by omega) htheta hy2

end CurrentModule

end

end VOA.DeligneAudit.A2.CVCrossRoot

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.CVCrossRoot.f2_square_QFrom
#print axioms VOA.DeligneAudit.A2.CVCrossRoot.tail_square_kills
#print axioms VOA.DeligneAudit.A2.CVCrossRoot.shifted_generator_square_kills
end AxiomAudit
