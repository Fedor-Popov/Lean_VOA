import VOA.DeligneAudit.DeligneFusionCLFilt

/-!
# Chari–Loktev Prop. 3.3.3 for `sl₃` (Gelfand–Tsetlin spanning at degree 0)

In a module with `MabRel ρ w N 0`, the degree-0 vectors `M(C) = f₁^{p−C} f_θ^C f₂^{q−C} w` with `C > N`
are combinations of those with `C ≤ N` (`prop333`).  The proof is a triangular induction: normal-ordering
`f₁^{a} f_θ^{c} f₂^{b} f₁^{N+1} w = 0` (Heisenberg relation `[f₂, f₁] = f_θ`) gives a relation whose top term is
a nonzero multiple of `M(C)`.
-/

namespace VOA.DeligneAudit.CLGT

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl

noncomputable section

section Heis

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {X Y Z : Module.End ℂ V}
  (hYX : Y * X - X * Y = Z) (hXZ : X * Z = Z * X) (hYZ : Y * Z = Z * Y)
include hYX hYZ

theorem comm_pow : ∀ k : ℕ, Y ^ k * X = X * Y ^ k + (k : ℂ) • (Z * Y ^ (k - 1))
  | 0 => by simp
  | k + 1 => by
      have ih := comm_pow k
      have h1 : Y * X = X * Y + Z := by rw [← hYX]; abel
      rw [pow_succ', mul_assoc, ih, mul_add, ← mul_assoc, h1, mul_smul_comm, ← mul_assoc Y Z, hYZ]
      rcases k with _ | k
      · simp
      · simp only [add_mul, mul_assoc, ← pow_succ', show k + 1 + 1 - 1 = k + 1 from rfl,
          show k + 1 - 1 = k from rfl, Nat.cast_add, Nat.cast_one, add_smul, one_smul]
        rw [pow_succ' Y (k + 1)]
        abel

/-- The span of the normal-ordered monomials `X^{m−i} Z^i Y^{b−i}`, `i < m`. -/
def Tsp (X Y Z : Module.End ℂ V) (m b : ℕ) : Submodule ℂ (Module.End ℂ V) :=
  Submodule.span ℂ {T | ∃ i, i < m ∧ T = X ^ (m - i) * Z ^ i * Y ^ (b - i)}

include hXZ in
/-- `Y^b X^m ≡ b^{(m)} Z^m Y^{b−m}` modulo lower `Z`-powers, for `m ≤ b`. -/
theorem normal_order : ∀ m b, m ≤ b →
    Y ^ b * X ^ m - ((b.descFactorial m : ℕ) : ℂ) • (Z ^ m * Y ^ (b - m)) ∈ Tsp X Y Z m b
  | 0, b, _ => by simp
  | m + 1, b, hmb => by
      have ih := normal_order m b (by omega)
      set s := Y ^ b * X ^ m - ((b.descFactorial m : ℕ) : ℂ) • (Z ^ m * Y ^ (b - m)) with hs
      have hsX : s * X ∈ Tsp X Y Z (m + 1) b := by
        have : ∀ T ∈ Tsp X Y Z m b, T * X ∈ Tsp X Y Z (m + 1) b := by
          intro T hT
          induction hT using Submodule.span_induction with
          | mem T hT =>
              obtain ⟨i, hi, rfl⟩ := hT
              rw [mul_assoc, comm_pow hYX hYZ, mul_add, mul_smul_comm]
              refine Submodule.add_mem _ (Submodule.subset_span ⟨i, by omega, ?_⟩)
                (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i + 1, by omega, ?_⟩))
              · rw [show m + 1 - i = (m - i) + 1 by omega, pow_succ]
                simp only [mul_assoc]
                rw [← mul_assoc (Z ^ i) X, show Z ^ i * X = X * Z ^ i from ((Commute.pow_right hXZ i).eq).symm]
                simp only [mul_assoc]
              · rw [show m + 1 - (i + 1) = m - i by omega, show b - (i + 1) = b - i - 1 by omega,
                  pow_succ Z i]
                simp only [mul_assoc]
          | zero => simp
          | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
          | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hx
        exact this s ih
      have key : Y ^ b * X ^ (m + 1) - ((b.descFactorial (m + 1) : ℕ) : ℂ) • (Z ^ (m + 1) * Y ^ (b - (m + 1)))
          = s * X + ((b.descFactorial m : ℕ) : ℂ) • (X * Z ^ m * Y ^ (b - m)) := by
        rw [hs, sub_mul, smul_mul_assoc, mul_assoc (Z ^ m), comm_pow hYX hYZ, mul_add, mul_smul_comm,
          pow_succ X m, ← mul_assoc, Nat.descFactorial_succ]
        rw [← mul_assoc (Z ^ m) X, show Z ^ m * X = X * Z ^ m from ((Commute.pow_right hXZ m).eq).symm,
          ← mul_assoc (Z ^ m) Z, ← pow_succ, show b - m - 1 = b - (m + 1) by omega]
        push_cast
        simp only [smul_add, smul_smul]
        module
      rw [key]
      refine Submodule.add_mem _ hsX (Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, by omega, ?_⟩))
      rw [show m + 1 - m = 1 by omega, pow_one]

end Heis

/-! ## The `sl₃` statement -/

section Sl3

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule (bracketTable) V) (w : V)

/-- `M(p,q,C) = f₁^{p−C} f_θ^C f₂^{q−C} w`. -/
def Mv (p q C : ℕ) : V := (ρ.op 3 0 ^ (p - C) * ρ.op 5 0 ^ C * ρ.op 4 0 ^ (q - C)) w

theorem f2f1 : ρ.op 4 0 * ρ.op 3 0 - ρ.op 3 0 * ρ.op 4 0 = ρ.op 5 0 := by
  ext v; simp only [LinearMap.sub_apply, Module.End.mul_apply]
  rw [ρ.comm 4 3 0 0 v]; simp [Fin.sum_univ_eight, bracketTable]

theorem f1fθ : ρ.op 3 0 * ρ.op 5 0 = ρ.op 5 0 * ρ.op 3 0 := by
  ext v; simp only [Module.End.mul_apply]
  rw [comm_apply 3 5 0 0]; simp [Fin.sum_univ_eight, bracketTable]

theorem f2fθ : ρ.op 4 0 * ρ.op 5 0 = ρ.op 5 0 * ρ.op 4 0 := by
  ext v; simp only [Module.End.mul_apply]
  rw [comm_apply 4 5 0 0]; simp [Fin.sum_univ_eight, bracketTable]

/-- **CL Prop. 3.3.3 for `sl₃`**: `M(p,q,C)` with `C > N` is a combination of `M(p,q,C')`,
`C' ≤ N`. -/
theorem prop333 {N : ℕ} (h : MabRel ρ w N 0) :
    ∀ C p q, C ≤ p → C ≤ q →
      Mv ρ w p q C ∈ Submodule.span ℂ {v | ∃ C', C' ≤ N ∧ C' ≤ p ∧ C' ≤ q ∧ v = Mv ρ w p q C'} := by
  intro C
  induction C using Nat.strong_induction_on with
  | _ C ih =>
  intro p q hp hq
  by_cases hC : C ≤ N
  · exact Submodule.subset_span ⟨C, hC, hp, hq, rfl⟩
  set X := ρ.op 3 0
  set Y := ρ.op 4 0
  set Z := ρ.op 5 0
  set c := C - N - 1
  set a := p - C
  set b := q - c
  have hrel : (X ^ a * Z ^ c * (Y ^ b * X ^ (N + 1))) w = 0 := by
    rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, Module.End.pow_apply X (N + 1)]
    have := h.lowering_f1
    simp only [add_zero] at this
    rw [this]; simp
  have hno := normal_order (f2f1 ρ) (f1fθ ρ) (f2fθ ρ) (N + 1) b (by omega)
  set s := Y ^ b * X ^ (N + 1) - ((b.descFactorial (N + 1) : ℕ) : ℂ) • (Z ^ (N + 1) * Y ^ (b - (N + 1)))
  have hsplit : Y ^ b * X ^ (N + 1) =
      ((b.descFactorial (N + 1) : ℕ) : ℂ) • (Z ^ (N + 1) * Y ^ (b - (N + 1))) + s := by
    simp only [s]; abel
  have hZX : ∀ i k, Z ^ i * X ^ k = X ^ k * Z ^ i := fun i k =>
    ((Commute.pow_pow (show Commute X Z from f1fθ ρ) k i).eq).symm
  -- the top term is `M(C)`
  have htop : (X ^ a * Z ^ c * (Z ^ (N + 1) * Y ^ (b - (N + 1)))) w = Mv ρ w p q C := by
    simp only [Mv, X, Y, Z]
    rw [show b - (N + 1) = q - C by omega, ← mul_assoc, mul_assoc (X ^ a) (Z ^ c), ← pow_add,
      show c + (N + 1) = C by omega]
  -- the lower terms
  have hlow : (X ^ a * Z ^ c * s) w ∈
      Submodule.span ℂ {v | ∃ C', C' ≤ N ∧ C' ≤ p ∧ C' ≤ q ∧ v = Mv ρ w p q C'} := by
    have : ∀ T ∈ Tsp X Y Z (N + 1) b, (X ^ a * Z ^ c * T) w ∈
        Submodule.span ℂ {v | ∃ C', C' ≤ N ∧ C' ≤ p ∧ C' ≤ q ∧ v = Mv ρ w p q C'} := by
      intro T hT
      induction hT using Submodule.span_induction with
      | mem T hT =>
          obtain ⟨i, hi, rfl⟩ := hT
          have := ih (c + i) (by omega) p q (by omega) (by omega)
          convert this using 1
          simp only [Mv, X, Y, Z]
          rw [show q - (c + i) = b - i by omega, show p - (c + i) = a + (N + 1 - i) by omega]
          simp only [← mul_assoc]
          rw [mul_assoc (X ^ a) (Z ^ c), hZX, ← mul_assoc, ← pow_add, mul_assoc _ (Z ^ c), ← pow_add]
      | zero => simp
      | add x y _ _ hx hy => rw [mul_add, LinearMap.add_apply]; exact Submodule.add_mem _ hx hy
      | smul r x _ hx => rw [mul_smul_comm, LinearMap.smul_apply]; exact Submodule.smul_mem _ _ hx
    exact this s hno
  rw [hsplit, mul_add, mul_smul_comm, LinearMap.add_apply, LinearMap.smul_apply, htop] at hrel
  have hκ : ((b.descFactorial (N + 1) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (by omega)).ne'
  have : Mv ρ w p q C = -(((b.descFactorial (N + 1) : ℕ) : ℂ))⁻¹ • (X ^ a * Z ^ c * s) w := by
    rw [neg_smul, eq_neg_iff_add_eq_zero, ← smul_eq_zero_iff_right hκ, smul_add, smul_smul,
      mul_inv_cancel₀ hκ, one_smul]
    exact hrel
  rw [this]
  exact Submodule.smul_mem _ _ hlow

end Sl3

end

end VOA.DeligneAudit.CLGT

section AxiomAudit
#print axioms VOA.DeligneAudit.CLGT.prop333
end AxiomAudit
