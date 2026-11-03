import VOA.DeligneAudit.DeligneFusionD1TensorGGrRelations

/-! The actual current-degree graded tensor model satisfies the explicit
source presentation. The identical canonical ravFam specification is kept
in a separate compatibility wrapper to avoid its unrelated heavy imports.
No character equality or coefficientwise Demazure bound is assumed. -/
namespace VOA.DeligneAudit.D1TensorG.Gr

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.UnivG

noncomputable section

private theorem word_replicate {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (R : CurrentModule f V) (x : Fin n) (r : ℕ) (v : V) :
    ∀ k : ℕ, (R.op x r ^ k) v = wordOp R (List.replicate k (x, r)) v
  | 0 => rfl
  | k + 1 => by
      rw [pow_succ', Module.End.mul_apply, word_replicate R x r v k]
      rfl

/-- The explicit N-site source presentation: highest weight N theta,
sharp simple zero-mode powers, non-theta cutoff N and theta cutoff 2N.
The canonical Ravinder family has exactly these tails and eigenrelations;
its equality is checked in the separate resource-safe compatibility stage. -/
def tensorSpec (S : DeligneSectorData) (N : ℕ) : RelSpec S.n where
  tails := {t | (∃ e r, S.raising e ∧ t = [(e, r)]) ∨
    (∃ h r, S.cartan h ∧ 1 ≤ r ∧ t = [(h, r)]) ∨
    (∃ i, S.lowering i ∧ t = List.replicate (N * S.lowExp i + 1) (i, 0)) ∨
    (∃ x, S.fusion x ∧ t = [(x, if x = S.c₀ then 2 * N else N)]) ∨
    (∃ h r, S.cartanN h ∧ 1 ≤ r ∧ t = [(h, r)])}
  eig := {q | (∃ h, S.cartan h ∧ q = (h, ((N * S.thetaH h : ℕ) : ℂ))) ∨
    (∃ h, S.cartanN h ∧ q = (h, -((N * S.thetaN h : ℕ) : ℂ)))}

variable (S : DeligneSectorData)
variable (hskew : ∀ a b c, S.f a b c = -S.f b a c)
variable {N : ℕ} (z : Fin N → ℂ)

/-- All explicit source tails hold modulo strictly lower degree in
the shifted tensor model. The eigenrelations already hold exactly. -/
theorem tensor_filtSat :
    FiltSat (D1TensorG.rep S.f S.jacobi hskew z) (generator S.c₀) (tensorSpec S N) := by
  constructor
  · intro t ht
    simp only [tensorSpec, Set.mem_setOf_eq] at ht
    rcases ht with ⟨e, r, he, rfl⟩ | ⟨h, r, hh, hr, rfl⟩ |
      ⟨i, hi, rfl⟩ | ⟨x, _, rfl⟩ | ⟨h, r, hh, hr, rfl⟩
    · change (D1TensorG.rep S.f S.jacobi hskew z).op e r (generator S.c₀) ∈ _
      rw [tensor_raising S hskew z e he r]
      exact Submodule.zero_mem _
    · change (D1TensorG.rep S.f S.jacobi hskew z).op h r (generator S.c₀) ∈ _
      rw [tensor_cartan S hskew z h hh r]
      exact Submodule.smul_mem _ _ (w_mem_Fbelow _ _ (by
        simpa [degree, SectorGraded.wordDeg] using hr))
    · rw [← word_replicate, tensor_lowering S hskew z i hi]
      exact Submodule.zero_mem _
    · by_cases hx : x = S.c₀
      · subst x
        simpa only [if_pos rfl, degree, SectorGraded.wordDeg, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] using
          tensor_trunc_theta S hskew z
      · simpa only [if_neg hx, degree, SectorGraded.wordDeg, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] using
          tensor_trunc_non_theta S hskew z x hx
    · change (D1TensorG.rep S.f S.jacobi hskew z).op h r (generator S.c₀) ∈ _
      rw [tensor_cartanN S hskew z h hh r]
      exact Submodule.smul_mem _ _ (w_mem_Fbelow _ _ (by
        simpa [degree, SectorGraded.wordDeg] using hr))
  · rintro _ (⟨h, hh, rfl⟩ | ⟨h, hh, rfl⟩)
    · simpa using tensor_cartan S hskew z h hh 0
    · simpa using tensor_cartanN S hskew z h hh 0

/-- The constructed graded current action satisfies every explicit source relation. -/
theorem tensor_gr_sat :
    Sat S.f (grRep (D1TensorG.rep S.f S.jacobi hskew z) (generator S.c₀))
      (wg (D1TensorG.rep S.f S.jacobi hskew z) (generator S.c₀)) (tensorSpec S N) :=
  gr_sat _ _ (tensor_filtSat S hskew z)

end
end VOA.DeligneAudit.D1TensorG.Gr

#print axioms VOA.DeligneAudit.D1TensorG.Gr.tensor_filtSat
#print axioms VOA.DeligneAudit.D1TensorG.Gr.tensor_gr_sat
