import VOA.DeligneAudit.D4FusionToroidalFusionGrGenerator

/-!
# Homogeneous cyclic `u`-degree pieces

The toroidal operator of `u` degree `i` carries the cyclic word piece of
degree `k` into the piece of degree `k+i`.
-/

namespace VOA.DeligneAudit.Toroidal.FusionGr

open VOA.DeligneAudit.Toroidal

noncomputable section

variable {n m : ℕ} {f : Fin n → Fin n → Fin n → ℂ}
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem cycDegT_op (M : ToroidalModule f m V) (w : V)
    (c : Fin n) (i s k : ℕ) :
    cycDegT M w k ≤ (cycDegT M w (k + i)).comap (M.op c i s) := by
  rw [cycDegT, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  exact Submodule.subset_span ⟨(c, i, s) :: l, by
    change i + uDeg l = k + i
    omega, rfl⟩

variable (A : ToroidalAction f V) (w : V) (m : ℕ)
variable (h : HighTShift A w m)

theorem gr_u_shift (c : Fin n) (i s k : ℕ) :
    cycDegT (grToroidal A w m h) (grGenerator A w) k ≤
      (cycDegT (grToroidal A w m h) (grGenerator A w) (k + i)).comap
        ((grToroidal A w m h).op c i s) :=
  cycDegT_op (grToroidal A w m h) (grGenerator A w) c i s k

end

end VOA.DeligneAudit.Toroidal.FusionGr

#print axioms VOA.DeligneAudit.Toroidal.FusionGr.cycDegT_op
#print axioms VOA.DeligneAudit.Toroidal.FusionGr.gr_u_shift
