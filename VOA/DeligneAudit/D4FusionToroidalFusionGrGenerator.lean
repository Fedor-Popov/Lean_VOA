import VOA.DeligneAudit.D4FusionToroidalFusionEvalGr

/-!
# Generator symbols in the cyclic toroidal associated graded

Exact source relations pass to degree-zero generator classes. A scalar
positive `t` mode also vanishes because its image has degree zero.
-/

namespace VOA.DeligneAudit.Toroidal.FusionGr

open VOA.DeligneAudit.Toroidal VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ}
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (A : ToroidalAction f V) (w : V) (m : ℕ)

theorem generator_mem : w ∈ evalFbelow A w 1 :=
  Submodule.subset_span ⟨[], by simp [tDegree], rfl⟩

/-- The class of the actual tensor generator in `t` degree zero. -/
def grGenerator : Gr A w :=
  (kernel A w).mkQ (single A w 0 w (generator_mem A w))

theorem grOp_single (c : Fin n) (i s d : ℕ) (hs : s < m) (x : V)
    (hx : x ∈ evalFbelow A w (d + 1)) :
    grOp A w m c i s ((kernel A w).mkQ (single A w d x hx)) =
      (kernel A w).mkQ
        (single A w (d + s) (A.op c i s x) (by
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            evalFbelow_op A w c i s (d + 1) hx)) := by
  rw [grOp_mk A w m c i s hs]
  congr 1
  apply Subtype.ext
  exact liftedOp_single A c i s d x

/-- An exact relation on the source generator remains exact on its symbol. -/
theorem grGenerator_zero_of_raw (c : Fin n) (i s : ℕ)
    (hz : A.op c i s w = 0) : grOp A w m c i s (grGenerator A w) = 0 := by
  by_cases hs : s < m
  · rw [grGenerator, grOp_single A w m c i s 0 hs w (generator_mem A w)]
    apply (Submodule.Quotient.mk_eq_zero (kernel A w)).mpr
    change (single A w (0 + s) (A.op c i s w) (by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        evalFbelow_op A w c i s (0 + 1) (generator_mem A w))).1 ∈
      denominator A w
    simp only [single, Subtype.coe_mk, zero_add]
    rw [hz]
    simp
  · rw [grOp_high_zero A w m c i s (Nat.le_of_not_lt hs)]
    simp

/-- A scalar positive `t`-mode has zero leading symbol on the generator. -/
theorem grGenerator_zero_of_scalar (c : Fin n) (i s : ℕ)
    (hs : 1 ≤ s) (ha : ∃ a : ℂ, A.op c i s w = a • w) :
    grOp A w m c i s (grGenerator A w) = 0 := by
  by_cases hsm : s < m
  · rw [grGenerator, grOp_single A w m c i s 0 hsm w (generator_mem A w)]
    apply (Submodule.Quotient.mk_eq_zero (kernel A w)).mpr
    change (single A w (0 + s) (A.op c i s w) (by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        evalFbelow_op A w c i s (0 + 1) (generator_mem A w))).1 ∈
      denominator A w
    simp only [single, Subtype.coe_mk, zero_add]
    obtain ⟨a, ha⟩ := ha
    apply Submodule.subset_span
    refine ⟨s, A.op c i s w, ?_, rfl⟩
    rw [ha]
    exact Submodule.smul_mem _ a
      (evalFbelow_mono A w hs (generator_mem A w))
  · rw [grOp_high_zero A w m c i s (Nat.le_of_not_lt hsm)]
    simp

theorem grGenerator_eigen (c : Fin n) (a : ℂ) (hm : 0 < m)
    (he : A.op c 0 0 w = a • w) :
    grOp A w m c 0 0 (grGenerator A w) = a • grGenerator A w := by
  rw [grGenerator, grOp_single A w m c 0 0 0 hm w (generator_mem A w)]
  have heq : single A w (0 + 0) (A.op c 0 0 w) (by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        evalFbelow_op A w c 0 0 (0 + 1) (generator_mem A w)) =
      a • single A w 0 w (generator_mem A w) := by
    apply Subtype.ext
    simp [single, he]
  rw [heq, map_smul]

end

end VOA.DeligneAudit.Toroidal.FusionGr

#print axioms VOA.DeligneAudit.Toroidal.FusionGr.grGenerator_zero_of_raw
#print axioms VOA.DeligneAudit.Toroidal.FusionGr.grGenerator_zero_of_scalar
#print axioms VOA.DeligneAudit.Toroidal.FusionGr.grGenerator_eigen
