import VOA.DeligneAudit.D4FusionToroidalFusionFilt

/-!
# The cyclic `t`-degree associated graded

Only filtration components occur in the numerator. The denominator consists
of strictly lower components at each degree. A high-mode shift identifies
the resulting action with the truncated toroidal commutator.
-/

namespace VOA.DeligneAudit.Toroidal.FusionGr

open VOA.DeligneAudit.Toroidal VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ}
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (A : ToroidalAction f V) (w : V) (m : ℕ)

/-- The polynomial-type shift needed to kill modes at least `m` on symbols. -/
def HighTShift : Prop :=
  ∀ c i s d, m ≤ s →
    evalFbelow A w d ≤ (evalFbelow A w (d + s - 1)).comap (A.op c i s)

/-- The direct sum of the actual filtration pieces. -/
def numerator : Submodule ℂ (ℕ →₀ V) :=
  Submodule.span ℂ {v | ∃ d x, x ∈ evalFbelow A w (d + 1) ∧
    v = Finsupp.single d x}

/-- The lower filtration piece in each tagged degree. -/
def denominator : Submodule ℂ (ℕ →₀ V) :=
  Submodule.span ℂ {v | ∃ d x, x ∈ evalFbelow A w d ∧
    v = Finsupp.single d x}

theorem denominator_le_numerator : denominator A w ≤ numerator A w := by
  rw [denominator, Submodule.span_le]
  rintro _ ⟨d, x, hx, rfl⟩
  exact Submodule.subset_span
    ⟨d, x, evalFbelow_mono A w (Nat.le_succ d) hx, rfl⟩

def kernel : Submodule ℂ (numerator A w) :=
  (denominator A w).comap (numerator A w).subtype

/-- The full associated graded of the cyclic `t` filtration. -/
abbrev Gr := numerator A w ⧸ kernel A w

def single (d : ℕ) (x : V) (hx : x ∈ evalFbelow A w (d + 1)) :
    numerator A w :=
  ⟨Finsupp.single d x, Submodule.subset_span ⟨d, x, hx, rfl⟩⟩

/-- Apply a toroidal operator and shift the tagged `t` degree. -/
def liftedOp (c : Fin n) (i s : ℕ) : (ℕ →₀ V) →ₗ[ℂ] (ℕ →₀ V) :=
  Finsupp.lmapDomain V ℂ (fun d : ℕ => d + s) ∘ₗ
    Finsupp.mapRange.linearMap (A.op c i s)

theorem liftedOp_single (c : Fin n) (i s d : ℕ) (x : V) :
    liftedOp A c i s (Finsupp.single d x) =
      Finsupp.single (d + s) (A.op c i s x) := by
  simp [liftedOp]

theorem lifted_comm (a b : Fin n) (i j r s : ℕ) (v : ℕ →₀ V) :
    liftedOp A a i r (liftedOp A b j s v) -
      liftedOp A b j s (liftedOp A a i r v) =
        ∑ e, f a b e • liftedOp A e (i + j) (r + s) v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v u hv hu =>
      simp only [map_add, Finset.sum_add_distrib, smul_add] at hv hu ⊢
      rw [← hv, ← hu]
      abel
  | single d x =>
      rw [liftedOp_single, liftedOp_single, liftedOp_single, liftedOp_single,
        show d + s + r = d + (r + s) by omega,
        show d + r + s = d + (r + s) by omega,
        ← Finsupp.single_sub, A.comm a b i j r s x, Finsupp.single_finsetSum]
      apply Finset.sum_congr rfl
      intro e _
      rw [liftedOp_single, ← Finsupp.smul_single]

theorem numerator_inv (c : Fin n) (i s : ℕ) :
    numerator A w ≤ (numerator A w).comap (liftedOp A c i s) := by
  rw [numerator, Submodule.span_le]
  rintro _ ⟨d, x, hx, rfl⟩
  change liftedOp A c i s (Finsupp.single d x) ∈ numerator A w
  rw [liftedOp_single]
  exact Submodule.subset_span ⟨d + s, _, by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      evalFbelow_op A w c i s (d + 1) hx, rfl⟩

theorem denominator_inv (c : Fin n) (i s : ℕ) :
    denominator A w ≤ (denominator A w).comap (liftedOp A c i s) := by
  rw [denominator, Submodule.span_le]
  rintro _ ⟨d, x, hx, rfl⟩
  change liftedOp A c i s (Finsupp.single d x) ∈ denominator A w
  rw [liftedOp_single]
  exact Submodule.subset_span
    ⟨d + s, _, evalFbelow_op A w c i s d hx, rfl⟩

/-- A high-mode lifted operator maps every genuine graded component to
the denominator, so its induced symbol vanishes. -/
theorem high_mem_denominator (h : HighTShift A w m) (c : Fin n) (i s : ℕ)
    (hs : m ≤ s) :
    numerator A w ≤ (denominator A w).comap (liftedOp A c i s) := by
  rw [numerator, Submodule.span_le]
  rintro _ ⟨d, x, hx, rfl⟩
  change liftedOp A c i s (Finsupp.single d x) ∈ denominator A w
  rw [liftedOp_single]
  exact Submodule.subset_span ⟨d + s, _, by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      Nat.add_sub_cancel_left] using h c i s (d + 1) hs hx, rfl⟩

def restrictedOp (c : Fin n) (i s : ℕ) :
    numerator A w →ₗ[ℂ] numerator A w where
  toFun v := ⟨liftedOp A c i s v.1, numerator_inv A w c i s v.2⟩
  map_add' v u := by
    apply Subtype.ext
    exact map_add (liftedOp A c i s) v.1 u.1
  map_smul' a v := by
    apply Subtype.ext
    exact map_smul (liftedOp A c i s) a v.1

theorem restrictedOp_kernel_inv (c : Fin n) (i s : ℕ) :
    kernel A w ≤ (kernel A w).comap (restrictedOp A w c i s) := by
  intro v hv
  exact denominator_inv A w c i s hv

/-- The truncated action, with high modes explicitly set to zero. -/
def grOp (c : Fin n) (i s : ℕ) : Gr A w →ₗ[ℂ] Gr A w :=
  if s < m then
    (kernel A w).mapQ (kernel A w) (restrictedOp A w c i s)
      (restrictedOp_kernel_inv A w c i s)
  else 0

theorem grOp_mk (c : Fin n) (i s : ℕ) (hs : s < m) (v : numerator A w) :
    grOp A w m c i s ((kernel A w).mkQ v) =
      (kernel A w).mkQ (restrictedOp A w c i s v) := by
  simp [grOp, hs, Submodule.mapQ_apply]

theorem grOp_high_zero (c : Fin n) (i s : ℕ) (hs : m ≤ s) :
    grOp A w m c i s = 0 := by
  simp [grOp, Nat.not_lt.mpr hs]

theorem grOp_comm (h : HighTShift A w m) (a b : Fin n)
    (i j r s : ℕ) (v : Gr A w) :
    grOp A w m a i r (grOp A w m b j s v) -
      grOp A w m b j s (grOp A w m a i r v) =
        if r + s < m then
          ∑ e, f a b e • grOp A w m e (i + j) (r + s) v else 0 := by
  by_cases hr : r < m
  · by_cases hs : s < m
    · obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (kernel A w) v
      by_cases hc : r + s < m
      · rw [if_pos hc]
        simp only [grOp_mk A w m a i r hr, grOp_mk A w m b j s hs]
        have hsub :
            restrictedOp A w a i r (restrictedOp A w b j s y) -
              restrictedOp A w b j s (restrictedOp A w a i r y) =
              ∑ e, f a b e • restrictedOp A w e (i + j) (r + s) y := by
          apply Subtype.ext
          simpa only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul]
            using lifted_comm A a b i j r s y.1
        rw [← map_sub, hsub, map_sum]
        apply Finset.sum_congr rfl
        intro e _
        rw [map_smul, grOp_mk A w m e (i + j) (r + s) hc]
      · rw [if_neg hc]
        simp only [grOp_mk A w m a i r hr, grOp_mk A w m b j s hs]
        rw [← map_sub]
        apply (Submodule.Quotient.mk_eq_zero (kernel A w)).mpr
        change liftedOp A a i r (liftedOp A b j s y.1) -
          liftedOp A b j s (liftedOp A a i r y.1) ∈ denominator A w
        rw [lifted_comm]
        apply Submodule.sum_mem
        intro e _
        exact Submodule.smul_mem _ _
          (high_mem_denominator A w m h e (i + j) (r + s)
            (Nat.le_of_not_lt hc) y.2)
    · have hc : ¬ r + s < m := by omega
      simp [grOp_high_zero A w m b j s (Nat.le_of_not_lt hs), hc]
  · have hc : ¬ r + s < m := by omega
    simp [grOp_high_zero A w m a i r (Nat.le_of_not_lt hr), hc]

/-- The cyclic associated graded is a truncated toroidal module. -/
def grToroidal (h : HighTShift A w m) : ToroidalModule f m (Gr A w) where
  op := grOp A w m
  high_zero := grOp_high_zero A w m
  comm := grOp_comm A w m h

end

end VOA.DeligneAudit.Toroidal.FusionGr

#print axioms VOA.DeligneAudit.Toroidal.FusionGr.high_mem_denominator
#print axioms VOA.DeligneAudit.Toroidal.FusionGr.grOp_comm
#print axioms VOA.DeligneAudit.Toroidal.FusionGr.grToroidal
