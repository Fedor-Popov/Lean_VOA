import VOA.DeligneAudit.DeligneFusionUnivG

/-! Type-generic current-degree associated graded and filtered source relations.
This light construction reuses the Finsupp realization of GrFilt without
importing its A2 character upper bounds. No character formula is assumed. -/
namespace VOA.DeligneAudit.D1TensorG.Gr

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.UnivG

noncomputable section
variable {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ}
variable {T : Type*} [AddCommGroup T] [Module ℂ T]
variable (R : CurrentModule f T) (w : T)

abbrev degree {σ : Type*} (l : List (σ × ℕ)) : ℕ :=
  VOA.DeligneAudit.SectorGraded.wordDeg l

/-- Actual current words below the indicated current degree. -/
def Fbelow (d : ℕ) : Submodule ℂ T :=
  Submodule.span ℂ {v | ∃ l : List (Fin n × ℕ), degree l < d ∧ v = wordOp R l w}

abbrev Fle (d : ℕ) : Submodule ℂ T := Fbelow R w (d + 1)

theorem degree_cons (x : Fin n × ℕ) (l : List (Fin n × ℕ)) :
    degree (x :: l) = x.2 + degree l := by simp [degree, SectorGraded.wordDeg]

theorem Fbelow_op (c : Fin n) (k d : ℕ) :
    Fbelow R w d ≤ (Fbelow R w (d + k)).comap (R.op c k) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l, hl, rfl⟩
  exact Submodule.subset_span ⟨(c, k) :: l, by rw [degree_cons]; omega, rfl⟩

theorem Fbelow_mono {d e : ℕ} (h : d ≤ e) : Fbelow R w d ≤ Fbelow R w e :=
  Submodule.span_mono fun _ ⟨l, hl, hv⟩ => ⟨l, by omega, hv⟩

theorem Fbelow_zero : Fbelow R w 0 = ⊥ := by
  apply Submodule.span_eq_bot.mpr
  rintro _ ⟨l, hl, _⟩
  omega

theorem w_mem_Fbelow {d : ℕ} (hd : 1 ≤ d) : w ∈ Fbelow R w d :=
  Submodule.subset_span ⟨[], by simp [degree, SectorGraded.wordDeg]; omega, rfl⟩

/-- A homogeneous presentation holds modulo strictly lower current degree. -/
structure FiltSat (spec : RelSpec n) : Prop where
  tail : ∀ t ∈ spec.tails, wordOp R t w ∈ Fbelow R w (degree t)
  eig : ∀ p ∈ spec.eig, R.op p.1 0 w = p.2 • w

/-- Lift each current action to its actual degree shift. -/
def gop (c : Fin n) (k : ℕ) : (ℕ →₀ T) →ₗ[ℂ] (ℕ →₀ T) :=
  Finsupp.lmapDomain T ℂ (fun p : ℕ => p + k) ∘ₗ Finsupp.mapRange.linearMap (R.op c k)

theorem gop_single (c : Fin n) (k p : ℕ) (v : T) :
    gop R c k (Finsupp.single p v) = Finsupp.single (p + k) (R.op c k v) := by
  simp [gop]

def gRep : CurrentModule f (ℕ →₀ T) where
  op := gop R
  comm := by
    intro a b r s v
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add u v hu hv =>
        simp only [map_add, Finset.sum_add_distrib, smul_add] at hu hv ⊢
        rw [← hu, ← hv]; abel
    | single p v =>
        rw [gop_single, gop_single, gop_single, gop_single,
          show p + s + r = p + (r + s) by omega,
          show p + r + s = p + (r + s) by omega,
          ← Finsupp.single_sub, R.comm, Finsupp.single_finsetSum]
        apply Finset.sum_congr rfl
        intro e _
        rw [gop_single, ← Finsupp.smul_single]

/-- The strictly lower part in each tagged degree. -/
def Lsub : Submodule ℂ (ℕ →₀ T) :=
  Submodule.span ℂ {v | ∃ d t, t ∈ Fbelow R w d ∧ v = Finsupp.single d t}

theorem Lsub_inv (c : Fin n) (k : ℕ) :
    Lsub R w ≤ (Lsub R w).comap ((gRep R).op c k) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨d, v, hv, rfl⟩
  exact Submodule.subset_span
    ⟨d + k, R.op c k v, Fbelow_op R w c k d hv, gop_single R c k d v⟩

theorem single_mem_Lsub {d : ℕ} {v : T} (hv : v ∈ Fbelow R w d) :
    Finsupp.single d v ∈ Lsub R w := Submodule.subset_span ⟨d, v, hv, rfl⟩

/-- The actual current-degree associated graded action. Its cyclic part is
used as the model; the ambient quotient may contain unused classes. -/
def grRep : CurrentModule f ((ℕ →₀ T) ⧸ Lsub R w) where
  op c k := (Lsub R w).mapQ (Lsub R w) ((gRep R).op c k) (Lsub_inv R w c k)
  comm := by
    intro a b r s v
    obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective (Lsub R w) v
    have hh := congrArg (Lsub R w).mkQ ((gRep R).comm a b r s u)
    simpa only [Submodule.mapQ_apply, map_sub, map_sum, map_smul] using hh

abbrev wg : (ℕ →₀ T) ⧸ Lsub R w := (Lsub R w).mkQ (Finsupp.single 0 w)

theorem gRep_word (p : ℕ) (v : T) : ∀ l : List (Fin n × ℕ),
    wordOp (gRep R) l (Finsupp.single p v) =
      Finsupp.single (p + degree l) (wordOp R l v)
  | [] => by simp [degree, SectorGraded.wordDeg]; rfl
  | x :: l => by
      change gop R x.1 x.2 (wordOp (gRep R) l (Finsupp.single p v)) = _
      rw [gRep_word p v l, gop_single, degree_cons]
      congr 1
      omega

theorem grRep_word : ∀ l : List (Fin n × ℕ),
    wordOp (grRep R w) l (wg R w) =
      (Lsub R w).mkQ (Finsupp.single (degree l) (wordOp R l w))
  | [] => rfl
  | x :: l => by
      change (grRep R w).op x.1 x.2 (wordOp (grRep R w) l (wg R w)) = _
      rw [grRep_word l]
      change (Lsub R w).mkQ (gop R x.1 x.2 _) = _
      rw [gop_single, degree_cons]
      congr 2
      omega

/-- Filtered source relations become exact relations in the actual graded action. -/
theorem gr_sat {spec : RelSpec n} (h : FiltSat R w spec) :
    Sat f (grRep R w) (wg R w) spec where
  tail t ht := by
    rw [grRep_word]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (single_mem_Lsub R w (h.tail t ht))
  eig p hp := by
    have hop : (grRep R w).op p.1 0 (wg R w) =
        (Lsub R w).mkQ (Finsupp.single 0 (R.op p.1 0 w)) := by
      simpa only [degree, SectorGraded.wordDeg, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Nat.add_zero] using grRep_word R w [(p.1, 0)]
    rw [hop, h.eig p hp, ← Finsupp.smul_single, map_smul]

end
end VOA.DeligneAudit.D1TensorG.Gr

#print axioms VOA.DeligneAudit.D1TensorG.Gr.gr_sat
