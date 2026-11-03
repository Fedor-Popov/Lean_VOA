import VOA.DeligneAudit.DeligneFusionCLAssembly
import VOA.DeligneAudit.DeligneFusionCount
import VOA.DeligneAudit.DeligneFusionGrade

/-!
# From a filtered (ungraded) model to `DemazureRealization N`

Let `T` be a finite-dimensional `CurrentModule` (no grading) and `w ∈ T`, and let `F_{<d}` be the span of the
words of degree `< d` applied to `w`.  If `w` satisfies the relations of `M_{N,0}` *up to lower filtration*
(`FiltRel`), then the associated graded — realized as `G = (ℕ →₀ T) ⧸ span{single d v : v ∈ F_{<d}}` with
`x ⊗ tᵏ` shifting the degree — is a model with `MabRel N 0` (`grRep`, `mabRel_gr`), whose degree-`d` cyclic
piece has dimension at least `dim F_{≤d} − dim F_{<d}` (`finrank_gr_ge`).

With (S1) (`finrank_cycDeg_le`) and `Σ_d demazureHilb N d = 9^N` (`demazureHilb_sum`), a single *total* lower
bound `9^N ≤ dim F_{≤D}` gives `DemazureRealization N` (`demazureRealization_of_filt`).  This is CL's fusion-
product lower bound, with the associated graded built by the Finsupp device.
-/

namespace VOA.DeligneAudit.GrFilt

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {T : Type} [AddCommGroup T] [Module ℂ T] (ρ : CurrentModule (bracketTable) T) (w : T)

/-- Words of degree `< d` applied to `w`. -/
def Fbelow (d : ℕ) : Submodule ℂ T :=
  Submodule.span ℂ {v | ∃ l : List (Fin 8 × ℕ), SectorGraded.wordDeg l < d ∧ v = wordOp ρ l w}

/-- Words of degree `≤ d` applied to `w`. -/
abbrev Fle (d : ℕ) : Submodule ℂ T := Fbelow ρ w (d + 1)

theorem wordDeg_cons (x : Fin 8 × ℕ) (l : List (Fin 8 × ℕ)) : SectorGraded.wordDeg (x :: l) = x.2 + SectorGraded.wordDeg l := by
  simp [SectorGraded.wordDeg]

theorem Fbelow_op (c : Fin 8) (k d : ℕ) : Fbelow ρ w d ≤ (Fbelow ρ w (d + k)).comap (ρ.op c k) := by
  rw [Fbelow, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  exact Submodule.subset_span ⟨(c, k) :: l, by rw [wordDeg_cons]; omega, rfl⟩

theorem Fbelow_mono {d e : ℕ} (h : d ≤ e) : Fbelow ρ w d ≤ Fbelow ρ w e :=
  Submodule.span_mono fun _ ⟨l, hl, hv⟩ => ⟨l, by omega, hv⟩

/-- The filtered relations of `M_{N,0}`. -/
structure FiltRel (N : ℕ) : Prop where
  raising : ∀ (e : Fin 8), e.val < 3 → ∀ r, ρ.op e r w = 0
  cartan : ∀ (h : Fin 8), 6 ≤ h.val → ∀ r, ρ.op h r w ∈ ℂ ∙ w
  cartan_zero : ∀ (h : Fin 8), 6 ≤ h.val → ρ.op h 0 w = (N : ℂ) • w
  lowering_f1 : (ρ.op 3 0)^[N + 1] w = 0
  lowering_f2 : (ρ.op 4 0)^[N + 1] w = 0
  trunc_f1 : ρ.op 3 N w ∈ Fbelow ρ w N
  trunc_f2 : ρ.op 4 N w ∈ Fbelow ρ w N
  trunc_theta : ρ.op 5 (2 * N) w ∈ Fbelow ρ w (2 * N)

/-! ## The degree lift and its quotient -/

/-- The lifted operator (degree shift by `k`). -/
def gop (c : Fin 8) (k : ℕ) : (ℕ →₀ T) →ₗ[ℂ] (ℕ →₀ T) :=
  Finsupp.lmapDomain T ℂ (fun p : ℕ => p + k) ∘ₗ Finsupp.mapRange.linearMap (ρ.op c k)

theorem gop_single (c : Fin 8) (k p : ℕ) (v : T) :
    gop ρ c k (Finsupp.single p v) = Finsupp.single (p + k) (ρ.op c k v) := by
  simp [gop]

/-- The degree lift as a current module. -/
def gRep : CurrentModule (bracketTable) (ℕ →₀ T) where
  op := gop ρ
  comm := by
    intro a b r s f
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg =>
        simp only [map_add, Finset.sum_add_distrib, smul_add] at hf hg ⊢
        rw [← hf, ← hg]; abel
    | single p v =>
        rw [gop_single, gop_single, gop_single, gop_single, show p + s + r = p + (r + s) by ring,
          show p + r + s = p + (r + s) by ring, ← Finsupp.single_sub, ρ.comm a b r s v,
          Finsupp.single_finsetSum]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [gop_single, ← Finsupp.smul_single]

/-- The lower filtration, placed in each degree. -/
def Lsub : Submodule ℂ (ℕ →₀ T) :=
  Submodule.span ℂ {f | ∃ d v, v ∈ Fbelow ρ w d ∧ f = Finsupp.single d v}

theorem Lsub_inv (c : Fin 8) (k : ℕ) : Lsub ρ w ≤ (Lsub ρ w).comap ((gRep ρ).op c k) := by
  rw [Lsub, Submodule.span_le]
  rintro _ ⟨d, v, hv, rfl⟩
  exact Submodule.subset_span ⟨d + k, ρ.op c k v, Fbelow_op ρ w c k d hv, (gop_single ρ c k d v)⟩

theorem single_mem_Lsub {d : ℕ} {v : T} (hv : v ∈ Fbelow ρ w d) : Finsupp.single d v ∈ Lsub ρ w :=
  Submodule.subset_span ⟨d, v, hv, rfl⟩

/-- The associated graded model. -/
abbrev grRep : CurrentModule (bracketTable) ((ℕ →₀ T) ⧸ Lsub ρ w) :=
  quotRep (gRep ρ) (Lsub ρ w) (Lsub_inv ρ w)

/-- Its generator. -/
abbrev wg : (ℕ →₀ T) ⧸ Lsub ρ w := (Lsub ρ w).mkQ (Finsupp.single 0 w)

theorem gRep_wordOp (p : ℕ) (v : T) : ∀ l : List (Fin 8 × ℕ),
    wordOp (gRep ρ) l (Finsupp.single p v) = Finsupp.single (p + SectorGraded.wordDeg l) (wordOp ρ l v)
  | [] => by simp [SectorGraded.wordDeg]; rfl
  | (x :: l) => by
      change gop ρ x.1 x.2 (wordOp (gRep ρ) l (Finsupp.single p v)) = _
      rw [gRep_wordOp p v l, gop_single, wordDeg_cons, add_assoc, add_comm (SectorGraded.wordDeg l)]
      rfl

theorem grRep_wordOp (l : List (Fin 8 × ℕ)) :
    wordOp (grRep ρ w) l (wg ρ w) = (Lsub ρ w).mkQ (Finsupp.single (SectorGraded.wordDeg l) (wordOp ρ l w)) := by
  rw [quot_wordOp, gRep_wordOp, zero_add]

theorem w_mem_Fbelow {d : ℕ} (hd : 1 ≤ d) : w ∈ Fbelow ρ w d :=
  Submodule.subset_span ⟨[], by simp [SectorGraded.wordDeg]; omega, rfl⟩

theorem grRep_op_wg (c : Fin 8) (k : ℕ) :
    (grRep ρ w).op c k (wg ρ w) = (Lsub ρ w).mkQ (Finsupp.single k (ρ.op c k w)) := by
  have := grRep_wordOp ρ w [(c, k)]
  simpa [SectorGraded.wordDeg] using this

/-- The associated graded satisfies the relations of `M_{N,0}`. -/
theorem mabRel_gr {N : ℕ} (h : FiltRel ρ w N) : MabRel (grRep ρ w) (wg ρ w) N 0 where
  raising e he r := by rw [grRep_op_wg, h.raising e he r]; simp
  cartan_pos hh h6 r hr := by
    rw [grRep_op_wg, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (h.cartan hh h6 r)
    rw [← ha]
    exact single_mem_Lsub ρ w (Submodule.smul_mem _ _ (w_mem_Fbelow ρ w hr))
  cartan_zero hh h6 := by
    rw [grRep_op_wg, h.cartan_zero hh h6, ← Finsupp.smul_single, map_smul]
    simp
  lowering_f1 := by
    rw [quot_iterate (gRep ρ) (Lsub ρ w) (Lsub_inv ρ w) ((3 : Fin 8), 0), iterate_eq_wordOp,
      gRep_wordOp, ← iterate_eq_wordOp]
    simp only [add_zero] at h ⊢
    rw [h.lowering_f1]; simp
  lowering_f2 := by
    rw [quot_iterate (gRep ρ) (Lsub ρ w) (Lsub_inv ρ w) ((4 : Fin 8), 0), iterate_eq_wordOp,
      gRep_wordOp, ← iterate_eq_wordOp]
    simp only [add_zero] at h ⊢
    rw [h.lowering_f2]; simp
  trunc_f1 := by
    rw [add_zero, grRep_op_wg, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact single_mem_Lsub ρ w h.trunc_f1
  trunc_f2 := by
    rw [add_zero, grRep_op_wg, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact single_mem_Lsub ρ w h.trunc_f2
  trunc_theta := by
    rw [add_zero, grRep_op_wg, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact single_mem_Lsub ρ w h.trunc_theta

/-! ## Dimensions -/

/-- Reading off degree `d`, modulo `F_{<d}`. -/
def readD (d : ℕ) : ((ℕ →₀ T) ⧸ Lsub ρ w) →ₗ[ℂ] (T ⧸ Fbelow ρ w d) :=
  (Lsub ρ w).liftQ ((Fbelow ρ w d).mkQ ∘ₗ Finsupp.lapply d) (by
    rw [Lsub, Submodule.span_le]
    rintro _ ⟨e, v, hv, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      Finsupp.lapply_apply, Finsupp.single_apply]
    split_ifs with he
    · subst he; simpa using hv
    · simp)

theorem readD_mk (d p : ℕ) (v : T) :
    readD ρ w d ((Lsub ρ w).mkQ (Finsupp.single p v)) = if p = d then (Fbelow ρ w d).mkQ v else 0 := by
  simp only [readD, Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.coe_comp, Function.comp_apply,
    Finsupp.lapply_apply]
  by_cases h : p = d
  · subst h; simp
  · simp [Finsupp.single_apply, h]

theorem Fle_le (d : ℕ) : Fle ρ w d ≤ Fbelow ρ w d ⊔ Submodule.span ℂ
    {v | ∃ l : List (Fin 8 × ℕ), SectorGraded.wordDeg l = d ∧ v = wordOp ρ l w} := by
  rw [Fle, Fbelow, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  rcases Nat.lt_or_ge (SectorGraded.wordDeg l) d with h | h
  · exact Submodule.mem_sup_left (Submodule.subset_span ⟨l, h, rfl⟩)
  · exact Submodule.mem_sup_right (Submodule.subset_span ⟨l, by omega, rfl⟩)

variable [FiniteDimensional ℂ T]

/-- The degree-`d` cyclic piece of the associated graded has dimension `≥ dim F_{≤d} − dim F_{<d}`. -/
theorem finrank_gr_ge (d : ℕ) :
    Module.finrank ℂ (Fle ρ w d) ≤
      Module.finrank ℂ (Fbelow ρ w d) + Module.finrank ℂ (cycDeg (grRep ρ w) (wg ρ w) d) := by
  have himg : (Fle ρ w d).map (Fbelow ρ w d).mkQ ≤ (cycDeg (grRep ρ w) (wg ρ w) d).map (readD ρ w d) := by
    refine (Submodule.map_mono (Fle_le ρ w d)).trans ?_
    rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, Submodule.map_span,
      Submodule.span_le]
    rintro _ ⟨v, ⟨l, hl, rfl⟩, rfl⟩
    refine ⟨_, Submodule.subset_span ⟨l, hl, rfl⟩, ?_⟩
    rw [grRep_wordOp, readD_mk, if_pos hl]
  have hcyc : cycDeg (grRep ρ w) (wg ρ w) d ≤
      LinearMap.range ((Lsub ρ w).mkQ ∘ₗ Finsupp.lsingle d) := by
    rw [cycDeg, Submodule.span_le]
    rintro _ ⟨l, hl, rfl⟩
    rw [grRep_wordOp, hl]
    exact ⟨_, rfl⟩
  haveI : FiniteDimensional ℂ (cycDeg (grRep ρ w) (wg ρ w) d) :=
    Submodule.finiteDimensional_of_le hcyc
  have h1 := Submodule.finrank_mono himg
  have h2 := LinearMap.finrank_range_le ((readD ρ w d).domRestrict (cycDeg (grRep ρ w) (wg ρ w) d))
  rw [LinearMap.range_domRestrict] at h2
  have h3 := finrank_le_map_add_inf (Fbelow ρ w d).mkQ (Fle ρ w d)
  rw [Submodule.ker_mkQ] at h3
  have h4 := Submodule.finrank_mono (inf_le_right : Fle ρ w d ⊓ Fbelow ρ w d ≤ Fbelow ρ w d)
  omega

omit [FiniteDimensional ℂ T] in
theorem Fbelow_zero : Fbelow ρ w 0 = ⊥ := by
  rw [Fbelow, Submodule.span_eq_bot]
  rintro _ ⟨l, hl, rfl⟩
  omega

/-- Telescoping: `dim F_{≤D} ≤ Σ_{d ≤ D} dim (cyclic piece of the associated graded in degree d)`. -/
theorem finrank_Fle_le_sum (D : ℕ) :
    Module.finrank ℂ (Fle ρ w D) ≤
      ∑ d ∈ Finset.range (D + 1), Module.finrank ℂ (cycDeg (grRep ρ w) (wg ρ w) d) := by
  induction D with
  | zero =>
      have := finrank_gr_ge ρ w 0
      rw [Fbelow_zero, finrank_bot] at this
      simpa using this
  | succ D ih =>
      have := finrank_gr_ge ρ w (D + 1)
      rw [Finset.sum_range_succ]
      change Module.finrank ℂ (Fle ρ w (D + 1)) ≤ _ at this
      have e : Fbelow ρ w (D + 1) = Fle ρ w D := rfl
      rw [e] at this
      omega

/-- **`DemazureRealization N` from a filtered model of total dimension `≥ 9^N`.** -/
theorem demazureRealization_of_filt {N : ℕ} (h : FiltRel ρ w N) (D : ℕ)
    (hD : 9 ^ N ≤ Module.finrank ℂ (Fle ρ w D)) : A2.DemazureRealization N := by
  refine ⟨_, _, _, grRep ρ w, wg ρ w, mabRel_gr ρ w h, fun d => ?_⟩
  have hR := mabRel_gr ρ w h
  set c : ℕ → ℕ := fun d => Module.finrank ℂ (cycDeg (grRep ρ w) (wg ρ w) d) with hc
  have hup : ∀ d, c d ≤ A2.demazureHilb N d := fun d => CLAssembly.finrank_cycDeg_le hR d
  obtain ⟨B, hB0, hBsum⟩ := A2.demazureHilb_sum N
  by_cases hdB : B ≤ d
  · rw [hB0 d hdB]; exact Nat.zero_le _
  set M := max B (D + 1)
  have hsumD : ∑ e ∈ Finset.range M, A2.demazureHilb N e = 9 ^ N := by
    rw [← hBsum]
    refine (Finset.sum_subset (Finset.range_mono (le_max_left _ _)) fun e he he' => ?_).symm
    exact hB0 e (by simp at he he'; omega)
  have hsumc : 9 ^ N ≤ ∑ e ∈ Finset.range M, c e :=
    hD.trans ((finrank_Fle_le_sum ρ w D).trans
      (Finset.sum_le_sum_of_subset (Finset.range_mono (le_max_right _ _))))
  by_contra hlt
  push_neg at hlt
  have : ∑ e ∈ Finset.range M, c e < ∑ e ∈ Finset.range M, A2.demazureHilb N e :=
    Finset.sum_lt_sum (fun e _ => hup e) ⟨d, by simp; omega, hlt⟩
  omega

end

end VOA.DeligneAudit.GrFilt

section AxiomAudit
#print axioms VOA.DeligneAudit.GrFilt.mabRel_gr
#print axioms VOA.DeligneAudit.GrFilt.demazureRealization_of_filt
end AxiomAudit
