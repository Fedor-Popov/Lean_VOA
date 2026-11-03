import VOA.DeligneAudit.DeligneFusionD1TensorGGrRankProjection

/-!
# The actual cyclic graded module inside the ambient quotient

An explicit filtration cutoff identifies this cyclic space with the range
of the finite product sum map. Its finiteness and rank therefore concern
the actual generated module, without asserting finiteness of the ambient
quotient.
-/

namespace VOA.DeligneAudit.D1TensorG.Gr

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.UnivG

noncomputable section

variable {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ}
variable {T : Type*} [AddCommGroup T] [Module ℂ T]
variable (R : CurrentModule f T) (w : T)

abbrev GrSpace := (ℕ →₀ T) ⧸ Lsub R w

def cyclicGr : Submodule ℂ (GrSpace R w) :=
  Submodule.span ℂ (Set.range fun l : List (Fin n × ℕ) =>
    wordOp (grRep R w) l (wg R w))

theorem word_mem_cyclicGr (l : List (Fin n × ℕ)) :
    wordOp (grRep R w) l (wg R w) ∈ cyclicGr R w :=
  Submodule.subset_span ⟨l, rfl⟩

theorem cyclicGr_inv (c : Fin n) (k : ℕ) :
    cyclicGr R w ≤ (cyclicGr R w).comap ((grRep R w).op c k) := by
  rw [cyclicGr, Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  exact word_mem_cyclicGr R w ((c, k) :: l)

def cyclicRep : CurrentModule f (cyclicGr R w) where
  op c k := ((grRep R w).op c k).restrict (fun _ hx => cyclicGr_inv R w c k hx)
  comm a b r s x := by
    apply Subtype.ext
    simpa only [LinearMap.coe_restrict_apply, Submodule.coe_sub, Submodule.coe_sum,
      Submodule.coe_smul] using (grRep R w).comm a b r s (x : GrSpace R w)

def cyclicGenerator : cyclicGr R w :=
  ⟨wg R w, word_mem_cyclicGr R w []⟩

theorem cyclicRep_word : ∀ l : List (Fin n × ℕ),
    ((wordOp (cyclicRep R w) l (cyclicGenerator R w) : cyclicGr R w) : GrSpace R w) =
      wordOp (grRep R w) l (wg R w)
  | [] => rfl
  | x :: l => by
      change (grRep R w).op x.1 x.2
        ((wordOp (cyclicRep R w) l (cyclicGenerator R w) : cyclicGr R w) : GrSpace R w) = _
      rw [cyclicRep_word]
      rfl

theorem cyclicRep_sat {spec : RelSpec n} (h : Sat f (grRep R w) (wg R w) spec) :
    Sat f (cyclicRep R w) (cyclicGenerator R w) spec where
  tail l hl := by
    apply Subtype.ext
    exact (cyclicRep_word R w l).trans (h.tail l hl)
  eig p hp := by
    apply Subtype.ext
    exact h.eig p hp

theorem cyclicRep_filtSat {spec : RelSpec n} (h : FiltSat R w spec) :
    Sat f (cyclicRep R w) (cyclicGenerator R w) spec :=
  cyclicRep_sat R w (gr_sat R w h)

theorem cyclicRep_span : Submodule.span ℂ
    (Set.range fun l : List (Fin n × ℕ) =>
      wordOp (cyclicRep R w) l (cyclicGenerator R w)) = ⊤ := by
  let P : Submodule ℂ (cyclicGr R w) := Submodule.span ℂ
    (Set.range fun l : List (Fin n × ℕ) =>
      wordOp (cyclicRep R w) l (cyclicGenerator R w))
  have hC : cyclicGr R w ≤ P.map (cyclicGr R w).subtype := by
    apply Submodule.span_le.mpr
    rintro _ ⟨l, rfl⟩
    exact ⟨wordOp (cyclicRep R w) l (cyclicGenerator R w),
      Submodule.subset_span ⟨l, rfl⟩, cyclicRep_word R w l⟩
  apply top_unique
  intro x _
  change x ∈ P
  obtain ⟨y, hy, hval⟩ := hC x.property
  have he : y = x := Subtype.ext hval
  rw [← he]
  exact hy

theorem map_cycDeg_cyclicRep (d : ℕ) :
    (cycDeg (cyclicRep R w) (cyclicGenerator R w) d).map (cyclicGr R w).subtype =
      GradePiece R w d := by
  change (cycDeg (cyclicRep R w) (cyclicGenerator R w) d).map (cyclicGr R w).subtype =
    cycDeg (grRep R w) (wg R w) d
  rw [cycDeg, cycDeg, Submodule.map_span]
  apply congrArg (Submodule.span ℂ)
  ext x
  constructor
  · rintro ⟨y, ⟨l, hl, rfl⟩, rfl⟩
    exact ⟨l, hl, cyclicRep_word R w l⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨wordOp (cyclicRep R w) l (cyclicGenerator R w),
      ⟨l, hl, rfl⟩, cyclicRep_word R w l⟩

theorem finrank_cycDeg_cyclicRep (d : ℕ) :
    Module.finrank ℂ (cycDeg (cyclicRep R w) (cyclicGenerator R w) d) =
      Module.finrank ℂ (GradePiece R w d) := by
  rw [← map_cycDeg_cyclicRep R w d]
  exact (Submodule.finrank_map_subtype_eq (cyclicGr R w)
    (cycDeg (cyclicRep R w) (cyclicGenerator R w) d)).symm

theorem gradePiece_le_cyclicGr (d : ℕ) : GradePiece R w d ≤ cyclicGr R w := by
  change cycDeg (grRep R w) (wg R w) d ≤ cyclicGr R w
  rw [cycDeg, Submodule.span_le]
  rintro _ ⟨l, _, rfl⟩
  exact word_mem_cyclicGr R w l

theorem pieceSum_single (B : ℕ) (i : Fin B) (x : GradePiece R w i.val) :
    pieceSum R w B (Pi.single i x) = (x : GrSpace R w) := by
  change (∑ j : Fin B,
    ((Pi.single i x : Π j : Fin B, GradePiece R w j.val) j : GrSpace R w)) = _
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hj : (Pi.single i x : Π j : Fin B, GradePiece R w j.val) j = 0 := by
      simp [hji]
    rw [hj]
    rfl
  · simp

theorem word_zero_of_cutoff (B : ℕ) (hB : Fbelow R w B = ⊤)
    (l : List (Fin n × ℕ)) (hl : B ≤ degree l) :
    wordOp (grRep R w) l (wg R w) = 0 := by
  rw [grRep_word]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply single_mem_Lsub R w
  apply Fbelow_mono R w hl
  rw [hB]
  exact Submodule.mem_top

theorem range_pieceSum_eq_cyclicGr (B : ℕ) (hB : Fbelow R w B = ⊤) :
    LinearMap.range (pieceSum R w B) = cyclicGr R w := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    change (∑ i : Fin B, (v i : GrSpace R w)) ∈ cyclicGr R w
    exact Submodule.sum_mem _ fun i _ => gradePiece_le_cyclicGr R w i.val (v i).property
  · rw [cyclicGr, Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    change wordOp (grRep R w) l (wg R w) ∈ LinearMap.range (pieceSum R w B)
    by_cases hl : degree l < B
    · let i : Fin B := ⟨degree l, hl⟩
      let x : GradePiece R w i.val :=
        ⟨wordOp (grRep R w) l (wg R w), Submodule.subset_span ⟨l, rfl, rfl⟩⟩
      exact ⟨Pi.single i x, pieceSum_single R w B i x⟩
    · rw [word_zero_of_cutoff R w B hB l (by omega)]
      exact Submodule.zero_mem _

theorem finite_cyclicGr_of_cutoff [FiniteDimensional ℂ T]
    (B : ℕ) (hB : Fbelow R w B = ⊤) : FiniteDimensional ℂ (cyclicGr R w) := by
  letI (i : Fin B) : FiniteDimensional ℂ (GradePiece R w i.val) :=
    finite_cycDeg R w i.val
  rw [← range_pieceSum_eq_cyclicGr R w B hB]
  infer_instance

theorem finrank_cyclicGr_eq_fin_sum [FiniteDimensional ℂ T]
    (B : ℕ) (hB : Fbelow R w B = ⊤) :
    Module.finrank ℂ (cyclicGr R w) =
      ∑ i : Fin B, Module.finrank ℂ (GradePiece R w i.val) := by
  letI (i : Fin B) : FiniteDimensional ℂ (GradePiece R w i.val) :=
    finite_cycDeg R w i.val
  rw [← range_pieceSum_eq_cyclicGr R w B hB,
    LinearMap.finrank_range_of_inj (pieceSum_injective R w B), Module.finrank_pi_fintype]

theorem finrank_cyclicGr_eq_sum [FiniteDimensional ℂ T]
    (B : ℕ) (hB : Fbelow R w B = ⊤) :
    Module.finrank ℂ (cyclicGr R w) =
      ∑ d ∈ Finset.range B, Module.finrank ℂ (GradePiece R w d) := by
  rw [finrank_cyclicGr_eq_fin_sum R w B hB]
  exact Fin.sum_univ_eq_sum_range (fun d => Module.finrank ℂ (GradePiece R w d)) B

end

end VOA.DeligneAudit.D1TensorG.Gr

#print axioms VOA.DeligneAudit.D1TensorG.Gr.cyclicRep_sat
#print axioms VOA.DeligneAudit.D1TensorG.Gr.cyclicRep_span
#print axioms VOA.DeligneAudit.D1TensorG.Gr.finrank_cycDeg_cyclicRep
#print axioms VOA.DeligneAudit.D1TensorG.Gr.range_pieceSum_eq_cyclicGr
#print axioms VOA.DeligneAudit.D1TensorG.Gr.finite_cyclicGr_of_cutoff
#print axioms VOA.DeligneAudit.D1TensorG.Gr.finrank_cyclicGr_eq_sum
