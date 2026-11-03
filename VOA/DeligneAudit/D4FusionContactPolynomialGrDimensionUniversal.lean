import VOA.DeligneAudit.D4FusionContactPolynomialGrDimensionSource
import VOA.DeligneAudit.DeligneFusionUnivG

/-! Homogeneous universal current degrees and transfer to arbitrary sources.
Each RelSpec has one-word tails and degree-zero eigenrelations, so its
universal quotient has actual degree projections. Independence is proved
there; arbitrary ungraded source pieces are bounded only through univMapG.
No source finite-dimensionality or flatness premise is used. -/
namespace VOA.DeligneAudit.D4FusionContact.Polynomial

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.UnivG

noncomputable section
local notation "deg" => VOA.DeligneAudit.SectorGraded.wordDeg
variable {n : ℕ} (f : Fin n → Fin n → Fin n → ℂ)

theorem uDeg_cons (x : Ltr n) (l : List (Ltr n)) : deg (x :: l) = x.2 + deg l := by
  simp [VOA.DeligneAudit.SectorGraded.wordDeg]

theorem uDeg_nil : deg ([] : List (Ltr n)) = 0 := rfl

theorem uDeg_append (l m : List (Ltr n)) : deg (l ++ m) = deg l + deg m := by
  simp [VOA.DeligneAudit.SectorGraded.wordDeg]

/-! ## Degree projections -/

/-- The projection of formal combinations of words onto word degree `N`. -/
def univProjF (N : ℕ) : FreeW n →ₗ[ℂ] FreeW n :=
  Finsupp.linearCombination ℂ (fun l => if deg l = N then sw l else 0)

theorem univProjF_sw (N : ℕ) (l : List (Ltr n)) :
    univProjF N (sw l) = if deg l = N then sw l else 0 := by
  simp [univProjF, sw]

/-- **Every relation subspace is homogeneous.** -/
theorem univProjF_J (R : RelSpec n) (N : ℕ) : Jrel f R ≤ (Jrel f R).comap (univProjF N) := by
  rw [Jrel, Submodule.span_le]
  intro g hg
  have hmem : g ∈ Jrel f R := Submodule.subset_span hg
  change univProjF N g ∈ Jrel f R
  rcases hg with ⟨p, ⟨s, x, y, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨q, hq, rfl⟩⟩
  · by_cases hD : deg p + (x.2 + (y.2 + deg s)) = N
    · have h2 : deg p + (y.2 + (x.2 + deg s)) = N := by omega
      have h3 : deg p + (x.2 + y.2 + deg s) = N := by omega
      have : univProjF N (commInst f p s x y) = commInst f p s x y := by
        simp only [commInst, map_sub, map_sum, map_smul, univProjF_sw, uDeg_append, uDeg_cons]
        simp [hD, h2, h3]
      rw [this]; exact hmem
    · have h2 : ¬ deg p + (y.2 + (x.2 + deg s)) = N := by omega
      have h3 : ¬ deg p + (x.2 + y.2 + deg s) = N := by omega
      have : univProjF N (commInst f p s x y) = 0 := by
        simp only [commInst, map_sub, map_sum, map_smul, univProjF_sw, uDeg_append, uDeg_cons]
        simp [hD, h2, h3]
      rw [this]; exact zero_mem _
  · rw [univProjF_sw]; split_ifs
    · exact hmem
    · exact zero_mem _
  · by_cases hD : deg p = N
    · have : univProjF N (sw (p ++ [(q.1, 0)]) - q.2 • sw p) =
          sw (p ++ [(q.1, 0)]) - q.2 • sw p := by
        simp only [map_sub, map_smul, univProjF_sw, uDeg_append, uDeg_cons, uDeg_nil, add_zero]
        simp [hD]
      rw [this]; exact hmem
    · have : univProjF N (sw (p ++ [(q.1, 0)]) - q.2 • sw p) = 0 := by
        simp only [map_sub, map_smul, univProjF_sw, uDeg_append, uDeg_cons, uDeg_nil, add_zero]
        simp [hD]
      rw [this]; exact zero_mem _

/-- The degree projection on `U(R)`. -/
def univProj (R : RelSpec n) (N : ℕ) : UModG f R →ₗ[ℂ] UModG f R :=
  (Jrel f R).mapQ (Jrel f R) (univProjF N) (univProjF_J f R N)

theorem univProj_mk (R : RelSpec n) (N : ℕ) (l : List (Ltr n)) :
    univProj f R N (Submodule.Quotient.mk (sw l)) =
      if deg l = N then (Submodule.Quotient.mk (sw l) : UModG f R) else 0 := by
  rw [univProj, Submodule.mapQ_apply, univProjF_sw]
  split_ifs <;> simp

theorem univProj_cyc (R : RelSpec n) (N : ℕ) {x : UModG f R}
    (hx : x ∈ cycDeg (univRepG f R) (wUG f R) N) : univProj f R N x = x := by
  induction hx using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨l, hl, rfl⟩ := hv
      rw [wordOp_univG, univProj_mk, if_pos hl]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

/-- All universal word vectors span the actual universal quotient. -/
theorem universal_word_span (spec : RelSpec n) :
    Submodule.span ℂ (Set.range fun l : List (Ltr n) =>
      wordOp (univRepG f spec) l (wUG f spec)) = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective (Jrel f spec) x
  induction u using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u v hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv
  | single l a =>
      rw [show Finsupp.single l a = a • sw l from by simp [sw], map_smul]
      exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨l, wordOp_univG f spec l⟩)

/-- A universal current-degree projection is identity on its own piece
and zero on every different actual degree piece. -/
theorem univProj_cyc_degree (spec : RelSpec n) (d e : ℕ) {x : UModG f spec}
    (hx : x ∈ cycDeg (univRepG f spec) (wUG f spec) e) :
    univProj f spec d x = if e = d then x else 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      simp only [wordOp_univG, univProj_mk, hl]
  | zero => simp
  | add x y hx hy ihx ihy => rw [map_add, ihx, ihy]; split_ifs <;> simp
  | smul a x hx ih => rw [map_smul, ih]; split_ifs <;> simp

/-- The sum of finitely many actual universal current-degree components. -/
def univPieceSum (spec : RelSpec n) (s : Finset ℕ) :
    (∀ d : {e : ℕ // e ∈ s}, cycDeg (univRepG f spec) (wUG f spec) d.1) →ₗ[ℂ]
      UModG f spec where
  toFun x := ∑ d, (x d : UModG f spec)
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum]

theorem univProj_pieceSum (spec : RelSpec n) (s : Finset ℕ)
    (x : ∀ d : {e : ℕ // e ∈ s}, cycDeg (univRepG f spec) (wUG f spec) d.1)
    (i : {e : ℕ // e ∈ s}) :
    univProj f spec i.1 (univPieceSum f spec s x) = x i := by
  change univProj f spec i.1 (∑ d, (x d : UModG f spec)) = x i
  rw [map_sum, Finset.sum_eq_single i]
  · simpa using univProj_cyc_degree f spec i.1 i.1 (x i).property
  · intro d _ hdi
    rw [univProj_cyc_degree f spec i.1 d.1 (x d).property,
      if_neg (fun h => hdi (Subtype.ext h))]
  · simp

theorem univPieceSum_injective (spec : RelSpec n) (s : Finset ℕ) :
    Function.Injective (univPieceSum f spec s) := by
  intro x y hxy
  funext i
  apply Subtype.ext
  have hh := congrArg (univProj f spec i.1) hxy
  simpa only [univProj_pieceSum] using hh

/-- Current-degree independence is used only in the homogeneous universal
quotient, never asserted for arbitrary ungraded source pieces. -/
theorem sum_finrank_univ_cycDeg_le (spec : RelSpec n) (s : Finset ℕ)
    [FiniteDimensional ℂ (UModG f spec)] :
    (∑ d ∈ s, Module.finrank ℂ (cycDeg (univRepG f spec) (wUG f spec) d)) ≤
      Module.finrank ℂ (UModG f spec) := by
  have hh := LinearMap.finrank_le_finrank_of_injective (univPieceSum_injective f spec s)
  rw [Module.finrank_pi_fintype] at hh
  calc
    _ = ∑ d : {e : ℕ // e ∈ s},
        Module.finrank ℂ (cycDeg (univRepG f spec) (wUG f spec) d.1) :=
      (Finset.sum_coe_sort (s := s)
        (f := fun d => Module.finrank ℂ (cycDeg (univRepG f spec) (wUG f spec) d))).symm
    _ ≤ _ := hh

variable {f} {spec : RelSpec n}
variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule f V} {w : V}

/-- Finite universal source rank bounds the sum of degree ranks in any
ungraded quotient source, by its actual universal word map. -/
theorem sum_source_cycDeg_le_univ [FiniteDimensional ℂ (UModG f spec)]
    (h : Sat f R w spec) (B : ℕ) :
    (∑ d ∈ Finset.range B, Module.finrank ℂ (cycDeg R w d)) ≤
      Module.finrank ℂ (UModG f spec) := by
  exact (Finset.sum_le_sum (fun d _ => finrank_cycDeg_le_univG h d)).trans
    (sum_finrank_univ_cycDeg_le f spec (Finset.range B))

theorem source_cycDeg_finite_of_univ [FiniteDimensional ℂ (UModG f spec)]
    (h : Sat f R w spec) (d : ℕ) : FiniteDimensional ℂ (cycDeg R w d) := by
  rw [← map_cycDegG h d]
  infer_instance

end
end VOA.DeligneAudit.D4FusionContact.Polynomial

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.univPieceSum_injective
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.sum_source_cycDeg_le_univ
