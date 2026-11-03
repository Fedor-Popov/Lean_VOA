import VOA.DeligneAudit.DeligneFusionCVUniv

/-!
# Degree projections and independent finite graded sums for auxiliary CV modules

All CV relations have been encoded as homogeneous single-word tails and
zero-degree eigenrelations. Thus degree filters descend to the actual
universal quotient. The resulting projections separate distinct graded
pieces without any finiteness premise. A finite family of pieces embeds
in the ambient universal module through its sum map.

Only the lightweight universal-module import is used; no character or
fusion-squeeze module is required for this bookkeeping.
-/

namespace VOA.DeligneAudit.A2.CVUniv

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.A2.CVFamily

noncomputable section

local notation "deg" => VOA.DeligneAudit.SectorGraded.wordDeg

private theorem cvDeg_nil : deg ([] : List (UnivG.Ltr 8)) = 0 := rfl

/-- Filter formal word combinations by their exact current degree. -/
def cvFreeDegreeProj (N : ℕ) : UnivG.FreeW 8 →ₗ[ℂ] UnivG.FreeW 8 :=
  Finsupp.linearCombination ℂ (fun l => if deg l = N then UnivG.sw l else 0)

theorem cvFreeDegreeProj_sw (N : ℕ) (l : List (UnivG.Ltr 8)) :
    cvFreeDegreeProj N (UnivG.sw l) = if deg l = N then UnivG.sw l else 0 := by
  simp [cvFreeDegreeProj, UnivG.sw]

/-- The actual universal CV relation space is preserved by every degree filter. -/
theorem cvFreeDegreeProj_J (ε ν ϱ : Weight) (j N : ℕ) :
    UnivG.Jrel bracketTable (cvSpec ε ν ϱ j) ≤
      (UnivG.Jrel bracketTable (cvSpec ε ν ϱ j)).comap (cvFreeDegreeProj N) := by
  rw [UnivG.Jrel, Submodule.span_le]
  intro g hg
  have hmem : g ∈ UnivG.Jrel bracketTable (cvSpec ε ν ϱ j) := Submodule.subset_span hg
  change cvFreeDegreeProj N g ∈ UnivG.Jrel bracketTable (cvSpec ε ν ϱ j)
  rcases hg with ⟨p, ⟨s, x, y, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨q, hq, rfl⟩⟩
  · by_cases hD : deg p + (x.2 + (y.2 + deg s)) = N
    · have h2 : deg p + (y.2 + (x.2 + deg s)) = N := by omega
      have h3 : deg p + (x.2 + y.2 + deg s) = N := by omega
      have : cvFreeDegreeProj N (UnivG.commInst bracketTable p s x y) =
          UnivG.commInst bracketTable p s x y := by
        simp only [UnivG.commInst, map_sub, map_sum, map_smul,
          cvFreeDegreeProj_sw, deg_append', deg_cons']
        simp [hD, h2, h3]
      rw [this]; exact hmem
    · have h2 : ¬ deg p + (y.2 + (x.2 + deg s)) = N := by omega
      have h3 : ¬ deg p + (x.2 + y.2 + deg s) = N := by omega
      have : cvFreeDegreeProj N (UnivG.commInst bracketTable p s x y) = 0 := by
        simp only [UnivG.commInst, map_sub, map_sum, map_smul,
          cvFreeDegreeProj_sw, deg_append', deg_cons']
        simp [hD, h2, h3]
      rw [this]; exact zero_mem _
  · rw [cvFreeDegreeProj_sw]; split_ifs
    · exact hmem
    · exact zero_mem _
  · by_cases hD : deg p = N
    · have : cvFreeDegreeProj N (UnivG.sw (p ++ [(q.1, 0)]) - q.2 • UnivG.sw p) =
          UnivG.sw (p ++ [(q.1, 0)]) - q.2 • UnivG.sw p := by
        simp only [map_sub, map_smul, cvFreeDegreeProj_sw,
          deg_append', deg_cons', cvDeg_nil, add_zero]
        simp [hD]
      rw [this]; exact hmem
    · have : cvFreeDegreeProj N (UnivG.sw (p ++ [(q.1, 0)]) - q.2 • UnivG.sw p) = 0 := by
        simp only [map_sub, map_smul, cvFreeDegreeProj_sw,
          deg_append', deg_cons', cvDeg_nil, add_zero]
        simp [hD]
      rw [this]; exact zero_mem _


/-- The exact degree projection on the actual universal CV module. -/
def cvDegreeProj (ε ν ϱ : Weight) (j N : ℕ) : CVMod ε ν ϱ j →ₗ[ℂ] CVMod ε ν ϱ j :=
  (UnivG.Jrel bracketTable (cvSpec ε ν ϱ j)).mapQ
    (UnivG.Jrel bracketTable (cvSpec ε ν ϱ j)) (cvFreeDegreeProj N)
    (cvFreeDegreeProj_J ε ν ϱ j N)

theorem cvDegreeProj_mk (ε ν ϱ : Weight) (j N : ℕ) (l : List (UnivG.Ltr 8)) :
    cvDegreeProj ε ν ϱ j N (Submodule.Quotient.mk (UnivG.sw l)) =
      if deg l = N then (Submodule.Quotient.mk (UnivG.sw l) : CVMod ε ν ϱ j) else 0 := by
  rw [cvDegreeProj, Submodule.mapQ_apply, cvFreeDegreeProj_sw]
  split_ifs <;> simp

/-- The projection acts on a word by the indicator of its current degree. -/
theorem cvDegreeProj_wordOp (ε ν ϱ : Weight) (j N : ℕ) (l : List (UnivG.Ltr 8)) :
    cvDegreeProj ε ν ϱ j N (wordOp (cvUnivRep ε ν ϱ j) l (cv_wU ε ν ϱ j)) =
      if deg l = N then wordOp (cvUnivRep ε ν ϱ j) l (cv_wU ε ν ϱ j) else 0 := by
  simp only [cvUnivRep, cv_wU, UnivG.wordOp_univG, cvDegreeProj_mk]

/-- Kronecker action of a degree projection on every homogeneous cyclic piece. -/
theorem cvDegreeProj_cycDeg (ε ν ϱ : Weight) (j N m : ℕ) {x : CVMod ε ν ϱ j}
    (hx : x ∈ cycDeg (cvUnivRep ε ν ϱ j) (cv_wU ε ν ϱ j) m) :
    cvDegreeProj ε ν ϱ j N x = if m = N then x else 0 := by
  induction hx using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨l, hl, rfl⟩ := hv
      rw [cvDegreeProj_wordOp, hl]
  | zero => simp
  | add x y _ _ hx hy =>
      rw [map_add, hx, hy]
      split_ifs <;> simp
  | smul c x _ hx =>
      rw [map_smul, hx]
      split_ifs <;> simp

/-- The sum map from a finite family of actual universal graded pieces. -/
def cvFiniteDegreeSum (ε ν ϱ : Weight) (j : ℕ) (s : Finset ℕ) :
    (∀ d : {k : ℕ // k ∈ s}, cycDeg (cvUnivRep ε ν ϱ j) (cv_wU ε ν ϱ j) d.1)
      →ₗ[ℂ] CVMod ε ν ϱ j where
  toFun x := ∑ d, (x d : CVMod ε ν ϱ j)
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum]

/-- Each coordinate is recovered by projecting the finite graded sum. -/
theorem cvDegreeProj_finiteDegreeSum (ε ν ϱ : Weight) (j : ℕ) (s : Finset ℕ)
    (x : ∀ d : {k : ℕ // k ∈ s}, cycDeg (cvUnivRep ε ν ϱ j) (cv_wU ε ν ϱ j) d.1)
    (i : {k : ℕ // k ∈ s}) :
    cvDegreeProj ε ν ϱ j i.1 (cvFiniteDegreeSum ε ν ϱ j s x) = x i := by
  change cvDegreeProj ε ν ϱ j i.1 (∑ d, (x d : CVMod ε ν ϱ j)) = x i
  rw [map_sum, Finset.sum_eq_single i]
  · simpa using cvDegreeProj_cycDeg ε ν ϱ j i.1 i.1 (x i).property
  · intro d _ hdi
    have hd : d.1 ≠ i.1 := fun h => hdi (Subtype.ext h)
    rw [cvDegreeProj_cycDeg ε ν ϱ j i.1 d.1 (x d).property, if_neg hd]
  · simp

/-- A finite family of graded pieces has no nontrivial additive relation. -/
theorem cvFiniteDegreeSum_injective (ε ν ϱ : Weight) (j : ℕ) (s : Finset ℕ) :
    Function.Injective (cvFiniteDegreeSum ε ν ϱ j s) := by
  intro x y hxy
  funext i
  apply Subtype.ext
  have hp := congrArg (cvDegreeProj ε ν ϱ j i.1) hxy
  simpa only [cvDegreeProj_finiteDegreeSum] using hp

/-- Finite sums of graded dimensions fit in any proved finite-dimensional universal module. -/
theorem sum_finrank_cycDeg_le (ε ν ϱ : Weight) (j : ℕ) (s : Finset ℕ)
    [FiniteDimensional ℂ (CVMod ε ν ϱ j)] :
    (∑ d ∈ s, Module.finrank ℂ (cycDeg (cvUnivRep ε ν ϱ j) (cv_wU ε ν ϱ j) d)) ≤
      Module.finrank ℂ (CVMod ε ν ϱ j) := by
  have hd := LinearMap.finrank_le_finrank_of_injective (cvFiniteDegreeSum_injective ε ν ϱ j s)
  rw [Module.finrank_pi_fintype] at hd
  calc
    (∑ d ∈ s, Module.finrank ℂ (cycDeg (cvUnivRep ε ν ϱ j) (cv_wU ε ν ϱ j) d)) =
        ∑ d : {k : ℕ // k ∈ s},
          Module.finrank ℂ (cycDeg (cvUnivRep ε ν ϱ j) (cv_wU ε ν ϱ j) d.1) :=
      (Finset.sum_coe_sort (s := s)
        (f := fun d : ℕ => Module.finrank ℂ
          (cycDeg (cvUnivRep ε ν ϱ j) (cv_wU ε ν ϱ j) d))).symm
    _ ≤ _ := hd

end

end VOA.DeligneAudit.A2.CVUniv

#print axioms VOA.DeligneAudit.A2.CVUniv.cvDegreeProj
#print axioms VOA.DeligneAudit.A2.CVUniv.cvDegreeProj_cycDeg
#print axioms VOA.DeligneAudit.A2.CVUniv.cvFiniteDegreeSum_injective
#print axioms VOA.DeligneAudit.A2.CVUniv.sum_finrank_cycDeg_le
