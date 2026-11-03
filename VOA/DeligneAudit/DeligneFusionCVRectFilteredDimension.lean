import VOA.DeligneAudit.DeligneFusionCVRectFiltered
import Mathlib.Data.Nat.Lattice

/-!
# Dimension transfer for the actual PBW filtration

Length projections separate graded pieces without assuming the original
module is finite-dimensional. A bounded increasing filtration by genuinely
finite-dimensional pieces stabilizes; its exhaustive union is therefore
finite-dimensional. No ungraded degree independence is assumed.
-/

namespace VOA.DeligneAudit.A2.CVRectFiltered

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Bounded ranks of actual finite pieces force an increasing filtration to
stabilize, with no finite-dimensionality premise on the ambient space. -/
theorem finite_of_bounded_filtration (F : ℕ → Submodule ℂ V) (hF : Monotone F)
    (hFD : ∀ n, FiniteDimensional ℂ (F n)) (C : ℕ)
    (hB : ∀ n, Module.finrank ℂ (F n) ≤ C) :
    FiniteDimensional ℂ (⨆ n, F n : Submodule ℂ V) ∧
      Module.finrank ℂ (⨆ n, F n : Submodule ℂ V) ≤ C := by
  let dims : ℕ → ℕ := fun n => Module.finrank ℂ (F n)
  have hbdd : BddAbove (Set.range dims) := ⟨C, by rintro _ ⟨n, rfl⟩; exact hB n⟩
  obtain ⟨N, hN⟩ := Nat.sSup_mem (Set.range_nonempty dims) hbdd
  have hmax : ∀ n, Module.finrank ℂ (F n) ≤ Module.finrank ℂ (F N) := by
    intro n
    change dims n ≤ dims N
    rw [hN]
    exact le_csSup hbdd ⟨n, rfl⟩
  have hle : ∀ n, F n ≤ F N := by
    intro n
    haveI := hFD (max n N)
    have he : F N = F (max n N) :=
      Submodule.eq_of_le_of_finrank_le (hF (le_max_right n N)) (hmax (max n N))
    exact (hF (le_max_left n N)).trans he.ge
  have he : (⨆ n, F n : Submodule ℂ V) = F N := le_antisymm (iSup_le hle) (le_iSup F N)
  rw [he]
  exact ⟨hFD N, hB N⟩

variable (R : CurrentModule bracketTable V) (w : V)

def projLift (n : ℕ) : (ℕ →₀ V) →ₗ[ℂ] (ℕ →₀ V) :=
  Finsupp.lsingle n ∘ₗ Finsupp.lapply n

theorem projLift_single (n m : ℕ) (v : V) :
    projLift n (Finsupp.single m v) = if m = n then Finsupp.single m v else 0 := by
  by_cases h : m = n
  · subst m
    simp [projLift]
  · simp [projLift, Finsupp.single_apply, h]

theorem projLift_Lsub (n : ℕ) : Lsub R w ≤ (Lsub R w).comap (projLift n) := by
  rw [Lsub, Submodule.span_le]
  rintro _ ⟨m, v, hv, rfl⟩
  change projLift n (Finsupp.single m v) ∈ Lsub R w
  rw [projLift_single]
  split_ifs
  · exact Submodule.subset_span ⟨m, v, hv, rfl⟩
  · exact Submodule.zero_mem _

def ambientProj (n : ℕ) : Module.End ℂ (AmbientGr R w) :=
  (Lsub R w).mapQ (Lsub R w) (projLift n) (projLift_Lsub R w n)

theorem ambientProj_symbol (n m : ℕ) (v : V) :
    ambientProj R w n (symbol R w m v) = if m = n then symbol R w m v else 0 := by
  change (Lsub R w).mkQ (projLift n (Finsupp.single m v)) = _
  rw [projLift_single]
  split_ifs
  · rfl
  · exact map_zero _

theorem ambientProj_wordSymbol (n : ℕ) (l : List NegLtr) :
    ambientProj R w n (wordSymbol R w l) = if l.length = n then wordSymbol R w l else 0 :=
  ambientProj_symbol R w n l.length (nword R w l)

theorem gradedCyclic_proj (n : ℕ) : gradedCyclic R w ≤
    (gradedCyclic R w).comap (ambientProj R w n) := by
  rw [gradedCyclic, Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  change ambientProj R w n (wordSymbol R w l) ∈ gradedCyclic R w
  rw [ambientProj_wordSymbol]
  split_ifs
  · exact Submodule.subset_span ⟨l, rfl⟩
  · exact Submodule.zero_mem _

def grProj (n : ℕ) : Module.End ℂ (Gr R w) :=
  (ambientProj R w n).restrict (fun _ hv => gradedCyclic_proj R w n hv)

theorem grProj_grWord (n : ℕ) (l : List NegLtr) :
    grProj R w n (grWord R w l) = if l.length = n then grWord R w l else 0 := by
  apply Subtype.ext
  change ambientProj R w n (wordSymbol R w l) = _
  rw [ambientProj_wordSymbol]
  split_ifs <;> rfl

/-- The actual homogeneous PBW-length piece in the graded cyclic module. -/
def Piece (n : ℕ) : Submodule ℂ (Gr R w) :=
  Submodule.span ℂ {x | ∃ l : List NegLtr, l.length = n ∧ x = grWord R w l}

theorem grProj_piece (n m : ℕ) {x : Gr R w} (hx : x ∈ Piece R w m) :
    grProj R w n x = if m = n then x else 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      rw [grProj_grWord, hl]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy]; split_ifs <;> simp
  | smul c x _ hx => rw [map_smul, hx]; split_ifs <;> simp

def pieceSum (s : Finset ℕ) :
    (∀ d : {n : ℕ // n ∈ s}, Piece R w d.1) →ₗ[ℂ] Gr R w where
  toFun x := ∑ d, (x d : Gr R w)
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum]

theorem grProj_pieceSum (s : Finset ℕ)
    (x : ∀ d : {n : ℕ // n ∈ s}, Piece R w d.1) (i : {n : ℕ // n ∈ s}) :
    grProj R w i.1 (pieceSum R w s x) = x i := by
  change grProj R w i.1 (∑ d, (x d : Gr R w)) = x i
  rw [map_sum, Finset.sum_eq_single i]
  · simpa using grProj_piece R w i.1 i.1 (x i).property
  · intro d _ hdi
    rw [grProj_piece R w i.1 d.1 (x d).property,
      if_neg (fun h => hdi (Subtype.ext h))]
  · simp

theorem pieceSum_injective (s : Finset ℕ) : Function.Injective (pieceSum R w s) := by
  intro x y hxy
  funext i
  apply Subtype.ext
  have hh := congrArg (grProj R w i.1) hxy
  simpa only [grProj_pieceSum] using hh

theorem sum_finrank_piece_le (s : Finset ℕ) [FiniteDimensional ℂ (Gr R w)] :
    (∑ n ∈ s, Module.finrank ℂ (Piece R w n)) ≤ Module.finrank ℂ (Gr R w) := by
  have hh := LinearMap.finrank_le_finrank_of_injective (pieceSum_injective R w s)
  rw [Module.finrank_pi_fintype] at hh
  calc
    (∑ n ∈ s, Module.finrank ℂ (Piece R w n)) =
        ∑ n : {n : ℕ // n ∈ s}, Module.finrank ℂ (Piece R w n.1) :=
      (Finset.sum_coe_sort (s := s) (f := fun n : ℕ => Module.finrank ℂ (Piece R w n))).symm
    _ ≤ _ := hh

/-- Read one actual length symbol modulo its lower filtration. -/
def readAmbient (n : ℕ) : AmbientGr R w →ₗ[ℂ] (V ⧸ Pbelow R w n) :=
  (Lsub R w).liftQ ((Pbelow R w n).mkQ ∘ₗ Finsupp.lapply n) (by
    rw [Lsub, Submodule.span_le]
    rintro _ ⟨m, v, hv, rfl⟩
    change (Pbelow R w n).mkQ ((Finsupp.single m v) n) = 0
    by_cases hm : m = n
    · subst m
      simpa using (Submodule.Quotient.mk_eq_zero (Pbelow R w n)).mpr hv
    · simp [Finsupp.single_apply, hm])

def readD (n : ℕ) : Gr R w →ₗ[ℂ] (V ⧸ Pbelow R w n) :=
  (readAmbient R w n).domRestrict (gradedCyclic R w)

theorem readD_grWord (n : ℕ) (l : List NegLtr) :
    readD R w n (grWord R w l) =
      if l.length = n then (Pbelow R w n).mkQ (nword R w l) else 0 := by
  change readAmbient R w n ((Lsub R w).mkQ
    (Finsupp.single l.length (nword R w l))) = _
  change (Pbelow R w n).mkQ ((Finsupp.single l.length (nword R w l)) n) = _
  simp only [Finsupp.single_apply]
  split_ifs <;> simp

theorem Ple_map_le_piece (n : ℕ) :
    (Ple R w n).map (Pbelow R w n).mkQ ≤ (Piece R w n).map (readD R w n) := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  rintro _ ⟨l, hl, rfl⟩
  change (Pbelow R w n).mkQ (nword R w l) ∈ (Piece R w n).map (readD R w n)
  by_cases hn : l.length < n
  · have hv : nword R w l ∈ Pbelow R w n := Submodule.subset_span ⟨l, hn, rfl⟩
    have hz : (Pbelow R w n).mkQ (nword R w l) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hv
    rw [hz]
    exact Submodule.zero_mem _
  · have he : l.length = n := by omega
    exact ⟨grWord R w l, Submodule.subset_span ⟨l, he, rfl⟩,
      by rw [readD_grWord, if_pos he]⟩

theorem Ple_inf_ker (n : ℕ) :
    Ple R w n ⊓ LinearMap.ker (Pbelow R w n).mkQ = Pbelow R w n := by
  rw [Submodule.ker_mkQ]
  exact inf_eq_right.mpr (Pbelow_mono R w (by omega))

variable [FiniteDimensional ℂ (Gr R w)]

/-- Finiteness of each actual filtered piece follows from the genuinely finite
graded module and the already established lower piece. Ambient finiteness is
not a premise. -/
theorem Pbelow_finite : ∀ n : ℕ, FiniteDimensional ℂ (Pbelow R w n) := by
  intro n
  induction n with
  | zero => rw [Pbelow_zero]; infer_instance
  | succ n ih =>
      apply Module.Finite.iff_fg.mpr
      change (Ple R w n).FG
      refine Submodule.fg_of_fg_map_of_fg_inf_ker (Pbelow R w n).mkQ ?_ ?_
      · exact Module.Finite.iff_fg.mp
          (Submodule.finiteDimensional_of_le (Ple_map_le_piece R w n))
      · rw [Ple_inf_ker]
        exact Module.Finite.iff_fg.mp ih

theorem finrank_Ple_step (n : ℕ) :
    Module.finrank ℂ (Ple R w n) ≤ Module.finrank ℂ (Pbelow R w n) +
      Module.finrank ℂ (Piece R w n) := by
  haveI := Pbelow_finite R w (n + 1)
  have hh := CVsl2.finrank_le_map_add_inf' (Pbelow R w n).mkQ (Ple R w n)
  rw [Ple_inf_ker] at hh
  have hmap := Submodule.finrank_mono (Ple_map_le_piece R w n)
  have hpiece := Submodule.finrank_map_le (readD R w n) (Piece R w n)
  omega

theorem finrank_Pbelow_le_sum : ∀ n : ℕ,
    Module.finrank ℂ (Pbelow R w n) ≤
      ∑ i ∈ Finset.range n, Module.finrank ℂ (Piece R w i) := by
  intro n
  induction n with
  | zero => rw [Pbelow_zero]; simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      exact (finrank_Ple_step R w n).trans (Nat.add_le_add_right ih _)

/-- The actual ungraded cyclic span of negative-current words. -/
def negativeCyclic : Submodule ℂ V := Submodule.span ℂ (Set.range (nword R w))

theorem iSup_Pbelow : (⨆ n : ℕ, Pbelow R w n) = negativeCyclic R w := by
  apply le_antisymm
  · apply iSup_le
    intro n
    rw [Pbelow, Submodule.span_le]
    rintro _ ⟨l, _, rfl⟩
    exact Submodule.subset_span ⟨l, rfl⟩
  · rw [negativeCyclic, Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    exact (le_iSup (Pbelow R w) (l.length + 1))
      (Submodule.subset_span ⟨l, by omega, rfl⟩)

/-- A finite actual graded cyclic module bounds the actual ungraded cyclic
module through the exhaustive nonnegative PBW filtration. No source finiteness
or independence of ungraded pieces is assumed. -/
theorem negativeCyclic_bound : FiniteDimensional ℂ (negativeCyclic R w) ∧
    Module.finrank ℂ (negativeCyclic R w) ≤ Module.finrank ℂ (Gr R w) := by
  obtain ⟨hFD, hdim⟩ := finite_of_bounded_filtration (Pbelow R w)
    (fun _ _ h => Pbelow_mono R w h) (Pbelow_finite R w) (Module.finrank ℂ (Gr R w))
    (fun n => (finrank_Pbelow_le_sum R w n).trans (sum_finrank_piece_le R w (Finset.range n)))
  rw [iSup_Pbelow] at hFD hdim
  exact ⟨hFD, hdim⟩

end

end VOA.DeligneAudit.A2.CVRectFiltered

#print axioms VOA.DeligneAudit.A2.CVRectFiltered.finite_of_bounded_filtration
#print axioms VOA.DeligneAudit.A2.CVRectFiltered.pieceSum_injective
#print axioms VOA.DeligneAudit.A2.CVRectFiltered.sum_finrank_piece_le
#print axioms VOA.DeligneAudit.A2.CVRectFiltered.negativeCyclic_bound
