import VOA.DeligneAudit.D4FusionContactAllMModelReduction

/-! Per-current-degree PBW transfer. In the universal quotient the actual
current-degree projections split the PBW filtration of each degree piece, so
the universal degree-d piece is bounded by the degree-d word symbols of its
graded cyclic module. Source finiteness and ungraded independence are not
premises; the only independence used is that of the universal projections. -/
namespace VOA.DeligneAudit.D4FusionContact.Polynomial
open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.UnivG
noncomputable section

/-- The current degree of a radical-letter word. -/
def letterDeg (l : List CurrentLetter) : ℕ := (l.map Prod.snd).sum

theorem letterDeg_cons (x : CurrentLetter) (l : List CurrentLetter) :
    letterDeg (x :: l) = x.2 + letterDeg l := by
  simp [letterDeg]

section Graded
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule contactF V) (w : V)

/-- Negative words of PBW length below n and current degree d. -/
def PbelowDeg (d n : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ l : List CurrentLetter, l.length < n ∧ letterDeg l = d ∧
    v = nword R w l}

theorem PbelowDeg_mono (d : ℕ) {n n' : ℕ} (h : n ≤ n') :
    PbelowDeg R w d n ≤ PbelowDeg R w d n' :=
  Submodule.span_mono fun _ ⟨l, hl, hd, hv⟩ => ⟨l, by omega, hd, hv⟩

theorem PbelowDeg_zero (d : ℕ) : PbelowDeg R w d 0 = ⊥ := by
  rw [PbelowDeg, Submodule.span_eq_bot]
  rintro _ ⟨l, hl, _⟩
  omega

/-- PBW-length-n word symbols of current degree d. -/
def PieceDeg (d n : ℕ) : Submodule ℂ (Gr R w) :=
  Submodule.span ℂ {x | ∃ l : List CurrentLetter, l.length = n ∧ letterDeg l = d ∧
    x = grWord R w l}

/-- All word symbols of current degree d. -/
def GrDeg (d : ℕ) : Submodule ℂ (Gr R w) :=
  Submodule.span ℂ {x | ∃ l : List CurrentLetter, letterDeg l = d ∧ x = grWord R w l}

theorem PieceDeg_le_Piece (d n : ℕ) : PieceDeg R w d n ≤ Piece R w n :=
  Submodule.span_mono fun _ ⟨l, hl, _, hx⟩ => ⟨l, hl, hx⟩

theorem PieceDeg_le_GrDeg (d n : ℕ) : PieceDeg R w d n ≤ GrDeg R w d :=
  Submodule.span_mono fun _ ⟨l, _, hd, hx⟩ => ⟨l, hd, hx⟩

def pieceDegSum (d : ℕ) (s : Finset ℕ) :
    (∀ i : {n : ℕ // n ∈ s}, PieceDeg R w d i.1) →ₗ[ℂ] Gr R w where
  toFun x := ∑ i, (x i : Gr R w)
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum]

theorem grProj_pieceDegSum (d : ℕ) (s : Finset ℕ)
    (x : ∀ i : {n : ℕ // n ∈ s}, PieceDeg R w d i.1) (i : {n : ℕ // n ∈ s}) :
    grProj R w i.1 (pieceDegSum R w d s x) = x i := by
  change grProj R w i.1 (∑ j, (x j : Gr R w)) = x i
  rw [map_sum, Finset.sum_eq_single i]
  · simpa using grProj_piece R w i.1 i.1 (PieceDeg_le_Piece R w d i.1 (x i).property)
  · intro j _ hji
    rw [grProj_piece R w i.1 j.1 (PieceDeg_le_Piece R w d j.1 (x j).property),
      if_neg (fun h => hji (Subtype.ext h))]
  · simp

theorem pieceDegSum_injective (d : ℕ) (s : Finset ℕ) :
    Function.Injective (pieceDegSum R w d s) := by
  intro x y hxy
  funext i
  apply Subtype.ext
  have hh := congrArg (grProj R w i.1) hxy
  simpa only [grProj_pieceDegSum] using hh

/-- The PBW-length pieces of one current degree are independent inside it. -/
theorem sum_finrank_pieceDeg_le (d : ℕ) (s : Finset ℕ) [FiniteDimensional ℂ (Gr R w)] :
    (∑ n ∈ s, Module.finrank ℂ (PieceDeg R w d n)) ≤ Module.finrank ℂ (GrDeg R w d) := by
  have hrange : LinearMap.range (pieceDegSum R w d s) ≤ GrDeg R w d := by
    rintro _ ⟨x, rfl⟩
    exact Submodule.sum_mem _ (fun i _ => PieceDeg_le_GrDeg R w d i.1 (x i).property)
  have hinj := LinearMap.finrank_range_of_inj (pieceDegSum_injective R w d s)
  rw [Module.finrank_pi_fintype] at hinj
  calc
    (∑ n ∈ s, Module.finrank ℂ (PieceDeg R w d n)) =
        ∑ i : {n : ℕ // n ∈ s}, Module.finrank ℂ (PieceDeg R w d i.1) :=
      (Finset.sum_coe_sort (s := s) (f := fun n => Module.finrank ℂ (PieceDeg R w d n))).symm
    _ = Module.finrank ℂ (LinearMap.range (pieceDegSum R w d s)) := hinj.symm
    _ ≤ _ := Submodule.finrank_mono hrange

theorem PbelowDeg_map_le (d n : ℕ) :
    (PbelowDeg R w d (n + 1)).map (Pbelow R w n).mkQ ≤
      (PieceDeg R w d n).map (readD R w n) := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  rintro _ ⟨l, hl, hd, rfl⟩
  change (Pbelow R w n).mkQ (nword R w l) ∈ (PieceDeg R w d n).map (readD R w n)
  by_cases hn : l.length < n
  · have hv : nword R w l ∈ Pbelow R w n := Submodule.subset_span ⟨l, hn, rfl⟩
    have hz : (Pbelow R w n).mkQ (nword R w l) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hv
    rw [hz]
    exact Submodule.zero_mem _
  · have he : l.length = n := by omega
    exact ⟨grWord R w l, Submodule.subset_span ⟨l, he, hd, rfl⟩,
      by rw [readD_grWord, if_pos he]⟩

/-- A radical-only word is literally a word in the nine radical letters. -/
theorem exists_radical_word (l : List (Fin 28 × ℕ)) (hl : ∀ x ∈ l, active x.1) :
    ∃ a : List CurrentLetter, l = a.map (fun x => (radIndex x.1, x.2)) := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons x l ih =>
      obtain ⟨i, hi⟩ := (active_iff_index x.1).mp (hl x (by simp))
      obtain ⟨a, ha⟩ := ih (fun y hy => hl y (by simp [hy]))
      refine ⟨(i, x.2) :: a, ?_⟩
      rw [List.map_cons, hi, ← ha]

theorem wordDeg_radical (a : List CurrentLetter) :
    SectorGraded.wordDeg (a.map (fun x => (radIndex x.1, x.2))) = letterDeg a := by
  simp only [SectorGraded.wordDeg, letterDeg, List.map_map]
  rfl

/-- Highest relations place each current-degree piece in the union of its
degree-d negative PBW filtration (the established contact reduction). -/
theorem cycDeg_le_iSup_PbelowDeg {m : ℕ} (h : HighestRel R w m) (d : ℕ) :
    cycDeg R w d ≤ ⨆ n, PbelowDeg R w d n := by
  apply (cycDeg_le_contact h d).trans
  apply Submodule.span_le.mpr
  rintro _ ⟨l, -, ha, hd, rfl⟩
  obtain ⟨a, rfl⟩ := exists_radical_word l ha
  rw [wordDeg_radical] at hd
  exact (le_iSup (PbelowDeg R w d) (a.length + 1))
    (Submodule.subset_span ⟨a, by omega, hd, rfl⟩)

end Graded

section Universal
variable (spec : RelSpec 28)

theorem univProj_nword (d : ℕ) (l : List CurrentLetter) :
    univProj contactF spec d (nword (univRepG contactF spec) (wUG contactF spec) l) =
      if letterDeg l = d then nword (univRepG contactF spec) (wUG contactF spec) l
      else 0 := by
  change univProj contactF spec d (wordOp (univRepG contactF spec)
      (l.map fun x => (radIndex x.1, x.2)) (wUG contactF spec)) =
    if letterDeg l = d then wordOp (univRepG contactF spec)
      (l.map fun x => (radIndex x.1, x.2)) (wUG contactF spec) else 0
  rw [wordOp_univG, univProj_mk, wordDeg_radical]

theorem univProj_PbelowDeg (d n : ℕ) {x : UModG contactF spec}
    (hx : x ∈ PbelowDeg (univRepG contactF spec) (wUG contactF spec) d n) :
    univProj contactF spec d x = x := by
  induction hx using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨l, -, hd, rfl⟩ := hv
      rw [univProj_nword, if_pos hd]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

theorem univProj_Pbelow (d n : ℕ) {x : UModG contactF spec}
    (hx : x ∈ Pbelow (univRepG contactF spec) (wUG contactF spec) n) :
    univProj contactF spec d x ∈
      PbelowDeg (univRepG contactF spec) (wUG contactF spec) d n := by
  induction hx using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨l, hl, rfl⟩ := hv
      rw [univProj_nword]
      split_ifs with hd
      · exact Submodule.subset_span ⟨l, hl, hd, rfl⟩
      · exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/-- The universal projection removes every lower-length vector of other degrees. -/
theorem PbelowDeg_succ_inf (d n : ℕ) :
    PbelowDeg (univRepG contactF spec) (wUG contactF spec) d (n + 1) ⊓
        Pbelow (univRepG contactF spec) (wUG contactF spec) n ≤
      PbelowDeg (univRepG contactF spec) (wUG contactF spec) d n := by
  rintro x ⟨hx1, hx2⟩
  rw [← univProj_PbelowDeg spec d (n + 1) hx1]
  exact univProj_Pbelow spec d n hx2

variable [FiniteDimensional ℂ (UModG contactF spec)]
variable [FiniteDimensional ℂ (Gr (univRepG contactF spec) (wUG contactF spec))]

theorem finrank_PbelowDeg_step (d n : ℕ) :
    Module.finrank ℂ (PbelowDeg (univRepG contactF spec) (wUG contactF spec) d (n + 1)) ≤
      Module.finrank ℂ (PbelowDeg (univRepG contactF spec) (wUG contactF spec) d n) +
        Module.finrank ℂ (PieceDeg (univRepG contactF spec) (wUG contactF spec) d n) := by
  have hh := finrank_le_map_add_inf
    (Pbelow (univRepG contactF spec) (wUG contactF spec) n).mkQ
    (PbelowDeg (univRepG contactF spec) (wUG contactF spec) d (n + 1))
  rw [Submodule.ker_mkQ] at hh
  have hker := Submodule.finrank_mono (PbelowDeg_succ_inf spec d n)
  have hmap := Submodule.finrank_mono
    (PbelowDeg_map_le (univRepG contactF spec) (wUG contactF spec) d n)
  have hpiece := Submodule.finrank_map_le
    (readD (univRepG contactF spec) (wUG contactF spec) n)
    (PieceDeg (univRepG contactF spec) (wUG contactF spec) d n)
  omega

theorem finrank_PbelowDeg_le_sum (d : ℕ) : ∀ n : ℕ,
    Module.finrank ℂ (PbelowDeg (univRepG contactF spec) (wUG contactF spec) d n) ≤
      ∑ i ∈ Finset.range n,
        Module.finrank ℂ (PieceDeg (univRepG contactF spec) (wUG contactF spec) d i) := by
  intro n
  induction n with
  | zero => rw [PbelowDeg_zero]; simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      exact (finrank_PbelowDeg_step spec d n).trans (Nat.add_le_add_right ih _)

/-- PER-DEGREE universal bound: the universal degree-d piece is bounded by the
degree-d word symbols of its PBW graded module. -/
theorem finrank_univ_cycDeg_le_GrDeg {m : ℕ}
    (h : HighestRel (univRepG contactF spec) (wUG contactF spec) m) (d : ℕ) :
    Module.finrank ℂ (cycDeg (univRepG contactF spec) (wUG contactF spec) d) ≤
      Module.finrank ℂ (GrDeg (univRepG contactF spec) (wUG contactF spec) d) := by
  obtain ⟨-, hdim⟩ := finite_of_bounded_filtration
    (PbelowDeg (univRepG contactF spec) (wUG contactF spec) d)
    (fun _ _ h => PbelowDeg_mono _ _ d h) (fun _ => inferInstance)
    (Module.finrank ℂ (GrDeg (univRepG contactF spec) (wUG contactF spec) d))
    (fun n => (finrank_PbelowDeg_le_sum spec d n).trans
      (sum_finrank_pieceDeg_le _ _ d (Finset.range n)))
  exact (Submodule.finrank_mono (cycDeg_le_iSup_PbelowDeg _ _ h d)).trans hdim

end Universal

end
end VOA.DeligneAudit.D4FusionContact.Polynomial

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.sum_finrank_pieceDeg_le
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.cycDeg_le_iSup_PbelowDeg
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.finrank_univ_cycDeg_le_GrDeg
