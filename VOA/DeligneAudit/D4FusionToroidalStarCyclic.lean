import VOA.DeligneAudit.D4FusionToroidalStarRank

/-! Cyclicity of the high-mode associated graded. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {n : ℕ} (f : Fin n → Fin n → Fin n → ℂ) (R : RelSpec n)
    (m : ℕ) (hm : 1 ≤ m) (h : HighModeShift f R m)

private theorem weight_le_symbolDegree (hm : 1 ≤ m) : ∀ l : List (Ltr n),
    tmWeight m l ≤ symbolDegree m l
  | [] => by simp [tmWeight, symbolDegree]
  | a :: l => by
      have ih := weight_le_symbolDegree hm l
      by_cases ha : m ≤ a.2
      · have hd : 1 ≤ a.2 / m :=
          (Nat.le_div_iff_mul_le hm).mpr (by simpa using ha)
        simp only [tmWeight, symbolDegree, if_pos ha]
        omega
      · simp only [tmWeight, symbolDegree, if_neg ha]
        rw [Nat.div_eq_of_lt (Nat.lt_of_not_ge ha)]
        omega

private def symbolMap (j : ℕ) : TU f R m j →ₗ[ℂ] Gr f R m where
  toFun x := (grKernel f R m).mkQ (gradedSingle f R m j x.1 x.2)
  map_add' x y := by
    rw [← map_add]
    congr 1
    apply Subtype.ext
    simp [gradedSingle]
  map_smul' a x := by
    rw [← map_smul]
    congr 1
    apply Subtype.ext
    simp [gradedSingle]

private theorem symbolMap_word (hm : 1 ≤ m) (j : ℕ) (l : List (Ltr n))
    (hj : j ≤ tmWeight m l) :
    symbolMap f R m j ⟨wordOp (univRepG f R) l (wUG f R), by
      rw [wordOp_univG]
      exact Submodule.mem_map_of_mem (sw_mem_T m j l hj)⟩ ∈
      Submodule.span ℂ (Set.range fun t : List (TLtr n) =>
        wordOpT (grToroidal f R m h) t (grGenerator f R m)) := by
  let P := Submodule.span ℂ (Set.range fun t : List (TLtr n) =>
    wordOpT (grToroidal f R m h) t (grGenerator f R m))
  let x := wordOp (univRepG f R) l (wUG f R)
  have hxj : x ∈ TU f R m j := by
    dsimp [x]
    rw [wordOp_univG]
    exact Submodule.mem_map_of_mem (sw_mem_T m j l hj)
  have hw : wUG f R ∈ TU f R m 0 := by rw [TU_zero]; trivial
  have hd : x ∈ TU f R m (symbolDegree m l) := by
    simpa only [Nat.zero_add] using
      word_mem_shift f R m h hm l 0 (wUG f R) hw
  have hle : j ≤ symbolDegree m l :=
    hj.trans (weight_le_symbolDegree m hm l)
  rcases eq_or_lt_of_le hle with he | he
  · have hh := wordOpT_gr f R m h hm l 0 (wUG f R) hw
    have hh' : wordOpT (grToroidal f R m h) (symbolLetters m l)
        (grGenerator f R m) =
        (grKernel f R m).mkQ
          (gradedSingle f R m (symbolDegree m l) x hd) := by
      simpa only [grGenerator, Nat.zero_add] using hh
    change (grKernel f R m).mkQ (gradedSingle f R m j x hxj) ∈ P
    subst j
    rw [← hh']
    exact Submodule.subset_span ⟨symbolLetters m l, rfl⟩
  · have hx : x ∈ TU f R m (j + 1) :=
      TU_mono f R m (by omega) hd
    have hz : (grKernel f R m).mkQ
        (gradedSingle f R m j x (TU_mono f R m (by omega) hx)) = 0 := by
      apply (Submodule.Quotient.mk_eq_zero (grKernel f R m)).mpr
      exact gradedSingle_mem_kernel f R m j x hx
    change (grKernel f R m).mkQ (gradedSingle f R m j x hxj) ∈ P
    have hz' : (grKernel f R m).mkQ (gradedSingle f R m j x hxj) = 0 := by
      convert hz using 1
    rw [hz']
    exact Submodule.zero_mem P

theorem gr_cyclic (hm : 1 ≤ m) (h : HighModeShift f R m) :
    Submodule.span ℂ (Set.range fun l : List (TLtr n) =>
      wordOpT (grToroidal f R m h) l (grGenerator f R m)) = ⊤ := by
  let P := Submodule.span ℂ (Set.range fun l : List (TLtr n) =>
    wordOpT (grToroidal f R m h) l (grGenerator f R m))
  have hs : ∀ j x (hx : x ∈ TU f R m j),
      symbolMap f R m j ⟨x, hx⟩ ∈ P := by
    intro j x hx0
    have hspan_le : Submodule.span ℂ
        {v | ∃ l, j ≤ tmWeight m l ∧ v =
          wordOp (univRepG f R) l (wUG f R)} ≤ TU f R m j := by
      rw [Submodule.span_le]
      rintro _ ⟨l, hl, rfl⟩
      rw [wordOp_univG]
      exact Submodule.mem_map_of_mem (sw_mem_T m j l hl)
    have hx : x ∈ Submodule.span ℂ
        {v | ∃ l, j ≤ tmWeight m l ∧ v =
          wordOp (univRepG f R) l (wUG f R)} := by
      change x ∈ (T m j).map (Jrel f R).mkQ at hx0
      rw [T, Submodule.map_span] at hx0
      apply (Submodule.span_mono ?_) hx0
      rintro v ⟨u, ⟨l, hl, rfl⟩, rfl⟩
      exact ⟨l, hl, (wordOp_univG f R l).symm⟩
    induction hx using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨l, hl, rfl⟩ := hv
        exact symbolMap_word f R m h hm j l hl
    | zero =>
        change symbolMap f R m j (0 : TU f R m j) ∈ P
        rw [map_zero]
        exact Submodule.zero_mem P
    | add a b ha hb iha ihb =>
        change symbolMap f R m j (⟨a, hspan_le ha⟩ + ⟨b, hspan_le hb⟩) ∈ P
        rw [map_add]
        exact Submodule.add_mem P (iha (hspan_le ha)) (ihb (hspan_le hb))
    | smul a b hb ih =>
        change symbolMap f R m j (a • ⟨b, hspan_le hb⟩) ∈ P
        rw [map_smul]
        exact Submodule.smul_mem P a (ih (hspan_le hb))
  have hnum : grNumerator f R m ≤
      (P.comap (grKernel f R m).mkQ).map (grNumerator f R m).subtype := by
    change Submodule.span ℂ
      {v | ∃ j x, x ∈ TU f R m j ∧ v = Finsupp.single j x} ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨j, x, hx, rfl⟩
    refine ⟨gradedSingle f R m j x hx, ?_, rfl⟩
    exact hs j x hx
  apply top_unique
  intro y _
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (grKernel f R m) y
  obtain ⟨u, hu, hval⟩ := hnum v.2
  have he : u = v := Subtype.ext hval
  rw [← he]
  exact hu

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.gr_cyclic
