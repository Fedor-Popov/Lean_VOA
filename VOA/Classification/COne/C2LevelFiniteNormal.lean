import VOA.Huang.BuhlSpanningMain

/-!
# Normal words on an arbitrary seed subspace

This extends the bottom-level normal-form argument in `BuhlSpanningNormal`
to any subspace with a uniform upper mode cutoff on sorted words. In particular,
a homogeneous seed at level `k` has cutoff `k + max wt`, not merely `max wt`.
The repeated-block and potential-induction proofs follow the existing library
proofs, with the bottom-level assumption replaced by this explicit cutoff.
-/

namespace VOA.Classification.COne.C2LevelFinite

open VOA.Huang.BuhlSpanning VOA.Huang.ModuleC2 VOA.Huang.FusionC2

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
  {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

variable (D : GenData W) (A : WeakModule W M) (B : Submodule ℂ M)

/-- Products of modes of one generator, read as a generator word. -/
theorem wordX_eq_wordL (i₀ : Fin D.g) (l' : List (Ltr D)) (b : M) :
    ∀ c : List ℤ, wordX A (D.gen i₀) c (wordL D A l' b)
      = wordL D A (c.map (fun k => (i₀, k)) ++ l') b
  | [] => rfl
  | a :: c => by
      rw [wordX_cons, wordX_eq_wordL i₀ l' b c]
      rfl

variable {D A B}

/-- **The `C₂` relation on a repeated block**: `gen_{i₀,(n)}^{N₀+1} z` lies in the previous
grade plus the span of unbalanced products. -/
theorem block_mem {N₀ : ℕ} (hN₀ : ∀ n : ℤ, (N₀ : ℤ) ≤ n → W.grading n ≤ O₂ W) (i₀ : Fin D.g)
    (n : ℤ) (l' : List (Ltr D)) {b : M} (hb : b ∈ B) :
    wordL D A (List.replicate (N₀ + 1) (i₀, n) ++ l') b ∈
      E D A (B) (grade D (List.replicate (N₀ + 1) (i₀, n) ++ l') - 1) ⊔
        Submodule.span ℂ {y | ∃ c : List ℤ, c.length = N₀ + 1 ∧ c.sum = ((N₀ : ℤ) + 1) * n ∧
          c ≠ List.replicate (N₀ + 1) n ∧
          y = wordL D A (c.map (fun k => (i₀, k)) ++ l') b} := by
  set x := D.gen i₀
  set z := wordL D A l' b with hzdef
  set t : ℤ := ((N₀ : ℤ) + 1) * n + N₀ with ht
  have hz : z ∈ E D A (B) (grade D l') := wordL_mem_E hb le_rfl
  set p : ℕ := (N₀ + 1) * D.wt i₀ with hp
  have hwt := D.wt_pos i₀
  have hp1 : N₀ + 1 ≤ p := by rw [hp]; nlinarith
  have hvg : vPow W x N₀ ∈ W.grading (p : ℤ) := by
    have := vPow_mem_grading (D.gen_mem i₀) N₀
    rw [hp]; push_cast; exact this
  have hO : vPow W x N₀ ∈ O₂ W ⊓ W.grading (p : ℤ) :=
    ⟨hN₀ (p : ℤ) (by exact_mod_cast (show N₀ ≤ p by omega)) hvg, hvg⟩
  have h1 := O₂_act_mem_E (A := A) (D := D) (B₀ := B) p hO t hz
  have h2 := vPow_mode_sub_mem_Sp (A := A) (x := x) n N₀ t z
  rw [if_pos (by rw [ht])] at h2
  have hgr : grade D (List.replicate (N₀ + 1) (i₀, n) ++ l') - 1 = grade D l' + (p - 1) := by
    rw [grade_append, grade_replicate]; dsimp only; rw [← hp]; omega
  have hrep : wordL D A (List.replicate (N₀ + 1) (i₀, n) ++ l') b
      = wordX A x (List.replicate (N₀ + 1) n) z := by
    rw [hzdef, wordX_eq_wordL D A i₀ l' b, List.map_replicate]
  rw [hrep, hgr]
  have heq : wordX A x (List.replicate (N₀ + 1) n) z
      = mode (A.YM (vPow W x N₀)) t z
        - (mode (A.YM (vPow W x N₀)) t z - wordX A x (List.replicate (N₀ + 1) n) z) := by abel
  rw [heq]
  refine Submodule.sub_mem _ (Submodule.mem_sup_left h1) (Submodule.mem_sup_right ?_)
  refine (Submodule.span_le.mpr ?_) h2
  rintro _ ⟨c, hlen, hsum, hne, rfl⟩
  refine Submodule.subset_span ⟨c, hlen, ?_, hne, ?_⟩
  · rw [hsum, ht]; ring
  · exact wordX_eq_wordL D A i₀ l' b c

/-- Normal words on an arbitrary seed subspace. -/
noncomputable def normalSpan (D : GenData W) (A : WeakModule W M)
    (B : Submodule ℂ M) (Q : ℕ) : Submodule ℂ M :=
  Submodule.span ℂ {y | ∃ (l : List (Ltr D)) (b : M), Normal D Q l ∧ b ∈ B ∧
    y = wordL D A l b}

/-- Normal-form spanning using only a cutoff for sorted words on the seed. -/
theorem E_le_normalSpan {N₀ : ℕ} (hN₀ : ∀ n : ℤ, (N₀ : ℤ) ≤ n → W.grading n ≤ O₂ W) {Bm : ℕ}
    (hcut : ∀ (l : List (Ltr D)), l.Pairwise (modeLE D) →
      (∃ e ∈ l, (Bm : ℤ) ≤ e.2) → ∀ b ∈ B, wordL D A l b = 0) :
    ∀ G : ℕ, E D A (B) G ≤ normalSpan D A B (N₀ + 1) := by
  set Q := N₀ + 1 with hQ
  intro G
  induction G using Nat.strong_induction_on with
  | _ G IH =>
  have hlow : 1 ≤ G → E D A (B) (G - 1) ≤ normalSpan D A B Q := fun h => IH (G - 1) (by omega)
  -- the sorted words of grade `G`
  have hsorted : ∀ (d : ℕ) (l : List (Ltr D)), l.Pairwise (modeLE D) → grade D l = G →
      ∀ b ∈ B,
        (Kbd (Bm : ℤ) l.length (modeSum D l) - phi D l).toNat ≤ d → wordL D A l b ∈ normalSpan D A B Q := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d IHd =>
    intro l hp hg b hb hd
    by_cases hbig : ∃ e ∈ l, (Bm : ℤ) ≤ e.2
    · rw [hcut l hp hbig b hb]; exact Submodule.zero_mem _
    push Not at hbig
    by_cases hnorm : ∀ a, l.count a < Q
    · exact Submodule.subset_span ⟨l, b, ⟨hp, hnorm⟩, hb, rfl⟩
    push Not at hnorm
    obtain ⟨a, ha⟩ := hnorm
    have hsub : List.Sublist (List.replicate Q a) l := List.replicate_sublist_iff.mpr ha
    obtain ⟨l', hperm⟩ := hsub.exists_perm_append
    have hgG : grade D (List.replicate Q a ++ l') = G := by rw [← grade_perm D hperm, hg]
    have hG1 : 1 ≤ G := by
      rw [← hgG, grade_append, grade_replicate]
      have := D.wt_pos a.1
      nlinarith
    have hdiff := perm_sub_mem_E (A := A) (B₀ := B) hperm hb
    rw [hg] at hdiff
    have hblock := block_mem (A := A) (B := B) hN₀ a.1 a.2 l' hb
    rw [Prod.mk.eta, hgG] at hblock
    have hspan : Submodule.span ℂ {y | ∃ c : List ℤ, c.length = N₀ + 1 ∧
        c.sum = ((N₀ : ℤ) + 1) * a.2 ∧ c ≠ List.replicate (N₀ + 1) a.2 ∧
        y = wordL D A (c.map (fun k => (a.1, k)) ++ l') b} ≤ normalSpan D A B Q := by
      rw [Submodule.span_le]
      rintro _ ⟨c, hlen, hsum, hne, rfl⟩
      set l'' := c.map (fun k => (a.1, k)) ++ l' with hl''
      set s'' := List.insertionSort (modeLE D) l'' with hs''
      have hps : s''.Perm l'' := List.perm_insertionSort (modeLE D) l''
      have hgl'' : grade D l'' = G := by
        rw [← hgG, hl'', grade_append, grade_append, grade_map, grade_replicate, hlen]
      have hd2 := perm_sub_mem_E (A := A) (B₀ := B) hps.symm hb
      rw [hgl''] at hd2
      have hs_mem : wordL D A s'' b ∈ normalSpan D A B Q := by
        have hsp : s''.Pairwise (modeLE D) := List.pairwise_insertionSort (modeLE D) l''
        by_cases hbig' : ∃ e ∈ s'', (Bm : ℤ) ≤ e.2
        · rw [hcut s'' hsp hbig' b hb]; exact Submodule.zero_mem _
        push Not at hbig'
        -- invariants
        have hlen_eq : s''.length = l.length := by
          rw [hps.length_eq, hperm.length_eq, hl'']; simp [hlen, hQ]
        have hsum_eq : modeSum D s'' = modeSum D l := by
          rw [modeSum_perm hps, modeSum_perm hperm, hl'', modeSum_append, modeSum_append,
            modeSum_map, hsum]
          simp [modeSum, List.map_replicate, List.sum_replicate, hQ]
        have hphi_gt : phi D l < phi D s'' := by
          rw [phi_perm hps, phi_perm hperm, hl'', phi_append, phi_append, phi_map]
          have hrep : phi D (List.replicate Q a) = (Q : ℤ) * a.2 ^ 2 := by
            simp [phi, List.map_replicate, List.sum_replicate]
          rw [hrep]
          have := sum_sq_gt (Q := Q) (n := a.2) hlen (by rw [hsum]; push_cast [hQ]; ring) hne
          linarith
        have hbd := phi_le_Kbd (D := D) (by positivity) s'' hbig'
        rw [hlen_eq, hsum_eq] at hbd
        refine IHd _ ?_ s'' hsp (by rw [grade_perm D hps, hgl'']) b hb le_rfl
        rw [hlen_eq, hsum_eq]
        omega
      have := Submodule.add_mem _ hs_mem (hlow hG1 (by simpa using hd2))
      rwa [add_sub_cancel] at this
    have hrest : wordL D A (List.replicate Q a ++ l') b ∈ normalSpan D A B Q := by
      have := (sup_le (hlow hG1) hspan) hblock
      exact this
    have := Submodule.add_mem _ (hlow hG1 hdiff) hrest
    rwa [sub_add_cancel] at this
  -- all words of grade `≤ G`
  rw [E, Submodule.span_le]
  rintro _ ⟨l, b, hl, hb, rfl⟩
  rcases lt_or_eq_of_le hl with hlt | heq
  · exact (IH (grade D l) hlt) (wordL_mem_E hb le_rfl)
  · by_cases hl0 : l = []
    · subst hl0
      exact Submodule.subset_span ⟨[], b, ⟨List.Pairwise.nil, fun a => by simp [hQ]⟩, hb, rfl⟩
    have hG1 : 1 ≤ G := by
      rw [← heq]
      rcases l with _ | ⟨e, l⟩
      · exact absurd rfl hl0
      · rw [grade_cons]; have := D.wt_pos e.1; omega
    set s := List.insertionSort (modeLE D) l
    have hps : s.Perm l := List.perm_insertionSort (modeLE D) l
    have hd := perm_sub_mem_E (A := A) (B₀ := B) hps.symm hb
    rw [heq] at hd
    have hs := hsorted _ s (List.pairwise_insertionSort (modeLE D) l)
      (by rw [grade_perm D hps, heq]) b hb le_rfl
    have := Submodule.add_mem _ hs (hlow hG1 hd)
    rwa [add_sub_cancel] at this

/-- The upper mode cutoff for a seed at any admissible level. -/
theorem wordL_eq_zero_of_big_level (N : AdmissibleModule W M) {k : ℤ} {Bm : ℕ}
    (hBm : ∀ i, k + (D.wt i : ℤ) ≤ Bm) :
    ∀ (l : List (Ltr D)), l.Pairwise (modeLE D) → (∃ e ∈ l, (Bm : ℤ) ≤ e.2) →
      ∀ b ∈ N.lev k, wordL D N.toWeakModule l b = 0 := by
  intro l
  induction l with
  | nil => rintro _ ⟨e, he, _⟩; simp at he
  | cons a l ih =>
      intro hp ⟨e, he, hbig⟩ b hb
      rw [wordL_cons]
      by_cases h' : ∃ e ∈ l, (Bm : ℤ) ≤ e.2
      · rw [ih hp.of_cons h' b hb, map_zero]
      · push Not at h'
        have hea : e = a := by
          rcases List.mem_cons.mp he with h | h
          · exact h
          · exact absurd hbig (not_le.mpr (h' e h))
        subst hea
        have hl : l = [] := by
          rcases l with _ | ⟨e', l'⟩
          · rfl
          · exfalso
            have := List.rel_of_pairwise_cons hp (List.mem_cons_self ..)
            have := h' e' (List.mem_cons_self ..)
            simp only [modeLE] at *
            omega
        subst hl
        have hmem := N.act_lev (D.gen_mem e.1) hb (p := e.2)
        have hneg : k + ((D.wt e.1 : ℤ) - e.2 - 1) < 0 := by
          have := hBm e.1; omega
        rw [N.lev_eq_bot_of_neg _ hneg, Submodule.mem_bot] at hmem
        exact hmem

end VOA.Classification.COne.C2LevelFinite
