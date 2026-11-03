import VOA.DeligneAudit.DeligneFusionUnivGGrade

/-!
# High-mode-letter filtration of the universal current module

This file constructs the decreasing filtration that counts letters of mode at least `m`,
proves compatibility with prepending one letter, and proves that its first quotient
satisfies the truncated relation specification. It makes no dimension or surjectivity
claim. A letter of mode `i*m+s` contributes one step, independently of `i`.
-/

namespace VOA.DeligneAudit.FusionToroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {n : ℕ} (f : Fin n → Fin n → Fin n → ℂ)

/-- Number of letters with mode at least `m`. -/
def tmWeight (m : ℕ) (l : List (Ltr n)) : ℕ :=
  (l.filter fun x => m ≤ x.2).length

theorem tmWeight_cons (m : ℕ) (x : Ltr n) (l : List (Ltr n)) :
    tmWeight m (x :: l) = tmWeight m l + if m ≤ x.2 then 1 else 0 := by
  by_cases h : m ≤ x.2 <;> simp [tmWeight, h]

/-- The span of words with at least `j` high-mode letters. -/
def Tfree (m j : ℕ) : Submodule ℂ (FreeW n) :=
  Submodule.span ℂ {v | ∃ l, j ≤ tmWeight m l ∧ v = sw l}

theorem sw_mem_Tfree (m j : ℕ) (l : List (Ltr n))
    (h : j ≤ tmWeight m l) : sw l ∈ Tfree m j :=
  Submodule.subset_span ⟨l, h, rfl⟩

theorem Tfree_anti (m : ℕ) {j k : ℕ} (h : j ≤ k) :
    Tfree (n := n) m k ≤ Tfree m j := by
  apply Submodule.span_mono
  rintro _ ⟨l, hl, rfl⟩
  exact ⟨l, h.trans hl, rfl⟩

/-- Prepending a letter raises the high-letter count by its indicator. -/
theorem consL_Tfree (m j : ℕ) (x : Ltr n) :
    Tfree (n := n) m j ≤
      (Tfree m (j + if m ≤ x.2 then 1 else 0)).comap (consL x) := by
  rw [Tfree, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  change consL x (sw l) ∈ Tfree m (j + if m ≤ x.2 then 1 else 0)
  rw [consL_sw]
  apply sw_mem_Tfree
  rw [tmWeight_cons]
  omega

/-- The image filtration on the universal module. -/
def TU (R : RelSpec n) (m j : ℕ) : Submodule ℂ (UModG f R) :=
  (Tfree m j).map (Jrel f R).mkQ

theorem TU_anti (R : RelSpec n) (m : ℕ) {j k : ℕ} (h : j ≤ k) :
    TU f R m k ≤ TU f R m j :=
  Submodule.map_mono (Tfree_anti m h)

theorem word_mem_TU (R : RelSpec n) (m j : ℕ) (l : List (Ltr n))
    (h : j ≤ tmWeight m l) :
    wordOp (univRepG f R) l (wUG f R) ∈ TU f R m j := by
  rw [wordOp_univG]
  exact ⟨sw l, sw_mem_Tfree m j l h, rfl⟩

theorem op_TU (R : RelSpec n) (m j : ℕ) (x : Ltr n) :
    TU f R m j ≤
      (TU f R m (j + if m ≤ x.2 then 1 else 0)).comap
        ((univRepG f R).op x.1 x.2) := by
  rintro _ ⟨v, hv, rfl⟩
  refine ⟨consL x v, consL_Tfree m j x hv, ?_⟩
  change (univRepG f R).op x.1 x.2 ((Jrel f R).mkQ v) = _
  rw [show (univRepG f R).op x.1 x.2 = opU f R x from rfl]

/-- Add every high-mode singleton to the tail relations. -/
def truncSpec (R : RelSpec n) (m : ℕ) : RelSpec n where
  tails := R.tails ∪ {t | ∃ c r, m ≤ r ∧ t = [(c, r)]}
  eig := R.eig

theorem TU_one_inv (R : RelSpec n) (m : ℕ) (c : Fin n) (r : ℕ) :
    TU f R m 1 ≤ (TU f R m 1).comap ((univRepG f R).op c r) := by
  exact (op_TU f R m 1 (c, r)).trans
    (Submodule.comap_mono (TU_anti f R m (by omega)))

/-- The quotient by words containing a high-mode letter. -/
abbrev truncMod (R : RelSpec n) (m : ℕ) := UModG f R ⧸ TU f R m 1

def truncRep (R : RelSpec n) (m : ℕ) : CurrentModule f (truncMod f R m) :=
  quotRepG (univRepG f R) (TU f R m 1) (TU_one_inv f R m)

def truncGen (R : RelSpec n) (m : ℕ) : truncMod f R m :=
  (TU f R m 1).mkQ (wUG f R)

/-- The first filtration quotient satisfies the original and high-mode relations. -/
theorem trunc_sat (R : RelSpec n) (m : ℕ) :
    Sat f (truncRep f R m) (truncGen f R m) (truncSpec R m) where
  tail t ht := by
    rcases ht with ht | ⟨c, r, hr, rfl⟩
    · rw [truncGen, truncRep, quot_wordOpG]
      rw [(univG_sat f R).tail t ht]
      simp
    · rw [truncGen, truncRep, quot_wordOpG]
      apply (Submodule.mkQ_apply (TU f R m 1) _).symm ▸
        (Submodule.Quotient.mk_eq_zero (TU f R m 1)).mpr ?_
      apply word_mem_TU
      simp [tmWeight, hr]
  eig q hq := by
    rw [truncGen, truncRep, quotRepG_op, (univG_sat f R).eig q hq]
    exact map_smul _ _ _

/-! ## Obstruction to an `i`-step shift for this filtration -/

/-- The coefficient of a one-letter word vanishes on the second step. -/
theorem Tfree_two_le_ker_single (m : ℕ) (x : Ltr n) :
    Tfree (n := n) m 2 ≤ LinearMap.ker (Finsupp.lapply [x]) := by
  rw [Tfree, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  change Finsupp.lapply [x] (sw l) = 0
  by_cases he : l = [x]
  · subst l
    by_cases hm : m ≤ x.2 <;> simp [tmWeight, hm] at hl
  · simp [sw, Finsupp.lapply_apply, he]

/-- A one-letter word never lies in the second high-letter filtration step. -/
theorem single_not_mem_Tfree_two (m : ℕ) (x : Ltr n) :
    sw [x] ∉ Tfree m 2 := by
  intro h
  have hz := Tfree_two_le_ker_single m x h
  simp [sw, Finsupp.lapply_apply] at hz

/-- Prepending a mode-two letter does not raise this filtration by two steps. -/
theorem no_two_step_shift :
    ¬ Tfree (n := 1) 1 0 ≤
      (Tfree 1 2).comap (consL ((0 : Fin 1), 2)) := by
  intro h
  have h0 : sw ([] : List (Ltr 1)) ∈ Tfree 1 0 :=
    sw_mem_Tfree 1 0 [] (Nat.zero_le _)
  have hx := h h0
  change consL ((0 : Fin 1), 2) (sw []) ∈ Tfree 1 2 at hx
  rw [consL_sw] at hx
  exact single_not_mem_Tfree_two 1 ((0 : Fin 1), 2) hx

end

end VOA.DeligneAudit.FusionToroidal

section AxiomAudit
#print axioms VOA.DeligneAudit.FusionToroidal.consL_Tfree
#print axioms VOA.DeligneAudit.FusionToroidal.op_TU
#print axioms VOA.DeligneAudit.FusionToroidal.TU_one_inv
#print axioms VOA.DeligneAudit.FusionToroidal.trunc_sat
#print axioms VOA.DeligneAudit.FusionToroidal.Tfree_two_le_ker_single
#print axioms VOA.DeligneAudit.FusionToroidal.no_two_step_shift
end AxiomAudit
