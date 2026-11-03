import VOA.DeligneAudit.D4FusionToroidalFusionAudit
import VOA.DeligneAudit.D4FusionToroidalFusionCyclic

/-! Cyclicity of the associated graded of the pure evaluation tensor. -/

namespace VOA.DeligneAudit.Toroidal.FusionGr

open VOA.DeligneAudit.Toroidal VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ}
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (A : ToroidalAction f V) (w : V) (m : ℕ)
variable (h : HighTShift A w m)

def gradedCyclic : Submodule ℂ (Gr A w) :=
  Submodule.span ℂ (Set.range fun l : List (TLtr n) =>
    wordOpT (grToroidal A w m h) l (grGenerator A w))

theorem gradedCyclic_op (c : Fin n) (i s : ℕ) :
    gradedCyclic A w m h ≤ (gradedCyclic A w m h).comap
      ((grToroidal A w m h).op c i s) := by
  rw [gradedCyclic, Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  exact Submodule.subset_span ⟨(c, i, s) :: l, rfl⟩

theorem evalWord_mem (l : List (TLtr n)) :
    evalWord A l w ∈ evalFbelow A w (tDegree l + 1) :=
  Submodule.subset_span ⟨l, Nat.lt_succ_self _, rfl⟩

theorem graded_word_mem (l : List (TLtr n)) :
    (kernel A w).mkQ
      (single A w (tDegree l) (evalWord A l w) (evalWord_mem A w l)) ∈
        gradedCyclic A w m h := by
  induction l with
  | nil =>
      exact Submodule.subset_span ⟨[], rfl⟩
  | cons a l ih =>
      by_cases hs : a.2.2 < m
      · have he := grOp_single A w m a.1 a.2.1 a.2.2 (tDegree l) hs
          (evalWord A l w) (evalWord_mem A w l)
        have hp := gradedCyclic_op A w m h a.1 a.2.1 a.2.2 ih
        change grOp A w m a.1 a.2.1 a.2.2 _ ∈ gradedCyclic A w m h at hp
        rw [he] at hp
        simpa only [evalWord, tDegree, Nat.add_comm] using hp
      · have hlow : A.op a.1 a.2.1 a.2.2 (evalWord A l w) ∈
            evalFbelow A w (tDegree l + a.2.2) := by
          have hh := h a.1 a.2.1 a.2.2 (tDegree l + 1)
            (Nat.le_of_not_lt hs) (evalWord_mem A w l)
          change A.op a.1 a.2.1 a.2.2 (evalWord A l w) ∈
            evalFbelow A w ((tDegree l + 1) + a.2.2 - 1) at hh
          have hi : (tDegree l + 1) + a.2.2 - 1 =
              tDegree l + a.2.2 := by omega
          rw [hi] at hh
          exact hh
        have hz : (kernel A w).mkQ
            (single A w (tDegree (a :: l)) (evalWord A (a :: l) w)
              (evalWord_mem A w (a :: l))) = 0 := by
          apply (Submodule.Quotient.mk_eq_zero (kernel A w)).mpr
          exact Submodule.subset_span ⟨tDegree (a :: l), _, by
            simpa only [tDegree, evalWord, Nat.add_comm] using hlow, rfl⟩
        rw [hz]
        exact Submodule.zero_mem _

theorem gradedCyclic_top : gradedCyclic A w m h = ⊤ := by
  let P := gradedCyclic A w m h
  have hs : ∀ d x (hx : x ∈ evalFbelow A w (d + 1)),
      symbol A w d ⟨x, hx⟩ ∈ P := by
    intro d x hx
    change x ∈ Submodule.span ℂ
      {v | ∃ l : List (TLtr n), tDegree l < d + 1 ∧ v = evalWord A l w} at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨l, hd, rfl⟩ := hx
        by_cases he : tDegree l = d
        · subst d
          simpa only [symbol_apply] using graded_word_mem A w m h l
        · have hlt : tDegree l < d := by omega
          rw [symbol_apply]
          have hz : (kernel A w).mkQ
              (single A w d (evalWord A l w) (by
                exact Submodule.subset_span ⟨l, hd, rfl⟩)) = 0 := by
            apply (Submodule.Quotient.mk_eq_zero (kernel A w)).mpr
            exact Submodule.subset_span ⟨d, _,
              Submodule.subset_span ⟨l, hlt, rfl⟩, rfl⟩
          rw [hz]
          exact Submodule.zero_mem P
    | zero =>
        change symbol A w d (0 : evalFbelow A w (d + 1)) ∈ P
        rw [map_zero]
        exact Submodule.zero_mem P
    | add x y hx hy ihx ihy =>
        change symbol A w d (⟨x, hx⟩ + ⟨y, hy⟩) ∈ P
        rw [map_add]
        exact Submodule.add_mem P ihx ihy
    | smul a x hx ih =>
        change symbol A w d (a • ⟨x, hx⟩) ∈ P
        rw [map_smul]
        exact Submodule.smul_mem P a ih
  have hnum : numerator A w ≤
      ((P.comap (kernel A w).mkQ).map (numerator A w).subtype) := by
    change Submodule.span ℂ
      {v | ∃ d x, x ∈ evalFbelow A w (d + 1) ∧ v = Finsupp.single d x} ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨d, x, hx, rfl⟩
    refine ⟨single A w d x hx, ?_, rfl⟩
    exact hs d x hx
  apply top_unique
  intro y _
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (kernel A w) y
  obtain ⟨u, hu, hval⟩ := hnum v.2
  have he : u = v := Subtype.ext hval
  rw [← he]
  exact hu

end

end VOA.DeligneAudit.Toroidal.FusionGr

#print axioms VOA.DeligneAudit.Toroidal.FusionGr.gradedCyclic_top
