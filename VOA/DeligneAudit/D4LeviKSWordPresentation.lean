import VOA.DeligneAudit.D4LeviKSWordCoeff
import VOA.DeligneAudit.D4LeviKSLemma0Perm
import VOA.DeligneAudit.D4LeviKSSymmetricFinal

/-! Finite fixed-shape radical word sums as mode polynomials. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- A mode-labelled word can be reordered into the prescribed colour shape. -/
def HasWordShape {σ : Type*} [Fintype σ]
    (shape : σ → Fin 6) (l : List (Fin 6 × ℕ)) : Prop :=
  ∃ a : σ →₀ ℕ,
    l.Perm (shapedModes shape Finset.univ.toList a)

private theorem map_eq_on {α β : Type*} (is : List α) (f g : α → β)
    (h : is.map f = is.map g) : ∀ i ∈ is, f i = g i := by
  induction is with
  | nil => simp
  | cons i is ih =>
      simp only [List.map_cons, List.cons.injEq] at h
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact h.1
      · exact ih h.2 j hj

private theorem nodup_map_surj {α β : Type*} [Inhabited β] (is : List α)
    (his : is.Nodup) (ys : List β) (hlen : is.length = ys.length) :
    ∃ f : α → β, is.map f = ys := by
  classical
  induction is generalizing ys with
  | nil =>
      cases ys with
      | nil => exact ⟨fun _ => default, rfl⟩
      | cons y ys => simp at hlen
  | cons i is ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have hi : i ∉ is := (List.nodup_cons.mp his).1
          have ht : is.Nodup := (List.nodup_cons.mp his).2
          obtain ⟨f, hf⟩ := ih ht ys (Nat.succ.inj hlen)
          refine ⟨Function.update f i y, ?_⟩
          simp only [List.map_cons, Function.update_self]
          congr 1
          rw [← hf]
          apply List.map_congr_left
          intro j hj
          have hne : j ≠ i := by
            intro he
            subst j
            exact hi hj
          exact Function.update_of_ne hne _ _

theorem exists_colour_shape {σ : Type*} [Fintype σ]
    (cs : List (Fin 6)) (h : cs.length = Fintype.card σ) :
    ∃ shape : σ → Fin 6, Finset.univ.toList.map shape = cs := by
  classical
  apply nodup_map_surj Finset.univ.toList (Finset.nodup_toList _) cs
  simpa using h.symm

private theorem forall₂_fst_eq (cs : List (Fin 6))
    (ps : List (Fin 6 × ℕ))
    (h : List.Forall₂ (fun c p => c = p.1) cs ps) :
    cs = ps.map Prod.fst := by
  induction h with
  | nil => rfl
  | @cons c p cs ps hcp htail ih => simp [hcp, ih]

/-- Matching colour multisets can be reordered and assigned modes in any
    fixed enumeration of the common colour shape. -/
theorem hasWordShape_of_colourPerm {σ : Type*} [Fintype σ]
    (shape : σ → Fin 6) (l : List (Fin 6 × ℕ))
    (h : (l.map Prod.fst).Perm (Finset.univ.toList.map shape)) :
    HasWordShape shape l := by
  classical
  let is : List σ := Finset.univ.toList
  have hrel : (is.map shape).Perm (l.map Prod.fst) := h.symm
  have hpair_all (t : List (Fin 6 × ℕ)) :
      List.Forall₂ (fun c p => c = p.1) (t.map Prod.fst) t := by
    induction t with
    | nil => exact List.Forall₂.nil
    | cons p ps ih => exact List.Forall₂.cons rfl ih
  have hpair := hpair_all l
  obtain ⟨l', hfit, hp⟩ := List.perm_comp_forall₂ hrel hpair
  have hcolour : is.map shape = l'.map Prod.fst :=
    forall₂_fst_eq _ _ hfit
  have hlen : is.length = l'.length := by
    calc
      is.length = (is.map shape).length := (List.length_map ..).symm
      _ = (l'.map Prod.fst).length := congrArg List.length hcolour
      _ = l'.length := List.length_map ..
  obtain ⟨f, hf⟩ := nodup_map_surj is (Finset.nodup_toList _) l' hlen
  have hfirst : ∀ i ∈ is, shape i = (f i).1 := by
    apply map_eq_on is shape (fun i => (f i).1)
    simpa [← hf, List.map_map, Function.comp_def] using hcolour
  let a : σ →₀ ℕ := Finsupp.onFinset Finset.univ (fun i => (f i).2) (by simp)
  refine ⟨a, ?_⟩
  have hword : shapedModes shape is a = l' := by
    rw [← hf]
    apply List.map_congr_left
    intro i hi
    simp [shapedModes, a, hfirst i hi]
  rw [← hword] at hp
  exact hp.symm

/-- The explicit polynomial presenting a finite sum of radical words, after
    choosing their mode assignments in a common colour shape. -/
noncomputable def wordSumPolynomial {σ : Type*} [Fintype σ]
    (shape : σ → Fin 6) (terms : List (ℂ × List (Fin 6 × ℕ)))
    (hshape : ∀ p ∈ terms, HasWordShape shape p.2) :
    MvPolynomial σ ℂ :=
  (terms.attach.map fun p => p.1.1 • modeMonomial σ
    (Classical.choose (hshape p.1 p.2))).sum

/-- Reorder each summand using the abelian radical, then collect the
    resulting fixed-shape monomials into one polynomial. -/
theorem xyzEvaluation_of_wordSum {σ : Type*} [Fintype σ]
    (ρ : CurrentModule D4sector.f V) (w : V)
    (shape : σ → Fin 6) (terms : List (ℂ × List (Fin 6 × ℕ)))
    (hshape : ∀ p ∈ terms, HasWordShape shape p.2) :
    xyzEvaluation ρ w shape (wordSumPolynomial shape terms hshape) =
      (terms.map fun p => p.1 • radicalWord ρ w p.2).sum := by
  classical
  simp only [wordSumPolynomial, map_list_sum, List.map_map,
    Function.comp_def, map_smul]
  conv_rhs =>
    rw [← List.attach_map_subtype_val terms]
  simp only [List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro p hp
  have hperm := Classical.choose_spec (hshape p.1 p.2)
  simp only [xyzEvaluation, modeWordEvaluation_monomial]
  exact congrArg (p.1.1 • ·) (radicalWord_perm ρ w hperm).symm

/-- A fixed multiset of XYZ colours suffices for a polynomial presentation
    of any finite linear combination of radical words. -/
theorem xyzEvaluation_of_wordSum_colourPerm {σ : Type*} [Fintype σ]
    (ρ : CurrentModule D4sector.f V) (w : V)
    (shape : σ → Fin 6) (terms : List (ℂ × List (Fin 6 × ℕ)))
    (hcolour : ∀ p ∈ terms,
      (p.2.map Prod.fst).Perm (Finset.univ.toList.map shape)) :
    ∃ W : MvPolynomial σ ℂ,
      xyzEvaluation ρ w shape W =
        (terms.map fun p => p.1 • radicalWord ρ w p.2).sum := by
  have hshape : ∀ p ∈ terms, HasWordShape shape p.2 := by
    intro p hp
    exact hasWordShape_of_colourPerm shape p.2 (hcolour p hp)
  exact ⟨wordSumPolynomial shape terms hshape,
    xyzEvaluation_of_wordSum ρ w shape terms hshape⟩

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.xyzEvaluation_of_wordSum
#print axioms VOA.DeligneAudit.D4Levi.hasWordShape_of_colourPerm
#print axioms VOA.DeligneAudit.D4Levi.xyzEvaluation_of_wordSum_colourPerm
#print axioms VOA.DeligneAudit.D4Levi.exists_colour_shape
