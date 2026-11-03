/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaMomentumPolynomial

/-!
# A PBW basis for every general Virasoro Verma module

Mode stability and cyclicity give spanning by all negative words. Existing
straightening sorts those words. Free-momentum separation supplies their
independence at every complex charge and highest weight, with no PBW axiom.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule
open Module (End)
open LieAlgebra LieAlgebra.Extension UniversalEnvelopingAlgebra
variable (c h : ℂ)

/-- The `ℂ`-span of all creation monomials. -/
noncomputable def vermaNegSpan : Submodule ℂ (Verma c h) :=
  Submodule.span ℂ (Set.range (negWord c h))

/-- Every creation word belongs to their linear span by its defining generating set. This supplies the base membership used in mode-stability and spanning arguments. -/
theorem vermaNegWord_mem (L : List ℕ) : negWord c h L ∈ vermaNegSpan c h :=
  Submodule.subset_span ⟨L, rfl⟩

/-- The creation modes `L₋ₙ₋₁` preserve `negSpan` (prepend another creation operator). -/
theorem vermaNegSpan_neg_stable (n : ℕ) {s : Verma c h} (hs : s ∈ vermaNegSpan c h) :
    vermaMode c h (-(n : ℤ) - 1) s ∈ vermaNegSpan c h := by
  induction hs using Submodule.span_induction with
  | mem y hy => obtain ⟨ws, rfl⟩ := hy; exact vermaNegWord_mem c h (n :: ws)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ r ha

/-- Every mode sends a negative word into the negative-word span. Move
it to the right until the highest-weight equations apply; the commutator
produces shorter words and a scalar central term. -/
theorem vermaMode_negWord (m : ℤ) (ws : List ℕ) :
    vermaMode c h m (negWord c h ws) ∈ vermaNegSpan c h := by
  induction ws generalizing m with
  | nil =>
      rw [negWord_nil]
      by_cases hm : m<0
      · obtain ⟨i,hi⟩ : ∃ i : ℕ, m=-(i:ℤ)-1 := ⟨(-m-1).toNat,by omega⟩
        rw [hi]
        exact vermaNegWord_mem c h [i]
      · by_cases hz : m=0
        · subst m
          rw [vermaMode,verma_zero_acts]
          exact Submodule.smul_mem _ _ (vermaNegWord_mem c h [])
        · rw [vermaMode,verma_pos_annihilate c h m (by omega)]
          exact Submodule.zero_mem _
  | cons i ws ih =>
      rw [negWord_cons,vermaMode_comm_apply]
      apply Submodule.add_mem
      · exact Submodule.add_mem _ (vermaNegSpan_neg_stable c h i (ih m))
          (Submodule.smul_mem _ _ (ih _))
      · split_ifs
        · simp only [LinearMap.smul_apply,Module.End.one_apply]
          exact Submodule.smul_mem _ _ (vermaNegWord_mem c h ws)
        · exact Submodule.zero_mem _

/-- Any element of `𝔙𝔦𝔯` applied to a creation monomial stays in `negSpan` (reduce to the
generators via `mem_span_gensVir`). -/
theorem vermaRho_negWord_mem (x : Virasoro) (ws : List ℕ) :
    vermaRho c h x (negWord c h ws) ∈ vermaNegSpan c h := by
  induction (mem_span_gensVir x) using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨n, rfl⟩ | hy
      · exact vermaMode_negWord c h n ws
      · rw [Set.mem_singleton_iff] at hy; subst hy
        rw [verma_acts_central, LinearMap.smul_apply, LinearMap.id_coe, id_eq]
        exact Submodule.smul_mem _ _ (vermaNegWord_mem c h ws)
  | zero => rw [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ _ ha

/-- `negSpan` is stable under the whole `𝔙𝔦𝔯`-action. -/
theorem vermaNegSpan_rho_stable (x : Virasoro) {s : Verma c h} (hs : s ∈ vermaNegSpan c h) :
    vermaRho c h x s ∈ vermaNegSpan c h := by
  induction hs using Submodule.span_induction with
  | mem y hy => obtain ⟨ws, rfl⟩ := hy; exact vermaRho_negWord_mem c h x ws
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

/-- `negSpan` is a `U(𝔙𝔦𝔯)`-submodule. -/
theorem vermaNegSpan_smul_stable (r : UVir) {s : Verma c h} (hs : s ∈ vermaNegSpan c h) :
    r • s ∈ vermaNegSpan c h := by
  suffices H : ∀ p : TensorAlgebra ℂ Virasoro, ∀ t ∈ vermaNegSpan c h, (mkU p) • t ∈ vermaNegSpan c h by
    obtain ⟨p, rfl⟩ := mkU_surjective r
    exact H p s hs
  intro p
  induction p using TensorAlgebra.induction with
  | algebraMap a =>
      intro t ht; rw [AlgHom.commutes, algebraMap_smul UVir]; exact Submodule.smul_mem _ a ht
  | ι x => intro t ht; exact vermaNegSpan_rho_stable c h x ht
  | mul p q hp hq => intro t ht; rw [map_mul, mul_smul]; exact hp _ (hq t ht)
  | add p q hp hq =>
      intro t ht; rw [map_add, add_smul]; exact Submodule.add_mem _ (hp t ht) (hq t ht)

/-! ## §5  The spanning theorem. -/

/-- **The creation monomials span** `M(c,h)`: `negSpan = ⊤` (i.e. `L(c,0) = U(𝔙𝔦𝔯₋)·|0⟩`), the
spanning half of PBW.  `pbw`-free — via cyclicity `verma_cyclic c h`. -/
theorem vermaNegSpan_eq_top : vermaNegSpan c h = ⊤ := by
  rw [eq_top_iff]
  intro m _
  have hm : m ∈ Submodule.span UVir {highestVector c h} := by rw [verma_cyclic c h]; trivial
  rw [Submodule.mem_span_singleton] at hm
  obtain ⟨r, rfl⟩ := hm
  exact vermaNegSpan_smul_stable c h r (vermaNegWord_mem c h [])


/-- Straightening all negative words gives spanning by sorted words. Their
energy is preserved, although this statement combines every level. -/
theorem verma_sortedWord_span_top :
    ⊤ ≤ Submodule.span ℂ
      (Set.range (fun w : {w : List ℕ // SortedWord w} => negWord c h w.val)) := by
  rw [← vermaNegSpan_eq_top c h,vermaNegSpan,Submodule.span_le]
  rintro x ⟨ws,rfl⟩
  have hle : sortedSpan c h (energyHW ws) ≤ Submodule.span ℂ
      (Set.range (fun w : {w : List ℕ // SortedWord w} => negWord c h w.val)) := by
    rw [sortedSpan,Submodule.span_le]
    rintro y ⟨u,hu,_,rfl⟩
    exact Submodule.subset_span ⟨⟨u,hu⟩,rfl⟩
  exact hle (negWord_mem_sortedSpan c h ws)

/-- The unconditional PBW basis of M(c,h), indexed by all sorted negative
words. Entry i denotes L_(-i-1), so the index includes arbitrary L₋₁ powers.
Both spanning and independence are proved at every complex (c,h). -/
noncomputable def vermaSortedBasis :
    Module.Basis {w : List ℕ // SortedWord w} ℂ (Verma c h) :=
  Module.Basis.mk (verma_sortedWord_linearIndependent c h) (verma_sortedWord_span_top c h)

/-- The constructed basis vector is the original creation word, with no
normalization or change of basis hidden in the construction. -/
@[simp] theorem vermaSortedBasis_apply (w : {w : List ℕ // SortedWord w}) :
    vermaSortedBasis c h w=negWord c h w.val := Module.Basis.mk_apply _ _ w

/-- Every word letter contributes at least one to its Verma level, so its
length is bounded by that level. -/
theorem verma_length_le_energy (w : List ℕ) : w.length≤energyHW w := by
  induction w with
  | nil => simp
  | cons i w ih => simp only [List.length_cons,energyHW_cons]; omega

/-- Every mode index is bounded by the total level of a word containing it. -/
theorem verma_mem_lt_energy_succ (w : List ℕ) : ∀ i ∈ w, i<energyHW w+1 := by
  induction w with
  | nil => simp
  | cons j w ih =>
    intro i hi
    rw [energyHW_cons]
    rcases List.mem_cons.mp hi with he | he
    · omega
    · have := ih i he; omega

/-- At each fixed Verma level there are only finitely many words, since
both the word length and every entry are bounded by that level. -/
theorem verma_finite_energyEq (m : ℕ) : {ws : List ℕ | energyHW ws = m}.Finite := by
  set f : List ℕ → List (Fin (m + 1)) := fun ws => ws.map (fun i => ⟨min i m, by omega⟩) with hf
  have recover : ∀ ws ∈ {ws : List ℕ | energyHW ws = m}, (f ws).map Fin.val = ws := by
    intro ws hws
    simp only [Set.mem_setOf_eq] at hws
    rw [hf, List.map_map]
    conv_rhs => rw [← List.map_id ws]
    apply List.map_congr_left
    intro x hx
    have : x < m + 1 := hws ▸ verma_mem_lt_energy_succ ws x hx
    simp only [Function.comp_apply, id_eq]; omega
  apply Set.Finite.of_finite_image (f := f)
  · apply Set.Finite.subset (List.finite_length_le (Fin (m + 1)) (n := m))
    rintro _ ⟨ws, hws, rfl⟩
    simp only [Set.mem_setOf_eq] at hws
    change (f ws).length ≤ m
    simp only [hf, List.length_map]
    have := verma_length_le_energy ws; omega
  · intro ws1 h1 ws2 h2 heq
    rw [← recover ws1 h1, ← recover ws2 h2, heq]

/-- A sorted word of level n is a partition of n into positive parts:
entry i stands for the part i+1. -/
def VermaPartitions (n : ℕ) := {w : List ℕ // SortedWord w ∧ energyHW w=n}

/-- The finite partition index type needed for level matrices and dimensions. -/
noncomputable instance vermaPartitionsFintype (n : ℕ) : Fintype (VermaPartitions n) :=
  ((verma_finite_energyEq n).subset (fun _ hw => hw.2)).fintype

/-- The original creation word, regarded as a vector in its level span. -/
noncomputable def vermaLevelWord (n : ℕ) (w : VermaPartitions n) : sortedSpan c h n :=
  ⟨negWord c h w.val,negWord_mem_sortedSpan_of_sorted c h w.property.1 w.property.2⟩

/-- Independence survives restriction to any one Verma level. -/
theorem vermaLevelWord_linearIndependent (n : ℕ) :
    LinearIndependent ℂ (vermaLevelWord c h n) := by
  refine LinearIndependent.of_comp (sortedSpan c h n).subtype ?_
  rw [linearIndependent_iff']
  intro s g he i hi
  exact verma_negWord_coef_zero_indexed (fun w : VermaPartitions n => w.val)
    Subtype.val_injective (fun w => w.property.1) c h s g he i hi

/-- The indexed level words span the level space by its definition. -/
theorem vermaLevelWord_span (n : ℕ) :
    ⊤ ≤ Submodule.span ℂ (Set.range (vermaLevelWord c h n)) := by
  have hi : Function.Injective (sortedSpan c h n).subtype := Subtype.val_injective
  have hm : Submodule.map (sortedSpan c h n).subtype
      (Submodule.span ℂ (Set.range (vermaLevelWord c h n))) =
      Submodule.map (sortedSpan c h n).subtype ⊤ := by
    rw [Submodule.map_span,Submodule.map_subtype_top,← Set.range_comp]
    have hs : Set.range ((sortedSpan c h n).subtype ∘ vermaLevelWord c h n) =
        {x | ∃ w : List ℕ, SortedWord w ∧ energyHW w=n ∧ negWord c h w=x} := by
      ext x
      constructor
      · rintro ⟨w,rfl⟩; exact ⟨w.val,w.property.1,w.property.2,rfl⟩
      · rintro ⟨w,hw,he,rfl⟩; exact ⟨⟨w,hw,he⟩,rfl⟩
    rw [hs]
    rfl
  rw [Submodule.map_injective_of_injective hi hm]

/-- The partition-indexed basis of the actual level-n Verma word span. -/
noncomputable def vermaLevelBasis (n : ℕ) :
    Module.Basis (VermaPartitions n) ℂ (sortedSpan c h n) :=
  Module.Basis.mk (vermaLevelWord_linearIndependent c h n) (vermaLevelWord_span c h n)

/-- The dimension of a Verma word level is the number of partitions into
positive parts, independently of c and h. This is not a character formula
for a simple quotient or a singular submodule. -/
theorem vermaLevel_finrank (n : ℕ) :
    Module.finrank ℂ (sortedSpan c h n)=Fintype.card (VermaPartitions n) :=
  Module.finrank_eq_card_basis (vermaLevelBasis c h n)

end VOA.InverseDS.VirasoroVerma
