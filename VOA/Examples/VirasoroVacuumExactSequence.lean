/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVacuumProjection
import VOA.Examples.VirasoroVermaEigenspaces

/-!
# The actual Verma-to-vacuum exact sequence

At every charge, the weight-one Verma module embeds in the weight-zero
Verma module by sending its highest vector to the translation descendant.
The vacuum projection has exactly this image as kernel. The proof uses the
actual PBW bases, not a character assumption or a Kac determinant formula.
This is an ordinary representation input for the uniform vacuum determinant
argument; it does not construct the additional minimal-model singular vector.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule

/-- The translation descendant of the weight-zero highest vector is itself
a highest-weight-one vector. The central commutator contributes nothing at
mode one, and every other positive mode reduces to a positive vacuum mode. -/
theorem translation_highest (c : ℂ) :
    IsHighestWeightVector (vermaRep c 0)
      (vermaMode c 0 (-1) (highestVector c 0)) c 1 where
  centralCharge := rfl
  pos_annihilate n hn := by
    change vermaMode c 0 n (vermaMode c 0 (-1) _) = 0
    rw [vermaMode_comm_apply]
    have hp : vermaMode c 0 n (highestVector c 0) = 0 :=
      verma_pos_annihilate c 0 n hn
    rw [hp, map_zero]
    by_cases he : n = 1
    · subst n
      norm_num [vermaMode, verma_zero_acts]
    · have hp' : vermaMode c 0 (n + -1) (highestVector c 0) = 0 :=
        verma_pos_annihilate c 0 _ (by omega)
      rw [hp', smul_zero, if_neg (by omega)]
      simp
  zero_acts := by
    change vermaMode c 0 0 (vermaMode c 0 (-1) _) = _
    rw [vermaMode_comm_apply]
    have hz : vermaMode c 0 0 (highestVector c 0) = 0 := by
      simpa using verma_zero_acts c 0
    simp [hz]

/-- The genuine representation map from highest weight one to highest weight
zero, obtained from the universal property at the translation descendant. -/
noncomputable def translationEmbedding (c : ℂ) : Verma c 1 →ₗ[ℂ] Verma c 0 :=
  universalMap (vermaRep c 0) _ (translation_highest c)

/-- On highest vectors the embedding is exactly translation, with coefficient
one. There is no charge-dependent normalization. -/
@[simp] theorem translationEmbedding_highest (c : ℂ) :
    translationEmbedding c (highestVector c 1) =
      vermaMode c 0 (-1) (highestVector c 0) :=
  universalMap_highestVector _ _ _

/-- The embedding commutes with every Virasoro mode, so its image is an
actual subrepresentation, not merely a vector-space copy. -/
theorem translationEmbedding_mode (c : ℂ) (n : ℤ) (v : Verma c 1) :
    translationEmbedding c (vermaMode c 1 n v) =
      vermaMode c 0 n (translationEmbedding c v) :=
  universalMap_intertwines _ _ _ _ _

/-- Every PBW word is sent to the same word with a final translation mode.
Appending zero preserves descending order and distinguishes all basis words. -/
theorem translationEmbedding_negWord (c : ℂ) (w : List ℕ) :
    translationEmbedding c (negWord c 1 w) = negWord c 0 (w ++ [0]) := by
  induction w with
  | nil => simp
  | cons i w ih => simp only [negWord_cons, translationEmbedding_mode, ih,
      List.cons_append]

/-- Appending a translation index to a sorted Verma word keeps it sorted. -/
theorem sortedWord_append_zero {w : List ℕ} (hw : SortedWord w) :
    SortedWord (w ++ [0]) := by
  exact List.pairwise_append.mpr ⟨hw, sortedWord_singleton 0, by simp⟩

/-- The translation map is injective at every charge: its images are a
subfamily of the already proved weight-zero Verma PBW basis. -/
theorem translationEmbedding_injective (c : ℂ) :
    Function.Injective (translationEmbedding c) := by
  let f : {w : List ℕ // SortedWord w} → {w : List ℕ // SortedWord w} :=
    fun w => ⟨w.val ++ [0], sortedWord_append_zero w.property⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact List.append_cancel_right (congrArg Subtype.val hab)
  have hi := (vermaSortedBasis c 0).linearIndependent.comp f hf
  have he : translationEmbedding c = (vermaSortedBasis c 1).constr ℂ
      (fun w => vermaSortedBasis c 0 (f w)) := by
    apply (vermaSortedBasis c 1).ext
    intro w
    rw [Module.Basis.constr_basis]
    simp only [vermaSortedBasis_apply, translationEmbedding_negWord]
    rfl
  rw [he]
  exact (vermaSortedBasis c 1).injective_constr_of_linearIndependent hi

/-- Projection kills every image of the translation embedding: the extra
vacuum relation is precisely that translation kills the vacuum. -/
theorem vacuumProjection_translationEmbedding (c : ℂ) :
    (vacuumProjection c).comp (translationEmbedding c) = 0 := by
  apply (vermaSortedBasis c 1).ext
  intro w
  suffices ∀ u : List ℕ,
      vacuumProjection c (translationEmbedding c (negWord c 1 u)) = 0 by
    simpa using this w.val
  intro u
  induction u with
  | nil => simp only [negWord_nil, translationEmbedding_highest,
      vacuumProjection_mode, vacuumProjection_highest]
           exact Lop_vacuum c (by omega)
  | cons i u ih => simp only [negWord_cons, translationEmbedding_mode,
      vacuumProjection_mode, ih, map_zero]

/-- Incrementing the indices converts a vacuum creation word to the same
actual Verma word. Projection returns the original vacuum creation state. -/
theorem vacuumProjection_succ_word (c : ℂ) (w : List ℕ) :
    vacuumProjection c (negWord c 0 (w.map Nat.succ)) = negWordVir c w := by
  induction w with
  | nil => exact vacuumProjection_highest c
  | cons i w ih =>
    simp only [List.map_cons, negWord_cons, vacuumProjection_mode, ih, negWordVir]
    rw [show (-(i.succ : ℤ) - 1) = -(i : ℤ) - 2 by omega]

/-- All sorted vacuum words span the universal vacuum module, including
all weights. This combines the existing straightening and cyclic spanning. -/
theorem vacuum_sortedWord_span_top (c : ℂ) :
    ⊤ ≤ Submodule.span ℂ
      (Set.range (fun w : {w : List ℕ // SortedWord w} => negWordVir c w.val)) := by
  rw [← negSpanVir_eq_top c, negSpanVir, Submodule.span_le]
  rintro x ⟨w, rfl⟩
  have hle : sortedSpanVir c (energyVir w) ≤ Submodule.span ℂ
      (Set.range (fun w : {w : List ℕ // SortedWord w} => negWordVir c w.val)) := by
    rw [sortedSpanVir, Submodule.span_le]
    rintro y ⟨u, hu, _, rfl⟩
    exact Submodule.subset_span ⟨⟨u, hu⟩, rfl⟩
  exact hle (negWordVir_mem_sortedSpanVir c w)

/-- The full vacuum PBW basis, combining the global
independence proved earlier with spanning. Its indices omit translation modes. -/
noncomputable def vacuumSortedBasis (c : ℂ) :
    Module.Basis {w : List ℕ // SortedWord w} ℂ (VirUniv c) :=
  Module.Basis.mk (sortedWord_linearIndependent c) (vacuum_sortedWord_span_top c)

/-- The vacuum basis is literally the original negative-word family. -/
@[simp] theorem vacuumSortedBasis_apply (c : ℂ) (w : {w : List ℕ // SortedWord w}) :
    vacuumSortedBasis c w = negWordVir c w.val := Module.Basis.mk_apply _ _ w

/-- A vector-space section of vacuum projection lifts the partition basis to
words with no translation index. It need not intertwine positive modes. -/
noncomputable def vacuumPBWSection (c : ℂ) : VirUniv c →ₗ[ℂ] Verma c 0 :=
  (vacuumSortedBasis c).constr ℂ (fun w => negWord c 0 (w.val.map Nat.succ))

/-- Projection after the PBW section is the identity on the entire vacuum
module. This proves surjectivity without an extra cyclicity assumption. -/
theorem vacuumProjection_section (c : ℂ) :
    (vacuumProjection c).comp (vacuumPBWSection c) = LinearMap.id := by
  apply (vacuumSortedBasis c).ext
  intro w
  change vacuumProjection c ((vacuumSortedBasis c).constr ℂ _ (vacuumSortedBasis c w)) = _
  rw [Module.Basis.constr_basis, vacuumProjection_succ_word]
  simp only [LinearMap.id_apply, vacuumSortedBasis_apply]

/-- Every vacuum state has an actual preimage in the weight-zero Verma
module, supplied by the partition-word section. -/
theorem vacuumProjection_surjective (c : ℂ) : Function.Surjective (vacuumProjection c) := by
  intro v
  exact ⟨vacuumPBWSection c v, LinearMap.congr_fun (vacuumProjection_section c) v⟩


/-- A decreasing word containing a translation index ends in that index.
Removing it leaves another decreasing word. This identifies exactly the PBW
words in the image of the weight-one embedding. -/
theorem sortedWord_zero_suffix {w : List ℕ} (hw : SortedWord w) (hz : 0 ∈ w) :
    ∃ u, SortedWord u ∧ w = u ++ [0] := by
  induction w with
  | nil => simp at hz
  | cons i w ih =>
    by_cases ht : 0 ∈ w
    · obtain ⟨u, hu, he⟩ := ih hw.tail ht
      refine ⟨i :: u, SortedWord.cons hu ?_, ?_⟩
      · intro j hj
        apply hw.head_ge j
        rw [he]
        exact List.mem_append_left _ hj
      · simp [he]
    · have hi : i = 0 := by simpa [ht, eq_comm] using hz
      subst i
      have he : w = [] := by
        cases w with
        | nil => rfl
        | cons j u =>
          have hj := hw.head_ge j (by simp)
          have : j = 0 := by omega
          simp [this] at ht
      subst w
      exact ⟨[], sortedWord_nil, rfl⟩

/-- A sorted word with no translation index comes uniquely from a vacuum
word by incrementing all indices. The predecessor operation preserves order. -/
theorem sortedWord_without_zero {w : List ℕ} (hw : SortedWord w) (hz : 0 ∉ w) :
    ∃ u, SortedWord u ∧ w = u.map Nat.succ := by
  refine ⟨w.map Nat.pred, ?_, ?_⟩
  · exact hw.map Nat.pred (fun a b hab => Nat.pred_le_pred hab)
  · rw [List.map_map]
    symm
    conv_rhs => rw [← List.map_id w]
    apply List.map_congr_left
    intro i hi
    have : i ≠ 0 := by intro he; subst i; exact hz hi
    exact Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero this)

/-- For every Verma state, subtracting the canonical lift of its vacuum
projection leaves a state in the embedded weight-one Verma module. This is
proved on the full PBW basis, including all translation powers. -/
theorem sub_section_projection_mem_translation_range (c : ℂ) (v : Verma c 0) :
    v - vacuumPBWSection c (vacuumProjection c v) ∈
      LinearMap.range (translationEmbedding c) := by
  let K := LinearMap.range (translationEmbedding c)
  let Q : Verma c 0 →ₗ[ℂ] Verma c 0 :=
    LinearMap.id - (vacuumPBWSection c).comp (vacuumProjection c)
  change Q v ∈ K
  have hv := (vermaSortedBasis c 0).mem_span v
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    rw [vermaSortedBasis_apply]
    change negWord c 0 w.val - vacuumPBWSection c
      (vacuumProjection c (negWord c 0 w.val)) ∈ K
    by_cases hz : 0 ∈ w.val
    · obtain ⟨u, hu, he⟩ := sortedWord_zero_suffix w.property hz
      rw [he, ← translationEmbedding_negWord]
      have hzero := LinearMap.congr_fun (vacuumProjection_translationEmbedding c)
        (negWord c 1 u)
      change vacuumProjection c (translationEmbedding c (negWord c 1 u)) = 0 at hzero
      rw [hzero, map_zero, sub_zero]
      exact ⟨negWord c 1 u, rfl⟩
    · obtain ⟨u, hu, he⟩ := sortedWord_without_zero w.property hz
      rw [he, vacuumProjection_succ_word]
      have hs : vacuumPBWSection c (negWordVir c u) = negWord c 0 (u.map Nat.succ) := by
        change ((vacuumSortedBasis c).constr ℂ _) (negWordVir c u) = _
        rw [← vacuumSortedBasis_apply c ⟨u, hu⟩, Module.Basis.constr_basis]
      rw [hs, sub_self]
      exact K.zero_mem
  | zero => rw [map_zero]; exact K.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact K.add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact K.smul_mem a hx

/-- The exact ordinary vacuum quotient: the kernel of M(c,0) to V(c,0)
is precisely the embedded M(c,1), at every complex central charge. This
neither assumes nor proves an additional minimal-model singular relation. -/
theorem vacuumProjection_ker (c : ℂ) :
    LinearMap.ker (vacuumProjection c) = LinearMap.range (translationEmbedding c) := by
  apply le_antisymm
  · intro v hv
    have h := sub_section_projection_mem_translation_range c v
    rw [LinearMap.mem_ker.mp hv, map_zero, sub_zero] at h
    exact h
  · rintro v ⟨u, rfl⟩
    exact LinearMap.congr_fun (vacuumProjection_translationEmbedding c) u


/-- The actual quotient by the embedded weight-one Verma module is linearly
equivalent to the universal vacuum module. Its construction uses the proved
kernel equality and surjectivity, rather than assuming an exact sequence. -/
noncomputable def vacuumQuotientEquiv (c : ℂ) :
    (Verma c 0 ⧸ LinearMap.range (translationEmbedding c)) ≃ₗ[ℂ] VirUniv c :=
  (Submodule.quotEquivOfEq _ _ (vacuumProjection_ker c).symm).trans
    ((vacuumProjection c).quotKerEquivOfSurjective (vacuumProjection_surjective c))

/-- On representatives the quotient equivalence is the original vacuum
projection; in particular it is normalized and compatible with all modes. -/
@[simp] theorem vacuumQuotientEquiv_mk (c : ℂ) (v : Verma c 0) :
    vacuumQuotientEquiv c (Submodule.Quotient.mk v) = vacuumProjection c v := rfl

/-- The quotient equivalence respects the actual action of every mode on
representatives. Stability of the embedded submodule follows from the
intertwining theorem for the embedding. -/
theorem vacuumQuotientEquiv_mode (c : ℂ) (n : ℤ) (v : Verma c 0) :
    vacuumQuotientEquiv c (Submodule.Quotient.mk (vermaMode c 0 n v)) =
      Lop c n (vacuumQuotientEquiv c (Submodule.Quotient.mk v)) :=
  vacuumProjection_mode c n v

/-- The weight-one embedding shifts relative PBW level by one, in both
directions. Injectivity prevents a nonhomogeneous preimage from becoming a
homogeneous image. Absolute L0 weights are unchanged. -/
theorem translationEmbedding_mem_level_iff (c : ℂ) (n : ℕ) (v : Verma c 1) :
    translationEmbedding c v ∈ sortedSpan c 0 (n + 1) ↔ v ∈ sortedSpan c 1 n := by
  rw [verma_mem_level_iff_eigen, verma_mem_level_iff_eigen]
  have he : (0 : ℂ) + ((n+1 : ℕ) : ℂ) = 1 + (n : ℂ) := by push_cast; ring
  rw [he, ← translationEmbedding_mode, ← map_smul]
  exact (translationEmbedding_injective c).eq_iff

/-- A homogeneous kernel vector of positive weight has a preimage in the
correct weight-one Verma level. This is the graded form of exactness needed
for character and singular-submodule comparisons. -/
theorem vacuumProjection_kernel_level (c : ℂ) (n : ℕ) (v : Verma c 0)
    (hv : v ∈ sortedSpan c 0 (n + 1)) (hz : vacuumProjection c v = 0) :
    ∃ u ∈ sortedSpan c 1 n, translationEmbedding c u = v := by
  have hr : v ∈ LinearMap.range (translationEmbedding c) := by
    rw [← vacuumProjection_ker]
    exact hz
  obtain ⟨u, rfl⟩ := hr
  exact ⟨u, (translationEmbedding_mem_level_iff c n u).mp hv, rfl⟩


/-- A mode kills an embedded state exactly when it kills its preimage.
This permits positive-mode singularity tests to pass through the actual
weight-one submodule in either direction. -/
theorem translationEmbedding_mode_zero_iff (c : ℂ) (m : ℤ) (u : Verma c 1) :
    vermaMode c 0 m (translationEmbedding c u) = 0 ↔ vermaMode c 1 m u = 0 := by
  rw [← translationEmbedding_mode, ← map_zero (translationEmbedding c)]
  exact (translationEmbedding_injective c).eq_iff

/-- If the weight-one Verma module has no singular state at the relevant
relative level, a nonzero singular state in M(c,0) survives in the actual
vacuum quotient. The ordinary absence condition remains explicit; proving it
at minimal charges requires further representation theory. -/
theorem vacuumProjection_survives_of_no_singular (c : ℂ) (n : ℕ)
    (habsent : ∀ u ∈ sortedSpan c 1 n,
      vermaMode c 1 1 u = 0 → vermaMode c 1 2 u = 0 → u = 0)
    (v : Verma c 0) (hv : v ∈ sortedSpan c 0 (n + 1)) (hne : v ≠ 0)
    (h1 : vermaMode c 0 1 v = 0) (h2 : vermaMode c 0 2 v = 0) :
    vacuumProjection c v ≠ 0 := by
  intro hz
  obtain ⟨u, hu, rfl⟩ := vacuumProjection_kernel_level c n v hv hz
  have hu0 := habsent u hu
    ((translationEmbedding_mode_zero_iff c 1 u).mp h1)
    ((translationEmbedding_mode_zero_iff c 2 u).mp h2)
  exact hne (by rw [hu0, map_zero])

end VOA.InverseDS.VirasoroVerma
