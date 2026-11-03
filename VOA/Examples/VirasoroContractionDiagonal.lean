/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroContractionSupport

/-!
# Nonzero diagonal central contractions

For a sorted word, contracting its first index gives one contribution for
each occurrence of that index. Removing the first index leaves the same word
in every such contribution. Repeating gives an explicit nonzero product:
each mode contributes its central bracket coefficient, and repeated equal
modes contribute successive positive integer multiplicities.
-/
namespace VOA.VirDeformModes.NormalOrdering

/-- The central bracket coefficient for the creation mode indexed by a,
whose actual positive mode number is a+2. -/
noncomputable def contractionWeight (a : ℕ) : ℂ :=
  (((a:ℂ)+2)^3-((a:ℂ)+2))/12

/-- The central coefficient factors into three consecutive positive integers.
In particular none of the creation modes allowed in a vacuum partition has
zero contraction weight. -/
theorem contractionWeight_factor (a : ℕ) :
    contractionWeight a = ((a:ℂ)+1)*((a:ℂ)+2)*((a:ℂ)+3)/12 := by
  unfold contractionWeight
  ring

/-- Every allowed creation index has a nonzero central contraction coefficient. -/
theorem contractionWeight_ne_zero (a : ℕ) : contractionWeight a ≠ 0 := by
  rw [contractionWeight_factor]
  apply div_ne_zero
  · apply mul_ne_zero
    · apply mul_ne_zero <;> norm_cast <;> omega
    · norm_cast <;> omega
  · norm_num

/-- A contraction vanishes if its matching index never occurs in the word. -/
theorem contractionNormal_eq_zero_of_not_mem (a : ℕ) (w : List ℕ) (ha : a ∉ w) :
    contractionNormal ((a:ℤ)+2) w = 0 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    have hai : a ≠ i := by intro h; subst i; simp at ha
    have haw : a ∉ w := fun h => ha (List.mem_cons_of_mem i h)
    have hmode : ¬ (a:ℤ)+2-(i:ℤ)-2=0 := by omega
    simp [contractionNormal, ih haw, hmode]

/-- In natural creation indices, a central contraction tests equality of
indices and uses their bracket weight. This form makes multiplicities explicit. -/
theorem contractionNormal_cons_index (a i : ℕ) (w : List ℕ) :
    contractionNormal ((a:ℤ)+2) (i::w) = prepend i (contractionNormal ((a:ℤ)+2) w) +
      if a=i then Finsupp.single (1,w) (contractionWeight a) else 0 := by
  rw [contractionNormal]
  have he : (a:ℤ)+2-(i:ℤ)-2=0 ↔ a=i := by omega
  simp [he, contractionWeight]

/-- Contracting the first index of a sorted word removes it with multiplicity
equal to its number of occurrences. Sortedness makes all matching removals
leave exactly the same ordered residual word. -/
theorem contractionNormal_sorted_head (a : ℕ) (w : List ℕ)
    (hs : (a::w).Pairwise (· ≥ ·)) :
    contractionNormal ((a:ℤ)+2) (a::w) =
      Finsupp.single (1,w) (((w.count a+1:ℕ):ℂ)*contractionWeight a) := by
  induction w with
  | nil => simp [contractionNormal, contractionWeight]
  | cons b v ih =>
    have hs' := List.pairwise_cons.mp hs
    have hv := List.pairwise_cons.mp hs'.2
    by_cases hab : a=b
    · subst b
      have he := ih hs'.2
      rw [contractionNormal_cons_index, if_pos rfl]
      rw [he]
      simp only [prepend, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
        ← Finsupp.single_add]
      congr 1
      simp only [List.count_cons_self, Nat.cast_add, Nat.cast_one]
      ring
    · have hnot : a ∉ b::v := by
        intro ha
        rcases List.mem_cons.mp ha with ha | ha
        · exact hab ha
        · have hba := hs'.1 b (by simp)
          have hab' := hv.1 a ha
          exact hab (by omega)
      have hz := contractionNormal_eq_zero_of_not_mem a (b::v) hnot
      have hc : (b::v).count a = 0 := List.count_eq_zero.mpr hnot
      rw [contractionNormal_cons_index, if_pos rfl, hz]
      simp [hc]

/-- The exact diagonal product, with each repeated index contributing its
remaining multiplicity. A block of r equal indices therefore contributes r!
times the r-th power of its central bracket coefficient. -/
noncomputable def diagonalContraction : List ℕ → ℂ
  | [] => 1
  | a::w => (((w.count a+1:ℕ):ℂ)*contractionWeight a)*diagonalContraction w

/-- Every factor in the diagonal product is nonzero: multiplicities are
positive integers and central bracket coefficients never vanish here. -/
theorem diagonalContraction_ne_zero (w : List ℕ) : diagonalContraction w ≠ 0 := by
  induction w with
  | nil => exact one_ne_zero
  | cons a w ih =>
    exact mul_ne_zero (mul_ne_zero (by norm_cast <;> omega)
      (contractionWeight_ne_zero a)) ih

/-- Concatenation of contraction words corresponds to composition of their
linear actions, with the rightmost word acting first. -/
theorem applyContractions_append (u v : List ℤ) (f : NormalForm) :
    applyContractions (u++v) f = applyContractions u (applyContractions v f) := by
  induction u with
  | nil => rfl
  | cons m u ih =>
    simpa only [List.cons_append, applyContractions, LinearMap.comp_apply] using
      congrArg (actContraction m) ih

/-- The first contraction of a sorted creation word adds one central factor
and multiplies by the number of matching indices and their bracket weight. -/
theorem actContraction_sorted_head (p a : ℕ) (w : List ℕ)
    (hs : (a::w).Pairwise (· ≥ ·)) :
    actContraction ((a:ℤ)+2) (Finsupp.single (p,a::w) 1) =
      Finsupp.single (p+1,w) (((w.count a+1:ℕ):ℂ)*contractionWeight a) := by
  simp only [actContraction, Finsupp.linearCombination_single, one_smul,
    contractionNormal_sorted_head a w hs, centralShift, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]

/-- Contracting a sorted word against its reversed adjoint leaves only the
vacuum, with the exact diagonal coefficient and one central factor per mode.
The initial central power p is arbitrary, allowing induction without an
extra commutation assumption. -/
theorem applyContractions_diagonal (w : List ℕ) (hs : w.Pairwise (· ≥ ·)) (p : ℕ) :
    applyContractions (w.reverse.map (fun (a : ℕ) => (a:ℤ)+2))
      (Finsupp.single (p,w) 1) =
      Finsupp.single (p+w.length,[]) (diagonalContraction w) := by
  induction w generalizing p with
  | nil => simp [applyContractions, diagonalContraction]
  | cons a w ih =>
    rw [List.reverse_cons, List.map_append, applyContractions_append]
    simp only [List.map_cons, List.map_nil, applyContractions, LinearMap.comp_apply,
      LinearMap.id_apply]
    rw [actContraction_sorted_head p a w hs]
    have he : Finsupp.single (p+1,w) (((w.count a+1:ℕ):ℂ)*contractionWeight a) =
        (((w.count a+1:ℕ):ℂ)*contractionWeight a) • Finsupp.single (p+1,w) 1 := by
      simp
    rw [he, map_smul, ih (List.pairwise_cons.mp hs).2]
    simp [Finsupp.smul_single, diagonalContraction, smul_eq_mul, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm]

/-- The diagonal entry of the actual top Gram matrix is the explicit
nonzero contraction product; this calculation holds at every weight. -/
theorem partitionTopMatrix_diagonal (n : ℕ) (i : VirModule.SortedOfEnergy n) :
    partitionTopMatrix n i i = diagonalContraction i.val := by
  rw [partitionTopMatrix_eq_contractions n i i rfl, adjoint_partitionWord,
    applyContractions_diagonal i.val i.property.1 0]
  simp [centralPolynomial, Polynomial.coeff_smul, smul_eq_mul]

/-- No diagonal entry of an equal-length top Gram block vanishes. -/
theorem partitionTopMatrix_diagonal_ne_zero (n : ℕ) (i : VirModule.SortedOfEnergy n) :
    partitionTopMatrix n i i ≠ 0 := by
  rw [partitionTopMatrix_diagonal]
  exact diagonalContraction_ne_zero i.val

end VOA.VirDeformModes.NormalOrdering
