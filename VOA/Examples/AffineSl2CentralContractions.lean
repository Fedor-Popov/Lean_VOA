/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2GramDegree

/-!
# Leading affine Gram terms from central contractions

The filtration counting central powers twice controls every noncentral sl2
bracket term. At equal word lengths the highest permitted level coefficient
is therefore exactly the coloured central-contraction algorithm. This is an
ordinary leading-term theorem; no determinant roots are asserted.
-/
namespace VOA.AffineVOA.NormalOrdering
open Polynomial

/-- A filtration in which a central factor counts twice and a creation mode
counts once. Central contractions attain the upper degree; merged-mode terms
lose one unit and therefore cannot contribute to the equal-length top pairing. -/
noncomputable def contractionFiltration (d : ℕ) : Submodule ℂ NormalForm :=
  Submodule.span ℂ {f | ∃ t : Label, 2*t.1+t.2.length ≤ d ∧ f=Finsupp.single t 1}

/-- A larger bound permits every term allowed by a smaller bound. -/
theorem contractionFiltration_mono {d e : ℕ} (h : d ≤ e) :
    contractionFiltration d ≤ contractionFiltration e :=
  Submodule.span_mono (by rintro f ⟨t,ht,rfl⟩; exact ⟨t,ht.trans h,rfl⟩)

/-- Scalar multiples of a single normal-form term obey its weighted bound. -/
theorem single_mem_contractionFiltration (t : Label) (a : ℂ) {d : ℕ}
    (h : 2*t.1+t.2.length ≤ d) : Finsupp.single t a ∈ contractionFiltration d := by
  have ht : Finsupp.single t (1:ℂ) ∈ contractionFiltration d :=
    Submodule.subset_span ⟨t,h,rfl⟩
  simpa only [Finsupp.smul_single, smul_eq_mul, mul_one] using
    Submodule.smul_mem (contractionFiltration d) a ht

/-- Prefixing one creation mode raises the weighted bound by one. -/
theorem prepend_mem_contractionFiltration (i : Fin 3 × ℕ) {d : ℕ} {f : NormalForm}
    (h : f ∈ contractionFiltration d) : prepend i f ∈ contractionFiltration (d+1) := by
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨t,ht,rfl⟩ := hf
    simp only [prepend, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    apply single_mem_contractionFiltration
    change 2*t.1+(i::t.2).length ≤ d+1
    simp only [List.length_cons]; omega
  | zero => simp
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul a f _ hf => simpa only [map_smul] using Submodule.smul_mem _ a hf

/-- Adding p central factors costs twice p in the weighted filtration. -/
theorem centralShift_mem_contractionFiltration (p : ℕ) {d : ℕ} {f : NormalForm}
    (h : f ∈ contractionFiltration d) : centralShift p f ∈ contractionFiltration (2*p+d) := by
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨t,ht,rfl⟩ := hf
    simp only [centralShift, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    apply single_mem_contractionFiltration
    change 2*(p+t.1)+t.2.length ≤ 2*p+d
    omega
  | zero => simp
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul a f _ hf => simpa only [map_smul] using Submodule.smul_mem _ a hf

/-- Every actual mode raises the weighted bound of a creation word by at
most one. This includes the noncentral commutator terms with changed indices. -/
theorem modeNormal_mem_contractionFiltration (a : Fin 3) (m : ℤ) (w : List (Fin 3 × ℕ)) :
    modeNormal a m w ∈ contractionFiltration (w.length+1) := by
  induction w generalizing a m with
  | nil =>
    by_cases hm : m < 0
    · simp only [modeNormal, if_pos hm]
      exact single_mem_contractionFiltration _ _ (by simp)
    · simp [modeNormal, hm]
  | cons i w ih =>
    by_cases hm : m < 0
    · simp only [modeNormal, if_pos hm]
      exact single_mem_contractionFiltration _ _ (by simp)
    · simp only [modeNormal, if_neg hm, List.length_cons]
      apply Submodule.add_mem
      · apply Submodule.add_mem
        · exact prepend_mem_contractionFiltration i (ih a m)
        · apply Submodule.sum_mem
          intro c hc
          exact Submodule.smul_mem _ _ (contractionFiltration_mono (by omega) (ih _ _))
      · split_ifs
        · exact single_mem_contractionFiltration _ _ (by simp; omega)
        · exact Submodule.zero_mem _

/-- Retain only central contractions when commuting a mode through a creation
word. The surviving terms remove a matching creation mode and add one central
factor; the remaining creation modes keep their original order. -/
noncomputable def contractionNormal (a : Fin 3) (m : ℤ) : List (Fin 3 × ℕ) → NormalForm
  | [] => 0
  | i::w => prepend i (contractionNormal a m w) +
      if m-(i.2:ℤ)-1=0 then Finsupp.single (1,w) ((m:ℂ)*kappa a i.1) else 0

/-- A single-mode central-contraction expression respects the same weighted
upper bound as the actual mode action. -/
theorem contractionNormal_mem (a : Fin 3) (m : ℤ) (w : List (Fin 3 × ℕ)) :
    contractionNormal a m w ∈ contractionFiltration (w.length+1) := by
  induction w with
  | nil => exact Submodule.zero_mem _
  | cons i w ih =>
    apply Submodule.add_mem
    · exact prepend_mem_contractionFiltration i ih
    · split_ifs
      · exact single_mem_contractionFiltration _ _ (by simp; omega)
      · exact Submodule.zero_mem _

/-- For a vacuum-annihilating mode, the discarded noncentral terms have one
less weighted degree than the full upper bound. This is the key error estimate. -/
theorem modeNormal_sub_contractionNormal_mem (a : Fin 3) (m : ℤ) (hm : 0 ≤ m) (w : List (Fin 3 × ℕ)) :
    modeNormal a m w - contractionNormal a m w ∈ contractionFiltration w.length := by
  induction w with
  | nil => simp [modeNormal, contractionNormal, show ¬m < 0 by omega]
  | cons i w ih =>
    have he : modeNormal a m (i::w) - contractionNormal a m (i::w) =
        prepend i (modeNormal a m w - contractionNormal a m w) +
          (∑ c : Fin 3, fabc a i.1 c • modeNormal c (m-(i.2:ℤ)-1) w) := by
      simp only [modeNormal, if_neg (by omega : ¬m < 0), contractionNormal, map_sub]
      abel
    rw [he]
    apply Submodule.add_mem _ (prepend_mem_contractionFiltration i ih)
    apply Submodule.sum_mem
    intro c hc
    exact Submodule.smul_mem _ _ (modeNormal_mem_contractionFiltration c _ w)

/-- Extend the central-contraction action linearly and leave existing central
powers in place. This is an auxiliary combinatorial operator, not an assumed
affine representation. -/
noncomputable def actContraction (a : Fin 3) (m : ℤ) : NormalForm →ₗ[ℂ] NormalForm :=
  Finsupp.linearCombination ℂ (fun t => centralShift t.1 (contractionNormal a m t.2))

/-- An actual mode raises the weighted bound by at most one on arbitrary
finite normal forms, including terms that already have central powers. -/
theorem actNormal_mem_contractionFiltration (a : Fin 3) (m : ℤ) {d : ℕ} {f : NormalForm}
    (h : f ∈ contractionFiltration d) : actNormal a m f ∈ contractionFiltration (d+1) := by
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨t,ht,rfl⟩ := hf
    simp only [actNormal, Finsupp.linearCombination_single, one_smul]
    exact contractionFiltration_mono (by omega)
      (centralShift_mem_contractionFiltration t.1 (modeNormal_mem_contractionFiltration a m t.2))
  | zero => simp
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul a f _ hf => simpa only [map_smul] using Submodule.smul_mem _ a hf

/-- The central-contraction action also raises the bound by at most one. -/
theorem actContraction_mem (a : Fin 3) (m : ℤ) {d : ℕ} {f : NormalForm}
    (h : f ∈ contractionFiltration d) : actContraction a m f ∈ contractionFiltration (d+1) := by
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨t,ht,rfl⟩ := hf
    simp only [actContraction, Finsupp.linearCombination_single, one_smul]
    exact contractionFiltration_mono (by omega)
      (centralShift_mem_contractionFiltration t.1 (contractionNormal_mem a m t.2))
  | zero => simp
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul a f _ hf => simpa only [map_smul] using Submodule.smul_mem _ a hf

/-- Replacing a vacuum-annihilating actual mode by central contractions loses
one unit relative to the maximal degree. The error preserves the original bound. -/
theorem actNormal_sub_actContraction_mem (a : Fin 3) (m : ℤ) (hm : 0 ≤ m)
    {d : ℕ} {f : NormalForm} (h : f ∈ contractionFiltration d) :
    actNormal a m f - actContraction a m f ∈ contractionFiltration d := by
  change (actNormal a m - actContraction a m) f ∈ contractionFiltration d
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨t,ht,rfl⟩ := hf
    simp only [LinearMap.sub_apply, actNormal, actContraction,
      Finsupp.linearCombination_single, one_smul, ← map_sub]
    exact contractionFiltration_mono ht (centralShift_mem_contractionFiltration t.1
      (modeNormal_sub_contractionNormal_mem a m hm t.2))
  | zero => simp
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul a f _ hf => simpa only [map_smul] using Submodule.smul_mem _ a hf

/-- Apply a finite mode word to an arbitrary normal form by actual normal
ordering. The list order is the operator composition order. -/
noncomputable def applyNormal : List (Fin 3 × ℤ) → NormalForm →ₗ[ℂ] NormalForm
  | [] => LinearMap.id
  | m::u => (actNormal m.1 m.2).comp (applyNormal u)

/-- Apply the same word using only central contractions at each step. -/
noncomputable def applyContractions : List (Fin 3 × ℤ) → NormalForm →ₗ[ℂ] NormalForm
  | [] => LinearMap.id
  | m::u => (actContraction m.1 m.2).comp (applyContractions u)

/-- Applying a prefix to a normalized word is the normalization of the
concatenated word. Thus the auxiliary linear action computes the same object
as the original recursive normalization. -/
theorem applyNormal_wordNormal (u v : List (Fin 3 × ℤ)) :
    applyNormal u (wordNormal v) = wordNormal (u++v) := by
  induction u with
  | nil => rfl
  | cons m u ih => simp only [applyNormal, LinearMap.comp_apply, ih, List.cons_append, wordNormal]

/-- A central-contraction word of length k raises the weighted bound by at
most k. This includes partial contractions that leave creation modes behind. -/
theorem applyContractions_mem (u : List (Fin 3 × ℤ)) {d : ℕ} {f : NormalForm}
    (h : f ∈ contractionFiltration d) :
    applyContractions u f ∈ contractionFiltration (d+u.length) := by
  induction u with
  | nil => simpa only [applyContractions, LinearMap.id_apply, List.length_nil, Nat.add_zero] using h
  | cons m u ih =>
    simpa only [applyContractions, LinearMap.comp_apply, List.length_cons, Nat.add_assoc] using
      actContraction_mem m.1 m.2 ih

/-- In a word of vacuum-annihilating modes, replacing all actual actions by
central contractions lowers the maximal weighted degree by at least one.
The induction retains every discarded noncentral term in the error bound. -/
theorem applyNormal_sub_applyContractions_mem (u : List (Fin 3 × ℤ))
    (hu : ∀ m ∈ u, 0 ≤ m.2) {d : ℕ} {f : NormalForm}
    (h : f ∈ contractionFiltration (d+1)) :
    applyNormal u f - applyContractions u f ∈ contractionFiltration (d+u.length) := by
  induction u with
  | nil => simp [applyNormal, applyContractions]
  | cons m u ih =>
    have hm := hu m (by simp)
    have ht : ∀ k ∈ u, 0 ≤ k.2 := fun k hk => hu k (by simp [hk])
    have he : applyNormal (m::u) f - applyContractions (m::u) f =
        actNormal m.1 m.2 (applyNormal u f - applyContractions u f) +
          (actNormal m.1 m.2 (applyContractions u f) - actContraction m.1 m.2 (applyContractions u f)) := by
      simp only [applyNormal, applyContractions, LinearMap.comp_apply, map_sub]
      abel
    rw [he]
    apply Submodule.add_mem
    · simpa only [List.length_cons, Nat.add_assoc] using
        actNormal_mem_contractionFiltration m.1 m.2 (ih ht)
    · have hh := actNormal_sub_actContraction_mem m.1 m.2 hm (applyContractions_mem u h)
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 u.length] using hh

/-- Vacuum pairing of weighted degree below 2k has zero coefficient at
central degree k: an empty creation term K^a has weighted degree 2a. -/
theorem centralPolynomial_coeff_zero_of_weight {d : ℕ} {f : NormalForm}
    (h : f ∈ contractionFiltration d) (k : ℕ) (hk : d < 2*k) :
    (centralPolynomial f).coeff k = 0 := by
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨t,ht,rfl⟩ := hf
    simp only [centralPolynomial, Finsupp.linearCombination_single, one_smul]
    split_ifs
    · apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_X_pow]
      omega
    · simp
  | zero => simp
  | add f g _ _ hf hg => simp only [map_add, coeff_add, hf, hg, add_zero]
  | smul a f _ hf => simp only [map_smul, coeff_smul, hf, smul_zero]

/-- The top charge coefficient of an equal-length pairing is computed by
central contractions alone. All noncentral merged-mode terms are proved to
vanish at that degree; this equality holds for every word length. -/
theorem equal_length_pairing_top_contractions (u : List (Fin 3 × ℤ)) (v : List (Fin 3 × ℕ))
    (hu : ∀ m ∈ u, 0 ≤ m.2) (hlen : u.length=v.length) :
    (wordPolynomial (u ++ v.map (fun i => (i.1,-(i.2:ℤ)-1)))).coeff v.length =
      (centralPolynomial (applyContractions u (Finsupp.single (0,v) 1))).coeff v.length := by
  change (centralPolynomial (wordNormal (u ++ v.map (fun i => (i.1,-(i.2:ℤ)-1))))).coeff _ = _
  rw [← applyNormal_wordNormal, wordNormal_creation]
  cases v with
  | nil =>
    have hu0 : u=[] := by simpa using hlen
    subst u
    rfl
  | cons i v =>
    have hf : Finsupp.single (0,i::v) (1:ℂ) ∈ contractionFiltration (v.length+1) :=
      single_mem_contractionFiltration _ _ (by simp)
    have hh := applyNormal_sub_applyContractions_mem u hu hf
    have hz := centralPolynomial_coeff_zero_of_weight hh (i::v).length (by
      simp only [List.length_cons] at hlen ⊢; omega)
    simpa only [map_sub, coeff_sub, sub_eq_zero] using hz


end VOA.AffineVOA.NormalOrdering
