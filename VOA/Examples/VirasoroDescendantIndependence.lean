/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroFockConjugation
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Independent creation descendants of nonzero vacuum-module states

Creation modes of index at most -2 have quadratic multiplication as their
highest polynomial-degree part. Acting on a nonzero polynomial preserves
that symbol, multiplied by the initial polynomial. Cancellation in a domain
therefore extends the vacuum independence argument to arbitrary starting states.
-/
namespace VOA.VirModule
open MvPolynomial (X)

/-- Multiplying by k copies of one oscillator variable raises the filtration
bound by k. This also covers the empty product. -/
theorem powX_mul_mem_FDeg (i k : ℕ) {d : ℕ} {p : Fock} (hp : p ∈ FDeg d) :
    (X i : Fock)^k * p ∈ FDeg (d+k) := by
  induction k with
  | zero => simpa using hp
  | succ k ih =>
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm, Nat.add_assoc] using
      mulX_mem_FDeg i ih

/-- A monomial belongs to the oscillator filtration at its exponent sum. -/
theorem monomial_mem_FDeg (s : ℕ →₀ ℕ) (a : ℂ) :
    MvPolynomial.monomial s a ∈ FDeg (s.sum fun _ k => k) := by
  classical
  suffices hh : MvPolynomial.monomial s (1:ℂ) ∈ FDeg (s.sum fun _ k => k) by
    simpa [MvPolynomial.smul_monomial] using (FDeg _).smul_mem a hh
  induction s using Finsupp.induction with
  | zero => simpa using one_mem_FDeg 0
  | @single_add i k s hi hk ih =>
    rw [add_comm, MvPolynomial.monomial_add_single]
    simpa [Finsupp.sum_add_index, add_comm, add_left_comm, add_assoc, mul_comm] using
      powX_mul_mem_FDeg i k ih

/-- The hand-built oscillator filtration contains every polynomial up to its
ordinary total degree, so no arbitrary filtration bound is needed later. -/
theorem mem_FDeg_totalDegree (p : Fock) : p ∈ FDeg p.totalDegree := by
  classical
  conv => arg 2; rw [p.as_sum]
  apply Submodule.sum_mem
  intro s hs
  apply FDeg_mono _ (monomial_mem_FDeg s _)
  exact Finset.le_sup (f := fun s : ℕ →₀ ℕ => s.sum fun _ k => k) hs

/-- Creation words acting on an arbitrary Fock state; entries i mean L_(-i-2).
The initial state need not be a highest-weight vector. -/
noncomputable def fockDescendant (lam : ℂ) : List ℕ → Fock →ₗ[ℂ] Fock
  | [] => LinearMap.id
  | i::w => (Lld lam (-(i:ℤ)-2)).comp (fockDescendant lam w)

/-- Each creation mode raises the polynomial filtration by at most two. -/
theorem fockDescendant_mem (lam : ℂ) (w : List ℕ) {d : ℕ} {p : Fock}
    (hp : p ∈ FDeg d) : fockDescendant lam w p ∈ FDeg (d+2*w.length) := by
  induction w with
  | nil => simpa [fockDescendant] using hp
  | cons i w ih =>
    simpa [fockDescendant, Nat.mul_add, Nat.add_assoc] using Lld_mem_FDeg lam i ih

/-- For a nonempty word, the difference from multiplication by its creation
symbol is at least one degree below the maximal degree bound. -/
theorem fockDescendant_error (lam : ℂ) (w : List ℕ) {d : ℕ} {p : Fock}
    (hp : p ∈ FDeg d) :
    fockDescendant lam w p - creationProd w * p ∈ FDeg (d+2*w.length-1) := by
  induction w with
  | nil => simp [fockDescendant]
  | cons i w ih =>
    change Lld lam (-(i:ℤ)-2) (fockDescendant lam w p) -
      creationPoly i * creationProd w * p ∈ _
    have he := errLd_mem lam i (fockDescendant_mem lam w hp)
    have hs : Lld lam (-(i:ℤ)-2) (fockDescendant lam w p) -
        creationPoly i * creationProd w * p =
        (Lld lam (-(i:ℤ)-2) (fockDescendant lam w p) -
          creationPoly i * fockDescendant lam w p) +
        creationPoly i * (fockDescendant lam w p - creationProd w * p) := by ring
    rw [hs]
    apply Submodule.add_mem
    · exact FDeg_mono (by simp only [List.length_cons]; omega) he
    · cases w with
      | nil => simp [fockDescendant]
      | cons j w =>
        exact FDeg_mono (by simp only [List.length_cons]; omega)
          (creationPoly_mul_mem i ih)


/-- At a fixed word length, sorted products of creation quadratics are
independent. The existing super-increasing one-variable specialization
separates their polynomial degrees. -/
theorem creationProd_fixedLength_coef_zero (K : ℕ) (s : Finset (List ℕ))
    (coef : List ℕ → ℂ) (hsort : ∀ w ∈ s, SortedWord w)
    (hlen : ∀ w ∈ s, w.length = K)
    (hsum : ∑ w ∈ s, coef w • creationProd w = 0) :
    ∀ w ∈ s, coef w = 0 := by
  classical
  have ht : ∑ w ∈ s, coef w • tSub (K+2) (creationProd w) = 0 := by
    have hh := congrArg (tSub (K+2)) hsum
    simpa only [map_sum, map_smul, map_zero] using hh
  apply coef_eq_zero_of_natDegree_inj s _ coef _ _ ht
  · intro w _; exact tSub_creationProd_ne_zero (K+2) (by omega) w
  · intro u hu v hv hd
    rw [natDegree_tSub_creationProd _ (by omega),
      natDegree_tSub_creationProd _ (by omega), hlen u hu, hlen v hv] at hd
    exact wordVal_inj (K+2) K (by omega) (by omega) u v (hsort u hu) (hsort v hv)
      (by rw [hlen u hu]) (by rw [hlen v hv]) (by omega)

/-- In a vanishing relation on a nonzero starting polynomial, the longest
creation words have zero coefficients. Their common starting polynomial
cannot cancel a nonzero highest-degree symbol in a polynomial domain. -/
theorem fockDescendant_topLength (lam : ℂ) (p : Fock) (hp : p ≠ 0)
    (K : ℕ) (hK : 0 < K) (s : Finset (List ℕ)) (coef : List ℕ → ℂ)
    (hsort : ∀ w ∈ s, SortedWord w) (hlen : ∀ w ∈ s, w.length ≤ K)
    (hsum : ∑ w ∈ s, coef w • fockDescendant lam w p = 0) :
    ∀ w ∈ s, w.length = K → coef w = 0 := by
  classical
  let t := s.filter (fun w => w.length = K)
  let S : Fock := ∑ w ∈ t, coef w • creationProd w
  have herr : ∀ w ∈ s,
      fockDescendant lam w p - (if w.length = K then creationProd w * p else 0)
        ∈ FDeg (p.totalDegree+2*K-1) := by
    intro w hw
    by_cases he : w.length = K
    · rw [if_pos he]
      simpa [he] using fockDescendant_error lam w (mem_FDeg_totalDegree p)
    · rw [if_neg he, sub_zero]
      exact FDeg_mono (by have := hlen w hw; omega)
        (fockDescendant_mem lam w (mem_FDeg_totalDegree p))
  have hmem : -(S*p) ∈ FDeg (p.totalDegree+2*K-1) := by
    have hh := (FDeg (p.totalDegree+2*K-1)).sum_mem
      (fun w hw => (FDeg _).smul_mem (coef w) (herr w hw))
    have he : (∑ w ∈ s, coef w •
        (fockDescendant lam w p - (if w.length = K then creationProd w * p else 0)))
        = -(S*p) := by
      simp only [smul_sub, Finset.sum_sub_distrib, hsum, zero_sub]
      congr 1
      simp only [S, t, Finset.sum_mul, smul_mul_assoc, Finset.sum_filter,
        smul_ite, smul_zero, ite_mul, zero_mul, smul_mul_assoc]
    rwa [he] at hh
  have hS : S = 0 := by
    by_contra hn
    have hh : S.IsHomogeneous (2*K) := by
      change S ∈ MvPolynomial.homogeneousSubmodule ℕ ℂ (2*K)
      apply Submodule.sum_mem
      intro w hw
      apply Submodule.smul_mem
      have he := (Finset.mem_filter.mp hw).2
      simpa [he] using creationProd_isHomogeneous w
    have hd := FDeg_totalDegree ((FDeg _).neg_mem hmem)
    rw [neg_neg, MvPolynomial.totalDegree_mul_of_isDomain hn hp,
      hh.totalDegree hn] at hd
    omega
  intro w hw he
  exact creationProd_fixedLength_coef_zero K t coef
    (fun u hu => hsort u (Finset.mem_filter.mp hu).1)
    (fun u hu => (Finset.mem_filter.mp hu).2) hS w (Finset.mem_filter.mpr ⟨hw,he⟩)

/-- Descending on the longest word eliminates every coefficient in a finite
relation among sorted creation descendants of any nonzero Fock polynomial. -/
theorem fockDescendant_coef_zero (lam : ℂ) (p : Fock) (hp : p ≠ 0) :
    ∀ (K : ℕ) (s : Finset (List ℕ)) (coef : List ℕ → ℂ),
      (∀ w ∈ s, SortedWord w) → (∀ w ∈ s, w.length ≤ K) →
      (∑ w ∈ s, coef w • fockDescendant lam w p = 0) → ∀ w ∈ s, coef w = 0 := by
  classical
  intro K
  induction K with
  | zero =>
    intro s coef hsort hlen hsum w hw
    have hall : ∀ u ∈ s, u = [] := by
      intro u hu
      exact List.length_eq_zero_iff.mp (by have := hlen u hu; omega)
    have hw0 := hall w hw
    have hs : s = {[]} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hw0 ▸ hw, hall⟩
    subst w
    rw [hs] at hsum
    simp only [Finset.sum_singleton, fockDescendant, LinearMap.id_apply] at hsum
    exact (smul_eq_zero.mp hsum).resolve_right hp
  | succ K ih =>
    intro s coef hsort hlen hsum w hw
    have ht := fockDescendant_topLength lam p hp (K+1) (by omega) s coef hsort hlen hsum
    by_cases he : w.length = K+1
    · exact ht w hw he
    · have hz : ∑ u ∈ s.filter (fun u => u.length = K+1),
          coef u • fockDescendant lam u p = 0 := by
        apply Finset.sum_eq_zero
        intro u hu
        rw [ht u (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hu).2, zero_smul]
      rw [← Finset.sum_filter_add_sum_filter_not s (fun u => u.length = K+1),
        hz, zero_add] at hsum
      apply ih (s.filter (fun u => ¬ u.length = K+1)) coef
        (fun u hu => hsort u (Finset.mem_filter.mp hu).1) _ hsum w
        (Finset.mem_filter.mpr ⟨hw,he⟩)
      intro u hu
      obtain ⟨hus,huK⟩ := Finset.mem_filter.mp hu
      have := hlen u hus
      omega


/-- Sorted creation descendants of any nonzero Fock polynomial are linearly
independent, with no bound on the word length or background charge. -/
theorem fockDescendant_linearIndependent (lam : ℂ) (p : Fock) (hp : p ≠ 0) :
    LinearIndependent ℂ (fun w : {w : List ℕ // SortedWord w} => fockDescendant lam w.1 p) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  have hinj : Function.Injective (fun w : {w : List ℕ // SortedWord w} => w.1) :=
    Subtype.val_injective
  have hcv : ∀ j : {w : List ℕ // SortedWord w},
      (Function.extend (fun w : {w : List ℕ // SortedWord w} => w.1) g 0) j.1 = g j :=
    fun j => hinj.extend_apply g 0 j
  have hsum' : ∑ l ∈ s.image (fun w : {w : List ℕ // SortedWord w} => w.1),
      (Function.extend (fun w : {w : List ℕ // SortedWord w} => w.1) g 0) l
        • fockDescendant lam l p = 0 := by
    rw [Finset.sum_image (fun x _ y _ h => hinj h)]
    simp only [hcv]
    exact hsum
  have hs : ∀ l ∈ s.image (fun w : {w : List ℕ // SortedWord w} => w.1), SortedWord l := by
    intro l hl
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hl
    exact j.2
  obtain ⟨w₀, -, hK⟩ := (s.image (fun w : {w : List ℕ // SortedWord w} => w.1)).exists_max_image
    List.length ⟨i.1, Finset.mem_image_of_mem _ hi⟩
  have hh := fockDescendant_coef_zero lam p hp w₀.length _ _ hs hK hsum' i.1
    (Finset.mem_image_of_mem _ hi)
  rwa [hcv i] at hh

/-- Ordered creation operators acting on an arbitrary universal vacuum-module
state. Entries i encode L_(-i-2); L_(-1) is not included in this family. -/
noncomputable def creationDescendant (c : ℂ) : List ℕ → VirUniv c →ₗ[ℂ] VirUniv c
  | [] => LinearMap.id
  | i::w => (Lop c (-(i:ℤ)-2)).comp (creationDescendant c w)

/-- The injective Fock realization intertwines entire creation words on any
starting state, not just on the vacuum. -/
theorem fockMap_creationDescendant {c lam : ℂ} (hlam : 1-12*lam^2=c)
    (w : List ℕ) (v : VirUniv c) :
    fockMap hlam (creationDescendant c w v) =
      fockDescendant lam w (fockMap hlam v) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change fockMap hlam (Lop c (-(i:ℤ)-2) (creationDescendant c w v)) = _
    rw [fockMap_Lop, ih]
    rfl

/-- At every central charge, sorted modes L_(-2), L_(-3), ... acting on ANY
nonzero universal vacuum-module state give an independent family. This proves
an actual descendant count; no singularity assumption is required. -/
theorem creationDescendant_linearIndependent (c : ℂ) (v : VirUniv c) (hv : v ≠ 0) :
    LinearIndependent ℂ
      (fun w : {w : List ℕ // SortedWord w} => creationDescendant c w.1 v) := by
  obtain ⟨lam,hlam⟩ := exists_lam c
  apply LinearIndependent.of_comp (fockMap hlam)
  have hp : fockMap hlam v ≠ 0 := fun he =>
    hv (fockMap_injective hlam (he.trans (map_zero _).symm))
  simpa only [Function.comp_def, fockMap_creationDescendant] using
    fockDescendant_linearIndependent lam (fockMap hlam v) hp
end VOA.VirModule
