/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.JacobiTripleCore

/-!
# Power series indexed by an arbitrary type with finite fibres

`fsr c e = ∑_{i : ι} c i · X^{e i}` for any index type `ι`, meaningful when every fibre `e⁻¹(d)` is
finite (`FinFib e`).  This is the bookkeeping device for lattice sums: reindexing along an
equivalence or along an injective map whose range contains the support (`fsr_equiv`,
`fsr_comp_injective`), splitting the index set (`fsr_split`), products of sums
(`fsr_mul`), sign-reversing involutions (`fsr_eq_zero_of_antisymm`), and the bridge to
`zSeries` (`zSeries_eq_fsr`).
-/

namespace VOA.QSeries.JTP

open PowerSeries

open scoped BigOperators

noncomputable section

section Fiber

variable {R : Type*} [CommRing R] {ι κ : Type*}

/-- `∑_{i : ι} c i · X^{e i}` (coefficientwise `finsum`). -/
def fsr (c : ι → R) (e : ι → ℕ) : PowerSeries R :=
  PowerSeries.mk fun d => ∑ᶠ i, if e i = d then c i else 0

/-- Every fibre of `e` is finite. -/
def FinFib (e : ι → ℕ) : Prop := ∀ d, {i | e i = d}.Finite

theorem coeff_fsr (c : ι → R) (e : ι → ℕ) (d : ℕ) :
    coeff d (fsr c e) = ∑ᶠ i, if e i = d then c i else 0 := by
  simp [fsr]

/-- Any finset containing the relevant part of the fibre computes the coefficient. -/
theorem coeff_fsr_of_subset (c : ι → R) (e : ι → ℕ) (d : ℕ) (s : Finset ι)
    (hs : ∀ i, e i = d → c i ≠ 0 → i ∈ s) :
    coeff d (fsr c e) = ∑ i ∈ s, if e i = d then c i else 0 := by
  rw [coeff_fsr]
  apply finsum_eq_sum_of_support_subset
  intro i hi
  rw [Function.mem_support] at hi
  split_ifs at hi with h
  · exact hs i h hi
  · exact absurd rfl hi

theorem coeff_fsr_fib (c : ι → R) {e : ι → ℕ} (he : FinFib e) (d : ℕ) :
    coeff d (fsr c e) = ∑ i ∈ (he d).toFinset, if e i = d then c i else 0 :=
  coeff_fsr_of_subset c e d _ fun _ hi _ => (he d).mem_toFinset.mpr hi

theorem fsr_congr {c c' : ι → R} {e e' : ι → ℕ} (hc : ∀ i, c i = c' i) (he : ∀ i, e i = e' i) :
    fsr c e = fsr c' e' := by
  rw [show c = c' from funext hc, show e = e' from funext he]

/-- Reindexing along an equivalence. -/
theorem fsr_equiv (σ : κ ≃ ι) (c : ι → R) (e : ι → ℕ) :
    fsr (fun k => c (σ k)) (fun k => e (σ k)) = fsr c e := by
  ext d
  rw [coeff_fsr, coeff_fsr]
  exact finsum_comp_equiv σ (f := fun i => if e i = d then c i else 0)

/-- Reindexing along an injective map whose range contains the support of `c`. -/
theorem fsr_comp_injective (f : κ → ι) (hf : Function.Injective f) (c : ι → R) {e : ι → ℕ}
    (he : FinFib e) (hc : ∀ i, c i ≠ 0 → i ∈ Set.range f) :
    fsr (fun k => c (f k)) (fun k => e (f k)) = fsr c e := by
  ext d
  set s := (he d).toFinset
  rw [coeff_fsr_fib c he d]
  rw [coeff_fsr_of_subset _ _ d (s.preimage f hf.injOn) (fun k hk _ => by
    rw [Finset.mem_preimage]; exact (he d).mem_toFinset.mpr hk)]
  apply Finset.sum_preimage f s hf.injOn (fun i => if e i = d then c i else 0)
  intro i _ hi
  split_ifs
  · by_contra h; exact hi (hc i h)
  · rfl

theorem fsr_add (c c' : ι → R) {e : ι → ℕ} (he : FinFib e) :
    fsr (fun i => c i + c' i) e = fsr c e + fsr c' e := by
  ext d
  rw [map_add, coeff_fsr_fib _ he, coeff_fsr_fib _ he, coeff_fsr_fib _ he,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

theorem fsr_const_mul (a : R) (c : ι → R) {e : ι → ℕ} (he : FinFib e) :
    fsr (fun i => a * c i) e = PowerSeries.C a * fsr c e := by
  ext d
  rw [coeff_C_mul, coeff_fsr_fib _ he, coeff_fsr_fib _ he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

theorem fsr_neg (c : ι → R) {e : ι → ℕ} (he : FinFib e) :
    fsr (fun i => -c i) e = -fsr c e := by
  have := fsr_const_mul (-1) c he
  simp only [neg_one_mul, map_neg, map_one] at this
  rw [this]

theorem fsr_sub (c c' : ι → R) {e : ι → ℕ} (he : FinFib e) :
    fsr (fun i => c i - c' i) e = fsr c e - fsr c' e := by
  simp only [sub_eq_add_neg]
  rw [fsr_add _ _ he, fsr_neg _ he]

theorem fsr_zero (e : ι → ℕ) : fsr (fun _ => (0 : R)) e = 0 := by
  ext d; simp [coeff_fsr]

/-- Products of sums. -/
theorem fsr_mul (c : ι → R) (c' : κ → R) {e : ι → ℕ} {e' : κ → ℕ} (he : FinFib e)
    (he' : FinFib e') :
    fsr c e * fsr c' e' = fsr (fun p : ι × κ => c p.1 * c' p.2) (fun p => e p.1 + e' p.2) := by
  classical
  ext d
  set I := (Finset.range (d + 1)).biUnion fun a => (he a).toFinset
  set J := (Finset.range (d + 1)).biUnion fun b => (he' b).toFinset
  have hI : ∀ i, e i ≤ d → i ∈ I := fun i hi => Finset.mem_biUnion.mpr
    ⟨e i, Finset.mem_range.mpr (by omega), (he (e i)).mem_toFinset.mpr rfl⟩
  have hJ : ∀ j, e' j ≤ d → j ∈ J := fun j hj => Finset.mem_biUnion.mpr
    ⟨e' j, Finset.mem_range.mpr (by omega), (he' (e' j)).mem_toFinset.mpr rfl⟩
  rw [coeff_mul, coeff_fsr_of_subset _ _ d (I ×ˢ J) (fun p hp _ =>
    Finset.mem_product.mpr ⟨hI _ (by omega), hJ _ (by omega)⟩)]
  have hA : ∀ p ∈ Finset.antidiagonal d,
      coeff p.1 (fsr c e) * coeff p.2 (fsr c' e') =
        ∑ i ∈ I, ∑ j ∈ J, if (e i, e' j) = p then c i * c' j else 0 := by
    intro p hp
    have hp' := Finset.mem_antidiagonal.mp hp
    rw [coeff_fsr_of_subset _ _ p.1 I (fun i hi _ => hI i (by omega)),
      coeff_fsr_of_subset _ _ p.2 J (fun j hj _ => hJ j (by omega)), Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    obtain ⟨p1, p2⟩ := p
    simp only [Prod.mk.injEq]
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl hA, Finset.sum_comm, Finset.sum_product]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_antidiagonal]

/-- Sign-reversing involutions kill the sum. -/
theorem fsr_eq_zero_of_antisymm [NoZeroDivisors R] [CharZero R] (σ : ι ≃ ι) (c : ι → R)
    (e : ι → ℕ) (he : ∀ i, e (σ i) = e i) (hc : ∀ i, c (σ i) = -c i) (hfin : FinFib e) :
    fsr c e = 0 := by
  have h := fsr_equiv σ c e
  simp only [he, hc] at h
  rw [fsr_neg _ hfin] at h
  ext d
  have hd := congrArg (coeff d) h
  rw [map_neg] at hd
  rw [map_zero]
  have : (2 : R) * coeff d (fsr c e) = 0 := by linear_combination -hd
  exact (mul_eq_zero.mp this).resolve_left two_ne_zero

/-- Splitting the index set into the (disjoint) ranges of two injective maps. -/
theorem fsr_split {κ' : Type*} (f : κ → ι) (g : κ' → ι) (hf : Function.Injective f)
    (hg : Function.Injective g) (hcover : ∀ i, i ∈ Set.range f ∨ i ∈ Set.range g)
    (hdisj : ∀ k k', f k ≠ g k') (c : ι → R) {e : ι → ℕ} (he : FinFib e) :
    fsr c e = fsr (fun k => c (f k)) (fun k => e (f k)) +
      fsr (fun k => c (g k)) (fun k => e (g k)) := by
  classical
  have hsplit : fsr c e = fsr (fun i => (if i ∈ Set.range f then c i else 0) +
      (if i ∈ Set.range f then 0 else c i)) e :=
    fsr_congr (fun i => by split_ifs <;> simp) (fun _ => rfl)
  rw [hsplit, fsr_add _ _ he]
  congr 1
  · rw [← fsr_comp_injective f hf _ he (fun i hi => by by_contra h; simp [h] at hi)]
    exact fsr_congr (fun k => by simp) (fun _ => rfl)
  · rw [← fsr_comp_injective g hg _ he (fun i hi => by
      rcases hcover i with h | h
      · simp [h] at hi
      · exact h)]
    refine fsr_congr (fun k => ?_) (fun _ => rfl)
    have : g k ∉ Set.range f := by rintro ⟨k', hk'⟩; exact hdisj k' k hk'
    simp [this]

theorem fsr_indicator_range (f : κ → ι) [DecidablePred (· ∈ Set.range f)]
    (hf : Function.Injective f) (c : ι → R) {e : ι → ℕ} (he : FinFib e) :
    fsr (fun i => if i ∈ Set.range f then c i else 0) e =
      fsr (fun k => c (f k)) (fun k => e (f k)) := by
  rw [← fsr_comp_injective f hf _ he (fun i hi => by by_contra hn; simp [hn] at hi)]
  exact fsr_congr (fun k => by simp) (fun _ => rfl)

/-- Splitting the index set into the (disjoint) ranges of three injective maps. -/
theorem fsr_split3 {κ' κ'' : Type*} (f : κ → ι) (g : κ' → ι) (h : κ'' → ι)
    (hf : Function.Injective f) (hg : Function.Injective g) (hh : Function.Injective h)
    (hcover : ∀ i, i ∈ Set.range f ∨ i ∈ Set.range g ∨ i ∈ Set.range h)
    (hfg : ∀ k k', f k ≠ g k') (hfh : ∀ k k', f k ≠ h k') (hgh : ∀ k k', g k ≠ h k')
    (c : ι → R) {e : ι → ℕ} (he : FinFib e) :
    fsr c e = fsr (fun k => c (f k)) (fun k => e (f k)) +
      fsr (fun k => c (g k)) (fun k => e (g k)) + fsr (fun k => c (h k)) (fun k => e (h k)) := by
  classical
  have hsplit : fsr c e = fsr (fun i => ((if i ∈ Set.range f then c i else 0) +
      (if i ∈ Set.range g then c i else 0)) + (if i ∈ Set.range h then c i else 0)) e := by
    refine fsr_congr (fun i => ?_) (fun _ => rfl)
    rcases hcover i with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have h1 : f k ∉ Set.range g := by rintro ⟨k', hk'⟩; exact hfg k k' hk'.symm
      have h2 : f k ∉ Set.range h := by rintro ⟨k', hk'⟩; exact hfh k k' hk'.symm
      simp [h1, h2]
    · have h1 : g k ∉ Set.range f := by rintro ⟨k', hk'⟩; exact hfg k' k hk'
      have h2 : g k ∉ Set.range h := by rintro ⟨k', hk'⟩; exact hgh k k' hk'.symm
      simp [h1, h2]
    · have h1 : h k ∉ Set.range f := by rintro ⟨k', hk'⟩; exact hfh k' k hk'
      have h2 : h k ∉ Set.range g := by rintro ⟨k', hk'⟩; exact hgh k' k hk'
      simp [h1, h2]
  rw [hsplit, fsr_add _ _ he, fsr_add _ _ he]
  rw [fsr_indicator_range f hf c he, fsr_indicator_range g hg c he,
    fsr_indicator_range h hh c he]

/-- The bridge to `zSeries`. -/
theorem zSeries_eq_fsr (c : ℤ → R) (e : ℤ → ℕ) (he : ∀ n, n.natAbs ≤ e n + 1) :
    zSeries c e = fsr c e := by
  ext d
  rw [coeff_zSeries, coeff_fsr_of_subset c e d (Finset.Icc (-(d : ℤ) - 1) (d + 1)) (fun n hn _ => by
    have := he n; simp only [Finset.mem_Icc]; omega), Finset.sum_filter]

theorem map_fsr {S : Type*} [CommRing S] (φ : R →+* S) (c : ι → R) {e : ι → ℕ} (he : FinFib e) :
    PowerSeries.map φ (fsr c e) = fsr (fun i => φ (c i)) e := by
  ext d
  rw [coeff_map, coeff_fsr_fib _ he, coeff_fsr_fib _ he, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

theorem X_pow_mul_fsr (m : ℕ) (c : ι → R) (e : ι → ℕ) :
    (X : PowerSeries R) ^ m * fsr c e = fsr c (fun i => e i + m) := by
  ext d
  rw [coeff_X_pow_mul', coeff_fsr, coeff_fsr]
  split_ifs with h
  · congr 1; ext i; congr 1; apply propext; omega
  · symm
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    rw [if_neg (by omega)]

theorem expand_fsr (p : ℕ) (hp : p ≠ 0) (c : ι → R) {e : ι → ℕ} (he : FinFib e) :
    expand p hp (fsr c e) = fsr c (fun i => p * e i) := by
  ext d
  rw [coeff_expand]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp), coeff_fsr_fib _ he,
      coeff_fsr_of_subset _ _ _ (he m).toFinset (fun i hi _ => (he m).mem_toFinset.mpr
        (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp) hi))]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Nat.mul_left_cancel_iff (Nat.pos_of_ne_zero hp)]
  · rw [coeff_fsr]
    symm
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    rw [if_neg (fun h' => h ⟨e i, h'.symm⟩)]

/-! ### Finiteness of fibres -/

theorem finFib_of_natAbs_le (e : ℤ → ℕ) (he : ∀ n, n.natAbs ≤ e n + 1) : FinFib e := by
  intro d
  apply (Set.finite_Icc (-(d : ℤ) - 1) (d + 1)).subset
  intro n hn
  have := he n
  simp only [Set.mem_setOf_eq] at hn
  simp only [Set.mem_Icc]
  omega

theorem FinFib.le {e : ι → ℕ} (he : FinFib e) (d : ℕ) : {i | e i ≤ d}.Finite := by
  have : {i | e i ≤ d} = ⋃ a ∈ Finset.range (d + 1), {i | e i = a} := by
    ext i; simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range, exists_prop]
    constructor
    · intro h; exact ⟨e i, by omega, rfl⟩
    · rintro ⟨a, ha, rfl⟩; omega
  rw [this]
  exact Set.Finite.biUnion (Finset.finite_toSet _) fun a _ => he a

theorem FinFib.prod {e : ι → ℕ} {e' : κ → ℕ} (he : FinFib e) (he' : FinFib e') :
    FinFib (fun p : ι × κ => e p.1 + e' p.2) := by
  intro d
  apply ((he.le d).prod (he'.le d)).subset
  intro p hp
  simp only [Set.mem_setOf_eq] at hp
  simp only [Set.mem_prod, Set.mem_setOf_eq]
  omega

theorem FinFib.comp_injective {e : ι → ℕ} (he : FinFib e) (f : κ → ι)
    (hf : Function.Injective f) : FinFib (fun k => e (f k)) := fun d =>
  (he d).preimage hf.injOn

theorem FinFib.of_le {e e' : ι → ℕ} (he : FinFib e) (h : ∀ i, e i ≤ e' i) : FinFib e' :=
  fun d => (he.le d).subset fun i hi => by
    simp only [Set.mem_setOf_eq] at hi ⊢; rw [← hi]; exact h i

theorem FinFib.add_const {e : ι → ℕ} (he : FinFib e) (m : ℕ) : FinFib (fun i => e i + m) :=
  he.of_le fun _ => Nat.le_add_right _ _

theorem FinFib.mul_const {e : ι → ℕ} (he : FinFib e) {p : ℕ} (hp : 0 < p) :
    FinFib (fun i => p * e i) :=
  he.of_le fun _ => Nat.le_mul_of_pos_left _ hp

end Fiber

end

end VOA.QSeries.JTP
