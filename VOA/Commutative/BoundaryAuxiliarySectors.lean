/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Commutative.BoundaryAuxiliaryHilbert
import VOA.Commutative.GordonRestrictedDual
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.Finiteness.Lattice
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Conformal pieces and canonical particle sectors

A polynomial monomial is sorted by its three current colors. Its jet orders give
an actual mode product in the canonical sector, with conformal weight equal to
particle count plus derivative degree.
-/
namespace VOA.BoundaryAuxiliarySectors
open scoped BigOperators
open MvPolynomial VOA.BoundaryAuxiliary VOA.GordonRestrictedDual
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

abbrev Slots (a b c : ℕ) := (Fin a ⊕ Fin b) ⊕ Fin c

def color (a b c : ℕ) : Slots a b c → Fin 3 :=
  Sum.elim (Sum.elim (fun _ => 0) (fun _ => 2)) (fun _ => 1)

def piece (m a b c D : ℕ) : Submodule K (Auxiliary (R := K) m) :=
  sector m D (color a b c)

def orders (l : List (Fin 3 × ℕ)) (i : Fin 3) : List ℕ :=
  (l.filter (fun v => v.1 == i)).map Prod.snd

def wordProduct (l : List (Fin 3 × ℕ)) : JetPoly K :=
  (l.map (fun v => X v)).prod

def wordWeight (l : List (Fin 3 × ℕ)) : ℕ :=
  (l.map conformalWeight).sum

/-- Sorting the three species preserves the actual polynomial product. -/
theorem wordProduct_eq_species (l : List (Fin 3 × ℕ)) :
    wordProduct (K := K) l =
      ((orders l 0).map (fun n => X ((0 : Fin 3), n))).prod *
      ((orders l 2).map (fun n => X ((2 : Fin 3), n))).prod *
      ((orders l 1).map (fun n => X ((1 : Fin 3), n))).prod := by
  induction l with
  | nil => simp [wordProduct, orders]
  | cons v l ih =>
      rcases v with ⟨i, n⟩
      fin_cases i <;> simp [wordProduct, orders, List.filter_cons] at ih ⊢ <;> rw [ih] <;> ring

/-- The conformal weight is the derivative degree plus the three particle counts. -/
theorem wordWeight_eq_species (l : List (Fin 3 × ℕ)) :
    wordWeight l = (orders l 0).length + (orders l 2).length + (orders l 1).length +
      ((orders l 0).sum + (orders l 2).sum + (orders l 1).sum) := by
  induction l with
  | nil => simp [wordWeight, orders]
  | cons v l ih =>
      rcases v with ⟨i, n⟩
      fin_cases i <;> simp [wordWeight, orders, List.filter_cons, conformalWeight] at * <;> omega

/-- The exact exponent tuple obtained from the three sorted jet-order lists. -/
def modes (e f h : List ℕ) : Slots e.length f.length h.length →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    (Sum.elim (Sum.elim (fun i => e[i.val]) (fun i => f[i.val])) (fun i => h[i.val]))

theorem modes_degree (e f h : List ℕ) :
    (modes e f h).degree = e.sum + f.sum + h.sum := by
  rw [Finsupp.degree_eq_sum]
  simp [modes, Fintype.sum_sum_type]

theorem modes_product (e f h : List ℕ) :
    (∏ i : Slots e.length f.length h.length,
      (X (color _ _ _ i, modes e f h i) : JetPoly K)) =
      (e.map (fun n => X ((0 : Fin 3), n))).prod *
      (f.map (fun n => X ((2 : Fin 3), n))).prod *
      (h.map (fun n => X ((1 : Fin 3), n))).prod := by
  simp only [Fintype.prod_sum_type, modes, color, Finsupp.coe_equivFunOnFinite_symm,
    Sum.elim_inl, Sum.elim_inr]
  rw [Fin.prod_univ_fun_getElem e (fun n => (X ((0 : Fin 3), n) : JetPoly K)),
    Fin.prod_univ_fun_getElem f (fun n => (X ((2 : Fin 3), n) : JetPoly K)),
    Fin.prod_univ_fun_getElem h (fun n => (X ((1 : Fin 3), n) : JetPoly K))]

/-- Every current word is in its literal canonical finite quotient sector. -/
theorem wordProduct_mem_piece (m : ℕ) (l : List (Fin 3 × ℕ)) :
    Ideal.Quotient.mk (auxiliaryIdeal (R := K) m) (wordProduct (K := K) l) ∈
      piece (K := K) m (orders l 0).length (orders l 2).length (orders l 1).length
        ((orders l 0).sum + (orders l 2).sum + (orders l 1).sum) := by
  rw [wordProduct_eq_species, ← modes_product]
  exact quotientMode_mem_sector m _ _ (modes _ _ _) (modes_degree _ _ _)

/-- The multiset spelling of the ordinary conformal weight of an exponent vector. -/
theorem wordWeight_toMultiset (d : Fin 3 × ℕ →₀ ℕ) :
    wordWeight d.toMultiset.toList = Finsupp.weight conformalWeight d := by
  unfold wordWeight
  rw [Multiset.sum_map_toList]
  rw [Finsupp.toMultiset_apply]
  simp only [Finsupp.sum]
  rw [← Multiset.coe_mapAddMonoidHom, map_sum]
  simp only [Multiset.coe_mapAddMonoidHom, Multiset.map_nsmul,
    Multiset.map_singleton, Multiset.sum_sum, Multiset.sum_nsmul,
    Multiset.sum_singleton, nsmul_eq_mul, Finsupp.weight_apply, Finsupp.sum]

/-- The word realization includes precisely the exponent multiplicities of a monomial. -/
theorem wordProduct_toMultiset (d : Fin 3 × ℕ →₀ ℕ) :
    wordProduct (K := K) d.toMultiset.toList = monomial d 1 := by
  unfold wordProduct
  rw [Multiset.prod_map_toList]
  rw [Finsupp.toMultiset_apply, monomial_eq]
  simp only [Finsupp.sum, Finsupp.prod, map_one, one_mul]
  rw [← Multiset.coe_mapAddMonoidHom, map_sum]
  simp only [Multiset.coe_mapAddMonoidHom, Multiset.map_nsmul,
    Multiset.map_singleton, Multiset.prod_sum, Multiset.prod_nsmul,
    Multiset.prod_singleton]

/-- All possible particle multiplicities in a fixed conformal weight. -/
abbrev Index (N : ℕ) := {t : Fin (N + 1) × Fin (N + 1) × Fin (N + 1) //
  t.1.val + t.2.1.val + t.2.2.val ≤ N}

def indexedPiece (m N : ℕ) (t : Index N) : Submodule K (Auxiliary (R := K) m) :=
  piece m t.val.1 t.val.2.1 t.val.2.2
    (N - (t.val.1.val + t.val.2.1.val + t.val.2.2.val))

instance indexedPiece_finite (m N : ℕ) (t : Index N) :
    FiniteDimensional K (indexedPiece (K := K) m N t) :=
  sector_finite _ _ _

/-- Every supported conformal monomial belongs to one finite canonical sector. -/
theorem monomial_mem_iSup_indexedPiece (m N : ℕ) (d : Fin 3 × ℕ →₀ ℕ)
    (hd : Finsupp.weight conformalWeight d = N) :
    Ideal.Quotient.mk (auxiliaryIdeal (R := K) m) (monomial d (1 : K)) ∈
      ⨆ t : Index N, indexedPiece (K := K) m N t := by
  let l := d.toMultiset.toList
  let a := (orders l 0).length
  let b := (orders l 2).length
  let c := (orders l 1).length
  let D := (orders l 0).sum + (orders l 2).sum + (orders l 1).sum
  have hN : a + b + c + D = N := by
    rw [← wordWeight_eq_species l, wordWeight_toMultiset, hd]
  let t : Index N := ⟨(⟨a, by omega⟩, ⟨b, by omega⟩, ⟨c, by omega⟩), by change a + b + c ≤ N; omega⟩
  have hD : N - (a + b + c) = D := by omega
  have hm := wordProduct_mem_piece (K := K) m l
  rw [wordProduct_toMultiset] at hm
  apply (le_iSup (indexedPiece (K := K) m N) t)
  simpa only [indexedPiece, t, hD] using hm

/-- The actual auxiliary conformal piece is spanned by finitely many canonical sectors. -/
theorem auxiliaryPiece_le_iSup_indexedPiece (m N : ℕ) :
    auxiliaryPiece (K := K) m N ≤ ⨆ t : Index N, indexedPiece (K := K) m N t := by
  intro x hx
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
  change Ideal.Quotient.mk (auxiliaryIdeal (R := K) m) f ∈ _
  clear hx
  induction hf using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add f g hf hg ihf ihg =>
      rw [map_add]
      exact Submodule.add_mem _ ihf ihg
  | monomial d c hd =>
      have hm := monomial_mem_iSup_indexedPiece (K := K) m N d hd
      have hc : monomial d c = c • (monomial d (1 : K) : JetPoly K) := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [hc]
      change (Ideal.Quotient.mkₐ K (auxiliaryIdeal (R := K) m))
        (c • monomial d (1 : K)) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ c hm

/-- A prescribed-particle mode product has precisely derivative degree plus particle count. -/
theorem piece_le_auxiliaryPiece (m a b c D : ℕ) :
    piece (K := K) m a b c D ≤ auxiliaryPiece (K := K) m (D + a + b + c) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨r, hr, rfl⟩
  have hrD := (VOA.GordonParticlePolynomial.mem_degreeFiber D r).mp hr
  have hh := MvPolynomial.IsWeightedHomogeneous.prod (Finset.univ : Finset (Slots a b c))
    (fun i => (X (color a b c i, r i) : JetPoly K))
    (fun i => conformalWeight (color a b c i, r i))
    (fun i _ => MvPolynomial.isWeightedHomogeneous_X K conformalWeight (color a b c i, r i))
  have hsum : (∑ i : Slots a b c, conformalWeight (color a b c i, r i)) = D + a + b + c := by
    simp only [conformalWeight, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, mul_one, ← Finsupp.degree_eq_sum,
      Fintype.card_sum, Fintype.card_fin, hrD]
    omega
  rw [hsum] at hh
  exact Submodule.mem_map.mpr ⟨_, hh, rfl⟩

/-- Every canonical sector in the finite sum has the correct conformal weight. -/
theorem iSup_indexedPiece_le_auxiliaryPiece (m N : ℕ) :
    (⨆ t : Index N, indexedPiece (K := K) m N t) ≤ auxiliaryPiece (K := K) m N := by
  apply iSup_le
  intro t
  have hN : N - (t.val.1.val + t.val.2.1.val + t.val.2.2.val) +
      t.val.1.val + t.val.2.1.val + t.val.2.2.val = N := by have h := t.property; omega
  unfold indexedPiece
  simpa only [hN] using piece_le_auxiliaryPiece (K := K) m t.val.1 t.val.2.1 t.val.2.2
    (N - (t.val.1.val + t.val.2.1.val + t.val.2.2.val))

/-- Exact sector decomposition inside the actual auxiliary arc quotient. -/
theorem auxiliaryPiece_eq_iSup_indexedPiece (m N : ℕ) :
    auxiliaryPiece (K := K) m N = ⨆ t : Index N, indexedPiece (K := K) m N t :=
  le_antisymm (auxiliaryPiece_le_iSup_indexedPiece m N)
    (iSup_indexedPiece_le_auxiliaryPiece m N)

/-- A finite submodule sum has dimension at most the sum of the component dimensions. -/
theorem finrank_finset_sup_le {ι V : Type*} [DecidableEq ι] [AddCommGroup V] [Module K V]
    (s : Finset ι) (P : ι → Submodule K V) [∀ i, FiniteDimensional K (P i)] :
    Module.finrank K ↥(s.sup P) ≤ ∑ i ∈ s, Module.finrank K (P i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sup_insert, Finset.sum_insert hi]
      exact (Submodule.finrank_add_le_finrank_add_finrank (P i) (s.sup P)).trans
        (Nat.add_le_add_left ih _)

/-- The global conformal bound is reduced to the finitely many actual canonical particle sectors. -/
theorem auxiliaryPiece_finrank_le_sum_sectors (m N : ℕ) :
    Module.finrank K (auxiliaryPiece (K := K) m N) ≤
      ∑ t : Index N, Module.finrank K (indexedPiece (K := K) m N t) := by
  rw [auxiliaryPiece_eq_iSup_indexedPiece, ← Finset.sup_univ_eq_iSup]
  exact finrank_finset_sup_le (K := K) Finset.univ (indexedPiece (K := K) m N)

end
end VOA.BoundaryAuxiliarySectors
