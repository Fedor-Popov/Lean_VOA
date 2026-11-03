/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Examples.VirasoroPartitionBasis

/-!
# The Virasoro modes on `V(c,0)` have structure constants polynomial in `c`

This is step 1 of the route to an inhabitant of `VirCDef.IsCDeformation` (the `∂_c` deformation of
`V(c,0)`). The carrier `VirUniv c` depends on `c`, so "the
structure constants as functions of `c`" only makes sense against a `c`-free index set. The sorted
creation words supply one (`VirasoroPartitionBasis`).

A finitely supported family `P : List ℕ →₀ ℂ[X]` of polynomials gives, at every central charge,
the vector `polyComb P c = Σ_u (P u)(c) · L₋ᵤ|0⟩`.

* `exists_polyComb_Lop`: for each mode `m` and word `w` there is **one** `P`, independent of `c`,
  with `L_m (L₋w|0⟩) = polyComb P c` for **every** `c`. Here the words in `P` are arbitrary.
* `exists_sorted_polyComb`: every creation word is a `c`-uniform combination of **sorted** words.
  The straightening identity has no central term.
* `exists_sorted_polyComb_Lop`: the combination of the two. `L_m (L₋w|0⟩)` has a `c`-uniform
  expansion in the sorted basis with polynomial coefficients.
* `polyComb_injective`: such an expansion is unique, since sorted words are independent at every
  `c`. So the matrix of `L_m` in the sorted basis is a well-defined matrix of polynomials in `c`.

The remaining steps of the route are:
* the same statement for the modes of **all** states, not only of `ω`;
* differentiation, which gives `Y₁`;
* the order-`t` Jacobi identity, from polynomial identities via `Polynomial.funext`.
-/

namespace VOA.VirPoly

open VOA VOA.VirModule Polynomial

/-- `Σ_u (P u)(c) · L₋ᵤ|0⟩`, additive in `P`. -/
noncomputable def polyComb (c : ℂ) : (List ℕ →₀ ℂ[X]) →+ VirUniv c :=
  Finsupp.liftAddHom fun u =>
    { toFun := fun p => p.eval c • negWordVir c u
      map_zero' := by simp
      map_add' := fun p q => by simp [add_smul] }

@[simp] theorem polyComb_single (c : ℂ) (u : List ℕ) (p : ℂ[X]) :
    polyComb c (Finsupp.single u p) = p.eval c • negWordVir c u := by
  simp [polyComb]

theorem polyComb_smul (c : ℂ) (q : ℂ[X]) (P : List ℕ →₀ ℂ[X]) :
    polyComb c (q • P) = q.eval c • polyComb c P := by
  induction P using Finsupp.induction_linear with
  | zero => simp
  | add P Q hP hQ => rw [smul_add, map_add, map_add, hP, hQ, smul_add]
  | single u p => rw [Finsupp.smul_single, polyComb_single, polyComb_single, smul_eq_mul,
      eval_mul, mul_smul]

theorem polyComb_eq_sum (c : ℂ) (P : List ℕ →₀ ℂ[X]) :
    polyComb c P = ∑ u ∈ P.support, (P u).eval c • negWordVir c u := by
  conv_lhs => rw [← Finsupp.sum_single P]
  rw [Finsupp.sum, map_sum]
  simp

/-- Prepending a creation mode to every word. -/
theorem Lop_polyComb (c : ℂ) (n : ℕ) (P : List ℕ →₀ ℂ[X]) :
    Lop c (-(n : ℤ) - 2) (polyComb c P) = polyComb c (P.mapDomain (n :: ·)) := by
  induction P using Finsupp.induction_linear with
  | zero => simp
  | add P Q hP hQ => rw [map_add, map_add, hP, hQ, Finsupp.mapDomain_add, map_add]
  | single u p =>
      rw [polyComb_single, Finsupp.mapDomain_single, polyComb_single, map_smul]
      rfl

/-! ## §1  Unsorted polynomial expansion of `L_m` on creation words -/

/-- `L_m (L₋w|0⟩)` is a `c`-uniform polynomial combination of creation words. -/
theorem exists_polyComb_Lop (w : List ℕ) :
    ∀ m : ℤ, ∃ P : List ℕ →₀ ℂ[X], ∀ c : ℂ, Lop c m (negWordVir c w) = polyComb c P := by
  induction w with
  | nil =>
      intro m
      by_cases hm : -1 ≤ m
      · exact ⟨0, fun c => by rw [negWordVir_nil, Lop_vacuum c hm, map_zero]⟩
      · refine ⟨Finsupp.single [(-m - 2).toNat] 1, fun c => ?_⟩
        rw [polyComb_single, eval_one, one_smul, negWordVir_cons, negWordVir_nil]
        congr 2
        omega
  | cons n rest ih =>
      intro m
      obtain ⟨P1, h1⟩ := ih m
      obtain ⟨P2, h2⟩ := ih (m + (-(n : ℤ) - 2))
      let κ : ℂ[X] := if m + (-(n : ℤ) - 2) = 0 then Polynomial.C (((m : ℂ) ^ 3 - m) / 12) * X else 0
      refine ⟨P1.mapDomain (n :: ·) + Polynomial.C ((m : ℂ) - ((-(n : ℤ) - 2 : ℤ) : ℂ)) • P2 +
        Finsupp.single rest κ, fun c => ?_⟩
      have hκ : κ.eval c = (if m + (-(n : ℤ) - 2) = 0 then ((m : ℂ) ^ 3 - m) / 12 * c else 0) := by
        simp only [κ]; split_ifs <;> simp
      rw [negWordVir_cons, Lop_apply_bracket, h1, h2, Lop_polyComb, map_add, map_add,
        polyComb_smul, polyComb_single, eval_C, hκ]

/-! ## §2  `c`-uniform sorting -/

/-- `P` is supported on sorted words of energy `N`. -/
def SortedSupp (N : ℕ) (P : List ℕ →₀ ℂ[X]) : Prop :=
  ∀ u ∈ P.support, SortedWord u ∧ energyVir u = N

theorem sortedSupp_single {N : ℕ} {u : List ℕ} (hu : SortedWord u) (he : energyVir u = N)
    (p : ℂ[X]) : SortedSupp N (Finsupp.single u p) := by
  intro v hv
  rw [Finsupp.mem_support_iff, Finsupp.single_apply] at hv
  split_ifs at hv with h
  · exact h ▸ ⟨hu, he⟩
  · exact absurd rfl hv

theorem sortedSupp_add {N : ℕ} {P Q : List ℕ →₀ ℂ[X]} (hP : SortedSupp N P)
    (hQ : SortedSupp N Q) : SortedSupp N (P + Q) := fun u hu =>
  (Finset.mem_union.mp (Finsupp.support_add hu)).elim (hP u) (hQ u)

theorem sortedSupp_smul {N : ℕ} (q : ℂ[X]) {P : List ℕ →₀ ℂ[X]} (hP : SortedSupp N P) :
    SortedSupp N (q • P) := fun u hu => hP u (Finsupp.support_smul hu)

theorem sortedSupp_sum {N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → List ℕ →₀ ℂ[X])
    (hf : ∀ i ∈ s, SortedSupp N (f i)) : SortedSupp N (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro u hu; simp at hu
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact sortedSupp_add (hf a (Finset.mem_insert_self a s))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Stability: if every sorted word of energy `M` has a uniform sorted expansion after one more
creation mode, then so does every uniform sorted combination of energy `M`. -/
theorem stable {M : ℕ}
    (H : ∀ u : List ℕ, SortedWord u → energyVir u = M → ∀ j : ℕ, ∃ Q, SortedSupp (M + j + 2) Q ∧
      ∀ c : ℂ, Lop c (-(j : ℤ) - 2) (negWordVir c u) = polyComb c Q)
    (j : ℕ) (P : List ℕ →₀ ℂ[X]) (hP : SortedSupp M P) :
    ∃ Q, SortedSupp (M + j + 2) Q ∧
      ∀ c : ℂ, Lop c (-(j : ℤ) - 2) (polyComb c P) = polyComb c Q := by
  classical
  have hch : ∀ u : P.support, ∃ Q, SortedSupp (M + j + 2) Q ∧
      ∀ c : ℂ, Lop c (-(j : ℤ) - 2) (negWordVir c u.1) = polyComb c Q := fun u =>
    H u.1 (hP u.1 u.2).1 (hP u.1 u.2).2 j
  choose Q hQ hQeq using hch
  refine ⟨∑ u ∈ P.support.attach, P u.1 • Q u, sortedSupp_sum _ _ fun u _ =>
    sortedSupp_smul _ (hQ u), fun c => ?_⟩
  rw [polyComb_eq_sum, map_sum, map_sum, ← Finset.sum_attach]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [map_smul, hQeq u c, polyComb_smul]

/-- The insertion lemma, `c`-uniformly (the analogue of `Lop_sorted_insert`). -/
theorem sorted_insert (N : ℕ) :
    ∀ w : List ℕ, SortedWord w → energyVir w = N → ∀ n : ℕ, ∃ Q, SortedSupp (N + n + 2) Q ∧
      ∀ c : ℂ, Lop c (-(n : ℤ) - 2) (negWordVir c w) = polyComb c Q := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro w hsort hw n
    match w with
    | [] =>
        have hN : N = 0 := by rw [← hw]; rfl
        subst hN
        refine ⟨Finsupp.single [n] 1, sortedSupp_single (sortedWord_singleton n)
          (by simp only [energyVir_cons, energyVir_nil]; omega) 1, fun c => ?_⟩
        rw [polyComb_single, eval_one, one_smul]
        rfl
    | (j :: rest) =>
        have hw' : (j + 2) + energyVir rest = N := by rw [← hw, energyVir_cons]
        rcases Nat.lt_or_ge n j with hnj | hjn
        · -- swap: `n :: j :: rest = j :: n :: rest + (j - n) · (n+j+2) :: rest`
          obtain ⟨Q1, hQ1, hQ1e⟩ := ih (energyVir rest) (by omega) rest hsort.tail rfl n
          obtain ⟨Q2, hQ2, hQ2e⟩ := stable (ih (energyVir rest + n + 2) (by omega)) j Q1 hQ1
          have hsortm : SortedWord ((n + j + 2) :: rest) :=
            SortedWord.cons hsort.tail fun b hb => le_trans (hsort.head_ge b hb) (by omega)
          refine ⟨Q2 + Polynomial.C ((j : ℂ) - n) • Finsupp.single ((n + j + 2) :: rest) 1, ?_, fun c => ?_⟩
          · have hrw : energyVir rest + n + 2 + j + 2 = N + n + 2 := by omega
            rw [hrw] at hQ2
            exact sortedSupp_add hQ2 (sortedSupp_smul _ (sortedSupp_single hsortm
              (by simp only [energyVir_cons]; omega) 1))
          · have hstep : Lop c (-(n : ℤ) - 2) (negWordVir c (j :: rest))
                = negWordVir c (n :: j :: rest) := rfl
            rw [hstep, negWordVir_swap, map_add, polyComb_smul, polyComb_single, eval_C, eval_one,
              one_smul, ← hQ2e, ← hQ1e]
            rfl
        · -- already sorted
          have hs : SortedWord (n :: j :: rest) := SortedWord.cons hsort fun b hb => by
            rcases List.mem_cons.mp hb with rfl | hb'
            · exact hjn
            · exact le_trans (hsort.head_ge b hb') hjn
          refine ⟨Finsupp.single (n :: j :: rest) 1, sortedSupp_single hs
            (by simp only [energyVir_cons] at hw ⊢; omega) 1, fun c => ?_⟩
          rw [polyComb_single, eval_one, one_smul]
          rfl

/-- Every creation word is a `c`-uniform combination of sorted words of the same energy. -/
theorem exists_sorted_polyComb (w : List ℕ) :
    ∃ Q, SortedSupp (energyVir w) Q ∧ ∀ c : ℂ, negWordVir c w = polyComb c Q := by
  induction w with
  | nil =>
      exact ⟨Finsupp.single [] 1, sortedSupp_single sortedWord_nil rfl 1, fun c => by
        rw [polyComb_single, eval_one, one_smul]⟩
  | cons i rest ih =>
      obtain ⟨Q, hQ, hQe⟩ := ih
      obtain ⟨Q', hQ', hQ'e⟩ :=
        stable (fun u hu he => sorted_insert (energyVir rest) u hu he) i Q hQ
      refine ⟨Q', ?_, fun c => ?_⟩
      · have hrw : energyVir rest + i + 2 = energyVir (i :: rest) := by
          rw [energyVir_cons]; omega
        rwa [hrw] at hQ'
      · rw [negWordVir_cons, hQe c, hQ'e]

/-! ## §3  The sorted polynomial matrix of `L_m`, and its uniqueness -/

/-- Sorted support of unspecified energy. -/
def Sorted (P : List ℕ →₀ ℂ[X]) : Prop := ∀ u ∈ P.support, SortedWord u

/-- **`L_m` has a polynomial matrix in the sorted basis**: for each mode `m` and word `w` there is
one `c`-independent family `P` of polynomials, supported on sorted words, with
`L_m (L₋w|0⟩) = Σ_u P_u(c) L₋ᵤ|0⟩` at **every** central charge `c`. -/
theorem exists_sorted_polyComb_Lop (w : List ℕ) (m : ℤ) :
    ∃ P : List ℕ →₀ ℂ[X], Sorted P ∧ ∀ c : ℂ, Lop c m (negWordVir c w) = polyComb c P := by
  classical
  obtain ⟨P, hP⟩ := exists_polyComb_Lop w m
  have hch : ∀ u : P.support, ∃ Q, SortedSupp (energyVir u.1) Q ∧
      ∀ c : ℂ, negWordVir c u.1 = polyComb c Q := fun u => exists_sorted_polyComb u.1
  choose Q hQ hQe using hch
  refine ⟨∑ u ∈ P.support.attach, P u.1 • Q u, fun v hv => ?_, fun c => ?_⟩
  · obtain ⟨u, -, hu⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hv)
    exact (hQ u v (Finsupp.support_smul hu)).1
  · rw [hP c, polyComb_eq_sum, map_sum, ← Finset.sum_attach]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [polyComb_smul, ← hQe u c]

/-- **Uniqueness.** A sorted polynomial combination vanishing at every central charge is zero,
because sorted words are linearly independent at each `c` (`sortedWord_linearIndependent`). -/
theorem polyComb_eq_zero {P : List ℕ →₀ ℂ[X]} (hP : Sorted P) (h : ∀ c : ℂ, polyComb c P = 0) :
    P = 0 := by
  classical
  refine Finsupp.ext fun u => Polynomial.funext fun c => ?_
  rw [Finsupp.coe_zero, Pi.zero_apply, eval_zero]
  by_cases hu : u ∈ P.support
  · have hli := (linearIndependent_iff'.mp (sortedWord_linearIndependent c))
    let s : Finset {w : List ℕ // SortedWord w} := P.support.attach.map
      ⟨fun x => ⟨x.1, hP x.1 x.2⟩, fun x y hxy => Subtype.ext (by simpa using congrArg Subtype.val hxy)⟩
    have hsum : ∑ i ∈ s, (P i.1).eval c • negWordVir c i.1 = 0 := by
      rw [Finset.sum_map, ← h c, polyComb_eq_sum]
      exact Finset.sum_attach P.support fun u => eval c (P u) • negWordVir c u
    exact hli s (fun i => (P i.1).eval c) hsum ⟨u, hP u hu⟩
      (Finset.mem_map.mpr ⟨⟨u, hu⟩, Finset.mem_attach _ _, rfl⟩)
  · rw [Finsupp.notMem_support_iff.mp hu, eval_zero]

/-- Sorted polynomial expansions are unique. -/
theorem polyComb_injective {P Q : List ℕ →₀ ℂ[X]} (hP : Sorted P) (hQ : Sorted Q)
    (h : ∀ c : ℂ, polyComb c P = polyComb c Q) : P = Q := by
  have hPQ : Sorted (P - Q) := fun u hu =>
    (Finset.mem_union.mp (Finsupp.support_sub hu)).elim (hP u) (hQ u)
  exact sub_eq_zero.mp (polyComb_eq_zero hPQ fun c => by rw [map_sub, h c, sub_self])

end VOA.VirPoly

section AxiomAudit
#print axioms VOA.VirPoly.exists_polyComb_Lop
#print axioms VOA.VirPoly.exists_sorted_polyComb
#print axioms VOA.VirPoly.exists_sorted_polyComb_Lop
#print axioms VOA.VirPoly.polyComb_injective
end AxiomAudit
