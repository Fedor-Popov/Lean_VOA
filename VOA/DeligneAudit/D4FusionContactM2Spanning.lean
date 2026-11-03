import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finset.Sym
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Tactic

/-! Finite commutative-word spanning after a genuine high-word cutoff.
Any chosen representatives covering the short words up to permutation suffice;
the canonical family uses symmetric powers, with no enumeration of ordered words. -/
namespace VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

variable (K σ : Type*) [Field K]

def wordMonomial (l : List σ) : MvPolynomial σ K := (l.map MvPolynomial.X).prod

theorem wordMonomial_append (l t : List σ) :
    wordMonomial K σ (l ++ t) = wordMonomial K σ l * wordMonomial K σ t := by
  simp [wordMonomial, List.map_append, List.prod_append]

theorem wordMonomial_replicate (k : ℕ) (x : σ) :
    wordMonomial K σ (List.replicate k x) = MvPolynomial.X x ^ k := by
  simp [wordMonomial]

theorem wordMonomial_perm {l t : List σ} (h : l.Perm t) :
    wordMonomial K σ l = wordMonomial K σ t := (h.map _).prod_eq

/-- Every coefficient-one monomial is an actual product of variables. -/
theorem exists_wordMonomial (u : σ →₀ ℕ) :
    ∃ l : List σ, MvPolynomial.monomial u (1 : K) = wordMonomial K σ l := by
  classical
  refine u.induction ?_ ?_
  · exact ⟨[], rfl⟩
  · intro x k v hx hk ih
    obtain ⟨l, hl⟩ := ih
    refine ⟨l ++ List.replicate k x, ?_⟩
    rw [add_comm, MvPolynomial.monomial_add_single, hl,
      wordMonomial_append, wordMonomial_replicate]

variable {K σ} {V A : Type*} [AddCommGroup V] [Module K V]

/-- A genuine surjective polynomial map and an actual high-word vanishing
statement reduce all spanning to any chosen short-word representatives. -/
theorem bounded_word_map_span (L : MvPolynomial σ K →ₗ[K] V)
    (hsurj : Function.Surjective L) (d : ℕ) (reps : A → List σ)
    (hcover : ∀ l : List σ, l.length ≤ d → ∃ a, l.Perm (reps a))
    (hhigh : ∀ l : List σ, d + 1 ≤ l.length → L (wordMonomial K σ l) = 0) :
    Submodule.span K (Set.range fun a => L (wordMonomial K σ (reps a))) = ⊤ := by
  let P := Submodule.span K (Set.range fun a => L (wordMonomial K σ (reps a)))
  have hw : ∀ l : List σ, L (wordMonomial K σ l) ∈ P := by
    intro l
    by_cases hl : l.length ≤ d
    · obtain ⟨a, ha⟩ := hcover l hl
      rw [wordMonomial_perm K σ ha]
      exact Submodule.subset_span ⟨a, rfl⟩
    · rw [hhigh l (by omega)]
      exact P.zero_mem
  have hm : ∀ (u : σ →₀ ℕ) (c : K), L (MvPolynomial.monomial u c) ∈ P := by
    intro u c
    obtain ⟨l, hl⟩ := exists_wordMonomial K σ u
    have he : MvPolynomial.monomial u c = c • wordMonomial K σ l := by
      rw [← hl, MvPolynomial.smul_monomial]
      simp
    rw [he, map_smul]
    exact P.smul_mem c (hw l)
  apply top_unique
  intro v _
  obtain ⟨p, rfl⟩ := hsurj v
  exact MvPolynomial.induction_on' p hm (fun p q hp hq => by
    rw [map_add]
    exact P.add_mem hp hq)

/-- Finiteness is a consequence of the actual cutoff and a finite covering family. -/
theorem finite_of_bounded_word_map [Finite A] (L : MvPolynomial σ K →ₗ[K] V)
    (hsurj : Function.Surjective L) (d : ℕ) (reps : A → List σ)
    (hcover : ∀ l : List σ, l.length ≤ d → ∃ a, l.Perm (reps a))
    (hhigh : ∀ l : List σ, d + 1 ≤ l.length → L (wordMonomial K σ l) = 0) :
    FiniteDimensional K V := by
  let P := Submodule.span K (Set.range fun a => L (wordMonomial K σ (reps a)))
  letI : FiniteDimensional K P := FiniteDimensional.span_of_finite K (Set.finite_range _)
  have htop : P = ⊤ := bounded_word_map_span L hsurj d reps hcover hhigh
  apply Module.Finite.of_surjective P.subtype
  intro v
  refine ⟨⟨v, ?_⟩, rfl⟩
  rw [htop]
  exact Submodule.mem_top

/-- One symmetric power for each length from zero through d. -/
abbrev ShortSymWords (σ : Type*) (d : ℕ) := Σ n : Fin (d + 1), Sym σ n.val

def shortSymReps (d : ℕ) (s : ShortSymWords σ d) : List σ := s.2.val.toList

theorem shortSymReps_cover (d : ℕ) (l : List σ) (hl : l.length ≤ d) :
    ∃ a : ShortSymWords σ d, l.Perm (shortSymReps d a) := by
  refine ⟨⟨⟨l.length, by omega⟩, ⟨(l : Multiset σ), rfl⟩⟩, ?_⟩
  apply Multiset.coe_eq_coe.mp
  exact (Multiset.coe_toList (l : Multiset σ)).symm

/-- The cutoff alone gives a finite spanning family indexed by unordered words. -/
theorem short_sym_map_span (L : MvPolynomial σ K →ₗ[K] V)
    (hsurj : Function.Surjective L) (d : ℕ)
    (hhigh : ∀ l : List σ, d + 1 ≤ l.length → L (wordMonomial K σ l) = 0) :
    Submodule.span K (Set.range fun a : ShortSymWords σ d =>
      L (wordMonomial K σ (shortSymReps d a))) = ⊤ :=
  bounded_word_map_span L hsurj d (shortSymReps d) (shortSymReps_cover d) hhigh

theorem finite_of_high_words [Finite σ] (L : MvPolynomial σ K →ₗ[K] V)
    (hsurj : Function.Surjective L) (d : ℕ)
    (hhigh : ∀ l : List σ, d + 1 ≤ l.length → L (wordMonomial K σ l) = 0) :
    FiniteDimensional K V := by
  classical
  letI := Fintype.ofFinite σ
  exact finite_of_bounded_word_map L hsurj d (shortSymReps d) (shortSymReps_cover d) hhigh

end
end VOA.DeligneAudit.D4FusionContact.Polynomial

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.bounded_word_map_span
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.finite_of_high_words
