/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroKacLaurent

/-!
# Bootstrapping ordinary Kac roots into actual singular states

Only determinant roots at the proposed first levels are supplied. Strong
induction constructs actual nonzero singular vectors: earlier labels already
give the lower Kac products, and nonreal label separation makes every lower
Gram determinant nonzero. The first-degenerate-level theorem then applies.
This separates a possible root construction from the stronger task of writing
singular vectors explicitly.  The roots themselves are proved in
`VirasoroScreening.screening_kac_root` (`VirasoroScreeningKacRoots.lean`).
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule VirSimple Deform
open scoped Classical
set_option maxHeartbeats 1200000

/-- Roots at the proposed Kac levels suffice to construct actual singular
states on a nonreal parameter. Earlier determinants are proved nonzero
internally by induction and exact degree exhaustion, not assumed. -/
theorem verma_singular_of_nonreal_kac_roots (t : ℂ) (ht : t.im ≠ 0) (N : ℕ)
    (hroots : ∀ r s : ℕ, 0 < r → 0 < s → r*s ≤ N →
      (vermaGramMatrix (vermaBSACharge t) (fusionKacWeight r s t) (r*s)).det = 0) :
    ∀ r s : ℕ, 0 < r → 0 < s → r*s ≤ N →
      ∃ v : sortedSpan (vermaBSACharge t) (fusionKacWeight r s t) (r*s),
        v ≠ 0 ∧ vermaMode (vermaBSACharge t) (fusionKacWeight r s t) 1 v = 0 ∧
          vermaMode (vermaBSACharge t) (fusionKacWeight r s t) 2 v = 0 := by
  have aux : ∀ n : ℕ, n ≤ N → ∀ r s : ℕ, 0 < r → 0 < s → r*s = n →
      ∃ v : sortedSpan (vermaBSACharge t) (fusionKacWeight r s t) (r*s),
        v ≠ 0 ∧ vermaMode (vermaBSACharge t) (fusionKacWeight r s t) 1 v = 0 ∧
          vermaMode (vermaBSACharge t) (fusionKacWeight r s t) 2 v = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn r s hr hs hrs
      have hlower : ∀ k < r*s,
          (vermaGramMatrix (vermaBSACharge t) (fusionKacWeight r s t) k).det ≠ 0 := by
        intro k hk
        have hformula := vermaWeightDeterminant_eq_kac_of_singular
          (vermaBSACharge t) t k ht (by
            intro i hi
            have hil := (Finset.mem_filter.mp hi).2
            have hiv := ih ((i.1.val+1)*(i.2.val+1)) (by omega) (by omega)
              (i.1.val+1) (i.2.val+1) (by omega) (by omega) rfl
            have hw : fusionKacWeight (i.1.val+1:ℕ) (i.2.val+1:ℕ) t =
                fusionKacWeight ((i.1.val:ℂ)+1) ((i.2.val:ℂ)+1) t := by
              simp only [Nat.cast_add,Nat.cast_one]
            let S : ℂ → Prop := fun h => ∃ v : sortedSpan (vermaBSACharge t) h
              ((i.1.val+1)*(i.2.val+1)), v ≠ 0 ∧
              vermaMode (vermaBSACharge t) h 1 v = 0 ∧
              vermaMode (vermaBSACharge t) h 2 v = 0
            exact Eq.mp (congrArg S hw) hiv)
        rw [← vermaWeightDeterminant_eval,hformula,Polynomial.eval_mul,Polynomial.eval_C]
        apply mul_ne_zero
        · exact Finset.prod_ne_zero_iff.mpr (fun w _ => vermaDiagonalContraction_ne_zero w.val)
        · simp only [kacWeightProduct,Polynomial.eval_prod,Polynomial.eval_pow,
            Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
          apply Finset.prod_ne_zero_iff.mpr
          intro i hi
          apply pow_ne_zero
          apply sub_ne_zero.mpr
          intro he
          have he' : fusionKacWeight r s t =
              fusionKacWeight (i.1.val+1:ℕ) (i.2.val+1:ℕ) t := by
            simpa only [Nat.cast_add,Nat.cast_one] using he
          obtain ⟨hri,hsi⟩ := fusionKacWeight_injective_positive t ht r s
            (i.1.val+1) (i.2.val+1) hr (by omega) he'
          have hil := (Finset.mem_filter.mp hi).2
          have hle : r*s ≤ k := by rw [hri,hsi]; exact hil
          omega
      obtain ⟨v,hv,hlev,hpos⟩ := verma_singular_of_first_gram_root
        (vermaBSACharge t) (fusionKacWeight r s t) (r*s)
        (hroots r s hr hs (by omega)) hlower
      exact ⟨⟨v,hlev⟩,(fun hz => hv (congrArg Subtype.val hz)),hpos 1 (by norm_num),
        hpos 2 (by norm_num)⟩
  intro r s hr hs hrs
  exact aux (r*s) hrs r s hr hs rfl

/-- Infinitely many distinct nonzero sample roots for each positive Kac
label suffice for minimal-model rigidity. Laurent interpolation, singular
construction, Kac degree exhaustion and the vacuum transfer are all internal.
The infinite root families themselves are NOT constructed here; isolated
collision parameters cannot satisfy this hypothesis. -/
theorem minimal_rigidity_of_infinite_kac_roots (p q : ℕ) (hp : 2 ≤ p)
    (hq : 2 ≤ q) (hcop : p.Coprime q)
    (hroots : ∀ r s : ℕ, 0 < r → 0 < s → r*s ≤ (p-1)*(q-1) →
      ∃ S : Set ℂ, S.Infinite ∧ (∀ t ∈ S, t ≠ 0) ∧
        ∀ t ∈ S, (vermaGramMatrix (vermaBSACharge t)
          (fusionKacWeight r s t) (r*s)).det = 0) :
    IsRigidGraded (virasoroSimple (minimalCentralCharge p q)) := by
  apply minimal_graded_rigidity_of_kac_singular p q hp hq hcop
  intro t ht
  apply verma_singular_of_nonreal_kac_roots t ht ((p-1)*(q-1))
  intro r s hr hs hrs
  obtain ⟨S,hS,hne,hzero⟩ := hroots r s hr hs hrs
  exact kacGram_root_of_infinite r s (r*s) S hS hne hzero t
    (by intro he; apply ht; simp [he])

end VOA.InverseDS.VirasoroVerma
