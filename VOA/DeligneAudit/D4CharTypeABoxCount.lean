import VOA.DeligneAudit.D4CharBoxConvolution
import VOA.DeligneAudit.D4CharGaussian
import VOA.DeligneAudit.LeviTypeA3GradedKS

/-! The original type-A two-box and three-box multiplicities in each exact degree. -/

namespace VOA.DeligneAudit.D4Char

open A3Sector Sl2Weyl

noncomputable section

theorem a2BoxPairs_card_degree (p q a b d : ℕ) (ha : a ≤ p) (hb : b ≤ q) :
    (a2TwoBoxKeyPairs p q a b d).card =
      A2.conv (A2.qbinomCoeff p a) (A2.qbinomCoeff q b) d := by
  unfold a2TwoBoxKeyPairs
  rw [boxDegree_card_product (a2BoxModeSet p a) (a2BoxModeSet q b)
    (fun f => (Finsupp.weight om f).2) (fun g => (Finsupp.weight om g).2)]
  congr 1
  · funext i
    exact modeBox_card_degree p a i ha
  · funext i
    exact modeBox_card_degree q b i hb

theorem a3BoxTriples_card_degree (a b c x y z d : ℕ)
    (hx : x ≤ a) (hy : y ≤ b) (hz : z ≤ c) :
    (a3ThreeBoxKeyTriples a b c x y z d).card =
      A2.conv (A2.conv (A2.qbinomCoeff a x) (A2.qbinomCoeff b y))
        (A2.qbinomCoeff c z) d := by
  unfold a3ThreeBoxKeyTriples a3ThreeBoxModeSet a3BoxDegree
  rw [boxDegree_card_product (a2BoxModeSet a x ×ˢ a2BoxModeSet b y)
    (a2BoxModeSet c z)
    (fun p => (Finsupp.weight om p.1).2 + (Finsupp.weight om p.2).2)
    (fun f => (Finsupp.weight om f).2)]
  congr 1
  · funext i
    exact a2BoxPairs_card_degree a b x y i hx hy
  · funext i
    exact modeBox_card_degree c z i hz

theorem natGaussian_complement (n k : ℕ) (hk : k ≤ n) :
    A2.qbinomCoeff n (n - k) = A2.qbinomCoeff n k := by
  funext d
  have hh := congrArg (fun p : Polynomial ℚ => p.coeff d)
    (qbinom_symm (Polynomial.X : Polynomial ℚ) n k hk)
  dsimp only at hh
  rw [A2.coeff_qbinom_X, A2.coeff_qbinom_X] at hh
  exact_mod_cast hh

theorem sum_nat_interval_add {M : Type*} [AddCommMonoid M] (a n : ℕ) (f : ℕ → M) :
    (∑ m ∈ Finset.Icc a (a + n), f m) = ∑ j ∈ Finset.range (n + 1), f (a + j) := by
  rw [show Finset.Icc a (a + n) = Finset.Ico a (a + n + 1) by ext; simp,
    Finset.sum_Ico_eq_sum_range, show a + n + 1 - a = n + 1 by omega]

/-- Type-A2 branching with the same radical counts as `a2KeyHeight`. -/
theorem gl3Hilb_eq_box_branch (p q N : ℕ) :
    A2.gl3Hilb (p + q) q 0 N =
      ∑ a ∈ Finset.range (p + 1), ∑ b ∈ Finset.range (q + 1),
        A2.conv (fun d => (a2TwoBoxKeyPairs p q a b d).card)
          (A2.gl2Hilb (q + a) b) N := by
  unfold A2.gl3Hilb
  rw [show p + q = q + p by omega, sum_nat_interval_add,
    ← Nat.range_succ_eq_Icc_zero]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have ha' : a ≤ p := by simpa using ha
  have hb' : b ≤ q := by simpa using hb
  rw [show q + p - q = p by omega, Nat.sub_zero,
    show q + p - (q + a) = p - a by omega,
    natGaussian_complement p a ha', natGaussian_complement q b hb']
  congr 1
  funext d
  exact (a2BoxPairs_card_degree p q a b d ha' hb').symm

/-- Type-A3 branching with the same three radical counts as its key filtration. -/
theorem gl4Hilb_eq_box_branch (a b c N : ℕ) :
    gl4Hilb (a + b + c) (b + c) c 0 N =
      ∑ x ∈ Finset.range (a + 1), ∑ y ∈ Finset.range (b + 1),
        ∑ z ∈ Finset.range (c + 1),
          A2.conv (fun d => (a3ThreeBoxKeyTriples a b c x y z d).card)
            (A2.gl3Hilb (b + c + x) (c + y) z) N := by
  unfold gl4Hilb
  rw [show a + b + c = (b + c) + a by omega, sum_nat_interval_add]
  apply Finset.sum_congr rfl
  intro x hx
  rw [show b + c = c + b by omega, sum_nat_interval_add]
  apply Finset.sum_congr rfl
  intro y hy
  rw [← Nat.range_succ_eq_Icc_zero]
  apply Finset.sum_congr rfl
  intro z hz
  have hx' : x ≤ a := by simpa using hx
  have hy' : y ≤ b := by simpa using hy
  have hz' : z ≤ c := by simpa using hz
  have h₁ : c + b + a - (c + b) = a := by omega
  have h₂ : c + b - c = b := by omega
  have h₃ : c + b + a - (c + b + x) = a - x := by omega
  have h₄ : c + b - (c + y) = b - y := by omega
  rw [h₁, h₂, h₃, h₄, Nat.sub_zero, natGaussian_complement a x hx',
    natGaussian_complement b y hy', natGaussian_complement c z hz']
  rw [show c + b + x = b + c + x by omega]
  congr 1
  funext d
  exact (a3BoxTriples_card_degree a b c x y z d hx' hy' hz').symm

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.a2BoxPairs_card_degree
#print axioms VOA.DeligneAudit.D4Char.a3BoxTriples_card_degree
#print axioms VOA.DeligneAudit.D4Char.natGaussian_complement
#print axioms VOA.DeligneAudit.D4Char.sum_nat_interval_add
#print axioms VOA.DeligneAudit.D4Char.gl3Hilb_eq_box_branch
#print axioms VOA.DeligneAudit.D4Char.gl4Hilb_eq_box_branch
