import VOA.Classification.COne.QExpWeightOneSlash

/-! # Independence of the choice of primitive root

Matching the values of the primitive-root powers gives exact equality of
the integral coefficients, including the exceptional constant term and
the coefficient-clearing scalar. Thus the complete slash predicate
transfers between any two primitive roots without an analytic hypothesis.
-/

open Complex UpperHalfPlane ModularForm
open scoped MatrixGroups

noncomputable section
namespace VOA.Classification.COne.SSHecke

theorem weightOne_root_index_zero_iff {N : ℕ} {ζ ξ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (hξ : IsPrimitiveRoot ξ N) (b b' : Fin N)
    (hb : ζ ^ b.val = ξ ^ b'.val) : b.val = 0 ↔ b'.val = 0 := by
  constructor
  · intro h
    by_contra h'
    exact hξ.pow_ne_one_of_pos_of_lt h' b'.isLt (by simpa [h] using hb.symm)
  · intro h
    by_contra h'
    exact hζ.pow_ne_one_of_pos_of_lt h' b.isLt (by simpa [h] using hb)

theorem weightOneScale_rootChange {N : ℕ} {ζ ξ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (hξ : IsPrimitiveRoot ξ N) (a b b' : Fin N)
    (hb : ζ ^ b.val = ξ ^ b'.val) : weightOneScale N ζ a b = weightOneScale N ξ a b' := by
  simp only [weightOneScale, hb, ne_eq, weightOne_root_index_zero_iff hζ hξ b b' hb]

/-- Root reindexing also respects the negative powers, represented by `N - b`. -/
theorem weightOne_root_complement {N : ℕ} (hN : 0 < N) {ζ ξ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (hξ : IsPrimitiveRoot ξ N) (b b' : Fin N)
    (hb : ζ ^ b.val = ξ ^ b'.val) : ζ ^ (N - b.val) = ξ ^ (N - b'.val) := by
  apply mul_right_cancel₀ (pow_ne_zero b.val (hζ.ne_zero hN.ne'))
  calc
    ζ ^ (N - b.val) * ζ ^ b.val = 1 := by
      rw [← pow_add, Nat.sub_add_cancel b.isLt.le, hζ.pow_eq_one]
    _ = ξ ^ (N - b'.val) * ζ ^ b.val := by
      rw [hb, ← pow_add, Nat.sub_add_cancel b'.isLt.le, hξ.pow_eq_one]

/-- Exact comparison of the existing coefficients, with no rescaling loss. -/
theorem weightOneIntegralCoeff_rootChange {N : ℕ} (hN : 0 < N) {ζ ξ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (hξ : IsPrimitiveRoot ξ N) (a b b' : Fin N)
    (hb : ζ ^ b.val = ξ ^ b'.val) (n : ℕ) :
    weightOneIntegralCoeff N ζ a b n = weightOneIntegralCoeff N ξ a b' n := by
  have hz := weightOne_root_index_zero_iff hζ hξ b b' hb
  have hc := weightOne_root_complement hN hζ hξ b b' hb
  have hd : weightOneDivisorCoeff N ζ a b n = weightOneDivisorCoeff N ξ a b' n := by
    unfold weightOneDivisorCoeff
    apply Finset.sum_congr rfl
    intro t ht
    rw [pow_mul', pow_mul', pow_mul', pow_mul', hb, hc]
  simp only [weightOneIntegralCoeff, hz, hb, hd, weightOneScale_rootChange hζ hξ a b b' hb]

theorem weightOneQSeries_rootChange {N : ℕ} (hN : 0 < N) {ζ ξ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (hξ : IsPrimitiveRoot ξ N) (a b b' : Fin N)
    (hb : ζ ^ b.val = ξ ^ b'.val) :
    weightOneQSeries N ζ a b = weightOneQSeries N ξ a b' := by
  funext τ
  unfold weightOneQSeries
  exact tsum_congr (fun n => congrArg (fun c : ℂ =>
    c * Function.Periodic.qParam (N : ℝ) τ ^ n)
      (weightOneIntegralCoeff_rootChange hN hζ hξ a b b' hb n))

theorem weightOne_root_matching_index {N : ℕ} (hN : 0 < N) {ζ ξ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (hξ : IsPrimitiveRoot ξ N) (b : Fin N) :
    ∃ b' : Fin N, ζ ^ b.val = ξ ^ b'.val := by
  letI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨m, hm, he⟩ := hξ.eq_pow_of_pow_eq_one
    (show (ζ ^ b.val) ^ N = 1 by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow])
  exact ⟨⟨m, hm⟩, he.symm⟩

/-- The full predicate, including scalar orbits under every integral matrix,
is independent of the chosen primitive root. -/
theorem weightOneSlashLaws_rootChange {N : ℕ} (hN : 0 < N) {ζ ξ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (hξ : IsPrimitiveRoot ξ N)
    (hslash : WeightOneSlashLaws N ξ) : WeightOneSlashLaws N ζ := by
  constructor
  · intro a b γ hγ
    obtain ⟨b', hb⟩ := weightOne_root_matching_index hN hζ hξ b
    rw [weightOneQSeries_rootChange hN hζ hξ a b b' hb]
    exact hslash.1 a b' γ hγ
  · intro a b γ
    obtain ⟨b', hb⟩ := weightOne_root_matching_index hN hζ hξ b
    obtain ⟨a', b'', c, hc⟩ := hslash.2 a b' γ
    obtain ⟨b''', hb'⟩ := weightOne_root_matching_index hN hξ hζ b''
    refine ⟨a', b''', c, ?_⟩
    rw [weightOneQSeries_rootChange hN hζ hξ a b b' hb, hc,
      weightOneQSeries_rootChange hN hξ hζ a' b'' b''' hb']

/-- All requested slash laws at a positive level follow from the single theta
Fourier input at that level. No restriction to positive first indices remains. -/
theorem weightOneSlashLaws_of_thetaFourier {N : ℕ} (hN : 0 < N)
    (hf : WeightOneThetaFourier N) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) :
    WeightOneSlashLaws N ζ :=
  weightOneSlashLaws_rootChange hN hζ (Complex.isPrimitiveRoot_exp N hN.ne')
    (weightOneSlashLaws_standard_of_thetaFourier hN hf)

/-- The one remaining classical analytic input at the levels used by the
classification. Nonvanishing and the logarithmic Fourier identity are exactly
those of `WeightOneThetaFourier`, with the zero torsion point excluded.
Reference: the Jacobi product and logarithmic derivative, DLMF 20.5.1 and
20.5.10, https://dlmf.nist.gov/20.5. This is an unproved Prop, not an axiom. -/
def WeightOneThetaFourier24 : Prop :=
  ∀ N : ℕ, 0 < N → 24 ∣ N → WeightOneThetaFourier N

/-- Conditional completion of the original full-level slash target. -/
theorem fullLevelWeightOneSlash24_of_thetaFourier (hf : WeightOneThetaFourier24) :
    FullLevelWeightOneSlash24 := by
  intro N hN h24 ζ hζ
  exact weightOneSlashLaws_of_thetaFourier hN (hf N hN h24) hζ

end VOA.Classification.COne.SSHecke
