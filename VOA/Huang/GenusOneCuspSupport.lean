import VOA.Huang.GenusOneCuspWeight

/-! # Support increase and finite determination for formal insertion blocks

The algebraic subtraction step of Miyamoto, math/0010180, Lemma 4.13.
These statements concern already extracted, log-free formal blocks. They do
not supply expansions or coefficient comparison for analytic blocks.
-/
namespace VOA.Huang.GenusOne.Cusp
open VOA
open scoped BigOperators

/-- Vanishing of the first `n` coefficients shifts the support by `n`. -/
theorem support_shift {S : FormalQSeries} {b : ℂ} (hS : S ∈ QSeriesAt b)
    (n : ℕ) (hz : ∀ k < n, S (b + (k : ℂ)) = 0) : S ∈ QSeriesAt (b + (n : ℂ)) := by
  intro e he
  by_cases hb : ∃ k : ℕ, e = b + (k : ℂ)
  · obtain ⟨k, rfl⟩ := hb
    by_cases hkn : k < n
    · exact hz k hkn
    · exact False.elim (he (k - n) (by rw [Nat.cast_sub (by omega)]; ring))
  · exact hS e (by simpa only [not_exists] using hb)

/-- Matching the leading term and the support gives a genuine one-step
increase of support for the difference. -/
theorem support_sub_succ {S T : FormalQSeries} {b : ℂ}
    (hS : S ∈ QSeriesAt b) (hT : T ∈ QSeriesAt b) (he : S b = T b) :
    S - T ∈ QSeriesAt (b + 1) := by
  simpa only [Nat.cast_one] using support_shift ((QSeriesAt b).sub_mem hS hT) 1
    (fun k hk => by
      have : k = 0 := by omega
      subst k
      simpa using sub_eq_zero.mpr he)

end VOA.Huang.GenusOne.Cusp

namespace VOA.Huang.GenusOne
open VOA VOA.FZ FusionTop
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {A : OrdVModule W M} {ι : Type u} [Finite ι]

/-- A nonzero leading coefficient forces a matching lowest conformal weight.
No intertwiner lifting hypothesis is needed for this spectral restriction. -/
theorem leading_weight_mem (P : ι → LWModule W)
    (hB : InsertionTopBimoduleExists A P)
    {S : M →ₗ[ℂ] FormalQSeries} {b : ℂ} (hsupp : ∀ w, S w ∈ QSeriesAt b)
    (hS : IsInsertionFormalBlock A S) {w : M} (hw : S w b ≠ 0) :
    ∃ i, (P i).h = b + W.centralCharge / 24 := by
  classical
  letI := Fintype.ofFinite ι
  obtain ⟨B⟩ := hB
  obtain ⟨T, hT, hz⟩ := insertionTopDecomposition_weighted P B
    (b + W.centralCharge / 24) (Cusp.leading S b) (Cusp.leading_kills_fzO hsupp hS)
    (fun p _ ha v => Cusp.leading_balanced hS p ha v) (Cusp.leading_conformal hsupp hS)
  by_contra hn
  push Not at hn
  apply hw
  change Cusp.leading S b w = 0
  rw [hT]
  apply Finset.sum_eq_zero
  intro i _
  rw [hz i (hn i)]
  simp

omit [Finite ι] in
/-- The actual trace family can be subtracted at the common exponent, leaving
support at least one integer step higher. -/
theorem leading_subtraction_at_weight [Fintype ι] (P : ι → LWModule W)
    (hB : InsertionTopBimoduleExists A P) (hlift : InsertionTopSurjectivity A P)
    {S : M →ₗ[ℂ] FormalQSeries} {b : ℂ} (hsupp : ∀ w, S w ∈ QSeriesAt b)
    (hS : IsInsertionFormalBlock A S) :
    ∃ Y : ∀ i, IntertwiningOperator A (P i).isMod (P i).isMod,
      (∀ i, (P i).h ≠ b + W.centralCharge / 24 → Y i = 0) ∧
      (∀ w, (∑ i, trace (Y i) w) ∈ QSeriesAt b) ∧
      ∀ w, S w - ∑ i, trace (Y i) w ∈ QSeriesAt (b + 1) := by
  classical
  obtain ⟨Y, hY, he⟩ := leading_realized_at_weight P hB hlift hsupp hS
  have htrace (w : M) : (∑ i, trace (Y i) w) ∈ QSeriesAt b := by
    apply Submodule.sum_mem
    intro i _
    by_cases hi : (P i).h = b + W.centralCharge / 24
    · have ht := trace_mem_QSeriesAt (Y i) ⟨(P i).realized, (P i).isLow⟩ w
      simpa only [hi, add_sub_cancel_right] using ht
    · rw [hY i hi]
      have hz := congrArg (fun t : M →ₗ[ℂ] FormalQSeries => t w)
        (traceLinear (A := A) (N := (P i).isMod)).map_zero
      change trace (0 : IntertwiningOperator A (P i).isMod (P i).isMod) w = 0 at hz
      rw [hz]
      exact (QSeriesAt b).zero_mem
  exact ⟨Y, hY, htrace, fun w => Cusp.support_sub_succ (hsupp w) (htrace w)
    (by simpa only [Finset.sum_apply] using he w)⟩

/-- If no allowed top weight occurs on the support progression, the entire
formal block vanishes. This does not use a choice of increasing complex exponents. -/
theorem formal_block_eq_zero_of_no_weights (P : ι → LWModule W)
    (hB : InsertionTopBimoduleExists A P)
    {S : M →ₗ[ℂ] FormalQSeries} {b : ℂ} (hsupp : ∀ w, S w ∈ QSeriesAt b)
    (hS : IsInsertionFormalBlock A S)
    (hno : ∀ (n : ℕ) i, (P i).h ≠ (b + (n : ℂ)) + W.centralCharge / 24) : S = 0 := by
  have hz (n : ℕ) : ∀ w, S w (b + (n : ℂ)) = 0 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w
      by_contra hn
      have hs : ∀ v, S v ∈ QSeriesAt (b + (n : ℂ)) :=
        fun v => Cusp.support_shift (hsupp v) n (fun k hk => ih k hk v)
      obtain ⟨i, hi⟩ := leading_weight_mem P hB hs hS hn
      exact hno n i hi
  apply LinearMap.ext
  intro w
  exact QSeriesAt.ext (hsupp w) (QSeriesAt b).zero_mem (fun n => hz n w)

/-- A bound strictly above all top weights gives a finite determining jet for
supported formal blocks. The hypothesis is an explicit real inequality. -/
theorem formal_block_eq_zero_of_initial_coefficients (P : ι → LWModule W)
    (hB : InsertionTopBimoduleExists A P) (b : ℂ) (N : ℕ)
    (hN : ∀ i, (P i).h.re < (b + (N : ℂ) + W.centralCharge / 24).re)
    {S : M →ₗ[ℂ] FormalQSeries} (hsupp : ∀ w, S w ∈ QSeriesAt b)
    (hS : IsInsertionFormalBlock A S)
    (hz : ∀ w k, k < N → S w (b + (k : ℂ)) = 0) : S = 0 := by
  apply formal_block_eq_zero_of_no_weights P hB
    (fun w => Cusp.support_shift (hsupp w) N (hz w)) hS
  intro n i he
  have hi := hN i
  have hr := congrArg Complex.re he
  simp only [Complex.add_re, Complex.natCast_re] at hi hr
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- There is a uniform finite determining jet for all supported formal blocks,
using only the finite family of top weights and the quotient bimodule. -/
theorem exists_formal_determining_jet (P : ι → LWModule W)
    (hB : InsertionTopBimoduleExists A P) (b : ℂ) :
    ∃ N : ℕ, ∀ S : M →ₗ[ℂ] FormalQSeries,
      (∀ w, S w ∈ QSeriesAt b) → IsInsertionFormalBlock A S →
      (∀ w k, k < N → S w (b + (k : ℂ)) = 0) → S = 0 := by
  classical
  letI := Fintype.ofFinite ι
  have hn (i : ι) : ∃ n : ℕ, (P i).h.re - b.re - (W.centralCharge / 24).re < n :=
    exists_nat_gt _
  choose n hn using hn
  let N := ∑ i, n i
  have hN (i : ι) : (P i).h.re < (b + (N : ℂ) + W.centralCharge / 24).re := by
    have hi : n i ≤ N := Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
    have hi' : (n i : ℝ) ≤ N := by exact_mod_cast hi
    have h := hn i
    simp only [Complex.add_re, Complex.natCast_re]
    linarith
  exact ⟨N, fun S hs hS hz => formal_block_eq_zero_of_initial_coefficients P hB b N hN hs hS hz⟩

end VOA.Huang.GenusOne
