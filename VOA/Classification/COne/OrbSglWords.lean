import VOA.Classification.COne.OrbSglData
import VOA.Classification.COne.OrbOddChain

/-!
# OrbSgl (7): modes of a primary on Virasoro descendants of the vacuum

For a primary `a ∈ W_h` and a Virasoro word `w` (letter `k ↔ L(-k-1)`) of weight `|w|`:

* `a₍ₘ₎ (w 𝟙) = 0` for `m ≥ |w|`;
* `a₍|w|-1₎ (w 𝟙) = γ_h(w) a`, `γ_h(k :: w) = -((h-1)(-k) - (|k :: w| - 1)) γ_h(w)`.

(Commute `a₍ₘ₎` through `L(-p)` with `L_smul_primary`.)  Hence `u₍₁₅₎ x₀ = (Σ c_w γ₉(w)) u`.
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000

noncomputable section

namespace VOA.Classification.COne.OrbSgl

open VOA VertexOperatorAlgebra VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational
  OrbC2g OrbC2h OrbC2c OrbC2e OrbC2f PlusC2 PlusC2Eval PlusUnitary

/-- The contraction coefficient. -/
def gam (h : ℤ) : List ℕ → ℚ
  | [] => 1
  | k :: w => -(((h - 1) * (-(k : ℤ)) - ((wWt (k :: w) : ℤ) - 1) : ℤ) : ℚ) * gam h w

section Generic

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)

theorem smul_L_primary {a : V} {h : ℤ} (ha : a ∈ W.grading h)
    (hp : ∀ m : ℕ, 1 ≤ m → W.L (m : ℤ) a = 0) (n k : ℤ) (y : V) :
    W.smul a k (W.L n y) = W.L n (W.smul a k y) -
      (((h - 1) * (n + 1) - k : ℤ) : ℂ) • W.smul a (n + k) y := by
  rw [OrbOdd.L_smul_primary ha hp n k y]; abel

theorem primary_word {a : V} {h : ℤ} (ha : a ∈ W.grading h)
    (hp : ∀ m : ℕ, 1 ≤ m → W.L (m : ℤ) a = 0) :
    ∀ w : List ℕ, (∀ m : ℤ, (wWt w : ℤ) ≤ m → W.smul a m (virWord W w W.vacuum) = 0) ∧
      W.smul a ((wWt w : ℤ) - 1) (virWord W w W.vacuum) = ((gam h w : ℚ) : ℂ) • a
  | [] => by
    refine ⟨fun m hm => ?_, ?_⟩
    · exact PreVertexAlgebra.smul_vacuum_nonneg _ a (by simpa [wWt] using hm)
    · simp [virWord, wWt, gam]
  | k :: w => by
    obtain ⟨h0, h1⟩ := primary_word ha hp w
    have hw : (wWt (k :: w) : ℤ) = k + 1 + wWt w := by simp [wWt]
    refine ⟨fun m hm => ?_, ?_⟩
    · rw [virWord, smul_L_primary W ha hp, h0 m (by omega), h0 _ (by omega), map_zero,
        smul_zero, sub_zero]
    · rw [virWord, smul_L_primary W ha hp, h0 _ (by omega), map_zero, zero_sub,
        show (-(k : ℤ) - 1 + ((wWt (k :: w) : ℤ) - 1)) = (wWt w : ℤ) - 1 by omega, h1,
        smul_smul, gam, ← neg_smul]
      congr 1
      push_cast
      ring

theorem primary_wordSum {a : V} {h : ℤ} (ha : a ∈ W.grading h)
    (hp : ∀ m : ℕ, 1 ≤ m → W.L (m : ℤ) a = 0) (ts : List (ℚ × List ℕ)) (N : ℕ)
    (hts : ∀ t ∈ ts, wWt t.2 = N) :
    W.smul a ((N : ℤ) - 1) (wordSum W W.vacuum ts) =
      (((ts.map fun t => t.1 * gam h t.2).sum : ℚ) : ℂ) • a := by
  induction ts with
  | nil => simp [wordSum]
  | cons t ts ih =>
    rw [wordSum, List.map_cons, List.sum_cons, PreVertexAlgebra.smul_add_right,
      PreVertexAlgebra.smul_smul_right]
    have h1 := (primary_word W ha hp t.2).2
    rw [hts t (by simp)] at h1
    rw [h1]
    change _ + W.smul a _ (wordSum W W.vacuum ts) = _
    rw [ih fun s hs => hts s (by simp [hs]), smul_smul, ← add_smul]
    push_cast
    simp [List.map_cons, List.sum_cons]

end Generic

theorem wsP_primary : ∀ m : ℕ, 1 ≤ m → (V2mPlus 4 four_ge_one).L (m : ℤ) wsP = 0 :=
  OrbOdd.L_pos_of_L1_L2 (W := V2mPlus 4 four_ge_one) wsP_L1 wsP_L2

set_option maxHeartbeats 4000000 in
theorem x0_gam_sum : (x0Words.map fun t => t.1 * gam 9 t.2).sum = 1871608842 / 5 := by
  decide +kernel

/-- `u₍₁₅₎ x₀ = (1871608842/5) u`. -/
theorem nine_smul_x0 :
    (V2mPlus 4 four_ge_one).smul weightNine 15 x0P = ((1871608842 / 5 : ℚ) : ℂ) • weightNine := by
  have h := primary_wordSum (V2mPlus 4 four_ge_one) weightNine_mem_grading
    (fun m hm => weightNine_primary (m : ℤ) (by omega)) x0Words 16 x0Words_wt
  rw [x0_gam_sum] at h
  rw [x0P, ← h]
  norm_num

end VOA.Classification.COne.OrbSgl
