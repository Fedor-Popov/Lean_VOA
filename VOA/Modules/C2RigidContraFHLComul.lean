import VOA.Modules.C2RigidContraFHL
import VOA.Core.InvariantFormAdjoint

/-!
# Port of `Modules/ContragredientFHLComul.lean` from `OrdVModule` to `GWModule`

Input to the McRae rigidity argument.  Statements and proofs are those of the original file, with the
structure `OrdVModule` replaced by `C2Rigid.GWModule` (graded weak modules, `L₀` possibly
non-semisimple) and the namespace `VOA` replaced by `VOA.C2Rigid`.  See
`Modules/C2RigidGraded.lean` for why this is the only change needed.
-/


open VOA VertexOperatorAlgebra
open scoped BigOperators
open Classical
open Module (End Dual)

namespace VOA.C2Rigid
variable {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **Single-step homogeneous `L₁`-bracket, vector form.**  For `u ∈ 𝒱_p`,
`L₁(u₍s₎v) = (2p−s−2)•u₍s+1₎v + (L₁u)₍s₎v + u₍s₎(L₁v)`. -/
theorem L1_smul_homog_step (W : VertexOperatorAlgebra 𝒱) {p : ℤ} {u : 𝒱} (hu : u ∈ W.grading p)
    (s : ℤ) (v : 𝒱) :
    W.L 1 (W.smul u s v)
      = ((2 * p - s - 2 : ℤ) : ℂ) • W.smul u (s + 1) v
        + W.smul (W.L 1 u) s v + W.smul u s (W.L 1 v) := by
  have hbr := L1_bracket_smul W hu s v
  rw [sub_eq_iff_eq_add] at hbr
  rw [hbr]; push_cast; abel

/-- **Single-step `adL₁(u₍s₎)` homogeneous collapse, as an operator (`End`).**
For `u ∈ 𝒱_p`, `adL₁(u₍s₎) = (2p−s−2)•u₍s+1₎ + (L₁u)₍s₎` as endomorphisms.  This is the homogeneous
collapse of `adL1_mode` (the `L₋₁`,`L₀` Virasoro tower terms are absorbed into the `u₍s+1₎` shift),
and is the u-slot single-step engine for the `e^{zL₁}` comultiplication. -/
theorem adL1_mode_homog (W : VertexOperatorAlgebra 𝒱) {p : ℤ} {u : 𝒱} (hu : u ∈ W.grading p)
    (s : ℤ) :
    adL1 W (mode (W.Y u) s)
      = ((2 * p - s - 2 : ℤ) : ℂ) • mode (W.Y u) (s + 1) + mode (W.Y (W.L 1 u)) s := by
  ext v
  show W.L 1 (W.smul u s v) - W.smul u s (W.L 1 v)
      = ((2 * p - s - 2 : ℤ) : ℂ) • W.smul u (s + 1) v + W.smul (W.L 1 u) s v
  have hbr := L1_bracket_smul W hu s v
  rw [hbr]; push_cast; ring_nf

/-- `adL1` is additive in its operator argument. -/
theorem adL1_add (W : VertexOperatorAlgebra 𝒱) (M N : Module.End ℂ 𝒱) :
    adL1 W (M + N) = adL1 W M + adL1 W N := by
  simp only [adL1, lie_add]

/-- `adL1` is ℂ-linear (scalar) in its operator argument. -/
theorem adL1_smul (W : VertexOperatorAlgebra 𝒱) (c : ℂ) (M : Module.End ℂ 𝒱) :
    adL1 W (c • M) = c • adL1 W M := by
  simp only [adL1, lie_smul]

/-- `adL1` kills `0`. -/
theorem adL1_zero (W : VertexOperatorAlgebra 𝒱) : adL1 W 0 = 0 := by
  simp only [adL1, lie_zero]

/-- `adL1` as a ℂ-linear map on `End ℂ 𝒱` (so `map_sum` etc. apply). -/
noncomputable def adL1ₗ (W : VertexOperatorAlgebra 𝒱) :
    Module.End ℂ 𝒱 →ₗ[ℂ] Module.End ℂ 𝒱 where
  toFun M := adL1 W M
  map_add' := adL1_add W
  map_smul' c M := adL1_smul W c M

@[simp] theorem adL1ₗ_apply (W : VertexOperatorAlgebra 𝒱) (M : Module.End ℂ 𝒱) :
    adL1ₗ W M = adL1 W M := rfl

/-- **The u-slot comultiplication coefficient.**  `K p s b a` is the ℂ-coefficient of the
`(L₁ᵃu)₍s+(b−a)₎` term in `adL₁ᵇ(u₍s₎)` for `u ∈ 𝒱_p`.  Defined by the Pascal-like recursion
`K p s (b+1) a = (2p−a−s−b−2)·K p s b a + K p s b (a−1)`, `K p s 0 = δ_{a,0}`. -/
noncomputable def K (p s : ℤ) : ℕ → ℕ → ℂ
  | 0, a => if a = 0 then 1 else 0
  | b + 1, 0 => ((2 * p - (s : ℤ) - (b : ℤ) - 2 : ℤ) : ℂ) * K p s b 0
  | b + 1, a + 1 =>
      ((2 * p - ((a : ℤ) + 1) - (s : ℤ) - (b : ℤ) - 2 : ℤ) : ℂ) * K p s b (a + 1) + K p s b a

/-- The coefficient `K` vanishes above the diagonal (`a > b`): `adL₁ᵇ` produces at most `b`
applications of `L₁` to `u`. -/
theorem K_vanish (p s : ℤ) : ∀ (b a : ℕ), b < a → K p s b a = 0 := by
  intro b
  induction b with
  | zero =>
      intro a ha
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      rw [K]; simp
  | succ b ih =>
      intro a ha
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      have hb : b < a' := by omega
      rw [K, ih (a' + 1) (by omega), ih a' hb]; ring

/-- **The fully-closed u-slot `adL₁`-iterate (only-`L₁` tower).**  For `u ∈ 𝒱_p`,
`adL₁ᵇ(u₍s₎) = ∑_{a≤b} K p s b a • (L₁ᵃu)₍s+(b−a)₎`, an explicit ℂ-linear combination of the
only-`L₁` u-slot tower modes `(L₁ᵃu)₍·₎` (no `L₋₁`). -/
theorem adL1_pow_mode_homog (W : VertexOperatorAlgebra 𝒱) {p : ℤ} {u : 𝒱} (hu : u ∈ W.grading p)
    (s : ℤ) (b : ℕ) :
    (adL1 W)^[b] (mode (W.Y u) s)
      = ∑ a ∈ Finset.range (b + 1), K p s b a • mode (W.Y (((W.L 1) ^ a) u)) (s + ((b - a : ℕ) : ℤ)) := by
  induction b generalizing s with
  | zero =>
      rw [Function.iterate_zero, id_eq, show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one]
      rw [show K p s 0 0 = 1 from by rw [K]; simp, one_smul]
      simp
  | succ b ih =>
      rw [Function.iterate_succ', Function.comp_apply, ih]
      -- adL1 distributes over the sum and smul (via the bundled linear map adL1ₗ)
      rw [show adL1 W (∑ a ∈ Finset.range (b + 1),
            K p s b a • mode (W.Y (((W.L 1) ^ a) u)) (s + ((b - a : ℕ) : ℤ)))
          = adL1ₗ W (∑ a ∈ Finset.range (b + 1),
            K p s b a • mode (W.Y (((W.L 1) ^ a) u)) (s + ((b - a : ℕ) : ℤ))) from rfl]
      rw [map_sum]
      simp only [adL1ₗ_apply]
      -- rewrite each summand
      have hstep : ∀ a ∈ Finset.range (b + 1),
          adL1 W (K p s b a • mode (W.Y (((W.L 1) ^ a) u)) (s + ((b - a : ℕ) : ℤ)))
            = (K p s b a * ((2 * p - (a : ℤ) - (s : ℤ) - (b : ℤ) - 2 : ℤ) : ℂ))
                • mode (W.Y (((W.L 1) ^ a) u)) (s + ((b - a : ℕ) : ℤ) + 1)
              + K p s b a • mode (W.Y (((W.L 1) ^ (a + 1)) u)) (s + ((b - a : ℕ) : ℤ)) := by
        intro a ha
        rw [Finset.mem_range, Nat.lt_succ_iff] at ha
        have hmem : ((W.L 1) ^ a) u ∈ W.grading (p - (a : ℤ)) := L_one_pow_mem W hu a
        rw [adL1_smul, adL1_mode_homog W hmem (s + ((b - a : ℕ) : ℤ))]
        rw [smul_add, smul_smul]
        -- the (L₁^a u) at next mode (first term) and L₁^{a+1} (second term)
        rw [show ((W.L 1) ^ (a + 1)) u = (W.L 1) (((W.L 1) ^ a) u) from by
          rw [pow_succ', Module.End.mul_apply]]
        congr 2
        -- coefficient equality: K * (2(p-a)-(s+(b-a))-2) = K * (2p-a-s-b-2)
        rw [show ((2 * (p - (a : ℤ)) - (s + ((b - a : ℕ) : ℤ)) - 2 : ℤ) : ℂ)
            = ((2 * p - (a : ℤ) - s - (b : ℤ) - 2 : ℤ) : ℂ) from by
          congr 1; push_cast [Nat.cast_sub ha]; ring]
      rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
      -- abbreviate the uniform tower mode operator  V a = (L₁ᵃu)₍s+(b+1-a)₎  (an `End`)
      set V : ℕ → Module.End ℂ 𝒱 :=
        fun a => mode (W.Y (((W.L 1) ^ a) u)) (s + ((b + 1 - a : ℕ) : ℤ)) with hV
      -- First sum:  ∑_{a≤b} (K(b,a)·c_a)·(L₁ᵃu)₍s+(b-a)+1₎ = ∑_{a≤b} (K(b,a)·c_a)·V a
      have hSum1 : ∑ a ∈ Finset.range (b + 1),
            (K p s b a * ((2 * p - (a : ℤ) - (s : ℤ) - (b : ℤ) - 2 : ℤ) : ℂ))
              • mode (W.Y (((W.L 1) ^ a) u)) (s + ((b - a : ℕ) : ℤ) + 1)
          = ∑ a ∈ Finset.range (b + 1),
            (K p s b a * ((2 * p - (a : ℤ) - (s : ℤ) - (b : ℤ) - 2 : ℤ) : ℂ)) • V a := by
        refine Finset.sum_congr rfl (fun a ha => ?_)
        rw [Finset.mem_range, Nat.lt_succ_iff] at ha
        rw [hV]; congr 2
        push_cast [Nat.cast_sub ha, Nat.cast_sub (by omega : a ≤ b + 1)]; ring
      -- Second sum:  ∑_{a≤b} K(b,a)·(L₁^{a+1}u)₍s+(b-a)₎ = ∑_{a≤b} K(b,a)·V (a+1)
      have hSum2 : ∑ a ∈ Finset.range (b + 1),
            K p s b a • mode (W.Y (((W.L 1) ^ (a + 1)) u)) (s + ((b - a : ℕ) : ℤ))
          = ∑ a ∈ Finset.range (b + 1), K p s b a • V (a + 1) := by
        refine Finset.sum_congr rfl (fun a ha => ?_)
        rw [Finset.mem_range, Nat.lt_succ_iff] at ha
        rw [hV]; congr 2
        push_cast [Nat.cast_sub ha, Nat.cast_sub (by omega : a + 1 ≤ b + 1)]; ring
      rw [hSum1, hSum2]
      -- Target:  ∑_{a≤b+1} K(b+1,a)·V a.
      rw [show (∑ a ∈ Finset.range (b + 1 + 1),
            K p s (b + 1) a • mode (W.Y (((W.L 1) ^ a) u)) (s + ((b + 1 - a : ℕ) : ℤ)))
          = ∑ a ∈ Finset.range (b + 2), K p s (b + 1) a • V a from rfl]
      -- Pad the FIRST LHS sum from range(b+1) to range(b+2): the extra a=b+1 term is 0
      -- since K(b, b+1)=0 (`K_vanish`).
      have hpad1 : ∑ a ∈ Finset.range (b + 1),
            (K p s b a * ((2 * p - (a : ℤ) - (s : ℤ) - (b : ℤ) - 2 : ℤ) : ℂ)) • V a
          = ∑ a ∈ Finset.range (b + 2),
            (K p s b a * ((2 * p - (a : ℤ) - (s : ℤ) - (b : ℤ) - 2 : ℤ) : ℂ)) • V a := by
        rw [show b + 2 = (b + 1) + 1 from rfl,
          Finset.sum_range_succ (fun a =>
            (K p s b a * ((2 * p - (a : ℤ) - (s : ℤ) - (b : ℤ) - 2 : ℤ) : ℂ)) • V a) (b + 1)]
        rw [K_vanish p s b (b + 1) (by omega)]; simp
      -- Reindex the SECOND LHS sum (∑_{a≤b} K(b,a)·V(a+1)) to a sum over range(b+2) at index a:
      -- ∑_{a∈[1,b+1]} K(b,a-1)·V a, padded with a=0 term K(b,-1):=0.
      have hpad2 : ∑ a ∈ Finset.range (b + 1), K p s b a • V (a + 1)
          = ∑ a ∈ Finset.range (b + 2), (if a = 0 then (0 : ℂ) else K p s b (a - 1)) • V a := by
        rw [show b + 2 = (b + 1) + 1 from rfl]
        rw [Finset.sum_range_succ' (fun a => (if a = 0 then (0 : ℂ) else K p s b (a - 1)) • V a) (b + 1)]
        simp only [Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero _), if_pos]
        simp
      rw [hpad1, hpad2, ← Finset.sum_add_distrib]
      -- Now both sides are sums over range(b+2); match coefficients termwise.
      refine Finset.sum_congr rfl (fun a ha => ?_)
      rw [Finset.mem_range] at ha
      rw [← add_smul]
      congr 1
      -- coefficient: (K(b,a)·c_a) + (a=0 ? 0 : K(b,a-1)) = K(b+1,a)
      rcases Nat.eq_zero_or_pos a with rfl | hapos
      · -- a = 0:  K(b,0)·c_0 + 0 = K(b+1,0) = c_0·K(b,0)
        simp only [if_true, add_zero]
        rw [show K p s (b + 1) 0
              = ((2 * p - (0 : ℤ) - (s : ℤ) - (b : ℤ) - 2 : ℤ) : ℂ) * K p s b 0 from by
          rw [K]; push_cast; ring]
        push_cast; ring
      · -- a = a'+1:  K(b,a)·c_a + K(b,a-1) = K(b+1,a)
        obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
        rw [if_neg (Nat.succ_ne_zero _)]
        rw [show a' + 1 - 1 = a' from by omega]
        rw [show K p s (b + 1) (a' + 1)
              = ((2 * p - ((a' : ℤ) + 1) - (s : ℤ) - (b : ℤ) - 2 : ℤ) : ℂ) * K p s b (a' + 1)
                + K p s b a' from by rw [K]]
        push_cast; ring

/-- **The `e^{zL₁}`-comultiplication of a mode product, closed in the only-`L₁` double tower.**
For `u ∈ 𝒱_p`, `L₁ᵗ(u₍s₎v)` is the explicit ℂ-linear combination of the two-sided only-`L₁` tower
modes `(L₁ᵃu)₍s+(b−a)₎(L₁^{t−b}v)`:
`L₁ᵗ(u₍s₎v) = ∑_{b≤t} ∑_{a≤b} C(t,b)·K p s b a • (L₁ᵃu)₍s+(b−a)₎(L₁^{t−b}v)`.
(`L1_pow_smul` (binomial/Hadamard iterate, v-slot) ∘ `adL1_pow_mode_homog` (u-slot homogeneous
collapse).  No `L₋₁` appears.) -/
theorem L1pow_smul_comul (W : VertexOperatorAlgebra 𝒱) {p : ℤ} {u : 𝒱} (hu : u ∈ W.grading p)
    (v : 𝒱) (s : ℤ) (t : ℕ) :
    ((W.L 1) ^ t) (W.smul u s v)
      = ∑ b ∈ Finset.range (t + 1), ∑ a ∈ Finset.range (b + 1),
          ((t.choose b : ℂ) * K p s b a)
            • W.smul (((W.L 1) ^ a) u) (s + ((b - a : ℕ) : ℤ)) (((W.L 1) ^ (t - b)) v) := by
  -- v-slot binomial iterate (Hadamard form)
  rw [L1_pow_smul W u s v t]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  -- u-slot homogeneous collapse of `adL1^b (u₍s₎)`
  rw [show ((adL1 W)^[b] (mode (W.Y u) s)) (((W.L 1) ^ (t - b)) v)
        = (∑ a ∈ Finset.range (b + 1),
            K p s b a • mode (W.Y (((W.L 1) ^ a) u)) (s + ((b - a : ℕ) : ℤ)))
              (((W.L 1) ^ (t - b)) v) from by rw [adL1_pow_mode_homog W hu s b]]
  -- evaluate the operator-sum at the vector `(L₁^{t-b} v)`
  rw [LinearMap.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [LinearMap.smul_apply, smul_smul]
  rfl

end VOA.C2Rigid