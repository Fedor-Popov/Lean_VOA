import VOA.Huang.GenusOneWardAssembly
import VOA.Huang.GenusTwoPointSepFormalTrace

/-!
# Level-indexed two-point traces and their Ward relations

For homogeneous insertions `x ∈ P₁` (weight `α₁`) and `y ∈ P₂` (weight `α₂`),
`tauZ … n k` is the trace over the level-`n` weight space of `N` of
`Y₁(x)∘Y₂(y)`, with the modes fixed so that the middle module `Q` is met at
level `k`. Negative levels give zero. With a homogeneous state `c` inserted at
the trace boundary (`AZ`) or between the insertions (`MZ`), q-graded
cyclicity, the commutator formula and the Jacobi iterate formula give the
relations consumed by `ward_neg_one_abstract`. All traces are finite.
-/
noncomputable section
namespace VOA.Huang.GenusOneWard
open VOA Module
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

/-- The graded trace on the level-`m` weight space `N_{h+m}`. -/
def lvl (N : LWModule W) (T : Module.End ℂ N.carrier) (m : ℤ) : ℂ :=
  gradedTraceOp N.isMod T (N.h - W.centralCharge / 24 + m)

/-- The `Y₂`-mode carrying `N_{h+n}` to `Q_{h_Q+k}`. -/
def rMode (N Q : LWModule W) (α₂ : ℂ) (n k : ℤ) : ℂ := α₂ + (N.h + n) - (Q.h + k) - 1

/-- The `Y₁`-mode carrying `Q_{h_Q+k}` to `N_{h+n}`. -/
def sMode (N Q : LWModule W) (α₁ : ℂ) (n k : ℤ) : ℂ := α₁ + (Q.h + k) - (N.h + n) - 1

section Defs
variable (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
  (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)

/-- Level-indexed two-point trace. -/
def tauZ (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ : ℂ) (n k : ℤ) : ℂ :=
  lvl N ((Y₁.val (sMode N Q α₁ n k) x).comp (Y₂.val (rMode N Q α₂ n k) y)) n

/-- The two-point trace as an element of `ℂ⟦u⟧⟦t⟧`. -/
def phiH (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ : ℂ) : R2 :=
  mk2 fun n k => tauZ Y₁ Y₂ x y α₁ α₂ n k

/-- The state mode at the trace boundary. -/
def AZ (c : V) (kc : ℤ) (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ : ℂ) (p n k : ℤ) : ℂ :=
  lvl N (mode (N.isMod.YM c) p *
    ((Y₁.val (sMode N Q α₁ n k + ((kc : ℂ) - p - 1)) x).comp (Y₂.val (rMode N Q α₂ n k) y))) n

/-- The state mode between the two insertions. -/
def MZ (c : V) (kc : ℤ) (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ : ℂ) (p n k : ℤ) : ℂ :=
  lvl N ((Y₁.val (sMode N Q α₁ n k + ((kc : ℂ) - p - 1)) x).comp
    ((mode (Q.isMod.YM c) p).comp (Y₂.val (rMode N Q α₂ n k) y))) n

end Defs

/-! ## Vanishing at negative levels -/

theorem lvl_eq_zero_of_kills (N : LWModule W) (T : Module.End ℂ N.carrier) (m : ℤ)
    (h : ∀ v ∈ N.isMod.weight (N.h + m), T v = 0) : lvl N T m = 0 := by
  have h0 : lvl N T m = lvl N 0 m := by
    unfold lvl
    apply VOA.Huang.GenusTwoPoint.Separate.gradedTraceOp_congr_on_weight
    intro v hv
    rw [h v (by convert hv using 2; ring), LinearMap.zero_apply]
  rw [h0]
  unfold lvl
  have := gradedTraceOp_smul N.isMod 0 (0 : Module.End ℂ N.carrier)
  rw [zero_smul] at this
  rw [this]
  simp

theorem lvl_neg (N : LWModule W) (T : Module.End ℂ N.carrier) {m : ℤ} (hm : m < 0) :
    lvl N T m = 0 := by
  apply lvl_eq_zero_of_kills
  intro v hv
  rw [LWBottomRecovery.weight_neg_eq_bot N hm, Submodule.mem_bot] at hv
  rw [hv, map_zero]

section Vanish
variable (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
  (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
  {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}

/-- `Y₂(y)` lands in the empty weight space below the bottom of `Q`. -/
theorem Y₂_rMode_eq_zero (hy : y ∈ P₂.isMod.weight α₂) {n k : ℤ} (hk : k < 0)
    (v : N.carrier) (hv : v ∈ N.isMod.weight (N.h + n)) :
    Y₂.val (rMode N Q α₂ n k) y v = 0 := by
  have hm := FusionTop.mem_weight Y₂.property hy hv (rMode N Q α₂ n k)
  rw [show α₂ + (N.h + n) - rMode N Q α₂ n k - 1 = Q.h + (k : ℂ) by unfold rMode; ring,
    LWBottomRecovery.weight_neg_eq_bot Q hk, Submodule.mem_bot] at hm
  exact hm

theorem tauZ_neg_left (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ : ℂ) {n : ℤ} (hn : n < 0) (k : ℤ) :
    tauZ Y₁ Y₂ x y α₁ α₂ n k = 0 := lvl_neg N _ hn

theorem tauZ_neg_right (hy : y ∈ P₂.isMod.weight α₂) (x : P₁.carrier) (α₁ : ℂ) (n : ℤ)
    {k : ℤ} (hk : k < 0) : tauZ Y₁ Y₂ x y α₁ α₂ n k = 0 := by
  apply lvl_eq_zero_of_kills
  intro v hv
  rw [LinearMap.comp_apply, Y₂_rMode_eq_zero Y₂ hy hk v hv, map_zero]

theorem AZ_neg_left (c : V) (kc : ℤ) (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ : ℂ)
    (p : ℤ) {n : ℤ} (hn : n < 0) (k : ℤ) : AZ Y₁ Y₂ c kc x y α₁ α₂ p n k = 0 := lvl_neg N _ hn

theorem AZ_neg_right (hy : y ∈ P₂.isMod.weight α₂) (c : V) (kc : ℤ) (x : P₁.carrier) (α₁ : ℂ)
    (p n : ℤ) {k : ℤ} (hk : k < 0) : AZ Y₁ Y₂ c kc x y α₁ α₂ p n k = 0 := by
  apply lvl_eq_zero_of_kills
  intro v hv
  rw [Module.End.mul_apply, LinearMap.comp_apply, Y₂_rMode_eq_zero Y₂ hy hk v hv, map_zero,
    map_zero]

end Vanish

/-! ## Coefficients of shifted series -/

/-- A coefficient function vanishing at negative indices. -/
def Vanishes (f : ℤ → ℤ → ℂ) : Prop := ∀ n k, (n < 0 ∨ k < 0) → f n k = 0

/-- The series attached to an integer-indexed coefficient function. -/
def ofZ (f : ℤ → ℤ → ℂ) : R2 := mk2 fun n k => f n k

theorem c2_ofZ (f : ℤ → ℤ → ℂ) (n k : ℕ) : c2 (ofZ f) n k = f n k := by
  simp [ofZ]

theorem c2_qq_pow_ofZ {f : ℤ → ℤ → ℂ} (hf : Vanishes f) (d n k : ℕ) :
    c2 (qq ^ d * ofZ f) n k = f ((n : ℤ) - d) ((k : ℤ) - d) := by
  rw [c2_qq_pow_mul]
  split_ifs with h
  · rw [c2_ofZ]
    push_cast [h.1, h.2]
    rfl
  · rw [hf]
    omega

theorem c2_uu_pow_ofZ {f : ℤ → ℤ → ℂ} (hf : Vanishes f) (d n k : ℕ) :
    c2 (uu ^ d * ofZ f) n k = f ((n : ℤ) - d) k := by
  rw [c2_uu_pow_mul]
  split_ifs with h
  · rw [c2_ofZ]
    push_cast [h]
    rfl
  · rw [hf]
    omega

theorem c2_tt_pow_ofZ {f : ℤ → ℤ → ℂ} (hf : Vanishes f) (d n k : ℕ) :
    c2 (tt ^ d * ofZ f) n k = f n ((k : ℤ) - d) := by
  rw [c2_tt_pow_mul]
  split_ifs with h
  · rw [c2_ofZ]
    push_cast [h]
    rfl
  · rw [hf]
    omega

end VOA.Huang.GenusOneWard
