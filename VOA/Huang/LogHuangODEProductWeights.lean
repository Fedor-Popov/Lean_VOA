import VOA.Huang.LogHuangODEModes
import VOA.Modules.LogTensorGraded
import VOA.Modules.LogModuleC1Parts

/-! Genuine generalized weight bookkeeping for product equations.
A base belongs to one integral coset and only excludes negative levels in
that coset. It makes no semisimplicity or global single-coset assertion. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogHuangODEProduct
open VOA VOA.C2Rigid VOA.LogTensor VOA.LogTensor.Pz
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- A lower base for just one integral generalized-weight coset. -/
def CosetBase (N : GWModule W M) (h : ℂ) : Prop :=
  ∀ j : ℤ, j < 0 → N.weight (h+(j : ℂ)) = ⊥

/-- Global lower truncation gives such a base below any requested weight. -/
theorem exists_cosetBase (N : GWModule W M) (α : ℂ) :
    ∃ (h : ℂ) (K : ℕ), α = h+K ∧ CosetBase N h := by
  obtain ⟨B,hB⟩ := N.boundedBelow
  let K : ℕ := Nat.ceil (α.re-B)+1
  refine ⟨α-K,K,by ring,?_⟩
  intro j hj
  by_contra hn
  have hb := hB _ hn
  have hc : α.re-B ≤ (Nat.ceil (α.re-B) : ℝ) := Nat.le_ceil _
  have hjr : (j : ℝ) < 0 := by exact_mod_cast hj
  have hK : (K : ℝ) = (Nat.ceil (α.re-B) : ℝ)+1 := by simp [K]
  simp only [Complex.add_re,Complex.sub_re,Complex.natCast_re,Complex.intCast_re] at hb
  linarith

/-- A vector below its genuine coset base vanishes. -/
theorem eq_zero_of_mem_weight_neg {N : GWModule W M} {h : ℂ}
    (hl : CosetBase N h) {x : M} {β : ℂ} (hx : x ∈ N.weight β)
    {j : ℤ} (hβ : β=h+j) (hj : j<0) : x=0 := by
  rw [hβ,hl j hj] at hx
  exact (Submodule.mem_bot ℂ).mp hx

theorem mode_eq_zero_of_le {N : GWModule W M} {h : ℂ}
    (hl : CosetBase N h) {d n : ℕ} {v : V} (hv : v ∈ W.grading (d : ℤ))
    {x : M} (hx : x ∈ N.weight (h+n)) {k : ℤ} (hk : (n : ℤ)+d ≤ k) :
    mode (N.YM v) k x=0 :=
  eq_zero_of_mem_weight_neg hl (C2Rigid.mode_mem_weight N hv hx k)
    (j := n+d-k-1) (by push_cast; ring) (by omega)

theorem mode_mem_weight_nat {N : GWModule W M} {h : ℂ} {d n : ℕ} {v : V}
    (hv : v ∈ W.grading (d : ℤ)) {x : M} (hx : x ∈ N.weight (h+n))
    {k : ℕ} (hk : k<n+d) :
    mode (N.YM v) (k : ℤ) x ∈ N.weight (h+((n+d-(k+1) : ℕ) : ℂ)) := by
  have hm := C2Rigid.mode_mem_weight N hv hx (k : ℤ)
  convert hm using 1
  congr 1
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

theorem mode_neg_one_mem_weight {N : GWModule W M} {h : ℂ} {d n : ℕ} {v : V}
    (hv : v ∈ W.grading (d : ℤ)) {x : M} (hx : x ∈ N.weight (h+n)) :
    mode (N.YM v) (-1) x ∈ N.weight (h+((n+d : ℕ) : ℂ)) := by
  have hm := C2Rigid.mode_mem_weight N hv hx (-1)
  convert hm using 1
  congr 1
  push_cast
  ring

/-- Truncation, full Jacobi and generalized weight shift; no derivative is
imposed on an individual logarithmic coefficient. -/
structure IsGradedJacobiFamily {M₁ M₂ M₃ : Type u}
    [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
    [AddCommGroup M₃] [Module ℂ M₃]
    (N₁ : GWModule W M₁) (N₂ : GWModule W M₂) (N₃ : GWModule W M₃)
    (Y : IntertwiningModes M₁ M₂ M₃) : Prop
    extends IsJacobiFamily N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule Y where
  mem_weight : ∀ {α₁ α₂ : ℂ} {x : M₁} {y : M₂}, x ∈ N₁.weight α₁ →
    y ∈ N₂.weight α₂ → ∀ n : ℂ, Y n x y ∈ N₃.weight (α₁+α₂-n-1)

/-- Every actual log coefficient has precisely the graded Jacobi properties. -/
theorem logCoefficient_isGradedJacobi {M₁ M₂ M₃ : Type u}
    [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
    [AddCommGroup M₃] [Module ℂ M₃]
    {N₁ : LogVModule W M₁} {N₂ : LogVModule W M₂} {N₃ : LogVModule W M₃}
    {Y : LogModes M₁ M₂ M₃}
    (hY : IsLogIntertwining N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule Y) (k : ℕ) :
    IsGradedJacobiFamily N₁.toGW N₂.toGW N₃.toGW (fun n => Y n k) where
  toIsJacobiFamily := LogHuangODEModes.logCoefficient_isJacobi hY k
  mem_weight := fun hx hy n => hY.mem_weight hx hy n k

/-- The actual homogeneous C1 cutoff supplies the Nat-level reduction in
any chosen genuine coset base. -/
def C1Graded (N : GWModule W M) (h : ℂ) (B : ℕ) : Prop :=
  ∀ n : ℕ, B<n → ∀ x ∈ N.weight (h+n), x ∈ Submodule.span ℂ
    {z | ∃ (d : ℕ) (v : V) (y : M), 1≤d ∧ d≤n ∧ v∈W.grading (d : ℤ) ∧
      y∈N.weight (h+((n-d : ℕ) : ℂ)) ∧ z=mode (N.YM v) (-1) y}

/-- Actual C2-cofiniteness and finite generation provide graded C1 reduction
in every lower coset base of a logarithmic module. -/
theorem exists_C1Graded (hC2 : C2Cofinite W) (N : LogVModule W M)
    (hfg : FinGen N.toWeakModule) {h : ℂ} (hl : CosetBase N.toGW h) :
    ∃ B : ℕ, C1Graded N.toGW h B := by
  obtain ⟨b,hb⟩ := ModuleC2.c1Part_generalized_cutoff hC2 N hfg
  let B : ℕ := Nat.ceil (b-h.re)+1
  refine ⟨B,?_⟩
  intro n hn x hx
  have hre : b < (h+(n : ℂ)).re := by
    have hc : b-h.re ≤ (Nat.ceil (b-h.re) : ℝ) := Nat.le_ceil _
    have hnr : (B : ℝ)<n := by exact_mod_cast hn
    simp only [Complex.add_re,Complex.natCast_re]
    dsimp [B] at hnr
    push_cast at hnr
    linarith
  have hc1 := hb (h+n) hre hx
  let S : Submodule ℂ M := Submodule.span ℂ
    {z | ∃ (d : ℕ) (v : V) (y : M), 1≤d ∧ d≤n ∧ v∈W.grading (d : ℤ) ∧
      y∈N.toGW.weight (h+((n-d : ℕ) : ℂ)) ∧ z=mode (N.YM v) (-1) y}
  change x∈S
  refine Submodule.span_induction (p := fun z _ => z∈S) ?_
    S.zero_mem (fun z t _ _ hz ht => S.add_mem hz ht)
    (fun c z _ hz => S.smul_mem c hz) hc1
  rintro z ⟨d,v,y,hd,hv,hy,rfl⟩
  change mode (N.YM v) (-1) y ∈ S
  have hd0 : 0≤d := by omega
  have hdc : (d.toNat : ℤ)=d := Int.toNat_of_nonneg hd0
  by_cases hdn : d≤(n : ℤ)
  · have hdnn : d.toNat≤n := by omega
    apply Submodule.subset_span
    refine ⟨d.toNat,v,y,by omega,hdnn,?_,?_,rfl⟩
    · simpa only [hdc] using hv
    · have hdi : (d.toNat : ℂ)=(d : ℂ) := by exact_mod_cast hdc
      change y∈N.weight (h+((n-d.toNat : ℕ) : ℂ))
      convert hy using 1
      congr 1
      rw [Nat.cast_sub hdnn,hdi]
      ring
  · have hy0 : y=0 := eq_zero_of_mem_weight_neg hl hy
      (j := (n : ℤ)-d) (by push_cast; ring) (by omega)
    rw [hy0,map_zero]
    exact S.zero_mem

end VOA.Huang.LogHuangODEProduct
