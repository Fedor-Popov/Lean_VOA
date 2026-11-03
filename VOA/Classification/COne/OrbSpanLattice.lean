import VOA.Classification.COne.OrbSpanFock
import VOA.Classification.COne.OrbSpanUnitary
import VOA.Classification.COne.Statement

/-! # OrbSpan: every even positive-definite lattice VOA is Virasoro-unitary

On `V_L = FockN ⊗ ℂ{L} ≅ (L →₀ FockN)` the form is the orthogonal sum of the Fock forms of
the charge sectors. On the sector `γ`, `L(n) = L^{Fock}(n) + γ(n) + δ_{n,0} ½⟨γ,γ⟩`
(`LLGen_tmul`); each piece is adjoint to its `-n` partner (`fockForm_LvirN`,
`fockForm_oscN`, real frame coordinates). Hence `latticeVirUnitary`.
-/

set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbSpan
open VOA VOA.LatGen VOA.IntegralLattice HeisenbergN
open scoped Classical

variable (L : IntegralLattice)

/-- `V_L ≅ (L →₀ FockN)`. -/
abbrev latE : LatModuleGen L ≃ₗ[ℂ] (L.carrier →₀ FockN (rank L)) :=
  TensorProduct.finsuppScalarRight ℂ ℂ (FockN (rank L)) L.carrier

def latPair (x y : LatModuleGen L) : ℂ :=
  ∑ γ ∈ (latE L x).support, fockForm (latE L x γ) (latE L y γ)

theorem latPair_eq_sum (x y : LatModuleGen L) {S : Finset L.carrier}
    (hS : (latE L x).support ⊆ S) :
    latPair L x y = ∑ γ ∈ S, fockForm (latE L x γ) (latE L y γ) := by
  apply Finset.sum_subset hS
  intro γ _ h
  rw [Finsupp.notMem_support_iff.mp h, map_zero, LinearMap.zero_apply]

/-- The Hermitian form on `V_L`. -/
def latForm : LatModuleGen L →ₗ[ℂ] LatModuleGen L →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (latPair L)
    (fun x x' y => by
      classical
      have hS : (latE L (x + x')).support ⊆ (latE L x).support ∪ (latE L x').support := by
        rw [map_add]; exact Finsupp.support_add
      rw [latPair_eq_sum L _ _ hS, latPair_eq_sum L x y Finset.subset_union_left,
        latPair_eq_sum L x' y Finset.subset_union_right, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro γ _
      rw [map_add, Finsupp.add_apply, map_add, LinearMap.add_apply])
    (fun c x y => by
      classical
      have hS : (latE L (c • x)).support ⊆ (latE L x).support := by
        rw [map_smul]; exact Finsupp.support_smul
      rw [latPair_eq_sum L _ _ hS, latPair, RingHom.id_apply, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro γ _
      rw [map_smul, Finsupp.smul_apply, map_smul, LinearMap.smul_apply])
    (fun x y y' => by
      simp only [latPair, map_add, Finsupp.add_apply, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [latPair, map_smul, Finsupp.smul_apply, LinearMap.map_smulₛₗ, Finset.smul_sum])

theorem latForm_apply (x y : LatModuleGen L) : latForm L x y = latPair L x y := rfl

theorem latForm_hermitian (x y : LatModuleGen L) :
    latForm L y x = starRingEnd ℂ (latForm L x y) := by
  classical
  rw [latForm_apply, latForm_apply,
    latPair_eq_sum L y x (Finset.subset_union_right (s₁ := (latE L x).support)),
    latPair_eq_sum L x y (Finset.subset_union_left (s₂ := (latE L y).support)), map_sum]
  exact Finset.sum_congr rfl fun γ _ => fockForm_hermitian _ _

theorem latForm_pos {x : LatModuleGen L} (hx : x ≠ 0) : 0 < (latForm L x x).re := by
  rw [latForm_apply, latPair, Complex.re_sum]
  have hne : (latE L x).support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    exact fun h => hx ((latE L).map_eq_zero_iff.mp h)
  apply Finset.sum_pos _ hne
  intro γ hγ
  exact fockForm_pos (Finsupp.mem_support_iff.mp hγ)

/-- The lattice Virasoro mode on one charge sector. -/
def latOp (γ : L.carrier) (n : ℤ) : FockN (rank L) →ₗ[ℂ] FockN (rank L) :=
  LvirN (rank L) 1 n + chargeOsc L γ n +
    (if n = 0 then ((1 / 2 : ℂ) * ((L.form γ γ : ℤ) : ℂ)) • LinearMap.id else 0)

theorem latE_latStateGen (q : FockN (rank L)) (δ γ : L.carrier) :
    latE L (latStateGen L q δ) γ = if δ = γ then q else 0 := by
  classical
  rw [latStateGen, TensorProduct.finsuppScalarRight_apply_tmul_apply, eGen,
    Finsupp.single_apply]
  split_ifs <;> simp

theorem latE_LLGen (hPos : L.PosDef) (n : ℤ) (x : LatModuleGen L) (γ : L.carrier) :
    latE L (LLGen L n x) γ = latOp L γ n (latE L x γ) := by
  classical
  have hx : x ∈ Submodule.span ℂ (Set.range (fun q : FockN (rank L) × L.carrier =>
      latStateGen L q.1 q.2)) := by rw [latStateGen_span]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨q, δ⟩, rfl⟩ := hy
    dsimp only
    rw [LLGen_tmul L hPos]
    by_cases hn : n = 0
    · rw [if_pos hn, ← latStateGen_smul_boson, map_add, map_add, Finsupp.add_apply,
        Finsupp.add_apply, latE_latStateGen, latE_latStateGen, latE_latStateGen,
        latE_latStateGen]
      by_cases hδ : δ = γ
      · subst hδ; simp [latOp, hn]
      · simp [hδ, Ne.symm hδ]
    · rw [if_neg hn, add_zero, map_add, Finsupp.add_apply, latE_latStateGen, latE_latStateGen,
        latE_latStateGen]
      by_cases hδ : δ = γ
      · subst hδ; simp [latOp, hn]
      · simp [hδ, Ne.symm hδ]
  | zero => simp
  | add y z _ _ hy hz => simp only [map_add, Finsupp.add_apply, hy, hz]
  | smul c y _ hy => simp only [map_smul, Finsupp.smul_apply, hy]

theorem fockForm_chargeOsc (γ : L.carrier) (n : ℤ) (p q : FockN (rank L)) :
    fockForm (chargeOsc L γ n p) q = fockForm p (chargeOsc L γ (-n) q) := by
  rw [chargeOsc_apply_sum, chargeOsc_apply_sum, map_sum, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, fockForm_oscN]
  congr 1
  simp [chargeCoord, Complex.conj_ofReal]

theorem fockForm_latOp (γ : L.carrier) (n : ℤ) (p q : FockN (rank L)) :
    fockForm (latOp L γ n p) q = fockForm p (latOp L γ (-n) q) := by
  simp only [latOp, LinearMap.add_apply, map_add, LinearMap.add_apply, fockForm_LvirN,
    fockForm_chargeOsc, neg_eq_zero]
  congr 1
  by_cases hn : n = 0
  · simp only [if_pos hn, LinearMap.smul_apply, LinearMap.id_apply, map_smul,
      LinearMap.map_smulₛₗ, smul_eq_mul]
    congr 1
    simp [map_div₀, map_ofNat]
  · simp [hn]

/-- `L(n)` and `L(-n)` are adjoint for the lattice form. -/
theorem latForm_LLGen (hPos : L.PosDef) (n : ℤ) (x y : LatModuleGen L) :
    latForm L (LLGen L n x) y = latForm L x (LLGen L (-n) y) := by
  classical
  rw [latForm_apply, latForm_apply,
    latPair_eq_sum L _ y (Finset.subset_union_right (s₁ := (latE L x).support)),
    latPair_eq_sum L x _ (Finset.subset_union_left (s₂ := (latE L (LLGen L n x)).support))]
  apply Finset.sum_congr rfl
  intro γ _
  rw [latE_LLGen L hPos, latE_LLGen L hPos, fockForm_latOp]

theorem latticeVOAGen_L (hEven : L.Even) (hPos : L.PosDef) (n : ℤ) :
    (latticeVOAGen L hEven hPos).L n = LLGen L n := by
  rw [VertexOperatorAlgebra.L_def]
  exact mode_YfullGen_omega_eq_LLGen L hEven hPos n

/-- **Every even positive-definite lattice VOA is Virasoro-unitary.** -/
def latticeVirUnitary (hEven : L.Even) (hPos : L.PosDef) :
    VirUnitaryForm (latticeVOAGen L hEven hPos) where
  form := latForm L
  hermitian := latForm_hermitian L
  pos _ hx := latForm_pos L hx
  adjoint n x y := by
    rw [latticeVOAGen_L, latticeVOAGen_L]
    exact latForm_LLGen L hPos n x y

end VOA.Classification.COne.OrbSpan
