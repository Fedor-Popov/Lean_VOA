import VOA.Moonshine.MoonshineCNBorcherdsData
import Mathlib.Algebra.Lie.Sl2

/-! Real-root strings in the abstract rank-two setting. -/

noncomputable section
namespace VOA.Moonshine.ConwayNorton.BorcherdsData

variable {g : Type*} [LieRing g] [LieAlgebra ℂ g] (D : BorcherdsData g)

theorem real_sl2_triple (e f : g)
    (he : e ∈ D.weightSpace borcherdsRealRoot)
    (hf : f ∈ D.weightSpace (-borcherdsRealRoot)) (hef : D.form e f = 1) :
    IsSl2Triple (D.cartanMap (1, -1)) e f := by
  obtain ⟨hef', he', hf'⟩ := D.real_sl2_relations e f he hf hef
  refine ⟨?_, hef', ?_, ?_⟩
  · intro h
    have h0 := D.cartan_injective (h.trans D.cartanMap.map_zero.symm)
    have := congrArg Prod.fst h0
    norm_num at this
  · simpa [two_smul] using he'
  · simpa [neg_smul, two_smul] using hf'

theorem simple_cartan_weight (j : ℤ) (v : g)
    (hv : v ∈ D.weightSpace (borcherdsImaginaryRoot j)) :
    ⁅D.cartanMap (1, -1), v⁆ = (1 - (j : ℂ)) • v := by
  simpa [borcherdsImaginaryRoot, borcherdsCartanPairing, borcherdsWeightVector, sub_eq_add_neg]
    using D.cartan_action (1, -1) (borcherdsImaginaryRoot j) v hv

/-- The k-th raising operator has precisely the degree `(1+k,j-k)`. -/
theorem adReal_pow_mem (e : g) (he : e ∈ D.weightSpace borcherdsRealRoot)
    (j : ℤ) (v : g) (hv : v ∈ D.weightSpace (borcherdsImaginaryRoot j)) (k : ℕ) :
    (LieModule.toEnd ℂ g g e ^ k) v ∈ D.weightSpace (1 + (k : ℤ), j - (k : ℤ)) := by
  induction k with
  | zero => simpa [borcherdsImaginaryRoot] using hv
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, LieModule.toEnd_apply_apply]
      have h := D.bracket_weight he ih
      convert h using 1 <;>
        simp [borcherdsRealRoot, Nat.cast_add, Nat.cast_one, sub_eq_add_neg] <;> abel

/-- The real-root string terminates at the unsupported horizontal axis. -/
theorem adReal_pow_simple_vanishes (e : g) (he : e ∈ D.weightSpace borcherdsRealRoot)
    (j : ℕ) (v : g) (hv : v ∈ D.weightSpace (borcherdsImaginaryRoot (j : ℤ))) :
    (LieModule.toEnd ℂ g g e ^ j) v = 0 := by
  have h := D.adReal_pow_mem e he (j : ℤ) v hv j
  rw [sub_self, D.weight_eq_bot_of_not_supported (1 + (j : ℤ), 0)] at h
  · exact h
  · intro hs
    have hz := borcherdsRootSupport_axis hs (Or.inr rfl)
    have := congrArg Prod.fst hz
    simp only [Prod.fst_zero] at this
    omega

/-- The lowering coefficient on a real-root string, with the lowest-weight convention. -/
theorem real_lowering_string (e f : g)
    (he : e ∈ D.weightSpace borcherdsRealRoot)
    (hf : f ∈ D.weightSpace (-borcherdsRealRoot)) (hef : D.form e f = 1)
    (j : ℤ) (hj : 1 ≤ j) (v : g)
    (hv : v ∈ D.weightSpace (borcherdsImaginaryRoot j)) (k : ℕ) :
    ⁅f, (LieModule.toEnd ℂ g g e ^ (k + 1)) v⁆ =
      (((k : ℂ) + 1) * ((j : ℂ) - (k : ℂ) - 1)) •
        (LieModule.toEnd ℂ g g e ^ k) v := by
  by_cases hzero : v = 0
  · simp [hzero]
  let t := (D.real_sl2_triple e f he hf hef).symm
  have hp : t.HasPrimitiveVectorWith v ((j : ℂ) - 1) := by
    refine ⟨hzero, ?_, D.simple_lowering_vanishes j hj f v hf hv⟩
    rw [neg_lie, D.simple_cartan_weight j v hv, ← neg_smul]
    congr 1
    ring
  convert hp.lie_e_pow_succ_toEnd_f k using 1 <;> congr 1 <;> ring

/-- Before the endpoint, raising is injective on the entire imaginary simple root space. -/
theorem adReal_pow_injective (e f : g)
    (he : e ∈ D.weightSpace borcherdsRealRoot)
    (hf : f ∈ D.weightSpace (-borcherdsRealRoot)) (hef : D.form e f = 1)
    (j : ℤ) (hj : 1 ≤ j) (k : ℕ) (hk : (k : ℤ) < j) :
    Function.Injective (fun v : D.weightSpace (borcherdsImaginaryRoot j) =>
      (LieModule.toEnd ℂ g g e ^ k) (v : g)) := by
  induction k with
  | zero =>
      intro u v huv
      exact Subtype.ext (by simpa using huv)
  | succ k ih =>
      intro u v huv
      apply ih (by omega)
      have h := congrArg (fun x : g => ⁅f, x⁆) huv
      dsimp only at h
      rw [D.real_lowering_string e f he hf hef j hj u u.property k,
        D.real_lowering_string e f he hf hef j hj v v.property k] at h
      have hc : ((k : ℂ) + 1) * ((j : ℂ) - (k : ℂ) - 1) ≠ 0 := by
        apply mul_ne_zero
        · exact_mod_cast (show (k : ℤ) + 1 ≠ 0 by omega)
        · exact_mod_cast (show j - (k : ℤ) - 1 ≠ 0 by omega)
      exact (smul_right_injective g hc) h

/-- Each component of the generating space is the image of its imaginary simple root space. -/
def generatorString (e : g) (j : ℤ) (k : ℕ) : Submodule ℂ g :=
  (D.weightSpace (borcherdsImaginaryRoot j)).map (LieModule.toEnd ℂ g g e ^ k)

/-- The full generating space U consists of all real-root strings before their endpoints. -/
def genSpace (e : g) : Submodule ℂ g :=
  ⨆ (j : ℤ) (_ : 1 ≤ j) (k : ℕ) (_ : (k : ℤ) < j), D.generatorString e j k

theorem generatorString_le_weight (e : g) (he : e ∈ D.weightSpace borcherdsRealRoot)
    (j : ℤ) (k : ℕ) :
    D.generatorString e j k ≤ D.weightSpace (1 + (k : ℤ), j - (k : ℤ)) := by
  rintro _ ⟨v, hv, rfl⟩
  exact D.adReal_pow_mem e he j v hv k

def generatorStringMap (e : g) (j : ℤ) (k : ℕ) :
    D.weightSpace (borcherdsImaginaryRoot j) →ₗ[ℂ] D.generatorString e j k :=
  (((LieModule.toEnd ℂ g g e ^ k).comp
    (D.weightSpace (borcherdsImaginaryRoot j)).subtype)).codRestrict _
      (fun v => ⟨v, v.property, rfl⟩)

/-- Each string component is linearly isomorphic to its initial imaginary simple root space. -/
def generatorStringEquiv (e f : g)
    (he : e ∈ D.weightSpace borcherdsRealRoot)
    (hf : f ∈ D.weightSpace (-borcherdsRealRoot)) (hef : D.form e f = 1)
    (j : ℤ) (hj : 1 ≤ j) (k : ℕ) (hk : (k : ℤ) < j) :
    D.weightSpace (borcherdsImaginaryRoot j) ≃ₗ[ℂ] D.generatorString e j k :=
  LinearEquiv.ofBijective (D.generatorStringMap e j k) ⟨
    fun u v h => D.adReal_pow_injective e f he hf hef j hj k hk (congrArg Subtype.val h),
    fun ⟨_, v, hv, h⟩ => ⟨⟨v, hv⟩, Subtype.ext h⟩⟩

theorem genSpace_le_positive (e : g) (he : e ∈ D.weightSpace borcherdsRealRoot) :
    D.genSpace e ≤ ⨆ (γ : ℤ × ℤ) (_ : borcherdsPositiveCone γ), D.weightSpace γ := by
  apply iSup_le
  intro j
  apply iSup_le
  intro hj
  apply iSup_le
  intro k
  apply iSup_le
  intro hk
  apply le_trans (D.generatorString_le_weight e he j k)
  exact le_iSup_of_le (1 + (k : ℤ), j - (k : ℤ))
    (le_iSup_of_le (by constructor <;> omega : borcherdsPositiveCone
      (1 + (k : ℤ), j - (k : ℤ))) le_rfl)

/-- Every real-root raising power intertwines any action satisfying BD6. -/
theorem generatorStringMap_equivariant {G : Type*} [Group G] (A : D.GAction G)
    (σ : G) (e : g) (he : e ∈ D.weightSpace borcherdsRealRoot) (k : ℕ) (v : g) :
    A.action σ ((LieModule.toEnd ℂ g g e ^ k) v) =
      (LieModule.toEnd ℂ g g e ^ k) (A.action σ v) := by
  induction k with
  | zero => simp
  | succ k ih =>
      simp only [pow_succ', Module.End.mul_apply, LieModule.toEnd_apply_apply,
        A.preserves_lie, A.fixes_real σ e (Or.inl he), ih]

end VOA.Moonshine.ConwayNorton.BorcherdsData
