import VOA.Huang.LogGenusOneTracePolynomials
import VOA.Modularity.GradedTrace

/-! Honest q-graded trace calculus on actual generalized modules.
Cross-weight cyclicity and the terminating geometric recurrence use the genuine
finite generalized blocks and lower bound, with no ordinary-module premise. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogGenusOne
open VOA
open Module (End)
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- The literal diagonal block of an arbitrary actual operator. -/
def weightDiagonal (N : LogVModule W M) (A : End ℂ M) (b : ℂ) : End ℂ (N.weight b) :=
  (internalProjTo N.isInternal b).comp (A.comp (N.weight b).subtype)

@[simp] theorem weightDiagonal_add (N : LogVModule W M) (A B : End ℂ M) (b : ℂ) :
    weightDiagonal N (A+B) b=weightDiagonal N A b+weightDiagonal N B b := by
  ext y
  simp [weightDiagonal]

@[simp] theorem weightDiagonal_smul (N : LogVModule W M) (s : ℂ) (A : End ℂ M) (b : ℂ) :
    weightDiagonal N (s•A) b=s•weightDiagonal N A b := by
  ext y
  simp [weightDiagonal]

/-- Honest graded trace of the actual operator on the true generalized grading. -/
def gradedTraceOp (N : LogVModule W M) (A : End ℂ M) : FormalQSeries :=
  fun e => LinearMap.trace ℂ (N.weight (e+W.centralCharge/24))
    (weightDiagonal N A (e+W.centralCharge/24))

@[simp] theorem gradedTraceOp_add (N : LogVModule W M) (A B : End ℂ M) :
    gradedTraceOp N (A+B)=gradedTraceOp N A+gradedTraceOp N B := by
  funext e
  simp [gradedTraceOp]

@[simp] theorem gradedTraceOp_smul (N : LogVModule W M) (s : ℂ) (A : End ℂ M) :
    gradedTraceOp N (s•A)=s•gradedTraceOp N A := by
  funext e
  simp [gradedTraceOp]

theorem gradedTraceOp_sub (N : LogVModule W M) (A B : End ℂ M) :
    gradedTraceOp N (A-B)=gradedTraceOp N A-gradedTraceOp N B := by
  rw [sub_eq_add_neg,← neg_one_smul ℂ B,gradedTraceOp_add,gradedTraceOp_smul]
  funext e
  simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  ring

/-- Actual generalized weight shift of a genuine operator. -/
def WeightShift (N : LogVModule W M) (A : End ℂ M) (s : ℂ) : Prop :=
  ∀ b : ℂ,∀ x∈N.weight b,A x∈N.weight (b+s)

/-- Actual blocks compose across the stated generalized weight shift. -/
theorem weightDiagonal_mul_shift (N : LogVModule W M) (A B : End ℂ M) (a b : ℂ)
    (hA : ∀ x∈N.weight b,A x∈N.weight a) (hB : ∀ x∈N.weight a,B x∈N.weight b) :
    weightDiagonal N (A*B) a=(LinearMap.restrict A hA) ∘ₗ (LinearMap.restrict B hB) := by
  apply LinearMap.ext
  intro y
  have hm := hA _ (hB _ y.2)
  change internalProjTo N.isInternal a (A (B (y : M)))=⟨A (B y),hm⟩
  exact internalProjTo_coe N.isInternal a ⟨A (B y),hm⟩

/-- True cross-weight cyclicity of the finite generalized blocks. -/
theorem trace_weightDiagonal_comm_shift (N : LogVModule W M) (A B : End ℂ M) (a b : ℂ)
    (hA : ∀ x∈N.weight b,A x∈N.weight a) (hB : ∀ x∈N.weight a,B x∈N.weight b) :
    LinearMap.trace ℂ (N.weight a) (weightDiagonal N (A*B) a)=
      LinearMap.trace ℂ (N.weight b) (weightDiagonal N (B*A) b) := by
  haveI := N.finrank a
  haveI := N.finrank b
  rw [weightDiagonal_mul_shift N A B a b hA hB,
    weightDiagonal_mul_shift N B A b a hB hA,LinearMap.trace_comp_comm']

/-- Moving a real operator around the honest trace shifts its q-degree. -/
theorem gradedTraceOp_comm_shift (N : LogVModule W M) (A B : End ℂ M) (s : ℂ)
    (hA : WeightShift N A (-s)) (hB : WeightShift N B s) (e : ℂ) :
    gradedTraceOp N (A*B) e=gradedTraceOp N (B*A) (e+s) := by
  have hB' : ∀ x∈N.weight (e+W.centralCharge/24),B x∈N.weight (e+s+W.centralCharge/24) := by
    intro x hx
    have he := hB _ x hx
    rwa [show e+W.centralCharge/24+s=e+s+W.centralCharge/24 by ring] at he
  have hA' : ∀ x∈N.weight (e+s+W.centralCharge/24),A x∈N.weight (e+W.centralCharge/24) := by
    intro x hx
    have he := hA _ x hx
    rwa [show e+s+W.centralCharge/24+ -s=e+W.centralCharge/24 by ring] at he
  exact trace_weightDiagonal_comm_shift N A B _ _ hA' hB'

/-- The genuine commutator produces the actual coefficient recurrence. -/
theorem gradedTraceOp_commutator_step (N : LogVModule W M) (A B : End ℂ M) (s : ℂ)
    (hA : WeightShift N A (-s)) (hB : WeightShift N B s) (e : ℂ) :
    gradedTraceOp N (B*A) (e+s)=gradedTraceOp N (B*A) e+gradedTraceOp N (A*B-B*A) e := by
  rw [gradedTraceOp_sub,Pi.sub_apply,← gradedTraceOp_comm_shift N A B s hA hB e]
  ring

/-- The actual generalized module lower bound bounds the support of every honest graded trace. -/
theorem gradedTraceOp_boundedBelow (N : LogVModule W M) (A : End ℂ M) :
    ∃ B : ℝ,∀ e : ℂ,(e+W.centralCharge/24).re < B → gradedTraceOp N A e=0 := by
  obtain ⟨B,hB⟩ := N.boundedBelow
  refine ⟨B,fun e he => ?_⟩
  have hb : N.weight (e+W.centralCharge/24)=⊥ := by
    by_contra hn
    exact absurd (hB _ hn) (not_le.mpr he)
  haveI : Subsingleton (N.weight (e+W.centralCharge/24)) := by rw [hb]; infer_instance
  change LinearMap.trace ℂ _ (weightDiagonal N A _)=0
  rw [Subsingleton.elim (weightDiagonal N A _) 0,map_zero]

/-- The genuine positive-shift geometric telescope terminates by the actual
module lower bound, so its vanishing input is proved. -/
theorem gradedTraceOp_geomSolve (N : LogVModule W M) (A B : End ℂ M) {s : ℂ}
    (hs : 0 < s.re) (hA : WeightShift N A (-s)) (hB : WeightShift N B s) (e : ℂ) :
    ∃ n : ℕ,gradedTraceOp N (B*A) e=
      ∑ j∈Finset.range n,gradedTraceOp N (A*B-B*A) (e-((j : ℂ)+1)*s) := by
  obtain ⟨Bd,hBd⟩ := gradedTraceOp_boundedBelow N (B*A)
  obtain ⟨n,hn⟩ := exists_nat_gt ((e.re+(W.centralCharge/24).re-Bd)/s.re)
  have hv : gradedTraceOp N (B*A) (e-(n : ℂ)*s)=0 := by
    apply hBd
    have hlt := (div_lt_iff₀ hs).mp hn
    simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.natCast_re,
      Complex.natCast_im,zero_mul,sub_zero]
    linarith
  exact ⟨n,VOA.gradedTrace_geomSolve _ _ s (gradedTraceOp_commutator_step N A B s hA hB) e n hv⟩


/-- The trace of the actual diagonal is linear in the operator. -/
def gradedTraceAt (N : LogVModule W M) (e : ℂ) : End ℂ M →ₗ[ℂ] ℂ where
  toFun A := gradedTraceOp N A e
  map_add' A B := congrFun (gradedTraceOp_add N A B) e
  map_smul' s A := congrFun (gradedTraceOp_smul N s A) e

@[simp] theorem gradedTraceAt_apply (N : LogVModule W M) (e : ℂ) (A : End ℂ M) :
    gradedTraceAt N e A=gradedTraceOp N A e := rfl

/-- Every actual vertex mode has its true generalized-weight shift. -/
theorem weightShift_mode (N : LogVModule W M) {d : ℤ} {v : V}
    (hv : v∈W.grading d) (n : ℤ) : WeightShift N (mode (N.YM v) n) ((d : ℂ)-n-1) := by
  intro b x hx
  have he := N.mode_mem_weight hv hx n
  rwa [show b+(d : ℂ)-n-1=b+((d : ℂ)-n-1) by ring] at he

/-- The actual VOA zero mode's diagonal block is its genuine restricted block. -/
theorem weightDiagonal_logOMod (N : LogVModule W M) (v : V) (b : ℂ) :
    weightDiagonal N (logOMod N v) b=moduleZeroModeLinear N b v := by
  apply LinearMap.ext
  intro y
  change internalProjTo N.isInternal b (logOMod N v y)=
    ⟨logOMod N v y,logOMod_mem_generalized_weight N v y.2⟩
  exact internalProjTo_coe N.isInternal b
    ⟨logOMod N v y,logOMod_mem_generalized_weight N v y.2⟩

/-- The actual scalar realization equals the genuine q-graded trace
coefficient of the actual global VOA zero mode. -/
theorem actualTrace_eq_gradedTrace (N : LogVModule W M) (v : V) (e : ℂ) :
    (actualTraceData N).logPseudoTraceOnePoint v e=
      Polynomial.C (gradedTraceOp N (logOMod N v) e) := by
  rw [actualTrace_polynomial_eq_constant,gradedTraceOp,weightDiagonal_logOMod]

/-- Actual honest VOA one-point trace coefficients, linear in the inserted state. -/
def onePoint (N : LogVModule W M) : V →ₗ[ℂ] FormalQSeries where
  toFun v := gradedTraceOp N (logOMod N v)
  map_add' v w := by rw [map_add,gradedTraceOp_add]
  map_smul' s v := by rw [map_smul,gradedTraceOp_smul]; rfl

@[simp] theorem gradedTraceOp_logOMod (N : LogVModule W M) (v : V) :
    gradedTraceOp N (logOMod N v)=onePoint N v := rfl


end VOA.Huang.LogGenusOne
