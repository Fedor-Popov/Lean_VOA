import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeSupport

/-! Uniform color straightening for the actual whole normalized cube orbit.
The lower part is a linear subspace, not an asserted ideal. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
noncomputable section
variable (K : Type*) [CommRing K]

def chainTerm (r a b c : ℕ) : P8 K :=
  (towerCoeff r a b c : P8 K) * MvPolynomial.X 0^(r-a) *
    MvPolynomial.X 1^(a-b) * MvPolynomial.X 3^(b-c) * MvPolynomial.X 7^c

def colorLow (L : ℕ) : Submodule K (P8 K) :=
  Finsupp.supported K K {d | energy d < L}

theorem embed_chain_projection (r a b c : ℕ)
    (ha : a ≤ r) (hb : b ≤ a) (hc : c ≤ b) :
    chainEmbed K (chainProj K (orbit K r a b c)) = chainTerm K r a b c := by
  rw [chain_projection_formula K r a b c ha hb hc]
  simp [chainEmbed,chainIndex,chainTerm]

theorem orbit_sub_chainTerm_energy (r a b c : ℕ)
    (ha : a ≤ r) (hb : b ≤ a) (hc : c ≤ b) (d : Fin 8 →₀ ℕ)
    (hd : MvPolynomial.coeff d (orbit K r a b c - chainTerm K r a b c) ≠ 0) :
    energy d < a + 3*b + 5*c := by
  apply orbit_remainder_energy K r a b c d
  simpa only [remainder,embed_chain_projection K r a b c ha hb hc] using hd

/-- Every order gives a genuine strict color-filtration reduction. -/
theorem orbit_sub_chainTerm_mem (r a b c : ℕ)
    (ha : a ≤ r) (hb : b ≤ a) (hc : c ≤ b) :
    orbit K r a b c - chainTerm K r a b c ∈ colorLow K (a + 3*b + 5*c) := by
  change (↑(orbit K r a b c - chainTerm K r a b c).support : Set (Fin 8 →₀ ℕ)) ⊆
    {d | energy d < a + 3*b + 5*c}
  intro d hd
  exact orbit_sub_chainTerm_energy K r a b c ha hb hc d
    (MvPolynomial.mem_support_iff.mp hd)

theorem chainTerm_ne_zero [CharZero K] (r a b c : ℕ)
    (ha : a ≤ r) (hb : b ≤ a) (hc : c ≤ b) : chainTerm K r a b c ≠ 0 := by
  intro hz
  have he := congrArg (MvPolynomial.aeval (fun _ : Fin 8 => (1:K))) hz
  simp only [chainTerm,map_mul,map_natCast,map_pow,MvPolynomial.aeval_X,
    one_pow,mul_one,map_zero] at he
  exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (towerCoeff_pos r a b c ha hb hc))) he

/-- An unconditional normalized-cube color-leading theorem at every order. -/
theorem orbit_color_leading [CharZero K] (r a b c : ℕ)
    (ha : a ≤ r) (hb : b ≤ a) (hc : c ≤ b) :
    chainTerm K r a b c ≠ 0 ∧
      orbit K r a b c - chainTerm K r a b c ∈ colorLow K (a + 3*b + 5*c) :=
  ⟨chainTerm_ne_zero K r a b c ha hb hc,orbit_sub_chainTerm_mem K r a b c ha hb hc⟩

theorem energy_add (d e : Counts) : energy (d+e) = energy d + energy e := by
  simp only [energy,Pi.add_apply]
  omega

end
#print axioms orbit_color_leading
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
