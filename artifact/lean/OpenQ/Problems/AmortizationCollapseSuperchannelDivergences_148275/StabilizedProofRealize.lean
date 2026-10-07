/-
Registration candidate, e002-i03. Derived from the unaccepted critic-written source
problems/amortization-collapse-for-superchannel-divergences-148275/work/critic/e002_i02/CriticRealizeE2I02.lean.
Only import and namespace tokens are renamed. The historical source header below
is retained for provenance. This port is submitted for independent review.
-/

import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofUpper
import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofSums

/-!
Critic scratch (amortization problem, e002-i02). Not part of the research record.

Pure tester realization of the reviewed note, Section 5, on the locked definitions.
Data: an invertible factor `T` of a tester `Γ = T Tᴴ` on `C ⊗ A ⊗ B`, an invertible
factor `ψ` of its marginal `τ = ψ ψᴴ`, an identification `R ≃ C ⊗ A ⊗ B` of the single
common inserted reference, and base labels that embed `C` into `R`. The joint insertion
is given by its Choi matrix (one isometric Kraus operator on the embedded subspace and a
reset on its complement), the state is pure, and for every physical superchannel the
output is the congruence `K_T J K_Tᴴ` of the comb operator with an invertible `K_T`.
-/

set_option linter.unusedSectionVars false

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofRealize

open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofDivergence
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.ProofKnown
open OpenQ.Problems.EqualWeightLowChoiRank_523ed7
  (IsCPTP amplification choiLinearEquiv ofChoiMatrix choiLinearEquiv_ofChoiMatrix
    isCPTP_iff_isChannelChoi IsChannelChoi)
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofDom OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofComb OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofTester OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofChannel OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofUpper
open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofSums
open scoped ComplexOrder Kronecker Matrix

noncomputable section

/-- Tester data for the realization. -/
structure Data (a b c r : ℕ) where
  a₀ : Fin a
  b₀ : Fin b
  k₀ : Fin (b * r)
  eR : Fin r ≃ X3 c a b
  T : Matrix (X3 c a b) (X3 c a b) ℂ
  T' : Matrix (X3 c a b) (X3 c a b) ℂ
  ψ : Matrix (Fin c) (Fin c) ℂ
  ψ' : Matrix (Fin c) (Fin c) ℂ
  hT1 : T' * T = 1
  hT2 : T * T' = 1
  hψ : ψ * ψ' = 1
  hψ' : ψ' * ψ = 1
  htr : Matrix.trace (ψ * ψᴴ) = 1
  hmarg : OpenQ.partialTraceRight (T * Tᴴ) = (ψ * ψᴴ) ⊗ₖ (1 : Matrix (Fin a) (Fin a) ℂ)

variable {a b c d r : ℕ} (D : Data a b c r)

/-- The reference label lies in the embedded copy of `C`. -/
def Data.inR (u : Fin r) : Prop := (D.eR u).1.2 = D.a₀ ∧ (D.eR u).2 = D.b₀

instance (u : Fin r) : Decidable (D.inR u) := by
  unfold Data.inR
  infer_instance

/-- Embedding `C ↪ R`. -/
def Data.emb (c' : Fin c) : Fin r := D.eR.symm ((c', D.a₀), D.b₀)

theorem Data.inR_emb (c' : Fin c) : D.inR (D.emb c') := by
  simp [Data.inR, Data.emb]

theorem Data.eR_emb (c' : Fin c) : (D.eR (D.emb c')).1.1 = c' := by
  simp [Data.emb]

theorem Data.emb_of_inR {u : Fin r} (h : D.inR u) : D.emb (D.eR u).1.1 = u := by
  apply D.eR.injective
  obtain ⟨h1, h2⟩ := h
  rw [Data.emb, Equiv.apply_symm_apply]
  ext <;> simp [h1, h2]

/-- A sum over the embedded reference labels. -/
theorem Data.sum_inR (g : Fin r → ℂ) :
    ∑ u, (if D.inR u then g u else 0) = ∑ c' : Fin c, g (D.emb c') := by
  have h1 : ∑ u, (if D.inR u then g u else 0) =
      ∑ x : X3 c a b, (if x.1.2 = D.a₀ ∧ x.2 = D.b₀ then g (D.eR.symm x) else 0) := by
    rw [← Equiv.sum_comp D.eR.symm]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Data.inR, Equiv.apply_symm_apply]
  rw [h1, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [Finset.sum_eq_single D.a₀, Finset.sum_eq_single D.b₀]
  · simp [Data.emb]
  · intro b' _ hb'
    simp [hb']
  · simp
  · intro a' _ ha'
    simp [ha']
  · simp

/-- Amplitudes of the pure input state on `C ⊗ R`. -/
def Data.phiP (c₀ : Fin c) (u : Fin r) : ℂ :=
  if D.inR u then D.ψ c₀ (D.eR u).1.1 else 0

/-- Matrix elements of the isometry `A ⊗ R → B ⊗ R` on the embedded subspace. -/
def Data.vP (a₁ : Fin a) (u : Fin r) (b₁ : Fin b) (t : Fin r) : ℂ :=
  if D.inR u then ∑ c'', D.ψ' (D.eR u).1.1 c'' * D.T ((c'', a₁), b₁) (D.eR t) else 0

/-- State and isometry contract to the tester factor. -/
theorem Data.link (c₀ : Fin c) (a₁ : Fin a) (b₁ : Fin b) (t : Fin r) :
    ∑ u, D.vP a₁ u b₁ t * D.phiP c₀ u = D.T ((c₀, a₁), b₁) (D.eR t) := by
  have h1 : ∀ u, D.vP a₁ u b₁ t * D.phiP c₀ u =
      if D.inR u then (∑ c'', D.ψ' (D.eR u).1.1 c'' * D.T ((c'', a₁), b₁) (D.eR t)) *
        D.ψ c₀ (D.eR u).1.1 else 0 := by
    intro u
    unfold Data.vP Data.phiP
    split_ifs <;> simp
  simp only [h1]
  rw [D.sum_inR (fun u => (∑ c'', D.ψ' (D.eR u).1.1 c'' * D.T ((c'', a₁), b₁) (D.eR t)) *
    D.ψ c₀ (D.eR u).1.1)]
  simp only [Data.eR_emb, Finset.sum_mul]
  rw [Finset.sum_comm]
  have h2 : ∀ c'' : Fin c, ∑ c' : Fin c, D.ψ' c' c'' * D.T ((c'', a₁), b₁) (D.eR t) * D.ψ c₀ c' =
      (D.ψ * D.ψ') c₀ c'' * D.T ((c'', a₁), b₁) (D.eR t) := by
    intro c''
    rw [Matrix.mul_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun c' _ => by ring
  simp only [h2, D.hψ, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]

/-! ### The pure input state -/

/-- Amplitude vector of the pure state on `C ⊗ R` in the flattened basis. -/
def Data.phi : Fin (c * r) → ℂ :=
  fun k => D.phiP (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

theorem Data.phi_apply (c₀ : Fin c) (u : Fin r) :
    D.phi (finProdFinEquiv (c₀, u)) = D.phiP c₀ u := by
  simp [Data.phi]

/-- The pure input state. -/
def Data.rho : Operator (Fin (c * r)) := Matrix.vecMulVec D.phi (star D.phi)

theorem Data.rho_apply (k l : Fin (c * r)) : D.rho k l = D.phi k * star (D.phi l) := rfl

theorem Data.rho_density : OpenQ.IsDensityMatrix D.rho := by
  refine ⟨Matrix.posSemidef_vecMulVec_self_star _, ?_⟩
  have h0 : Matrix.trace D.rho = ∑ k, D.phi k * star (D.phi k) := rfl
  rw [h0, sum_fin_prod]
  simp only [Data.phi_apply]
  have h1 : ∀ c₀ u, D.phiP c₀ u * star (D.phiP c₀ u) =
      if D.inR u then D.ψ c₀ (D.eR u).1.1 * star (D.ψ c₀ (D.eR u).1.1) else 0 := by
    intro c₀ u
    unfold Data.phiP
    split_ifs <;> simp
  have h2 : ∀ c₀, ∑ u, D.phiP c₀ u * star (D.phiP c₀ u) =
      ∑ c', D.ψ c₀ c' * star (D.ψ c₀ c') := by
    intro c₀
    simp only [h1]
    rw [D.sum_inR (fun u => D.ψ c₀ (D.eR u).1.1 * star (D.ψ c₀ (D.eR u).1.1))]
    simp only [Data.eR_emb]
  simp only [h2]
  have h3 := D.htr
  simpa [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply] using h3

/-! ### The joint insertion -/

/-- Gram identity of the tester factor: the `B` marginal of `T Tᴴ`. -/
theorem Data.gram (P P' : Fin c → ℂ) (a₁ a₂ : Fin a) :
    ∑ b₁ : Fin b, ∑ t : Fin r, (∑ x, P x * D.T ((x, a₁), b₁) (D.eR t)) *
        star (∑ y, P' y * D.T ((y, a₂), b₁) (D.eR t)) =
      ∑ x, ∑ y, P x * star (P' y) *
        ((D.ψ * D.ψᴴ) x y * (1 : Matrix (Fin a) (Fin a) ℂ) a₁ a₂) := by
  have hm : ∀ x y : Fin c, (D.ψ * D.ψᴴ) x y * (1 : Matrix (Fin a) (Fin a) ℂ) a₁ a₂ =
      ∑ b₁ : Fin b, ∑ t : Fin r, D.T ((x, a₁), b₁) (D.eR t) *
        star (D.T ((y, a₂), b₁) (D.eR t)) := by
    intro x y
    have h := congrFun (congrFun D.hmarg (x, a₁)) (y, a₂)
    rw [Matrix.kroneckerMap_apply] at h
    rw [← h]
    simp only [OpenQ.partialTraceRight, Matrix.mul_apply, Matrix.conjTranspose_apply]
    refine Finset.sum_congr rfl fun b₁ _ => ?_
    exact (Equiv.sum_comp D.eR (fun z => D.T ((x, a₁), b₁) z * star (D.T ((y, a₂), b₁) z))).symm
  have hL : ∀ (b₁ : Fin b) (t : Fin r), (∑ x, P x * D.T ((x, a₁), b₁) (D.eR t)) *
      star (∑ y, P' y * D.T ((y, a₂), b₁) (D.eR t)) =
      ∑ x, ∑ y, P x * star (P' y) *
        (D.T ((x, a₁), b₁) (D.eR t) * star (D.T ((y, a₂), b₁) (D.eR t))) := by
    intro b₁ t
    rw [star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [star_mul']
    ring
  have hRr : ∀ x y : Fin c, P x * star (P' y) *
      ((D.ψ * D.ψᴴ) x y * (1 : Matrix (Fin a) (Fin a) ℂ) a₁ a₂) =
      ∑ b₁ : Fin b, ∑ t : Fin r, P x * star (P' y) *
        (D.T ((x, a₁), b₁) (D.eR t) * star (D.T ((y, a₂), b₁) (D.eR t))) := by
    intro x y
    rw [hm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b₁ _ => ?_
    rw [Finset.mul_sum]
  simp only [hL, hRr]
  exact sum4_pairs _

theorem Data.psi_unit : D.ψ' * (D.ψ * D.ψᴴ) * D.ψ'ᴴ = 1 := by
  calc D.ψ' * (D.ψ * D.ψᴴ) * D.ψ'ᴴ = (D.ψ' * D.ψ) * (D.ψ' * D.ψ)ᴴ := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [D.hψ', Matrix.conjTranspose_one, Matrix.mul_one]

/-- The Kraus operator is an isometry on the embedded subspace and zero elsewhere. -/
theorem Data.iso (a₁ a₂ : Fin a) (u₁ u₂ : Fin r) :
    ∑ b₁ : Fin b, ∑ t : Fin r, D.vP a₁ u₁ b₁ t * star (D.vP a₂ u₂ b₁ t) =
      if a₁ = a₂ ∧ u₁ = u₂ ∧ D.inR u₁ then 1 else 0 := by
  by_cases h1 : D.inR u₁
  · by_cases h2 : D.inR u₂
    · have e : ∀ (b₁ : Fin b) (t : Fin r), D.vP a₁ u₁ b₁ t * star (D.vP a₂ u₂ b₁ t) =
          (∑ x, D.ψ' (D.eR u₁).1.1 x * D.T ((x, a₁), b₁) (D.eR t)) *
            star (∑ y, D.ψ' (D.eR u₂).1.1 y * D.T ((y, a₂), b₁) (D.eR t)) := by
        intro b₁ t
        simp only [Data.vP, h1, h2, ↓reduceIte]
      simp only [e]
      rw [D.gram (fun x => D.ψ' (D.eR u₁).1.1 x) (fun y => D.ψ' (D.eR u₂).1.1 y) a₁ a₂]
      have hu : (∑ x, ∑ y, D.ψ' (D.eR u₁).1.1 x * star (D.ψ' (D.eR u₂).1.1 y) *
          ((D.ψ * D.ψᴴ) x y * (1 : Matrix (Fin a) (Fin a) ℂ) a₁ a₂)) =
          (D.ψ' * (D.ψ * D.ψᴴ) * D.ψ'ᴴ) (D.eR u₁).1.1 (D.eR u₂).1.1 *
            (1 : Matrix (Fin a) (Fin a) ℂ) a₁ a₂ := by
        generalize D.ψ * D.ψᴴ = Mm
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
      rw [hu, D.psi_unit, Matrix.one_apply, Matrix.one_apply]
      by_cases ha : a₁ = a₂
      · by_cases hu' : u₁ = u₂
        · subst hu'
          simp [ha, h1]
        · have hc : (D.eR u₁).1.1 ≠ (D.eR u₂).1.1 := by
            intro hcc
            apply hu'
            rw [← D.emb_of_inR h1, ← D.emb_of_inR h2, hcc]
          simp [ha, hu', hc]
      · simp [ha]
    · have e : ∀ (b₁ : Fin b) (t : Fin r), D.vP a₁ u₁ b₁ t * star (D.vP a₂ u₂ b₁ t) = 0 := by
        intro b₁ t
        simp only [Data.vP, h2, ↓reduceIte, star_zero, mul_zero]
      have hne : ¬ (a₁ = a₂ ∧ u₁ = u₂ ∧ D.inR u₁) := by
        rintro ⟨-, hu', -⟩
        exact h2 (hu' ▸ h1)
      simp only [e, Finset.sum_const_zero, hne, ↓reduceIte]
  · have e : ∀ (b₁ : Fin b) (t : Fin r), D.vP a₁ u₁ b₁ t * star (D.vP a₂ u₂ b₁ t) = 0 := by
      intro b₁ t
      simp only [Data.vP, h1, ↓reduceIte, zero_mul]
    have hne : ¬ (a₁ = a₂ ∧ u₁ = u₂ ∧ D.inR u₁) := fun h => h1 h.2.2
    simp only [e, Finset.sum_const_zero, hne, ↓reduceIte]

/-- Kraus amplitudes in the flattened bases of `A ⊗ R` and `B ⊗ R`. -/
def Data.vK : Fin (a * r) × Fin (b * r) → ℂ := fun x =>
  D.vP (finProdFinEquiv.symm x.1).1 (finProdFinEquiv.symm x.1).2
    (finProdFinEquiv.symm x.2).1 (finProdFinEquiv.symm x.2).2

theorem Data.vK_apply (a₁ : Fin a) (u : Fin r) (b₁ : Fin b) (t : Fin r) :
    D.vK (finProdFinEquiv (a₁, u), finProdFinEquiv (b₁, t)) = D.vP a₁ u b₁ t := by
  simp [Data.vK]

/-- Reset on the complement of the embedded subspace. -/
def Data.dR : Fin (a * r) × Fin (b * r) → ℂ := fun x =>
  if D.inR (finProdFinEquiv.symm x.1).2 then 0 else if x.2 = D.k₀ then 1 else 0

/-- Choi matrix of the joint insertion. -/
def Data.JN : Matrix (Fin (a * r) × Fin (b * r)) (Fin (a * r) × Fin (b * r)) ℂ :=
  Matrix.vecMulVec D.vK (star D.vK) + Matrix.diagonal D.dR

theorem Data.JN_psd : D.JN.PosSemidef := by
  refine (Matrix.posSemidef_vecMulVec_self_star _).add (Matrix.PosSemidef.diagonal ?_)
  intro x
  unfold Data.dR
  split_ifs <;> simp

theorem Data.JN_marg : OpenQ.partialTraceRight D.JN = 1 := by
  ext i j
  obtain ⟨⟨a₁, u₁⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨a₂, u₂⟩, rfl⟩ := finProdFinEquiv.surjective j
  have h1 : OpenQ.partialTraceRight D.JN (finProdFinEquiv (a₁, u₁)) (finProdFinEquiv (a₂, u₂)) =
      (∑ k : Fin (b * r), D.vK (finProdFinEquiv (a₁, u₁), k) *
        star (D.vK (finProdFinEquiv (a₂, u₂), k))) +
      ∑ k : Fin (b * r), Matrix.diagonal D.dR (finProdFinEquiv (a₁, u₁), k)
        (finProdFinEquiv (a₂, u₂), k) := by
    simp only [OpenQ.partialTraceRight, Data.JN, Matrix.add_apply, Finset.sum_add_distrib]
    rfl
  rw [h1, sum_fin_prod]
  simp only [Data.vK_apply]
  rw [D.iso, Matrix.one_apply]
  by_cases he : a₁ = a₂ ∧ u₁ = u₂
  · obtain ⟨rfl, rfl⟩ := he
    by_cases hin : D.inR u₁
    · simp [Matrix.diagonal_apply, Data.dR, hin]
    · simp [Matrix.diagonal_apply, Data.dR, hin]
  · have hne : finProdFinEquiv (a₁, u₁) ≠ finProdFinEquiv (a₂, u₂) := by
      intro h
      apply he
      have := finProdFinEquiv.injective h
      exact Prod.mk.inj this
    have hne' : ¬ (a₁ = a₂ ∧ u₁ = u₂ ∧ D.inR u₁) := fun h => he ⟨h.1, h.2.1⟩
    simp [Matrix.diagonal_apply, hne, hne']

/-- The joint insertion as a locked channel. -/
def Data.chan : Channel (a * r) (b * r) :=
  ⟨ofChoiMatrix D.JN, (isCPTP_iff_isChannelChoi _).2
    ⟨by rw [choiLinearEquiv_ofChoiMatrix]; exact D.JN_psd,
     by rw [choiLinearEquiv_ofChoiMatrix]; exact D.JN_marg⟩⟩

theorem Data.choi_chan : choi D.chan.val = D.JN := choiLinearEquiv_ofChoiMatrix D.JN

/-! ### The output is a congruence of the comb operator -/

/-- The reset part of the insertion does not see the input state. -/
theorem Data.reset_zero (a₁ a₂ : Fin a) (u₁ u₂ : Fin r) (k l : Fin (b * r)) (c₁ c₂ : Fin c) :
    Matrix.diagonal D.dR (finProdFinEquiv (a₁, u₁), k) (finProdFinEquiv (a₂, u₂), l) *
      (D.phiP c₁ u₁ * star (D.phiP c₂ u₂)) = 0 := by
  rw [Matrix.diagonal_apply]
  split_ifs with h
  · by_cases hin : D.inR u₁
    · simp [Data.dR, hin]
    · simp [Data.phiP, hin]
  · simp

/-- The congruence matrix `K_T` from `C ⊗ A ⊗ B ⊗ D` to `D ⊗ R`. -/
def Data.KT (d : ℕ) : Matrix (Fin (d * r)) (X4 c a b d) ℂ :=
  Matrix.of fun k y =>
    if (finProdFinEquiv.symm k).1 = y.2 then D.T y.1 (D.eR (finProdFinEquiv.symm k).2) else 0

/-- Its inverse. -/
def Data.KT' (d : ℕ) : Matrix (X4 c a b d) (Fin (d * r)) ℂ :=
  Matrix.of fun y k =>
    if (finProdFinEquiv.symm k).1 = y.2 then D.T' (D.eR (finProdFinEquiv.symm k).2) y.1 else 0

theorem Data.KT_apply (d₀ : Fin d) (t : Fin r) (y : X4 c a b d) :
    D.KT d (finProdFinEquiv (d₀, t)) y = if d₀ = y.2 then D.T y.1 (D.eR t) else 0 := by
  simp only [Data.KT, Matrix.of_apply, Equiv.symm_apply_apply]

theorem Data.KT'_apply (d₀ : Fin d) (t : Fin r) (y : X4 c a b d) :
    D.KT' d y (finProdFinEquiv (d₀, t)) = if d₀ = y.2 then D.T' (D.eR t) y.1 else 0 := by
  simp only [Data.KT', Matrix.of_apply, Equiv.symm_apply_apply]

theorem Data.conj_apply (J : Matrix (X4 c a b d) (X4 c a b d) ℂ) (d₀ d₁ : Fin d) (t₀ t₁ : Fin r) :
    (D.KT d * J * (D.KT d)ᴴ) (finProdFinEquiv (d₀, t₀)) (finProdFinEquiv (d₁, t₁)) =
      ∑ x : X3 c a b, ∑ y : X3 c a b,
        J (x, d₀) (y, d₁) * D.T x (D.eR t₀) * star (D.T y (D.eR t₁)) := by
  have h1 : (D.KT d * J * (D.KT d)ᴴ) (finProdFinEquiv (d₀, t₀)) (finProdFinEquiv (d₁, t₁)) =
      ∑ y : X3 c a b, ∑ x : X3 c a b,
        D.T x (D.eR t₀) * J (x, d₀) (y, d₁) * star (D.T y (D.eR t₁)) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Data.KT_apply, Fintype.sum_prod_type,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      apply_ite (star : ℂ → ℂ), star_zero, mul_ite, mul_zero, Finset.sum_mul]
  rw [h1, Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

/-- **Output of the pure test.** For every physical superchannel the locked extended
action on the insertion and the pure state is the congruence `K_T J K_Tᴴ`. -/
theorem Data.output (Θ : PhysicalSuperchannel a b c d) :
    Θ.referenceAct r D.chan.val D.rho = D.KT d * combJ Θ * (D.KT d)ᴴ := by
  ext k l
  obtain ⟨⟨d₀, t₀⟩, rfl⟩ := finProdFinEquiv.surjective k
  obtain ⟨⟨d₁, t₁⟩, rfl⟩ := finProdFinEquiv.surjective l
  rw [refAct_entry, D.conj_apply]
  have hterm : ∀ z z' : Z4 c a b r,
      combJ Θ (z.1, d₀) (z'.1, d₁) *
        choi D.chan.val (finProdFinEquiv (z.1.1.2, z.2), finProdFinEquiv (z.1.2, t₀))
          (finProdFinEquiv (z'.1.1.2, z'.2), finProdFinEquiv (z'.1.2, t₁)) *
        D.rho (finProdFinEquiv (z.1.1.1, z.2)) (finProdFinEquiv (z'.1.1.1, z'.2)) =
      combJ Θ (z.1, d₀) (z'.1, d₁) * (D.vP z.1.1.2 z.2 z.1.2 t₀ * D.phiP z.1.1.1 z.2) *
        star (D.vP z'.1.1.2 z'.2 z'.1.2 t₁ * D.phiP z'.1.1.1 z'.2) := by
    intro z z'
    rw [D.choi_chan, Data.JN, Matrix.add_apply, Data.rho_apply, Data.phi_apply, Data.phi_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, Data.vK_apply, Data.vK_apply, mul_add, add_mul,
      mul_assoc _ (Matrix.diagonal D.dR _ _) _, D.reset_zero, mul_zero, add_zero, star_mul']
    ring
  simp only [hterm]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => ?_
  obtain ⟨⟨c₀, a₀⟩, b₀⟩ := x
  obtain ⟨⟨c₁, a₁⟩, b₁⟩ := y
  rw [← D.link c₀ a₀ b₀ t₀, ← D.link c₁ a₁ b₁ t₁, star_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u' _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]

/-- Trace of a congruent operator: pairing of its `D` marginal with the tester. -/
theorem Data.trace_conj (G : Matrix (X4 c a b d) (X4 c a b d) ℂ) :
    Matrix.trace (D.KT d * G * (D.KT d)ᴴ) =
      ∑ x, ∑ y, OpenQ.partialTraceRight G x y * (D.T * D.Tᴴ) x y := by
  have hT : ∀ x y : X3 c a b, (D.T * D.Tᴴ) x y =
      ∑ t : Fin r, D.T x (D.eR t) * star (D.T y (D.eR t)) := by
    intro x y
    rw [Matrix.mul_apply]
    exact (Equiv.sum_comp D.eR (fun z => D.T x z * star (D.T y z))).symm
  have hL : Matrix.trace (D.KT d * G * (D.KT d)ᴴ) =
      ∑ d₀ : Fin d, ∑ t : Fin r, ∑ x : X3 c a b, ∑ y : X3 c a b,
        G (x, d₀) (y, d₀) * (D.T x (D.eR t) * star (D.T y (D.eR t))) := by
    rw [Matrix.trace, sum_fin_prod]
    refine Finset.sum_congr rfl fun d₀ _ => Finset.sum_congr rfl fun t _ => ?_
    rw [Matrix.diag_apply, D.conj_apply]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  rw [hL]
  refine (sum4_pairs _).trans ?_
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [hT, OpenQ.partialTraceRight, Finset.sum_mul_sum]

theorem Data.KT'_mul_KT : D.KT' d * D.KT d = 1 := by
  ext y y'
  have h1 : (D.KT' d * D.KT d) y y' =
      if y.2 = y'.2 then (D.T * D.T') y'.1 y.1 else 0 := by
    rw [Matrix.mul_apply, sum_fin_prod]
    simp only [Data.KT_apply, Data.KT'_apply, mul_ite, mul_zero, ite_mul, zero_mul]
    by_cases h : y.2 = y'.2
    · rw [Finset.sum_eq_single y.2]
      · simp only [h, ↓reduceIte, Matrix.mul_apply]
        rw [← Equiv.sum_comp D.eR]
        exact Finset.sum_congr rfl fun t _ => by ring
      · intro d₀ _ hd
        simp [hd]
      · simp
    · simp only [h, ↓reduceIte]
      apply Finset.sum_eq_zero
      intro d₀ _
      apply Finset.sum_eq_zero
      intro t _
      by_cases h1 : d₀ = y'.2
      · have h2 : d₀ ≠ y.2 := fun h3 => h (h3.symm.trans h1)
        simp [h2]
      · simp [h1]
  rw [h1, D.hT2, Matrix.one_apply, Matrix.one_apply]
  obtain ⟨x, d₀⟩ := y
  obtain ⟨x', d₁⟩ := y'
  by_cases hd : d₀ = d₁ <;> by_cases hx : x = x' <;> simp [hd, hx, eq_comm]

theorem Data.KT_mul_KT' : D.KT d * D.KT' d = 1 := by
  ext k l
  obtain ⟨⟨d₀, t₀⟩, rfl⟩ := finProdFinEquiv.surjective k
  obtain ⟨⟨d₁, t₁⟩, rfl⟩ := finProdFinEquiv.surjective l
  have h1 : (D.KT d * D.KT' d) (finProdFinEquiv (d₀, t₀)) (finProdFinEquiv (d₁, t₁)) =
      if d₀ = d₁ then (D.T' * D.T) (D.eR t₁) (D.eR t₀) else 0 := by
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    simp only [Data.KT_apply, Data.KT'_apply, mul_ite, mul_zero, ite_mul, zero_mul]
    by_cases h : d₀ = d₁
    · subst h
      simp only [↓reduceIte, Matrix.mul_apply, Finset.sum_ite_eq, Finset.mem_univ]
      exact Finset.sum_congr rfl fun x _ => by ring
    · simp only [h, ↓reduceIte]
      apply Finset.sum_eq_zero
      intro x _
      apply Finset.sum_eq_zero
      intro d' _
      by_cases h1 : d₁ = d'
      · have h2 : d₀ ≠ d' := fun h3 => h (h3.trans h1.symm)
        simp [h2]
      · simp [h1]
  rw [h1, D.hT1, Matrix.one_apply, Matrix.one_apply]
  by_cases hd : d₀ = d₁ <;> by_cases ht : t₀ = t₁ <;> simp [hd, ht, eq_comm]

end
end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedProofRealize
