import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.Statement

/-!
Physical inserted-reference extension in finite complex computational bases.
The reference belongs to the inserted map; the internal memory is inaccessible.
All action identities hold for arbitrary complex-linear maps, on every matrix.
-/

namespace OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275

open scoped Classical
open OpenQ.Problems.EqualWeightLowChoiRank_523ed7 (IsCPTP)
open OpenQ.Problems.MultiSlotOverheadVirtualChannel_06e9f0.General
  (insertSlot insertSlot_formula insertSlot_isCPTP isCPTP_comp)
open OpenQ.Problems.MultiSlotOverheadVirtualChannel_06e9f0.Preparation
  (basisMap basisMap_apply basisMap_isCPTP)

noncomputable section

/-- Reassociate and exchange the reference and the inaccessible memory. -/
def swapReferenceMemory {X R E : Type} : (X × R) × E ≃ (X × E) × R where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun p := ((p.1.1, p.2), p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Computational-basis permutation `(x,r,e) ↦ (x,e,r)`.
The direction is the pullback used by `basisMap`. -/
def memoryReferenceEquiv (x e r : ℕ) :
    Fin ((x * r) * e) ≃ Fin ((x * e) * r) :=
  (finProdFinEquiv.symm : Fin ((x * r) * e) ≃ Fin (x * r) × Fin e) |>.trans
    (Equiv.prodCongr finProdFinEquiv.symm (Equiv.refl (Fin e))) |>.trans
    swapReferenceMemory |>.trans
    (Equiv.prodCongr finProdFinEquiv (Equiv.refl (Fin r))) |>.trans
    finProdFinEquiv

@[simp] theorem memoryReferenceEquiv_apply (x e r : ℕ)
    (i : Fin x) (s : Fin r) (u : Fin e) :
    memoryReferenceEquiv x e r (finProdFinEquiv (finProdFinEquiv (i, s), u)) =
      finProdFinEquiv (finProdFinEquiv (i, u), s) := by
  simp [memoryReferenceEquiv, swapReferenceMemory]

@[simp] theorem memoryReferenceEquiv_symm_apply (x e r : ℕ)
    (i : Fin x) (u : Fin e) (s : Fin r) :
    (memoryReferenceEquiv x e r).symm
        (finProdFinEquiv (finProdFinEquiv (i, u), s)) =
      finProdFinEquiv (finProdFinEquiv (i, s), u) := by
  apply (memoryReferenceEquiv x e r).injective
  simp

/-- Tensoring on a reference respects composition on arbitrary linear maps. -/
theorem insertReference_comp {a b c : ℕ} (r : ℕ)
    (F : ChannelMap a b) (G : ChannelMap b c) :
    insertSlot r (G ∘ₗ F) = insertSlot r G ∘ₗ insertSlot r F := by
  apply LinearMap.ext
  intro X
  apply Matrix.ext
  intro i j
  obtain ⟨⟨k, s⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨l, t⟩, rfl⟩ := finProdFinEquiv.surjective j
  simp only [LinearMap.comp_apply, insertSlot_formula]
  rfl

/-- Passing the reference past memory commutes with a product slot insertion.
This identity is on the entire matrix space, including correlated inputs. -/
theorem insertReference_memory_commute {a b : ℕ} (e r : ℕ)
    (N : ChannelMap a b) :
    basisMap (memoryReferenceEquiv b e r).symm ∘ₗ
        insertSlot e (insertSlot r N) ∘ₗ basisMap (memoryReferenceEquiv a e r) =
      insertSlot r (insertSlot e N) := by
  apply LinearMap.ext
  intro X
  apply Matrix.ext
  intro i j
  obtain ⟨⟨k, s⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨l, t⟩, rfl⟩ := finProdFinEquiv.surjective j
  obtain ⟨⟨β, u⟩, rfl⟩ := finProdFinEquiv.surjective k
  obtain ⟨⟨γ, v⟩, rfl⟩ := finProdFinEquiv.surjective l
  simp only [LinearMap.comp_apply, basisMap_apply, memoryReferenceEquiv_symm_apply,
    insertSlot_formula]
  have hL := insertSlot_formula (e := r) N
    (fun i j => X (memoryReferenceEquiv a e r (finProdFinEquiv (i, u)))
      (memoryReferenceEquiv a e r (finProdFinEquiv (j, v)))) (β, s) (γ, t)
  have hR := insertSlot_formula (e := e) N
    (fun i j => X (finProdFinEquiv (i, s)) (finProdFinEquiv (j, t))) (β, u) (γ, v)
  have hblocks :
      (fun i j : Fin a => X
        (memoryReferenceEquiv a e r (finProdFinEquiv (finProdFinEquiv (i, s), u)))
        (memoryReferenceEquiv a e r (finProdFinEquiv (finProdFinEquiv (j, t), v)))) =
      (fun i j : Fin a => X (finProdFinEquiv (finProdFinEquiv (i, u), s))
        (finProdFinEquiv (finProdFinEquiv (j, v), t))) := by
    funext i j
    rw [memoryReferenceEquiv_apply, memoryReferenceEquiv_apply]
  exact hL.trans ((congrArg (fun W : Operator (Fin a) => N W β γ) hblocks).trans hR.symm)

/-- Each tooth is tensored with `id_R`, then the reference is permuted past
the inaccessible memory to place the entire joint slot before that memory. -/
def PhysicalSuperchannel.referenceRealization {a b c d : ℕ}
    (Θ : PhysicalSuperchannel a b c d) (r : ℕ) :
    PhysicalSuperchannel (a * r) (b * r) (c * r) (d * r) where
  memory := Θ.memory
  memory_pos := Θ.memory_pos
  pre := basisMap (memoryReferenceEquiv a Θ.memory r) ∘ₗ insertSlot r Θ.pre
  post := insertSlot r Θ.post ∘ₗ basisMap (memoryReferenceEquiv b Θ.memory r).symm
  pre_cptp := isCPTP_comp (insertSlot_isCPTP Θ.pre Θ.pre_cptp)
    (basisMap_isCPTP _)
  post_cptp := isCPTP_comp (basisMap_isCPTP _)
    (insertSlot_isCPTP Θ.post Θ.post_cptp)

/-- Action on an arbitrary joint map `L(A ⊗ R) → L(B ⊗ R)`.
Only the inaccessible memory is passed unchanged around this joint map. -/
def PhysicalSuperchannel.referenceAct {a b c d : ℕ}
    (Θ : PhysicalSuperchannel a b c d) (r : ℕ)
    (N : ChannelMap (a * r) (b * r)) : ChannelMap (c * r) (d * r) :=
  (Θ.referenceRealization r).act N

/-- The extended realization is complex linear on the entire joint-map space. -/
def PhysicalSuperchannel.referenceActionLinear {a b c d : ℕ}
    (Θ : PhysicalSuperchannel a b c d) (r : ℕ) :
    ChannelMap (a * r) (b * r) →ₗ[ℂ] ChannelMap (c * r) (d * r) :=
  (Θ.referenceRealization r).actionLinear

theorem PhysicalSuperchannel.referenceAct_formula {a b c d : ℕ}
    (Θ : PhysicalSuperchannel a b c d) (r : ℕ)
    (N : ChannelMap (a * r) (b * r)) :
    Θ.referenceAct r N =
      insertSlot r Θ.post ∘ₗ basisMap (memoryReferenceEquiv b Θ.memory r).symm ∘ₗ
      insertSlot Θ.memory N ∘ₗ basisMap (memoryReferenceEquiv a Θ.memory r) ∘ₗ
      insertSlot r Θ.pre := by
  simp only [PhysicalSuperchannel.referenceAct, PhysicalSuperchannel.act,
    PhysicalSuperchannel.referenceRealization, LinearMap.comp_assoc]

/-- Independently CPTP joint insertions produce independently CPTP outputs. -/
theorem PhysicalSuperchannel.referenceAct_isCPTP {a b c d : ℕ}
    (Θ : PhysicalSuperchannel a b c d) (r : ℕ)
    (N : ChannelMap (a * r) (b * r)) (hN : IsCPTP N) :
    IsCPTP (Θ.referenceAct r N) :=
  (Θ.referenceRealization r).act_isCPTP N hN

/-- Bundled action for the operational divergences, with no promise on a joint
insertion other than its independently defined CPTP property. -/
def PhysicalSuperchannel.referenceOnChannel {a b c d : ℕ}
    (Θ : PhysicalSuperchannel a b c d) (r : ℕ)
    (N : Channel (a * r) (b * r)) : Channel (c * r) (d * r) :=
  ⟨Θ.referenceAct r N.val, Θ.referenceAct_isCPTP r N.val N.property⟩

/-- On a product insertion `N ⊗ id_R`, the output is `Θ(N) ⊗ id_R`.
No complete positivity or trace preservation of `N` is assumed. -/
theorem PhysicalSuperchannel.referenceAct_product {a b c d : ℕ}
    (Θ : PhysicalSuperchannel a b c d) (r : ℕ) (N : ChannelMap a b) :
    Θ.referenceAct r (insertSlot r N) = insertSlot r (Θ.act N) := by
  rw [Θ.referenceAct_formula]
  change insertSlot r Θ.post ∘ₗ
    (basisMap (memoryReferenceEquiv b Θ.memory r).symm ∘ₗ
      insertSlot Θ.memory (insertSlot r N) ∘ₗ
      basisMap (memoryReferenceEquiv a Θ.memory r)) ∘ₗ
    insertSlot r Θ.pre = _
  rw [insertReference_memory_commute]
  simp only [PhysicalSuperchannel.act, insertReference_comp]

/-- Canonical identification `ℂ^(x*1) ≃ ℂ^x` in the computational basis. -/
def trivialReferenceEquiv (x : ℕ) : Fin (x * 1) ≃ Fin x :=
  finCongr (Nat.mul_one x)

@[simp] theorem trivialReferenceEquiv_apply (x : ℕ) (i : Fin x) (s : Fin 1) :
    trivialReferenceEquiv x (finProdFinEquiv (i, s)) = i := by
  apply Fin.ext
  have hs : s = 0 := Subsingleton.elim _ _
  subst s
  simp [trivialReferenceEquiv, finProdFinEquiv]

/-- Remove the one-dimensional tensor factor on both sides of a joint map. -/
def removeTrivialReference {a b : ℕ}
    (N : ChannelMap (a * 1) (b * 1)) : ChannelMap a b :=
  basisMap (trivialReferenceEquiv b).symm ∘ₗ N ∘ₗ
    basisMap (trivialReferenceEquiv a)

/-- Every joint linear map at `r=1` is a product insertion under the canonical
identifications. This does not restrict the map to be CPTP. -/
theorem insertReference_one_remove {a b : ℕ}
    (N : ChannelMap (a * 1) (b * 1)) :
    insertSlot 1 (removeTrivialReference N) = N := by
  apply LinearMap.ext
  intro X
  apply Matrix.ext
  intro i j
  obtain ⟨⟨β, s⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨γ, t⟩, rfl⟩ := finProdFinEquiv.surjective j
  rw [insertSlot_formula]
  change N (fun k l => X
      (finProdFinEquiv (trivialReferenceEquiv a k, s))
      (finProdFinEquiv (trivialReferenceEquiv a l, t)))
      ((trivialReferenceEquiv b).symm β) ((trivialReferenceEquiv b).symm γ) = _
  have hs : (trivialReferenceEquiv b).symm β = finProdFinEquiv (β, s) := by
    apply (trivialReferenceEquiv b).injective
    simp
  have ht : (trivialReferenceEquiv b).symm γ = finProdFinEquiv (γ, t) := by
    apply (trivialReferenceEquiv b).injective
    simp
  rw [hs, ht]
  have hX : (fun k l => X (finProdFinEquiv (trivialReferenceEquiv a k, s))
      (finProdFinEquiv (trivialReferenceEquiv a l, t))) = X := by
    funext k l
    obtain ⟨⟨i, u⟩, rfl⟩ := finProdFinEquiv.surjective k
    obtain ⟨⟨j, v⟩, rfl⟩ := finProdFinEquiv.surjective l
    simp only [trivialReferenceEquiv_apply]
    rw [Subsingleton.elim s u, Subsingleton.elim t v]
  rw [hX]

/-- Removing a product one-dimensional factor recovers the original map. -/
theorem removeTrivialReference_insert {a b : ℕ} (N : ChannelMap a b) :
    removeTrivialReference (insertSlot 1 N) = N := by
  apply LinearMap.ext
  intro X
  apply Matrix.ext
  intro i j
  simp only [removeTrivialReference, LinearMap.comp_apply, basisMap_apply]
  have hi : (trivialReferenceEquiv b).symm i = finProdFinEquiv (i, (0 : Fin 1)) := by
    apply (trivialReferenceEquiv b).injective
    simp
  have hj : (trivialReferenceEquiv b).symm j = finProdFinEquiv (j, (0 : Fin 1)) := by
    apply (trivialReferenceEquiv b).injective
    simp
  rw [hi, hj, insertSlot_formula]
  simp only [basisMap_apply, trivialReferenceEquiv_apply]

/-- Trivial-reference action agrees with the locked physical action under
canonical identifications, for every joint complex-linear insertion. -/
theorem PhysicalSuperchannel.referenceAct_one {a b c d : ℕ}
    (Θ : PhysicalSuperchannel a b c d) (N : ChannelMap (a * 1) (b * 1)) :
    removeTrivialReference (Θ.referenceAct 1 N) =
      Θ.act (removeTrivialReference N) := by
  conv_lhs => rw [← insertReference_one_remove N]
  rw [Θ.referenceAct_product, removeTrivialReference_insert]

end
end OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275
