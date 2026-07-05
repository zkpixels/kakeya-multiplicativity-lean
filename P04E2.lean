import N27

namespace KakeyaMultiplicativity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem natB10 :
    ∀ (a : Fin 27),
      9 ≤ a.val →
      classCountN (511 ||| (1 <<< a.val)) ≤ 10 := by
  decide +kernel

/-- Case B, `u = 10`. -/
theorem endgame_caseB_ten :
    ∀ extras ∈ ((Finset.univ : Finset (Fin 27)) \ zPlaneIdx).powersetCard 1,
      classCountIdx (zPlaneIdx ∪ extras) ≤ 10 := by
  intro extras hmem
  rw [Finset.mem_powersetCard] at hmem
  obtain ⟨hsub, hcard⟩ := hmem
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
  have h9a : 9 ≤ a.val := (notZPlane_iff a).mp (Finset.mem_sdiff.mp (hsub (by simp))).2
  have hspec : ∀ p : Fin 27,
      (511 ||| (1 <<< a.val)).testBit p.val = true ↔ p ∈ zPlaneIdx ∪ {a} := by
    intro p
    simp only [or_testBit, Bool.or_eq_true, shiftF_testBit,
      zplane_bit p, Finset.mem_union, Finset.mem_singleton]
  rw [classCountN_eq hspec]
  exact natB10 a h9a 

end KakeyaMultiplicativity
