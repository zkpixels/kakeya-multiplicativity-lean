import N27

namespace KakeyaMultiplicativity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem natB11 :
    ∀ (a : Fin 27) (b : Fin 27),
      9 ≤ a.val → 9 ≤ b.val → a.val ≠ b.val →
      classCountN (511 ||| (1 <<< a.val) ||| (1 <<< b.val)) ≤ 11 := by
  decide +kernel

/-- Case B, `u = 11`. -/
theorem endgame_caseB_eleven :
    ∀ extras ∈ ((Finset.univ : Finset (Fin 27)) \ zPlaneIdx).powersetCard 2,
      classCountIdx (zPlaneIdx ∪ extras) ≤ 11 := by
  intro extras hmem
  rw [Finset.mem_powersetCard] at hmem
  obtain ⟨hsub, hcard⟩ := hmem
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
  have h9a : 9 ≤ a.val := (notZPlane_iff a).mp (Finset.mem_sdiff.mp (hsub (by simp))).2
  have h9b : 9 ≤ b.val := (notZPlane_iff b).mp (Finset.mem_sdiff.mp (hsub (by simp))).2
  have hspec : ∀ p : Fin 27,
      (511 ||| (1 <<< a.val) ||| (1 <<< b.val)).testBit p.val = true ↔ p ∈ zPlaneIdx ∪ {a, b} := by
    intro p
    simp only [or_testBit, Bool.or_eq_true, shiftF_testBit,
      zplane_bit p, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [classCountN_eq hspec]
  exact natB11 a b h9a h9b (fun h => hab (Fin.val_injective h))

end KakeyaMultiplicativity
