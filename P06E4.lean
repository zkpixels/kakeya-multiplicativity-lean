import N27

namespace KakeyaMultiplicativity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem natB12 :
    ∀ (a : Fin 27) (b : Fin 27) (c : Fin 27),
      9 ≤ a.val → 9 ≤ b.val → 9 ≤ c.val → a.val ≠ b.val → a.val ≠ c.val → b.val ≠ c.val →
      classCountN (511 ||| (1 <<< a.val) ||| (1 <<< b.val) ||| (1 <<< c.val)) ≤ 12 := by
  decide +kernel

/-- Case B, `u = 12`. -/
theorem endgame_caseB_twelve :
    ∀ extras ∈ ((Finset.univ : Finset (Fin 27)) \ zPlaneIdx).powersetCard 3,
      classCountIdx (zPlaneIdx ∪ extras) ≤ 12 := by
  intro extras hmem
  rw [Finset.mem_powersetCard] at hmem
  obtain ⟨hsub, hcard⟩ := hmem
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
  have h9a : 9 ≤ a.val := (notZPlane_iff a).mp (Finset.mem_sdiff.mp (hsub (by simp))).2
  have h9b : 9 ≤ b.val := (notZPlane_iff b).mp (Finset.mem_sdiff.mp (hsub (by simp))).2
  have h9c : 9 ≤ c.val := (notZPlane_iff c).mp (Finset.mem_sdiff.mp (hsub (by simp))).2
  have hspec : ∀ p : Fin 27,
      (511 ||| (1 <<< a.val) ||| (1 <<< b.val) ||| (1 <<< c.val)).testBit p.val = true ↔ p ∈ zPlaneIdx ∪ {a, b, c} := by
    intro p
    simp only [or_testBit, Bool.or_eq_true, shiftF_testBit,
      zplane_bit p, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [classCountN_eq hspec]
  exact natB12 a b c h9a h9b h9c (fun h => hab (Fin.val_injective h)) (fun h => hac (Fin.val_injective h)) (fun h => hbc (Fin.val_injective h))

end KakeyaMultiplicativity
