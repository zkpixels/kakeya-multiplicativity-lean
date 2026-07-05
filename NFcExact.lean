import P50BFc

namespace KakeyaMultiplicativity

/-! Exactness of the small mod-2 fractional-cost values: both halves of
`fc(2,2) = 3`, `fc(2,3) = 4`, `fc(2,4) = 6` as kernel facts.  The
positive halves `FC(2,2,3)` and `FC(2,4,6)` and the refutation
`¬FC(2,3,5)` live in the main development; this file adds the three
complementary halves, so that each of the three values is pinned from
both sides by the kernel. -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `FC(2,3,4)` holds: the mod-2 three-space certificate at the
discounted price four (all 256 windows, kernel-enumerated). -/
theorem fractionalCostAt_two_three_at_four :
    FractionalCostAt 2 3 (nonzeroDirections 2 3) 4 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `¬FC(2,2,4)`: the plane certificate fails one above its true price
(all 16 windows, kernel-enumerated). -/
theorem not_fractionalCostAt_two_two_at_four :
    ¬ FractionalCostAt 2 2 (nonzeroDirections 2 2) 4 := by
  decide

set_option maxRecDepth 100000 in
/-- `¬FC(2,4,7)`: the six-point Kakeya witness kills the dimension-four
certificate one above its true price — it carries all fifteen
directions, and `15 · 7 = 105 > 90 = 6 · 15`. -/
theorem not_fractionalCostAt_two_four_at_seven :
    ¬ FractionalCostAt 2 4 (nonzeroDirections 2 4) 7 := by
  intro h
  have hb := h twoFourWitness
  have hall : (nonzeroDirections 2 4).filter
      (fun b => CarriesLine twoFourWitness b) = nonzeroDirections 2 4 :=
    Finset.filter_true_of_mem fun b _ =>
      isKakeyaSet_iff_forall_carriesLine.mp twoFourWitness_isKakeyaSet b
  rw [hall, twoFourWitness_card] at hb
  have hmenu : (nonzeroDirections 2 4).card = 15 := by decide
  rw [hmenu] at hb
  omega

end KakeyaMultiplicativity
