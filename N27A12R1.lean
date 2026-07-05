import N27

namespace KakeyaMultiplicativity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Case A `u = 12` slice: free rep `7` only (parallel-friendly). -/
theorem natA12_r1 :
    ∀ a b c : Fin 27,
      (starMaskN (7 : Fin 27)).testBit a.val = false →
      (starMaskN (7 : Fin 27)).testBit b.val = false →
      (starMaskN (7 : Fin 27)).testBit c.val = false →
      a.val ≠ b.val → a.val ≠ c.val → b.val ≠ c.val →
      classCountN (starMaskN (7 : Fin 27) ||| (1 <<< a.val)
        ||| (1 <<< b.val) ||| (1 <<< c.val)) ≤ 12 := by
  decide +kernel

end KakeyaMultiplicativity
