import P12Schema
import P31AFc
import P50BFc

/-!
Root module: building this target builds the entire verification tree
(all theorems of the paper) in dependency order.

The `#print axioms` lines below run at build time: every public payoff
must report exactly `[propext, Classical.choice, Quot.sound]` — the
standard classical trio.  No `sorry`, no extra axioms, no
`Lean.ofReduceBool` (i.e. no `native_decide`): every enumeration is
checked by the Lean kernel itself.
-/

#print axioms KakeyaMultiplicativity.minKakeyaSize_three_three
#print axioms KakeyaMultiplicativity.minKakeyaSize_six_three
#print axioms KakeyaMultiplicativity.minKakeyaSize_six_three_eq_product
#print axioms KakeyaMultiplicativity.minKakeyaSize_squarefree_dim_two
#print axioms KakeyaMultiplicativity.minKakeyaSize_four_two
#print axioms KakeyaMultiplicativity.minKakeyaSize_twelve_two
#print axioms KakeyaMultiplicativity.minKakeyaSize_two_four'
#print axioms KakeyaMultiplicativity.minKakeyaSize_two_mul_dim_four
