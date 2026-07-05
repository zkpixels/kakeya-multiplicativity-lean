/-
Multiplicativity of Kakeya minima over ℤ/Nℤ.

Self-contained Lean 4 development of:
* the coprime transfer principle (fractional cost certificate on one
  factor ⟹ lower bound against every coprime co-factor; exactness at
  the true price),
* the direction-price theorem for 𝔽₃³ (any `s` points contain full
  lines in at most `s` direction classes),
* the exact values K(2,2)=3, K(3,2)=7, K(6,2)=21, K(2,3)=5, K(3,3)=13,
  K(6,3)=65, and the infinite families K(2M,2)=3K(M,2) (odd M),
  K(3M,2)=7K(M,2), K(6M,2)=21K(M,2), K(3M,3)=13K(M,3) (gcd(M,3)=1).

Only `decide` (kernel evaluation) is used for finite checks; no
`native_decide`, no axioms beyond propext/Classical.choice/Quot.sound.

Checked with Lean toolchain leanprover/lean4:v4.32.0-rc1 and the
matching Mathlib release (lake manifest inputRev v4.32.0-rc1).
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace KakeyaMultiplicativity

/--
A point of the rank-`n` free module over the residue ring `ZMod N`,
represented as a coordinate function.

The definitions below are stated without a `NeZero N` hypothesis, in the
standard Mathlib total-function style: for `N = 0` the ring `ZMod 0 = ℤ`
is infinite, no finite Kakeya set exists in positive dimension, the
achievable-size set can be empty, and `minKakeyaSize` silently takes the
junk value `sInf ∅ = 0`.  Every theorem that actually needs finiteness
carries `[NeZero N]` explicitly.  Totality is what lets the squarefree
fold corollary write `∏ p ∈ N.primeFactors, minKakeyaSize p n` without
threading a per-prime instance through the product binder.
-/
abbrev ResiduePoint (N n : ℕ) := Fin n → ZMod N

/--
The line through `a` with direction `b`, as a parametrized family of
points: `t ↦ a + t • b`.

No primitivity or nonvanishing is assumed about `b`.  For `b = 0` the
family is constantly `a`; the Kakeya predicate below therefore only asks
for a point at the zero direction.  The parametrization is by ring
elements `t : ZMod N`, so a "line" has at most `N` distinct points and
may have fewer when `b` has non-unit coordinates.  These degeneracies are
deliberate: they are exactly what survives the Chinese remainder
transport unconditionally.
-/
def residueLine {N n : ℕ} (a b : ResiduePoint N n) :
    ZMod N → ResiduePoint N n :=
  fun t => a + t • b

/-- The line's value at a parameter, stated as a rewriting lemma. -/
theorem residueLine_apply {N n : ℕ} (a b : ResiduePoint N n)
    (t : ZMod N) :
    residueLine a b t = a + t • b :=
  rfl

/-- At parameter zero every line passes through its anchor. -/
theorem residueLine_zero {N n : ℕ} (a b : ResiduePoint N n) :
    residueLine a b 0 = a := by
  funext i
  simp [residueLine]

/--
The Kakeya predicate over `(ZMod N)^n`: the finite set `K` contains, for
every direction `b`, a full line `t ↦ a + t • b` for some anchor `a`.

This is the all-directions convention described in the module docstring.
The predicate is stated for `Finset` carriers because the object of study
is the minimum cardinality; the ambient type is finite whenever
`NeZero N` holds.
-/
def IsKakeyaSet {N n : ℕ}
    (K : Finset (ResiduePoint N n)) : Prop :=
  ∀ b : ResiduePoint N n, ∃ a : ResiduePoint N n,
    ∀ t : ZMod N, residueLine a b t ∈ K

/-- Over a finite carrier the Kakeya predicate is decidable: the
quantifiers range over fintypes and membership is decidable.  This is
what lets small cells be settled by kernel `decide` with no search
infrastructure. -/
instance {N n : ℕ} [NeZero N] (K : Finset (ResiduePoint N n)) :
    Decidable (IsKakeyaSet K) :=
  inferInstanceAs
    (Decidable (∀ b : ResiduePoint N n, ∃ a : ResiduePoint N n,
      ∀ t : ZMod N, residueLine a b t ∈ K))

/-- Kakeya sets are upward closed: any superset of a Kakeya set is again
a Kakeya set.  This is the monotonicity that makes the minimum the only
interesting size statistic. -/
theorem IsKakeyaSet.mono {N n : ℕ}
    {K K' : Finset (ResiduePoint N n)} (hsub : K ⊆ K')
    (hK : IsKakeyaSet K) : IsKakeyaSet K' := by
  intro b
  rcases hK b with ⟨a, ha⟩
  exact ⟨a, fun t => hsub (ha t)⟩

/-- The full space is a Kakeya set: every line is contained in it.  This
witness makes the achievable-size set nonempty, so the minimum below is
attained rather than a vacuous infimum. -/
theorem univ_isKakeyaSet (N n : ℕ) [NeZero N] :
    IsKakeyaSet (Finset.univ : Finset (ResiduePoint N n)) := by
  intro b
  exact ⟨0, fun t => Finset.mem_univ _⟩

/-- A Kakeya set is nonempty: the zero direction already demands a point.
Degenerate but load-bearing: it gives the uniform lower bound
`1 ≤ minKakeyaSize` and the dimension-zero sanity value. -/
theorem IsKakeyaSet.nonempty {N n : ℕ}
    {K : Finset (ResiduePoint N n)} (hK : IsKakeyaSet K) :
    K.Nonempty := by
  rcases hK 0 with ⟨a, ha⟩
  exact ⟨a, residueLine_zero a 0 ▸ ha 0⟩

/--
The set of achievable Kakeya cardinalities over `(ZMod N)^n`.

Kept as a named definition so that the minimum below has a stable
description and so later files can reason about membership directly.
-/
def kakeyaSizes (N n : ℕ) : Set ℕ :=
  {k | ∃ K : Finset (ResiduePoint N n), IsKakeyaSet K ∧ K.card = k}

/-- The full space witnesses that some size is achievable. -/
theorem kakeyaSizes_nonempty (N n : ℕ) [NeZero N] :
    (kakeyaSizes N n).Nonempty :=
  ⟨(Finset.univ : Finset (ResiduePoint N n)).card,
    Finset.univ, univ_isKakeyaSet N n, rfl⟩

/--
The minimum size of a Kakeya set over `(ZMod N)^n`.

Defined as `Nat.sInf` of the achievable sizes.  Because the achievable
set is nonempty (`kakeyaSizes_nonempty`), this infimum is attained
(`exists_minKakeyaSize_witness`), so the definition really is a minimum
and not merely a lower bound.  This is the global quantity the
local-global composition law will bound by products of local minima.
-/
noncomputable def minKakeyaSize (N n : ℕ) : ℕ :=
  sInf (kakeyaSizes N n)

/-- Any Kakeya set bounds the minimum from above.  This is the workhorse
inequality: to bound `minKakeyaSize`, exhibit a Kakeya set. -/
theorem minKakeyaSize_le_card {N n : ℕ}
    {K : Finset (ResiduePoint N n)} (hK : IsKakeyaSet K) :
    minKakeyaSize N n ≤ K.card :=
  Nat.sInf_le ⟨K, hK, rfl⟩

/-- The minimum is attained by an actual Kakeya set. -/
theorem exists_minKakeyaSize_witness (N n : ℕ) [NeZero N] :
    ∃ K : Finset (ResiduePoint N n),
      IsKakeyaSet K ∧ K.card = minKakeyaSize N n :=
  Nat.sInf_mem (kakeyaSizes_nonempty N n)

/-- Trivial upper bound: the minimum is at most the size of the whole
space, `N ^ n`. -/
theorem minKakeyaSize_le_pow (N n : ℕ) [NeZero N] :
    minKakeyaSize N n ≤ N ^ n := by
  have h := minKakeyaSize_le_card (univ_isKakeyaSet N n)
  calc minKakeyaSize N n
      ≤ (Finset.univ : Finset (ResiduePoint N n)).card := h
    _ = N ^ n := by
        rw [Finset.card_univ, Fintype.card_fun, ZMod.card,
          Fintype.card_fin]

/-- Uniform lower bound: a Kakeya set is nonempty, so the minimum is at
least one.  In particular the minimum never degenerates to zero, which
later defect accounting relies on. -/
theorem one_le_minKakeyaSize (N n : ℕ) [NeZero N] :
    1 ≤ minKakeyaSize N n := by
  rcases exists_minKakeyaSize_witness N n with ⟨K, hK, hcard⟩
  have hpos : 0 < K.card := Finset.card_pos.mpr hK.nonempty
  omega

/-! ## Chinese remainder transport

The local-global layer.  `ZMod.chineseRemainder` is the trusted Mathlib
ring isomorphism `ZMod (N₁ * N₂) ≃+* ZMod N₁ × ZMod N₂` for coprime
moduli; here it is lifted componentwise to points, and the two facts the
composition law needs are proved:

* lines transport to pairs of lines, with the line parameter splitting
  through the same isomorphism (this is where the ring structure of the
  isomorphism is load-bearing: anchors add, directions scale);
* the pulled-back product of two finite point sets has cardinality equal
  to the product of the cardinalities.

Nothing in this section mentions the Kakeya predicate; it is pure
transport, so the statements stay usable for any later residue-ring
development.
-/


variable {N₁ N₂ n : ℕ}

/--
The componentwise Chinese-remainder equivalence on points: a point modulo
`N₁ * N₂` corresponds to a pair of points modulo `N₁` and modulo `N₂`.

Defined directly (rather than through equivalence combinators) so that
both directions reduce definitionally at each coordinate, which keeps the
transport lemmas below close to `rfl`.
-/
def crtPointEquiv (h : N₁.Coprime N₂) :
    ResiduePoint (N₁ * N₂) n ≃ ResiduePoint N₁ n × ResiduePoint N₂ n where
  toFun x :=
    (fun i => (ZMod.chineseRemainder h (x i)).1,
     fun i => (ZMod.chineseRemainder h (x i)).2)
  invFun y := fun i => (ZMod.chineseRemainder h).symm (y.1 i, y.2 i)
  left_inv x := by
    funext i
    show (ZMod.chineseRemainder h).symm
      ((ZMod.chineseRemainder h (x i)).1,
       (ZMod.chineseRemainder h (x i)).2) = x i
    rw [Prod.mk.eta, RingEquiv.symm_apply_apply]
  right_inv y := by
    refine Prod.ext ?_ ?_ <;> funext i
    · show (ZMod.chineseRemainder h
        ((ZMod.chineseRemainder h).symm (y.1 i, y.2 i))).1 = y.1 i
      rw [RingEquiv.apply_symm_apply]
    · show (ZMod.chineseRemainder h
        ((ZMod.chineseRemainder h).symm (y.1 i, y.2 i))).2 = y.2 i
      rw [RingEquiv.apply_symm_apply]

/-- First local component of a transported point, at a coordinate. -/
theorem crtPointEquiv_fst_apply (h : N₁.Coprime N₂)
    (x : ResiduePoint (N₁ * N₂) n) (i : Fin n) :
    (crtPointEquiv h x).1 i = (ZMod.chineseRemainder h (x i)).1 :=
  rfl

/-- Second local component of a transported point, at a coordinate. -/
theorem crtPointEquiv_snd_apply (h : N₁.Coprime N₂)
    (x : ResiduePoint (N₁ * N₂) n) (i : Fin n) :
    (crtPointEquiv h x).2 i = (ZMod.chineseRemainder h (x i)).2 :=
  rfl

/-- Inverse transport, at a coordinate: local pairs recombine through the
inverse Chinese remainder map. -/
theorem crtPointEquiv_symm_apply (h : N₁.Coprime N₂)
    (y : ResiduePoint N₁ n) (z : ResiduePoint N₂ n) (i : Fin n) :
    (crtPointEquiv h).symm (y, z) i =
      (ZMod.chineseRemainder h).symm (y i, z i) :=
  rfl

/--
Line-to-line transport: the Chinese remainder equivalence carries the
line through `a` with direction `b` at parameter `t` to the pair of local
lines through the local anchors with the local directions, at the SPLIT
parameter `ZMod.chineseRemainder h t`.

This is the load-bearing algebraic fact of the whole composition law: it
holds because the Chinese remainder map is a ring isomorphism, so it
preserves the affine expression `a + t * b` coordinatewise.  As `t`
ranges over all of `ZMod (N₁ * N₂)`, the split parameters range over all
of `ZMod N₁ × ZMod N₂` (the map is surjective), which is why a global
line covers full local lines and conversely.
-/
theorem crtPointEquiv_residueLine (h : N₁.Coprime N₂)
    (a b : ResiduePoint (N₁ * N₂) n) (t : ZMod (N₁ * N₂)) :
    crtPointEquiv h (residueLine a b t) =
      (residueLine (crtPointEquiv h a).1 (crtPointEquiv h b).1
        (ZMod.chineseRemainder h t).1,
       residueLine (crtPointEquiv h a).2 (crtPointEquiv h b).2
        (ZMod.chineseRemainder h t).2) := by
  refine Prod.ext ?_ ?_ <;> funext i <;>
    simp [crtPointEquiv_fst_apply, crtPointEquiv_snd_apply, residueLine,
      smul_eq_mul, map_add, map_mul]

/--
The Chinese remainder product of two finite point sets: the pullback of
`K₁ ×ˢ K₂` along the point equivalence.  This is the set the composition
law will exhibit as a global Kakeya witness.
-/
def crtProductSet (h : N₁.Coprime N₂)
    (K₁ : Finset (ResiduePoint N₁ n)) (K₂ : Finset (ResiduePoint N₂ n)) :
    Finset (ResiduePoint (N₁ * N₂) n) :=
  (K₁ ×ˢ K₂).map (crtPointEquiv h).symm.toEmbedding

/-- Membership in the Chinese remainder product is exactly componentwise
membership of the transported point. -/
theorem mem_crtProductSet (h : N₁.Coprime N₂)
    {K₁ : Finset (ResiduePoint N₁ n)} {K₂ : Finset (ResiduePoint N₂ n)}
    (x : ResiduePoint (N₁ * N₂) n) :
    x ∈ crtProductSet h K₁ K₂ ↔
      (crtPointEquiv h x).1 ∈ K₁ ∧ (crtPointEquiv h x).2 ∈ K₂ := by
  constructor
  · intro hx
    rcases Finset.mem_map.mp hx with ⟨p, hp, hpx⟩
    rcases Finset.mem_product.mp hp with ⟨h1, h2⟩
    have hxp : crtPointEquiv h x = p := by
      rw [← hpx]
      simp [Equiv.toEmbedding]
    rw [hxp]
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine Finset.mem_map.mpr
      ⟨crtPointEquiv h x, Finset.mem_product.mpr ⟨h1, h2⟩, ?_⟩
    simp [Equiv.toEmbedding]

/-- Cardinality transport: the Chinese remainder product has exactly the
product cardinality.  Injectivity is carried by the embedding, so no
counting argument is repeated here. -/
theorem crtProductSet_card (h : N₁.Coprime N₂)
    (K₁ : Finset (ResiduePoint N₁ n)) (K₂ : Finset (ResiduePoint N₂ n)) :
    (crtProductSet h K₁ K₂).card = K₁.card * K₂.card := by
  rw [crtProductSet, Finset.card_map, Finset.card_product]


/-! ## The composition law

The class-level theorem: for coprime moduli the global Kakeya minimum is
at most the product of the local minima, in every dimension at once.  The
proof is the CRT product construction: local minimum witnesses combine
through `crtProductSet`, whose Kakeya property is exactly the line
transport of the previous section applied at the recombined anchor, and
whose cardinality is exactly the product.
-/


variable {N₁ N₂ n : ℕ}

/--
The Chinese remainder product of two Kakeya sets is a Kakeya set.

Given a global direction `b`, take local anchors for the two local
components of `b`, recombine them through the inverse point equivalence,
and observe that at every global parameter `t` the transported point lies
on both local lines at the split parameters.  No surjectivity or
primitivity input is needed for this direction of the transport.
-/
theorem crtProductSet_isKakeyaSet (h : N₁.Coprime N₂)
    {K₁ : Finset (ResiduePoint N₁ n)} {K₂ : Finset (ResiduePoint N₂ n)}
    (hK₁ : IsKakeyaSet K₁) (hK₂ : IsKakeyaSet K₂) :
    IsKakeyaSet (crtProductSet h K₁ K₂) := by
  intro b
  obtain ⟨a₁, ha₁⟩ := hK₁ (crtPointEquiv h b).1
  obtain ⟨a₂, ha₂⟩ := hK₂ (crtPointEquiv h b).2
  refine ⟨(crtPointEquiv h).symm (a₁, a₂), fun t => ?_⟩
  rw [mem_crtProductSet, crtPointEquiv_residueLine,
    Equiv.apply_symm_apply]
  exact ⟨ha₁ _, ha₂ _⟩

/--
CLASS THEOREM (CRT submultiplicativity of Kakeya minima): for coprime
moduli `N₁, N₂` and every dimension `n`,

`minKakeyaSize (N₁ * N₂) n ≤ minKakeyaSize N₁ n * minKakeyaSize N₂ n`.

This single statement covers all coprime factorizations and all
dimensions.  Whether the inequality is ever strict is exactly the
multiplicativity question this development answers on the certified
cells below.
-/
theorem minKakeyaSize_mul_le [NeZero N₁] [NeZero N₂]
    (h : N₁.Coprime N₂) (n : ℕ) :
    minKakeyaSize (N₁ * N₂) n ≤
      minKakeyaSize N₁ n * minKakeyaSize N₂ n := by
  obtain ⟨K₁, hK₁, hcard₁⟩ := exists_minKakeyaSize_witness N₁ n
  obtain ⟨K₂, hK₂, hcard₂⟩ := exists_minKakeyaSize_witness N₂ n
  calc minKakeyaSize (N₁ * N₂) n
      ≤ (crtProductSet h K₁ K₂).card :=
        minKakeyaSize_le_card (crtProductSet_isKakeyaSet h hK₁ hK₂)
    _ = K₁.card * K₂.card := crtProductSet_card h K₁ K₂
    _ = minKakeyaSize N₁ n * minKakeyaSize N₂ n := by
        rw [hcard₁, hcard₂]


/-! ## The squarefree prime fold

Iterating the composition law along the prime factorization of a
squarefree modulus bounds the global minimum by the product of the
prime-local minima.  This is the fully local-global form of the class
theorem: every prime place contributes its own local minimum, and the
global carrier pays at most their product.
-/

/-- The explicit three-point Kakeya witness in `(ZMod 2)²`: the origin
and its two coordinate neighbors.  The three pairwise differences realize
the three nonzero directions, and the zero direction is a point. -/
def twoTwoKakeyaWitness : Finset (ResiduePoint 2 2) :=
  {fun _ => 0,
   fun i => if i = 0 then 0 else 1,
   fun i => if i = 0 then 1 else 0}

/-- The witness is a Kakeya set (kernel-decided over the 4-point space). -/
theorem twoTwoKakeyaWitness_isKakeyaSet :
    IsKakeyaSet twoTwoKakeyaWitness := by
  decide

/-- The witness has exactly three points. -/
theorem twoTwoKakeyaWitness_card : twoTwoKakeyaWitness.card = 3 := by
  decide

/-- No two-point set is Kakeya over `(ZMod 2)²`: kernel-decided over all
sixteen subsets.  A two-point set carries exactly one difference, but
three nonzero directions each demand a two-point line. -/
theorem three_le_card_of_twoTwo_isKakeyaSet :
    ∀ K : Finset (ResiduePoint 2 2), IsKakeyaSet K → 3 ≤ K.card := by
  decide

/-- Exact value: the minimum Kakeya size over `(ZMod 2)²` is three. -/
theorem minKakeyaSize_two_two : minKakeyaSize 2 2 = 3 := by
  refine le_antisymm ?_ ?_
  · have h := minKakeyaSize_le_card twoTwoKakeyaWitness_isKakeyaSet
    rwa [twoTwoKakeyaWitness_card] at h
  · obtain ⟨K, hK, hcard⟩ := exists_minKakeyaSize_witness 2 2
    rw [← hcard]
    exact three_le_card_of_twoTwo_isKakeyaSet K hK

/-- The line at parameter one passes through anchor plus direction. -/
theorem residueLine_one {N n : ℕ} (a b : ResiduePoint N n) :
    residueLine a b 1 = a + b := by
  funext i
  simp [residueLine]

/-- Pair-counting bound for mod-2 Kakeya sets, all dimensions at once:
`2^n - 1 ≤ (K.card).choose 2`. -/
theorem pow_sub_one_le_choose_of_isKakeyaSet {n : ℕ}
    {K : Finset (ResiduePoint 2 n)} (hK : IsKakeyaSet K) :
    2 ^ n - 1 ≤ Nat.choose K.card 2 := by
  classical
  choose anchor hanchor using hK
  have hxx : ∀ x : ZMod 2, x + x = 0 := by decide
  have hchar : ∀ x y : ZMod 2, x + (x + y) = y := by decide
  have hne : ∀ b : ResiduePoint 2 n, b ≠ 0 →
      anchor b ≠ anchor b + b := by
    intro b hb heq
    apply hb
    funext i
    have h : anchor b i = anchor b i + b i := congrFun heq i
    have hc := hchar (anchor b i) (b i)
    rw [← h, hxx] at hc
    exact hc.symm
  have key : (Finset.univ.filter
      (fun b : ResiduePoint 2 n => b ≠ 0)).card ≤
      (K.powersetCard 2).card := by
    refine Finset.card_le_card_of_injOn
      (fun b => ({anchor b, anchor b + b} : Finset _)) ?_ ?_
    · intro b hb
      have hb0 : b ≠ 0 :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
      show ({anchor b, anchor b + b} : Finset _) ∈
        ↑(K.powersetCard 2)
      rw [Finset.mem_powersetCard]
      constructor
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact residueLine_zero (anchor b) b ▸ hanchor b 0
        · rw [Finset.mem_singleton] at hx'
          subst hx'
          exact residueLine_one (anchor b) b ▸ hanchor b 1
      · exact Finset.card_pair (hne b hb0)
    · intro b hb b' hb' heq
      have hb0 : b ≠ 0 :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
      have hb0' : b' ≠ 0 :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp hb')).2
      have hsum : ∀ c : ResiduePoint 2 n, c ≠ 0 →
          (({anchor c, anchor c + c} : Finset _)).sum id = c := by
        intro c hc0
        rw [Finset.sum_pair (hne c hc0)]
        funext i
        exact hchar (anchor c i) (c i)
      have heq' : ({anchor b, anchor b + b} : Finset _) =
          ({anchor b', anchor b' + b'} : Finset _) := heq
      calc b = ({anchor b, anchor b + b} : Finset _).sum id :=
            (hsum b hb0).symm
        _ = ({anchor b', anchor b' + b'} : Finset _).sum id := by
            rw [heq']
        _ = b' := hsum b' hb0'
  have hdirs : (Finset.univ.filter
      (fun b : ResiduePoint 2 n => b ≠ 0)).card = 2 ^ n - 1 := by
    rw [Finset.filter_ne',
      Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [Finset.card_powersetCard] at key
  rw [hdirs] at key
  exact key

/-- No five-point set is Kakeya over `(ZMod 2)⁴`: pair counting demands
fifteen distinct pairs and five points supply only ten. -/
theorem six_le_card_of_twoFour_isKakeyaSet
    {K : Finset (ResiduePoint 2 4)} (hK : IsKakeyaSet K) :
    6 ≤ K.card := by
  have h := pow_sub_one_le_choose_of_isKakeyaSet hK
  have h15 : (2 : ℕ) ^ 4 - 1 = 15 := by norm_num
  rw [h15] at h
  by_contra hlt
  rw [Nat.not_le] at hlt
  have hmono : Nat.choose K.card 2 ≤ Nat.choose 5 2 :=
    Nat.choose_le_choose 2 (by omega)
  have h52 : Nat.choose 5 2 = 10 := by decide
  omega


variable {N n : ℕ} [NeZero N]

/-- `S` carries a full line in direction `b`: some anchor's entire
parametrized line lies inside `S`.  For `K` a Kakeya set this holds for
every `b` by definition; here it is the per-subset, per-direction atom
that the fractional cost condition prices. -/
def CarriesLine (S : Finset (ResiduePoint N n)) (b : ResiduePoint N n) :
    Prop :=
  ∃ a : ResiduePoint N n, ∀ t : ZMod N, residueLine a b t ∈ S

/-- Decidability of line-carrying, by finite search over anchors and
parameters — this is what makes the fractional cost condition a
kernel-checkable certificate. -/
instance (S : Finset (ResiduePoint N n)) (b : ResiduePoint N n) :
    Decidable (CarriesLine S b) :=
  inferInstanceAs
    (Decidable (∃ a : ResiduePoint N n, ∀ t : ZMod N,
      residueLine a b t ∈ S))

omit [NeZero N] in
/-- A Kakeya set carries a line in every direction; definitional
bridge between the Kakeya predicate and the per-direction atom. -/
theorem isKakeyaSet_iff_forall_carriesLine
    {K : Finset (ResiduePoint N n)} :
    IsKakeyaSet K ↔ ∀ b, CarriesLine K b :=
  Iff.rfl

/--
THE FRACTIONAL COST CONDITION at direction menu `Dirs` and price `m`:
every subset `S` of the small factor pays at least price `m` per menu
direction it fully carries, relative to budget `|S| * |Dirs|`:

`#(carried menu directions) * m ≤ |S| * |Dirs|`.

This is a FINITE condition on `(ZMod N)^n` alone — no mention of any
co-factor — and it is decidable, so specific instances are kernel
certificates.  It is exactly the affordability condition that makes the
slice double count close: rearranged over rationals it says the
per-direction cost of `S` is at least `m / |Dirs|`, i.e., the
LP-relaxed covering price of the small factor is met by every
configuration.
-/
def FractionalCostAt (N n : ℕ) [NeZero N]
    (Dirs : Finset (ResiduePoint N n)) (m : ℕ) : Prop :=
  ∀ S : Finset (ResiduePoint N n),
    (Dirs.filter fun b => CarriesLine S b).card * m ≤ S.card * Dirs.card

/-- Decidability of the fractional cost condition: the quantifier
ranges over the finite powerset of the small factor, so specific
instances are kernel certificates.  Registered explicitly because
instance search does not unfold the definition. -/
instance (N n : ℕ) [NeZero N] (Dirs : Finset (ResiduePoint N n))
    (m : ℕ) : Decidable (FractionalCostAt N n Dirs m) :=
  inferInstanceAs
    (Decidable (∀ S : Finset (ResiduePoint N n),
      (Dirs.filter fun b => CarriesLine S b).card * m ≤
        S.card * Dirs.card))

/-- The canonical direction menu: all nonzero directions. -/
def nonzeroDirections (N n : ℕ) [NeZero N] : Finset (ResiduePoint N n) :=
  Finset.univ.filter fun b => b ≠ 0


/-! ## The general slice transport

The `(2,3,2)` slice argument,
generalized verbatim to EVERY coprime pair `N₁, N₂` and EVERY
dimension `n`.  Nothing here
is specific to small numbers; the Chinese remainder line-product
structure is all that is used.
-/


variable {N₁ N₂ n : ℕ} [NeZero N₁] [NeZero N₂]

/-- The fiber of a composite-modulus set over a mod-`N₂` slice point:
the elements whose Chinese remainder second component is the given
slice. -/
def crtSliceFiber (h : N₁.Coprime N₂)
    (K : Finset (ResiduePoint (N₁ * N₂) n)) (y : ResiduePoint N₂ n) :
    Finset (ResiduePoint (N₁ * N₂) n) :=
  K.filter fun k => (crtPointEquiv h k).2 = y

/-- The mod-`N₁` carrier of a slice: the first Chinese remainder
components of the fiber's elements. -/
def crtSliceCarrier (h : N₁.Coprime N₂)
    (K : Finset (ResiduePoint (N₁ * N₂) n)) (y : ResiduePoint N₂ n) :
    Finset (ResiduePoint N₁ n) :=
  (crtSliceFiber h K y).image fun k => (crtPointEquiv h k).1

/-- The slices whose carrier holds a full line in the mod-`N₁`
direction `b₁`.  The transport theorem below shows this set is Kakeya
over the CO-FACTOR — the engine of the transfer. -/
def crtCarrierSlices (h : N₁.Coprime N₂)
    (K : Finset (ResiduePoint (N₁ * N₂) n)) (b₁ : ResiduePoint N₁ n) :
    Finset (ResiduePoint N₂ n) :=
  Finset.univ.filter fun y => CarriesLine (crtSliceCarrier h K y) b₁

/--
SLICE TRANSPORT: for `K` Kakeya over the composite modulus and ANY
mod-`N₁` direction `b₁`, the `b₁`-carrier slices form a Kakeya set over
`(ZMod N₂)^n`.

Given a mod-`N₂` direction `b₂`, take the global Kakeya line in the
Chinese-remainder-combined direction `(b₁, b₂)`; because the parameter
ring itself splits through the same isomorphism, the transported line
is the FULL PRODUCT of a `b₁`-line and a `b₂`-line.  Every point of the
`b₂`-line is therefore a slice whose carrier contains the same
`b₁`-line.  This generalizes the `(2,3,2)` special case with no new
ideas — the generality was already latent in `crtPointEquiv_residueLine`.
-/
theorem crtCarrierSlices_isKakeyaSet (h : N₁.Coprime N₂)
    {K : Finset (ResiduePoint (N₁ * N₂) n)} (hK : IsKakeyaSet K)
    (b₁ : ResiduePoint N₁ n) :
    IsKakeyaSet (crtCarrierSlices h K b₁) := by
  intro b₂
  obtain ⟨a, ha⟩ := hK ((crtPointEquiv h).symm (b₁, b₂))
  refine ⟨(crtPointEquiv h a).2, fun t₂ => ?_⟩
  rw [crtCarrierSlices, Finset.mem_filter]
  refine ⟨Finset.mem_univ _,
    (crtPointEquiv h a).1, fun t₁ => ?_⟩
  rw [crtSliceCarrier, Finset.mem_image]
  refine ⟨residueLine a ((crtPointEquiv h).symm (b₁, b₂))
    ((ZMod.chineseRemainder h).symm (t₁, t₂)), ?_, ?_⟩
  · rw [crtSliceFiber, Finset.mem_filter]
    refine ⟨ha _, ?_⟩
    rw [crtPointEquiv_residueLine]
    simp
  · rw [crtPointEquiv_residueLine]
    simp

/--
THE CORE COUNTING THEOREM (the new half, at set level): a fractional
cost certificate on the small factor prices every composite-modulus
Kakeya set from below by `m * minKakeyaSize N₂ n`.

Proof shape, all in `ℕ` (no rational division):
1. each menu direction's carrier slices are Kakeya over the co-factor,
   so number at least `minKakeyaSize N₂ n` — slice transport;
2. summing carrier-slice counts over the menu equals summing carried
   menu counts over slices — the double count (`Finset.sum_comm`);
3. the fractional cost condition prices each slice's carried count
   against its carrier size;
4. carriers are images of fibers, and fiber sizes partition `|K|`.
-/
theorem mul_le_card_of_isKakeyaSet_of_fractionalCostAt
    (h : N₁.Coprime N₂) {K : Finset (ResiduePoint (N₁ * N₂) n)}
    (hK : IsKakeyaSet K) {Dirs : Finset (ResiduePoint N₁ n)}
    (hDirs : Dirs.Nonempty) {m : ℕ}
    (hfc : FractionalCostAt N₁ n Dirs m) :
    m * minKakeyaSize N₂ n ≤ K.card := by
  classical
  -- 1. transport: every menu direction's carrier slices are Kakeya
  --    over the co-factor, hence bounded below by its minimum.
  have hT : ∀ b₁ ∈ Dirs,
      minKakeyaSize N₂ n ≤ (crtCarrierSlices h K b₁).card := fun b₁ _ =>
    minKakeyaSize_le_card (crtCarrierSlices_isKakeyaSet h hK b₁)
  have hsum : Dirs.card * minKakeyaSize N₂ n ≤
      ∑ b₁ ∈ Dirs, (crtCarrierSlices h K b₁).card := by
    have hh := Finset.card_nsmul_le_sum Dirs
      (fun b₁ => (crtCarrierSlices h K b₁).card)
      (minKakeyaSize N₂ n) hT
    simpa [smul_eq_mul] using hh
  -- 2. double count: menu-indexed slice counts = slice-indexed menu
  --    counts.
  have hdc : ∑ b₁ ∈ Dirs, (crtCarrierSlices h K b₁).card =
      ∑ y : ResiduePoint N₂ n,
        (Dirs.filter fun b₁ => y ∈ crtCarrierSlices h K b₁).card := by
    calc ∑ b₁ ∈ Dirs, (crtCarrierSlices h K b₁).card
        = ∑ b₁ ∈ Dirs, ∑ y : ResiduePoint N₂ n,
            if y ∈ crtCarrierSlices h K b₁ then 1 else 0 := by
          refine Finset.sum_congr rfl fun b₁ _ => ?_
          rw [← Finset.card_filter]
          congr 1
          ext y
          simp
      _ = ∑ y : ResiduePoint N₂ n, ∑ b₁ ∈ Dirs,
            if y ∈ crtCarrierSlices h K b₁ then 1 else 0 :=
          Finset.sum_comm
      _ = ∑ y : ResiduePoint N₂ n,
            (Dirs.filter fun b₁ => y ∈ crtCarrierSlices h K b₁).card := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.card_filter]
  -- 3. pricing: per slice, the carried menu count times the price is
  --    within the carrier's budget (the fractional cost certificate,
  --    after translating slice membership into line-carrying).
  have hcost : ∀ y : ResiduePoint N₂ n,
      (Dirs.filter fun b₁ => y ∈ crtCarrierSlices h K b₁).card * m ≤
      (crtSliceCarrier h K y).card * Dirs.card := by
    intro y
    have hsub : (Dirs.filter fun b₁ => y ∈ crtCarrierSlices h K b₁) =
        Dirs.filter fun b₁ => CarriesLine (crtSliceCarrier h K y) b₁ := by
      refine Finset.filter_congr fun b₁ _ => ?_
      simp [crtCarrierSlices]
    rw [hsub]
    exact hfc (crtSliceCarrier h K y)
  -- 4. carriers are images of fibers; fibers partition the set.
  have himg : ∀ y : ResiduePoint N₂ n,
      (crtSliceCarrier h K y).card ≤ (crtSliceFiber h K y).card :=
    fun y => Finset.card_image_le
  have hpart : ∑ y : ResiduePoint N₂ n,
      (crtSliceFiber h K y).card = K.card :=
    (Finset.card_eq_sum_card_fiberwise fun k _ =>
      Finset.mem_univ ((crtPointEquiv h k).2)).symm
  -- assemble the chain and cancel the (positive) menu size.
  have hchain : Dirs.card * minKakeyaSize N₂ n * m ≤
      K.card * Dirs.card := by
    calc Dirs.card * minKakeyaSize N₂ n * m
        ≤ (∑ b₁ ∈ Dirs, (crtCarrierSlices h K b₁).card) * m :=
          Nat.mul_le_mul_right _ hsum
      _ = (∑ y : ResiduePoint N₂ n,
            (Dirs.filter fun b₁ =>
              y ∈ crtCarrierSlices h K b₁).card) * m := by rw [hdc]
      _ = ∑ y : ResiduePoint N₂ n,
            (Dirs.filter fun b₁ =>
              y ∈ crtCarrierSlices h K b₁).card * m :=
          Finset.sum_mul _ _ _
      _ ≤ ∑ y : ResiduePoint N₂ n,
            (crtSliceCarrier h K y).card * Dirs.card :=
          Finset.sum_le_sum fun y _ => hcost y
      _ ≤ ∑ y : ResiduePoint N₂ n,
            (crtSliceFiber h K y).card * Dirs.card :=
          Finset.sum_le_sum fun y _ =>
            Nat.mul_le_mul_right _ (himg y)
      _ = (∑ y : ResiduePoint N₂ n,
            (crtSliceFiber h K y).card) * Dirs.card :=
          (Finset.sum_mul _ _ _).symm
      _ = K.card * Dirs.card := by rw [hpart]
  have hpos : 0 < Dirs.card := Finset.card_pos.mpr hDirs
  have hfin : Dirs.card * (m * minKakeyaSize N₂ n) ≤
      Dirs.card * K.card := by
    calc Dirs.card * (m * minKakeyaSize N₂ n)
        = Dirs.card * minKakeyaSize N₂ n * m := by ring
      _ ≤ K.card * Dirs.card := hchain
      _ = Dirs.card * K.card := Nat.mul_comm _ _
  exact Nat.le_of_mul_le_mul_left hfin hpos

/--
THE ≥ HALF OF THE TRANSFER: a fractional cost certificate at price `m`
on the small factor forces `m * minKakeyaSize N₂ n` as a lower bound on
the composite minimum, for EVERY coprime co-factor `N₂`.

This is the direction that appears unrecorded in the literature
reviewed to date: the product UPPER bound is a construction (known
shape — see the module docstring); this is a certificate-driven lower
bound that quantifies over all co-factors at once.
-/
theorem mul_le_minKakeyaSize_of_fractionalCostAt
    (h : N₁.Coprime N₂) {Dirs : Finset (ResiduePoint N₁ n)}
    (hDirs : Dirs.Nonempty) {m : ℕ}
    (hfc : FractionalCostAt N₁ n Dirs m) :
    m * minKakeyaSize N₂ n ≤ minKakeyaSize (N₁ * N₂) n := by
  haveI : NeZero (N₁ * N₂) :=
    ⟨Nat.mul_ne_zero (NeZero.ne N₁) (NeZero.ne N₂)⟩
  obtain ⟨K, hK, hcard⟩ := exists_minKakeyaSize_witness (N₁ * N₂) n
  rw [← hcard]
  exact mul_le_card_of_isKakeyaSet_of_fractionalCostAt h hK hDirs hfc

/--
THE EXACTNESS TRANSFER THEOREM.  If the small factor certifies the
fractional cost condition AT ITS TRUE MINIMUM PRICE, then the Kakeya
minimum is EXACTLY multiplicative against every coprime co-factor:

`minKakeyaSize (N₁ * N₂) n = minKakeyaSize N₁ n * minKakeyaSize N₂ n`.

One finite kernel check on `(ZMod N₁)^n` closes infinitely many
composite cells.  The `≤` half is the product construction
(known shape); the `≥` half is `mul_le_minKakeyaSize_of_fractionalCostAt`.
-/
theorem minKakeyaSize_mul_eq_of_fractionalCostAt
    (h : N₁.Coprime N₂) {Dirs : Finset (ResiduePoint N₁ n)}
    (hDirs : Dirs.Nonempty)
    (hfc : FractionalCostAt N₁ n Dirs (minKakeyaSize N₁ n)) :
    minKakeyaSize (N₁ * N₂) n =
      minKakeyaSize N₁ n * minKakeyaSize N₂ n :=
  le_antisymm (minKakeyaSize_mul_le h n)
    (mul_le_minKakeyaSize_of_fractionalCostAt h hDirs hfc)


/-! ## Certificates and the infinite exact families in dimension two -/

/-- The mod-2 plane's nonzero direction menu is nonempty. -/
theorem nonzeroDirections_two_two_nonempty :
    (nonzeroDirections 2 2).Nonempty := by
  decide

/-- CERTIFICATE: the mod-2 plane satisfies the fractional cost
condition at price 3 over the nonzero menu.  Kernel-decided over all
16 subsets — this single finite check drives the entire odd-`M`
family below. -/
theorem fractionalCostAt_two_two :
    FractionalCostAt 2 2 (nonzeroDirections 2 2) 3 := by
  decide

/-- The certificate holds at the true minimum price (`min(2,2) = 3`). -/
theorem fractionalCost_two_two_at_min :
    FractionalCostAt 2 2 (nonzeroDirections 2 2) (minKakeyaSize 2 2) := by
  rw [minKakeyaSize_two_two]
  exact fractionalCostAt_two_two

/--
INFINITE EXACT FAMILY, mod-2 base: for EVERY odd modulus `M`,

`minKakeyaSize (2 * M) 2 = 3 * minKakeyaSize M 2`.

Infinitely many composite cells, each an exact-multiplicativity
statement, from one 16-subset kernel certificate.
-/
theorem minKakeyaSize_two_mul_dim_two (M : ℕ) [NeZero M]
    (hM : Nat.Coprime 2 M) :
    minKakeyaSize (2 * M) 2 = 3 * minKakeyaSize M 2 := by
  have h := minKakeyaSize_mul_eq_of_fractionalCostAt (N₁ := 2) (N₂ := M)
    hM nonzeroDirections_two_two_nonempty fractionalCost_two_two_at_min
  rwa [minKakeyaSize_two_two] at h

/-- The mod-3 plane's nonzero direction menu is nonempty. -/
theorem nonzeroDirections_three_two_nonempty :
    (nonzeroDirections 3 2).Nonempty := by
  decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1600000 in
/-- CERTIFICATE: the mod-3 plane satisfies the fractional cost
condition at price 7 over the nonzero menu.  Kernel-decided over all
512 subsets of the 9-point plane. -/
theorem fractionalCostAt_three_two :
    FractionalCostAt 3 2 (nonzeroDirections 3 2) 7 := by
  decide

/-- Explicit seven-point Kakeya witness in `(ZMod 3)²`: two full columns
and one extra point.  Located by external search, re-verified by the
kernel below. -/
def threeTwoKakeyaWitness : Finset (ResiduePoint 3 2) :=
  {fun _ => 0,
   fun i => if i = 0 then 0 else 1,
   fun i => if i = 0 then 0 else 2,
   fun i => if i = 0 then 1 else 0,
   fun i => if i = 0 then 1 else 1,
   fun i => if i = 0 then 1 else 2,
   fun i => if i = 0 then 2 else 0}

/-- The witness is a Kakeya set (kernel-decided). -/
theorem threeTwoKakeyaWitness_isKakeyaSet :
    IsKakeyaSet threeTwoKakeyaWitness := by
  decide

/-- The witness has exactly seven points. -/
theorem threeTwoKakeyaWitness_card : threeTwoKakeyaWitness.card = 7 := by
  decide

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8000 in
/-- No six-point set is Kakeya over `(ZMod 3)²`: kernel-decided over all
`2^9 = 512` subsets.  This is the Blokhuis-Mazzocca value at `q = 3`,
re-proved from scratch by finite quantification. -/
theorem seven_le_card_of_threeTwo_isKakeyaSet :
    ∀ K : Finset (ResiduePoint 3 2), IsKakeyaSet K → 7 ≤ K.card := by
  decide

/-- Exact value: the minimum Kakeya size over `(ZMod 3)²` is seven. -/
theorem minKakeyaSize_three_two : minKakeyaSize 3 2 = 7 := by
  refine le_antisymm ?_ ?_
  · have h := minKakeyaSize_le_card threeTwoKakeyaWitness_isKakeyaSet
    rwa [threeTwoKakeyaWitness_card] at h
  · obtain ⟨K, hK, hcard⟩ := exists_minKakeyaSize_witness 3 2
    rw [← hcard]
    exact seven_le_card_of_threeTwo_isKakeyaSet K hK

/-- The mod-3 certificate holds at the true minimum price
(`min(3,2) = 7`, matching the Blokhuis–Mazzocca value). -/
theorem fractionalCost_three_two_at_min :
    FractionalCostAt 3 2 (nonzeroDirections 3 2) (minKakeyaSize 3 2) := by
  rw [minKakeyaSize_three_two]
  exact fractionalCostAt_three_two

/-- INFINITE EXACT FAMILY, mod-3 base: for every `M` coprime to 3,
`minKakeyaSize (3 * M) 2 = 7 * minKakeyaSize M 2`. -/
theorem minKakeyaSize_three_mul_dim_two (M : ℕ) [NeZero M]
    (hM : Nat.Coprime 3 M) :
    minKakeyaSize (3 * M) 2 = 7 * minKakeyaSize M 2 := by
  have h := minKakeyaSize_mul_eq_of_fractionalCostAt (N₁ := 3) (N₂ := M)
    hM nonzeroDirections_three_two_nonempty fractionalCost_three_two_at_min
  rwa [minKakeyaSize_three_two] at h

/--
CHAINED FAMILY: for every `M` coprime to 6,

`minKakeyaSize (6 * M) 2 = 21 * minKakeyaSize M 2`.

Both certificates fire in sequence: split off the 2, then the 3.  Every
squarefree modulus with smallest prime factors 2 and 3 now reduces
exactly to its remaining prime cells in dimension two.
-/
theorem minKakeyaSize_six_mul_dim_two (M : ℕ) [NeZero M]
    (hM : Nat.Coprime 6 M) :
    minKakeyaSize (6 * M) 2 = 21 * minKakeyaSize M 2 := by
  have h2M : Nat.Coprime 2 M :=
    Nat.Coprime.coprime_dvd_left (by norm_num) hM
  have h3M : Nat.Coprime 3 M :=
    Nat.Coprime.coprime_dvd_left (by norm_num) hM
  have h23 : Nat.Coprime 2 3 := by decide
  have h23M : Nat.Coprime 2 (3 * M) := Nat.Coprime.mul_right h23 h2M
  haveI : NeZero (3 * M) :=
    ⟨Nat.mul_ne_zero (by norm_num) (NeZero.ne M)⟩
  calc minKakeyaSize (6 * M) 2
      = minKakeyaSize (2 * (3 * M)) 2 := by
        rw [show (6 : ℕ) * M = 2 * (3 * M) by ring]
    _ = 3 * minKakeyaSize (3 * M) 2 :=
        minKakeyaSize_two_mul_dim_two (3 * M) h23M
    _ = 3 * (7 * minKakeyaSize M 2) := by
        rw [minKakeyaSize_three_mul_dim_two M h3M]
    _ = 21 * minKakeyaSize M 2 := by ring

/-- The transfer route re-derives the first composite value: the
`M = 3` instance of the mod-2 family. -/
theorem exactnessTransfer_recovers_six_two :
    minKakeyaSize 6 2 = 3 * minKakeyaSize 3 2 :=
  minKakeyaSize_two_mul_dim_two 3 (by decide)

/-- SECOND PROOF of `minKakeyaSize 6 2 = 21`: through the class
theorem, independent of the direct slice count that first established
it.  The two routes agree — an internal consistency control. -/
theorem minKakeyaSize_six_two_via_transfer : minKakeyaSize 6 2 = 21 := by
  rw [exactnessTransfer_recovers_six_two, minKakeyaSize_three_two]


/-! ## The dimension-three frontier: failure at the true price,
transfer at a discounted price, and the open-cell sandwich -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 800000 in
/-- FRONTIER NEGATIVE: in dimension three the fractional cost condition
FAILS at the true minimum price 5 (the affine simplex carries six of
the seven nonzero directions with only four points).  This is the
formal reason a mod-2-priced slice argument cannot close the `(6,3)`
cell, and why its exact value is open. -/
theorem not_fractionalCostAt_two_three_at_five :
    ¬ FractionalCostAt 2 3 (nonzeroDirections 2 3) 5 := by
  decide

/-- The five-point witness for `(ZMod 2)³`: the affine simplex plus the
all-ones point — a perfect five-point Kakeya set in the mod-2
three-space. -/
def twoThreeKakeyaWitness : Finset (ResiduePoint 2 3) :=
  {fun _ => 0,
   fun i => if i = 0 then 1 else 0,
   fun i => if i = 1 then 1 else 0,
   fun i => if i = 2 then 1 else 0,
   fun _ => 1}

/-- The witness is a Kakeya set (kernel-decided). -/
theorem twoThreeKakeyaWitness_isKakeyaSet :
    IsKakeyaSet twoThreeKakeyaWitness := by
  decide

/-- The witness has exactly five points. -/
theorem twoThreeKakeyaWitness_card : twoThreeKakeyaWitness.card = 5 := by
  decide

/-- No four-point set is Kakeya over `(ZMod 2)³`: the
pair-counting class bound above demands
`7 ≤ C(card, 2)` and four
points supply only six pairs.  Cross-axis consumption: the DIMENSION
module's class theorem anchors the MODULUS module's open-cell
sandwich. -/
theorem five_le_card_of_twoThree_isKakeyaSet
    {K : Finset (ResiduePoint 2 3)} (hK : IsKakeyaSet K) :
    5 ≤ K.card := by
  have h := pow_sub_one_le_choose_of_isKakeyaSet hK
  have h7 : (2 : ℕ) ^ 3 - 1 = 7 := by norm_num
  rw [h7] at h
  by_contra hlt
  rw [Nat.not_le] at hlt
  have hmono : Nat.choose K.card 2 ≤ Nat.choose 4 2 :=
    Nat.choose_le_choose 2 (by omega)
  have h42 : Nat.choose 4 2 = 6 := by decide
  omega

/-- Exact anchor: `minKakeyaSize 2 3 = 5`. -/
theorem minKakeyaSize_two_three : minKakeyaSize 2 3 = 5 := by
  refine le_antisymm ?_ ?_
  · have h := minKakeyaSize_le_card twoThreeKakeyaWitness_isKakeyaSet
    rwa [twoThreeKakeyaWitness_card] at h
  · obtain ⟨K, hK, hcard⟩ := exists_minKakeyaSize_witness 2 3
    rw [← hcard]
    exact five_le_card_of_twoThree_isKakeyaSet hK

/-! ## Generic line lemmas

Small facts about `residueLine` used throughout: negation invariance of
line-carrying, reanchoring a full line at any of its points, and
injectivity of the parametrization over the prime modulus `3`.  Stated
at the generality they naturally hold at. -/


variable {N n : ℕ}

/-- Carrying a line in direction `-b` is the same as in direction `b`:
the parametrized point sets coincide (reparametrize `t ↦ -t`).  This is
the direction-pairing that halves the menu count below. -/
theorem carriesLine_neg {S : Finset (ResiduePoint N n)}
    {b : ResiduePoint N n} :
    CarriesLine S (-b) ↔ CarriesLine S b := by
  -- Pointwise reparametrization; stated coordinatewise because the
  -- pointwise `Pi` scalar action and the module-level `smul` lemmas
  -- live on different instance paths.
  have key : ∀ (a : ResiduePoint N n) (t : ZMod N),
      residueLine a (-b) t = residueLine a b (-t) := by
    intro a t
    funext i
    simp only [residueLine, Pi.add_apply, Pi.smul_apply, Pi.neg_apply,
      smul_eq_mul]
    ring
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, fun t => ?_⟩
    have h := ha (-t)
    rw [key, neg_neg] at h
    exact h
  · rintro ⟨a, ha⟩
    refine ⟨a, fun t => ?_⟩
    rw [key]
    exact ha (-t)

/-- REANCHORING: if the `b`-line through `a` lies in `S`, so does the
`b`-line through any of its points — the two parametrizations differ by
a parameter shift.  This is what lets incidence counts run over the
points of a witness line rather than its anchor. -/
theorem carriesLine_reanchor {S : Finset (ResiduePoint N n)}
    {a b : ResiduePoint N n}
    (ha : ∀ t, residueLine a b t ∈ S) (s : ZMod N) :
    ∀ t, residueLine (residueLine a b s) b t ∈ S := by
  intro t
  have h : residueLine (residueLine a b s) b t = residueLine a b (s + t) := by
    funext i
    simp only [residueLine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h]
  exact ha (s + t)

/-- Right cancellation by a nonzero factor over `ZMod 3`, settled by
kernel enumeration to avoid threading the primality `Fact` instance. -/
theorem zmod3_mul_right_cancel :
    ∀ x t t' : ZMod 3, x ≠ 0 → t * x = t' * x → t = t' := by
  decide

/-- Over the prime modulus `3` a line in a nonzero direction is
injectively parametrized: `t • b` determines `t` once some coordinate
of `b` is a unit, which over the field `ZMod 3` is any nonzero
coordinate.  Consequently every full line has exactly three points —
the nondegeneracy all the counting below rests on. -/
theorem residueLine_injective_three {n : ℕ} {a b : ResiduePoint 3 n}
    (hb : b ≠ 0) : Function.Injective (residueLine a b) := by
  intro t t' h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hb
  have h1 := congrFun h i
  simp only [residueLine, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1
  exact zmod3_mul_right_cancel (b i) t t' hi (add_left_cancel h1)


/-! ## The family transversal

The 26 nonzero directions of `(ZMod 3)³` pair into 13 families
`{b, -b}` with identical line geometry.  `classReps` is the concrete
lead-coefficient-one transversal; all its bookkeeping is settled by
kernel `decide` on the 27-point space. -/


/-- The canonical family representatives: nonzero directions whose
first nonzero coordinate is `1`.  Exactly one per family `{b, -b}`
(the other member has first nonzero coordinate `2 = -1`). -/
def classReps : Finset (ResiduePoint 3 3) :=
  Finset.univ.filter fun b =>
    b 0 = 1 ∨ (b 0 = 0 ∧ b 1 = 1) ∨ (b 0 = 0 ∧ b 1 = 0 ∧ b 2 = 1)

/-- Thirteen families: `9 + 3 + 1` by leading position. -/
theorem classReps_card : classReps.card = 13 := by decide

/-- Representatives are genuine directions (nonzero). -/
theorem classReps_subset_nonzero :
    classReps ⊆ nonzeroDirections 3 3 := by decide

/-- No family is represented twice: the negative of a representative is
never itself a representative (its lead coefficient is `2`). -/
theorem classReps_not_neg_mem :
    ∀ b ∈ classReps, -b ∉ classReps := by decide

/-- The menu decomposes as the transversal and its pointwise negation:
every nonzero direction is a representative or the negative of one. -/
theorem nonzeroDirections_eq_reps_union_neg :
    nonzeroDirections 3 3 =
      classReps ∪ classReps.image (fun b => -b) := by decide

/-- The transversal and its negation are disjoint. -/
theorem classReps_disjoint_neg :
    Disjoint classReps (classReps.image (fun b => -b)) :=
  Finset.disjoint_left.mpr (by decide)

/-- Membership in the transversal forces a nonzero direction — the
form used pointwise by the counting layer. -/
theorem mem_classReps_ne_zero {b : ResiduePoint 3 3}
    (hb : b ∈ classReps) : b ≠ 0 := by
  have h := classReps_subset_nonzero hb
  simp only [nonzeroDirections, Finset.mem_filter] at h
  exact h.2

/--
THE FAMILY COUNT: the number of direction families in which `S` carries
a full line, counted on the transversal.  This is the quantity the
whole campaign bounds by `S.card`.
-/
def classCount (S : Finset (ResiduePoint 3 3)) : ℕ :=
  (classReps.filter fun b => CarriesLine S b).card

/-- The 26-direction menu count is exactly twice the family count:
split the menu along the transversal decomposition and transport the
negated half through `carriesLine_neg`. -/
theorem carried_menu_card_eq_two_mul_classCount
    (S : Finset (ResiduePoint 3 3)) :
    ((nonzeroDirections 3 3).filter fun b => CarriesLine S b).card =
      2 * classCount S := by
  classical
  rw [nonzeroDirections_eq_reps_union_neg, Finset.filter_union,
    Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter classReps_disjoint_neg),
    Finset.filter_image]
  have himg :
      ((classReps.filter fun b => CarriesLine S (-b)).image
        (fun b => -b)).card =
      (classReps.filter fun b => CarriesLine S b).card := by
    rw [Finset.card_image_of_injective _ neg_injective]
    exact congrArg Finset.card
      (Finset.filter_congr fun b _ => by
        simp only [carriesLine_neg])
  rw [himg, classCount, two_mul]

/-- THE REDUCTION OF RECORD: the `(3,3)` fractional cost certificate at
price 13 is exactly the family-count bound `classCount S ≤ |S|` for
every subset.  All later milestones prove the right-hand side. -/
theorem fractionalCostAt_three_three_iff_classCount_le :
    FractionalCostAt 3 3 (nonzeroDirections 3 3) 13 ↔
      ∀ S : Finset (ResiduePoint 3 3), classCount S ≤ S.card := by
  have hmenu : (nonzeroDirections 3 3).card = 26 := by decide
  constructor
  · intro h S
    have hS := h S
    rw [carried_menu_card_eq_two_mul_classCount, hmenu] at hS
    omega
  · intro h S
    rw [carried_menu_card_eq_two_mul_classCount, hmenu]
    have hS := h S
    omega


/-! ## The counting layer

Two counting facts drive the whole lower-bound argument.

* PENCIL BOUND: for `p ∈ S`, the families whose full line THROUGH `p`
  lies in `S` consume pairwise disjoint pairs `{p+b, p-b}` of
  `S \ {p}`, so twice their number is at most `|S| - 1`.
* INCIDENCE BOUND: every carried family places its full line's three
  distinct points in `S`, and by reanchoring each of those points sees
  the family in its own pencil, so `3·classCount S ≤ Σ_{p∈S} μ_p`.

Together: `3·classCount S ≤ Σ_p ⌊(|S|-1)/2⌋`, which already closes
every `|S| ≤ 8` (there `μ_p ≤ 3`, so `classCount ≤ |S|`). -/


/-- The PENCIL at `p`: the families (on the transversal) whose full
line through `p` lies inside `S`.  By reanchoring this is the natural
per-point localization of the family count. -/
def linePencil (S : Finset (ResiduePoint 3 3)) (p : ResiduePoint 3 3) :
    Finset (ResiduePoint 3 3) :=
  classReps.filter fun b => ∀ t : ZMod 3, residueLine p b t ∈ S

/-- Scalar bookkeeping for the disjointness case split: a nonzero
parameter over `ZMod 3` is `1` or `2`. -/
theorem zmod3_nonzero_cases :
    ∀ u : ZMod 3, u ≠ 0 → u = 1 ∨ u = 2 := by
  decide

/-- Doubling by `2 = -1`: the other point of a line through `p` in
direction `b` is the antipode `p - b`.  Char-3 fact used to convert the
scalar case `ratio = 2` into a family collision. -/
theorem two_smul_eq_neg (b : ResiduePoint 3 3) :
    (2 : ZMod 3) • b = -b := by
  funext i
  have h2 : (2 : ZMod 3) = -1 := by decide
  simp [Pi.smul_apply, smul_eq_mul, h2]

/--
THE PENCIL BOUND: `2·μ_p ≤ |S| - 1`.  Each pencil family `b` owns the
two-point set `{p+b, p+2b} ⊆ S \ {p}`; distinct transversal families
own disjoint sets, because a shared point forces the directions to
agree up to a unit scalar — either equal (excluded) or mutual negatives
(excluded by the transversal normalization).
-/
theorem two_mul_linePencil_card_le {S : Finset (ResiduePoint 3 3)}
    {p : ResiduePoint 3 3} (hp : p ∈ S) :
    2 * (linePencil S p).card ≤ S.card - 1 := by
  classical
  set f : ResiduePoint 3 3 → Finset (ResiduePoint 3 3) :=
    fun b => {residueLine p b 1, residueLine p b 2} with hf
  -- Each family's pair sits inside `S` minus the center.
  have hsub : ∀ b ∈ linePencil S p, f b ⊆ S.erase p := by
    intro b hb x hx
    obtain ⟨hbrep, hbline⟩ := Finset.mem_filter.mp hb
    have hinj := residueLine_injective_three (a := p)
      (mem_classReps_ne_zero hbrep)
    have hne : ∀ s : ZMod 3, s ≠ 0 → residueLine p b s ≠ p := by
      intro s hs h
      exact hs (hinj (h.trans (residueLine_zero p b).symm))
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_erase.mpr ⟨hne 1 (by decide), hbline 1⟩
    · rw [Finset.mem_singleton] at hx
      subst hx
      exact Finset.mem_erase.mpr ⟨hne 2 (by decide), hbline 2⟩
  -- Distinct pencil families own disjoint pairs.
  have hdisj : ∀ b ∈ linePencil S p, ∀ b' ∈ linePencil S p, b ≠ b' →
      Disjoint (f b) (f b') := by
    intro b hb b' hb' hne
    obtain ⟨hbrep, _⟩ := Finset.mem_filter.mp hb
    obtain ⟨hb'rep, _⟩ := Finset.mem_filter.mp hb'
    rw [Finset.disjoint_left]
    intro x hxb hxb'
    -- Extract the two nonzero parameters placing `x` on both lines.
    have hget : ∀ c : ResiduePoint 3 3, x ∈ f c →
        ∃ s : ZMod 3, s ≠ 0 ∧ x = residueLine p c s := by
      intro c hx
      rcases Finset.mem_insert.mp hx with h | h
      · exact ⟨1, by decide, h⟩
      · rw [Finset.mem_singleton] at h
        exact ⟨2, by decide, h⟩
    obtain ⟨s, hs0, hxs⟩ := hget b hxb
    obtain ⟨s', hs'0, hxs'⟩ := hget b' hxb'
    -- The shared point equates the scaled directions.
    have hsb : s • b = s' • b' :=
      add_left_cancel ((hxs.symm.trans hxs') : p + s • b = p + s' • b')
    -- Case on the two possible nonzero scalars on each side: the
    -- directions agree exactly or up to negation.
    have hbb' : b' = b ∨ b' = -b := by
      rcases zmod3_nonzero_cases s hs0 with rfl | rfl <;>
        rcases zmod3_nonzero_cases s' hs'0 with rfl | rfl
      · rw [one_smul, one_smul] at hsb
        exact Or.inl hsb.symm
      · rw [one_smul, two_smul_eq_neg] at hsb
        exact Or.inr (by rw [hsb, neg_neg])
      · rw [one_smul, two_smul_eq_neg] at hsb
        exact Or.inr hsb.symm
      · rw [two_smul_eq_neg, two_smul_eq_neg] at hsb
        exact Or.inl (neg_injective hsb).symm
    rcases hbb' with hbb' | hbb'
    · exact hne hbb'.symm
    · rw [hbb'] at hb'rep
      exact classReps_not_neg_mem b hbrep hb'rep
  -- Each pair genuinely has two points.
  have hcard2 : ∀ b ∈ linePencil S p, (f b).card = 2 := by
    intro b hb
    obtain ⟨hbrep, _⟩ := Finset.mem_filter.mp hb
    have hinj := residueLine_injective_three (a := p)
      (mem_classReps_ne_zero hbrep)
    exact Finset.card_pair fun h =>
      (by decide : (1 : ZMod 3) ≠ 2) (hinj h)
  -- Assemble: disjoint union of 2-sets inside the punctured window.
  calc 2 * (linePencil S p).card
      = ∑ b ∈ linePencil S p, (f b).card := by
        rw [Finset.sum_congr rfl hcard2, Finset.sum_const,
          smul_eq_mul, mul_comm]
    _ = ((linePencil S p).biUnion f).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (S.erase p).card :=
        Finset.card_le_card (Finset.biUnion_subset.mpr hsub)
    _ = S.card - 1 := Finset.card_erase_of_mem hp

/--
THE INCIDENCE BOUND: `3·classCount S ≤ Σ_{p∈S} μ_p`.  Double count
incidences between points of `S` and pencil families: every carried
family contributes its witness line's three distinct points, each of
which sees the family in its own pencil by reanchoring.
-/
theorem three_mul_classCount_le_sum_linePencil
    (S : Finset (ResiduePoint 3 3)) :
    3 * classCount S ≤ ∑ p ∈ S, (linePencil S p).card := by
  classical
  -- Swap the double count to per-family incidence columns.
  have hswap : ∑ p ∈ S, (linePencil S p).card =
      ∑ b ∈ classReps,
        (S.filter fun p => ∀ t : ZMod 3, residueLine p b t ∈ S).card := by
    simp only [linePencil, Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap, classCount, Finset.card_filter, Finset.mul_sum]
  refine Finset.sum_le_sum fun b hb => ?_
  by_cases hc : CarriesLine S b
  · simp only [hc, if_true, mul_one]
    obtain ⟨a, ha⟩ := hc
    have hinj := residueLine_injective_three (a := a)
      (mem_classReps_ne_zero hb)
    -- The witness line's three points all lie in the incidence column.
    have himg : (Finset.univ : Finset (ZMod 3)).image (residueLine a b) ⊆
        S.filter fun p => ∀ t : ZMod 3, residueLine p b t ∈ S := by
      intro x hx
      obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_filter.mpr ⟨ha s, carriesLine_reanchor ha s⟩
    calc 3 = ((Finset.univ : Finset (ZMod 3)).image
              (residueLine a b)).card := by
              rw [Finset.card_image_of_injective _ hinj]
              decide
      _ ≤ _ := Finset.card_le_card himg
  · simp [hc]

/-- SMALL WINDOWS CLOSED: for `|S| ≤ 8` the pencil bound caps every
`μ_p` at `3` (integrality: `2μ ≤ 7`), so the incidence bound gives
`3·classCount ≤ 3·|S|` outright.  Together with the trivial `≥ 13`
case this leaves only `|S| ∈ {9,…,12}` for the star endgame. -/
theorem classCount_le_card_of_card_le_eight
    {S : Finset (ResiduePoint 3 3)} (h : S.card ≤ 8) :
    classCount S ≤ S.card := by
  have hsum := three_mul_classCount_le_sum_linePencil S
  have hbound : ∀ p ∈ S, (linePencil S p).card ≤ 3 := by
    intro p hp
    have hpencil := two_mul_linePencil_card_le hp
    omega
  have htotal : ∑ p ∈ S, (linePencil S p).card ≤ 3 * S.card := by
    calc ∑ p ∈ S, (linePencil S p).card ≤ ∑ _p ∈ S, 3 :=
          Finset.sum_le_sum hbound
      _ = 3 * S.card := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
  omega

/-- LARGE WINDOWS CLOSED: there are only 13 families in total. -/
theorem classCount_le_thirteen (S : Finset (ResiduePoint 3 3)) :
    classCount S ≤ 13 := by
  calc classCount S ≤ classReps.card := Finset.card_filter_le _ _
    _ = 13 := classReps_card


/-! ## The gauge layer

Translations and linear automorphisms of `(ZMod 3)³` preserve both the
cardinality and the family count of a configuration.  This is what
collapses the star endgame's configuration space to kernel size: a
high-multiplicity point can be moved to the origin and an independent
triple of its pencil directions to the standard basis, so the residual
case analysis quantifies over a few thousand concrete configurations
instead of `2^27` subsets.

The family count transports through the 26-direction menu (a linear
automorphism permutes directions but not the transversal pointwise),
using the `×2` bridge on both sides. -/


/-- Line-carrying is translation invariant, direction fixed. -/
theorem carriesLine_image_add (S : Finset (ResiduePoint 3 3))
    (v b : ResiduePoint 3 3) :
    CarriesLine (S.image (fun x => x + v)) b ↔ CarriesLine S b := by
  -- Both directions shift the anchor; coordinatewise `ring` again
  -- avoids the module/pointwise instance mismatch.
  have hline : ∀ (a : ResiduePoint 3 3) (t : ZMod 3),
      residueLine (a + v) b t = residueLine a b t + v := by
    intro a t
    funext i
    simp only [residueLine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hline' : ∀ (a : ResiduePoint 3 3) (t : ZMod 3),
      residueLine (a - v) b t = residueLine a b t - v := by
    intro a t
    funext i
    simp only [residueLine, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a - v, fun t => ?_⟩
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp (ha t)
    have hxeq : residueLine (a - v) b t = x := by
      rw [hline']
      exact (eq_sub_of_add_eq hxe).symm
    rw [hxeq]
    exact hx
  · rintro ⟨a, ha⟩
    refine ⟨a + v, fun t => ?_⟩
    rw [hline]
    exact Finset.mem_image_of_mem _ (ha t)

/-- The family count is translation invariant. -/
theorem classCount_image_add (S : Finset (ResiduePoint 3 3))
    (v : ResiduePoint 3 3) :
    classCount (S.image (fun x => x + v)) = classCount S := by
  unfold classCount
  exact congrArg Finset.card (Finset.filter_congr fun b _ => by
    rw [carriesLine_image_add])

/-- Line-carrying transports along a linear automorphism, with the
direction transported the same way. -/
theorem carriesLine_image_linearEquiv
    (g : ResiduePoint 3 3 ≃ₗ[ZMod 3] ResiduePoint 3 3)
    (S : Finset (ResiduePoint 3 3)) (b : ResiduePoint 3 3) :
    CarriesLine (S.image g) (g b) ↔ CarriesLine S b := by
  have hline : ∀ (a : ResiduePoint 3 3) (t : ZMod 3),
      residueLine (g a) (g b) t = g (residueLine a b t) := by
    intro a t
    simp only [residueLine, map_add, map_smul]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨g.symm a, fun t => ?_⟩
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp (ha t)
    have h2 : residueLine a (g b) t = g (residueLine (g.symm a) b t) := by
      rw [← hline, g.apply_symm_apply]
    have hx2 : x = residueLine (g.symm a) b t :=
      g.injective (hxe.trans h2)
    rw [← hx2]
    exact hx
  · rintro ⟨a, ha⟩
    refine ⟨g a, fun t => ?_⟩
    rw [hline]
    exact Finset.mem_image_of_mem _ (ha t)

/-- A linear automorphism permutes the direction menu. -/
theorem nonzeroDirections_image_linearEquiv
    (g : ResiduePoint 3 3 ≃ₗ[ZMod 3] ResiduePoint 3 3) :
    (nonzeroDirections 3 3).image g = nonzeroDirections 3 3 := by
  ext b
  simp only [nonzeroDirections, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact fun h => hx (g.map_eq_zero_iff.mp h)
  · intro hb
    refine ⟨g.symm b, fun h => hb ?_, g.apply_symm_apply b⟩
    rw [← g.apply_symm_apply b, h, map_zero]

/-- THE GAUGE THEOREM for the family count: linear automorphisms
preserve it.  Proved on the 26-direction menu — where the automorphism
acts by permutation — and pulled back through the `×2` bridge. -/
theorem classCount_image_linearEquiv
    (g : ResiduePoint 3 3 ≃ₗ[ZMod 3] ResiduePoint 3 3)
    (S : Finset (ResiduePoint 3 3)) :
    classCount (S.image g) = classCount S := by
  have h26 : ((nonzeroDirections 3 3).filter fun b =>
      CarriesLine (S.image g) b).card =
      ((nonzeroDirections 3 3).filter fun b => CarriesLine S b).card := by
    conv_lhs => rw [← nonzeroDirections_image_linearEquiv g]
    rw [Finset.filter_image,
      Finset.card_image_of_injective _ g.injective]
    exact congrArg Finset.card (Finset.filter_congr fun b _ => by
      rw [carriesLine_image_linearEquiv])
  have h1 := carried_menu_card_eq_two_mul_classCount (S.image g)
  have h2 := carried_menu_card_eq_two_mul_classCount S
  omega

/-- PIGEONHOLE: a violating configuration has a point of pencil
multiplicity at least four.  If every pencil had at most three
families, the incidence bound would cap the family count at `|S|`. -/
theorem exists_pencil_card_ge_four {S : Finset (ResiduePoint 3 3)}
    (hviol : S.card + 1 ≤ classCount S) :
    ∃ p ∈ S, 4 ≤ (linePencil S p).card := by
  by_contra hall
  have hall' : ∀ p ∈ S, (linePencil S p).card ≤ 3 := by
    intro p hp
    by_contra h4
    exact hall ⟨p, hp, by omega⟩
  have hsum := three_mul_classCount_le_sum_linePencil S
  have htotal : ∑ p ∈ S, (linePencil S p).card ≤ 3 * S.card := by
    calc ∑ p ∈ S, (linePencil S p).card ≤ ∑ _p ∈ S, 3 :=
          Finset.sum_le_sum hall'
      _ = 3 * S.card := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
  omega


/-! ## Star normalization

A violating window has a point whose pencil holds four distinct
families.  This section builds the normalizing gauge: the center moves
to the origin (translation), and either three pencil directions are
linearly independent — mapped to the standard basis, leaving one free
rep and the extra points as the only unknowns (case A) — or all pencil
directions lie in a common plane, which the four concurrent lines then
cover entirely, mapped to the concrete `z = 0` plane (case B).  The
span bookkeeping runs through a concrete 9-element combination window
(`spanPairFinset`) rather than abstract submodules, so every concrete
side condition stays kernel-checkable. -/


open Module

/-- `3` is prime — local `Fact` so `ZMod 3` is a field for the
independence and basis machinery. -/
private instance fact_prime_three : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

/-- The standard basis directions, in kernel-friendly form. -/
def stdDir (i : Fin 3) : ResiduePoint 3 3 :=
  fun j => if j = i then 1 else 0

/-- Parameter case split over `ZMod 3`. -/
theorem zmod3_cases : ∀ t : ZMod 3, t = 0 ∨ t = 1 ∨ t = 2 := by decide

/-- The 9-element combination window of two directions — the concrete
stand-in for `span {x, y}` that keeps the case split and its side
conditions kernel-checkable. -/
def spanPairFinset (x y : ResiduePoint 3 3) :
    Finset (ResiduePoint 3 3) :=
  (Finset.univ : Finset (ZMod 3 × ZMod 3)).image fun st =>
    st.1 • x + st.2 • y

theorem mem_spanPairFinset {x y z : ResiduePoint 3 3} :
    z ∈ spanPairFinset x y ↔ ∃ s t : ZMod 3, s • x + t • y = z := by
  simp only [spanPairFinset, Finset.mem_image, Finset.mem_univ, true_and,
    Prod.exists]

/-- THE TRIPLE CRITERION: extending an independent pair by `z` is
independent exactly when `z` avoids the combination window.  This is
`linearIndependent_finCons` with the span translated to the concrete
window through `Submodule.mem_span_pair`. -/
theorem linearIndependent_triple_iff {x y z : ResiduePoint 3 3}
    (hxy : LinearIndependent (ZMod 3) ![x, y]) :
    LinearIndependent (ZMod 3) ![z, x, y] ↔ z ∉ spanPairFinset x y := by
  -- `linearIndependent_finCons`, consumed at the term level: the
  -- `![z,x,y] = Fin.cons z ![x,y]` identification and the instance
  -- paths are handled by definitional unfolding, never by `rw`.
  have hfc : LinearIndependent (ZMod 3)
        (Fin.cons z ![x, y] : Fin 3 → ResiduePoint 3 3) ↔
      LinearIndependent (ZMod 3) ![x, y] ∧
        z ∉ Submodule.span (ZMod 3)
          (Set.range (![x, y] : Fin 2 → ResiduePoint 3 3)) :=
    linearIndependent_finCons
  have hrange : Set.range (![x, y] : Fin 2 → ResiduePoint 3 3) =
      {x, y} := by
    ext w
    simp [eq_comm, or_comm]
  have hspan : z ∈ Submodule.span (ZMod 3)
        (Set.range (![x, y] : Fin 2 → ResiduePoint 3 3)) ↔
      z ∈ spanPairFinset x y := by
    rw [hrange, Submodule.mem_span_pair, mem_spanPairFinset]
  constructor
  · intro h hmem
    exact (hfc.mp h).2 (hspan.mpr hmem)
  · intro hz
    exact hfc.mpr ⟨hxy, fun hmem => hz (hspan.mp hmem)⟩

/-- Distinct transversal representatives are linearly independent:
proportionality over `ZMod 3` means equality or negation, both
excluded by the transversal normalization. -/
theorem classReps_pair_linearIndependent {x y : ResiduePoint 3 3}
    (hx : x ∈ classReps) (hy : y ∈ classReps) (hne : x ≠ y) :
    LinearIndependent (ZMod 3) ![x, y] := by
  -- The `fin2` criterion, again consumed at the term level; the
  -- component goals are moved onto `x`/`y` by `show` (definitional).
  have h1 : (![x, y] : Fin 2 → ResiduePoint 3 3) 1 ≠ 0 := by
    show y ≠ 0
    exact mem_classReps_ne_zero hy
  have h2 : ∀ a : ZMod 3,
      a • (![x, y] : Fin 2 → ResiduePoint 3 3) 1 ≠ ![x, y] 0 := by
    intro a ha
    have ha' : a • y = x := ha
    by_cases ha0 : a = 0
    · subst ha0
      rw [zero_smul] at ha'
      exact mem_classReps_ne_zero hx ha'.symm
    · rcases zmod3_nonzero_cases a ha0 with rfl | rfl
      · rw [one_smul] at ha'
        exact hne ha'.symm
      · rw [two_smul_eq_neg] at ha'
        rw [← ha'] at hx
        exact classReps_not_neg_mem y hy hx
  exact linearIndependent_fin2.mpr ⟨h1, h2⟩

/-- The standard target triple `(e₂, e₀, e₁)` is independent: the pair
through the transversal pair criterion (the standard directions are
representatives — kernel-checked), the extension by a kernel-checked
window exclusion. -/
theorem stdTriple_linearIndependent :
    LinearIndependent (ZMod 3) ![stdDir 2, stdDir 0, stdDir 1] := by
  have hpair : LinearIndependent (ZMod 3) ![stdDir 0, stdDir 1] :=
    classReps_pair_linearIndependent (by decide) (by decide) (by decide)
  exact (linearIndependent_triple_iff hpair).mpr (by decide)

/-- The basis presented by an independent triple.  The rank side
condition is discharged inside the expected instance context, so no
cross-path `finrank` unification ever runs. -/
noncomputable def tripleBasis {x y z : ResiduePoint 3 3}
    (h : LinearIndependent (ZMod 3) ![z, x, y]) :
    Basis (Fin 3) (ZMod 3) (ResiduePoint 3 3) :=
  basisOfLinearIndependentOfCardEqFinrank h
    (by rw [Module.finrank_fintype_fun_eq_card])

theorem tripleBasis_coe {x y z : ResiduePoint 3 3}
    (h : LinearIndependent (ZMod 3) ![z, x, y]) :
    ⇑(tripleBasis h) = ![z, x, y] :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _

/-- THE NORMALIZING GAUGE: the linear automorphism sending an
independent triple `(z, x, y)` to the standard triple `(e₂, e₀, e₁)`.
Only its existence and its values on the triple are consumed. -/
noncomputable def gaugeEquiv {x y z : ResiduePoint 3 3}
    (h : LinearIndependent (ZMod 3) ![z, x, y]) :
    ResiduePoint 3 3 ≃ₗ[ZMod 3] ResiduePoint 3 3 :=
  (tripleBasis h).equiv (tripleBasis stdTriple_linearIndependent)
    (Equiv.refl _)

theorem gaugeEquiv_apply {x y z : ResiduePoint 3 3}
    (h : LinearIndependent (ZMod 3) ![z, x, y]) (i : Fin 3) :
    gaugeEquiv h (![z, x, y] i) = ![stdDir 2, stdDir 0, stdDir 1] i := by
  have h1 : (![z, x, y] : Fin 3 → ResiduePoint 3 3) i =
      (tripleBasis h) i := (congrFun (tripleBasis_coe h) i).symm
  simp only [gaugeEquiv]
  rw [h1, Basis.equiv_apply, Equiv.refl_apply]
  exact congrFun (tripleBasis_coe stdTriple_linearIndependent) i

/-- Gauge values on the triple, in consumable form. -/
theorem gaugeEquiv_fst {x y z : ResiduePoint 3 3}
    (h : LinearIndependent (ZMod 3) ![z, x, y]) :
    gaugeEquiv h z = stdDir 2 :=
  gaugeEquiv_apply h 0

theorem gaugeEquiv_snd {x y z : ResiduePoint 3 3}
    (h : LinearIndependent (ZMod 3) ![z, x, y]) :
    gaugeEquiv h x = stdDir 0 :=
  gaugeEquiv_apply h 1

theorem gaugeEquiv_trd {x y z : ResiduePoint 3 3}
    (h : LinearIndependent (ZMod 3) ![z, x, y]) :
    gaugeEquiv h y = stdDir 1 :=
  gaugeEquiv_apply h 2

/-- The full line through the origin in direction `b`. -/
def lineThrough0 (b : ResiduePoint 3 3) : Finset (ResiduePoint 3 3) :=
  (Finset.univ : Finset (ZMod 3)).image fun t => residueLine 0 b t

/-- Antipodal directions trace the same origin line. -/
theorem lineThrough0_neg (b : ResiduePoint 3 3) :
    lineThrough0 (-b) = lineThrough0 b := by
  have key : ∀ t : ZMod 3, residueLine 0 (-b) t = residueLine 0 b (-t) := by
    intro t
    funext i
    simp only [residueLine, Pi.add_apply, Pi.smul_apply, Pi.neg_apply,
      Pi.zero_apply, smul_eq_mul]
    ring
  unfold lineThrough0
  ext w
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨-t, (key t).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨-t, by rw [key, neg_neg]⟩

/-- Membership form of the origin line. -/
theorem lineThrough0_subset_iff {b : ResiduePoint 3 3}
    {S : Finset (ResiduePoint 3 3)} :
    lineThrough0 b ⊆ S ↔ ∀ t : ZMod 3, residueLine 0 b t ∈ S := by
  unfold lineThrough0
  constructor
  · intro h t
    exact h (Finset.mem_image_of_mem _ (Finset.mem_univ t))
  · intro h w hw
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hw
    exact h t

/-- Pencil membership survives translating the center to the origin. -/
theorem linePencil_translate {S : Finset (ResiduePoint 3 3)}
    {p b : ResiduePoint 3 3} (hb : b ∈ linePencil S p) :
    b ∈ linePencil (S.image (fun x => x + (-p))) 0 := by
  obtain ⟨hrep, hline⟩ := Finset.mem_filter.mp hb
  refine Finset.mem_filter.mpr ⟨hrep, fun t => ?_⟩
  have h : residueLine 0 b t = residueLine p b t + (-p) := by
    funext i
    simp only [residueLine, Pi.add_apply, Pi.smul_apply, Pi.neg_apply,
      Pi.zero_apply, smul_eq_mul]
    ring
  rw [h]
  exact Finset.mem_image_of_mem _ (hline t)

/-- Origin lines transport through a linear automorphism. -/
theorem lineThrough0_image_linearEquiv
    (g : ResiduePoint 3 3 ≃ₗ[ZMod 3] ResiduePoint 3 3)
    {S : Finset (ResiduePoint 3 3)} {b : ResiduePoint 3 3}
    (hb : ∀ t : ZMod 3, residueLine 0 b t ∈ S) :
    ∀ t : ZMod 3, residueLine 0 (g b) t ∈ S.image g := by
  intro t
  have h : residueLine 0 (g b) t = g (residueLine 0 b t) := by
    simp only [residueLine, map_add, map_smul, map_zero]
  rw [h]
  exact Finset.mem_image_of_mem _ (hb t)

set_option maxHeartbeats 1600000 in
/-- Every direction's family meets the transversal: itself or its
negation is a representative. -/
theorem exists_classRep :
    ∀ v ∈ nonzeroDirections 3 3, ∃ r ∈ classReps, r = v ∨ r = -v := by
  decide

/-- Direction menu membership is just nonvanishing. -/
theorem mem_nonzeroDirections_iff {b : ResiduePoint 3 3} :
    b ∈ nonzeroDirections 3 3 ↔ b ≠ 0 := by
  simp [nonzeroDirections]


/-! ## The fast carrier predicate

The endgame decides evaluate the family count on thousands of concrete
configurations; this predicate anchors the line search inside the
window and only tests the two nonzero parameters, cutting the kernel
cost per check.  It is proved equivalent to `CarriesLine` — the
authority always flows back through the bridge. -/


/-- Anchored two-parameter carrier check. -/
def CarriesLineFast (S : Finset (ResiduePoint 3 3))
    (b : ResiduePoint 3 3) : Prop :=
  ∃ p ∈ S, residueLine p b 1 ∈ S ∧ residueLine p b 2 ∈ S

instance (S : Finset (ResiduePoint 3 3)) (b : ResiduePoint 3 3) :
    Decidable (CarriesLineFast S b) :=
  inferInstanceAs (Decidable (∃ p ∈ S, _ ∧ _))

/-- The fast check is the real carrier predicate: the anchor is on the
line (parameter `0`), and three parameters exhaust `ZMod 3`. -/
theorem carriesLineFast_iff {S : Finset (ResiduePoint 3 3)}
    {b : ResiduePoint 3 3} :
    CarriesLineFast S b ↔ CarriesLine S b := by
  constructor
  · rintro ⟨p, hp, h1, h2⟩
    refine ⟨p, fun t => ?_⟩
    rcases zmod3_cases t with rfl | rfl | rfl
    · rw [residueLine_zero]
      exact hp
    · exact h1
    · exact h2
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_, ha 1, ha 2⟩
    rw [← residueLine_zero a b]
    exact ha 0

/-- Family count over the fast predicate — the quantity the endgame
decides actually evaluate. -/
def classCountFast (S : Finset (ResiduePoint 3 3)) : ℕ :=
  (classReps.filter fun b => CarriesLineFast S b).card

theorem classCountFast_eq (S : Finset (ResiduePoint 3 3)) :
    classCountFast S = classCount S :=
  congrArg Finset.card (Finset.filter_congr fun b _ => by
    rw [carriesLineFast_iff])


/-! ## The index world

The endgame decides evaluate `classCount` on thousands of concrete
configurations.  Doing that on `Finset (Fin 3 → ZMod 3)` is hopeless
for the kernel — every membership test re-runs `ZMod` arithmetic
through towers of instance projections (measured: 18 configurations
≈ 21 minutes).  This section re-expresses the check over `Fin 27`
(base-3 digit encoding) where addition is plain `Nat` div/mod
arithmetic — kernel-accelerated — and memberships are single `Nat`
comparisons.  The bridge back to the real predicates is structural and
one-time: digit-roundtrip and addition-transport facts settled by
small decides, then `carriesIdx`/`classCountIdx` proved equivalent to
the real predicates for every window at once.  Authority always flows
through the bridge; the index world is an evaluation strategy, not a
new definition of truth. -/


/-- Base-3 digit encoding of a point. -/
def toIdx (p : ResiduePoint 3 3) : Fin 27 :=
  ⟨(p 0).val + 3 * (p 1).val + 9 * (p 2).val, by
    have h0 : (p 0).val < 3 := ZMod.val_lt (p 0)
    have h1 : (p 1).val < 3 := ZMod.val_lt (p 1)
    have h2 : (p 2).val < 3 := ZMod.val_lt (p 2)
    omega⟩

/-- Digit decoding. -/
def ofIdx (k : Fin 27) : ResiduePoint 3 3 :=
  ![((k.val % 3 : ℕ) : ZMod 3), ((k.val / 3 % 3 : ℕ) : ZMod 3),
    ((k.val / 9 : ℕ) : ZMod 3)]

theorem ofIdx_toIdx : ∀ p : ResiduePoint 3 3, ofIdx (toIdx p) = p := by
  decide

theorem toIdx_ofIdx : ∀ k : Fin 27, toIdx (ofIdx k) = k := by decide

theorem toIdx_injective : Function.Injective toIdx := by
  intro p q h
  rw [← ofIdx_toIdx p, ← ofIdx_toIdx q, h]

/-- Membership transport along the encoding. -/
theorem mem_image_toIdx {S : Finset (ResiduePoint 3 3)}
    {p : ResiduePoint 3 3} :
    toIdx p ∈ S.image toIdx ↔ p ∈ S := by
  constructor
  · intro h
    obtain ⟨q, hq, he⟩ := Finset.mem_image.mp h
    rw [← toIdx_injective he]
    exact hq
  · exact Finset.mem_image_of_mem _

/-- Index-world addition: digitwise mod-3 on the base-3 digits, in raw
`Nat` div/mod arithmetic (kernel-accelerated). -/
def addIdx (a b : Fin 27) : Fin 27 :=
  ⟨(a.val % 3 + b.val % 3) % 3 +
    ((a.val / 3 % 3 + b.val / 3 % 3) % 3) * 3 +
    ((a.val / 9 + b.val / 9) % 3) * 9, by omega⟩

/-- Index-world doubling — which in characteristic three is also the
negation: `-b = 2b = b + b`. -/
def dblIdx (d : Fin 27) : Fin 27 := addIdx d d

/-- THE ADDITION BRIDGE: the encoding is additive.  One 729-case
kernel check ties every index-world evaluation back to the carrier. -/
theorem toIdx_add :
    ∀ p q : ResiduePoint 3 3, toIdx (p + q) = addIdx (toIdx p) (toIdx q) := by
  decide

/-- Characteristic-three negation as self-addition, on the carrier. -/
theorem neg_eq_add_self_res (b : ResiduePoint 3 3) : -b = b + b := by
  funext i
  have h : ∀ x : ZMod 3, -x = x + x := by decide
  exact h (b i)

theorem toIdx_neg (b : ResiduePoint 3 3) :
    toIdx (-b) = dblIdx (toIdx b) := by
  rw [neg_eq_add_self_res, toIdx_add]
  rfl

/-- Line evaluation at parameter two as double-addition
(`residueLine_one` from the pair-counting section above covers
parameter one). -/
theorem residueLine_two (p b : ResiduePoint 3 3) :
    residueLine p b 2 = p + (b + b) := by
  funext i
  simp only [residueLine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Index-world carrier check — the object the endgame decides
evaluate. -/
def carriesIdx (S : Finset (Fin 27)) (d : Fin 27) : Prop :=
  ∃ p ∈ S, addIdx p d ∈ S ∧ addIdx p (dblIdx d) ∈ S

instance (S : Finset (Fin 27)) (d : Fin 27) :
    Decidable (carriesIdx S d) :=
  inferInstanceAs (Decidable (∃ p ∈ S, _ ∧ _))

/-- THE CARRIER BRIDGE: the index-world check evaluates the real
carrier predicate on the encoded window. -/
theorem carriesIdx_iff {S : Finset (ResiduePoint 3 3)}
    {b : ResiduePoint 3 3} :
    carriesIdx (S.image toIdx) (toIdx b) ↔ CarriesLineFast S b := by
  constructor
  · rintro ⟨pi, hpi, h1, h2⟩
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hpi
    refine ⟨p, hp, ?_, ?_⟩
    · rw [residueLine_one]
      rw [← toIdx_add] at h1
      exact mem_image_toIdx.mp h1
    · rw [residueLine_two]
      rw [show dblIdx (toIdx b) = toIdx (b + b) by
            rw [toIdx_add]; rfl,
          ← toIdx_add] at h2
      exact mem_image_toIdx.mp h2
  · rintro ⟨p, hp, h1, h2⟩
    refine ⟨toIdx p, Finset.mem_image_of_mem _ hp, ?_, ?_⟩
    · rw [← toIdx_add, ← residueLine_one]
      exact mem_image_toIdx.mpr h1
    · rw [show dblIdx (toIdx b) = toIdx (b + b) by
            rw [toIdx_add]; rfl,
          ← toIdx_add, ← residueLine_two]
      exact mem_image_toIdx.mpr h2

/-- The transversal, encoded (`9 + 3 + 1` literals, kernel-checked
against the image of the real transversal). -/
def classRepsIdx : Finset (Fin 27) :=
  {1, 4, 7, 10, 13, 16, 19, 22, 25, 3, 12, 21, 9}

theorem classRepsIdx_eq : classReps.image toIdx = classRepsIdx := by decide

/-- Index-world family count. -/
def classCountIdx (S : Finset (Fin 27)) : ℕ :=
  (classRepsIdx.filter fun d => carriesIdx S d).card

/-- THE COUNT BRIDGE: the index-world count is the real family count
of the encoded window. -/
theorem classCountIdx_image (S : Finset (ResiduePoint 3 3)) :
    classCountIdx (S.image toIdx) = classCount S := by
  rw [← classCountFast_eq]
  unfold classCountIdx classCountFast
  rw [← classRepsIdx_eq, Finset.filter_image,
    Finset.card_image_of_injective _ toIdx_injective]
  exact congrArg Finset.card (Finset.filter_congr fun b _ => by
    rw [carriesIdx_iff])

/-- The origin line, encoded. -/
def lineIdx0 (d : Fin 27) : Finset (Fin 27) := {0, d, dblIdx d}

/-- The origin line on the carrier is the zero/point/double triple. -/
theorem lineThrough0_eq_triple (b : ResiduePoint 3 3) :
    lineThrough0 b = {0, b, b + b} := by
  unfold lineThrough0
  have huniv : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  rw [huniv]
  simp only [Finset.image_insert, Finset.image_singleton,
    residueLine_zero, residueLine_one, residueLine_two, zero_add]

theorem toIdx_zero : toIdx 0 = 0 := by decide

/-- Origin lines encode to origin lines. -/
theorem lineThrough0_image_toIdx (b : ResiduePoint 3 3) :
    (lineThrough0 b).image toIdx = lineIdx0 (toIdx b) := by
  rw [lineThrough0_eq_triple]
  simp only [Finset.image_insert, Finset.image_singleton, toIdx_zero,
    lineIdx0]
  rw [show toIdx (b + b) = dblIdx (toIdx b) by rw [toIdx_add]; rfl]

/-- The `z = 0` plane and its direction set, encoded (base-3 indices
below `9`). -/
def zPlaneIdx : Finset (Fin 27) := {0, 1, 2, 3, 4, 5, 6, 7, 8}

def zPlaneDirsIdx : Finset (Fin 27) := {1, 2, 3, 4, 5, 6, 7, 8}

/-- Nonzero plane vectors encode into the plane direction set. -/
theorem toIdx_mem_zPlaneDirsIdx :
    ∀ v : ResiduePoint 3 3, v ≠ 0 → v 2 = 0 →
      toIdx v ∈ zPlaneDirsIdx := by
  decide

/-- The standard star: the three axis lines plus one free line. -/
def stdStarIdx (d : Fin 27) : Finset (Fin 27) :=
  lineIdx0 1 ∪ lineIdx0 3 ∪ lineIdx0 9 ∪ lineIdx0 d

/-- The ten free representatives (transversal minus the axes). -/
def freeRepsIdx : Finset (Fin 27) :=
  classRepsIdx \ {1, 3, 9}

/-- Encoded standard directions. -/
theorem toIdx_stdDir_zero : toIdx (stdDir 0) = 1 := by decide
theorem toIdx_stdDir_one : toIdx (stdDir 1) = 3 := by decide
theorem toIdx_stdDir_two : toIdx (stdDir 2) = 9 := by decide

/-- Free stars have exactly nine points (four concurrent lines in
distinct classes). -/
theorem stdStarIdx_card : ∀ d ∈ freeRepsIdx, (stdStarIdx d).card = 9 := by
  decide

theorem zPlaneIdx_card : zPlaneIdx.card = 9 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12800000 in
/-- CASE-B COVERAGE: four concurrent plane lines in pairwise distinct
classes cover the whole plane.  `dblIdx` is index-world negation, so
the side condition is exactly class-distinctness.  Kernel-only
reduction (`+kernel`): the elaborator's slow preview pass is skipped —
same proof term, same authority. -/
theorem four_plane_classes_cover :
    ∀ D ∈ zPlaneDirsIdx.powersetCard 4, (∀ d ∈ D, dblIdx d ∉ D) →
      D.biUnion lineIdx0 = zPlaneIdx := by
  decide +kernel


set_option maxHeartbeats 0 in
/-- Case B, `u = 9`: the bare plane. -/
theorem endgame_caseB_nine :
    ∀ extras ∈ ((Finset.univ : Finset (Fin 27)) \ zPlaneIdx).powersetCard 0,
      classCountIdx (zPlaneIdx ∪ extras) ≤ 9 := by
  decide +kernel

set_option maxHeartbeats 0 in
/-- Case B, `u = 10`: plane plus one point. -/
theorem endgame_caseB_ten :
    ∀ extras ∈ ((Finset.univ : Finset (Fin 27)) \ zPlaneIdx).powersetCard 1,
      classCountIdx (zPlaneIdx ∪ extras) ≤ 10 := by
  decide +kernel

set_option maxHeartbeats 0 in
/-- Case B, `u = 11`: plane plus two points. -/
theorem endgame_caseB_eleven :
    ∀ extras ∈ ((Finset.univ : Finset (Fin 27)) \ zPlaneIdx).powersetCard 2,
      classCountIdx (zPlaneIdx ∪ extras) ≤ 11 := by
  decide +kernel

set_option maxHeartbeats 0 in
/-- Case B, `u = 12`: plane plus three points. -/
theorem endgame_caseB_twelve :
    ∀ extras ∈ ((Finset.univ : Finset (Fin 27)) \ zPlaneIdx).powersetCard 3,
      classCountIdx (zPlaneIdx ∪ extras) ≤ 12 := by
  decide +kernel

/-! ## Case A: the star cores -/

set_option maxHeartbeats 0 in
/-- Case A, `u = 9`: the bare four-line star. -/
theorem endgame_caseA_nine :
    ∀ d ∈ freeRepsIdx,
      ∀ extras ∈ ((Finset.univ : Finset (Fin 27)) \ stdStarIdx d).powersetCard 0,
        classCountIdx (stdStarIdx d ∪ extras) ≤ 9 := by
  decide +kernel

set_option maxHeartbeats 0 in
/-- Case A, `u = 10`: star plus one point. -/
theorem endgame_caseA_ten :
    ∀ d ∈ freeRepsIdx,
      ∀ extras ∈ ((Finset.univ : Finset (Fin 27)) \ stdStarIdx d).powersetCard 1,
        classCountIdx (stdStarIdx d ∪ extras) ≤ 10 := by
  decide +kernel

set_option maxHeartbeats 0 in
/-- Case A, `u = 11`: star plus two points. -/
theorem endgame_caseA_eleven :
    ∀ d ∈ freeRepsIdx,
      ∀ extras ∈ ((Finset.univ : Finset (Fin 27)) \ stdStarIdx d).powersetCard 2,
        classCountIdx (stdStarIdx d ∪ extras) ≤ 11 := by
  decide +kernel

set_option maxHeartbeats 0 in
/-- Case A, `u = 12`: star plus three points — the largest check
(`10 × C(18,3) = 8160` configurations). -/
theorem endgame_caseA_twelve :
    ∀ d ∈ freeRepsIdx,
      ∀ extras ∈ ((Finset.univ : Finset (Fin 27)) \ stdStarIdx d).powersetCard 3,
        classCountIdx (stdStarIdx d ∪ extras) ≤ 12 := by
  decide +kernel

/-- ENDGAME CLOSER: a window of violating size whose encoding contains
a 9-point normalized core, with the core's kernel-established count
ceilings, cannot exist.  Shared by both normalization cases. -/
private theorem endgame_absurd {S₂ : Finset (ResiduePoint 3 3)}
    {core : Finset (Fin 27)}
    (hcore_sub : core ⊆ S₂.image toIdx)
    (hcore_card : core.card = 9)
    (hbound : ∀ k : ℕ, k ≤ 3 →
      ∀ extras ∈ ((Finset.univ : Finset (Fin 27)) \ core).powersetCard k,
        classCountIdx (core ∪ extras) ≤ 9 + k)
    (hcard9 : 9 ≤ S₂.card) (hcard12 : S₂.card ≤ 12)
    (hviol : S₂.card + 1 ≤ classCount S₂) : False := by
  have hTcard : (S₂.image toIdx).card = S₂.card :=
    Finset.card_image_of_injective _ toIdx_injective
  have hsplit : core ∪ (S₂.image toIdx \ core) = S₂.image toIdx :=
    Finset.union_sdiff_of_subset hcore_sub
  have hex_card : (S₂.image toIdx \ core).card = S₂.card - 9 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hcore_sub, hTcard,
      hcore_card]
  have hex_mem : (S₂.image toIdx \ core) ∈
      ((Finset.univ : Finset (Fin 27)) \ core).powersetCard
        (S₂.card - 9) := by
    rw [Finset.mem_powersetCard]
    exact ⟨fun a ha => Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp ha).2⟩, hex_card⟩
  have hb := hbound (S₂.card - 9) (by omega) _ hex_mem
  rw [hsplit, classCountIdx_image] at hb
  omega

/-! ## The family-count bound -/

/-- THE FAMILY-COUNT BOUND: every subset of `(ZMod 3)³` carries full
lines in at most `|S|` distinct direction families.  This is the whole
content of the price-13 fractional cost certificate. -/
theorem classCount_le_card (S : Finset (ResiduePoint 3 3)) :
    classCount S ≤ S.card := by
  by_contra hlt
  have hviol : S.card + 1 ≤ classCount S := by omega
  have h13 := classCount_le_thirteen S
  -- The counting layer confines a violator to sizes 9–12.
  have hcard9 : 9 ≤ S.card := by
    rcases Nat.lt_or_ge S.card 9 with h8 | h9
    · have := classCount_le_card_of_card_le_eight (S := S) (by omega)
      omega
    · exact h9
  have hcard12 : S.card ≤ 12 := by omega
  -- Pigeonhole: a four-family pencil point.
  obtain ⟨p₀, hp₀, hpen⟩ := exists_pencil_card_ge_four hviol
  -- Stage 1: translate the pencil point to the origin.
  have hS₀card : (S.image (fun v => v + (-p₀))).card = S.card :=
    Finset.card_image_of_injective _ (add_left_injective _)
  have hS₀fam : classCount (S.image (fun v => v + (-p₀))) =
      classCount S := classCount_image_add S _
  have hpen₀ : 4 ≤ (linePencil (S.image (fun v => v + (-p₀))) 0).card :=
    le_trans hpen (Finset.card_le_card fun b hb => linePencil_translate hb)
  generalize hS₀gen : S.image (fun v => v + (-p₀)) = S₀ at hS₀card hS₀fam hpen₀
  have hPreps : linePencil S₀ 0 ⊆ classReps := Finset.filter_subset _ _
  have hPlines : ∀ b ∈ linePencil S₀ 0,
      ∀ t : ZMod 3, residueLine 0 b t ∈ S₀ :=
    fun b hb => (Finset.mem_filter.mp hb).2
  -- Stage 2: case on an independent triple among the pencil lines.
  by_cases hsplit : ∃ x ∈ linePencil S₀ 0, ∃ y ∈ linePencil S₀ 0,
      ∃ z ∈ linePencil S₀ 0, LinearIndependent (ZMod 3) ![z, x, y]
  · -- CASE A: gauge the triple to the axes; one free line remains.
    obtain ⟨x, hx, y, hy, z, hz, htriple⟩ := hsplit
    -- A fourth pencil direction outside the triple.
    have hnotsub : ¬ linePencil S₀ 0 ⊆ {x, y, z} := by
      intro hsub
      have hle := Finset.card_le_card hsub
      have h1 := Finset.card_insert_le x ({y, z} : Finset (ResiduePoint 3 3))
      have h2 := Finset.card_insert_le y ({z} : Finset (ResiduePoint 3 3))
      have h3 : ({z} : Finset (ResiduePoint 3 3)).card = 1 :=
        Finset.card_singleton z
      omega
    obtain ⟨w, hw, hwout⟩ := Finset.not_subset.mp hnotsub
    have hwx : w ≠ x := fun h =>
      hwout (by rw [h]; exact Finset.mem_insert_self _ _)
    have hwy : w ≠ y := fun h => hwout (by
      rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hwz : w ≠ z := fun h => hwout (by
      rw [h]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _)))
    -- Gauge to standard position.
    have hS₂card : (S₀.image ⇑(gaugeEquiv htriple)).card = S.card := by
      rw [Finset.card_image_of_injective _ (gaugeEquiv htriple).injective,
        hS₀card]
    have hS₂fam : classCount (S₀.image ⇑(gaugeEquiv htriple)) =
        classCount S := by
      rw [classCount_image_linearEquiv, hS₀fam]
    -- The three axis lines live in the gauged window.
    have hline_x : ∀ t : ZMod 3, residueLine 0 (stdDir 0) t ∈
        S₀.image ⇑(gaugeEquiv htriple) := by
      have h := lineThrough0_image_linearEquiv (gaugeEquiv htriple)
        (hPlines x hx)
      rwa [gaugeEquiv_snd htriple] at h
    have hline_y : ∀ t : ZMod 3, residueLine 0 (stdDir 1) t ∈
        S₀.image ⇑(gaugeEquiv htriple) := by
      have h := lineThrough0_image_linearEquiv (gaugeEquiv htriple)
        (hPlines y hy)
      rwa [gaugeEquiv_trd htriple] at h
    have hline_z : ∀ t : ZMod 3, residueLine 0 (stdDir 2) t ∈
        S₀.image ⇑(gaugeEquiv htriple) := by
      have h := lineThrough0_image_linearEquiv (gaugeEquiv htriple)
        (hPlines z hz)
      rwa [gaugeEquiv_fst htriple] at h
    -- The fourth line, with its direction transversal-normalized.
    have hgw_ne : gaugeEquiv htriple w ≠ 0 := fun h =>
      mem_classReps_ne_zero (hPreps hw)
        ((gaugeEquiv htriple).injective (by rw [h, map_zero]))
    obtain ⟨r, hr, hrval⟩ :=
      exists_classRep _ (mem_nonzeroDirections_iff.mpr hgw_ne)
    have hline_w : ∀ t : ZMod 3,
        residueLine 0 (gaugeEquiv htriple w) t ∈
          S₀.image ⇑(gaugeEquiv htriple) :=
      lineThrough0_image_linearEquiv (gaugeEquiv htriple) (hPlines w hw)
    have hline_r : lineThrough0 r ⊆ S₀.image ⇑(gaugeEquiv htriple) := by
      rcases hrval with rfl | hrneg
      · exact lineThrough0_subset_iff.mpr hline_w
      · rw [hrneg, lineThrough0_neg]
        exact lineThrough0_subset_iff.mpr hline_w
    -- `r`'s class is `w`'s, which differs from every axis class.
    have hne_axis : ∀ v ∈ linePencil S₀ 0, w ≠ v →
        r ≠ gaugeEquiv htriple v := by
      intro v hv hwv hreq
      rcases hrval with hrw | hrw
      · exact hwv ((gaugeEquiv htriple).injective (hrw.symm.trans hreq))
      · have h1 : gaugeEquiv htriple v = -(gaugeEquiv htriple w) :=
          hreq.symm.trans hrw
        have h2 : gaugeEquiv htriple w = gaugeEquiv htriple (-v) := by
          rw [map_neg, h1, neg_neg]
        have h3 : w = -v := (gaugeEquiv htriple).injective h2
        exact classReps_not_neg_mem v (hPreps hv)
          (by rw [← h3]; exact hPreps hw)
    have hr_free : toIdx r ∈ freeRepsIdx := by
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · rw [← classRepsIdx_eq]
        exact Finset.mem_image_of_mem _ hr
      · intro hmem
        have hcases : r = stdDir 0 ∨ r = stdDir 1 ∨ r = stdDir 2 := by
          rcases Finset.mem_insert.mp hmem with h | hmem'
          · exact Or.inl (toIdx_injective (by rw [h, toIdx_stdDir_zero]))
          · rcases Finset.mem_insert.mp hmem' with h | hmem''
            · exact Or.inr (Or.inl
                (toIdx_injective (by rw [h, toIdx_stdDir_one])))
            · rw [Finset.mem_singleton] at hmem''
              exact Or.inr (Or.inr
                (toIdx_injective (by rw [hmem'', toIdx_stdDir_two])))
        rcases hcases with h | h | h
        · exact hne_axis x hx hwx (by rw [h, ← gaugeEquiv_snd htriple])
        · exact hne_axis y hy hwy (by rw [h, ← gaugeEquiv_trd htriple])
        · exact hne_axis z hz hwz (by rw [h, ← gaugeEquiv_fst htriple])
    -- The standard star sits inside the encoded window.
    have hstar_sub : stdStarIdx (toIdx r) ⊆
        (S₀.image ⇑(gaugeEquiv htriple)).image toIdx := by
      unfold stdStarIdx
      refine Finset.union_subset (Finset.union_subset
        (Finset.union_subset ?_ ?_) ?_) ?_
      · rw [← toIdx_stdDir_zero, ← lineThrough0_image_toIdx]
        exact Finset.image_subset_image (lineThrough0_subset_iff.mpr hline_x)
      · rw [← toIdx_stdDir_one, ← lineThrough0_image_toIdx]
        exact Finset.image_subset_image (lineThrough0_subset_iff.mpr hline_y)
      · rw [← toIdx_stdDir_two, ← lineThrough0_image_toIdx]
        exact Finset.image_subset_image (lineThrough0_subset_iff.mpr hline_z)
      · rw [← lineThrough0_image_toIdx]
        exact Finset.image_subset_image hline_r
    exact endgame_absurd hstar_sub (stdStarIdx_card _ hr_free)
      (fun k hk extras hex => by
        have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
        rcases hk4 with rfl | rfl | rfl | rfl
        · have := endgame_caseA_nine _ hr_free _ hex; omega
        · have := endgame_caseA_ten _ hr_free _ hex; omega
        · have := endgame_caseA_eleven _ hr_free _ hex; omega
        · have := endgame_caseA_twelve _ hr_free _ hex; omega)
      (by omega) (by omega) (by omega)
  · -- CASE B: no independent triple — the pencil is planar and its
    -- four concurrent lines cover a full plane.
    have h2 : 1 < (linePencil S₀ 0).card := by omega
    obtain ⟨x, hx, y, hy, hxy_ne⟩ := Finset.one_lt_card.mp h2
    have hxy : LinearIndependent (ZMod 3) ![x, y] :=
      classReps_pair_linearIndependent (hPreps hx) (hPreps hy) hxy_ne
    have hspan : ∀ b ∈ linePencil S₀ 0, b ∈ spanPairFinset x y := by
      intro b hb
      by_contra hout
      exact hsplit ⟨x, hx, y, hy, b, hb,
        (linearIndependent_triple_iff hxy).mpr hout⟩
    -- A vector outside the 9-element span window.
    have hspan_card : (spanPairFinset x y).card ≤ 9 := by
      unfold spanPairFinset
      exact le_trans Finset.card_image_le (by decide)
    have hout : ∃ c, c ∉ spanPairFinset x y := by
      by_contra hall
      have hsub : (Finset.univ : Finset (ResiduePoint 3 3)) ⊆
          spanPairFinset x y := by
        intro c _
        by_contra hc
        exact hall ⟨c, hc⟩
      have hle := Finset.card_le_card hsub
      have h27 : (Finset.univ : Finset (ResiduePoint 3 3)).card = 27 := by
        decide
      omega
    obtain ⟨c, hc⟩ := hout
    have htriple : LinearIndependent (ZMod 3) ![c, x, y] :=
      (linearIndependent_triple_iff hxy).mpr hc
    have hS₂card : (S₀.image ⇑(gaugeEquiv htriple)).card = S.card := by
      rw [Finset.card_image_of_injective _ (gaugeEquiv htriple).injective,
        hS₀card]
    have hS₂fam : classCount (S₀.image ⇑(gaugeEquiv htriple)) =
        classCount S := by
      rw [classCount_image_linearEquiv, hS₀fam]
    -- Four pencil directions, gauged and encoded.
    obtain ⟨T4, hT4sub, hT4card⟩ := Finset.exists_subset_card_eq hpen₀
    have hinj : Function.Injective
        (fun b => toIdx (gaugeEquiv htriple b)) :=
      fun a b hab => (gaugeEquiv htriple).injective (toIdx_injective hab)
    have hDcard :
        (T4.image (fun b => toIdx (gaugeEquiv htriple b))).card = 4 := by
      rw [Finset.card_image_of_injective _ hinj, hT4card]
    have hDsub : T4.image (fun b => toIdx (gaugeEquiv htriple b)) ⊆
        zPlaneDirsIdx := by
      intro d hd
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨s, t, hst⟩ := mem_spanPairFinset.mp (hspan b (hT4sub hb))
      have hgb : gaugeEquiv htriple b = s • stdDir 0 + t • stdDir 1 := by
        rw [← hst, map_add, map_smul, map_smul,
          gaugeEquiv_snd htriple, gaugeEquiv_trd htriple]
      have hz2 : (gaugeEquiv htriple b) 2 = 0 := by
        rw [hgb]
        simp [stdDir]
      have hgb_ne : gaugeEquiv htriple b ≠ 0 := fun h =>
        mem_classReps_ne_zero (hPreps (hT4sub hb))
          ((gaugeEquiv htriple).injective (by rw [h, map_zero]))
      exact toIdx_mem_zPlaneDirsIdx _ hgb_ne hz2
    have hDneg :
        ∀ d ∈ T4.image (fun b => toIdx (gaugeEquiv htriple b)),
          dblIdx d ∉ T4.image (fun b => toIdx (gaugeEquiv htriple b)) := by
      intro d hd hdd
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨b', hb', hb'e⟩ := Finset.mem_image.mp hdd
      have hgg : gaugeEquiv htriple b' = gaugeEquiv htriple (-b) := by
        apply toIdx_injective
        rw [hb'e, ← toIdx_neg, map_neg]
      have hbb' : b' = -b := (gaugeEquiv htriple).injective hgg
      refine classReps_not_neg_mem b (hPreps (hT4sub hb)) ?_
      rw [← hbb']
      exact hPreps (hT4sub hb')
    have hcover := four_plane_classes_cover _
      (Finset.mem_powersetCard.mpr ⟨hDsub, hDcard⟩) hDneg
    -- The whole plane sits inside the encoded window.
    have hplane_sub : zPlaneIdx ⊆
        (S₀.image ⇑(gaugeEquiv htriple)).image toIdx := by
      rw [← hcover]
      refine Finset.biUnion_subset.mpr ?_
      intro d hd
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hd
      rw [← lineThrough0_image_toIdx]
      exact Finset.image_subset_image (lineThrough0_subset_iff.mpr
        (lineThrough0_image_linearEquiv _ (hPlines b (hT4sub hb))))
    exact endgame_absurd hplane_sub zPlaneIdx_card
      (fun k hk extras hex => by
        have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
        rcases hk4 with rfl | rfl | rfl | rfl
        · have := endgame_caseB_nine _ hex; omega
        · have := endgame_caseB_ten _ hex; omega
        · have := endgame_caseB_eleven _ hex; omega
        · have := endgame_caseB_twelve _ hex; omega)
      (by omega) (by omega) (by omega)

/-! ## The certificate of record and its consequences -/

/-- THE `(3,3)` FRACTIONAL COST CERTIFICATE AT PRICE 13.  Together
with the transfer theorem this prices the mod-3 factor of
every coprime composite in dimension three. -/
theorem fractionalCostAt_three_three :
    FractionalCostAt 3 3 (nonzeroDirections 3 3) 13 :=
  fractionalCostAt_three_three_iff_classCount_le.mpr classCount_le_card

/-- The direction menu is nonempty (transfer side condition). -/
theorem nonzeroDirections_three_three_nonempty :
    (nonzeroDirections 3 3).Nonempty := by decide

/-- Lower half of the exact cell: every Kakeya set over `(ZMod 3)³`
has at least 13 points — the certificate applied to a full carrier. -/
theorem thirteen_le_card_of_isKakeyaSet
    {K : Finset (ResiduePoint 3 3)} (hK : IsKakeyaSet K) :
    13 ≤ K.card := by
  have h := fractionalCostAt_three_three K
  have hall : (nonzeroDirections 3 3).filter
      (fun b => CarriesLine K b) = nonzeroDirections 3 3 :=
    Finset.filter_true_of_mem fun b _ =>
      isKakeyaSet_iff_forall_carriesLine.mp hK b
  have h26 : (nonzeroDirections 3 3).card = 26 := by decide
  rw [hall, h26] at h
  omega

/-- THE 13-POINT WITNESS, in encoded form — found by computer search,
re-verified by the kernel below (the search carries no authority). -/
def threeThreeWitnessIdx : Finset (Fin 27) :=
  {9, 18, 3, 6, 15, 24, 1, 19, 22, 25, 11, 20, 5}

/-- The witness on the carrier. -/
def threeThreeWitness : Finset (ResiduePoint 3 3) :=
  threeThreeWitnessIdx.image ofIdx

theorem ofIdx_injective : Function.Injective ofIdx := by
  intro a b h
  rw [← toIdx_ofIdx a, ← toIdx_ofIdx b, h]

theorem threeThreeWitness_image_toIdx :
    threeThreeWitness.image toIdx = threeThreeWitnessIdx := by
  unfold threeThreeWitness
  rw [Finset.image_image,
    show (toIdx ∘ ofIdx) = id from funext toIdx_ofIdx, Finset.image_id]

theorem threeThreeWitness_card : threeThreeWitness.card = 13 := by
  unfold threeThreeWitness
  rw [Finset.card_image_of_injective _ ofIdx_injective]
  decide

/-- The witness is Kakeya: the zero direction is anchored anywhere,
and every family is carried — checked on the transversal in the index
world and spread to all 26 directions by negation invariance. -/
theorem threeThreeWitness_isKakeyaSet : IsKakeyaSet threeThreeWitness := by
  intro b
  by_cases hb : b = 0
  · subst hb
    refine ⟨ofIdx 9, fun t => ?_⟩
    have hline : residueLine (ofIdx 9) 0 t = ofIdx 9 := by
      funext i
      simp only [residueLine, Pi.add_apply, Pi.smul_apply, Pi.zero_apply,
        smul_eq_mul, mul_zero, add_zero]
    rw [hline]
    exact Finset.mem_image_of_mem _ (by decide)
  · obtain ⟨r, hr, hrv⟩ :=
      exists_classRep b (mem_nonzeroDirections_iff.mpr hb)
    have hidx : ∀ d ∈ classRepsIdx, carriesIdx threeThreeWitnessIdx d := by
      decide
    have hfast : CarriesLineFast threeThreeWitness r := by
      have h1 : carriesIdx (threeThreeWitness.image toIdx) (toIdx r) := by
        rw [threeThreeWitness_image_toIdx]
        refine hidx _ ?_
        rw [← classRepsIdx_eq]
        exact Finset.mem_image_of_mem _ hr
      exact carriesIdx_iff.mp h1
    have hcar : CarriesLine threeThreeWitness r :=
      carriesLineFast_iff.mp hfast
    rcases hrv with rfl | hrneg
    · exact hcar
    · rw [hrneg] at hcar
      exact carriesLine_neg.mp hcar

/-- THE NEW EXACT CELL: `minKakeyaSize 3 3 = 13`. -/
theorem minKakeyaSize_three_three : minKakeyaSize 3 3 = 13 := by
  refine le_antisymm ?_ ?_
  · have h := minKakeyaSize_le_card threeThreeWitness_isKakeyaSet
    rwa [threeThreeWitness_card] at h
  · obtain ⟨K, hK, hcard⟩ := exists_minKakeyaSize_witness 3 3
    rw [← hcard]
    exact thirteen_le_card_of_isKakeyaSet hK

/-- THE INFINITE FAMILY: exact multiplicativity of the mod-3 factor in
dimension three against EVERY coprime co-factor — the transfer theorem
fires at the now-proved true price. -/
theorem minKakeyaSize_three_mul_dim_three (M : ℕ) [NeZero M]
    (h : Nat.Coprime 3 M) :
    minKakeyaSize (3 * M) 3 = 13 * minKakeyaSize M 3 := by
  have hfc : FractionalCostAt 3 3 (nonzeroDirections 3 3)
      (minKakeyaSize 3 3) := by
    rw [minKakeyaSize_three_three]
    exact fractionalCostAt_three_three
  have heq := minKakeyaSize_mul_eq_of_fractionalCostAt h
    nonzeroDirections_three_three_nonempty hfc
  rw [heq, minKakeyaSize_three_three]

/-- THE `(6,3)` CELL, CLOSED: `minKakeyaSize 6 3 = 65`.  The mod-2
certificate fails at its true price in dimension three, leaving only
`4·min(3,3) ≤ min(6,3) ≤ 5·min(3,3)`; the certificate priced on the
mod-3 factor collapses the sandwich. -/
theorem minKakeyaSize_six_three : minKakeyaSize 6 3 = 65 := by
  have h := minKakeyaSize_three_mul_dim_three 2 (by decide)
  rw [show (3 * 2 : ℕ) = 6 from rfl, minKakeyaSize_two_three] at h
  omega

/-- ZERO CHINESE REMAINDER DEFECT at `(6,3)`: the minimum is exactly
multiplicative — the first composite exact cell in dimension three in
this development. -/
theorem minKakeyaSize_six_three_eq_product :
    minKakeyaSize 6 3 = minKakeyaSize 2 3 * minKakeyaSize 3 3 := by
  rw [minKakeyaSize_six_three, minKakeyaSize_two_three,
    minKakeyaSize_three_three]

end KakeyaMultiplicativity
