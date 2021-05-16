import tactic

/-!

# Equivalence relations are the same as partitions

In this file we prove that there's a bijection between
the equivalence relations on a type, and the partitions of a type. 

Three sections:

1) partitions
2) equivalence classes
3) the proof

## Overview

Say `α` is a type, and `R : α → α → Prop` is a binary relation on `α`. 
The following things are already in Lean:

`reflexive R := ∀ (x : α), R x x`
`symmetric R := ∀ ⦃x y : α⦄, R x y → R y x`
`transitive R := ∀ ⦃x y z : α⦄, R x y → R y z → R x z`

`equivalence R := reflexive R ∧ symmetric R ∧ transitive R`

In the file below, we will define partitions of `α` and "build some
interface" (i.e. prove some propositions). We will define
equivalence classes and do the same thing.
Finally, we will prove that there's a bijection between
equivalence relations on `α` and partitions of `α`.

-/

/-

# 1) Partitions

We define a partition, and prove some lemmas about partitions. Some
I prove myself (not always using tactics) and some I leave for you.

## Definition of a partition

Let `α` be a type. A *partition* on `α` is defined to be
the following data:

1) A set C of subsets of α, called "blocks".
2) A hypothesis (i.e. a proof!) that all the blocks are non-empty.
3) A hypothesis that every term of type α is in one of the blocks.
4) A hypothesis that two blocks with non-empty intersection are equal.
-/

/-- The structure of a partition on a Type α. -/ 
@[ext] structure partition (α : Type) :=
(C : set (set α))
(Hnonempty : ∀ X ∈ C, (X : set α).nonempty)
(Hcover : ∀ a, ∃ X ∈ C, a ∈ X)
(Hdisjoint : ∀ X Y ∈ C, (X ∩ Y : set α).nonempty → X = Y)

/-

## Basic interface for partitions

Here's the way notation works. If `α` is a type (i.e. a set)
then a term `P` of type `partition α` is a partition of `α`,
that is, a set of disjoint nonempty subsets of `α` whose union is `α`.

The collection of sets underlying `P` is `P.C`, the proof that
they're all nonempty is `P.Hnonempty` and so on.

-/

namespace partition

-- let α be a type, and fix a partition P on α. Let X and Y be subsets of α.
variables {α : Type} {P : partition α} {X Y : set α}

/-- If X and Y are blocks, and a is in X and Y, then X = Y. -/
theorem eq_of_mem 
  (hX : X ∈ P.C) (hY : Y ∈ P.C) 
  {a : α} 
  (haX : a ∈ X) (haY : a ∈ Y) 
: X = Y :=
-- Proof: follows immediately from the disjointness hypothesis.
P.Hdisjoint _ _ hX hY ⟨a, haX, haY⟩

/-- If a is in two blocks X and Y, and if b is in X,
  then b is in Y (as X=Y) -/
theorem mem_of_mem (hX : X ∈ P.C) (hY : Y ∈ P.C) {a b : α}
  (haX : a ∈ X) (haY : a ∈ Y) (hbX : b ∈ X) : b ∈ Y :=
begin
  rwa ← (eq_of_mem hX hY haX haY),
end

/-- Every term of type `α` is in one of the blocks for a partition `P`. -/
theorem mem_block (a : α) : ∃ X : set α, X ∈ P.C ∧ a ∈ X := 
  let ⟨X, ⟨hX, haX⟩⟩ := P.Hcover a in ⟨X, ⟨hX, haX⟩⟩

end partition

/-

# 2) Equivalence classes.

We define equivalence classes and prove a few basic results about them.

-/

section equivalence_classes

/-!

## Definition of equivalence classes 

-/

-- Notation and variables for the equivalence class section:

-- let α be a type, and let R be a binary relation on R.
variables {α : Type} (R : α → α → Prop)

/-- The equivalence class of `a` is the set of `b` related to `a`. -/
def cl (a : α) :=
{b : α | R b a}

/-!

## Basic lemmas about equivalence classes

-/

/-- Useful for rewriting -- `b` is in the equivalence class of `a` iff
`b` is related to `a`. True by definition. -/
theorem mem_cl_iff {a b : α} : b ∈ cl R a ↔ R b a := by refl

-- Assume now that R is an equivalence relation.
variables {R} (hR : equivalence R)
include hR

/-- x is in cl(x) -/
lemma mem_cl_self (a : α) : a ∈ cl R a := hR.1 a

lemma cl_sub_cl_of_mem_cl {a b : α} : a ∈ cl R b → cl R a ⊆ cl R b := 
  λ ha c hc, hR.2.2 hc ha -- trans

lemma cl_eq_cl_of_mem_cl {a b : α} : a ∈ cl R b → cl R a = cl R b :=
  -- remember `set.subset.antisymm` says `X ⊆ Y → Y ⊆ X → X = Y`
  λ ah, set.subset.antisymm 
    (cl_sub_cl_of_mem_cl hR ah) 
    (cl_sub_cl_of_mem_cl hR (hR.2.1 ah))

end equivalence_classes -- section

/-!

# 3) The theorem

Let `α` be a type (i.e. a collection of stucff).

There is a bijection between equivalence relations on `α` and
partitions of `α`.

We prove this by writing down constructions in each direction
and proving that the constructions are two-sided inverses of one another.
-/

open partition


example (α : Type) : {R : α → α → Prop // equivalence R} ≃ partition α :=
-- We define constructions (functions!) in both directions and prove that
-- one is a two-sided inverse of the other
{ -- Here is the first construction, from equivalence
  -- relations to partitions.
  -- Let R be an equivalence relation.
  to_fun := λ R, {
    -- Let C be the set of equivalence classes for R.
    C := { B : set α | ∃ x : α, B = cl R.1 x},
    -- I claim that C is a partition. We need to check the three
    -- hypotheses for a partition (`Hnonempty`, `Hcover` and `Hdisjoint`),
    -- so we need to supply three proofs.
    Hnonempty := begin
      cases R with R hR,
      -- If X is an equivalence class then X is nonempty.
      show ∀ (X : set α), (∃ (a : α), X = cl R a) → X.nonempty,
      rintros X ⟨a, rfl⟩,
      exact ⟨a, hR.1 a⟩, -- hrefl
    end,
    Hcover := begin
      cases R with R hR,
      -- The equivalence classes cover α
      show ∀ (a : α), ∃ (X : set α) (H : ∃ (b : α), X = cl R b), a ∈ X,
      exact λ a, ⟨cl R a, ⟨⟨a, rfl⟩, hR.1 a⟩⟩,
    end,
    Hdisjoint := begin
      cases R with R hR,
      -- If two equivalence classes overlap, they are equal.
      show ∀ (X Y : set α), (∃ (a : α), X = cl R a) →
        (∃ (b : α), Y = cl _ b) → (X ∩ Y).nonempty → X = Y,
      rintros X Y ⟨x, rfl⟩ ⟨y, rfl⟩ ⟨z, hzX, hzY⟩,
      exact cl_eq_cl_of_mem_cl hR (hR.2.2 (hR.2.1 hzX) hzY),
    end },
  -- Conversely, say P is an partition. 
  inv_fun := λ P, 
    -- Let's define a binary relation `R` thus:
    --  `R a b` iff *every* block containing `a` also contains `b`.
    -- Because only one block contains a, this will work,
    -- and it turns out to be a nice way of thinking about it. 
    ⟨λ a b, ∀ X ∈ P.C, a ∈ X → b ∈ X, begin
      -- I claim this is an equivalence relation.
    split,
    { -- It's reflexive
      show ∀ (a : α) (X : set α), X ∈ P.C → a ∈ X → a ∈ X,
      exact λ a X hxP haX, haX
    },
    split,
    { -- it's symmetric
      show ∀ (a b : α),
        (∀ (X : set α), X ∈ P.C → a ∈ X → b ∈ X) →
         ∀ (X : set α), X ∈ P.C → b ∈ X → a ∈ X,
      intros a b hA X hXP hbX,
      obtain ⟨Y, hYP, aY⟩ := P.Hcover a,
      rwa (let hbY := hA Y hYP aY in eq_of_mem hXP hYP hbX hbY),
    },
    { -- it's transitive
      unfold transitive,
      show ∀ (a b c : α),
        (∀ (X : set α), X ∈ P.C → a ∈ X → b ∈ X) →
        (∀ (X : set α), X ∈ P.C → b ∈ X → c ∈ X) →
         ∀ (X : set α), X ∈ P.C → a ∈ X → c ∈ X,
      exact λ a b c hab hbc X hXP haX, hbc X hXP (hab X hXP haX),
    }
  end⟩,
  -- If you start with the equivalence relation, and then make the partition
  -- and a new equivalence relation, you get back to where you started.
  left_inv := begin
    rintro ⟨R, hR⟩,
    -- Tidying up the mess...
    suffices : (λ (a b : α), ∀ (c : α), a ∈ cl R c → b ∈ cl R c) = R,
      simpa,
    -- ... you have to prove two binary relations are equal.
    ext a b,
    -- so you have to prove an if and only if.
    show (∀ (c : α), a ∈ cl R c → b ∈ cl R c) ↔ R a b,
    exact let ⟨hRefl, hSymm, hTrans⟩ := hR in ⟨
      λ h, hSymm (h a (hRefl a)),
      λ hab c hca, hTrans (hSymm hab) hca,
    ⟩
  end,
  -- Similarly, if you start with the partition, and then make the
  -- equivalence relation, and then construct the corresponding partition 
  -- into equivalence classes, you have the same partition you started with.  
  right_inv := begin
    -- Let P be a partition
    intro P,
    -- It suffices to prove that a subset X is in the original partition
    -- if and only if it's in the one made from the equivalence relation.
    ext X,
    show (∃ (a : α), X = cl _ a) ↔ X ∈ P.C,
    dsimp only,
    split, {
      rintro ⟨a, ha⟩,
      obtain ⟨Y, hY, aY⟩ := P.Hcover a,
      have q : X = Y := begin
        subst ha,
        ext b,
        split, {
          intro hb,
          simp only [cl, set.mem_set_of_eq] at hb,
          obtain ⟨Z, hZ, bZ⟩ := P.Hcover b,
          rwa let aZ := hb Z hZ bZ in eq_of_mem hY hZ aY aZ,
        }, {
          simp only [cl, set.mem_set_of_eq],
          intros bY X hX bX, 
          rwa eq_of_mem hX hY bX bY,
        }
      end,
      rwa q,
    }, {
      intro hX,
      obtain ⟨a, aX⟩ := P.Hnonempty X hX,
      use a,
      --obtain ⟨Y, hY, bY⟩ := P.Hcover a,
      ext b,
      simp [cl],
      split, {
        intros bX Y hY bY,
        have q : X = Y := eq_of_mem hX hY bX bY,
        rwa ← q,
      }, {
        intros h,
        obtain ⟨Y, hY, bY⟩ := P.Hcover b,
        have aY := h Y hY bY,
        exact mem_of_mem hY hX aY aX bY,
      }
    },
  end }
