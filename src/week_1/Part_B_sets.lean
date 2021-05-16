import tactic

-- Let `Ω` be a "big underlying set" and let `X` and `Y` and `Z` be subsets

variables (Ω : Type) (X Y Z : set Ω) (a b c x y z : Ω)

namespace xena

/-!

# subsets

Let's think about `X ⊆ Y`. Typeset `⊆` with `\sub` or `\ss`
-/

-- `X ⊆ Y` is the same as `∀ a, a ∈ X → a ∈ Y` , by definition.

lemma subset_def : X ⊆ Y ↔ ∀ a, a ∈ X → a ∈ Y :=
begin
  -- true by definition
  refl
end

lemma subset_refl : X ⊆ X := λ x hX, hX

lemma subset_trans (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) : X ⊆ Z :=
begin
  -- If you start with `rw subset_def at *` then you
  -- will have things like `hYZ : ∀ (a : Ω), a ∈ Y → a ∈ Z`
  -- You need to think of `hYZ` as a function, which has two
  -- inputs: first a term `a` of type `Ω`, and second a proof `haY` that `a ∈ Y`.
  -- It then produces one output `haZ`, a proof that `a ∈ Z`.
  -- You can also think of it as an implication:
  -- "if a is in Ω, and if a ∈ Y, then a ∈ Z". Because it's an implication,
  -- you can `apply hYZ`. This is a really useful skill!
  intros x hX,
  rw subset_def at *,
  exact hYZ x (hXY x hX),
end

/-!

# Equality of sets

Two sets are equal if and only if they have the same elements.
The name of this theorem is `set.ext_iff`.
-/

example : X = Y ↔ (∀ a, a ∈ X ↔ a ∈ Y) := set.ext_iff

-- In practice, you often have a goal `⊢ X = Y` and you want to reduce
-- it to `a ∈ X ↔ a ∈ Y` for an arbitary `a : Ω`. This can be done with
-- the `ext` tactic. 

lemma subset.antisymm (hXY : X ⊆ Y) (hYX : Y ⊆ X) : X = Y :=
begin
  -- start with `ext a`,
  ext a,
  rw subset_def at *,
  exact ⟨hXY a, hYX a⟩
end

/-!

### Unions and intersections

Type `\cup` or `\un` for `∪`, and `\cap` or `\i` for `∩`

-/

lemma union_def : a ∈ X ∪ Y ↔ a ∈ X ∨ a ∈ Y :=
begin
  -- true by definition
  refl,
end

lemma inter_def : a ∈ X ∩ Y ↔ a ∈ X ∧ a ∈ Y :=
begin
  -- true by definition
  refl,
end


-- You can rewrite with those lemmas above if you're not comfortable with
-- assuming they're true by definition.

-- union lemmas

lemma union_cases {P : Prop} : (a ∈ X → P) → (a ∈ Y → P) → a ∈ X ∪ Y → P := begin
  intros hX hY haXuY,
  cases haXuY, {exact hX haXuY}, {exact hY haXuY},
end

lemma union_self : X ∪ X = X :=
begin
  ext a,
  exact ⟨
    union_cases Ω X X a (λ hxU, hxU) (λ hxU, hxU),
    or.inl
  ⟩ 
end

lemma subset_union_left : X ⊆ X ∪ Y := λ a, or.inl
lemma subset_union_right : Y ⊆ X ∪ Y := λ a, or.inr

lemma union_subset_iff : X ∪ Y ⊆ Z ↔ X ⊆ Z ∧ Y ⊆ Z := ⟨
  λ ha, ⟨
    subset_trans Ω X (X ∪ Y) Z (subset_union_left Ω X Y) ha,
    subset_trans Ω Y (X ∪ Y) Z (subset_union_right Ω X Y) ha
  ⟩,
  λ ⟨hXZ, hYZ⟩ a, union_cases Ω X Y a (λ haX, hXZ haX) (λ haY, hYZ haY)
⟩

variable (W : set Ω)

lemma union_subset_union (hWX : W ⊆ X) (hYZ : Y ⊆ Z) : W ∪ Y ⊆ X ∪ Z :=
  λ a, union_cases Ω W Y a (λ aW, or.inl (hWX aW)) (λ aY, or.inr (hYZ aY))


lemma union_subset_union_left (hXY : X ⊆ Y) : X ∪ Z ⊆ Y ∪ Z := 
  union_subset_union Ω Y Z Z X hXY (subset_refl Ω Z)

-- etc etc

-- intersection lemmas

lemma inter_subset_left : X ∩ Y ⊆ X := λ x ⟨hxX, _⟩, hxX

-- don't forget `ext` to make progress with equalities of sets

lemma inter_self : X ∩ X = X := subset.antisymm _ _ _ 
  (inter_subset_left _ _ _) 
  (λ x hxX, ⟨hxX, hxX⟩)

lemma inter_comm : X ∩ Y = Y ∩ X := subset.antisymm _ _ _ 
  (λ x ⟨hxX, hxY⟩, ⟨hxY, hxX⟩) 
  (λ x ⟨hxY, hxX⟩, ⟨hxX, hxY⟩)

lemma inter_assoc : X ∩ (Y ∩ Z) = (X ∩ Y) ∩ Z := subset.antisymm _ _ _ 
  (λ x ⟨hxX, ⟨hxY, hxZ⟩⟩, ⟨⟨hxX, hxY⟩, hxZ⟩)
  (λ x ⟨⟨hxX, hxY⟩, hxZ⟩, ⟨hxX, ⟨hxY, hxZ⟩⟩)

/-!

### Forall and exists

-/

lemma not_exists_iff_forall_not : ¬ (∃ a, a ∈ X) ↔ ∀ b, ¬ (b ∈ X) := ⟨
  λ ha b hb, ha ⟨b, hb⟩, 
  λ hb ⟨a, ha⟩, hb a ha
⟩

theorem contra {P : Prop}: ¬ (¬ P) → P :=
begin
  intro hnnP,
  by_contra,
  exact hnnP h,
end

example : ¬ (∀ a, a ∈ X) ↔ ∃ b, ¬ (b ∈ X) := ⟨
  λ ha, contra (λ hX, ha (λ a, contra (λ hanX, hX ⟨a, hanX⟩))),
  λ ⟨b, hb⟩ ha, hb (ha b),
⟩  

end xena

