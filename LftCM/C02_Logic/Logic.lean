import Mathlib
import LeanCopilot

/-
# Logics

* Get used to be precise about logical connective, phrases like "to prove
  `A ∧ B` we have to prove `A` and `B`." are awkward but necessary.

Overview of the most important connectives:

→   \to     if ... then ...           implication
∀   \all    for all                   universal quantification
∃   \ex     there exists              existential quantification
¬   \not    not                       negation
∧   \and    and                       conjunction
∨   \or     or                        disjunction
↔   \iff    ... if and only iff ...   biimplication
False       contradiction!            falsity
True        this is trivial           truth

... and how to use them:

            appearing as hypothesis `h`                appearing as goal
`A → B`     `have h' := h ha`, `apply h`               `intro ha`
`∀ x, P x`  `have h' := h x`, `apply h`, `specialize`  `intro x`

`A ∧ B`     `rcases h with ⟨ha, hb⟩`, `h.1`, `h.2`     `constructor`
`A ∨ B`     `rcases h with (ha | hb)`                  `left` or `right`
`∃ x. P x`  `rcases h with ⟨x, hx⟩`                    `constructor` or `use x`

`False`     `contradiction`                            --
`True`      --                                         `trivial`

`¬ A`       `contradiction`                            `intro ha`
`A ↔ B`     `rcases h with ⟨h₁, h₂⟩`                   `constructor`

* `by_contra` for proofs by contradiction
* Note that logical connectives can be hidden under other definitions:
  `a ∣ b` is existential, `s ⊆ t` is universal.
-/

/-!
## Implication and universal quantifiers
When you define an implication in Lean, such as p → q, you are essentially defining a function type. For instance, if you have a theorem or a lemma that states p → q, providing a proof for this is equivalent to providing a function that takes an argument of type p (a proof of p) and produces a result of type q (a proof of q).

Let's use the square function as a simple numerical function to illustrate how an implication works as a function type in Lean. We will define a theorem that states an implication involving the square function.
First, let's define the square function:
-/
def square (n : ℕ) : ℕ := n * n
/-
Now, let's state and prove a theorem that uses an implication. We will prove that if a natural number n is greater than 0, then its square is also greater than 0. This is a simple fact since the square of any positive number is positive.
Here's how we can express and prove this theorem in Lean:
-/
theorem square_pos (n : ℕ) : n > 0 → square n > 0 :=by
  intro h
  simp only [square]
  exact mul_pos h h
/-
In this proof, the implication n > 0 → square n > 0 is treated as a function that takes a proof of n > 0  and produces a proof of square n > 0.

Apparently the intro h tactic in Lean does automatically define h to be the hypothesis of the implication. When you use intro h in the context of proving an implication, it introduces the antecedent of the implication as a hypothesis named h into the local context and shifts the goal to proving the consequent.
-/
theorem my_add_le_add (x y z w : ℝ) (h₁ : x ≤ y) (h₂ : z ≤ w) :
    x + z ≤ y + w :=
  add_le_add h₁ h₂

section

variable (a b c d : ℝ)
variable (h₁ : a ≤ b) (h₂ : c ≤ d)

#check @my_add_le_add
#check my_add_le_add a b
#check my_add_le_add a b c d h₁
#check my_add_le_add _ _ _ _ h₁
#check my_add_le_add _ _ _ _ h₁ h₂

theorem my_add_le_add' {x y z w : ℝ} (h₁ : x ≤ y) (h₂ : z ≤ w) :
    x + z ≤ y + w :=
  add_le_add h₁ h₂

#check my_add_le_add' h₁
#check my_add_le_add' h₁ h₂

end

def fnUB (f : ℝ → ℝ) (a : ℝ) := ∀ x, f x ≤ a

section

-- Demonstrate use of `apply`, `have`, `specialize`, `dsimp`, proof structuring
-- Also show `have`,

theorem fnUB_add {f g a b} (hfa : fnUB f a) (hgb : fnUB g b) :
    fnUB (f + g) (a + b) := by
  simp only [fnUB] at hfa hgb ⊢
  intro x
  simp only [Pi.add_apply]
  have hfa' := hfa x
  specialize hgb x
  linarith


end

/-!
## The existential quantifier
-/

-- Demonstrate `use`, `refine` and `norm_num`, explain how to know that it is existential

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  use 2.4
  norm_num

example : 5 ∣ 20 := by
  use 4  -- Automatically closes trivial goals!

-- Demonstrate `rcases` and `obtain` on existential quantifiers

section

def fnHasUB (f : ℝ → ℝ) := ∃ a, fnUB f a

example {f g} (ubf : fnHasUB f) (ubg : fnHasUB g) : fnHasUB (f + g) := by
  simp only [fnHasUB] at *
  rcases ubf with ⟨a, ha⟩
  rcases ubg with ⟨b, hb⟩
  use a + b
  exact fnUB_add ha hb

end

/-
The existential quantifier in Lena comes with an axiom called *global choice*.
It provides a witness for all proofs of existentially quantified statements and
guarantees that the witness is the same if we deconstruct the same statement twice.
-/
#check Exists.choose
#check Exists.choose_spec

noncomputable def chooseNat (h : ∃ (x : ℕ), x > 4) : ℕ := by
  exact Exists.choose h

/-!
## Negation

`¬ A` is an abbreviation for `A → False`.
-/

section

variable {f : ℝ → ℝ}

-- Demonstrate `rintro`

example (h : ∀ a, ∃ x, f x > a) : ¬ fnHasUB f := by
  simp only [fnHasUB]
  rintro ⟨a, ha⟩
  specialize h a
  rcases h with ⟨b, hb⟩
  simp only [fnUB] at *
  specialize ha b
  rw [← not_lt] at ha
  contradiction


-- Repeat with demonstration of `simp`, `simp only`, `push_neg`

example (h : ∀ a, ∃ x, a < f x) : ¬ fnHasUB f := by
  simp only [fnHasUB, fnUB]
  push_neg
  assumption

end

/-!
## Conjuction
-/

section

variable {x y : ℝ}

-- Demonstrate `constructor`, `linarith`, `subst`, `contradiction`

example (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  · assumption
  · linarith

-- Demonstrate `rcases`, `.1`,

example (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x := by
  --rcases h with ⟨h₁, h₂⟩
  simp only [Not]
  intro h₃
  apply h.2
  exact LE.le.antisymm h.1 h₃

end

/-!
## Disjunction
-/

section

variable (x y z : ℝ)

-- Demonstrate `library_search`, `rcases`, `left`, `right`, `rwa`

#check abs_of_nonneg
#check abs_of_neg

example : x < |y| → x < y ∨ x < -y := by
  intro h
  by_cases hy : y < 0
  · right
    rwa [abs_of_neg hy] at h
  · left
    rw [not_lt] at hy
    rwa [abs_of_nonneg hy] at h

-- Demonstrate nested `rcases`

example (h : (x < y ∧ y < z) ∨ x < z) : x < z := by
  rcases h with (⟨h1,h3⟩|h2)
  · trans
    · exact h1
    · exact h3
  · assumption

end




















/-!
## More exercises
-/

section

variable (p q : Prop) -- Propositions
variable (r s : ℕ → Prop)  -- Predicates over the natural numbers

example : p ∧ q → q ∧ p := by

example : p ∨ q → q ∨ p := by

example : (∃ x, r x ∧ s x) → (∃ x, r x) ∧ (∃ x, s x) := by

example : ∀ z, (∃ x y, r x ∧ s y ∧ y = z) → ∃ x, r x ∧ s z := by

example : ¬¬(¬¬p → p) := by

example : ∃ x, r x → ∀ y, r y := by

end
