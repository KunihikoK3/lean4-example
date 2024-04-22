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
  `a ∣ b` is existential (there exist k such b=ak), `s ⊆ t` is universal (each x in s belongs to t).
-/

/-
The following is an example of an implication appearing as a HYPOTHESIS.
-/
namespace implication_examples
variable (h : ∀ n, n > 5 → n > 3)  -- this is an implication

-- Known Fact: We have a number `a` that is known to be greater than 5.
variable (ha : a > 5)

-- Applying the hypothesis
theorem a_gt_3 : a > 3 := by
  apply h  -- note that apply the implication h changes the goal from a > 3 to a > 5
  exact ha



-- The following is an example of an implication appearing as a GOAL.
variable (b : ℕ)

-- Goal: Prove that if `b` is greater than 5, then it is greater than 3.
theorem b_gt_5_imp_b_gt_3 : b > 5 → b > 3 := by
  intro hb_gt_5  -- the intro tactic in Lean defines hb_gt_5 to be the hypothesis of the implication
  apply h
  exact hb_gt_5

end implication_examples
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
theorem my_add_le_add (x y z w : ℝ) (h₁ : x ≤ y) (h₂ : z ≤ w) : x + z ≤ y + w :=
  add_le_add h₁ h₂

section

variable (a b c d : ℝ)
variable (h₁ : a ≤ b) (h₂ : c ≤ d)

#check @my_add_le_add
/- When you use #check @my_add_le_add, you are asking Lean to display the type of my_add_le_add with all of its arguments made EXPLICIT, including those that are normally implicit. This could include type class instances or other parameters that the type inference system would normally handle for you.

In Lean, a function or theorem with multiple arguments is often represented as a series of implications when describing its type, especially when those arguments involve proofs or conditions. This is due to a concept called "Currying", where a function of multiple arguments is transformed into a sequence of functions each with a single argument.

Let's break down the output you've provided:

`my_add_le_add : ∀ (x y z w : ℝ), x ≤ y → z ≤ w → x + z ≤ y + w`

This can be read as follows:

- `∀ (x y z w : ℝ)`: For all `x`, `y`, `z`, `w` that are real numbers (ℝ),
- `x ≤ y →`: if `x` is less than or equal to `y`,
- `z ≤ w →`: and `z` is less than or equal to `w`,
- `x + z ≤ y + w`: then `x + z` is less than or equal to `y + w`.

Each `→` represents an implication or a functional dependency. The output is essentially saying:

- Given `x` and `y`, if you have a proof of `x ≤ y`,
- and given `z` and `w`, if you have a proof of `z ≤ w`,
- then you can construct a proof of `x + z ≤ y + w`.

It is written in this "curried" form because in type theory and functional programming, a function `f : A → B → C` is typically a function that takes an argument of type `A` and returns a function of type `B → C`. Applied to the theorem:

1. The first implication (`x ≤ y →`) means that once you provide real numbers `x` and `y`, you need to provide a proof of `x ≤ y` to get to the next part of the function.
2. The second implication (`z ≤ w →`) means that after providing the first proof, you then provide real numbers `z` and `w`, and a proof of `z ≤ w` to get the final result.

This curried representation allows partial application. You can provide some of the arguments to `my_add_le_add` and get a function that expects the remaining arguments. This is powerful in proof assistants for building complex proofs step by step.
-/
#check my_add_le_add a b
/- In your theorem my_add_le_add, you defined it with six parameters: x y z w and two hypotheses h₁ : x ≤ y and h₂ : z ≤ w. When you pass only two arguments to my_add_le_add, Lean will attempt to match these with the first two parameters x and y.

However, since my_add_le_add expects six arguments (four real numbers and two proofs of inequality), just giving it a and b won't be sufficient for it to be a complete expression or statement. Lean will return the "type" of the partial application of my_add_le_add to a and b, which will effectively be a function type expecting the remaining four arguments.

So, if you execute #check my_add_le_add a b, Lean will display a function type that takes the remaining parameters: two real numbers and two proofs of inequalities, and returns a proof of the inequality a + z ≤ b + w (where z and w are the third and fourth real number arguments you'll need to provide, along with their respective inequalities).
-/
#check my_add_le_add a b c d h₁
#check my_add_le_add _ _ _ _ h₁
#check my_add_le_add _ _ _ _ h₁ h₂

/- In Lean, an underscore _ is used as a placeholder for an argument whose value can be inferred by the type checker. When you use _ in an expression like #check my_add_le_add _ _ _ _ h₁ h₂, you are telling Lean that you want it to automatically fill in these arguments based on the context and the types of h₁ and h₂.
-/
theorem my_add_le_add' {x y z w : ℝ} (h₁ : x ≤ y) (h₂ : z ≤ w) :
  x + z ≤ y + w :=
  add_le_add h₁ h₂

/-
In Lean, curly braces {} around parameters in function or theorem definitions indicate that these parameters are implicit. Implicit parameters are automatically inferred by Lean's type checker from the context, meaning that you typically do not need to explicitly provide them when you call the theorem or function. This makes the code more concise and easier to read, especially when the values of these parameters can be straightforwardly deduced from other arguments or the overall context.

{x y z w : ℝ}: The real numbers x, y, z, and w are implicit arguments. This means when you use my_add_le_add', you do not need to explicitly provide x, y, z, and w if Lean can infer their values from h₁ and h₂.

(h₁ : x ≤ y), (h₂ : z ≤ w): These are explicit arguments. You must provide proofs of these inequalities when you call my_add_le_add'.

-/
#check my_add_le_add' h₁
#check my_add_le_add' h₁ h₂

end

-- We'll use the following function below
def fnUB (f : ℝ → ℝ) (a : ℝ) := ∀ x, f x ≤ a

section

-- Demonstrate use of `apply`, `have`, `specialize`, `dsimp`, proof structuring
-- Also show `have`,

theorem fnUB_add {f g a b} (hfa : fnUB f a) (hgb : fnUB g b) :
    fnUB (f + g) (a + b) := by
    -- hfa : fnUB f a isn't just a declaration out of nowhere; it's part of the logical structure of theorem and proof writing in Lean. hfa : fnUB f a is saying that hfa is the name given to the assumption or hypothesis that the function f is bounded above by a.
  simp only [fnUB] at hfa hgb ⊢
  -- This command simplifies hfa and hgb using the definition of fnUB and also simplifies the goal (⊢ symbol stands for the current goal).
  intro x
  -- This introduces a new variable x, which is a real number. It allows us to work with f x, g x, f x + g x, etc.
  simp only [Pi.add_apply]
  -- This simplifies the application of (f + g) x to f x + g x.
  have hfa' := hfa x
  -- This assigns to hfa' the specific bound of f at x, effectively stating f x ≤ a.
  specialize hgb x
  -- This specializes the bound of g at x, effectively stating g x ≤ b.
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
