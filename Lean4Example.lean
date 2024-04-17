import LeanCopilot
import Mathlib.Data.Real.Basic
import Paperproof
open Nat (add_assoc add_comm)


theorem hello_world (a b c : Nat)
  : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_comm b, ←Nat.add_assoc]

theorem foo (a : Nat) : a + 1 = Nat.succ a := by
 rfl

theorem bar (a b c d : Nat) : a + b + c + d = a + (c + b) + d := by
ac_rfl

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  simp [h, mul_assoc]

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  aesop_subst h'
  simp [←
  mul_assoc,
  h]

--
section
variable (a b : ℝ)

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b  := by
  ring_nf


end
--
