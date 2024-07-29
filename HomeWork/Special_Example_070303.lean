import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Algebra.Group.MinimalAxioms

section Special_Example_070303

structure α where
/- Let $\alpha$ be the set of pairs of real numbers $(x,y)$ with $x \neq 0$ -/
  x : ℝ
  y : ℝ
  h : (x≠0)

instance: Mul α where
/- Define the multiplication on $\alpha$ by $(x,y)(z,w)=(xz,xw+y)$. -/
  mul :=
  fun {x := x, y := y, h := h₁}
      {x := z, y := w, h := h₂}  =>
    {
      x := x * z
      y := x * w + y
      h := mul_ne_zero h₁ h₂
      -- Since $x \neq 0 $, $y \neq 0 $, therefore $x*y \neq 0 $, multiplication is well defined.
    }

/- Prove that $\alpha$ is a group.-/

@[simp]
theorem alpha_mul_def(A B:α) :
/- Notice that the definition of multiplication is reducible -/
  A * B =
  {
    x := A.x * B.x
    y := A.x * B.y + A.y
    h := mul_ne_zero A.h B.h
  }
        := rfl

instance: One α where
/- We need to find an $\alpha$ element to act as one-/
  one := {
    x := 1
    y := 0
    h := (zero_ne_one' ℝ).symm -- $1 \neq 0 $
  }

@[simp]
theorem alpha_one_def:
/- Notice that the definition of one is reducible -/
  (1:α) =
  {
    x := 1
    y := 0
    h := (zero_ne_one' ℝ).symm
  }
        := rfl

noncomputable instance: Inv α where
/- We need to find an $\alpha \to \alpha$ function to act as inversion-/
  inv := fun {x,y,h} ↦
    {
      x := 1/x
      y := -y/x
      h := one_div_ne_zero h
    }

@[simp]
theorem alpha_inv_def(A:α):
/- Notice that the definition of inversion is reducible -/
  A⁻¹ =
  {
    x := 1/A.x
    y := -A.y/A.x
    h := one_div_ne_zero A.h
  }
      := rfl

noncomputable instance: Group α := by
  apply Group.ofLeftAxioms
  /- We just need to verify that it satisfies the left axiom of the group -/

  case assoc =>
    intro a b c
    let {x := x₁, y := y₁, h := h₁} := a
    let {x := x₂, y := y₂, h := h₂} := b
    let {x := x₃, y := y₃, h := h₃} := c
    simp[alpha_mul_def]
    constructor
    · rw[← mul_assoc]
    · rw[mul_add,← add_assoc,← mul_assoc]

  case mul_left_inv =>
    intro a
    have x_neq_zero : a.x ≠ 0 := a.h
    simp[alpha_inv_def]
    constructor
    · exact inv_mul_cancel x_neq_zero
    · have : -a.y / a.x = a.x⁻¹ * -a.y := div_eq_inv_mul (-a.y) a.x
      rw[this,← mul_add,add_right_neg,mul_zero]

  case one_mul =>
    intro a
    simp[alpha_one_def]

end Special_Example_070303
