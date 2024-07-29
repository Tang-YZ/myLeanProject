import Mathlib.Tactic
import Mathlib.Algebra.Group.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Algebra.Group.Action.Basic

section Example_4109B

section Formalize
/- Let G be a group of order n and H is a subgroup of index p in G,
where p is the smallest prime that divides n.
Prove that H is a normal subgroup of G.-/

variable{G : Type*}[Group G][Fintype G] -- G是有限群
variable(H : Subgroup G) -- H是G的子群
variable(p n : Nat)

export Fintype(card)
export Subgroup(index)
export Nat(minFac)

variable(OrderOfG_eq_n : (card G = n) ) -- G的阶数是n
variable(IndexOfH_eq_p : (H.index = p) ) -- H的指数是p
variable(p_minFac_n : (n.minFac = p) ) -- p是n的最小因数

/- need to sorry-elim -/
instance: Subgroup.Normal H where
  conj_mem := sorry

end Formalize
end Example_4109B
