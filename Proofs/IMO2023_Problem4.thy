theory IMO2023_Problem4
imports Complex_Main
begin

(* Main theorem statement *)
theorem imo2023_p4:
  fixes f :: "real ⇒ real"
  assumes "∀x y. f(x + y + f(x*y)) = f(x) * f(y)"
  shows "f = (λx. 0) ∨ f = (λx. 1)"