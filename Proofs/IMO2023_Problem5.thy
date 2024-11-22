theory IMO2023_Problem5
imports Complex_Main
begin

(* Define geometric predicates *)
definition perpendicular :: "point ⇒ point ⇒ point ⇒ point ⇒ bool"
  where "perpendicular A B C D ≡ 
    Re((B - A) * cnj(D - C)) = 0"

(* Main theorem statement *)
theorem imo2023_p5:
  fixes A B C O P F G :: point
  assumes "O = circumcenter A B C"
    and "D ∈ line B C"
    and "E ∈ line C A"
    and "P ∈ line A D"
    and "P ∈ line B E"
    and "perpendicular P F B C"
    and "perpendicular P G C A"
  shows "concyclic O P F G"