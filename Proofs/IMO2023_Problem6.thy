theory IMO2023_Problem6
imports Main
begin

(* Define the grid as a function from coordinates to stone count *)
type_synonym grid = "nat ⇒ nat ⇒ nat"

(* Define valid moves *)
definition valid_move :: "grid ⇒ nat × nat ⇒ nat × nat ⇒ bool"
  where "valid_move g from to ≡
    g (fst from) (snd from) = 1 ∧
    g (fst to) (snd to) = 0 ∧
    adjacent from to"

(* Main theorem statement *)
theorem imo2023_p6:
  fixes n :: nat
  assumes "initial_stones g n"  (* g has exactly n stones *)
  shows "∃g'. reachable g g' ∧ (row_aligned g' ∨ column_aligned g')"