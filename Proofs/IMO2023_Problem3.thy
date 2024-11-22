theory IMO2023_Problem3
imports Main
begin

(* Define the grid state as a set of coordinates *)
type_synonym position = "nat \<times> nat"
type_synonym game_state = "position set"

(* Define valid moves *)
definition valid_move :: "game_state \<Rightarrow> position \<Rightarrow> position \<Rightarrow> bool"
  where "valid_move state from to \<equiv> 
    from \<in> state \<and>
    to \<notin> state \<and>
    fst to = fst from + 1 \<and>
    snd to = snd from \<and>
    (\<exists>p\<in>state. fst p = fst from \<and> snd p = snd from + 1)"

(* Main theorem statement *)
theorem imo2023_p3:
  fixes n :: nat
  shows "max_moves n = n * (n - 1) div 2"