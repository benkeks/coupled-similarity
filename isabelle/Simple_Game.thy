section \<open>Simple Games\<close>

theory Simple_Game
imports
  Main
begin

text \<open>Simple games are games where player0 wins all infinite plays.\<close>
locale simple_game =
fixes
  game_move :: "'s \<Rightarrow> 's \<Rightarrow> bool" ("_ \<longmapsto>\<heartsuit> _" [70, 70] 80) and
  player0_position :: "'s \<Rightarrow> bool" and
  initial :: 's
begin

definition player1_position :: "'s \<Rightarrow> bool"
  where "player1_position s \<equiv> \<not> player0_position s"

--\<open>plays (to be precise: play p refixes) are lists. we model them 
  with the most recent move at the beginning. (for our purpose it's enough to consider finite plays)\<close>
type_synonym ('s2) play = "'s2 list"
type_synonym ('s2) strategy = "'s2 play \<Rightarrow> 's2"

inductive_set plays :: "'s play set" where
  "[initial] \<in> plays" |
  "p#play \<in> plays \<Longrightarrow> p \<longmapsto>\<heartsuit> p' \<Longrightarrow> p'#p#play \<in> plays"

--"plays for a given player 0 strategy"
inductive_set plays_for_strategy :: "'s strategy \<Rightarrow> 's play set" for f where
  init: "[initial] \<in> plays_for_strategy f" |
  p0move: "n0#play \<in> plays_for_strategy f \<Longrightarrow> player0_position n0 \<Longrightarrow> n0 \<longmapsto>\<heartsuit> f (n0#play)
    \<Longrightarrow> (f (n0#play))#n0#play \<in> plays_for_strategy f" |
  p1move: "n1#play \<in> plays_for_strategy f \<Longrightarrow> player1_position n1 \<Longrightarrow> n1 \<longmapsto>\<heartsuit> n1'
    \<Longrightarrow> n1'#n1#play \<in> plays_for_strategy f"

text \<open>a strategy is sound if it only decides on enabled transitions.\<close>
definition sound_strategy :: "'s strategy \<Rightarrow> bool" where
  "sound_strategy f \<equiv>
    \<forall> n0 play . n0#play \<in> plays_for_strategy f \<and> player0_position n0 \<longrightarrow> n0 \<longmapsto>\<heartsuit> f (n0#play)"

lemma strategy_plays_subset:
  assumes "play \<in> plays_for_strategy f"
  shows "play \<in> plays"
  using assms by (induct rule: plays_for_strategy.induct, auto simp add: plays.intros)

lemma no_empty_plays:
  assumes "[] \<in> plays"
  shows "False" 
  using assms plays.cases by blast


  text"player1 wins a play if the play has reached a deadlock where it's player0's turn"
definition player1_wins :: "'s play \<Rightarrow> bool" where
  "player1_wins play \<equiv> player0_position (hd play) \<and> (\<nexists> p' . (hd play) \<longmapsto>\<heartsuit> p')"

definition player0_winning_strategy :: "'s strategy \<Rightarrow> bool" where
  "player0_winning_strategy f \<equiv> (\<forall> play \<in> plays_for_strategy f . \<not> player1_wins play)"

end

end
