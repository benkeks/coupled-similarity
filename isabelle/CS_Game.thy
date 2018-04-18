section \<open>Game for Coupled Similarity\<close>

theory CS_Game
imports
  Coupled_Simulation
  Simple_Game
begin

subsection \<open>The Coupled Simulation Preorder Game\<close>

datatype ('s, 'a) cs_game_node =
  AttackerNode 's 's |
  DefenderStepNode 'a 's 's |
  DefenderCouplingNode 's 's

fun (in lts_tau) cs_game_moves ::
  "('s, 'a) cs_game_node \<Rightarrow> ('s, 'a) cs_game_node \<Rightarrow> bool" where
  simulation_challenge:
    "cs_game_moves (AttackerNode p q) (DefenderStepNode a p1 q0) =
      (p \<longmapsto> a p1 \<and> q = q0)" |
  simulation_answer: 
    "cs_game_moves (DefenderStepNode a p1 q0) (AttackerNode p11 q1) =
      (q0 \<longmapsto>^ a q1 \<and> p1 = p11)" |
  coupling_challenge:
    "cs_game_moves (AttackerNode p q) (DefenderCouplingNode p0 q0) =
      (p = p0 \<and> q = q0)" |
  coupling_answer:
    "cs_game_moves (DefenderCouplingNode p0 q0) (AttackerNode q1 p00) =
      (p0 = p00 \<and> q0 \<longmapsto>* tau q1)" |
  cs_game_moves_no_step:
    "cs_game_moves _ _ = False"

fun cs_game_defender_node :: "('s, 'a) cs_game_node \<Rightarrow> bool" where
  "cs_game_defender_node (AttackerNode _ _) = False" |
  "cs_game_defender_node (DefenderStepNode _ _ _) = True" |
  "cs_game_defender_node (DefenderCouplingNode _ _) = True"

locale cs_game =
  lts_tau trans \<tau> +
  simple_game cs_game_moves cs_game_defender_node initial
for
  trans :: "'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool" and
  \<tau> :: "'a" and 
  initial :: "('s, 'a) cs_game_node"
begin

subsection \<open>Coupled Simulation Implies Winning Strategy\<close>

fun strategy_from_coupledsim :: "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s, 'a) cs_game_node strategy" where
  "strategy_from_coupledsim R ((DefenderStepNode a p1 q0)#play) =
    (AttackerNode p1 (SOME q1 . R p1 q1 \<and> q0 \<longmapsto>^ a q1))" |
  "strategy_from_coupledsim R ((DefenderCouplingNode p0 q0)#play) =
    (AttackerNode (SOME q1 . R q1 p0 \<and> q0 \<longmapsto>* tau q1) p0)" |
  "strategy_from_coupledsim _ _ = undefined"

lemma attacker_followed_by_defender:
  assumes
    "n0 # play \<in> plays"
    "cs_game_defender_node n0"
    "initial = AttackerNode p0 q0"
  shows "\<exists> p q . hd play = AttackerNode p q \<and> cs_game_moves (AttackerNode p q) n0" "play \<noteq> []"
proof -
  have n0_not_init: "n0 \<noteq> initial" using assms(2,3) by auto
  hence "cs_game_moves (hd play) n0" using assms(1)
    by (metis list.sel(1) list.sel(3) plays.cases)
  thus "\<exists>p q. hd play = AttackerNode p q \<and> cs_game_moves (AttackerNode p q) n0" using assms(2)
    by (metis cs_game_defender_node.elims(2,3) local.cs_game_moves_no_step(1,2,3,7))
  show "play \<noteq> []" using n0_not_init assms(1) plays.cases by auto
qed

lemma strategy_from_coupledsim_retains_coupledsim:
  assumes
    "R p0 q0"
    "coupled_simulation R"
    "initial = AttackerNode p0 q0"
    "play \<in> plays_for_strategy (strategy_from_coupledsim R)"
  shows
    "hd play = AttackerNode p q \<Longrightarrow> R p q"
    "length play > 1 \<Longrightarrow> hd (tl play) = AttackerNode p q \<Longrightarrow> R p q"
  using assms(4)
proof (induct arbitrary: p q rule: plays_for_strategy.induct[OF assms(4)])
  case 1
  fix p q
  assume "hd [initial] = AttackerNode p q"
  hence "p = p0" "q = q0" using assms(3) by auto
  thus "R p q" using assms(1) by simp
next
  case 1
  fix p q
  assume "1 < length [initial]"
  hence False by auto
  thus "R p q"  ..
next
  case (2 n0 play)
  hence n0play_is_play: "n0 # play \<in> plays" using strategy_plays_subset by blast
  fix p q
  assume subassms:
    "hd (strategy_from_coupledsim R (n0 # play) # n0 # play) = AttackerNode p q"
    "strategy_from_coupledsim R (n0 # play) # n0 # play
      \<in> plays_for_strategy (strategy_from_coupledsim R)"
  then obtain pi qi where 
      piqi_def: "hd (play) = AttackerNode pi qi"
        "cs_game_moves (AttackerNode pi qi) n0" "play \<noteq> []"
    using attacker_followed_by_defender[OF n0play_is_play `cs_game_defender_node n0` assms(3)]
    by blast
  hence "R pi qi" using 2(1,3) by simp
  have "(\<exists> a . n0 = (DefenderStepNode a p qi) \<and> pi \<longmapsto> a p)
    \<or> (n0 = (DefenderCouplingNode pi qi))"
    using piqi_def(2) 2(4,5) subassms(1)
    by (metis cs_game_defender_node.elims(2) cs_game_moves.simps(2) list.sel(1)
        coupling_challenge simulation_challenge)
  thus "R p q"
  proof safe
    fix a
    assume n0_def: "n0 = DefenderStepNode a p qi" "pi \<longmapsto>a p"
    have "strategy_from_coupledsim R (n0 # play) =
        (AttackerNode p (SOME q1 . R p q1 \<and> qi \<longmapsto>^ a q1))"
      unfolding n0_def(1) by auto
    with subassms(1) have q_def: "q = (SOME q1. R p q1 \<and> qi \<longmapsto>^ a  q1)" by auto
    have "\<exists> qii . R p qii \<and> qi \<longmapsto>^ a qii"
      using n0_def(2) `R pi qi` `coupled_simulation R`
      unfolding coupled_simulation_def by blast
    from someI_ex[OF this] show "R p q" unfolding q_def by blast
  next
    assume n0_def: "n0 = DefenderCouplingNode pi qi"
    have "strategy_from_coupledsim R (n0 # play) =
        (AttackerNode (SOME q1 . R q1 pi \<and> qi \<longmapsto>* tau q1) pi)"
      unfolding n0_def(1) by auto
    with subassms(1) have qp_def: "p = (SOME q1 . R q1 pi \<and> qi \<longmapsto>* tau q1)" "q = pi" by auto
    have "\<exists> q1 . R q1 pi \<and> qi \<longmapsto>* tau q1"
      using n0_def `R pi qi` `coupled_simulation R`
      unfolding coupled_simulation_def by blast
    from someI_ex[OF this] show "R p q" unfolding qp_def by blast
  qed
next
  case (2 n0 play)
  fix p q
  assume "hd (tl (strategy_from_coupledsim R (n0 # play) # n0 # play)) = AttackerNode p q"
  hence False using 2(4) by auto
  thus "R p q" ..
next
  case (3 n1 play n1')
  fix p q
  assume "hd (n1' # n1 # play) = AttackerNode p q"
  hence False using 3(4,5) unfolding player1_position_def
    by (metis cs_game_moves_no_step(5) cs_game_defender_node.elims(3) list.sel(1))
  thus "R p q" ..
next
  case (3 n1 play n1')
  fix p q
  assume "hd (tl (n1' # n1 # play)) = AttackerNode p q"
  thus "R p q" using 3(1,2) by auto
qed

lemma strategy_from_coupledsim_sound:
  assumes
    "R p0 q0"
    "coupled_simulation R"
    "initial = AttackerNode p0 q0"
  shows
    "sound_strategy (strategy_from_coupledsim R)"
  unfolding sound_strategy_def
proof clarify
  fix n0 play
  assume subassms:
    "n0 # play \<in> plays_for_strategy(strategy_from_coupledsim R)"
    "cs_game_defender_node n0"
  then obtain pi qi where 
      piqi_def: "hd (play) = AttackerNode pi qi"
        "cs_game_moves (AttackerNode pi qi) n0" "play \<noteq> []"
    using attacker_followed_by_defender[OF _ `cs_game_defender_node n0` assms(3)]
      strategy_plays_subset by blast
  hence "R pi qi"
    using strategy_from_coupledsim_retains_coupledsim[OF assms] list.sel subassms by auto
  have "(\<exists> a p . n0 = (DefenderStepNode a p qi) \<and> pi \<longmapsto> a p)
    \<or> (n0 = (DefenderCouplingNode pi qi))"
    by (metis cs_game_defender_node.elims(2)
        coupling_challenge simulation_challenge piqi_def(2) subassms(2))
  thus "cs_game_moves n0 (strategy_from_coupledsim R (n0 # play))"
  proof safe
    fix a p
    assume dsn:
      "pi \<longmapsto>a  p"
      "n0 = DefenderStepNode a p qi"
    hence qi_spec:
      "(strategy_from_coupledsim R (n0 # play)) =
        AttackerNode p (SOME q1 . R p q1 \<and> qi \<longmapsto>^ a q1)"
      by simp
    then obtain qii where qii_spec:
      "AttackerNode p (SOME q1 . R p q1 \<and> qi \<longmapsto>^ a q1) = AttackerNode p qii" by blast
    have "\<exists> qii . R p qii \<and> qi \<longmapsto>^ a qii"
      using dsn `R pi qi` `coupled_simulation R`
      unfolding coupled_simulation_def by blast
    from someI_ex[OF this] have "R p qii \<and> qi \<longmapsto>^ a qii" using qii_spec by blast
    thus "cs_game_moves (DefenderStepNode a p qi)
          (strategy_from_coupledsim R (DefenderStepNode a p qi # play))"
      using qi_spec qii_spec unfolding dsn(2) by auto
  next --"coupling quite analogous."
    assume dcn:
      "n0 = DefenderCouplingNode pi qi"
    hence qi_spec:
      "(strategy_from_coupledsim R (n0 # play)) =
      AttackerNode (SOME q1 . R q1 pi \<and> qi \<longmapsto>* tau q1) pi"
      by simp
    then obtain qii where qii_spec:
      "AttackerNode (SOME q1 . R q1 pi \<and> qi \<longmapsto>* tau q1) pi = AttackerNode qii pi" by blast
    have "\<exists> qii . R qii pi \<and> qi \<longmapsto>* tau qii"
      using dcn `R pi qi` `coupled_simulation R`
      unfolding coupled_simulation_def by blast
    from someI_ex[OF this] have "R qii pi \<and> qi \<longmapsto>* tau qii" using qii_spec by blast
    thus "cs_game_moves (DefenderCouplingNode pi qi)
        (strategy_from_coupledsim R (DefenderCouplingNode pi qi # play))"
      using qi_spec qii_spec unfolding dcn by auto
  qed
qed

lemma coupledsim_implies_winning_strategy:
  assumes
    "R p q"
    "coupled_simulation R"
    "initial = AttackerNode p q"
  shows
    "player0_winning_strategy (strategy_from_coupledsim R)"
  unfolding player0_winning_strategy_def
proof (clarify)
  fix play
  assume subassms:
    "play \<in> plays_for_strategy (strategy_from_coupledsim R)"
    "player1_wins play"
  show "False" using subassms
  proof (induct rule: simple_game.plays_for_strategy.induct[OF subassms(1)])
    case 1
    then show ?case unfolding player1_wins_def using assms(3) by auto
  next
    case (2 n0 play)
    hence "\<not> cs_game_defender_node (strategy_from_coupledsim R (n0 # play))"
      using cs_game_moves_no_step cs_game_defender_node.elims(2) by metis
    hence "\<not>  player1_wins (strategy_from_coupledsim R (n0 # play) # n0 # play)"
      unfolding player1_wins_def by auto
    thus ?case using 2(6) by auto
  next
    case (3 n1 play n1')
    then obtain p q where n1_def: "n1 = AttackerNode p q"
      unfolding player1_position_def using cs_game_defender_node.elims(3) by blast
    hence "R p q"
      using strategy_from_coupledsim_retains_coupledsim[OF assms, of "n1 # play"] 3(1) by auto
    have "(\<exists> p1 a . n1' = (DefenderStepNode a p1 q) \<and> (p \<longmapsto> a p1))
        \<or> n1' = (DefenderCouplingNode p q)"
      using n1_def `cs_game_moves n1 n1'` coupling_challenge cs_game_moves_no_step(5)
        simulation_challenge
      by (metis cs_game_defender_node.elims(2, 3))
    then show ?case
    proof 
      assume "(\<exists> p1 a . n1' = (DefenderStepNode a p1 q) \<and> (p \<longmapsto> a p1))"
      then obtain p1 a where 
        n1'_def: "n1' = (DefenderStepNode a p1 q)" "p \<longmapsto> a p1"
        by blast
      hence "\<exists> q1 . q \<longmapsto>^ a q1" 
        using `R p q` `coupled_simulation R` unfolding coupled_simulation_def by blast
      hence "\<exists> q1 . cs_game_moves (DefenderStepNode a p1 q) (AttackerNode p1 q1)"
        by auto
      with `player1_wins (n1' # n1 # play)` show False unfolding player1_wins_def n1'_def
        by (metis list.sel(1))
    next
      assume n1'_def: "n1' = DefenderCouplingNode p q"
      have "\<exists> q1 . q \<longmapsto>*tau q1" 
        using `coupled_simulation R` `R p q` unfolding coupled_simulation_def by blast
      hence "\<exists> q1 . cs_game_moves (DefenderCouplingNode p q) (AttackerNode q1 p)"
        by auto
      with `player1_wins (n1' # n1 # play)` show False unfolding player1_wins_def n1'_def
        by (metis list.sel(1))
    qed
  qed
qed

subsection \<open>Winning Strategy Induces Coupled Simulation\<close>

lemma winning_strategy_implies_coupledsim:
  assumes
    "player0_winning_strategy f"
    "sound_strategy f"
  defines
    "R == \<lambda> p q . (\<exists> play \<in> plays_for_strategy f . hd play = AttackerNode p q)"
  shows
    "coupled_simulation R"
  unfolding coupled_simulation_def
proof safe
  fix p q p' a
  assume challenge:
    "R p q"
    "p \<longmapsto>a  p'"
  hence game_move: "cs_game_moves (AttackerNode p q) (DefenderStepNode a p' q)" by auto
  have "(\<exists> play \<in> plays_for_strategy f . hd play = AttackerNode p q)"
    using challenge(1) assms by blast
  then obtain play where
      play_spec: "AttackerNode p q # play \<in> plays_for_strategy f"
    by (metis list.sel(1) simple_game.plays.cases strategy_plays_subset)
  hence interplay: "(DefenderStepNode a p' q) # AttackerNode p q # play \<in> plays_for_strategy f"
    using game_move by (simp add: player1_position_def simple_game.plays_for_strategy.p1move)
  hence "\<not> player1_wins ((DefenderStepNode a p' q) # AttackerNode p q # play)"
    using assms(1) unfolding player0_winning_strategy_def by blast
  then obtain n1 where n1_def:
      "n1 = f (DefenderStepNode a p' q # AttackerNode p q # play)"
      "cs_game_moves (DefenderStepNode a p' q) n1"
    using interplay assms(2) unfolding player0_winning_strategy_def sound_strategy_def by simp
  obtain q' where q'_spec:
      "(AttackerNode p' q') = n1" "q \<longmapsto>^ a q'"
    using n1_def(2) by (cases n1, auto)
  hence "(AttackerNode p' q') # (DefenderStepNode a p' q) # AttackerNode p q # play
      \<in> plays_for_strategy f"
    using interplay n1_def by (simp add: simple_game.plays_for_strategy.p0move)
  hence "R p' q'" unfolding R_def by (meson list.sel(1))
  thus "\<exists>q'. R p' q' \<and> q \<longmapsto>^ a  q'" using q'_spec(2) by blast
next
  fix p q 
  assume challenge:
    "R p q"
  hence game_move: "cs_game_moves (AttackerNode p q) (DefenderCouplingNode p q)" by auto
  have "(\<exists> play \<in> plays_for_strategy f . hd play = AttackerNode p q)"
    using challenge assms by blast
  then obtain play where
      play_spec: "AttackerNode p q # play \<in> plays_for_strategy f"
    by (metis list.sel(1) simple_game.plays.cases strategy_plays_subset)
  hence interplay: "(DefenderCouplingNode p q) # AttackerNode p q # play
      \<in> plays_for_strategy f"
    using game_move by (simp add: player1_position_def simple_game.plays_for_strategy.p1move)
  hence "\<not> player1_wins ((DefenderCouplingNode p q) # AttackerNode p q # play)"
    using assms(1) unfolding player0_winning_strategy_def by blast
  then obtain n1 where n1_def:
      "n1 = f (DefenderCouplingNode p q # AttackerNode p q # play)"
      "cs_game_moves (DefenderCouplingNode p q) n1"
    using interplay assms(2)
    unfolding player0_winning_strategy_def sound_strategy_def by simp
  obtain q' where q'_spec:
      "(AttackerNode q' p) = n1" "q \<longmapsto>* tau q'"
    using n1_def(2) by (cases n1, auto)
  hence "(AttackerNode q' p) # (DefenderCouplingNode p q) # AttackerNode p q # play
      \<in> plays_for_strategy f"
    using interplay n1_def by (simp add: simple_game.plays_for_strategy.p0move)
  hence "R q' p" unfolding R_def by (meson list.sel(1))
  thus "\<exists>q'. q \<longmapsto>* tau  q' \<and> R q' p" using q'_spec(2) by blast
qed

theorem winning_strategy_iff_coupledsim:
  assumes
    "initial = AttackerNode p q"
  shows 
    "(\<exists> f . player0_winning_strategy f \<and> sound_strategy f)
    = p \<sqsubseteq>cs q"
proof (rule)
  assume
    "(\<exists>f. player0_winning_strategy f \<and> sound_strategy f)"
  then obtain f where
    "coupled_simulation (\<lambda>p q. \<exists>play\<in>plays_for_strategy f. hd play = AttackerNode p q)"
    using winning_strategy_implies_coupledsim by blast
  moreover have "(\<lambda>p q. \<exists>play\<in>plays_for_strategy f. hd play = AttackerNode p q) p q"
    using assms plays_for_strategy.init[of f] by (meson list.sel(1))
  ultimately show "p \<sqsubseteq>cs q" by blast
next
  assume
    "p \<sqsubseteq>cs  q"
  thus "(\<exists>f. player0_winning_strategy f \<and> sound_strategy f)"
    using coupledsim_implies_winning_strategy[OF _ _ assms]
          strategy_from_coupledsim_sound[OF _ _ assms] by blast
qed

end

end
