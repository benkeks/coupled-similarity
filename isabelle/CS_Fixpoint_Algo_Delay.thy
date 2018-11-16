section \<open>Fixed Point Algorithm for Coupled Similarity\<close>

theory CS_Fixpoint_Algo_Delay
imports
  Coupled_Simulation
  Finite_Weak_Transition_Systems
  "~~/src/HOL/Library/While_Combinator"
  "~~/src/HOL/Library/Finite_Lattice"
begin

context lts_tau
begin

definition fp_step :: 
  "'s rel \<Rightarrow> 's rel"
  where
  "fp_step R1 \<equiv> { (p,q)\<in>R1.
    (\<forall> p' a. p \<longmapsto> a p' \<longrightarrow> 
       (\<exists> q'. ((p',q')\<in>R1) \<and> (q \<longmapsto>^~ a q')))
  \<and> (\<exists> q'. q \<longmapsto>*tau q' \<and> ((q',p)\<in>R1)) }"

lemma mono_fp_step:
  "mono fp_step"
proof (rule, safe)
  fix x y::"'s rel" and p q
  assume
    "x \<subseteq> y"
    "(p, q) \<in> fp_step x"
  thus  "(p, q) \<in> fp_step y"
    unfolding fp_step_def
    by (auto, blast)
qed

lemma fp_fp_step:
  assumes
    "R = fp_step R"
  shows
    "coupled_delay_simulation (\<lambda> p q. (p, q) \<in> R)"
  using assms unfolding fp_step_def coupled_delay_simulation_def delay_simulation_def
  by fastforce

lemma gfp_fp_step_subset_gcs:
  shows "(gfp fp_step) \<subseteq> { (p,q) . greatest_coupled_simulation p q }"
  unfolding  gcs_eq_coupled_sim_by[symmetric] 
proof clarify
  fix a b
  assume
    "(a, b) \<in> gfp fp_step"
  thus "a \<sqsubseteq>cs  b"
    unfolding coupled_sim_by_eq_delay_coupled_simulation
    using fp_fp_step mono_fp_step gfp_unfold
    by metis
qed

lemma fp_fp_step_gcs:
  assumes
    "R = { (p,q) . greatest_coupled_simulation p q }"
  shows
    "fp_step R = R"
  unfolding assms
proof safe
  fix p q
  assume
    "(p, q) \<in> fp_step {(x, y). greatest_coupled_simulation x y}"
  hence "(\<forall>p' a. p \<longmapsto>a  p' \<longrightarrow> (\<exists>q'. greatest_coupled_simulation p' q' \<and> q \<longmapsto>^~ a  q')) \<and>
    (\<exists>q'. q \<longmapsto>* tau  q' \<and> greatest_coupled_simulation q' p)"
    unfolding fp_step_def by auto
  hence "(\<forall>p' a. p \<longmapsto>a  p' \<longrightarrow> (\<exists>q'. greatest_coupled_simulation p' q' \<and> q \<longmapsto>^ a  q')) \<and>
    (\<exists>q'. q \<longmapsto>* tau  q' \<and> greatest_coupled_simulation q' p)"
    unfolding fp_step_def using weak_step_delay_implies_weak_tau by blast
  hence "(\<forall>p' a. p \<longmapsto>a  p' \<longrightarrow> (\<exists>q'. greatest_coupled_simulation p' q' \<and> q \<longmapsto>^^ a  q')) \<and>
    (\<exists>q'. q \<longmapsto>* tau  q' \<and> greatest_coupled_simulation q' p)" using weak_step_tau2_def by simp
  thus "greatest_coupled_simulation p q"
    using lts_tau.gcs by metis
next
  fix p q
  assume asm:
    "greatest_coupled_simulation p q"
  then have "(p, q) \<in> {(x, y). greatest_coupled_simulation x y}" by blast
  moreover from asm have \<open>\<exists> R. R p q \<and> coupled_delay_simulation R\<close>
    unfolding gcs_eq_coupled_sim_by[symmetric] coupled_sim_by_eq_delay_coupled_simulation .
  moreover from asm have  "(\<forall> p' a. p \<longmapsto> a p' \<longrightarrow> (\<exists> q'. (greatest_coupled_simulation p' q') \<and> (q \<longmapsto>^~ a q')))"
    unfolding  gcs_eq_coupled_sim_by[symmetric] coupled_sim_by_eq_delay_coupled_simulation
    by (metis coupled_delay_simulation_def delay_simulation_def)
  moreover have  "(\<exists> q'. q \<longmapsto>*tau q' \<and> (greatest_coupled_simulation q' p))"
    using asm gcs_is_coupled_simulation coupled_simulation_implies_coupling by blast
  ultimately show "(p, q) \<in> fp_step {(x, y). greatest_coupled_simulation x y}"
    unfolding fp_step_def by blast
qed

lemma gfp_fp_step_gcs: "gfp fp_step = { (p,q) . greatest_coupled_simulation p q }"
  using fp_fp_step_gcs gfp_fp_step_subset_gcs
  by (simp add: equalityI gfp_upperbound)

end

context lts_tau_finite
begin
lemma gfp_fp_step_while:
  shows
    "gfp fp_step = while (\<lambda>R. fp_step R \<noteq> R) fp_step top"
  using gfp_while_lattice[OF mono_fp_step] finite_state_rel Finite_Set.finite_set by blast

theorem coupled_sim_fp_step_while:
  shows "while (\<lambda>R. fp_step R \<noteq> R) fp_step top = { (p,q) . greatest_coupled_simulation p q }"
  using gfp_fp_step_while gfp_fp_step_gcs by blast

end


end
