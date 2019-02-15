section \<open>Fixed Point Algorithm for Coupled Similarity\<close>

theory CS_Fixpoint_Algo
imports
  Coupled_Simulation
  Finite_Weak_Transition_Systems
  "~~/src/HOL/Library/While_Combinator"
  "~~/src/HOL/Library/Finite_Lattice"
begin

context lts_tau
begin

definition fp_step :: 
  \<open>'s rel \<Rightarrow> 's rel\<close>
  where
  \<open>fp_step R1 \<equiv> { (p,q)\<in>R1.
    (\<forall> p' a. p \<longmapsto>a p' \<longrightarrow> 
       (\<exists> q'. ((p',q')\<in>R1) \<and> (q \<Rightarrow>^a q')))
  \<and> (\<exists> q'. q \<longmapsto>*tau q' \<and> ((q',p)\<in>R1)) }\<close>

lemma mono_fp_step:
  \<open>mono fp_step\<close>
proof (rule, safe)
  fix x y::\<open>'s rel\<close> and p q
  assume
    \<open>x \<subseteq> y\<close>
    \<open>(p, q) \<in> fp_step x\<close>
  thus  \<open>(p, q) \<in> fp_step y\<close>
    unfolding fp_step_def
    by (auto, blast)
qed

lemma fp_fp_step:
  assumes
    \<open>R = fp_step R\<close>
  shows
    \<open>coupled_simulation (\<lambda> p q. (p, q) \<in> R)\<close>
  using assms unfolding fp_step_def coupled_simulation_def
  by fastforce

lemma gfp_fp_step_subset_gcs:
  shows \<open>(gfp fp_step) \<subseteq> { (p,q) . greatest_coupled_simulation p q }\<close>
  unfolding gcs_eq_coupled_sim_by[symmetric]
proof clarify
  fix a b
  assume
    \<open>(a, b) \<in> gfp fp_step\<close>
  thus \<open>a \<sqsubseteq>cs  b\<close>
    using fp_fp_step mono_fp_step gfp_unfold by auto
qed

lemma fp_fp_step_gcs:
  assumes
    \<open>R = { (p,q) . greatest_coupled_simulation p q }\<close>
  shows
    \<open>fp_step R = R\<close>
  unfolding assms
proof safe
  fix p q
  assume
    \<open>(p, q) \<in> fp_step {(x, y). greatest_coupled_simulation x y}\<close>
  hence \<open>(\<forall>p' a. p \<longmapsto>a  p' \<longrightarrow> (\<exists>q'. greatest_coupled_simulation p' q' \<and> q \<Rightarrow>^a  q')) \<and>
    (\<exists>q'. q \<longmapsto>* tau  q' \<and> greatest_coupled_simulation q' p)\<close>
    unfolding fp_step_def by auto
  hence \<open>(\<forall>p' a. p \<longmapsto>a  p' \<longrightarrow> (\<exists>q'. greatest_coupled_simulation p' q' \<and> q \<Rightarrow>^^ a  q')) \<and>
    (\<exists>q'. q \<longmapsto>* tau  q' \<and> greatest_coupled_simulation q' p)\<close> using weak_step_tau2_def by simp
  thus \<open>greatest_coupled_simulation p q\<close>
    using lts_tau.gcs by metis
next
  fix p q
  assume
    \<open>greatest_coupled_simulation p q\<close>
  hence \<open>(p, q) \<in> {(x, y). greatest_coupled_simulation x y} \<and> (\<forall> p' a. p \<longmapsto>a p' \<longrightarrow> 
      (\<exists> q'. (greatest_coupled_simulation p' q') \<and> (q \<Rightarrow>^a q')))
    \<and> (\<exists> q'. q \<longmapsto>*tau q' \<and> (greatest_coupled_simulation q' p))\<close>
    using gcs_is_coupled_simulation unfolding coupled_simulation_def by blast
  thus \<open>(p, q) \<in> fp_step {(x, y). greatest_coupled_simulation x y}\<close>
    unfolding fp_step_def by blast
qed

lemma gfp_fp_step_gcs: \<open>gfp fp_step = { (p,q) . greatest_coupled_simulation p q }\<close>
  using fp_fp_step_gcs gfp_fp_step_subset_gcs
  by (simp add: equalityI gfp_upperbound)

end

context lts_tau_finite
begin
lemma gfp_fp_step_while:
  shows
    \<open>gfp fp_step = while (\<lambda>R. fp_step R \<noteq> R) fp_step top\<close>
  using gfp_while_lattice[OF mono_fp_step] finite_state_rel Finite_Set.finite_set by blast

theorem coupled_sim_fp_step_while:
  shows \<open>while (\<lambda>R. fp_step R \<noteq> R) fp_step top = { (p,q) . greatest_coupled_simulation p q }\<close>
  using gfp_fp_step_while gfp_fp_step_gcs by blast

end


end
