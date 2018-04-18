section \<open>Definitions of Coupled Similarity and Simulations\<close>

theory Coupled_Simulation
  imports Weak_Relations
begin

context lts_tau
begin

subsection \<open>Van Glabbeeks's Coupled Simulation\<close>
  
text {*
  We will mainly use van glabbeks coupled simulation from his 2017 CSP paper.
  The other definitions are just introduces for comparison.
  So, all the other coupled simulations of this Section, will not really be of interest later on.
*}
  
definition coupled_simulation ::
  "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
  where
  "coupled_simulation R  \<equiv> \<forall> p q . 
    (R p q \<longrightarrow> 
      ((\<forall> p' a. p \<longmapsto> a p' \<longrightarrow> 
        (\<exists> q'. R p' q' \<and> (q \<longmapsto>^a q')))
      \<and> (\<exists> q'. q \<longmapsto>*tau q' \<and> R q' p)))"
  
abbreviation coupled_simulated_by :: "'s \<Rightarrow> 's \<Rightarrow> bool" ("_ \<sqsubseteq>cs  _" [60, 60] 65)
  where "coupled_simulated_by p q \<equiv> \<exists> R . coupled_simulation R \<and> R p q"
    
abbreviation coupled_similar :: "'s \<Rightarrow> 's \<Rightarrow> bool" ("_ \<equiv>cs  _" [60, 60] 65)
  where "coupled_similar p q \<equiv> p \<sqsubseteq>cs q \<and> q \<sqsubseteq>cs p"
 
subsection \<open>Parrow 92 S-Coupled Simulation\<close>

definition coupled_simulation_p92 :: 
  "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
where
  "coupled_simulation_p92 R1 R2 \<equiv> \<forall> p q . 
    (R1 p q \<longrightarrow> 
      ((\<forall> p' a. p \<longmapsto> a p' \<longrightarrow> 
        (\<exists> q'. R1 p' q' \<and> 
          (q \<longmapsto>^ a q')))
      \<and> (stable_state p \<longrightarrow> R2 p q))) \<and>
    (R2 p q \<longrightarrow> 
      ((\<forall> q' a. q \<longmapsto> a q' \<longrightarrow>
        (\<exists> p'. R2 p' q' \<and> 
          (p \<longmapsto>^ a p')))
      \<and> (stable_state q \<longrightarrow> R1 p q)))"

lemma weak_bisim_implies_coupled_sim_p92:
  assumes "weak_bisimulation R"
  shows "coupled_simulation_p92 R R"
using assms unfolding weak_bisimulation_def coupled_simulation_p92_def by blast
  
lemma coupled_sim_p92_symm:
  assumes "coupled_simulation_p92 R1 R2"
  shows "coupled_simulation_p92 (\<lambda> p q. R2 q p) (\<lambda> p q. R1 q p)"
using assms unfolding coupled_simulation_p92_def by blast
  
subsection \<open>Sangiorgi 2012 S-Coupled Simulation\<close>

definition s_coupled_simulation_sangiorgi12 :: 
  "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
where
  "s_coupled_simulation_sangiorgi12 R1 R2 \<equiv>
    weak_simulation R1 \<and> weak_simulation (\<lambda> p q . R2 q p)
  \<and> (\<forall> p q . R1 p q \<longrightarrow> stable_state p \<longrightarrow> R2 p q)
  \<and> (\<forall> p q . R2 p q \<longrightarrow> stable_state q \<longrightarrow> R1 p q)"

abbreviation s_coupled_simulated_by :: "'s \<Rightarrow> 's \<Rightarrow> bool" ("_ \<sqsubseteq>scs  _" [60, 60] 65)
  where "s_coupled_simulated_by p q \<equiv>
    \<exists> R1 R2 . s_coupled_simulation_sangiorgi12 R1 R2 \<and> R1 p q"
    
abbreviation s_coupled_similar :: "'s \<Rightarrow> 's \<Rightarrow> bool" ("_ \<equiv>scs  _" [60, 60] 65)
  where "s_coupled_similar p q \<equiv>
    \<exists> R1 R2 . s_coupled_simulation_sangiorgi12 R1 R2 \<and> R1 p q \<and> R2 p q"

lemma s_coupled_sim_is_original_coupled:
  "s_coupled_simulation_sangiorgi12 = coupled_simulation_p92"
unfolding coupled_simulation_p92_def
  s_coupled_simulation_sangiorgi12_def weak_simulation_def by blast
 
corollary weak_bisim_implies_s_coupled_sim:
  assumes "weak_bisimulation R"
  shows "s_coupled_simulation_sangiorgi12 R R"
  using assms s_coupled_sim_is_original_coupled weak_bisim_implies_coupled_sim_p92 by simp
   
corollary s_coupled_sim_symm:
  assumes "s_coupled_simulation_sangiorgi12 R1 R2"
  shows "s_coupled_simulation_sangiorgi12 (\<lambda> p q. R2 q p) (\<lambda> p q. R1 q p)"
  using assms coupled_sim_p92_symm s_coupled_sim_is_original_coupled by simp
   
corollary s_coupled_sim_union_cl:
  assumes
    "s_coupled_simulation_sangiorgi12 RA1 RA2"
    "s_coupled_simulation_sangiorgi12 RB1 RB2"
  shows
    "s_coupled_simulation_sangiorgi12 (\<lambda> p q. RA1 p q \<or> RB1 p q) (\<lambda> p q. RA2 p q \<or> RB2 p q)"
  using assms weak_sim_union_cl unfolding s_coupled_simulation_sangiorgi12_def by auto
    
corollary s_coupled_sim_symm_union:
  assumes "s_coupled_simulation_sangiorgi12 R1 R2"
  shows "s_coupled_simulation_sangiorgi12 (\<lambda> p q. R1 p q \<or> R2 q p) (\<lambda> p q. R2 p q \<or> R1 q p)"
  using s_coupled_sim_union_cl[OF assms s_coupled_sim_symm[OF assms]] .

lemma s_coupledsim_stable_eq:
  assumes
    "p \<sqsubseteq>scs q"
    "stable_state p"
  shows  "p \<equiv>scs q" 
proof -
  obtain R1 R2 where "R1 p q" "weak_simulation R1" "weak_simulation (\<lambda>p q. R2 q p)"
      "\<forall>p q. R1 p q \<longrightarrow> stable_state p \<longrightarrow> R2 p q" "\<forall>p q. R2 p q \<longrightarrow> stable_state q \<longrightarrow> R1 p q"
    using assms(1)  unfolding s_coupled_simulation_sangiorgi12_def by blast
  moreover hence "R2 p q" using assms(2) by blast
  ultimately show ?thesis unfolding s_coupled_simulation_sangiorgi12_def by blast
qed

lemma s_coupledsim_symm:
  assumes
    "p \<equiv>scs q" 
  shows 
    "q \<equiv>scs p" 
  using assms s_coupled_sim_symm by blast

lemma s_coupledsim_eq_parts:
  assumes
    "p \<equiv>scs q"
  shows
    "p \<sqsubseteq>scs q"
    "q \<sqsubseteq>scs p"
  using assms s_coupledsim_symm by metis+

subsection \<open>Sangiorgi 2012 Coupled Simulation\<close>
  
definition coupled_simulation_sangiorgi12 :: 
  "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
where
  "coupled_simulation_sangiorgi12 R1 R2 \<equiv>
    weak_simulation R1 \<and> weak_simulation (\<lambda> p q . R2 q p)
  \<and> (\<forall> p q . R1 p q \<longrightarrow> (\<exists> q' . q \<longmapsto>* tau q' \<and> R2 p q'))
  \<and> (\<forall> p q . R2 p q \<longrightarrow> (\<exists> p' . p \<longmapsto>* tau p' \<and> R1 p' q))"
  
lemma weak_bisim_implies_coupled_sim_sangiorgi12:
  assumes "weak_bisimulation R"
  shows "coupled_simulation_sangiorgi12 R R"
  using assms weak_bisim_weak_sim steps.refl[of _ tau]
  unfolding coupled_simulation_sangiorgi12_def
  by blast

section \<open>Properties of Coupled Simulation\<close>

subsection \<open>Position between Weak Simulation and Bisimulation\<close>

lemma coupled_simulation_weak_simulation:
  "coupled_simulation R = (weak_simulation R \<and> (\<forall> p q . R p q \<longrightarrow> (\<exists> q'. q \<longmapsto>*tau q' \<and> R q' p)))"
  unfolding coupled_simulation_def weak_simulation_def by blast

corollary coupled_simulation_implies_weak_simulation:
  assumes "coupled_simulation R"
  shows "weak_simulation R"
  using assms unfolding coupled_simulation_weak_simulation ..

corollary coupledsim_enabled_subs:
  assumes
    "p \<sqsubseteq>cs q"
    "weak_enabled p a"
    "\<not> tau a"
  shows "weak_enabled q a"
  using assms weak_sim_enabled_subs coupled_simulation_implies_weak_simulation by blast

lemma coupled_simulation_implies_coupling:
  assumes
    "coupled_simulation R"
    "R p q"
  shows
    "\<exists> q'. q \<longmapsto>*tau q' \<and> R q' p"
  using assms unfolding coupled_simulation_weak_simulation by blast

lemma weak_bisim_implies_coupled_sim_gla17:
  assumes
    wbisim:   "weak_bisimulation R" and
    symmetry: "\<And> p q . R p q \<Longrightarrow> R q p"
    -- "symmetry is needed here, which is alright because bisimilarity is symmetric."
  shows "coupled_simulation R"
unfolding coupled_simulation_def proof safe
  fix p q p' a
  assume "R p q" "p \<longmapsto>a  p'"
  thus "\<exists>q'. R p' q' \<and> (q \<longmapsto>^ a  q')"
    using wbisim unfolding weak_bisimulation_def by simp
next
  fix p q 
  assume "R p q"
  thus "\<exists>q'. q \<longmapsto>* tau  q' \<and> R q' p" 
    using symmetry steps.refl[of q tau] by auto
qed

subsection \<open>Coupled Simulation and Silent Steps\<close>

lemma coupledsim_step_gla17:
  "coupled_simulation (\<lambda> p1 q1 . q1 \<longmapsto>* tau p1)"
  unfolding coupled_simulation_def
  using lts.steps.simps by metis

corollary coupledsim_step:
  assumes
    "p \<longmapsto>* tau  q"
  shows
    "q \<sqsubseteq>cs p"
  using assms coupledsim_step_gla17 by auto

text \<open>A direct implication of this is that states on a tau loop are coupled similar.\<close>
corollary strongly_tau_connected_coupled_similar:
  assumes
    "p \<longmapsto>* tau  q"
    "q \<longmapsto>* tau  p"
  shows "p \<equiv>cs q"
  using assms coupledsim_step by auto

lemma silent_steps_retain_coupled_simulation:
assumes 
  "coupled_simulation R"
  "R p q"
  "p \<longmapsto>* A  p'"
  "A = tau" --{*some hack because the induction would always eat my tau when i placed it right in the @{text "\<longmapsto>* tau"} part . why is this?!*}
shows "\<exists> q' . q \<longmapsto>* A q' \<and> R p' q'"
  using assms(1,3,2,4) steps_retain_weak_sim
  unfolding coupled_simulation_weak_simulation by blast
  
lemma coupled_simulation_weak_premise:
  "coupled_simulation R 
  = (\<forall> p q . (R p q \<longrightarrow> 
      ((\<forall> p' a. p \<longmapsto>^a p' \<longrightarrow> 
        (\<exists> q'. R p' q' \<and> (q \<longmapsto>^a q')))
      \<and> (\<exists> q'. q \<longmapsto>*tau q' \<and> R q' p))))"
proof 
  assume weak_prem: "\<forall> p q . R p q \<longrightarrow> (\<forall>p' a. p \<longmapsto>^ a  p' \<longrightarrow> (\<exists>q'. R p' q' \<and> q \<longmapsto>^ a  q')) \<and> (\<exists>q'. q \<longmapsto>* tau  q' \<and> R q' p)"
  thus "coupled_simulation R"
    unfolding coupled_simulation_def
  proof (safe)
    fix p q p' a
    assume "R p q" "p \<longmapsto>a  p'"
    thus "\<exists>q'. R p' q' \<and> q \<longmapsto>^ a  q'" using step_weak_step_tau[OF `p \<longmapsto>a  p'`] weak_prem by blast
  next
    fix p q
    assume "R p q"
    thus "\<exists>q'. q \<longmapsto>* tau  q' \<and> R q' p" using weak_prem by blast
  qed
next
  assume CS: "coupled_simulation R"
  show "\<forall>p q. R p q \<longrightarrow> (\<forall>p' a. p \<longmapsto>^ a  p' \<longrightarrow> (\<exists>q'. R p' q' \<and> q \<longmapsto>^ a  q')) \<and> (\<exists>q'. q \<longmapsto>* tau  q' \<and> R q' p)"
  proof safe
    fix p q p' a pq1 pq2
    assume case_assms:
      "R p q"
      "p \<longmapsto>* tau  pq1"
      "pq1 \<longmapsto>a  pq2"
      "pq2 \<longmapsto>* tau  p'"
    then obtain q' where q'_def: "q \<longmapsto>* tau  q'" "R pq1 q'"
      using silent_steps_retain_coupled_simulation[OF CS] by blast
    then moreover obtain q'' where q''_def: "R pq2 q''" "q' \<longmapsto>^ a  q''"
      using CS case_assms(3) unfolding coupled_simulation_def by blast
    then moreover obtain q''' where q''_def: "R p' q'''" "q'' \<longmapsto>* tau  q'''"
      using case_assms(4) silent_steps_retain_coupled_simulation[OF CS] by blast
    ultimately show "\<exists> q'''. R p' q''' \<and> q \<longmapsto>^ a  q'''" using weak_step_extend by blast
  next
    fix p q p' a
    assume
      "R p q"
      "p \<longmapsto>* tau  p'"
      "\<nexists>q'. R p' q' \<and> q \<longmapsto>^ a  q'"
      "tau a"
    thus "False"
      using silent_steps_retain_coupled_simulation[OF CS] by blast
  next
    --"case identical to first case"
    fix p q p' a pq1 pq2
    assume case_assms:
      "R p q"
      "p \<longmapsto>* tau  pq1"
      "pq1 \<longmapsto>a  pq2"
      "pq2 \<longmapsto>* tau  p'"
    then obtain q' where q'_def: "q \<longmapsto>* tau  q'" "R pq1 q'"
      using silent_steps_retain_coupled_simulation[OF CS] by blast
    then moreover obtain q'' where q''_def: "R pq2 q''" "q' \<longmapsto>^ a  q''"
      using CS case_assms(3) unfolding coupled_simulation_def by blast
    then moreover obtain q''' where q''_def: "R p' q'''" "q'' \<longmapsto>* tau  q'''"
      using case_assms(4) silent_steps_retain_coupled_simulation[OF CS] by blast
    ultimately show "\<exists> q'''. R p' q''' \<and> q \<longmapsto>^ a  q'''" using weak_step_extend by blast
  next
    fix p q
    assume
      "R p q"
    thus "\<exists>q'. q \<longmapsto>* tau  q' \<and> R q' p" using CS unfolding coupled_simulation_def by blast
  qed
qed

subsection \<open>Closure, Preorder and Symmetry Properties\<close>
  
lemma coupledsim_union:
  assumes
    "coupled_simulation R1"
    "coupled_simulation R2"
  shows
    "coupled_simulation (\<lambda> p q . R1 p q \<or> R2 p q)"
  using assms unfolding coupled_simulation_def by (blast)  
  
lemma coupledsim_refl:
  "p \<sqsubseteq>cs p"
  using coupledsim_step steps.refl by auto
    
lemma coupledsim_trans:
  assumes
    "p \<sqsubseteq>cs pq"
    "pq \<sqsubseteq>cs q"
  shows
    "p \<sqsubseteq>cs q"
proof -
  obtain R1 where R1_def: "coupled_simulation R1" "R1 p pq"
    using assms(1) by blast
  obtain R2 where R2_def: "coupled_simulation R2" "R2 pq q"
    using assms(2) by blast
  define R where R_def: "R \<equiv> \<lambda> p q . \<exists> pq . (R1 p pq \<and> R2 pq q) \<or> (R2 p pq \<and> R1 pq q)"
  have "weak_simulation R" "R p q"
    using weak_sim_trans_constructive
      R1_def(2) R2_def(2)
      coupled_simulation_implies_weak_simulation[OF R1_def(1)]
      coupled_simulation_implies_weak_simulation[OF R2_def(1)] 
    unfolding R_def by auto
  moreover have "(\<forall> p q . R p q \<longrightarrow> (\<exists> q'. q \<longmapsto>*tau q' \<and> R q' p))"
    unfolding R_def
  proof safe
    fix p q pq
    assume r1r2: "R1 p pq" "R2 pq q"
    then obtain pq' where "R1 pq' p" "pq \<longmapsto>* tau  pq'"
      using r1r2 R1_def(1) unfolding coupled_simulation_weak_premise by blast
    then moreover obtain q' where "R2 pq' q'" "q \<longmapsto>* tau q'"
      using r1r2 R2_def(1) weak_step_tau_tau[OF `pq \<longmapsto>* tau  pq'`] tau_tau
      unfolding coupled_simulation_weak_premise by blast
    then moreover obtain q'' where "R2 q'' pq'" "q' \<longmapsto>* tau  q''"
      using R2_def(1) unfolding coupled_simulation_weak_premise by blast
    ultimately show "\<exists>q'. q \<longmapsto>* tau  q' \<and> (\<exists>pq. R1 q' pq \<and> R2 pq p \<or> R2 q' pq \<and> R1 pq p)"
      using steps_concat by blast
  next --"analogous with R2 and R1 swapped"
    fix p q pq
    assume r2r1: "R2 p pq" "R1 pq q"
    then obtain pq' where "R2 pq' p" "pq \<longmapsto>* tau  pq'"
      using r2r1 R2_def(1) unfolding coupled_simulation_weak_premise by blast
    then moreover obtain q' where "R1 pq' q'" "q \<longmapsto>* tau q'"
      using r2r1 R1_def(1) weak_step_tau_tau[OF `pq \<longmapsto>* tau  pq'`] tau_tau
      unfolding coupled_simulation_weak_premise by blast
    then moreover obtain q'' where "R1 q'' pq'" "q' \<longmapsto>* tau  q''"
      using R1_def(1) unfolding coupled_simulation_weak_premise by blast
    ultimately show "\<exists>q'. q \<longmapsto>* tau  q' \<and> (\<exists>pq. R1 q' pq \<and> R2 pq p \<or> R2 q' pq \<and> R1 pq p)"
      using steps_concat by blast
  qed
  ultimately have "R p q" "coupled_simulation R"
    using coupled_simulation_weak_simulation by auto
  thus ?thesis by blast
qed

lemma coupled_similarity_equivalence:
  "equivp (\<lambda> p q. p \<equiv>cs q)"
proof (rule equivpI)
  show "reflp coupled_similar"
    unfolding reflp_def using coupledsim_refl by blast
next
  show "symp coupled_similar"
    unfolding symp_def by blast
next
  show "transp coupled_similar"
    unfolding transp_def using coupledsim_trans by meson
qed

lemma coupledsim_tau_max_eq:
  assumes
    "p \<sqsubseteq>cs q"
    "tau_max q"
  shows  "p \<equiv>cs q" 
  using assms using coupled_simulation_weak_simulation coupling_tau_max_symm by metis

corollary coupledsim_stable_eq:
  assumes
    "p \<sqsubseteq>cs q"
    "stable_state q"
  shows  "p \<equiv>cs q" 
  using assms using coupled_simulation_weak_simulation coupling_stability_symm by metis

subsection \<open>Coinductive Coupled Simulation Preorder\<close>

coinductive greatest_coupled_simulation :: "'s \<Rightarrow> 's \<Rightarrow> bool"
  where gcs:
    "\<lbrakk>\<And> a p' . p \<longmapsto> a p' \<Longrightarrow> \<exists>q'. q \<longmapsto>^^ a q' \<and> greatest_coupled_simulation p' q'; 
      \<exists> q' . q \<longmapsto>* tau q' \<and> greatest_coupled_simulation q' p\<rbrakk>
  \<Longrightarrow> greatest_coupled_simulation p q"

lemma gcs_implies_gws:
  assumes "greatest_coupled_simulation p q"
  shows "greatest_weak_simulation p q"
  using assms by (metis greatest_coupled_simulation.cases greatest_weak_simulation.coinduct)

lemma gcs_is_coupled_simulation:
  shows "coupled_simulation greatest_coupled_simulation"
  unfolding coupled_simulation_def
proof safe
  --"identical to ws"
  fix p q p' a
  assume ih:
    "greatest_coupled_simulation p q"
    "p \<longmapsto>a  p'"
  hence "(\<forall>x xa. p \<longmapsto>x xa \<longrightarrow> (\<exists>q'. q \<longmapsto>^^ x  q' \<and> greatest_coupled_simulation xa q')) "
    by (meson greatest_coupled_simulation.simps)
  then obtain q' where "q \<longmapsto>^^ a  q' \<and> greatest_coupled_simulation p' q'" using ih by blast
  thus "\<exists>q'. greatest_coupled_simulation p' q' \<and> q \<longmapsto>^ a  q'"
    unfolding weak_step_tau2_def by blast
next
  fix p q
  assume
    "greatest_coupled_simulation p q"
  thus "\<exists>q'. q \<longmapsto>* tau  q' \<and> greatest_coupled_simulation q' p"
    by (meson greatest_coupled_simulation.simps)
qed

lemma coupled_similarity_implies_gcs:
  assumes "p \<sqsubseteq>cs q"
  shows "greatest_coupled_simulation p q"
  using assms
proof (coinduct, simp del: weak_step_tau2_def, safe)
  fix x1 x2 R a xa
  assume ih: "coupled_simulation R" "R x1 x2" "x1 \<longmapsto>a  xa"
  then obtain q' where"x2 \<longmapsto>^^ a  q'" "R xa q'"
    unfolding coupled_simulation_def weak_step_tau2_def by blast
  thus "\<exists>q'. x2 \<longmapsto>^^ a  q' \<and> (xa \<sqsubseteq>cs  q' \<or> greatest_coupled_simulation xa q')"
    using ih by blast
next
  fix x1 x2 R
  assume ih: "coupled_simulation R" "R x1 x2"
  then obtain q' where"x2 \<longmapsto>* tau  q' " "R q' x1"
    unfolding coupled_simulation_def by blast
  thus "\<exists>q'. x2 \<longmapsto>* tau  q' \<and> (q' \<sqsubseteq>cs  x1 \<or> greatest_coupled_simulation q' x1)"
    using ih by blast
qed

lemma gcs_eq_coupled_sim_by:
  shows "p \<sqsubseteq>cs q = greatest_coupled_simulation p q"
  using coupled_similarity_implies_gcs gcs_is_coupled_simulation by blast

lemma coupled_sim_by_is_coupled_sim:
  shows
    "coupled_simulation (\<lambda> p q . p \<sqsubseteq>cs q)"
  unfolding gcs_eq_coupled_sim_by using gcs_is_coupled_simulation .

lemma coupledsim_unfold:
  shows "p \<sqsubseteq>cs q =
    ((\<forall>a p'. p \<longmapsto>a  p' \<longrightarrow> (\<exists>q'. q \<longmapsto>^ a  q' \<and> p' \<sqsubseteq>cs q')) \<and>
       (\<exists>q'. q \<longmapsto>* tau  q' \<and> q' \<sqsubseteq>cs p))"
  unfolding gcs_eq_coupled_sim_by weak_step_tau2_def[symmetric]
  by (metis lts_tau.greatest_coupled_simulation.simps)

subsection \<open>Coupled Simulation Join\<close>

--"Proposition 3 in @{cite glabbeek17}"
lemma coupledsim_choice_1:
  assumes 
    "p \<sqsubseteq>cs q"
    "\<And> pq a . pqc \<longmapsto> a pq \<longleftrightarrow> (a = \<tau> \<and> (pq = p \<or> pq = q))"
  shows
    "pqc \<sqsubseteq>cs q"
    "q \<sqsubseteq>cs pqc"
proof -
  define R1 where "R1 \<equiv> (\<lambda>p1 q1. q1 \<longmapsto>* tau  p1)"
  have "R1 q pqc"
    using assms(2) steps_one_step R1_def by simp
  moreover have "coupled_simulation R1"
    unfolding R1_def using coupledsim_step_gla17 .
  ultimately show q_pqc: "q \<sqsubseteq>cs pqc" by blast
--"next case"
  define R where "R \<equiv> \<lambda> p0 q0 . p0 = q \<and> q0 = pqc \<or> p0 = pqc \<and> q0 = q \<or> p0 = p \<and> q0 = q"
  hence "R pqc q" by blast
  thus "pqc \<sqsubseteq>cs  q"
    unfolding gcs_eq_coupled_sim_by
  proof (coinduct, auto)
    fix x1 x2 x xa
    assume ih:
      "R x1 x2"
      "x1 \<longmapsto>x  xa"
    hence "x1 = q \<and> x2 = pqc \<or> x1 = pqc \<and> x2 = q \<or> x1 = p \<and> x2 = q" using R_def by auto
    thus "\<exists>q'. (tau x \<longrightarrow> x2 \<longmapsto>* tau  q') \<and>
                (\<not> tau x \<longrightarrow> (\<exists>pq1. x2 \<longmapsto>* tau  pq1 \<and> (\<exists>pq2. pq1 \<longmapsto>x  pq2 \<and> pq2 \<longmapsto>* tau  q'))) \<and>
                (R xa q' \<or> greatest_coupled_simulation xa q')"
    proof safe
      assume "x1 = q" "x2 = pqc"
      thus "\<exists>q'. (tau x \<longrightarrow> pqc \<longmapsto>* tau  q') \<and>
         (\<not> tau x \<longrightarrow> (\<exists>pq1. pqc \<longmapsto>* tau  pq1 \<and> (\<exists>pq2. pq1 \<longmapsto>x  pq2 \<and> pq2 \<longmapsto>* tau  q')))
          \<and> (R xa q' \<or> greatest_coupled_simulation xa q')" 
        using ih `q \<sqsubseteq>cs pqc`
          coupled_simulation_implies_weak_simulation[OF gcs_is_coupled_simulation] 
        unfolding gcs_eq_coupled_sim_by
        by (metis (full_types) weak_sim_ruleformat)
    next
      assume "x1 = pqc" "x2 = q"
      hence "x = \<tau> \<and> (xa = q \<or> xa = p)" using ih(2) assms(2) by blast
      thus "\<exists>q'. (tau x \<longrightarrow> q \<longmapsto>* tau  q') \<and>
         (\<not> tau x \<longrightarrow> (\<exists>pq1. q \<longmapsto>* tau  pq1 \<and> (\<exists>pq2. pq1 \<longmapsto>x  pq2 \<and> pq2 \<longmapsto>* tau  q')))
          \<and> (R xa q' \<or> greatest_coupled_simulation xa q')"
        unfolding gcs_eq_coupled_sim_by[symmetric] 
        using steps.refl[of q tau] `p \<sqsubseteq>cs q` coupledsim_refl tau_tau
        by auto
    next
      assume "x1 = p" "x2 = q"
      thus "\<exists>q'. (tau x \<longrightarrow> q \<longmapsto>* tau  q') \<and>
         (\<not> tau x \<longrightarrow> (\<exists>pq1. q \<longmapsto>* tau  pq1 \<and> (\<exists>pq2. pq1 \<longmapsto>x  pq2 \<and> pq2 \<longmapsto>* tau  q')))
          \<and> (R xa q' \<or> greatest_coupled_simulation xa q')"
        using ih `p \<sqsubseteq>cs q`
          coupled_simulation_implies_weak_simulation[OF gcs_is_coupled_simulation] 
        unfolding gcs_eq_coupled_sim_by
        by (metis (full_types) weak_sim_ruleformat)
    qed
  next
    fix x1 x2
    assume
      "R x1 x2"
    hence "x1 = q \<and> x2 = pqc \<or> x1 = pqc \<and> x2 = q \<or> x1 = p \<and> x2 = q" using R_def by auto
    thus "\<exists>q'. x2 \<longmapsto>* tau  q' \<and> (R q' x1 \<or> greatest_coupled_simulation q' x1)"
    proof (auto)
      show "\<exists>q'. pqc \<longmapsto>* tau  q' \<and> (R q' q \<or> greatest_coupled_simulation q' q)"
        using \<open>R pqc q\<close> steps.simps by blast
    next
      show "\<exists>q'. q \<longmapsto>* tau  q' \<and> (R q' pqc \<or> greatest_coupled_simulation q' pqc)"
        using \<open>R1 q pqc\<close> \<open>coupled_simulation R1\<close> coupled_similarity_implies_gcs steps.refl by blast
    next
      show "\<exists>q'. q \<longmapsto>* tau  q' \<and> (R q' p \<or> greatest_coupled_simulation q' p)"
        using assms(1) coupled_simulation_weak_simulation
          lts_tau.coupled_similarity_implies_gcs by fastforce
    qed
  qed
qed

--\<open>the opposite direction is trivial\<close>
lemma coupledsim_choice_2:
  assumes 
    "pqc \<sqsubseteq>cs q" 
    "\<And> pq a . pqc \<longmapsto> a pq \<longleftrightarrow> (a = \<tau> \<and> (pq = p \<or> pq = q))"
  shows
    "p \<sqsubseteq>cs q"
proof -
  have "pqc \<longmapsto> \<tau> p" using assms(2) by blast
  then obtain q' where "q \<longmapsto>* tau q'" "p \<sqsubseteq>cs q'"
    using assms(1) tau_tau unfolding coupled_simulation_def by blast
  then moreover have "q' \<sqsubseteq>cs q" using coupledsim_step_gla17 by blast
  ultimately show ?thesis using coupledsim_trans tau_tau by blast
qed

lemma coupledsim_choice_join:
  assumes 
    "\<And> pq a . pqc \<longmapsto> a pq \<longleftrightarrow> (a = \<tau> \<and> (pq = p \<or> pq = q))"
  shows
    "p \<sqsubseteq>cs q \<longleftrightarrow> pqc \<equiv>cs q"
  using  coupledsim_choice_1[OF _ assms] coupledsim_choice_2[OF _ assms] by blast

subsection \<open>More on the Relationship to Contra, Delay and Weak Simulation\<close>

lemma coupled_similarity_delay_simulation:
  "delay_simulation (\<lambda> p q. p \<sqsubseteq>cs q)"
  unfolding delay_simulation_def
proof safe
  fix p q R p' a
  assume assms:
    "coupled_simulation R"
    "R p q "
    "p \<longmapsto> a p'"
  show "\<exists>q'. p' \<sqsubseteq>cs  q' \<and> q \<longmapsto>^~ a  q'"
  proof -
    obtain q''' where q'''_spec: "q \<longmapsto>^ a q'''" "p' \<sqsubseteq>cs q'''"
      using assms coupled_simulation_implies_weak_simulation weak_sim_ruleformat by metis
    show ?thesis
    proof (cases "tau a")
      case True
      then have "q \<longmapsto>* tau q'''" using q'''_spec by blast
      thus ?thesis using q'''_spec(2) True assms(1) steps.refl by blast
    next
      case False
      then obtain q' q'' where q'q''_spec:
          "q \<longmapsto>* tau q'" "q' \<longmapsto> a q''" "q'' \<longmapsto>* tau q'''"
        using q'''_spec by blast
      hence "q''' \<sqsubseteq>cs q''" using coupledsim_step by blast
      hence "p' \<sqsubseteq>cs q''" using q'''_spec(2) coupledsim_trans by blast
      thus ?thesis using q'q''_spec(1,2) False by blast
    qed
  qed
qed

lemma coupled_sim_by_eq_delay_coupled_simulation:
  "(p \<sqsubseteq>cs q) = (\<exists>R. R p q \<and> delay_simulation R \<and> coupling R)"
proof
  assume "p \<sqsubseteq>cs q"
  define R where "R \<equiv> coupled_simulated_by"
  hence "R p q \<and> delay_simulation R \<and> coupling R"
    using coupled_similarity_delay_simulation coupled_sim_by_is_coupled_sim
        coupled_simulation_implies_coupling \<open>p \<sqsubseteq>cs q\<close> by blast
  thus "\<exists>R. R p q \<and> delay_simulation R \<and> coupling R" by blast
next
  assume "\<exists>R. R p q \<and> delay_simulation R \<and> coupling R"
  then obtain R where "R p q" "delay_simulation R" "coupling R" by blast
  hence "coupled_simulation R"
    using delay_simulation_implies_weak_simulation coupled_simulation_weak_simulation by blast
  thus "p \<sqsubseteq>cs q" using \<open>R p q\<close> by blast
qed  

lemma weak_sim_and_contrasim_implies_coupled_sim:
  assumes
    "contrasim R"
    "weak_simulation R"
  shows
    "coupled_simulation R"
  unfolding coupled_simulation_weak_simulation
  using contrasim_implies_coupling assms by blast

lemma coupledsim_implies_contrasim:
  assumes
    "coupled_simulation R"
  shows 
    "contrasim R"
proof -
  have "contrasim_step R"
  unfolding contrasim_step_def
  proof (rule allI impI)+
    fix p q p' a
    assume
      "R p q \<and> p \<longmapsto>^ a  p'"
    then obtain q' where q'_def: "R p' q'" "q \<longmapsto>^ a  q'"
      using assms unfolding coupled_simulation_weak_premise by blast
    then obtain q'' where q''_def: "R q'' p'" "q' \<longmapsto>* tau  q''"
      using assms unfolding coupled_simulation_weak_premise by blast
    then have "q \<longmapsto>^ a  q''" using q'_def(2) steps_concat by blast
    thus "\<exists>q'. q \<longmapsto>^ a  q' \<and> R q' p'"
      using q''_def(1) by blast
  qed
  thus "contrasim R" using contrasim_step_seq_coincide_for_sims
      coupled_simulation_implies_weak_simulation[OF assms] by blast 
qed

lemma coupled_simulation_iff_weak_sim_and_contrasim:
  shows "coupled_simulation R \<longleftrightarrow> contrasim R \<and> weak_simulation R"
  using weak_sim_and_contrasim_implies_coupled_sim
    coupledsim_implies_contrasim coupled_simulation_weak_simulation by blast

text \<open>If there is a sink every state can reach via tau steps, then weak simulation implies
  (and thus coincides with) coupled simulation.\<close>
lemma tau_sink_sim_coupledsim:
  assumes
    "\<And> p . (p \<longmapsto>* tau sink)"
    "\<And> p . R sink p"
    "weak_simulation R"
  shows
    "coupled_simulation R"
  unfolding coupled_simulation_def
proof safe
  show " \<And>p q p' a. R p q \<Longrightarrow> p \<longmapsto>a  p' \<Longrightarrow> \<exists>q'. R p' q' \<and> q \<longmapsto>^ a  q'"
    using assms(3) unfolding weak_simulation_def by blast
next
  fix p q
  assume "R p q"
  hence "q \<longmapsto>* tau sink \<and> R sink p"
    using assms(1,2) by blast
  thus "\<exists>q'. q \<longmapsto>* tau  q' \<and> R q' p" by blast
qed

subsection \<open>Coupled Simulation, Divergence, Taus\<close>

text{* if there are no tau-steps, coupled simulations must be symmetric.*}
lemma taufree_coupledsim_symm:
  assumes
    "\<And> p1 a p2 . (p1 \<longmapsto> a p2 \<Longrightarrow> \<not> tau a)"
    "coupled_simulation R"
    "R p q"
  shows "R q p"
  using assms(1,3) taufree_contrasim_symm coupledsim_implies_contrasim[OF assms(2)] by blast

lemma taufree_coupledsim_weak_bisim:
  assumes
    "\<And> p1 a p2 . (p1 \<longmapsto> a p2 \<Longrightarrow> \<not> tau a)"
    "coupled_simulation R"
  shows "weak_bisimulation R"
  using assms taufree_contrasim_implies_weak_bisim coupledsim_implies_contrasim[OF assms(2)] by blast

lemma coupledsim_stable_state_symm:
  assumes
    "coupled_simulation R"
    "R p q"
    "stable_state q"
  shows
    "R q p"
  using assms steps_left unfolding coupled_simulation_def by metis

text\<open>In finite systems, coupling is guaranteed to happen through tau-maximal states.\<close>
lemma coupledsim_max_coupled:
  assumes 
    "p \<sqsubseteq>cs q"
    "\<And> r1 r2 . r1 \<longmapsto>* tau r2 \<and> r2 \<longmapsto>* tau r1 \<Longrightarrow> r1 = r2" --"contracted tau cycles"
    "\<And> r. finite {r'. r \<longmapsto>* tau r'}"
  shows
    "\<exists> q' . q \<longmapsto>* tau q' \<and> q' \<sqsubseteq>cs p \<and> tau_max q'"
proof -
  obtain q1 where q1_spec: "q \<longmapsto>* tau q1" "q1 \<sqsubseteq>cs p" 
    using assms(1) contrasim_implies_coupling coupledsim_implies_contrasim by fastforce
  then obtain q' where "q1 \<longmapsto>* tau q'" "(\<forall>q''. q' \<longmapsto>* tau q'' \<longrightarrow> q' = q'')"
    using tau_max_deadlock assms(2,3) by blast
  then moreover have "q' \<sqsubseteq>cs p" "q \<longmapsto>* tau q'"
    using q1_spec coupledsim_trans coupledsim_step steps_concat[of q1 tau q' q]
    by blast+
  ultimately show ?thesis by blast
qed

text\<open>In the greatest coupled simulation, \<open>\<tau>\<close>-challenges can be answered by stuttering.\<close>
lemma coupledsim_tau_challenge_trivial:
  assumes 
    "p \<sqsubseteq>cs q"
    "p \<longmapsto>* tau p'"
  shows
    "p' \<sqsubseteq>cs q"
  using assms coupledsim_trans coupledsim_step by blast

text\<open>In the greatest coupled simulation, \<open>a\<close>-challenges can be answered by a weak move without
  trailing \<open>\<tau>\<close>-steps.\<close>
lemma coupledsim_step_challenge_short_answer:
  assumes 
    "p \<sqsubseteq>cs q"
    "p \<longmapsto>a p'"
    "\<not> tau a"
  shows
    "\<exists> q' q1. p' \<sqsubseteq>cs q' \<and> q \<longmapsto>* tau q1 \<and> q1 \<longmapsto> a q'"
proof -
  obtain q' q1 q2 where "p' \<sqsubseteq>cs q2" "q \<longmapsto>* tau q1" "q1 \<longmapsto> a q'" "q' \<longmapsto>* tau q2"
    using assms coupled_simulation_implies_weak_simulation weak_sim_ruleformat(1) by blast
  then moreover have "p' \<sqsubseteq>cs  q'" using coupledsim_trans coupledsim_step by blast
  ultimately show ?thesis by blast
qed

text\<open>If two states share the same outgoing edges with except for one \<open>\<tau>\<close>-loop, then they cannot
  be distinguished by coupled similarity.\<close>
lemma coupledsim_tau_loop_ignorance:
  assumes
    "\<And> a p'. p \<longmapsto> a p' \<or> p' = pp \<and> a = \<tau> \<longleftrightarrow> pp \<longmapsto> a p'"
  shows
    "pp \<equiv>cs p"
proof -
  define R where "R \<equiv> \<lambda> p1 q1. p1 = q1 \<or> p1 = pp \<and> q1 = p \<or> p1 = p \<and> q1 = pp"
  have "coupled_simulation R"
    unfolding coupled_simulation_def R_def
  proof (safe)
    fix pa q p' a
    assume
      "q \<longmapsto>a  p'"
    thus "\<exists>q'. (p' = q' \<or> p' = pp \<and> q' = p \<or> p' = p \<and> q' = pp) \<and> q \<longmapsto>^ a  q'"
      using assms step_weak_step_tau by auto
  next
    fix pa q
    show "\<exists>q'. q \<longmapsto>* tau  q' \<and> (q' = q \<or> q' = pp \<and> q = p \<or> q' = p \<and> q = pp)"
      using steps.refl by blast
  next
    fix pa q p' a
    assume
      "pp \<longmapsto>a  p'"
    thus "\<exists>q'. (p' = q' \<or> p' = pp \<and> q' = p \<or> p' = p \<and> q' = pp) \<and> p \<longmapsto>^ a  q'"
      using assms by (metis lts.steps.simps tau_def)
  next
    fix pa q
    show "\<exists>q'. p \<longmapsto>* tau  q' \<and> (q' = pp \<or> q' = pp \<and> pp = p \<or> q' = p \<and> pp = pp)"
      using steps.refl[of p tau] by blast
  next
    fix pa q p' a
    assume
      "p \<longmapsto>a  p'"
    thus "\<exists>q'. (p' = q' \<or> p' = pp \<and> q' = p \<or> p' = p \<and> q' = pp) \<and> pp \<longmapsto>^ a  q'"
      using assms step_weak_step_tau by fastforce
  next
    fix pa q
    show "\<exists>q'. pp \<longmapsto>* tau  q' \<and> (q' = p \<or> q' = pp \<and> p = p \<or> q' = p \<and> p = pp)"
      using steps.refl[of pp tau] by blast
  qed
  moreover have "R p pp" "R pp p" unfolding R_def by auto
  ultimately show ?thesis by blast
qed

subsection \<open>On the Connection to Stronger Bisimulations\<close>

lemma coupledsim_eq_reducible_1:
  assumes
    contracted_cycles: "\<And> r1 r2 . r1 \<longmapsto>* tau r2 \<and> r2 \<longmapsto>* tau r1 \<Longrightarrow> r1 = r2" and
    finite_taus: "\<And> r. finite {r'. r \<longmapsto>* tau r'}" and
    one_step_taus: "\<And> r a r'. r \<longmapsto>* tau r' \<Longrightarrow> \<exists>r''. tau_max r'' \<and> r \<longmapsto>\<tau> r'' \<and> r' \<sqsubseteq>cs r''"
      --"this is some kind of cheat :/" and
    sim_vis_p:
      "\<And> p' a. \<not>tau a \<Longrightarrow> p \<longmapsto>^ a p' \<Longrightarrow> \<exists> p'' q'. q \<longmapsto>^ a q' \<and> p' \<sqsubseteq>cs q'" and
    sim_tau_max_p:
      "\<And> p'. tau_max p' \<Longrightarrow> p \<longmapsto>* tau p' \<Longrightarrow> \<exists> q'. tau_max q' \<and> q \<longmapsto>* tau q' \<and> p' \<equiv>cs q'"
  shows
    "p \<sqsubseteq>cs q"
proof-
  have
    "((\<forall>a p'. p \<longmapsto>a  p' \<longrightarrow> (\<exists>q'. q \<longmapsto>^ a  q' \<and> p' \<sqsubseteq>cs q')) \<and>
    (\<exists>q'. q \<longmapsto>* tau  q' \<and> q' \<sqsubseteq>cs p))"
  proof safe
    fix a p'
    assume
      step: "p \<longmapsto>a  p'"
    thus "\<exists>q'. q \<longmapsto>^ a  q' \<and> p' \<sqsubseteq>cs  q'"
    proof (cases "tau a")
      case True
      then obtain p'' where p''_spec: "p \<longmapsto>\<tau> p''" "tau_max p''" "p' \<sqsubseteq>cs p''"
        using one_step_taus step tau_def steps_one_step[of p \<tau> p']
        by (metis (no_types, lifting))
      then obtain q' where q'_spec: "q \<longmapsto>* tau q'" "p'' \<equiv>cs q'"
        using sim_tau_max_p steps_one_step[OF step, of tau, OF `tau a`]
          steps_one_step[of p \<tau> p''] tau_def
        by metis
      then show ?thesis using `tau a` p''_spec(3) using coupledsim_trans by blast
    next
      case False
      then show ?thesis using sim_vis_p step_weak_step_tau[OF step] by blast
    qed
  next
    obtain p_max where "p \<longmapsto>* tau p_max" "tau_max p_max"
      using tau_max_deadlock contracted_cycles finite_taus by blast
    then obtain q_max where "q \<longmapsto>* tau  q_max" "q_max \<sqsubseteq>cs p_max"
      using sim_tau_max_p[of p_max] by force
    moreover have "p_max \<sqsubseteq>cs  p" using `p \<longmapsto>* tau p_max` coupledsim_step by blast
    ultimately show "\<exists>q'. q \<longmapsto>* tau  q' \<and> q' \<sqsubseteq>cs  p"
      using coupledsim_trans by blast
  qed
  thus " p \<sqsubseteq>cs q" using coupledsim_unfold[symmetric] by auto
qed

text\<open>This lemma yields a neat argument why one can use a sigref algorithm to pre-select the
  tuples which come into question for further checking of coupled simulation by contraposition.\<close>
lemma coupledsim_eventual_symmetry:
  assumes
    contracted_cycles: "\<And> r1 r2 . r1 \<longmapsto>* tau r2 \<and> r2 \<longmapsto>* tau r1 \<Longrightarrow> r1 = r2" and
    finite_taus: "\<And> r. finite {r'. r \<longmapsto>* tau r'}" and
    cbisim: "p \<sqsubseteq>cs q" and
    step: "p \<longmapsto>^ a p'" and
    tau_max_p': "tau_max p'"
  shows
    "\<exists> q'. tau_max q' \<and> q \<longmapsto>^ a q' \<and> p' \<equiv>cs q'"
proof-
  obtain q' where q'_spec: "q \<longmapsto>^a q'" "p' \<sqsubseteq>cs q'"
    using cbisim step unfolding coupled_simulation_weak_premise by blast
  then obtain q'' where q''_spec: "q' \<longmapsto>* tau q''" "q'' \<sqsubseteq>cs p'"
    using cbisim unfolding coupled_simulation_weak_simulation by blast
  then obtain q_max where q_max_spec: "q'' \<longmapsto>* tau q_max" "tau_max q_max" 
    using tau_max_deadlock contracted_cycles finite_taus by force
  hence "q_max \<sqsubseteq>cs p'" using q''_spec coupledsim_tau_challenge_trivial by blast
  hence "q_max \<equiv>cs p'" using tau_max_p' coupledsim_tau_max_eq by blast
  moreover have "q \<longmapsto>^ a q_max" using q_max_spec q'_spec q''_spec steps_concat by blast
  ultimately show ?thesis using q_max_spec(2) by blast
qed

lemma coupledsim_eq_reducible_2:
  assumes
    cs: "p \<sqsubseteq>cs q" and
    contracted_cycles: "\<And> r1 r2 . r1 \<longmapsto>* tau r2 \<and> r2 \<longmapsto>* tau r1 \<Longrightarrow> r1 = r2" and
    finite_taus: "\<And> r. finite {r'. r \<longmapsto>* tau r'}"
  shows
    sim_vis_p:
      "\<And> p' a. \<not>tau a \<Longrightarrow> p \<longmapsto>^ a p' \<Longrightarrow> \<exists> q'. q \<longmapsto>^ a q' \<and> p' \<sqsubseteq>cs q'" and
    sim_tau_max_p:
      "\<And> p'. tau_max p' \<Longrightarrow> p \<longmapsto>* tau p' \<Longrightarrow> \<exists> q'. tau_max q' \<and> q \<longmapsto>* tau q' \<and> p' \<equiv>cs q'"
proof-
  fix p' a
  assume
    "\<not> tau a"
    "p \<longmapsto>^ a  p'"
  thus "\<exists>q'. q \<longmapsto>^ a  q' \<and> p' \<sqsubseteq>cs  q'"
    using cs unfolding coupled_simulation_weak_premise by blast
next
  fix p'
  assume step:
    "p \<longmapsto>* tau p'"
    "tau_max p'"
  hence "p \<longmapsto>^ \<tau>  p'"  by auto
  hence "\<exists> q'. tau_max q' \<and> q \<longmapsto>^ \<tau> q' \<and> p' \<equiv>cs q'"
    using coupledsim_eventual_symmetry[OF _ finite_taus, of p q \<tau> p']
      contracted_cycles cs step(2) by blast
  thus "\<exists> q'. tau_max q' \<and> q \<longmapsto>* tau q' \<and> p' \<equiv>cs q'"
    by auto
qed

lemma coupledsim_eventuality_2:
  assumes
    contracted_cycles: "\<And> r1 r2 . r1 \<longmapsto>* tau r2 \<and> r2 \<longmapsto>* tau r1 \<Longrightarrow> r1 = r2" and
    finite_taus: "\<And> r. finite {r'. r \<longmapsto>* tau r'}" and
    cbisim: "p \<equiv>cs q" and
    step: "p \<longmapsto>^ a p'"
  shows
    "\<exists> p'' q'. tau_max p'' \<and> tau_max q' \<and> p \<longmapsto>^ a p'' \<and> q \<longmapsto>^ a q' \<and> p'' \<equiv>cs q'"
proof-
  obtain q' where q'_spec: "q \<longmapsto>^ a q'"
    using cbisim step unfolding coupled_simulation_weak_premise by blast
  then obtain q_max where q_max_spec: "q' \<longmapsto>* tau q_max" "tau_max q_max"
    using tau_max_deadlock contracted_cycles finite_taus by force
  hence "q \<longmapsto>^ a q_max" using q'_spec steps_concat by blast
  then obtain p'' where p''_spec: "p \<longmapsto>^ a p''" "q_max \<sqsubseteq>cs p''"
    using cbisim unfolding coupled_simulation_weak_premise by blast
  then obtain p''' where p'''_spec: "p'' \<longmapsto>* tau p'''" "p''' \<sqsubseteq>cs q_max"
    using cbisim unfolding coupled_simulation_weak_simulation  by blast
  then obtain p_max where p_max_spec: "p''' \<longmapsto>* tau p_max" "tau_max p_max"
    using tau_max_deadlock contracted_cycles finite_taus by force
  hence "p_max \<sqsubseteq>cs p'''" using coupledsim_step by blast
  hence "p_max \<sqsubseteq>cs q_max" using p'''_spec coupledsim_trans by blast
  hence "q_max \<equiv>cs p_max" using coupledsim_tau_max_eq q_max_spec by blast
  moreover have  "p \<longmapsto>^ a p_max"
    using  p''_spec(1) steps_concat[OF p_max_spec(1) p'''_spec(1)] steps_concat by blast
  ultimately show ?thesis using p_max_spec(2) q_max_spec(2) `q \<longmapsto>^ a q_max` by blast
qed

subsection \<open>Relation to S-Coupled Simulation\<close>

--"from sangiorgi2012, p.~226"
lemma divergence_free_coupledsims_coincidence_1:
  defines 
    "R1 \<equiv> (\<lambda> p q . p \<sqsubseteq>cs q \<and> (stable_state p \<longrightarrow> stable_state q))" and
    "R2 \<equiv> (\<lambda> p q . q \<sqsubseteq>cs p \<and> (stable_state q \<longrightarrow> stable_state p))"
  assumes
    non_divergent_system: "\<And> p . \<not> divergent_state p"
  shows
    "s_coupled_simulation_sangiorgi12 R1 R2"
  unfolding s_coupled_simulation_sangiorgi12_def
proof safe
  show "weak_simulation R1" unfolding weak_simulation_def
  proof safe
    fix p q p' a
    assume sub_assms:
      "R1 p q"
      "p \<longmapsto>a  p'"
    then obtain q' where q'_def: "q \<longmapsto>^ a q'" "p' \<sqsubseteq>cs q'"
      using coupled_sim_by_is_coupled_sim unfolding R1_def coupled_simulation_def by blast
    show "\<exists>q'. R1 p' q' \<and> q \<longmapsto>^ a  q'"
    proof (cases "stable_state p'")
      case True
      obtain  q'' where q''_def: "q' \<longmapsto>* tau q''" "q'' \<sqsubseteq>cs  p'"
        using coupled_sim_by_is_coupled_sim q'_def(2)
        unfolding coupled_simulation_weak_simulation by blast
      then obtain q''' where q'''_def: "q'' \<longmapsto>* tau q'''" "stable_state q'''"
        using non_divergence_implies_eventual_stability non_divergent_system by blast
      hence "q''' \<sqsubseteq>cs p'" using coupledsim_step_gla17 coupledsim_trans[OF _ q''_def(2)] by blast
      hence "p' \<sqsubseteq>cs q'''"
        using `stable_state p'` coupled_sim_by_is_coupled_sim coupledsim_stable_state_symm by blast
      moreover have "q \<longmapsto>^ a q'''" using q'_def(1) q''_def(1) q'''_def(1) steps_concat by blast
      ultimately show ?thesis using q'''_def(2) unfolding R1_def by blast
    next
      case False
      then show ?thesis using q'_def unfolding R1_def by blast
    qed
  qed
  --"analogous to previous case"
  then show "weak_simulation (\<lambda>p q. R2 q p)" unfolding R1_def R2_def .
next
  fix p q
  assume
    "R1 p q"
    "stable_state p"
  thus "R2 p q"
    unfolding R1_def R2_def 
    using coupled_sim_by_is_coupled_sim coupledsim_stable_state_symm by blast
next --"analogous"
  fix p q
  assume
    "R2 p q"
    "stable_state q"
  thus "R1 p q"
    unfolding R1_def R2_def 
    using coupled_sim_by_is_coupled_sim coupledsim_stable_state_symm by blast
qed

--"from sangiorgi2012, p.~227"
lemma divergence_free_coupledsims_coincidence_2:
  defines 
    "R \<equiv> (\<lambda> p q . p \<sqsubseteq>scs q \<or> (\<exists> q' . q \<longmapsto>* tau q' \<and> p \<equiv>scs q'))"
  assumes
    non_divergent_system: "\<And> p . \<not> divergent_state p"
  shows
    "coupled_simulation R"
  unfolding coupled_simulation_weak_simulation
proof safe
  show "weak_simulation R" 
    unfolding weak_simulation_def
  proof safe
    fix p q p' a
    assume sub_assms:
      "R p q"
      "p \<longmapsto>a  p'"
    thus "\<exists>q'. R p' q' \<and> q \<longmapsto>^ a  q'"
      unfolding R_def
    proof (cases "p \<sqsubseteq>scs q")
      case True
      then obtain q' where "p' \<sqsubseteq>scs  q'" "q \<longmapsto>^ a  q'"
        using s_coupled_simulation_sangiorgi12_def sub_assms(2) weak_sim_ruleformat by metis
      thus "\<exists>q'. (p' \<sqsubseteq>scs  q' \<or> (\<exists>q'a. q' \<longmapsto>* tau  q'a \<and> p' \<equiv>scs  q'a)) \<and> q \<longmapsto>^ a  q'" by blast
    next
      case False
      then obtain q' where "q \<longmapsto>* tau  q'" "p \<equiv>scs  q'" using sub_assms(1) unfolding R_def by blast
      then obtain q'' where "q' \<longmapsto>^ a  q''" "p' \<sqsubseteq>scs  q''" 
        using s_coupled_simulation_sangiorgi12_def sub_assms(2) weak_sim_ruleformat by metis
      hence "p' \<sqsubseteq>scs  q'' \<and> q \<longmapsto>^ a  q''" using steps_concat `q \<longmapsto>* tau  q'` by blast
      thus "\<exists>q'. (p' \<sqsubseteq>scs  q' \<or> (\<exists>q'a. q' \<longmapsto>* tau  q'a \<and> p' \<equiv>scs  q'a)) \<and> q \<longmapsto>^ a  q'" by blast
    qed
  qed
next
  fix p q
  assume
    "R p q"
  thus "\<exists>q'. q \<longmapsto>* tau  q' \<and> R q' p" unfolding R_def
  proof safe
    fix R1 R2
    assume sub_assms:
      "s_coupled_simulation_sangiorgi12 R1 R2"
      "R1 p q"
    thus "\<exists>q'. q \<longmapsto>* tau  q' \<and> (q' \<sqsubseteq>scs  p \<or> (\<exists>q'a. p \<longmapsto>* tau  q'a \<and> q' \<equiv>scs  q'a))"
    proof -
      --"dropped a superfluous case distinction from @cite{sangiorgi2012}"
      obtain p' where "stable_state p'" "p \<longmapsto>* tau p'"
        using non_divergent_system non_divergence_implies_eventual_stability by blast
      hence "p \<longmapsto>^ \<tau>  p'" using tau_tau by blast
      then obtain q' where "q \<longmapsto>* tau q'" "p' \<sqsubseteq>scs q'"
        using s_coupled_simulation_sangiorgi12_def weak_sim_weak_premise sub_assms tau_tau
        by metis
      moreover hence "p' \<equiv>scs q'" using `stable_state p'` s_coupledsim_stable_eq by blast
      ultimately show ?thesis using `p \<longmapsto>* tau p'` s_coupledsim_symm by blast
    qed
  qed (metis s_coupledsim_symm)
qed

text {*
  as far as I can see, one has to use rooted coupled similarity---and not just coupled similarity---
  for this proof to go through (stability\_eq). or do I miss something?
*}
theorem divergence_free_coupledsims_coincidence:
  assumes
    non_divergent_system: "\<And> p . \<not> divergent_state p" and
    stability_eq: "stable_state p \<longleftrightarrow> stable_state q"
  shows
    "(p \<equiv>cs q) = (p \<equiv>scs q)"
proof rule
  assume "p \<equiv>cs q"
  hence "p \<sqsubseteq>cs q" "q \<sqsubseteq>cs p" by auto
  thus "p \<equiv>scs q"
    using stability_eq divergence_free_coupledsims_coincidence_1[OF non_divergent_system] by blast
next
  assume "p \<equiv>scs q"
  thus "p \<equiv>cs q"
    using stability_eq divergence_free_coupledsims_coincidence_2[OF non_divergent_system]
      s_coupledsim_eq_parts by blast
qed

subsection \<open>Relation to Sangiorgi's Coupled Simulation\<close>

lemma coupledsim_gla17_resembles_sangiorgi12:
  shows
    "coupled_simulation R1 =
    coupled_simulation_sangiorgi12 R1 (\<lambda> p q . R1 q p)"
  unfolding coupled_simulation_weak_simulation coupled_simulation_sangiorgi12_def by blast

lemma coupledsim_sangiorgi12_impl_gla17:
  assumes
    "coupled_simulation_sangiorgi12 R1 R2"
  shows
    "coupled_simulation (\<lambda> p q. R1 p q \<or> R2 q p)"
  unfolding coupled_simulation_weak_simulation
proof safe
  have "weak_simulation R1" "weak_simulation (\<lambda>p q. R2 q p)"
    using assms unfolding coupled_simulation_sangiorgi12_def by auto
  thus "weak_simulation (\<lambda>p q. R1 p q \<or> R2 q p)"
    using weak_sim_union_cl by blast
next
  fix p q
  assume  
    "R1 p q"
  hence "\<exists>q'. q \<longmapsto>* tau  q' \<and> R2 p q'"
    using assms unfolding coupled_simulation_sangiorgi12_def by auto
  thus "\<exists>q'. q \<longmapsto>* tau  q' \<and> (R1 q' p \<or> R2 p q')" by blast
next
  fix p q
  assume
    "R2 q p"
  hence "\<exists>q'. q \<longmapsto>* tau  q' \<and> R1 q' p"
    using assms unfolding coupled_simulation_sangiorgi12_def by auto
  thus "\<exists>q'. q \<longmapsto>* tau  q' \<and> (R1 q' p \<or> R2 p q')" by blast
qed

subsection \<open>Relation to Peters's Coupled Simulation\<close>

thm coupled_simulation_sangiorgi12_def
  
definition coupled_simulation_gp15 ::
  "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
where
  "coupled_simulation_gp15 R \<equiv> \<forall> p q p'. R p q \<and> (p \<longmapsto>* (\<lambda>a. True) p') \<longrightarrow>
    (\<exists> q'. (q \<longmapsto>* (\<lambda>a. True) q') \<and> R p' q') \<and>
    (\<exists> q'. (q \<longmapsto>* (\<lambda>a. True) q') \<and> R q' p')"

--"A little strange fact about gp15's CS."
lemma coupled_simulation_gp15_no_weak_bisim:
  assumes
    "(x::'s) \<noteq> y"
    "trans = (\<lambda> p a p'. False)"
  shows
    "\<not>coupled_simulation_gp15 (\<lambda>p q. p = x \<and> q = y)"
    "weak_bisimulation (\<lambda>p q. p = x \<and> q = y)"
using assms steps.refl unfolding weak_bisimulation_def coupled_simulation_gp15_def by auto

lemma weak_bisim_implies_coupled_sim_gp15:
  assumes
    wbisim: "weak_bisimulation R" and 
    symmetry: "\<And> p q . R p q \<Longrightarrow> R q p"
  shows "coupled_simulation_gp15 R"
unfolding coupled_simulation_gp15_def proof safe
  fix p q p'
  assume Rpq: "R p q" "p \<longmapsto>* (\<lambda>a. True)  p'"
  have always_tau: "\<And>a. tau a \<Longrightarrow> (\<lambda>a. True) a " by simp
  hence "\<exists>q'. q \<longmapsto>* (\<lambda>a. True)  q' \<and> R p' q'"
    using steps_retain_weak_bisim[OF wbisim Rpq] by auto
  moreover hence "\<exists>q'. q \<longmapsto>* (\<lambda>a. True)  q' \<and> R q' p'"
    using symmetry by auto
  ultimately show
    "(\<exists>q'. q \<longmapsto>* (\<lambda>a. True)  q' \<and> R p' q')"
    "(\<exists>q'. q \<longmapsto>* (\<lambda>a. True)  q' \<and> R q' p')" .
qed

lemma coupledsim_gla17_implies_gp15:
  assumes
    "coupled_simulation R"
  shows 
    "coupled_simulation_gp15 R"
  unfolding coupled_simulation_gp15_def
proof safe
  fix p q p'
  assume challenge:
    "R p q"
    "p \<longmapsto>*(\<lambda>a. True)p'"
  have tau_true: "\<And>a. tau a \<Longrightarrow> (\<lambda>a. True) a " by simp
  thus "\<exists>q'. q \<longmapsto>* (\<lambda>a. True)  q' \<and> R p' q'"
    using steps_retain_weak_sim assms challenge
    unfolding coupled_simulation_weak_simulation by meson
  then obtain q' where q'_def: "q \<longmapsto>* (\<lambda>a. True)  q'" "R p' q'" by blast
  then obtain q'' where "q' \<longmapsto>* tau  q''" "R q'' p'"
    using assms unfolding coupled_simulation_weak_simulation by blast
  moreover hence "q \<longmapsto>* (\<lambda>a. True)  q''"
    using q'_def(1) steps_concat steps_spec tau_true by meson
  ultimately show "\<exists>q'. q \<longmapsto>* (\<lambda>a. True)  q' \<and> R q' p'" by blast
qed

lemma coupledsim_gp15_implies_gla17_on_tau_systems:
  assumes
    "coupled_simulation_gp15 R"
    "\<And> a . tau a"
  shows 
    "coupled_simulation R"
  unfolding coupled_simulation_def
proof safe
  fix p q p' a
  assume challenge:
    "R p q"
    "p \<longmapsto>a  p'"
  hence "p \<longmapsto>* (\<lambda>a. True)  p'" using steps_one_step by metis
  then obtain q' where "q \<longmapsto>* (\<lambda>a. True)  q'" "R p' q'"
    using challenge(1) assms(1) unfolding coupled_simulation_gp15_def by blast
  hence "q \<longmapsto>^ a  q'" using assms(2) steps_concat steps_spec by meson
  thus "\<exists>q'. R p' q' \<and> q \<longmapsto>^ a  q'" using `R p' q'` by blast
next
  fix p q
  assume
    "R p q"
  moreover have "p \<longmapsto>* (\<lambda>a. True) p" using steps.refl by blast
  ultimately have "\<exists>q'. q \<longmapsto>* (\<lambda>a. True)  q' \<and> R q' p"
    using assms(1) unfolding coupled_simulation_gp15_def by blast
  thus "\<exists>q'. q \<longmapsto>* tau  q' \<and> R q' p" using assms(2) steps_spec by blast
qed

subsection \<open>Relation to Bell's Eventual Simulation\<close>

lemma coupled_simulation_implies_eventual_sim:
  assumes "coupled_simulation R"
  shows "eventual_sim R" 
  unfolding eventual_sim_def
proof (clarify)
  fix p q p' a
  assume challenge: "R p q" "tau a \<longrightarrow> p \<longmapsto>* tau  p'" "\<not> tau a \<longrightarrow> p \<longmapsto>~ a  p'"
  then show "\<exists>p'' q''. p' \<longmapsto>* tau  p'' \<and> q \<longmapsto>^ a  q'' \<and> R p'' q''"
  proof (cases "tau a", auto)
    assume "tau a" "p \<longmapsto>* tau  p'"
    then obtain q' where q'_def: "q \<longmapsto>* tau  q' \<and> R p' q'"
      using silent_steps_retain_coupled_simulation[OF assms challenge(1), of tau p'] by blast
    thus "\<exists>p''. p' \<longmapsto>* tau  p'' \<and> (\<exists>q''. q \<longmapsto>* tau  q'' \<and> R p'' q'')"
      using steps.refl[of p' tau] by blast
  next
    fix pq1 pq2
    assume
       notau: "\<not> tau a" and
       simstep:
        "p \<longmapsto>* tau  pq1"
        "pq1 \<longmapsto>a  pq2"
        "pq2 \<longmapsto>* tau  p'"
    then obtain q' where q'_def: "q \<longmapsto>* tau q'" "R pq1 q'"
      using silent_steps_retain_coupled_simulation[OF assms challenge(1) simstep(1)] by blast
    obtain q'' where q''_def: "q' \<longmapsto>~ a q''" "R pq2 q''"
      using assms q'_def(2) simstep(2) notau unfolding coupled_simulation_def by blast
    obtain q''' where q'''_def: "q'' \<longmapsto>* tau  q'''" "R p' q'''"
      using silent_steps_retain_coupled_simulation[OF assms q''_def(2) simstep(3)] by blast
    show "\<exists>p''. p' \<longmapsto>* tau  p'' \<and> 
      (\<exists>q''. (\<exists>pq1. q \<longmapsto>* tau  pq1 \<and> (\<exists>pq2. pq1 \<longmapsto>a  pq2 \<and> pq2 \<longmapsto>* tau  q'')) \<and> R p'' q'')" 
      using steps.refl[of p' tau] q'''_def(1,2) q'_def(1) q''_def(1) steps_concat by blast
  qed
qed
  
lemma mutual_coupled_simulation_implies_mutual_eventual_sim:
  assumes
    "coupled_simulation R1"
    "coupled_simulation R2"
    "R1 p q"
    "R2 q p"
  shows 
    "eventual_sim R1"
    "eventual_sim R2"
    "R1 p q"
    "R2 q p"
  using assms coupled_simulation_implies_eventual_sim
  unfolding eventual_bisim_def by auto
  
lemma mutual_coupled_simulation_implies_eventual_bisim:
  assumes
    "coupled_simulation R"
    "coupled_simulation (\<lambda> p q. R q p)"
  shows "eventual_bisim R" 
  using assms coupled_simulation_implies_eventual_sim
  unfolding eventual_bisim_def by simp    

end -- "context @{locale lts_tau}"

subsection \<open>Example Locale more s-coupled than coupled sim.\<close>
  
text \<open>The following example shows that a system might be related by s-coupled-simulation without
  being connected by coupled-simulation.\<close>
  
datatype ex_state = a0 | a1 | a2 | a3 | b0 | b1 | b2 
  
locale ex_lts = lts_tau trans \<tau>
  for trans :: "ex_state \<Rightarrow> nat \<Rightarrow> ex_state \<Rightarrow> bool" and \<tau> +
  assumes
    sys:
  "trans = (\<lambda> p act q .
     1 = act \<and> (p = a0 \<and> q = a1 
              \<or> p = a0 \<and> q = a2 
              \<or> p = a2 \<and> q = a3 
              \<or> p = b0 \<and> q = b1 
              \<or> p = b1 \<and> q = b2) \<or>
     0 = act \<and> (p = a1 \<and> q = a1))"
   "\<tau> = 0"
begin 
  
lemma no_root_coupled_sim:
  fixes R1 R2
  assumes
    coupled:
      "coupled_simulation_sangiorgi12 R1 R2" and
    root:
      "R1 a0 b0" "R2 a0 b0"
  shows
    False
proof -
  have
    R1sim: 
      "weak_simulation R1" and
    R1coupling:
      "\<forall>p q. R1 p q \<longrightarrow> (\<exists>q'. q \<longmapsto>* tau  q' \<and> R2 p q')" and
    R2sim: 
      "weak_simulation (\<lambda>p q. R2 q p)"
    using coupled unfolding coupled_simulation_sangiorgi12_def by auto
  hence R1sim_rf:
      "\<And> p q. R1 p q \<Longrightarrow> (\<forall>p' a. p \<longmapsto>a  p' \<longrightarrow> (\<exists>q'. R1 p' q' \<and> (\<not> tau a \<longrightarrow> q \<longmapsto>~ a  q') \<and> (tau a \<longrightarrow> q \<longmapsto>* tau  q')))"
    unfolding weak_simulation_def by blast
  have "a0 \<longmapsto> 1 a1" using sys by auto
  hence "\<exists>q'. R1 a1 q' \<and> b0 \<longmapsto>~ 1 q'"
    using R1sim_rf[OF root(1), rule_format, of 1 a1] tau_def by (auto simp add: sys)
  then obtain q' where q': "R1 a1 q'" "b0 \<longmapsto>~ 1 q'" by blast
  have b0_quasi_stable: "\<forall> q' . b0 \<longmapsto>*tau q' \<longrightarrow> b0 = q'"
    using steps_no_step[of b0 tau] tau_def by (auto simp add: sys)
  have b0_only_b1: "\<forall> q' . b0 \<longmapsto>1 q' \<longrightarrow> q' = b1" by (auto simp add: sys)
  have b1_quasi_stable: "\<forall> q' . b1 \<longmapsto>*tau q' \<longrightarrow> b1 = q'"
    using steps_no_step[of b1 tau] tau_def by (auto simp add: sys)
  have "\<forall> q' . b0 \<longmapsto>~1 q' \<longrightarrow> q' = b1" using b0_quasi_stable b0_only_b1 b1_quasi_stable by auto
  hence "q' = b1" using q'(2) by blast
  hence "R1 a1 b1" using q'(1) by simp
  hence "R2 a1 b1"
    using b1_quasi_stable R1coupling by auto
  have b1_b2: "b1 \<longmapsto>1 b2"
    by (auto simp add: sys)
  hence a1_sim: "\<exists> q' . R2 q' b2 \<and> a1 \<longmapsto>~ 1  q'"
     using `R2 a1 b1` R2sim b1_b2 unfolding weak_simulation_def tau_def by (auto simp add: sys)
  have a1_quasi_stable: "\<forall> q' . a1 \<longmapsto>*tau q' \<longrightarrow> a1 = q'"
    using steps_loop[of a1] by (auto simp add: sys)
  hence a1_stuck: "\<forall> q' . \<not> a1 \<longmapsto>~1 q'"
    by (auto simp add: sys)
  show ?thesis using a1_sim  a1_stuck by blast
qed

lemma root_s_coupled_sim:
  defines
    "R1 \<equiv> \<lambda> a b .
      a = a0 \<and> b = b0 \<or>
      a = a1 \<and> b = b1 \<or>
      a = a2 \<and> b = b1 \<or>
      a = a3 \<and> b = b2"
  and
    "R2 \<equiv> \<lambda> a b .
      a = a0 \<and> b = b0 \<or>
      a = a2 \<and> b = b1 \<or>
      a = a3 \<and> b = b2"
  shows
    coupled:
      "s_coupled_simulation_sangiorgi12 R1 R2"
  unfolding s_coupled_simulation_sangiorgi12_def
proof safe
  show "weak_simulation R1"
    unfolding weak_simulation_def proof (clarify)
    fix p q p' a
    show "R1 p q \<Longrightarrow> p \<longmapsto>a  p' \<Longrightarrow> \<exists>q'. R1 p' q' \<and> (q \<longmapsto>^ a  q')" 
      using step_tau_refl unfolding sys assms tau_def using sys(2) tau_def by (cases p, auto)
  qed
next
  show "weak_simulation (\<lambda>p q. R2 q p)"
    unfolding weak_simulation_def proof (clarify)
    fix p q p' a
    show "R2 q p \<Longrightarrow> p \<longmapsto>a  p' \<Longrightarrow> \<exists>q'. R2 q' p' \<and> (q \<longmapsto>^ a  q')" 
      using steps.refl[of _ tau] tau_def unfolding assms sys using sys(2) tau_def by (cases p, auto)
  qed
next 
  fix p q
  assume "R1 p q" "stable_state p"
  thus "R2 p q" unfolding assms sys using sys(2) tau_def by auto
next
  fix p q
  assume "R2 p q" "stable_state q"
  thus "R1 p q" unfolding assms sys using tau_def by auto
qed

end --"@{locale ex_lts} // example lts"
  
end