section \<open>Relations for Notions of Equivalence in Weak Setting\<close>

theory Weak_Relations
imports
  Weak_Transition_Systems
  Strong_Relations
begin

context lts_tau
begin

subsection \<open>Weak Simulation\<close>
  
definition weak_simulation :: 
  "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
where
  "weak_simulation R \<equiv> \<forall> p q. R p q \<longrightarrow> 
    (\<forall> p' a. p \<longmapsto> a p' \<longrightarrow> (\<exists> q'. R p' q'
      \<and> (q \<longmapsto>^ a q')))"

text {*
  for some reason I don't understand, Isabelle won't finish the proofs
  needed for the introduction of the following coinductive predicate if
  it unfolds the abbreviation of @{text "\<longmapsto>^"}.
*}
definition weak_step_tau2 :: "'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool"
    ("_ \<longmapsto>^^ _  _" [70, 70, 70] 80)
where [simp]:
  "(p \<longmapsto>^^ a q) \<equiv> p \<longmapsto>^ a q"

coinductive greatest_weak_simulation :: 
  "'s \<Rightarrow> 's \<Rightarrow> bool"
where
  "(\<forall> p' a. p \<longmapsto> a p' \<longrightarrow> (\<exists> q'. greatest_weak_simulation p' q' \<and> (q \<longmapsto>^^ a q')))
  \<Longrightarrow> greatest_weak_simulation p q"
  
lemma weak_sim_ruleformat:
assumes "weak_simulation R"
  and "R p q"
shows
  "p \<longmapsto> a p' \<Longrightarrow> \<not>tau a \<Longrightarrow> (\<exists> q'. R p' q' \<and> (q \<longmapsto>~ a q'))"
  "p \<longmapsto> a p' \<Longrightarrow>  tau a \<Longrightarrow> (\<exists> q'. R p' q' \<and> (q \<longmapsto>* tau q'))"
  using assms unfolding weak_simulation_def by (blast+)

abbreviation weakly_simulated_by :: "'s \<Rightarrow> 's \<Rightarrow> bool" ("_ \<sqsubseteq>ws  _" [60, 60] 65)
  where "weakly_simulated_by p q \<equiv> \<exists> R . weak_simulation R \<and> R p q"

lemma weaksim_greatest:
  shows "weak_simulation (\<lambda> p q . p \<sqsubseteq>ws q)"
  unfolding weak_simulation_def
  by (metis (no_types, lifting))


lemma gws_is_weak_simulation:
  shows "weak_simulation greatest_weak_simulation"
  unfolding weak_simulation_def
proof safe
  fix p q p' a
  assume ih:
    "greatest_weak_simulation p q"
    "p \<longmapsto>a  p'"
  hence "(\<forall>x xa. p \<longmapsto>x xa \<longrightarrow> (\<exists>q'. q \<longmapsto>^^ x  q' \<and> greatest_weak_simulation xa q')) "
    by (meson greatest_weak_simulation.simps)
  then obtain q' where "q \<longmapsto>^^ a  q' \<and> greatest_weak_simulation p' q'" using ih by blast
  thus "\<exists>q'. greatest_weak_simulation p' q' \<and> q \<longmapsto>^ a  q'"
    unfolding weak_step_tau2_def by blast
qed

lemma weakly_sim_by_implies_gws:
  assumes "p \<sqsubseteq>ws q"
  shows "greatest_weak_simulation p q"
  using assms
proof (coinduct, simp del: weak_step_tau2_def, safe)
  fix x1 x2 R a xa
  assume ih: "weak_simulation R" "R x1 x2" "x1 \<longmapsto>a  xa"
  then obtain q' where"x2 \<longmapsto>^^ a  q'" "R xa q'"
    unfolding weak_simulation_def weak_step_tau2_def by blast
  thus "\<exists>q'. (xa \<sqsubseteq>ws  q' \<or> greatest_weak_simulation xa q') \<and> x2 \<longmapsto>^^ a  q'"
    using ih by blast
qed

lemma gws_eq_weakly_sim_by:
  shows "p \<sqsubseteq>ws q = greatest_weak_simulation p q"
  using weakly_sim_by_implies_gws gws_is_weak_simulation by blast

lemma steps_retain_weak_sim:
assumes 
  "weak_simulation R"
  "R p q"
  "p \<longmapsto>*A  p'"
  "\<And> a . tau a \<Longrightarrow> A a"
shows "\<exists>q'. R p' q' \<and> q \<longmapsto>*A  q'"
  using assms(3,2,4) proof (induct)
  case (refl p' A)
  hence "R p' q  \<and> q \<longmapsto>* A  q" using assms(2) steps.refl by simp
  then show ?case by blast
next
  case (step p A p' a p'')
  then obtain q' where q': "R p' q'" "q \<longmapsto>* A  q'" by blast
  obtain q'' where q'':
    "R p'' q''" "(\<not> tau a \<longrightarrow> q' \<longmapsto>~ a  q'') \<and> (tau a \<longrightarrow> q' \<longmapsto>* tau  q'')"
    using `weak_simulation R` q'(1) step(3) unfolding weak_simulation_def by blast
  have "q' \<longmapsto>* A  q''"
    using q''(2) steps_spec[of q'] step(4) step(6) weak_steps[of q' a q''] by blast
  hence "q \<longmapsto>* A  q''" using steps_concat[OF _ q'(2)] by blast
  thus ?case using q''(1) by blast
qed

lemma weak_sim_weak_premise:
  "weak_simulation R 
  = (\<forall> p q . R p q \<longrightarrow> 
      (\<forall> p' a. p \<longmapsto>^a p' \<longrightarrow> 
        (\<exists> q'. R p' q' \<and> q \<longmapsto>^a q')))"
proof 
  assume weak_prem: "\<forall> p q . R p q \<longrightarrow> (\<forall>p' a. p \<longmapsto>^ a  p' \<longrightarrow> (\<exists>q'. R p' q' \<and> q \<longmapsto>^ a  q'))"
  thus "weak_simulation R"
    unfolding weak_simulation_def using step_weak_step_tau by simp
next
  assume ws: "weak_simulation R"
  show "\<forall>p q. R p q \<longrightarrow> (\<forall>p' a. p \<longmapsto>^ a  p' \<longrightarrow> (\<exists>q'. R p' q' \<and> q \<longmapsto>^ a  q'))"
  proof safe
    fix p q p' a pq1 pq2
    assume case_assms:
      "R p q"
      "p \<longmapsto>* tau  pq1"
      "pq1 \<longmapsto>a  pq2"
      "pq2 \<longmapsto>* tau  p'"
    then obtain q' where q'_def: "q \<longmapsto>* tau  q'" "R pq1 q'"
      using steps_retain_weak_sim[OF ws] by blast
    then moreover obtain q'' where q''_def: "R pq2 q''" "q' \<longmapsto>^ a  q''"
      using ws case_assms(3) unfolding weak_simulation_def by blast
    then moreover obtain q''' where q''_def: "R p' q'''" "q'' \<longmapsto>* tau  q'''"
      using case_assms(4) steps_retain_weak_sim[OF ws] by blast
    ultimately show "\<exists> q'''. R p' q''' \<and> q \<longmapsto>^ a  q'''" using weak_step_extend by blast
  next
    fix p q p' a
    assume
      "R p q"
      "p \<longmapsto>* tau  p'"
      "\<nexists>q'. R p' q' \<and> q \<longmapsto>^ a  q'"
      "tau a"
    thus "False"
      using steps_retain_weak_sim[OF ws] by blast
  next
    --"case identical to first case"
    fix p q p' a pq1 pq2
    assume case_assms:
      "R p q"
      "p \<longmapsto>* tau  pq1"
      "pq1 \<longmapsto>a  pq2"
      "pq2 \<longmapsto>* tau  p'"
    then obtain q' where q'_def: "q \<longmapsto>* tau  q'" "R pq1 q'"
      using steps_retain_weak_sim[OF ws] by blast
    then moreover obtain q'' where q''_def: "R pq2 q''" "q' \<longmapsto>^ a  q''"
      using ws case_assms(3) unfolding weak_simulation_def by blast
    then moreover obtain q''' where q''_def: "R p' q'''" "q'' \<longmapsto>* tau  q'''"
      using case_assms(4) steps_retain_weak_sim[OF ws] by blast
    ultimately show "\<exists> q'''. R p' q''' \<and> q \<longmapsto>^ a  q'''" using weak_step_extend by blast
  qed
qed

lemma weak_sim_enabled_subs:
  assumes
    "p \<sqsubseteq>ws q"
    "weak_enabled p a"
    "\<not> tau a"
  shows "weak_enabled q a"
proof-
  obtain p' where p'_spec: "p \<longmapsto>~ a p'"
    using \<open>weak_enabled p a\<close> weak_enabled_step by blast
  obtain R where "R p q" "weak_simulation R" using assms(1) by blast
  then obtain q' where "q \<longmapsto>^ a q'"
    unfolding weak_sim_weak_premise using weak_step_impl_weak_tau[OF p'_spec] by blast
  thus ?thesis using weak_enabled_step assms(3) by blast
qed

lemma weak_sim_union_cl:
  assumes
    "weak_simulation RA"
    "weak_simulation RB"
  shows
    "weak_simulation (\<lambda> p q. RA p q \<or> RB p q)"
  using assms unfolding weak_simulation_def by blast

lemma weak_sim_remove_dead_state:
  assumes
    "weak_simulation R"
    "\<And> a p . \<not> step d a p \<and> \<not> step p a d"
  shows
    "weak_simulation (\<lambda> p q . R p q \<and> q \<noteq> d)"
  unfolding weak_simulation_def
proof safe
  fix p q p' a
  assume
    "R p q"
    "q \<noteq> d"
    "p \<longmapsto>a  p'"
  then obtain q' where "R p' q'" "q \<longmapsto>^ a  q'"
    using assms(1) unfolding weak_simulation_def by blast
  moreover hence "q' \<noteq> d"
    using assms(2) `q \<noteq> d` by (metis steps.cases)
  ultimately show "\<exists>q'. (R p' q' \<and> q' \<noteq> d) \<and> q \<longmapsto>^ a  q'" by blast
qed

lemma weak_sim_tau_step:
  "weak_simulation (\<lambda> p1 q1 . q1 \<longmapsto>* tau p1)"
  unfolding weak_simulation_def
  using lts.steps.simps by metis

lemma weak_sim_trans_constructive:
  fixes R1 R2
  defines
    "R \<equiv> \<lambda> p q . \<exists> pq . (R1 p pq \<and> R2 pq q) \<or> (R2 p pq \<and> R1 pq q)"
  assumes
    R1_def: "weak_simulation R1" "R1 p pq" and
    R2_def: "weak_simulation R2" "R2 pq q"
  shows
    "R p q" "weak_simulation R"
proof-
  show "R p q" unfolding R_def using R1_def(2) R2_def(2) by blast
next
  show "weak_simulation R"
    unfolding weak_sim_weak_premise R_def
  proof (safe)
    fix p q pq p' a pq1 pq2
    assume
      "R1 p pq"
      "R2 pq q"
      "\<not> tau a"
      "p \<longmapsto>* tau  pq1"
      "pq1 \<longmapsto>a  pq2"
      "pq2 \<longmapsto>* tau  p'"
    thus "\<exists>q'. (\<exists>pq. R1 p' pq \<and> R2 pq q' \<or> R2 p' pq \<and> R1 pq q') \<and> q \<longmapsto>^ a  q'"
      using R1_def(1) R2_def(1) unfolding weak_sim_weak_premise by blast
  next
    fix p q pq p' a
    assume
      "R1 p pq"
      "R2 pq q"
      "p \<longmapsto>* tau  p'"
      "\<nexists>q'.(\<exists>pq. R1 p' pq \<and> R2 pq q' \<or> R2 p' pq \<and> R1 pq q')\<and> q \<longmapsto>^ a  q'"
      "tau a"
    thus "False"
      using R1_def(1) R2_def(1) unfolding weak_sim_weak_premise by blast
  next
    fix p q pq p' a pq1 pq2
    assume 
      "R1 p pq"
      "R2 pq q"
      "p \<longmapsto>* tau  p'"
      "p \<longmapsto>* tau  pq1"
      "pq1 \<longmapsto>a  pq2"
      "pq2 \<longmapsto>* tau  p'"
    then obtain pq' q' where "R1 p' pq'" "pq \<longmapsto>^ a  pq'" "R2 pq' q'" "q \<longmapsto>^ a  q'"
      using R1_def(1) R2_def(1) assms(3) unfolding weak_sim_weak_premise by blast
    thus "\<exists>q'. (\<exists>pq. R1 p' pq \<and> R2 pq q' \<or> R2 p' pq \<and> R1 pq q') \<and> q \<longmapsto>^ a  q'"
      by blast
  next
    fix p q pq p' a pq1 pq2
    assume sa:
      "R2 p pq"
      "R1 pq q"
      "\<not> tau a"
      "p \<longmapsto>* tau  pq1"
      "pq1 \<longmapsto>a  pq2"
      "pq2 \<longmapsto>* tau  p'"
    then obtain pq' q'  where "R2 p' pq'" "pq \<longmapsto>^ a  pq'" "R1 pq' q'" "q \<longmapsto>^ a  q'"
      using R2_def(1) R1_def(1) unfolding weak_sim_weak_premise by blast
    thus "\<exists>q'. (\<exists>pq. R1 p' pq \<and> R2 pq q' \<or> R2 p' pq \<and> R1 pq q') \<and> q \<longmapsto>^ a  q'"
      by blast
  next
    fix p q pq p' a
    assume
      "R2 p pq"
      "R1 pq q"
      "p \<longmapsto>* tau  p'"
      "\<nexists>q'.(\<exists>pq. R1 p' pq \<and> R2 pq q' \<or> R2 p' pq \<and> R1 pq q')\<and> q \<longmapsto>^ a  q'"
      "tau a"
    thus "False"
      using R1_def(1) R2_def(1) weak_step_tau_tau[OF `p \<longmapsto>* tau  p'` tau_tau]
      unfolding weak_sim_weak_premise by (metis (no_types, lifting))
  next
    fix p q pq p' a pq1 pq2
    assume sa:
      "R2 p pq"
      "R1 pq q"
      "p \<longmapsto>* tau  p'"
      "p \<longmapsto>* tau  pq1"
      "pq1 \<longmapsto>a  pq2"
      "pq2 \<longmapsto>* tau  p'"
    then obtain pq'  where "R2 p' pq'" "pq \<longmapsto>^ a  pq'"
      using R1_def(1) R2_def(1) weak_step_impl_weak_tau[of p a p']
      unfolding weak_sim_weak_premise by blast
    moreover then obtain q' where "R1 pq' q'" "q \<longmapsto>^ a  q'" 
      using R1_def(1) sa(2) unfolding weak_sim_weak_premise by blast
    ultimately show "\<exists>q'. (\<exists>pq. R1 p' pq \<and> R2 pq q' \<or> R2 p' pq \<and> R1 pq q') \<and> q \<longmapsto>^ a  q'"
      by blast
  qed
qed

lemma weak_sim_trans:
  assumes
    "p \<sqsubseteq>ws pq"
    "pq \<sqsubseteq>ws q"
  shows
    "p \<sqsubseteq>ws q"
  using assms(1,2)
proof -
  obtain R1 R2  where  "weak_simulation R1" "R1 p pq" "weak_simulation R2" "R2 pq q"
    using assms(1,2) by blast
  thus ?thesis
    using weak_sim_trans_constructive tau_tau
    by blast
qed

subsection \<open>Weak Bisimulation\<close>

definition weak_bisimulation :: 
  "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
where
  "weak_bisimulation R \<equiv> \<forall> p q. R p q \<longrightarrow> 
    (\<forall> p' a. p \<longmapsto> a p' \<longrightarrow> (\<exists> q'. R p' q'
      \<and> (q \<longmapsto>^ a q'))) \<and>
    (\<forall> q' a. q \<longmapsto> a q' \<longrightarrow> (\<exists> p'. R p' q'
      \<and> ( p \<longmapsto>^ a p')))"
  
lemma weak_bisim_ruleformat:
assumes "weak_bisimulation R"
  and "R p q"
shows
  "p \<longmapsto> a p' \<Longrightarrow> \<not>tau a \<Longrightarrow> (\<exists> q'. R p' q' \<and> (q \<longmapsto>~ a q'))"
  "p \<longmapsto> a p' \<Longrightarrow>  tau a \<Longrightarrow> (\<exists> q'. R p' q' \<and> (q \<longmapsto>* tau q'))"
  "q \<longmapsto> a q' \<Longrightarrow> \<not>tau a \<Longrightarrow> (\<exists> p'. R p' q' \<and> (p \<longmapsto>~ a p'))"
  "q \<longmapsto> a q' \<Longrightarrow>  tau a \<Longrightarrow> (\<exists> p'. R p' q' \<and> (p \<longmapsto>* tau p'))"
  using assms unfolding weak_bisimulation_def by (blast+)
  
definition tau_weak_bisimulation :: 
  "('s \<Rightarrow> 's \<Rightarrow>  bool) \<Rightarrow>  bool"
where
  "tau_weak_bisimulation R \<equiv> \<forall> p q. R p q \<longrightarrow> 
    (\<forall> p' a. p \<longmapsto> a p' \<longrightarrow> 
      (\<exists> q'. R p' q' \<and> (q \<longmapsto>~ a q'))) \<and>
    (\<forall> q' a. q \<longmapsto> a q' \<longrightarrow> 
      (\<exists> p'. R p' q' \<and> (p \<longmapsto>~ a p')))"

lemma weak_bisim_implies_tau_weak_bisim:
  assumes
    "tau_weak_bisimulation R"
  shows
    "weak_bisimulation R"
unfolding weak_bisimulation_def proof (safe)
  fix p q p' a
  assume "R p q" "p \<longmapsto>a  p'"
  thus "\<exists>q'. R p' q' \<and> (q \<longmapsto>^ a  q')"
    using assms weak_steps[of q a _ tau] unfolding tau_weak_bisimulation_def by blast
next
  fix p q q' a
  assume "R p q" "q \<longmapsto>a  q'"
  thus "\<exists>p'. R p' q' \<and> (p \<longmapsto>^ a  p')"
    using assms weak_steps[of p a _ tau] unfolding tau_weak_bisimulation_def by blast
qed

lemma weak_bisim_invert:
  assumes
    "weak_bisimulation R"
  shows
    "weak_bisimulation (\<lambda> p q. R q p)"
using assms unfolding weak_bisimulation_def by auto
  
lemma bisim_weak_bisim:
  assumes "bisimulation R"
  shows "weak_bisimulation R"
  unfolding weak_bisimulation_def
proof (clarify, rule)
  fix p q
  assume R: "R p q"
  show "\<forall>p' a. p \<longmapsto>a  p' \<longrightarrow> (\<exists>q'. R p' q' \<and> (q \<longmapsto>^ a  q'))"
  proof (clarify)
    fix p' a
    assume p'a: "p \<longmapsto>a  p'"
    have
      "\<not> tau a \<longrightarrow> (\<exists>q'. R p' q' \<and> q \<longmapsto>~ a  q')"
      "(tau a \<longrightarrow> (\<exists>q'. R p' q' \<and> q \<longmapsto>* tau  q'))" 
      using bisim_ruleformat(1)[OF assms R p'a] step_weak_step step_weak_step_tau by auto
    thus "\<exists>q'. R p' q' \<and> (q \<longmapsto>^ a  q')" by blast
  qed
next 
  fix p q
  assume R: "R p q"
  have "\<forall>q' a. q \<longmapsto>a  q' \<longrightarrow> (\<not> tau a \<longrightarrow> (\<exists>p'. R p' q' \<and> p \<longmapsto>~ a  p'))
     \<and> (tau a \<longrightarrow> (\<exists>p'. R p' q' \<and> p \<longmapsto>* tau  p'))"
  proof (clarify)
    fix q' a
    assume q'a: "q \<longmapsto>a  q'"
    show
      "(\<not> tau a \<longrightarrow> (\<exists>p'. R p' q' \<and> p \<longmapsto>~ a  p')) \<and>
      (tau a \<longrightarrow> (\<exists>p'. R p' q' \<and> p \<longmapsto>* tau  p'))" 
      using bisim_ruleformat(2)[OF assms R q'a] step_weak_step
        step_weak_step_tau steps_one_step by auto
  qed
  thus "\<forall>q' a. q \<longmapsto>a  q' \<longrightarrow> (\<exists>p'. R p' q' \<and> (p \<longmapsto>^ a  p'))" by blast
qed
  
lemma weak_bisim_weak_sim:  
shows
  "weak_bisimulation R = (weak_simulation R \<and> weak_simulation (\<lambda> p q . R q p))"
unfolding weak_bisimulation_def weak_simulation_def by auto

lemma steps_retain_weak_bisim:
  assumes 
    "weak_bisimulation R"
    "R p q"
    "p \<longmapsto>*A  p'"
    "\<And> a . tau a \<Longrightarrow> A a"
  shows "\<exists>q'. R p' q' \<and> q \<longmapsto>*A  q'"
    using assms weak_bisim_weak_sim steps_retain_weak_sim
    by auto
  
lemma weak_bisim_union:
  assumes
    "weak_bisimulation R1"
    "weak_bisimulation R2"
  shows
    "weak_bisimulation (\<lambda> p q . R1 p q \<or> R2 p q)"
  using assms unfolding weak_bisimulation_def by blast

subsection \<open>Delay Simulation\<close>

definition delay_simulation :: 
  "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
where
  "delay_simulation R \<equiv> \<forall> p q. R p q \<longrightarrow> 
    (\<forall> p' a. p \<longmapsto> a p' \<longrightarrow> (\<exists> q'. R p' q'
      \<and> (q \<longmapsto>^~ a q')))"

lemma delay_simulation_implies_weak_simulation:
  assumes
    "delay_simulation R"
  shows
    "weak_simulation R"
  using assms weak_step_delay_implies_weak_tau
  unfolding delay_simulation_def weak_simulation_def by blast

subsection \<open>Bell's Eventual Simulation\<close>
  
--"NOTE: Bell actually defines this on weak step-sequences rather than on single weak steps!!"
definition eventual_sim ::
  "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
where
  "eventual_sim R \<equiv> \<forall> p q p' a .
    R p q \<and> (p \<longmapsto>^ a p') \<longrightarrow>
    (\<exists> p'' q''.
        (p' \<longmapsto>* tau p'') 
      \<and> (q \<longmapsto>^ a q'')
      \<and> R p'' q'')"

definition eventual_bisim ::
  "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
where
  "eventual_bisim R \<equiv> eventual_sim R \<and> eventual_sim (\<lambda> p q . R q p)"
  
subsection \<open>Contrasimulation\<close>

definition contrasim ::
  "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
where
  "contrasim R \<equiv> \<forall> p q p' A .
    R p q \<and> (p \<longmapsto>^* A p') \<longrightarrow>
    (\<exists> q'. (q \<longmapsto>^* A q')
         \<and> R q' p')"

definition contrasim_step ::
  "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
where
  "contrasim_step R \<equiv> \<forall> p q p' a .
    R p q \<and> (p \<longmapsto>^ a p') \<longrightarrow>
    (\<exists> q'. (q \<longmapsto>^ a q')
         \<and> R q' p')"

lemma contrasim_step_weaker_than_seq:
  assumes
    "contrasim R"
  shows
    "contrasim_step R"
  unfolding contrasim_step_def
proof ((rule allI impI)+)
  fix p q p' a
  assume
    "R p q \<and> p \<longmapsto>^ a  p'"
  hence
    "R p q" "p \<longmapsto>^ a  p'" by safe
  hence "p \<longmapsto>^* [a]  p'" by safe
  then obtain q' where "R q' p'" "q \<longmapsto>^* [a]  q'"
    using assms `R p q` unfolding contrasim_def by blast
  hence "q \<longmapsto>^ a  q'" by blast
  thus "\<exists>q'. q \<longmapsto>^ a  q' \<and> R q' p'" using `R q' p'` by blast
qed

lemma contrasim_step_seq_coincide_for_sims:
  assumes
    "contrasim_step R"
    "weak_simulation R"
  shows
    "contrasim R"
  unfolding contrasim_def
proof (clarify)
  fix p q p' A
  assume
    "R p q"
    "p \<longmapsto>^* A  p'"
  thus "\<exists>q'. q \<longmapsto>^* A  q' \<and> R q' p'"
  proof (induct A arbitrary: p p' q)
    case Nil
    then show ?case using assms(1) unfolding contrasim_step_def
      using tau_tau weak_step_seq.simps(1) by blast
  next
    case (Cons a A)
    then obtain p1 where p1_def: "p \<longmapsto>^ a p1" "p1 \<longmapsto>^* (A)  p'" by auto
    then obtain q1 where q1_def: "q \<longmapsto>^ a q1" "R p1 q1" 
      using assms(2) `R p q` unfolding weak_sim_weak_premise by blast
    then obtain q' where "q1 \<longmapsto>^* (A)  q'" "R q' p'" using p1_def(2) Cons(1) by blast
    then show ?case using q1_def(1) by auto
  qed
qed

lemma eventual_bisim_implies_contrasim:
  assumes
    "eventual_bisim R" and
    symmetry: "\<And> p q . R p q \<Longrightarrow> R q p"
      --"it's alright to require symmetry because eventual bisimilarity is symmetric."
  shows 
    "contrasim_step (\<lambda> p q. \<exists>q'. q \<longmapsto>* tau q' \<and> R p q')"
  unfolding contrasim_step_def 
proof clarify
  fix p q p' a q' pq1 pq2
  assume challenge:
    "q \<longmapsto>* tau  q'"
    "R p q'"
    "tau a \<longrightarrow> p \<longmapsto>* tau  p'"
    "\<not> tau a \<longrightarrow> p \<longmapsto>~ a  p'"
  then obtain p'' q'' where p''q''_def:
    "p' \<longmapsto>* tau  p''"
    "q' \<longmapsto>^ a q''"
    "R p'' q''"
    using assms unfolding eventual_bisim_def eventual_sim_def by blast
  hence
    "(tau a \<longrightarrow> q \<longmapsto>* tau  q'') \<and>
    (\<not> tau a \<longrightarrow> q \<longmapsto>~ a q'')"
    using challenge steps_concat by blast
  hence "(\<not> tau a \<longrightarrow> q \<longmapsto>~ a  q'') \<and>
            (tau a \<longrightarrow> q \<longmapsto>* tau  q'') \<and> ( p' \<longmapsto>* tau p'' \<and> R p'' q'')"
    using p''q''_def by blast
  thus "\<exists>q'. q \<longmapsto>^ a  q' \<and> (\<exists>q'a. p' \<longmapsto>* tau  q'a \<and> R q' q'a)"
    using symmetry by blast
qed

definition contrasim_strong_step ::
  "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
where
  "contrasim_strong_step R \<equiv> \<forall> p q p' a .
    R p q \<and> (p \<longmapsto> a p') \<longrightarrow>
    (\<exists> q'. (q \<longmapsto>^ a q')
         \<and> R q' p')"

lemma contrasim_challenge_strength_step_impl_strong_step:
  assumes
    "contrasim_step R"
  shows
    "contrasim_strong_step R"
  using assms step_weak_step_tau
  unfolding contrasim_step_def contrasim_strong_step_def by fastforce

lemma contrasim_reflexive:
  shows
    "contrasim (\<lambda> p q . p = q)"
  unfolding contrasim_def using step_weak_step_tau by blast

lemma contrasim_union:
  assumes
    "contrasim R1"
    "contrasim R2"
  shows
    "contrasim (\<lambda> p q . R1 p q \<or> R2 p q)"
  using assms unfolding contrasim_def by (blast)

abbreviation coupling ::
  "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
  where "coupling R \<equiv> \<forall> p q . R p q \<longrightarrow> (\<exists> q'. q \<longmapsto>*tau q' \<and> R q' p)"

lemma contrasim_implies_coupling:
  assumes
    "contrasim R" --"actually also is true with 'weaker' @{term contrasim_step}"
    "R p q"
  shows
    "\<exists> q'. q \<longmapsto>*tau q' \<and> R q' p"
proof -
  have "p \<longmapsto>* tau p" using steps.refl by blast
  hence "p \<longmapsto>^ \<tau> p" using tau_tau by blast
  then obtain q' where "q \<longmapsto>^ \<tau> q'" "R q' p"
    using `R p q` `contrasim R` unfolding contrasim_def  by blast
  then moreover have "q \<longmapsto>* tau q'" using tau_tau by blast
  ultimately show ?thesis by blast
qed

lemma symm_contrasim_implies_weak_bisim:
  assumes
    "contrasim_strong_step R"
    "\<And> p q . R p q \<Longrightarrow> R q p"
  shows
    "weak_bisimulation R"
  unfolding weak_bisimulation_def
proof safe
  fix p q p' a
  assume "R p q" "p \<longmapsto>a  p'"
  then obtain q' where q'_def: "q \<longmapsto>^ a q'" "R q' p'"
    using assms(1) unfolding contrasim_strong_step_def by blast
  thus "\<exists>q'. R p' q' \<and> q \<longmapsto>^ a  q'" using assms(2) by blast
next
  fix p q q' a
  assume "R p q" "q \<longmapsto>a  q'"
  hence "R q p" using assms(2) by blast
  then obtain p' where p'_def: "p \<longmapsto>^ a p'" "R p' q'"
    using `q \<longmapsto>a  q'` assms(1) unfolding contrasim_strong_step_def by blast
  thus "\<exists>p'. R p' q' \<and> p \<longmapsto>^ a  p'" using assms(2) by blast
qed

lemma coupling_tau_max_symm:
  assumes
    "R p q \<longrightarrow> (\<exists> q'. q \<longmapsto>*tau q' \<and> R q' p)"
    "tau_max q"
    "R p q"
  shows
    "R q p"
  using assms steps_no_step_pos[of q tau] by blast

corollary coupling_stability_symm:
  assumes
    "R p q \<longrightarrow> (\<exists> q'. q \<longmapsto>*tau q' \<and> R q' p)"
    "stable_state q"
    "R p q"
  shows
    "R q p"
  using coupling_tau_max_symm stable_tauclosure_only_loop assms by metis

lemma taufree_contrasim_symm:
  assumes
    "\<And> p1 a p2 . (p1 \<longmapsto> a p2 \<Longrightarrow> \<not> tau a)"
    "contrasim R"
    "R p q"
  shows "R q p"
  using assms contrasim_implies_coupling
  by (metis steps.cases)

lemma taufree_contrasim_implies_weak_bisim:
  assumes
    "\<And> p1 a p2 . (p1 \<longmapsto> a p2 \<Longrightarrow> \<not> tau a)"
    "contrasim R"
  shows
    "weak_bisimulation R"
  using assms symm_contrasim_implies_weak_bisim taufree_contrasim_symm
    contrasim_step_weaker_than_seq[OF assms(2)]
    contrasim_challenge_strength_step_impl_strong_step by blast

lemma contrasim_challenge_strength_does_not_imply:
  fixes p1 q1
  defines
    "R \<equiv> \<lambda> p q . p = p1 \<and> q = q1"
  assumes
    "p1 \<noteq> q1"
    "trans = (\<lambda> p a p' . False)"
  shows
    "contrasim_strong_step R" "\<not>contrasim R"
  using taufree_contrasim_symm[of R p1 q1] assms
  unfolding contrasim_strong_step_def by (blast+)

end -- "context @{locale lts_tau}"
  
subsection \<open>Adding a tau sink retains similarity\<close>
  
lemma simulation_tau_sink_1:
  fixes
    step sink \<tau> R
  defines
    "step2 \<equiv> \<lambda> p1 a p2 . (p1 \<noteq> sink \<and> a = \<tau> \<and> p2 = sink) \<or> step p1 a p2"
  assumes
    "\<And> a p . \<not> step sink a p"
    "lts_tau.weak_simulation step \<tau> R"
  shows
    "lts_tau.weak_simulation step2 \<tau> (\<lambda> p q. p = sink \<or> R p q)"
proof -
  let ?tau = "(lts_tau.tau \<tau>)"
  let ?tauEx = "\<tau>"
  show ?thesis
    unfolding "lts_tau.weak_simulation_def"
  proof safe
    fix p q p' a
    assume "step2 sink a p'"
    hence "p' = sink" "a = \<tau>"
      using assms(2) unfolding step2_def by auto
    thus "\<exists>q'. (p' = sink \<or> R p' q') \<and>
      (?tau a \<longrightarrow> lts.steps step2 q ?tau q') \<and> 
      (\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. lts.steps step2 q ?tau pq1 \<and> step2 pq1 a pq2 
        \<and> lts.steps step2 pq2 ?tau q'))"
      using lts_tau.step_tau_refl[of \<tau> step2 q] lts.steps.refl[of step2 q ?tau]  by auto
  next
    fix p q p' a
    assume "step2 p a p'" "R p q"
    have step_impl_step2: "\<And> p1 a p2 . step p1 a p2 \<Longrightarrow> step2 p1 a p2"
      unfolding step2_def by blast
    have "(p \<noteq> sink \<and> a = ?tauEx \<and> p' = sink) \<or> step p a p'"
      using `step2 p a p'` unfolding step2_def .
    thus "\<exists>q'. (p' = sink \<or> R p' q') \<and>
      (?tau a \<longrightarrow> lts.steps step2 q ?tau q') \<and>
      (\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. lts.steps step2 q ?tau pq1 \<and> step2 pq1 a pq2
        \<and> lts.steps step2 pq2 ?tau q'))"
    proof safe
      show "\<exists>q'. (sink = sink \<or> R sink q') \<and>
           (?tau ?tauEx \<longrightarrow> lts.steps step2 q ?tau q') \<and>
           (\<not> ?tau ?tauEx \<longrightarrow> (\<exists>pq1 pq2. lts.steps step2 q ?tau pq1
            \<and> step2 pq1 ?tauEx pq2 \<and> lts.steps step2 pq2 ?tau q'))"
        using lts.steps.refl[of step2 q ?tau] assms(1) by (meson lts_tau.tau_tau)
    next
      assume "step p a p'"
      then obtain q' where q'_def:
        "R p' q' \<and>
        (?tau a \<longrightarrow> lts.steps step q ?tau q') \<and>
        (\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. lts.steps step q ?tau pq1 \<and> step pq1 a pq2
          \<and> lts.steps step pq2 ?tau q'))"
        using assms(3) `R p q` unfolding lts_tau.weak_simulation_def by blast
      hence "(p' = sink \<or> R p' q') \<and>
        (?tau a \<longrightarrow> lts.steps step2 q ?tau q') \<and>
        (\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. lts.steps step2 q ?tau pq1 \<and> step2 pq1 a pq2
          \<and> lts.steps step2 pq2 ?tau q'))"
        using lts_impl_steps[of step _ _ _ step2] step_impl_step2 by blast
      thus "\<exists>q'. (p' = sink \<or> R p' q') \<and>
        (?tau a \<longrightarrow> lts.steps step2 q ?tau q') \<and>
        (\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. lts.steps step2 q ?tau pq1 \<and> step2 pq1 a pq2
          \<and> lts.steps step2 pq2 ?tau q'))"
        by blast
    qed
  qed
qed
  
lemma simulation_tau_sink_2:
  fixes
    step sink R \<tau>
  defines
    "step2 \<equiv> \<lambda> p1 a p2 . (p1 \<noteq> sink \<and> a = \<tau> \<and> p2 = sink) \<or> step p1 a p2"
  assumes
    "\<And> a p . \<not> step sink a p \<and> \<not> step p a sink"
    "lts_tau.weak_simulation step2 \<tau> (\<lambda> p q. p = sink \<or> R p q)"
    "\<And> p' q' q . (p' = sink \<or> R p' q') 
      \<and> lts.steps step2 q (lts_tau.tau \<tau>) q'  \<longrightarrow> (p' = sink \<or> R p' q)"
  shows
    "lts_tau.weak_simulation step \<tau> (\<lambda> p q. p = sink \<or> R p q)"
proof -
  let ?tau = "(lts_tau.tau \<tau>)"
  let ?tauEx = "\<tau>"
  show ?thesis
    unfolding lts_tau.weak_simulation_def
  proof safe
    fix p q p' a
    assume
      "step sink a p'"
    hence False using assms(2) by blast
    thus "\<exists>q'. (p' = sink \<or> R p' q') \<and>
      (?tau a \<longrightarrow> lts.steps step q ?tau q') \<and>
      (\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. lts.steps step q ?tau pq1 \<and> step pq1 a pq2
        \<and> lts.steps step pq2 ?tau q'))" ..
  next
    fix p q p' a
    assume "R p q" "step p a p'"
    hence not_sink: "p \<noteq> sink" "p' \<noteq> sink"
      using assms(2)[of a p] assms(2)[of a p'] by auto
    have "step2 p a p'" using `step p a p'` unfolding step2_def by blast
    then obtain q' where q'_def:
      "p' = sink \<or> R p' q'"
      "?tau a \<longrightarrow> lts.steps step2 q ?tau q'"  
      "\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. lts.steps step2 q ?tau pq1 \<and> step2 pq1 a pq2 
        \<and> lts.steps step2 pq2 ?tau q')"
      using assms(3) `R p q` unfolding lts_tau.weak_simulation_def by blast
    hence outer_goal_a: "R p' q'" using not_sink by blast
    show "\<exists>q'. (p' = sink \<or> R p' q') \<and>
      (?tau a \<longrightarrow> lts.steps step q ?tau q') \<and>
      (\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. lts.steps step q ?tau pq1 \<and> step pq1 a pq2
        \<and> lts.steps step pq2 ?tau q'))"
    proof (cases "q' = sink")
      assume "q' = sink"
      then obtain q'' where q''_def:
        "?tau a \<longrightarrow> (lts.steps step q ?tau q'' \<and> lts.steps step2 q'' ?tau q')"
        "\<not> ?tau a \<longrightarrow> (\<exists>pq1. lts.steps step2 q ?tau pq1 \<and> step pq1 a q''
          \<and> lts.steps step2 q'' ?tau q')"
        using q'_def(2,3) assms(1) step2_def lts_tau.step_tau_refl[of \<tau>]
          lts_tau.tau_tau[of \<tau>] by metis
      hence "q'' = sink \<longrightarrow> q = sink"
        using assms(2) unfolding step2_def by (metis lts.steps.cases)
      have "lts.steps step2 q'' ?tau q'" using q''_def by auto
      hence "p' = sink \<or> R p' q''" using  q'_def(1) assms(4)[of p' q' q''] by blast
      moreover have "\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. lts.steps step q ?tau pq1 \<and> step pq1 a pq2
        \<and> lts.steps step pq2 ?tau q'')"
      proof
        assume "\<not> ?tau a"
        hence "q \<noteq> sink" using q'_def by (metis assms(2) lts.steps_left step2_def)
        hence "q'' \<noteq> sink" using `q'' = sink \<longrightarrow> q = sink` by simp
        obtain pq1 where pq1_def:
            "lts.steps step2 q ?tau pq1" "step pq1 a q''" "lts.steps step2 q'' ?tau q'"
          using q''_def(2) `\<not> ?tau a` by blast
        hence "pq1 \<noteq> sink" using `q'' \<noteq> sink` assms(2) by blast
        hence "lts.steps step q ?tau pq1" using `q \<noteq> sink` `lts.steps step2 q ?tau pq1`
        proof (induct rule: lts.steps.induct[OF `lts.steps step2 q ?tau pq1`])
          case (1 p af)
          then show ?case using lts.steps.refl[of step p af] by blast
        next
          case (2 p af q1 a q)
          hence "q1 \<noteq> sink" "step q1 a q" using assms(2) unfolding step2_def by auto
          moreover hence "lts.steps step p af q1" using 2 by blast 
          ultimately show ?case using 2(4) by (meson lts.step)
        qed
        thus
          " \<exists>pq1 pq2. lts.steps step q ?tau pq1 \<and> step pq1 a pq2 \<and> lts.steps step pq2 ?tau q''"
          using pq1_def(2) lts.steps.refl[of step q'' ?tau] by blast
      qed
      ultimately show "\<exists>q''. (p' = sink \<or> R p' q'') \<and>
           (?tau a \<longrightarrow> lts.steps step q ?tau q'') \<and>
           (\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. lts.steps step q ?tau pq1 \<and> step pq1 a pq2
            \<and> lts.steps step pq2 ?tau q''))"
        using q''_def(1) q'_def(1) by auto
    next
      assume not_sink_q': "q' \<noteq> sink"
      have outer_goal_b: "?tau a \<longrightarrow> lts.steps step q ?tau q'"
        using q'_def(2) not_sink_q' unfolding step2_def
      proof (safe)
        assume i:
          "q' \<noteq> sink" "?tau a"
          "lts.steps (\<lambda>p1 a p2.  p1 \<noteq> sink \<and> a = ?tauEx \<and> p2 = sink \<or> step p1 a p2) q ?tau q'"
        thus "lts.steps step q ?tau q'"
        proof (induct rule: lts.steps.induct[OF i(3)])
          case (1 p af)
          then show ?case using lts.steps.refl[of _ p af] by auto
        next
          case (2 p af q1 a q)
          hence "step q1 a q" by blast
          moreover have "lts.steps step p af q1" using 2 assms(2) by blast
          ultimately show ?case using `af a` lts.step[of step p af q1 a q] by blast
        qed
      qed
      have outer_goal_c:
          "\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. lts.steps step q ?tau pq1 \<and> step pq1 a pq2
          \<and> lts.steps step pq2 ?tau q')"
        using q'_def(3)
      proof safe
        fix pq1 pq2
        assume subassms:
          "\<not> ?tau a"
          "lts.steps step2 q ?tau pq1"
          "step2 pq1 a pq2"
          "lts.steps step2 pq2 ?tau q'"
        have "pq2 \<noteq> sink" 
          using subassms(4) assms(2) not_sink_q' lts.steps_loop
          unfolding step2_def by (metis (mono_tags, lifting))
        have  goal_c: "lts.steps step pq2 ?tau q'"
          using subassms(4) not_sink_q' unfolding step2_def
        proof (induct rule:lts.steps.induct[OF subassms(4)])
          case (1 p af) show ?case using lts.steps.refl by assumption
        next
          case (2 p af q1 a q)
          hence "step q1 a q" unfolding step2_def by simp
          moreover hence "q1 \<noteq> sink" using assms(2) by blast
          ultimately have "lts.steps step p af q1" using 2 unfolding step2_def by auto
          thus ?case using `step q1 a q` 2(4) lts.step[of step p af q1 a q] by blast
        qed
        have goal_b: "step pq1 a pq2"
          using `pq2 \<noteq> sink` subassms(3) unfolding step2_def by blast
        hence "pq1 \<noteq> sink" using assms(2) by blast
        hence goal_a: "lts.steps step q ?tau pq1"
          using subassms(4) unfolding step2_def
        proof (induct rule:lts.steps.induct[OF subassms(2)])
          case (1 p af) show ?case using lts.steps.refl by assumption
        next
          case (2 p af q1 a q)
          hence "step q1 a q" unfolding step2_def by simp
          moreover hence "q1 \<noteq> sink" using assms(2) by blast
          ultimately have "lts.steps step p af q1" using 2 unfolding step2_def by auto
          thus ?case using `step q1 a q` 2(4) lts.step[of step p af q1 a q] by blast
        qed
        thus
          "\<exists>pq1 pq2. lts.steps step q ?tau pq1 \<and> step pq1 a pq2 \<and> lts.steps step pq2 ?tau q'"
          using goal_b goal_c by auto
      qed
      thus "\<exists>q'. (p' = sink \<or> R p' q') \<and> (?tau a \<longrightarrow> lts.steps step q ?tau q') \<and>
        (\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. lts.steps step q ?tau pq1 \<and> step pq1 a pq2
          \<and> lts.steps step pq2 ?tau q'))"
        using outer_goal_a outer_goal_b by auto
    qed
  qed
qed

lemma simulation_sink_invariant:
  fixes
    step sink \<tau> R
  defines
    "step2 \<equiv> \<lambda> p1 a p2 . (p1 \<noteq> sink \<and> a =  \<tau> \<and> p2 = sink) \<or> step p1 a p2"
  assumes
    "\<And> a p . \<not> step sink a p \<and> \<not> step p a sink"
  shows "lts_tau.weakly_simulated_by step2 \<tau> p q = lts_tau.weakly_simulated_by step \<tau> p q"
proof (rule)
  have sink_sim_min: "lts_tau.weak_simulation step2 \<tau> (\<lambda> p q. p = sink)"
    unfolding lts_tau.weak_simulation_def step2_def using assms(2)
    by (meson lts.steps.simps)
  define R where "R \<equiv> lts_tau.weakly_simulated_by step2 \<tau>"
  have weak_sim_R: "lts_tau.weak_simulation step2 \<tau> R"
    using lts_tau.weaksim_greatest[of step2 \<tau>] unfolding R_def by blast
  have R_contains_inv_tau_closure:
    "R = (\<lambda>p1 q1. R p1 q1 \<or> lts.steps step2 q1 (lts_tau.tau \<tau>) p1)" unfolding R_def
  proof (rule, rule, rule, simp)
    fix p q
    assume
      "(\<exists>R. lts_tau.weak_simulation step2 \<tau>  R \<and> R p q) \<or> lts.steps step2 q (lts_tau.tau \<tau>) p"
    thus "\<exists>R. lts_tau.weak_simulation step2 \<tau> R \<and> R p q"
      using weak_sim_R
            lts_tau.weak_sim_tau_step[of step2 "\<tau>"]
            lts_tau.weak_sim_union_cl[of step2 "\<tau>"] by blast
  qed
  assume Rpq: "R p q"
  have "\<And> p' q' q . R p' q' \<and> lts.steps step2 q (lts_tau.tau \<tau>) q'  \<longrightarrow> R p' q"
    using R_contains_inv_tau_closure lts_tau.weak_sim_trans[of step2 "\<tau>" _ _ _] R_def assms(2)
    by meson
  hence closed_R:
      "\<And> p' q' q . (p' = sink \<or> R p' q') \<and> lts.steps step2 q (lts_tau.tau \<tau>) q'
         \<longrightarrow> (p' = sink \<or> R p' q)"
    using weak_sim_R sink_sim_min lts_tau.weak_sim_union_cl by blast
  have "lts_tau.weak_simulation step2 \<tau> (\<lambda>p q. p = sink \<or> R p q)"
    using weak_sim_R sink_sim_min lts_tau.weak_sim_union_cl[of step2 \<tau>] by blast
  hence "lts_tau.weak_simulation step \<tau> (\<lambda>p q. p = sink \<or> R p q)"
    using  simulation_tau_sink_2[of step sink \<tau> R] assms(2) closed_R
    unfolding step2_def by blast
  thus "\<exists>R. lts_tau.weak_simulation step \<tau> R \<and> R p q"
    using Rpq weak_sim_R by blast
next
  show "\<exists>R. lts_tau.weak_simulation step \<tau> R \<and> R p q \<Longrightarrow>
        \<exists>R. lts_tau.weak_simulation step2 \<tau> R \<and> R p q"
  proof clarify
    fix R
    assume
      "lts_tau.weak_simulation step \<tau> R"
      "R p q"
    hence "lts_tau.weak_simulation
        (\<lambda>p1 a p2. p1 \<noteq> sink \<and> a = \<tau> \<and> p2 = sink \<or> step p1 a p2) \<tau> (\<lambda>p q. p = sink \<or> R p q)"
      using simulation_tau_sink_1[of step sink \<tau> R] assms(2) unfolding step2_def by auto
    thus "\<exists>R. lts_tau.weak_simulation step2 \<tau> R \<and> R p q"
      using `R p q` unfolding step2_def by blast
  qed
qed

end