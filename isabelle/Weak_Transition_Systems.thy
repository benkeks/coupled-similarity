section \<open>Transition Systems with Silent Steps\<close>

theory Weak_Transition_Systems
  imports Transition_Systems
begin

locale lts_tau = lts trans for
  trans :: "'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool"
+ fixes
  \<tau> :: "'a"
begin
  
definition tau :: "'a \<Rightarrow> bool" where "tau a \<equiv> (a = \<tau>)"

lemma tau_tau[simp]: "tau \<tau>" unfolding tau_def by simp

abbreviation weak_step :: "'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool"
    ("_ \<longmapsto>~ _  _" [70, 70, 70] 80)
where
  "(p \<longmapsto>~ a q) \<equiv> (\<exists> pq1 pq2. 
        p \<longmapsto>* tau pq1
    \<and> pq1 \<longmapsto>  a   pq2
    \<and> pq2 \<longmapsto>* tau q)"
text {*
  this corresponds to @{text "\<Longrightarrow>^\<alpha>"} in Sangiorgi
  the tau step transitive closure @{text "'\<Longrightarrow>'"} of Sangiorgi is  @{text "'\<longmapsto>* tau'"}
  note that @{text "'\<Longrightarrow>^\<tau>'"} is defined as an alias for @{text "'\<Longrightarrow>'"} in [Par92] whereas Sangiorgi and
  this formalization consider @{text "'\<Longrightarrow>^\<tau>'"} / @{text "'p \<longmapsto>~ a q \<and> tau a'"} to enforce at least one @{text "\<tau>"}-step.
*}

lemma step_weak_step:
  assumes "p \<longmapsto> a p'"
  shows   "p \<longmapsto>~ a p'"
  using assms steps.refl by auto
    
abbreviation weak_step_tau :: "'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool"
    ("_ \<longmapsto>^ _  _" [70, 70, 70] 80)
where
  "(p \<longmapsto>^ a q) \<equiv>
      (tau a \<longrightarrow> p \<longmapsto>* tau q)
    \<and> (\<not>tau a \<longrightarrow> p \<longmapsto>~ a q)"

abbreviation weak_step_delay :: "'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool"
    ("_ \<longmapsto>^~ _  _" [70, 70, 70] 80)
where
  "(p \<longmapsto>^~ a q) \<equiv> 
      (tau a \<longrightarrow> p \<longmapsto>* tau q) \<and>
      (\<not>tau a \<longrightarrow>  (\<exists> pq.
            p \<longmapsto>* tau pq
        \<and> pq \<longmapsto>  a   q))"

lemma weak_step_delay_implies_weak_tau:
  assumes "p \<longmapsto>^~ a p'"
  shows "p \<longmapsto>^ a p'"
  using assms steps.refl[of p' tau] by blast

primrec weak_step_seq :: "'s \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> bool"
    ("_ \<longmapsto>^* _  _" [70, 70, 70] 80)
  where
    "weak_step_seq p0 [] p1 = p0 \<longmapsto>* tau p1"
  | "weak_step_seq p0 (a#A) p1 = (\<exists> p01 . p0 \<longmapsto>^ a p01 \<and> weak_step_seq p01 A p1)"

lemma step_weak_step_tau:
  assumes "p \<longmapsto> a p'"
  shows   "p \<longmapsto>^ a p'"
  using step_weak_step[OF assms] steps_one_step[OF assms]
  by blast
    
lemma step_tau_refl:
  shows   "p \<longmapsto>^ \<tau> p"
  using steps.refl[of p tau]
  by simp
    
lemma weak_step_tau_weak_step[simp]:
  assumes "p \<longmapsto>^ a p'" "\<not> tau a"
  shows   "p \<longmapsto>~ a p'"
  using assms by auto
  
lemma weak_steps:
  assumes
    "p \<longmapsto>~ a  p'"
    "\<And> a . tau a \<Longrightarrow> A a"
    "A a"
  shows
    "p \<longmapsto>* A  p'"
proof-
  obtain pp pp' where pp:
    "p \<longmapsto>* tau pp" "pp \<longmapsto> a  pp'" "pp' \<longmapsto>* tau p'"
    using assms(1) by blast
  then have cascade:
    "p \<longmapsto>* A pp" "pp \<longmapsto>* A  pp'" "pp' \<longmapsto>* A p'"
    using steps_one_step steps_spec assms(2,3) by auto
  have "p \<longmapsto>* A pp'" using steps_concat[OF cascade(2) cascade(1)] .
  show ?thesis using steps_concat[OF cascade(3) `p \<longmapsto>* A  pp'`] .
qed
  
lemma weak_step_impl_weak_tau:
  assumes "p \<longmapsto>~ a p'"
  shows   "p \<longmapsto>^ a p'"
  using assms weak_steps[OF assms, of tau] by auto
  
lemma weak_impl_strong_step:
  assumes
    "p \<longmapsto>~ a  p''"
  shows
    "(\<exists> a' p' . tau a' \<and> p \<longmapsto> a'  p') \<or> (\<exists> p' . p \<longmapsto> a  p')"
proof -
  from assms obtain pq1 pq2 where pq12:
    "p \<longmapsto>* tau pq1"
    "pq1 \<longmapsto>  a   pq2"
    "pq2 \<longmapsto>* tau p''" by blast
  show ?thesis
  proof (cases "p = pq1")
    case True
    then show ?thesis using pq12 by blast
  next
    case False
    then show ?thesis using pq12 steps_left[of p pq1 tau] by blast
  qed
qed
  
lemma weak_step_extend:
  assumes 
    "p1 \<longmapsto>* tau p2"
    "p2 \<longmapsto>^ a p3"
    "p3 \<longmapsto>* tau p4"
  shows
    "p1 \<longmapsto>^ a p4"
  using assms steps_concat by blast
    
lemma weak_step_tau_tau:
  assumes 
    "p1 \<longmapsto>* tau p2"
    "tau a"
  shows
    "p1 \<longmapsto>^ a p2"
  using assms by blast

lemma weak_single_step[iff]: 
  "p \<longmapsto>^* [a] p' \<longleftrightarrow> p \<longmapsto>^ a  p'"
  using steps.refl[of p' tau]
  by (meson steps_concat weak_step_seq.simps(1) weak_step_seq.simps(2)) 

abbreviation weak_enabled :: "'s \<Rightarrow> 'a \<Rightarrow> bool"
where
  "weak_enabled p a \<equiv>
    \<exists> pq1 pq2. p \<longmapsto>* tau pq1 \<and> pq1 \<longmapsto>  a pq2"

lemma weak_enabled_step:
  shows "weak_enabled p a = (\<exists> p'. p \<longmapsto>~ a p')"
  using step_weak_step steps_concat by blast

abbreviation tau_max :: "'s \<Rightarrow> bool" where
  "tau_max p \<equiv>  (\<forall>p'. p \<longmapsto>* tau p' \<longrightarrow> p = p')"

lemma tau_max_deadlock:
  fixes q
  assumes
    "\<And> r1 r2. r1 \<longmapsto>* tau r2 \<and> r2 \<longmapsto>* tau r1 \<Longrightarrow> r1 = r2" \<comment>\<open>contracted cycles (anti-symmetry)\<close>
    "finite {q'. q \<longmapsto>* tau q'}"
  shows
    "\<exists> q' . q \<longmapsto>* tau q' \<and> tau_max q'"
  using step_max_deadlock assms by blast

abbreviation stable_state :: "'s \<Rightarrow> bool" where
  "stable_state p \<equiv> \<nexists> p' . step_pred p tau p'"
  
lemma stable_tauclosure_only_loop:
  assumes
    "stable_state p"
  shows
    "tau_max p"
  using assms  steps_left by blast

coinductive divergent_state :: "'s \<Rightarrow> bool" where
  omega: "divergent_state p' \<Longrightarrow> tau t \<Longrightarrow>  p \<longmapsto>t p'\<Longrightarrow> divergent_state p"
text {* @{text \<open>this seems not to be in line with def in [Sangiorgi12, p. 115], which reads
  "largest predicate s.t. divergent_state p implies p tau-steps to p' for some divergent_state p'."\<close>}*}
    
lemma ex_divergent:
  assumes "p \<longmapsto>a p" "tau a"
  shows "divergent_state p"
using assms proof (coinduct)
  case (divergent_state p)
  then show ?case using assms by auto
qed
  
lemma ex_not_divergent:
  assumes "\<forall>a q. p \<longmapsto>a q \<longrightarrow> \<not> tau a" "divergent_state p"
  shows "False"
using assms(2) proof (cases rule:divergent_state.cases)
  case (omega p' t)
  thus ?thesis using assms(1) by auto
qed

lemma perpetual_instability_divergence:
  assumes
    "\<forall> p' . p \<longmapsto>* tau p' \<longrightarrow> \<not> stable_state p'"
  shows
    "divergent_state p"
  using assms
proof (coinduct rule: divergent_state.coinduct)
  case (divergent_state p)
  then obtain t p' where "tau t" "p \<longmapsto>t  p'" using steps.refl by blast
  then moreover have "\<forall>p''. p' \<longmapsto>* tau  p'' \<longrightarrow> \<not> stable_state p''"
    using divergent_state step_weak_step_tau steps_concat by blast
  ultimately show ?case by blast 
qed

corollary non_divergence_implies_eventual_stability:
  assumes
    "\<not> divergent_state p"
  shows
    "\<exists> p' . p \<longmapsto>* tau p' \<and> stable_state p'"
  using assms perpetual_instability_divergence by blast
  
end \<comment>\<open>context @{locale lts_tau}\<close>
  
end