section \<open>Transition Systems\<close>

theory Transition_Systems
  imports Main
begin
  
locale lts =
fixes
  trans :: "'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool" 
begin

abbreviation step_pred :: "'s \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool"  where
  "step_pred p af q \<equiv> \<exists> a. af a \<and> trans p a q"

abbreviation step :: 
  "'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool"
  ("_ \<longmapsto>_  _" [70, 70, 70] 80)
where
  "p \<longmapsto>a  q \<equiv> trans p a q"
  
inductive steps :: "'s \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool"
    ("_ \<longmapsto>* _  _" [70, 70, 70] 80)
where
  refl: "p \<longmapsto>* af p"
| step: "p \<longmapsto>* af q1 \<Longrightarrow> q1 \<longmapsto> a q \<Longrightarrow> af a \<Longrightarrow> (p \<longmapsto>* af q)"

lemma steps_one_step: 
  assumes
    "p \<longmapsto> a p'"
    "A a"
  shows
    "p \<longmapsto>* A p'"
using steps.step[of p A p a p'] steps.refl[of p A] assms .

lemma steps_left:
  assumes
    "p \<noteq> p'"
    "p \<longmapsto>* A p'"
  shows
    "\<exists>p'' a . p \<longmapsto> a p'' \<and> A a"
using assms(2,1) by (induct, auto)
  
lemma steps_no_step:
  assumes
    "\<And> a p' . p \<longmapsto> a p' \<Longrightarrow> \<not>A a"
    "p \<noteq> p''"
    "p \<longmapsto>* A p''"
  shows
    "False"
  using steps_left[OF assms(2,3)] assms(1) by blast
    
lemma steps_no_step_pos:
  assumes
    "\<And> a p' . p \<longmapsto> a p' \<Longrightarrow> \<not>A a"
    "p \<longmapsto>* A p'"
  shows
    "p = p'"
  using assms steps_no_step by blast
    
lemma steps_loop:
  assumes
    "\<And> a p' . p \<longmapsto> a p' \<Longrightarrow> p = p'"
    "p \<noteq> p''"
    "p \<longmapsto>* A p''"
  shows
    "False"
  using assms(3,1,2) by (induct, auto)
    
lemma steps_concat: 
  assumes
    "p' \<longmapsto>* A p''"
    "p \<longmapsto>* A p'"
  shows
    "p \<longmapsto>* A p''"
using assms proof (induct arbitrary: p)
  case (refl p'' A p')
  then show ?case by auto
next
  case (step p' A p'' a pp p)
  hence "p \<longmapsto>* A  p''" by simp
  show ?case using steps.step[OF `p \<longmapsto>* A  p''` step(3,4)] .
qed
  
lemma steps_spec: 
  assumes
    "p \<longmapsto>* A' p'"
    "\<And> a . A' a \<Longrightarrow> A a"
  shows
    "p \<longmapsto>* A p'"
using assms(1,2) proof induct
  case (refl p)
  show ?case using steps.refl .
next
  case (step p A' pp a pp')
  hence "p \<longmapsto>* A  pp" by simp 
  then show ?case using step(3,4,5) steps.step by auto
qed

text\<open>If one can reach only a finite portion of the graph following @{text "\<longmapsto>* A"},
  and all cycles are loops, then there must be nodes which are maximal wrt. \<open>\<longmapsto>* A\<close>.\<close>
lemma step_max_deadlock:
  fixes A q
  assumes
    "\<And> r1 r2. r1 \<longmapsto>* A r2 \<and> r2 \<longmapsto>* A r1 \<Longrightarrow> r1 = r2" \<comment>\<open>contracted cycles (anti-symmetry)\<close>
    "finite {q'. q \<longmapsto>* A q'}"
    "\<forall> q'. q \<longmapsto>* A q' \<longrightarrow> (\<exists>q''. q' \<longmapsto>* A q'' \<and> q' \<noteq> q'')"
  shows
    False
  using assms
  sorry \<comment>\<open>this should be easy to prove if i understood anything about \<open>finite\<close> in isabelle..\<close>
  
end \<comment>\<open>end of lts\<close>
  
lemma lts_impl_steps2:
  assumes
    "lts.steps step1 p1 ap p2"
    "\<And> p1 a p2 . step1 p1 a p2 \<and> P p1 a p2 \<Longrightarrow> step2 p1 a p2"
    "\<And> p1 a p2 . P p1 a p2"
  shows
    "lts.steps step2 p1 ap p2"
proof (induct rule: lts.steps.induct[OF assms(1)])
  case (1 p af)
  show ?case using lts.steps.refl[of step2 p af] by blast
next
  case (2 p af q1 a q)
  hence "step2 q1 a q" using assms(2,3) by blast
  thus ?case using lts.step[OF 2(2) _ 2(4)] by blast
qed 
  
lemma lts_impl_steps:
  assumes
    "lts.steps step1 p1 ap p2"
    "\<And> p1 a p2 . step1 p1 a p2 \<Longrightarrow> step2 p1 a p2"
  shows
    "lts.steps step2 p1 ap p2"
  using assms lts_impl_steps2[OF assms] by auto 
  
end