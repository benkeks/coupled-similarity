section \<open>Strong Simulation and Bisimulation\<close>

theory Strong_Relations
  imports Transition_Systems
begin

context lts
begin
  
definition simulation :: 
  "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
where
  "simulation R \<equiv> \<forall> p q. R p q \<longrightarrow> 
    (\<forall> p' a. p \<longmapsto> a p' \<longrightarrow> 
      (\<exists> q'. R p' q' \<and> (q \<longmapsto> a q')))"

definition simulation_on :: 
  "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's set \<Rightarrow> 's set \<Rightarrow> bool"
where
  "simulation_on R S1 S2 \<equiv> \<forall> p \<in> S1. \<forall> q \<in> S2. R p q \<longrightarrow> 
    (\<forall> p' \<in> S1 . \<forall> a . p \<longmapsto> a p' \<longrightarrow> 
      (\<exists> q' \<in> S2 . R p' q' \<and> (q \<longmapsto> a q')))"
  
  
definition bisimulation :: 
  "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
where
  "bisimulation R \<equiv> \<forall> p q. R p q \<longrightarrow> 
    (\<forall> p' a. p \<longmapsto> a p' \<longrightarrow> 
      (\<exists> q'. R p' q' \<and> (q \<longmapsto> a q'))) \<and>
    (\<forall> q' a. q \<longmapsto> a q' \<longrightarrow> 
      (\<exists> p'. R p' q' \<and> (p \<longmapsto> a p')))"
  
lemma bisim_ruleformat:
assumes "bisimulation R"
  and "R p q"
shows
  "p \<longmapsto> a p' \<Longrightarrow> (\<exists> q'. R p' q' \<and> (q \<longmapsto> a q'))"
  "q \<longmapsto> a q' \<Longrightarrow> (\<exists> p'. R p' q' \<and> (p \<longmapsto> a p'))"
  using assms unfolding bisimulation_def by auto
    
end --"context lts"

end
  