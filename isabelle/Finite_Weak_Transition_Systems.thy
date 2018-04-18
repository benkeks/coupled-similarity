theory Finite_Weak_Transition_Systems
  imports Weak_Transition_Systems
begin

section \<open>Finite transition systems with silent steps\<close>

locale lts_tau_finite = lts_tau trans \<tau> for
  trans :: "'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool" and
  \<tau> :: "'a" +
assumes 
 finite_state_set: "finite (top::'s set)"
begin

lemma finite_state_rel: "finite (top::('s rel))"
  using finite_state_set
  by (simp add: finite_prod)


end

end