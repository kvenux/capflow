theory DynamicSecurityModel_v1
imports Main
begin
subsection {* Security State Machine *}

datatype
  right = Taint
          |Endorse
          |Grant
          |Declassify
          |Export

record 'r cap = 
  target :: "'r"
  rights :: "right set"

record 'r cap_conf = conf :: "'r cap set"

datatype domain_id = nat

record 't state = s::'t 
                  c::"(domain_id \<times> domain_id ) set"


locale SM =
  fixes s0 :: 's
  fixes policy_config :: "'s \<Rightarrow> ('d \<times> 'd) set"
  fixes is_normal_step :: "'e \<Rightarrow> bool"
  fixes is_policy_config_step :: "'e \<Rightarrow> bool"
  fixes step :: "'s \<Rightarrow> 'e \<Rightarrow> 's"

    

end