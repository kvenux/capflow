theory CapFlow_v1
imports Dynamic_model_v1
begin

subsection {* Definitions *}

typedecl Message
type_synonym compartment_id = nat

type_synonym domain_id = nat
type_synonym domain_name = string

datatype
  right = TAINT
          |GRANT

record cap = 
  target :: compartment_id
  rights :: "right set"

record domain = 
  id_of_domain :: domain_id
  cap_config :: "cap set"

datatype Domain_Conf = DomainConf domain_id domain_name

type_synonym Domains = "domain_id \<rightharpoonup> Domain_Conf"

record 't State = 
  domains :: "domain set"
  next_comp_id :: compartment_id
  st :: 't
  

record Sys_Config = 
  domain_conf :: Domains

consts sysconf :: "Sys_Config" 

consts init_st :: "'t"

definition system_init :: "Sys_Config \<Rightarrow> 't State"
  where "system_init sc \<equiv> \<lparr>domains = {},
                           next_comp_id = 0,
                           st = init_st\<rparr>"

consts s0t :: "'t State"
definition s0t_witness :: "'t State"
  where "s0t_witness \<equiv> system_init sysconf"
specification (s0t) 
  s0t_init: "s0t = system_init sysconf"
  by simp

subsection {* Events *}

datatype Event = Create_Cap domain_id
                   |Grant_Cap domain_id domain_id cap
                   |Get_Taint_Cap_Set domain_id
                   |Get_Caps domain_id
                   |Send_Message domain_id domain_id Message

definition domain_id_is_valid :: "'t State \<Rightarrow> domain_id \<Rightarrow> bool" where
  "domain_id_is_valid s domain_id  \<equiv>
          (if (\<exists>d. d \<in> (domains s) \<and> id_of_domain d = domain_id )
          then True
          else False)
          "

definition get_domain :: "'t State \<Rightarrow> domain_id \<Rightarrow> domain option" where
  "get_domain s domain_id  \<equiv>
          (if (\<exists>d. d \<in> (domains s) \<and> id_of_domain d = domain_id )
          then Some (SOME d. d \<in> (domains s) \<and> id_of_domain d = domain_id)
          else None)   
          "

definition get_domain2 :: "'t State \<Rightarrow> domain_id \<Rightarrow> ('t State \<times> domain option)" where
  "get_domain2 s domain_id  \<equiv>
          (if (\<exists>d. d \<in> (domains s) \<and> id_of_domain d = domain_id )
          then (s, get_domain s domain_id)
          else (s, None)               
          )"

definition create_tag_add_new_caps_to_domain :: "domain \<Rightarrow> cap set \<Rightarrow> domain" where
  "create_tag_add_new_caps_to_domain d cs \<equiv> 
          \<lparr> id_of_domain = id_of_domain d,
            cap_config = cs \<union> (cap_config d)\<rparr>"

definition create_tag_add_new_caps_to_domain_1 :: "'t State \<Rightarrow> domain_id \<Rightarrow> cap set \<Rightarrow> domain" where
  "create_tag_add_new_caps_to_domain_1 s d_id cs \<equiv> 
          let d = the (get_domain s d_id)
          in
          \<lparr> id_of_domain = id_of_domain d,
            cap_config = cs \<union> (cap_config d)\<rparr>"

definition create_tag_state_trans :: "'t State \<Rightarrow> domain_id \<Rightarrow> 't State" where
  "create_tag_state_trans s d_id \<equiv> 
          let rest_domains = {v. v\<in>domains s \<and> \<not> (id_of_domain v = d_id) };
              new_add_cap =  \<lparr> target = next_comp_id s,
                             rights = {TAINT} \<rparr>;
              new_domain = create_tag_add_new_caps_to_domain_1 s d_id {new_add_cap}
          in
           \<lparr> domains = insert new_domain rest_domains,
             next_comp_id = next_comp_id s + 1,
             st = st s\<rparr>"

definition create_tag :: "'t State \<Rightarrow> domain_id \<Rightarrow> ('t State \<times> cap option) " where
  "create_tag s d_id \<equiv>
          if( domain_id_is_valid s d_id )
          then
            let rest_domains = {v. v\<in>domains s \<and> \<not> (id_of_domain v = d_id) };
                new_add_cap =  \<lparr> target = next_comp_id s,
                               rights = {TAINT,GRANT} \<rparr>;
                new_domain = create_tag_add_new_caps_to_domain_1 s d_id {new_add_cap}
            in (\<lparr> domains = insert new_domain rest_domains,
                  next_comp_id = next_comp_id s + 1,
                  st = st s \<rparr> , Some new_add_cap)
          else
            (s, None)
          "

definition get_caps0 :: "'t State \<Rightarrow> domain_id \<Rightarrow> (cap set) option " where
"get_caps0 s domain_id \<equiv>
          (if (\<exists>d. d \<in> (domains s) \<and> id_of_domain d = domain_id )
          then Some (SOME cap. \<exists>d. d \<in> (domains s) \<and> id_of_domain d = domain_id \<and> cap = cap_config d)
          else None
          )"

definition get_caps :: "'t State \<Rightarrow> domain_id \<Rightarrow> ('t State \<times> (cap set) option) " where
  "get_caps s domain_id \<equiv>
          (if (\<exists>d. d \<in> (domains s) \<and> id_of_domain d = domain_id )
          then (s, Some (SOME cap. \<exists>d. d \<in> (domains s) \<and> id_of_domain d = domain_id \<and> cap = cap_config d))
          else (s, None)                             
          )"

definition get_taint_cap_set0 :: "'t State \<Rightarrow> domain_id \<Rightarrow> (cap set) option " where
  "get_taint_cap_set0 s d_id \<equiv>
          (if ((get_domain s d_id) \<noteq> None )
            then 
              let
                dom = the (get_domain s d_id);
                cap_set = the (get_caps0 s d_id)
              in
                Some ({cap. cap \<in> cap_set \<and> TAINT \<in> rights cap})
            else None   
            )"

definition get_taint_cap_set :: "'t State \<Rightarrow> domain_id \<Rightarrow> ('t State \<times>  (cap set) option) " where
  "get_taint_cap_set s d_id \<equiv>
          (if ((get_domain s d_id) \<noteq> None )
            then 
              let
                dom = the (get_domain s d_id);
                cap_set = the (get_caps0 s d_id)
              in
                (s, Some ({cap. cap \<in> cap_set \<and> TAINT \<in> rights cap}))
            else (s, None)
            )"

definition grant_cap_is_valid :: "'t State \<Rightarrow> domain_id \<Rightarrow> domain_id \<Rightarrow> cap \<Rightarrow> bool" where 
  "grant_cap_is_valid s d_id dst_id cap \<equiv> True"

definition grant_cap :: "'t State \<Rightarrow> domain_id \<Rightarrow> domain_id \<Rightarrow> cap \<Rightarrow> 't State" where
  "grant_cap s d_id dst_id cap \<equiv> 
          let rest_domains = {v. v\<in>domains s \<and> \<not> (id_of_domain v = d_id) };
              newly_granted_cap =  \<lparr> target = target cap,
                             rights = {TAINT} \<rparr>;
              new_domain = create_tag_add_new_caps_to_domain_1 s d_id {newly_granted_cap}
          in
           \<lparr> domains = insert new_domain rest_domains,
             next_comp_id = next_comp_id s,
             st = st s \<rparr>
            "

definition send_message :: "'t State \<Rightarrow> domain_id \<Rightarrow> domain_id \<Rightarrow> Message \<Rightarrow> 't State"
  where
  "send_message s src_id dst_id m \<equiv>
        s
        "

definition exec_event :: "'t State \<Rightarrow> Event \<Rightarrow> 't State" where
  "exec_event s e  \<equiv>
    case e of  Create_Cap d_id \<Rightarrow> fst (create_tag s d_id)
               |Grant_Cap d_id dst_id cap \<Rightarrow> grant_cap  s d_id dst_id cap
               |Get_Taint_Cap_Set d_id \<Rightarrow> fst (get_taint_cap_set s d_id)
               |Get_Caps d_id \<Rightarrow> fst (get_caps s d_id)
               |Send_Message src_id dst_id msg \<Rightarrow> s
               "


definition domain_of_event :: "Event \<Rightarrow> domain_id option"
  where
    "domain_of_event e \<equiv> 
       case e of  Create_Cap d_id \<Rightarrow> Some d_id
                 |Grant_Cap d_id dst_id cap \<Rightarrow> Some d_id
                 |Get_Taint_Cap_Set d_id \<Rightarrow> Some d_id
                 |Get_Caps d_id \<Rightarrow> Some d_id
                 |Send_Message src_id dst_id msg \<Rightarrow> Some src_id
                 "

definition grant_dest_of_event :: "Event \<Rightarrow> domain_id option"
 where
    "grant_dest_of_event e \<equiv> 
       case e of  Create_Cap d_id \<Rightarrow> Some d_id
                 |Grant_Cap d_id dst_id cap \<Rightarrow> Some dst_id
                 |Get_Taint_Cap_Set d_id \<Rightarrow> None
                 |Get_Caps d_id \<Rightarrow> None
                 |Send_Message src_id dst_id msg \<Rightarrow> None
                 "                                            
definition is_execute1 :: "Event \<Rightarrow> bool"
  where
    "is_execute1 e \<equiv> 
          case e of   Create_Cap d_id \<Rightarrow> False
                 |Grant_Cap d_id dst_id cap \<Rightarrow> False
                 |Get_Taint_Cap_Set d_id \<Rightarrow> True
                 |Get_Caps d_id \<Rightarrow> True
                 |Send_Message src_id dst_id msg \<Rightarrow> True
                 "

definition is_grant1 :: "Event \<Rightarrow> bool"
  where
    "is_grant1 e \<equiv> \<not>is_execute1 e"

definition get_t_set :: "'t State \<Rightarrow> domain_id \<Rightarrow> (cap set) " where
  "get_t_set s d_id \<equiv>
          (if ((get_domain s d_id) \<noteq> None )
            then 
              let
                dom = the (get_domain s d_id);
                cap_set = cap_config dom
              in
                {cap. cap \<in> cap_set \<and> TAINT \<in> rights cap}
            else {}
            )"


definition vpeq1 :: "'t State \<Rightarrow> domain_id \<Rightarrow> 't State \<Rightarrow> bool"
  where
    "vpeq1 s d t \<equiv> 
        let
          d1 = get_domain s d;
          d2 = get_domain t d
        in
          if(d1 = d2)
          then
            True
          else
            False
          "

lemma vpeq1_transitive_lemma : "\<forall> s t r d. (vpeq1 s d t) \<and> (vpeq1 t d r) \<longrightarrow> (vpeq1 s d r)"
  by (simp add: vpeq1_def)

lemma vpeq1_symmetric_lemma : "\<forall> s t d. (vpeq1 s d t) \<longrightarrow> (vpeq1 t d s)"
  by (simp add: vpeq1_def)

lemma vpeq1_reflexive_lemma : "\<forall> s d. (vpeq1 s d s)"
  by (simp add: vpeq1_def)

lemma execute_exclusive1 :  "\<forall>a. is_execute1 a  \<longleftrightarrow> \<not>(is_grant1 a)"
  using is_grant1_def by auto

lemma grant_exclusive1: "\<forall>a. is_grant1 a   \<longleftrightarrow> \<not>(is_execute1 a)"
  using is_grant1_def by auto

lemma vpeq1_domain_eq_lemma : "\<forall>s t d. vpeq1 s d t \<longrightarrow> get_domain s d = get_domain t d"
  by (simp add: vpeq1_def)

lemma taint_set_respect_lemma1: "\<forall>s t d. vpeq1 s d t \<longrightarrow> get_t_set s d = get_t_set t d"
  by (simp add: get_t_set_def vpeq1_domain_eq_lemma)

lemma reachable_top: "\<forall> s a. (SM.reachable0 s0t exec_event) s \<longrightarrow> (\<exists>s'. s' = exec_event s a)"
  proof -
  {
    fix s a
    assume p0: "(SM.reachable0 s0t exec_event) s"
    have "(\<exists>s'. s' = exec_event s a)"
      proof (induct a)
        case (Create_Cap x) show ?case
          apply (induct x)
          by (simp add: exec_event_def) +
        next
        case (Grant_Cap x1a x2 x3a) show ?case
          apply (induct x1a)
          by (simp add: exec_event_def) +
        next
        case (Get_Taint_Cap_Set x) show ?case
          apply (induct x)
          by (simp add: exec_event_def) +
        next
        case (Get_Caps x) show ?case
          apply (induct x)
          by (simp add: exec_event_def) +
        next
        case (Send_Message x1a x2 x3a) show ?case
          apply (induct x1a)
          by (simp add: exec_event_def) +
      qed
    }
  then show ?thesis by auto
  qed

interpretation SM_enabled 
    s0t is_execute1 is_grant1 exec_event domain_of_event grant_dest_of_event get_t_set vpeq1
    using vpeq1_transitive_lemma vpeq1_symmetric_lemma vpeq1_reflexive_lemma
          grant_exclusive1 execute_exclusive1 taint_set_respect_lemma1 reachable_top
          s0t_init
          SM.intro[of vpeq1 is_execute1 is_grant1 get_t_set]
          SM_enabled_axioms.intro[of s0t exec_event]
          SM_enabled.intro[of is_execute1 is_grant1 get_t_set vpeq1 s0t exec_event] by blast1
(*
by1 (smt SM.intro SM_enabled.intro SM_enabled_axioms.intro grant_exclusive1 s0t_init taint_set_respect_lemma1 vpeq1_def vpeq1_symmetric_lemma)
*)
end