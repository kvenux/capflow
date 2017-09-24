theory CapFlow
imports Dynamic_model
begin

subsection {* Definitions *}

type_synonym max_buffer_size = nat
type_synonym buffer_size = nat
typedecl Message
typedecl Endpoint
typedecl Domain

type_synonym domain_id = nat
type_synonym domain_name = string

type_synonym endpoint_name = string
type_synonym endpoint_id = nat

datatype
  right = SEND
          |TAKE
          |GRANT
          |REMOVE

record cap =  target :: domain_id
              rights :: "right set"    

record Endpoint_Concig = 
  e_max_buf_size :: "endpoint_id \<rightharpoonup> max_buffer_size"
  e_name :: "endpoint_id \<rightharpoonup> endpoint_name"
  e_listener :: "endpoint_id \<rightharpoonup> domain_id"
  
record Domain_Config =                          
  d_name :: "domain_id \<rightharpoonup> domain_name"
  d_ep_set :: "domain_id \<Rightarrow> endpoint_id set"

record Sys_Config = 
  domconf :: Domain_Config
  commconf :: Endpoint_Concig

subsubsection {* System state *}

record State =  
  (*caps :: "domain_id \<Rightarrow> domain_id \<Rightarrow> right set"*)
  caps :: "domain_id \<Rightarrow> cap set"           
  e_msgs ::  "endpoint_id \<Rightarrow> Message set"
  e_buf_size :: "endpoint_id \<rightharpoonup> buffer_size"
  domain_endpoint :: "endpoint_id \<rightharpoonup> domain_id "

datatype Event = Client_Lookup_Endpoint_Name domain_id endpoint_name
               | Send_Queuing_Message domain_id endpoint_id Message
               | Receive_Queuing_Message domain_id endpoint_id
               | Get_My_Endpoints_Set domain_id
               | Get_Caps domain_id
               | Grant_Endpoint_Cap domain_id cap cap
               | Remove_Cap_Right domain_id cap right

subsubsection {* Utility Functions used for Event Specification *} 

definition get_domain_name_from_domain_id :: "Sys_Config \<Rightarrow> domain_id \<Rightarrow> domain_name option"
  where "get_domain_name_from_domain_id sc did \<equiv> 
            let
              dm_conf = (domconf sc)
            in
            if((d_name dm_conf) did \<noteq> None )
            then
              ((d_name dm_conf) did )
            else
              None"

definition get_endpoints_from_domain_id :: "Sys_Config \<Rightarrow> domain_id \<Rightarrow> endpoint_id set"
  where "get_endpoints_from_domain_id sc did \<equiv> 
            let
              dm_conf = (domconf sc)
            in
            if((d_name dm_conf) did \<noteq> None )
            then
              ((d_ep_set dm_conf) did )
            else
              {}"

definition get_domain_id_from_domain_name :: "Sys_Config \<Rightarrow> domain_name \<Rightarrow> domain_id option"
  where "get_domain_id_from_domain_name sc dname \<equiv> 
            let
              dm_conf = (domconf sc)           
            in
            if(\<exists>did. the((d_name dm_conf) did) = dname )
            then
              Some (SOME did. the((d_name dm_conf) did) = dname)
            else
              None"

definition get_listener_id_from_endpoint_id :: "Sys_Config \<Rightarrow> endpoint_id \<Rightarrow> domain_id option"
  where "get_listener_id_from_endpoint_id sc eid \<equiv> 
            let
              ep_conf = (commconf sc)
            in
            if((e_listener ep_conf) eid \<noteq> None )
            then
              ((e_listener ep_conf) eid )
            else
              None"

definition get_endpoint_name_from_endpoint_id :: "Sys_Config \<Rightarrow> endpoint_id \<Rightarrow> endpoint_name option"
  where "get_endpoint_name_from_endpoint_id sc eid \<equiv> 
            let
              ep_conf = (commconf sc)
            in                                   
            if((e_name ep_conf) eid \<noteq> None )
            then
              ((e_name ep_conf) eid )
            else
              None"

definition get_endpoint_id_from_endpoint_name :: "Sys_Config \<Rightarrow> endpoint_name \<Rightarrow> endpoint_id option"
  where "get_endpoint_id_from_endpoint_name sc ename \<equiv> 
            let
              ep_conf = (commconf sc)
            in                  
            if(\<exists>eid. the((e_name ep_conf) eid) = ename )
            then
              Some (SOME eid. the((e_name ep_conf) eid) = ename )
            else
              None"

definition get_endpoint_max_bufsize_from_sc_by_id :: "Sys_Config \<Rightarrow> endpoint_id \<Rightarrow> max_buffer_size option"
  where "get_endpoint_max_bufsize_from_sc_by_id sc eid \<equiv> 
            let
              ep_conf = (commconf sc)
            in
            if((e_max_buf_size ep_conf) eid \<noteq> None )
            then
              ((e_max_buf_size ep_conf) eid )
            else
              None"

definition is_a_domain :: "Sys_Config \<Rightarrow> domain_id \<Rightarrow> bool"
  where "is_a_domain sc did \<equiv> 
            let
              dm_conf = (domconf sc)
            in
            if((d_name dm_conf) did \<noteq> None )
            then
              True
            else
              False"

definition is_an_endpoint :: "Sys_Config \<Rightarrow> endpoint_id \<Rightarrow> bool"
  where "is_an_endpoint sc eid \<equiv> 
            let
              ep_conf = (commconf sc)
            in
            if((e_name ep_conf) eid \<noteq> None )
            then
              True
            else
              False"

definition is_an_endpoint_of_domain :: "Sys_Config \<Rightarrow> endpoint_id \<Rightarrow> domain_id \<Rightarrow> bool"
  where "is_an_endpoint_of_domain sc eid did \<equiv> 
            let
              dm_conf = (domconf sc) 
            in
            if(eid \<in> ((d_ep_set dm_conf) did))
            then
              True
            else
              False"

definition is_an_endpoint_of_listener :: "Sys_Config \<Rightarrow> endpoint_id \<Rightarrow> domain_id \<Rightarrow> bool"
  where "is_an_endpoint_of_listener sc eid did \<equiv> 
            let
              ep_conf = (commconf sc)
            in
            if(the((e_listener ep_conf) eid) = did )
            then                                
              True                              
            else
              False"

definition get_domain_cap_set_from_domain_id :: "State \<Rightarrow> domain_id \<Rightarrow> cap set"
  where "get_domain_cap_set_from_domain_id s did  \<equiv> 
            let
              cap_by_id = caps s
            in
              cap_by_id did
              "

definition get_msg_set_from_endpoint_id :: "State \<Rightarrow> endpoint_id \<Rightarrow> Message set"
  where "get_msg_set_from_endpoint_id s eid  \<equiv> 
            let
              msg_by_id = e_msgs s
            in
              msg_by_id eid
              "

definition get_buf_size_from_endpoint_id :: "State \<Rightarrow> endpoint_id \<Rightarrow> buffer_size option"
  where "get_buf_size_from_endpoint_id s eid  \<equiv> 
            let
              buf_size_by_id = e_buf_size s
            in
              buf_size_by_id eid
              "

definition endpoint_is_full :: "Sys_Config \<Rightarrow> State \<Rightarrow> endpoint_id \<Rightarrow> bool"
  where "endpoint_is_full sc s eid \<equiv> 
            get_buf_size_from_endpoint_id s eid 
               = get_endpoint_max_bufsize_from_sc_by_id sc eid"

definition get_endpoints_of_domain :: "State \<Rightarrow> domain_id \<Rightarrow> endpoint_id set"
  where "get_endpoints_of_domain s did \<equiv> 
            let
              dom_ep = domain_endpoint s
            in
              {x. dom_ep x = Some did}
              "

definition get_domain_id_from_endpoint :: "State \<Rightarrow> endpoint_id \<Rightarrow> domain_id option"
  where "get_domain_id_from_endpoint s eid \<equiv> 
            let
              dom_ep = domain_endpoint s
            in
              dom_ep eid
              "

definition get_endpoint_msg_set_of_domain :: "State \<Rightarrow> domain_id \<Rightarrow> Message set"
  where "get_endpoint_msg_set_of_domain s did \<equiv> 
            let
              dom_ep = domain_endpoint s;
              eid_set = get_endpoints_of_domain s did;
              msg_of_ep = e_msgs s
            in
                {x. \<exists>e. e\<in>eid_set \<and> x \<in> msg_of_ep e}
              " 

definition interferes :: "domain_id \<Rightarrow> State \<Rightarrow> domain_id \<Rightarrow> bool"
  where "interferes w s v \<equiv> 
        if( w = v
            \<or> (\<exists>c. c\<in>(get_domain_cap_set_from_domain_id s w) \<and> target c = v))
        then
          True
        else
          False
        "

subsubsection{* Event specification *}

definition client_lookup_endpoint_name :: "Sys_Config \<Rightarrow> State 
              \<Rightarrow> domain_id \<Rightarrow> endpoint_name \<Rightarrow> (State \<times> endpoint_id option)" 
  where "client_lookup_endpoint_name sc s did ename \<equiv> 
            if(get_endpoint_id_from_endpoint_name sc ename \<noteq> None)
            then
              (s, get_endpoint_id_from_endpoint_name sc ename)
            else
              (s, None)"

definition send_queuing_message :: "State \<Rightarrow> domain_id \<Rightarrow> endpoint_id \<Rightarrow> Message \<Rightarrow> (State \<times> bool)"
  where "send_queuing_message s did eid m \<equiv>
            let
              dom_ep = domain_endpoint s;
              dst_dom = dom_ep eid;
              emsgs = e_msgs s;
              msg_set = get_msg_set_from_endpoint_id s eid;
              new_msg_set = insert m msg_set
            in
            if(get_domain_id_from_endpoint s eid \<noteq> None 
               \<and> interferes did s (the (get_domain_id_from_endpoint s eid)))
            then
              (s\<lparr>
                  e_msgs := emsgs(eid := new_msg_set)
                \<rparr>, False)                                       
            else                                                   
              (s, False)"

definition receive_queuing_message :: "State \<Rightarrow> domain_id \<Rightarrow> endpoint_id \<Rightarrow> (State \<times> Message option)"
  where "receive_queuing_message s did eid \<equiv> 
            if(get_domain_id_from_endpoint s eid = Some did)
            then
              let
                emsgs = e_msgs s;
                msg_set = get_msg_set_from_endpoint_id s eid;
                m = SOME x. x\<in>msg_set;
                new_msg_set = msg_set - {m}               
              in                                             
                (s\<lparr>
                    e_msgs := emsgs(eid := new_msg_set)
                  \<rparr>, Some m)
            else
              (s, None)
            "

definition get_my_endpoints_set :: "State \<Rightarrow> domain_id \<Rightarrow> (State \<times> endpoint_id set)"
  where "get_my_endpoints_set s did \<equiv> 
            if(get_endpoints_of_domain s did \<noteq> {})
            then
              (s, get_endpoints_of_domain s did)
            else
              (s, {})
            "

definition get_caps :: "State \<Rightarrow> domain_id \<Rightarrow> (State \<times> cap set)"
  where "get_caps s did \<equiv> 
            (s, get_domain_cap_set_from_domain_id s did)"

definition grant_endpoint_cap :: "State \<Rightarrow> domain_id \<Rightarrow> cap \<Rightarrow> cap \<Rightarrow> (State \<times> bool)"
  where "grant_endpoint_cap s did grant_cap dst_cap \<equiv> 
            if(grant_cap\<in>get_domain_cap_set_from_domain_id s did 
              \<and> GRANT\<in>rights grant_cap
              \<and> target grant_cap \<noteq> target dst_cap
              \<and> dst_cap\<in>get_domain_cap_set_from_domain_id s did)
           then                                                                        
             let                                                     
               did_dst = target grant_cap;
               caps0 = caps s;
               cs_dst = get_domain_cap_set_from_domain_id s did_dst  
             in
             (s\<lparr>
                caps := caps0(did_dst := (insert dst_cap cs_dst))
               \<rparr>, True)    
           else
             (s, False)"

definition get_takable_caps :: "State \<Rightarrow> domain_id \<Rightarrow> cap \<Rightarrow> (State \<times> cap set)"
  where "get_takable_caps s did take_cap \<equiv>
            if(take_cap \<in> get_domain_cap_set_from_domain_id s did 
              \<and> TAKE \<in> rights take_cap)
            then
              let
                did_dst = target take_cap
              in
              (s, get_domain_cap_set_from_domain_id s did_dst)
            else
              (s, {})"

definition take_endpoint_cap :: "State \<Rightarrow> domain_id \<Rightarrow> cap \<Rightarrow> cap \<Rightarrow> (State \<times> bool)"
  where "take_endpoint_cap s did take_cap dst_cap \<equiv> 
            if(take_cap \<in>  get_domain_cap_set_from_domain_id s did 
              \<and> TAKE \<in> rights take_cap 
              \<and> interferes did s (target dst_cap)
              \<and> dst_cap \<in> get_domain_cap_set_from_domain_id s (target take_cap))
            then
              let                                                     
                caps0 = caps s;
                cs_dst = get_domain_cap_set_from_domain_id s did  
              in
              (s\<lparr>
                 caps := caps0(did := (insert dst_cap cs_dst))
                \<rparr>, True)
            else
              (s, False)"

definition remove_cap_right :: "State \<Rightarrow> domain_id \<Rightarrow> cap \<Rightarrow> right \<Rightarrow> (State \<times> bool)"
  where "remove_cap_right s did rm_cap right_to_rm \<equiv> 
            let
              caps0 = caps s;
              cs_dst = get_domain_cap_set_from_domain_id s did;
              cs_rest = {c. c\<in>cs_dst \<and> c\<noteq>rm_cap}
            in
            if(rm_cap \<in>  get_domain_cap_set_from_domain_id s did 
              \<and> REMOVE \<in> rights rm_cap
              \<and> right_to_rm \<in> rights rm_cap
              \<and> REMOVE = right_to_rm
              \<and> {REMOVE} = rights rm_cap)
            then
              (s\<lparr>
                 caps := caps0(did := (cs_rest))
                \<rparr>, True)
            else if(
              rm_cap \<in>  get_domain_cap_set_from_domain_id s did 
              \<and> REMOVE \<in> rights rm_cap
              \<and> right_to_rm \<in> rights rm_cap
              )
            then
              let
                new_cap = \<lparr> target = target rm_cap,
                            rights = (rights rm_cap) - {right_to_rm}\<rparr>
              in
              (s\<lparr>
                 caps := caps0(did := (insert new_cap cs_rest))
                \<rparr>, True)
            else
              (s, False)"

definition system_init :: "Sys_Config \<Rightarrow> State"
  where "system_init sc \<equiv> \<lparr>
                            caps = (\<lambda> x. {}),
                            e_msgs = (\<lambda> x. {}),
                            e_buf_size = (\<lambda> x. None),
                            domain_endpoint = e_listener(commconf sc)
                           \<rparr>"  

subsubsection{* Instantiation and Its Proofs of Security Model  *}

consts sysconf :: "Sys_Config" 
definition sys_config_witness :: Sys_Config 
  where 
    "sys_config_witness \<equiv> \<lparr>
                            domconf  = \<lparr> 
                                         d_name = (\<lambda> x. None),
                                         d_ep_set = (\<lambda> x. {})
                                       \<rparr> , 
                            commconf = \<lparr> 
                                         e_max_buf_size = (\<lambda> x. None),
                                         e_name = (\<lambda> x. None),
                                         e_listener = (\<lambda> x. None)
                                       \<rparr>                       
                            \<rparr>" 


consts s0t :: State
definition s0t_witness :: State
  where "s0t_witness \<equiv> system_init sysconf"
specification (s0t) 
  s0t_init: "s0t = system_init sysconf"
  by simp

definition exec_event :: "State \<Rightarrow> Event \<Rightarrow> State" 
  where "exec_event s e  \<equiv>
    case e of  Client_Lookup_Endpoint_Name did ename \<Rightarrow> fst (client_lookup_endpoint_name sysconf s did ename)
             | Send_Queuing_Message did eid m \<Rightarrow> fst (send_queuing_message s did eid m)
             | Receive_Queuing_Message did eid \<Rightarrow> fst (receive_queuing_message s did eid)
             | Get_My_Endpoints_Set did \<Rightarrow> fst (get_my_endpoints_set s did)
             | Get_Caps did \<Rightarrow>fst (get_caps s did)
             | Grant_Endpoint_Cap did grant_cap dst_cap \<Rightarrow> fst (grant_endpoint_cap s did grant_cap dst_cap)
             | Remove_Cap_Right did dst_cap right_to_rm \<Rightarrow> fst (remove_cap_right s did dst_cap right_to_rm)
              "

definition domain_of_event :: "Event \<Rightarrow> domain_id option"
  where "domain_of_event e \<equiv> 
    case e of  Client_Lookup_Endpoint_Name did ename \<Rightarrow> Some did
             | Send_Queuing_Message did eid m \<Rightarrow> Some did
             | Receive_Queuing_Message did eid \<Rightarrow> Some did
             | Get_My_Endpoints_Set did \<Rightarrow> Some did
             | Get_Caps did \<Rightarrow> Some did
             | Grant_Endpoint_Cap did grant_cap dst_cap \<Rightarrow> Some did
             | Remove_Cap_Right did dst_cap right_to_rm  \<Rightarrow> Some did
              "

definition vpeq1 :: "State \<Rightarrow> domain_id \<Rightarrow> State \<Rightarrow> bool" ("(_ \<sim> _ \<sim> _)") 
  where
    "vpeq1 s d t \<equiv> 
       let
         cs1 = get_domain_cap_set_from_domain_id s d;
         cs2 = get_domain_cap_set_from_domain_id t d;
         dom_eps1 = get_endpoints_of_domain s d;
         dom_eps2 = get_endpoints_of_domain t d
       in
       if(cs1 = cs2
          \<and> (\<forall>v. interferes v s d \<longleftrightarrow> interferes v t d)
          \<and> dom_eps1 = dom_eps2
          \<and> (\<forall>ep. ep\<in>dom_eps1 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id t ep )
            )
       then
         True
       else
         False
       "

declare vpeq1_def [cong]



lemma vpeq1_transitive_lemma : "\<forall> s t r d. (vpeq1 s d t) \<and> (vpeq1 t d r) \<longrightarrow> (vpeq1 s d r)"
  using vpeq1_def by auto

lemma vpeq1_symmetric_lemma : "\<forall> s t d. (vpeq1 s d t) \<longrightarrow> (vpeq1 t d s)"
  using vpeq1_def by auto

lemma vpeq1_reflexive_lemma : "\<forall> s d. (vpeq1 s d s)"
  using vpeq1_def by auto

lemma interf_reflexive_lemma : "\<forall>d s. interferes d s d" 
  using interferes_def by auto

lemma policy_respect_lemma : "\<forall>v u s t. (s \<sim> u \<sim> t)
                              \<longrightarrow> (interferes v s u = interferes v t u)"
  using vpeq1_def by auto

lemma reachable_top: "\<forall> s a. (SM.reachable0 s0t exec_event) s \<longrightarrow> (\<exists>s'. s' = exec_event s a)"
  proof -
  {
    fix s a
    assume p0: "(SM.reachable0 s0t exec_event) s"
    have "(\<exists>s'. s' = exec_event s a)"
      proof (induct a)
        case (Client_Lookup_Endpoint_Name x) show ?case
          apply (induct x)
          by (simp add: exec_event_def) +
        next
        case (Send_Queuing_Message x1a x2 x3a) show ?case
          apply (induct x1a)
          by (simp add: exec_event_def) +
        next
        case (Receive_Queuing_Message x) show ?case
          apply (induct x)
          by (simp add: exec_event_def) +
        next
        case (Get_My_Endpoints_Set x) show ?case
          apply (induct x)
          by (simp add: exec_event_def) +
        next
        case (Get_Caps x ) show ?case
          apply (induct x)
          by (simp add: exec_event_def) +
        case (Grant_Endpoint_Cap x1a x2 x3a ) show ?case
          apply (induct x1a)
          by (simp add: exec_event_def) +
        case (Remove_Cap_Right x1a x2 ) show ?case
          apply (induct x1a)
          by (simp add: exec_event_def) +
      qed
    }
  then show ?thesis by auto
  qed

declare  Let_def [cong] and vpeq1_def[cong]

interpretation SM_enabled 
    s0t exec_event domain_of_event vpeq1 interferes 
    using vpeq1_transitive_lemma vpeq1_symmetric_lemma vpeq1_reflexive_lemma
          interf_reflexive_lemma policy_respect_lemma reachable_top
          SM.intro[of vpeq1 interferes]
          SM_enabled_axioms.intro[of s0t exec_event]
          SM_enabled.intro[of vpeq1 interferes s0t exec_event] by blast

subsection{* Some lemmas of security proofs *}

subsection{* Concrete unwinding condition of "local respect" *}

subsubsection{*proving "client lookup endpoint name" satisfying the "local respect" property*}

  lemma client_lookup_endpoint_name_lcl_resp:
  assumes p0: "reachable0 s"
    and   p1: "\<not>(interferes did s d)"
    and   p2: "s' = fst (client_lookup_endpoint_name sysconf s did ename)"
  shows   "s \<sim> d \<sim> s'"
  proof -
  {
    have a1: "s = s'"
      by (simp add: p2 client_lookup_endpoint_name_def p1)
  }
  then show ?thesis by auto
  qed

  lemma client_lookup_endpoint_name_lcl_resp_e:
  assumes p0: "reachable0 s"
    and   p1: "a = (Client_Lookup_Endpoint_Name did ename)"
    and   p2: "\<not>(interferes (the (domain_of_event a)) s d)"
    and   p3: "s' = exec_event s a"
  shows   "s \<sim> d \<sim> s'"
  proof -
  {
    have a0: "(the (domain_of_event a)) = did"
      using p1 domain_of_event_def by auto
    have a1: "s' = fst (client_lookup_endpoint_name sysconf s did ename)"
      using p1 p3 exec_event_def by auto
    have a2: "\<not>(interferes did s d)"
      using p2 a0 by auto
    have a3: "s \<sim> d \<sim> s'"
      using a1 a2 p0 client_lookup_endpoint_name_lcl_resp by blast
  }
  then show ?thesis by auto
  qed

  lemma client_lookup_endpoint_name_lcrsp_e: "dynamic_local_respect_e (Client_Lookup_Endpoint_Name did ename)"
  proof -
    { 
      have "\<forall>d s. reachable0 s 
            \<and> \<not>(interferes (the (domain_of_event (Client_Lookup_Endpoint_Name did ename))) s d) 
            \<longrightarrow> (s \<sim> d \<sim> (exec_event s (Client_Lookup_Endpoint_Name did ename)))"
        proof -
        {
          fix d s
          assume p1: "reachable0 s "
          assume p2: " \<not>(interferes (the (domain_of_event (Client_Lookup_Endpoint_Name did ename))) s d)"
          have "(s \<sim> d \<sim> (exec_event s (Client_Lookup_Endpoint_Name did ename)))"
            using p1 p2 client_lookup_endpoint_name_lcl_resp_e by blast
        }
        then show ?thesis by blast
        qed
      }
    then show ?thesis 
      using dynamic_local_respect_e_def by blast
  qed
                                            
subsubsection{*proving "send queuing message" satisfying the "local respect" property*}

  lemma send_queuing_message_notchg_domain_cap_set:
  assumes p0: "reachable0 s"
    and   p1: "\<not>(interferes did s d)"
    and   p2: "s' = fst (send_queuing_message s did eid m)"
  shows   "get_domain_cap_set_from_domain_id s d 
           = get_domain_cap_set_from_domain_id s' d"
  proof (cases "(get_domain_id_from_endpoint s eid \<noteq> None 
               \<and> interferes did s (the (get_domain_id_from_endpoint s eid)))")
    assume b0: "(get_domain_id_from_endpoint s eid \<noteq> None 
           \<and> interferes did s (the (get_domain_id_from_endpoint s eid)))"
    have b1: "get_domain_cap_set_from_domain_id s d 
           = get_domain_cap_set_from_domain_id s' d"
      using b0 p2 send_queuing_message_def get_domain_cap_set_from_domain_id_def by auto
    then show ?thesis by auto
  next
    assume b0: "\<not> (get_domain_id_from_endpoint s eid \<noteq> None 
              \<and> interferes did s (the (get_domain_id_from_endpoint s eid)))"
    have b1: "s = s'"
      using b0 p2 send_queuing_message_def by auto
    have b2: "get_domain_cap_set_from_domain_id s d 
           = get_domain_cap_set_from_domain_id s' d"
      using b1 get_domain_cap_set_from_domain_id_def by auto
    then show ?thesis by auto
  qed

  lemma send_queuing_message_notchg_policy:
  assumes p0: "reachable0 s"
    and   p2: "s' = fst (send_queuing_message s did eid m)"
  shows   "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v s' d)"
  proof (cases "(get_domain_id_from_endpoint s eid \<noteq> None 
               \<and> interferes did s (the (get_domain_id_from_endpoint s eid)))")
    assume b0: "(get_domain_id_from_endpoint s eid \<noteq> None 
           \<and> interferes did s (the (get_domain_id_from_endpoint s eid)))"
    have b1: "get_domain_cap_set_from_domain_id s d 
           = get_domain_cap_set_from_domain_id s' d"
      using b0 p2 send_queuing_message_def get_domain_cap_set_from_domain_id_def by auto
    have b2: "\<forall>v. get_domain_cap_set_from_domain_id s v 
           = get_domain_cap_set_from_domain_id s' v"
      using b0 p2 send_queuing_message_def get_domain_cap_set_from_domain_id_def by auto
    have b3: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v s' d)"
      using b1 b2 interferes_def by auto
    then show ?thesis by auto
  next                                  
    assume b0: "\<not> (get_domain_id_from_endpoint s eid \<noteq> None 
              \<and> interferes did s (the (get_domain_id_from_endpoint s eid)))"
    have b1: "s = s'"
      using b0 p2 send_queuing_message_def by auto
    have b2: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v s' d)"
      using b1 interferes_def by auto
    then show ?thesis by auto
  qed

  lemma send_queuing_message_notchg_dom_eps:
  assumes p0: "reachable0 s"
    and   p2: "s' = fst (send_queuing_message s did eid m)"
  shows   "get_endpoints_of_domain s d = get_endpoints_of_domain s' d"
  proof (cases "(get_domain_id_from_endpoint s eid \<noteq> None 
               \<and> interferes did s (the (get_domain_id_from_endpoint s eid)))")
    assume b0: "(get_domain_id_from_endpoint s eid \<noteq> None 
           \<and> interferes did s (the (get_domain_id_from_endpoint s eid)))"
    have b1: "get_domain_cap_set_from_domain_id s d 
           = get_domain_cap_set_from_domain_id s' d"
      using b0 p2 send_queuing_message_def get_domain_cap_set_from_domain_id_def by auto
    have b2: "domain_endpoint s = domain_endpoint s'"
      using b0 p2 send_queuing_message_def by auto
    have b3: "get_endpoints_of_domain s d 
           = get_endpoints_of_domain s' d"
      using b2 get_endpoints_of_domain_def by auto
    then show ?thesis by auto
  next
    assume b0: "\<not> (get_domain_id_from_endpoint s eid \<noteq> None 
              \<and> interferes did s (the (get_domain_id_from_endpoint s eid)))"
    have b1: "s = s'"
      using b0 p2 send_queuing_message_def by auto
    have b2: "get_endpoints_of_domain s d 
           = get_endpoints_of_domain s' d"
      using b1 get_endpoints_of_domain_def by auto
    then show ?thesis by auto
  qed

  lemma send_queuing_message_notchg_ep_msgs:
  assumes p0: "reachable0 s"
    and   p1: "\<not>(interferes did s d)"
    and   p2: "s' = fst (send_queuing_message s did eid m)"
  shows   "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id s' ep )"
  proof (cases "(get_domain_id_from_endpoint s eid \<noteq> None 
               \<and> interferes did s (the (get_domain_id_from_endpoint s eid)))")
    assume b0: "(get_domain_id_from_endpoint s eid \<noteq> None 
           \<and> interferes did s (the (get_domain_id_from_endpoint s eid)))"
    have b1: "get_domain_cap_set_from_domain_id s d 
           = get_domain_cap_set_from_domain_id s' d"
      using b0 p2 send_queuing_message_def get_domain_cap_set_from_domain_id_def by auto
    have b2: "domain_endpoint s = domain_endpoint s'"
      using b0 p2 send_queuing_message_def by auto
    have b3: "\<forall>e. e\<noteq>eid
            \<longrightarrow> ((e_msgs s) e) = ((e_msgs s') e)"
      using b0 p2 send_queuing_message_def by auto
    have b4: "domain_endpoint s = domain_endpoint s'"
      using b0 p2 send_queuing_message_def by auto
    have b5: "get_endpoints_of_domain s d 
           = get_endpoints_of_domain s' d"
      using b2 get_endpoints_of_domain_def by auto
    have b6: "(the (get_domain_id_from_endpoint s eid)) \<noteq> d"
      using b0 p1 by auto
    have b7: "(the ((domain_endpoint s) eid)) \<noteq> d"
      using b6 get_domain_id_from_endpoint_def by auto
    have b8: "eid \<notin> get_endpoints_of_domain s d"
      using b7 b6 get_endpoints_of_domain_def by auto
    have b9: "\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> ((e_msgs s) ep) = ((e_msgs s') ep)"
      using b8 b3 by auto
    have b10: "\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id s' ep"
      using b9 get_msg_set_from_endpoint_id_def by auto
    then show ?thesis by auto
  next
    assume b0: "\<not> (get_domain_id_from_endpoint s eid \<noteq> None 
              \<and> interferes did s (the (get_domain_id_from_endpoint s eid)))"
    have b1: "s = s'"
      using b0 p2 send_queuing_message_def by auto
    have b2: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id s' ep )"
      using b1 by auto
    then show ?thesis by auto
  qed

  lemma send_queuing_message_lcl_resp:
  assumes p0: "reachable0 s"
    and   p1: "\<not>(interferes did s d)"
    and   p2: "s' = fst (send_queuing_message s did eid m)"
  shows   "s \<sim> d \<sim> s'"
  proof -
  {
    have a0: "did \<noteq> d"
      using p1 interferes_def by auto
    have a1: "get_domain_cap_set_from_domain_id s d 
             = get_domain_cap_set_from_domain_id s' d"
      using p0 p1 p2 send_queuing_message_notchg_domain_cap_set by auto
    have a2: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v s' d)"
      using p0 p1 p2 send_queuing_message_notchg_policy by auto
    have a3: "get_endpoints_of_domain s d = get_endpoints_of_domain s' d"
      using p0 p1 p2 send_queuing_message_notchg_dom_eps by auto
    have a4: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id s' ep )"
      using p0 p1 p2 send_queuing_message_notchg_ep_msgs by auto
    have a5: "s \<sim> d \<sim> s'"
      using a1 a2 a3 a4 by auto
    }
    then show ?thesis by auto
  qed


  lemma send_queuing_message_lcl_resp_e:
  assumes p0: "reachable0 s"
    and   p1: "a = Send_Queuing_Message did eid m"
    and   p2: "\<not>(interferes (the (domain_of_event a)) s d)"
    and   p3: "s' = exec_event s a"
  shows   "s \<sim> d \<sim> s'"
  proof -
  {
    have a0: "(the (domain_of_event a)) = did"
      using p1 domain_of_event_def by auto
    have a1: "s' = fst (send_queuing_message s did eid m)"
      using p1 p3 exec_event_def by auto
    have a2: "\<not>(interferes did s d)"
      using p2 a0 by auto
    have a3: "s \<sim> d \<sim> s'"
      using a1 a2 p0 send_queuing_message_lcl_resp by blast
  }
  then show ?thesis by auto
  qed

  lemma send_queuing_message_lcl_lcrsp_e: "dynamic_local_respect_e (Send_Queuing_Message did eid m)"
  proof -
    { 
      have "\<forall>d s. reachable0 s 
            \<and> \<not>(interferes (the (domain_of_event (Send_Queuing_Message did eid m))) s d) 
            \<longrightarrow> (s \<sim> d \<sim> (exec_event s (Send_Queuing_Message did eid m)))"
        proof -
        {
          fix d s
          assume p1: "reachable0 s "
          assume p2: " \<not>(interferes (the (domain_of_event (Send_Queuing_Message did eid m))) s d)"
          have "(s \<sim> d \<sim> (exec_event s (Send_Queuing_Message did eid m)))"
            using p1 p2 send_queuing_message_lcl_resp_e by blast
        }
        then show ?thesis by blast
        qed
      }
    then show ?thesis 
      using dynamic_local_respect_e_def by blast
  qed

subsubsection{*proving "receive queuing message" satisfying the "local respect" property*}

lemma receive_queuing_message_notchg_domain_cap_set:
  assumes p0: "reachable0 s"
    and   p1: "\<not>(interferes did s d)"
    and   p2: "s' = fst (receive_queuing_message s did eid)"
  shows   "get_domain_cap_set_from_domain_id s d 
           = get_domain_cap_set_from_domain_id s' d"
  proof (cases "the(get_domain_id_from_endpoint s eid) = did")
    assume a0: "the(get_domain_id_from_endpoint s eid) = did"
    have a1: "get_domain_cap_set_from_domain_id s d 
           = get_domain_cap_set_from_domain_id s' d"
      using a0 p2 receive_queuing_message_def get_domain_cap_set_from_domain_id_def by auto
    then show ?thesis by auto
  next
    assume a0: "the(get_domain_id_from_endpoint s eid) \<noteq> did"
    have a1: "get_domain_cap_set_from_domain_id s d 
           = get_domain_cap_set_from_domain_id s' d"
      using a0 p2 receive_queuing_message_def get_domain_cap_set_from_domain_id_def by auto
    then show ?thesis by auto
  qed

lemma receive_queuing_message_notchg_policy:
  assumes p0: "reachable0 s"
    and   p1: "\<not>(interferes did s d)"
    and   p2: "s' = fst (receive_queuing_message s did eid)"
  shows   "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v s' d)"
  proof (cases "the(get_domain_id_from_endpoint s eid) = did")
    assume a0: "the(get_domain_id_from_endpoint s eid) = did"
    have a1: "get_domain_cap_set_from_domain_id s d 
           = get_domain_cap_set_from_domain_id s' d"
      using a0 p2 receive_queuing_message_def get_domain_cap_set_from_domain_id_def by auto
    have a2: "\<forall>v. get_domain_cap_set_from_domain_id s v 
           = get_domain_cap_set_from_domain_id s' v"
      using a0 p2 receive_queuing_message_def get_domain_cap_set_from_domain_id_def by auto
    have a3: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v s' d)"
      using a1 a2 interferes_def by auto
    then show ?thesis by auto
  next
    assume a0: "the(get_domain_id_from_endpoint s eid) \<noteq> did"
    have a1: "s = s'"
      using a0 p2 receive_queuing_message_def get_domain_cap_set_from_domain_id_def by auto
    have a2: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v s' d)"
      using a1 interferes_def by auto
    then show ?thesis by auto
  qed

lemma receive_queuing_message_notchg_dom_eps:
  assumes p0: "reachable0 s"
    and   p2: "s' = fst (receive_queuing_message s did eid)"
  shows   "get_endpoints_of_domain s d = get_endpoints_of_domain s' d"
  proof (cases "the(get_domain_id_from_endpoint s eid) = did")
    assume a0: "the(get_domain_id_from_endpoint s eid) = did"
    have a1: "get_domain_cap_set_from_domain_id s d 
           = get_domain_cap_set_from_domain_id s' d"
      using a0 p2 receive_queuing_message_def get_domain_cap_set_from_domain_id_def by auto
    have a2: "domain_endpoint s = domain_endpoint s'"
      using a0 p2 receive_queuing_message_def get_domain_cap_set_from_domain_id_def by auto
    have a3: "get_endpoints_of_domain s d 
           = get_endpoints_of_domain s' d"
      using a1 a2 get_endpoints_of_domain_def by auto
    then show ?thesis by auto
  next
    assume a0: "the(get_domain_id_from_endpoint s eid) \<noteq> did"
    have a1: "s = s'"
      using a0 p2 receive_queuing_message_def get_domain_cap_set_from_domain_id_def by auto
    have a2: "get_endpoints_of_domain s d 
           = get_endpoints_of_domain s' d"
      using a1 get_endpoints_of_domain_def by auto
    then show ?thesis by auto
  qed

lemma receive_queuing_message_notchg_ep_msgs:
  assumes p0: "reachable0 s"
    and   p1: "\<not>(interferes did s d)"
    and   p2: "s' = fst (receive_queuing_message s did eid)"
  shows   "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id s' ep )"
  proof (cases "the(get_domain_id_from_endpoint s eid) = did")
    assume a0: "the(get_domain_id_from_endpoint s eid) = did"
    have a1: "get_domain_cap_set_from_domain_id s d 
           = get_domain_cap_set_from_domain_id s' d"
      using a0 p2 receive_queuing_message_def get_domain_cap_set_from_domain_id_def by auto
    have a2: "domain_endpoint s = domain_endpoint s'"
      using a0 p2 receive_queuing_message_def by auto
    have a3: "get_endpoints_of_domain s d 
           = get_endpoints_of_domain s' d"
      using a1 a2 get_endpoints_of_domain_def by auto
    have a4: "\<forall>e. e\<noteq>eid
            \<longrightarrow> ((e_msgs s) e) = ((e_msgs s') e)"
      using a0 p2 receive_queuing_message_def by auto
    have a5: "d \<noteq> did"
      using p1 interferes_def by auto
    have a6: "the(get_domain_id_from_endpoint s eid) \<noteq> d"
      using a5 a0 by auto
    have a7: "(the ((domain_endpoint s) eid)) \<noteq> d"
      using a6 get_domain_id_from_endpoint_def by auto
    have a8: "eid \<notin> get_endpoints_of_domain s d"
      using a7 a6 get_endpoints_of_domain_def by auto
    have a9: "\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> ((e_msgs s) ep) = ((e_msgs s') ep)"
      using a8 a4 by auto
    have a10: "\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id s' ep"
      using a9 get_msg_set_from_endpoint_id_def by auto
    then show ?thesis by auto
  next
    assume a0: "the(get_domain_id_from_endpoint s eid) \<noteq> did"
    have a1: "s = s'"
      using a0 p2 receive_queuing_message_def get_domain_cap_set_from_domain_id_def by auto
    have a2: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id s' ep )"
      using a1 get_msg_set_from_endpoint_id_def by auto
    then show ?thesis by auto
  qed

  lemma receive_queuing_message_lcl_resp:
  assumes p0: "reachable0 s"
    and   p1: "\<not>(interferes did s d)"
    and   p2: "s' = fst (receive_queuing_message s did eid)"
  shows   "s \<sim> d \<sim> s'"
  proof -
  {
    have a0: "did \<noteq> d"
      using p1 interferes_def by auto
    have a1: "get_domain_cap_set_from_domain_id s d 
             = get_domain_cap_set_from_domain_id s' d"
      using p0 p1 p2 receive_queuing_message_notchg_domain_cap_set by auto
    have a2: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v s' d)"
      using p0 p1 p2 receive_queuing_message_notchg_policy by auto
    have a3: "get_endpoints_of_domain s d = get_endpoints_of_domain s' d"
      using p0 p1 p2 receive_queuing_message_notchg_dom_eps by auto
    have a4: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id s' ep )"
      using p0 p1 p2 receive_queuing_message_notchg_ep_msgs by auto
    have a5: "s \<sim> d \<sim> s'"
      using a1 a2 a3 a4 by auto
    }
    then show ?thesis by auto
  qed

  lemma receive_queuing_message_lcl_resp_e:
  assumes p0: "reachable0 s"
    and   p1: "a = (Receive_Queuing_Message did eid)"
    and   p2: "\<not>(interferes (the (domain_of_event a)) s d)"
    and   p3: "s' = exec_event s a"
  shows   "s \<sim> d \<sim> s'"
  proof -
  {
    have a0: "(the (domain_of_event a)) = did"
      using p1 domain_of_event_def by auto
    have a1: "s' = fst (receive_queuing_message s did eid)"
      using p1 p3 exec_event_def by auto
    have a2: "\<not>(interferes did s d)"
      using p2 a0 by auto
    have a3: "s \<sim> d \<sim> s'"
      using a1 a2 p0 receive_queuing_message_lcl_resp by blast
  }
  then show ?thesis by auto
  qed

  lemma receive_queuing_message_lcrsp_e: "dynamic_local_respect_e (Receive_Queuing_Message did eid)"
  proof -
    { 
      have "\<forall>d s. reachable0 s 
            \<and> \<not>(interferes (the (domain_of_event (Receive_Queuing_Message did eid))) s d) 
            \<longrightarrow> (s \<sim> d \<sim> (exec_event s (Receive_Queuing_Message did eid)))"
        proof -
        {
          fix d s
          assume p1: "reachable0 s "
          assume p2: " \<not>(interferes (the (domain_of_event (Receive_Queuing_Message did eid))) s d)"
          have "(s \<sim> d \<sim> (exec_event s (Receive_Queuing_Message did eid)))"
            using p1 p2 receive_queuing_message_lcl_resp_e by blast
        }
        then show ?thesis by blast
        qed
      }
    then show ?thesis 
      using dynamic_local_respect_e_def by blast
  qed

subsubsection{*proving "get my endpoints set" satisfying the "local respect" property*}

  lemma get_my_endpoints_set_lcl_resp:
  assumes p0: "reachable0 s"
    and   p1: "\<not>(interferes did s d)"
    and   p2: "s' = fst (get_my_endpoints_set s did)"
  shows   "s \<sim> d \<sim> s'"
  proof -
  {
    have a1: "s = s'"
      by (simp add: p2 get_my_endpoints_set_def p1)
  }
  then show ?thesis by auto
  qed

  lemma get_my_endpoints_set_lcl_resp_e:
  assumes p0: "reachable0 s"
    and   p1: "a = (Get_My_Endpoints_Set did)"
    and   p2: "\<not>(interferes (the (domain_of_event a)) s d)"
    and   p3: "s' = exec_event s a"
  shows   "s \<sim> d \<sim> s'"
  proof -
  {
    have a0: "(the (domain_of_event a)) = did"
      using p1 domain_of_event_def by auto
    have a1: "s' = fst (get_my_endpoints_set s did)"
      using p1 p3 exec_event_def by auto
    have a2: "\<not>(interferes did s d)"
      using p2 a0 by auto
    have a3: "s \<sim> d \<sim> s'"
      using a1 a2 p0 get_my_endpoints_set_lcl_resp by blast
  }
  then show ?thesis by auto
  qed

  lemma get_my_endpoints_set_lcrsp_e: "dynamic_local_respect_e (Get_My_Endpoints_Set did)"
  proof -
    { 
      have "\<forall>d s. reachable0 s 
            \<and> \<not>(interferes (the (domain_of_event (Get_My_Endpoints_Set did))) s d) 
            \<longrightarrow> (s \<sim> d \<sim> (exec_event s (Get_My_Endpoints_Set did)))"
        proof -
        {
          fix d s
          assume p1: "reachable0 s "
          assume p2: " \<not>(interferes (the (domain_of_event (Get_My_Endpoints_Set did))) s d)"
          have "(s \<sim> d \<sim> (exec_event s (Get_My_Endpoints_Set did)))"
            using p1 p2 get_my_endpoints_set_lcl_resp_e by blast
        }
        then show ?thesis by blast
        qed
      }
    then show ?thesis 
      using dynamic_local_respect_e_def by blast
  qed

subsubsection{*proving "get caps" satisfying the "local respect" property*}

  lemma get_caps_lcl_resp:
  assumes p0: "reachable0 s"
    and   p1: "\<not>(interferes did s d)"
    and   p2: "s' = fst (get_caps s did)"
  shows   "s \<sim> d \<sim> s'"
  proof -
  {
    have a1: "s = s'"
      by (simp add: p2 get_caps_def p1)
  }
  then show ?thesis by auto
  qed

  lemma get_caps_lcl_resp_e:
  assumes p0: "reachable0 s"
    and   p1: "a = (Get_Caps did)"
    and   p2: "\<not>(interferes (the (domain_of_event a)) s d)"
    and   p3: "s' = exec_event s a"
  shows   "s \<sim> d \<sim> s'"
  proof -
  {
    have a0: "(the (domain_of_event a)) = did"
      using p1 domain_of_event_def by auto
    have a1: "s' = fst (get_caps s did)"
      using p1 p3 exec_event_def by auto
    have a2: "\<not>(interferes did s d)"
      using p2 a0 by auto
    have a3: "s \<sim> d \<sim> s'"
      using a1 a2 p0 get_caps_lcl_resp by blast
  }
  then show ?thesis by auto
  qed

  lemma get_caps_lcrsp_e: "dynamic_local_respect_e (Get_Caps did)"
  proof -
    { 
      have "\<forall>d s. reachable0 s 
            \<and> \<not>(interferes (the (domain_of_event (Get_Caps did))) s d) 
            \<longrightarrow> (s \<sim> d \<sim> (exec_event s (Get_Caps did)))"
        proof -
        {
          fix d s
          assume p1: "reachable0 s "
          assume p2: " \<not>(interferes (the (domain_of_event (Get_Caps did))) s d)"
          have "(s \<sim> d \<sim> (exec_event s (Get_Caps did)))"
            using p1 p2 get_caps_lcl_resp_e by blast
        }
        then show ?thesis by blast
        qed
      }
    then show ?thesis 
      using dynamic_local_respect_e_def by blast
    qed

subsubsection{*proving "grant endpoint cap" satisfying the "local respect" property*}

  lemma grant_endpoint_cap_notchg_domain_cap_set:
  assumes p0: "reachable0 s"
    and   p1: "\<not>(interferes did s d)"
    and   p2: "s' = fst (grant_endpoint_cap s did grant_cap dst_cap)"
  shows   "get_domain_cap_set_from_domain_id s d 
           = get_domain_cap_set_from_domain_id s' d"
  proof (cases "grant_cap\<in>get_domain_cap_set_from_domain_id s did 
              \<and> GRANT\<in>rights grant_cap
              \<and> target grant_cap \<noteq> target dst_cap
              \<and> dst_cap\<in>get_domain_cap_set_from_domain_id s did")
    assume a0: "grant_cap\<in>get_domain_cap_set_from_domain_id s did 
              \<and> GRANT\<in>rights grant_cap
              \<and> target grant_cap \<noteq> target dst_cap
              \<and> dst_cap\<in>get_domain_cap_set_from_domain_id s did"
    let ?did_dst = "target grant_cap"
    have a1: "\<forall>v. v\<noteq>?did_dst
              \<longrightarrow> (caps s) v = (caps s') v"
      using a0 p2 grant_endpoint_cap_def get_domain_cap_set_from_domain_id_def by auto
    have a2: "d \<noteq> did"
      using p1 interferes_def by auto
    have a3: "\<not>(( did = d
              \<or> (\<exists>c. c\<in>(get_domain_cap_set_from_domain_id s did) \<and> target c = d)))"
      using interferes_def p1 by force
    have a4: "\<forall>c. c\<in>(get_domain_cap_set_from_domain_id s did) 
              \<longrightarrow> target c \<noteq> d"
      using a3 by auto
    have a5: "?did_dst \<noteq> d"
      using a4 a0 by auto
    have a6: "(caps s) d = (caps s') d"
      using a1 a5 by auto
    have a7: "get_domain_cap_set_from_domain_id s d 
           = get_domain_cap_set_from_domain_id s' d"
      using a6 get_domain_cap_set_from_domain_id_def by auto
    then show ?thesis by auto
  next
    assume a0: "\<not> (grant_cap \<in> get_domain_cap_set_from_domain_id s did 
                  \<and> GRANT \<in> rights grant_cap 
                  \<and> target grant_cap \<noteq> target dst_cap
                  \<and> dst_cap \<in> get_domain_cap_set_from_domain_id s did)"
    have a1: "s = s'"
      using a0 p2 grant_endpoint_cap_def by auto
    have a2: "get_domain_cap_set_from_domain_id s d 
           = get_domain_cap_set_from_domain_id s' d"
      using a1 get_domain_cap_set_from_domain_id_def by auto
    then show ?thesis by auto
  qed

  lemma grant_endpoint_cap_notchg_policy:
  assumes p0: "reachable0 s"
    and   p1: "\<not>(interferes did s d)"
    and   p2: "s' = fst (grant_endpoint_cap s did grant_cap dst_cap)"
  shows   "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v s' d)"
  proof (cases "grant_cap\<in>get_domain_cap_set_from_domain_id s did 
              \<and> GRANT\<in>rights grant_cap
              \<and> target grant_cap \<noteq> target dst_cap
              \<and> dst_cap\<in>get_domain_cap_set_from_domain_id s did")
    assume a0: "grant_cap\<in>get_domain_cap_set_from_domain_id s did 
              \<and> GRANT\<in>rights grant_cap
              \<and> target grant_cap \<noteq> target dst_cap
              \<and> dst_cap\<in>get_domain_cap_set_from_domain_id s did"
    let ?did_dst = "target grant_cap"
    let ?did_granted = "target dst_cap"
    have a1: "\<forall>v. v\<noteq>?did_dst
              \<longrightarrow> (caps s) v = (caps s') v"
      using a0 p2 grant_endpoint_cap_def by auto
    have a2: "d \<noteq> did"
      using p1 interferes_def by auto
    have a3: "\<not>(( did = d
              \<or> (\<exists>c. c\<in>(get_domain_cap_set_from_domain_id s did) \<and> target c = d)))"
      using interferes_def p1 by force
    have a4: "\<forall>c. c\<in>(get_domain_cap_set_from_domain_id s did) 
              \<longrightarrow> target c \<noteq> d"
      using a3 by auto
    have a5: "?did_dst \<noteq> d"
      using a4 a0 by auto
    have a6: "(caps s) d = (caps s') d"
      using a1 a5 by auto
    have a7: "get_domain_cap_set_from_domain_id s d 
           = get_domain_cap_set_from_domain_id s' d"
      using a6 get_domain_cap_set_from_domain_id_def by auto
    have a8: "?did_granted \<noteq> d"
      using a4 a0 by auto
    have a9: "\<forall>v. v\<noteq>?did_dst
              \<longrightarrow> get_domain_cap_set_from_domain_id s v 
                = get_domain_cap_set_from_domain_id s' v"
      using a1 get_domain_cap_set_from_domain_id_def by auto
    have a10: "\<forall>v. v\<noteq>?did_dst
              \<longrightarrow> interferes v s d \<longleftrightarrow> interferes v s' d"
      using a9 a7 interferes_def by auto
    have a11: "get_domain_cap_set_from_domain_id s' ?did_dst
              = {dst_cap} \<union> get_domain_cap_set_from_domain_id s ?did_dst"
      using a0 p2 grant_endpoint_cap_def get_domain_cap_set_from_domain_id_def by auto 
    have a12: "interferes ?did_dst s d = interferes ?did_dst s' d"
      using a11 a8 interferes_def by auto
    have a13: "\<forall>v. interferes v s d \<longleftrightarrow> interferes v s' d"
      using a10 a12 by force
    then show ?thesis by auto
  next
    assume a0: "\<not> (grant_cap \<in> get_domain_cap_set_from_domain_id s did 
                  \<and> GRANT \<in> rights grant_cap
                  \<and> target grant_cap \<noteq> target dst_cap
                  \<and> dst_cap \<in> get_domain_cap_set_from_domain_id s did)"
    have a1: "s = s'"
      using a0 p2 grant_endpoint_cap_def by auto
    have a2: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v s' d)"
      using a1 interferes_def by auto
    then show ?thesis by auto
  qed

  lemma grant_endpoint_cap_notchg_dom_eps:
  assumes p0: "reachable0 s"
    and   p2: "s' = fst (grant_endpoint_cap s did grant_cap dst_cap)"
  shows   "get_endpoints_of_domain s d = get_endpoints_of_domain s' d"
  proof (cases "grant_cap\<in>get_domain_cap_set_from_domain_id s did 
              \<and> GRANT\<in>rights grant_cap
              \<and> target grant_cap \<noteq> target dst_cap
              \<and> dst_cap\<in>get_domain_cap_set_from_domain_id s did")
    assume a0: "grant_cap\<in>get_domain_cap_set_from_domain_id s did 
              \<and> GRANT\<in>rights grant_cap
              \<and> target grant_cap \<noteq> target dst_cap
              \<and> dst_cap\<in>get_domain_cap_set_from_domain_id s did"
    have a2: "domain_endpoint s = domain_endpoint s'"
      using a0 p2 grant_endpoint_cap_def by auto
    have a3: "get_endpoints_of_domain s d 
           = get_endpoints_of_domain s' d"
      using a2 get_endpoints_of_domain_def by auto
    then show ?thesis by auto
  next
    assume a0: "\<not>(grant_cap\<in>get_domain_cap_set_from_domain_id s did 
              \<and> GRANT\<in>rights grant_cap
              \<and> target grant_cap \<noteq> target dst_cap
              \<and> dst_cap\<in>get_domain_cap_set_from_domain_id s did)"
    have a1: "s = s'"
      using a0 p2 grant_endpoint_cap_def by auto
    have a2: "get_endpoints_of_domain s d 
           = get_endpoints_of_domain s' d"
      using a1 get_endpoints_of_domain_def by auto
    then show ?thesis by auto
  qed

  lemma grant_endpoint_cap_notchg_ep_msgs:
  assumes p0: "reachable0 s"
    and   p1: "\<not>(interferes did s d)"
    and   p2: "s' = fst (grant_endpoint_cap s did grant_cap dst_cap)"
  shows   "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id s' ep )"
  proof (cases "grant_cap\<in>get_domain_cap_set_from_domain_id s did 
              \<and> GRANT\<in>rights grant_cap
              \<and> target grant_cap \<noteq> target dst_cap
              \<and> dst_cap\<in>get_domain_cap_set_from_domain_id s did")
    assume a0: "grant_cap\<in>get_domain_cap_set_from_domain_id s did 
              \<and> GRANT\<in>rights grant_cap
              \<and> target grant_cap \<noteq> target dst_cap
              \<and> dst_cap\<in>get_domain_cap_set_from_domain_id s did"
    have a2: "domain_endpoint s = domain_endpoint s'"
      using a0 p2 grant_endpoint_cap_def by auto
    have a3: "get_endpoints_of_domain s d 
           = get_endpoints_of_domain s' d"
      using a2 get_endpoints_of_domain_def by auto
    have a4: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id s' ep )"
      using a0 p2 grant_endpoint_cap_def get_msg_set_from_endpoint_id_def by auto
    then show ?thesis by auto
  next
    assume a0: "\<not>(grant_cap\<in>get_domain_cap_set_from_domain_id s did 
              \<and> GRANT\<in>rights grant_cap
              \<and> target grant_cap \<noteq> target dst_cap
              \<and> dst_cap\<in>get_domain_cap_set_from_domain_id s did)"
    have a1: "s = s'"
      using a0 p2 grant_endpoint_cap_def by auto
    have a2: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id s' ep )"
      using a1 by auto
    then show ?thesis by auto
  qed

  lemma grant_endpoint_cap_lcl_resp:
  assumes p0: "reachable0 s"
    and   p1: "\<not>(interferes did s d)"
    and   p2: "s' = fst (grant_endpoint_cap s did eid m)"
  shows   "s \<sim> d \<sim> s'"
  proof -
  {
    have a0: "did \<noteq> d"
      using p1 interferes_def by auto
    have a1: "get_domain_cap_set_from_domain_id s d 
             = get_domain_cap_set_from_domain_id s' d"
      using p0 p1 p2 grant_endpoint_cap_notchg_domain_cap_set by auto
    have a2: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v s' d)"
      using p0 p1 p2 grant_endpoint_cap_notchg_policy by auto
    have a3: "get_endpoints_of_domain s d = get_endpoints_of_domain s' d"
      using p0 p1 p2 grant_endpoint_cap_notchg_dom_eps by auto
    have a4: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id s' ep )"
      using p0 p1 p2 grant_endpoint_cap_notchg_ep_msgs by auto
    have a5: "s \<sim> d \<sim> s'"
      using a1 a2 a3 a4 by auto
    }
    then show ?thesis by auto
  qed

  lemma grant_endpoint_cap_lcl_resp_e:
  assumes p0: "reachable0 s"
    and   p1: "a = (Grant_Endpoint_Cap did grant_cap dst_cap)"
    and   p2: "\<not>(interferes (the (domain_of_event a)) s d)"
    and   p3: "s' = exec_event s a"
  shows   "s \<sim> d \<sim> s'"
  proof -
  {
    have a0: "(the (domain_of_event a)) = did"
      using p1 domain_of_event_def by auto
    have a1: "s' = fst (grant_endpoint_cap s did grant_cap dst_cap)"
      using p1 p3 exec_event_def by auto
    have a2: "\<not>(interferes did s d)"
      using p2 a0 by auto
    have a3: "s \<sim> d \<sim> s'"
      using a1 a2 p0 grant_endpoint_cap_lcl_resp by blast
  }
  then show ?thesis by auto
  qed

  lemma grant_endpoint_cap_lcrsp_e: "dynamic_local_respect_e (Grant_Endpoint_Cap did grant_cap dst_cap)"
  proof -
    { 
      have "\<forall>d s. reachable0 s 
            \<and> \<not>(interferes (the (domain_of_event (Grant_Endpoint_Cap did grant_cap dst_cap))) s d) 
            \<longrightarrow> (s \<sim> d \<sim> (exec_event s (Grant_Endpoint_Cap did grant_cap dst_cap)))"
        proof -
        {
          fix d s
          assume p1: "reachable0 s "
          assume p2: " \<not>(interferes (the (domain_of_event (Grant_Endpoint_Cap did grant_cap dst_cap))) s d)"
          have "(s \<sim> d \<sim> (exec_event s (Grant_Endpoint_Cap did grant_cap dst_cap)))"
            using p1 p2 grant_endpoint_cap_lcl_resp_e by blast
        }
        then show ?thesis by blast
        qed
      }
    then show ?thesis 
      using dynamic_local_respect_e_def by blast
  qed

subsubsection{*proving "remove cap right" satisfying the "local respect" property*}

  lemma remove_cap_right_notchg_domain_cap_set:
  assumes p0: "reachable0 s"
    and   p1: "\<not>(interferes did s d)"
    and   p2: "s' = fst (remove_cap_right s did rm_cap right_to_rm)"
  shows   "get_domain_cap_set_from_domain_id s d 
           = get_domain_cap_set_from_domain_id s' d"
  proof -
  {
    have a0: "d \<noteq> did"
      using p1 interferes_def by auto
    have "get_domain_cap_set_from_domain_id s d 
           = get_domain_cap_set_from_domain_id s' d"
      proof (cases "rm_cap \<in>  get_domain_cap_set_from_domain_id s did 
              \<and> REMOVE \<in> rights rm_cap
              \<and> right_to_rm \<in> rights rm_cap")
      assume b0: "rm_cap \<in>  get_domain_cap_set_from_domain_id s did 
              \<and> REMOVE \<in> rights rm_cap
              \<and> right_to_rm \<in> rights rm_cap"
      have "get_domain_cap_set_from_domain_id s d 
           = get_domain_cap_set_from_domain_id s' d"  
        proof (cases " REMOVE = right_to_rm
                  \<and> {REMOVE} = rights rm_cap")
          assume c0: "REMOVE = right_to_rm
                  \<and> {REMOVE} = rights rm_cap"
          let ?cs_dst = "get_domain_cap_set_from_domain_id s did"
          let ?cs_rest = "{c. c\<in>?cs_dst \<and> c\<noteq>rm_cap}"
          have c1: "((caps s') did) = ?cs_rest"
            using b0 c0 p2 remove_cap_right_def by auto
          have c2: "\<forall>v. v\<noteq>did
                    \<longrightarrow> ((caps s') v) = ((caps s) v)"
            using b0 c0 p2 remove_cap_right_def by auto
          have c3: "\<forall>v. v\<noteq>did
                    \<longrightarrow> get_domain_cap_set_from_domain_id s v 
                      = get_domain_cap_set_from_domain_id s' v"
            using c2 get_domain_cap_set_from_domain_id_def by auto
          have c4: "get_domain_cap_set_from_domain_id s d 
                      = get_domain_cap_set_from_domain_id s' d"
            using c3 a0 by auto
          then show ?thesis by auto
        next
          assume c0: "\<not>(REMOVE = right_to_rm
                      \<and> {REMOVE} = rights rm_cap)"
          let ?cs_dst = "get_domain_cap_set_from_domain_id s did"
          let ?cs_rest = "{c. c\<in>?cs_dst \<and> c\<noteq>rm_cap}"
          let ?new_cap = "\<lparr> target = target rm_cap,
                            rights = (rights rm_cap) - {right_to_rm}\<rparr>"
          have c1: "((caps s') did) = (insert ?new_cap ?cs_rest)"
            using b0 c0 p2 remove_cap_right_def by auto
          have c2: "\<forall>v. v\<noteq>did
                    \<longrightarrow> ((caps s') v) = ((caps s) v)"
            using b0 c0 p2 remove_cap_right_def by auto
          have c3: "\<forall>v. v\<noteq>did
                    \<longrightarrow> get_domain_cap_set_from_domain_id s v 
                      = get_domain_cap_set_from_domain_id s' v"
            using c2 get_domain_cap_set_from_domain_id_def by auto
          have c4: "get_domain_cap_set_from_domain_id s d 
                      = get_domain_cap_set_from_domain_id s' d"
            using c3 a0 by auto
          then show ?thesis by auto
        qed
      then show ?thesis by auto
    next
      assume b0: "\<not>(rm_cap \<in>  get_domain_cap_set_from_domain_id s did 
                    \<and> REMOVE \<in> rights rm_cap
                    \<and> right_to_rm \<in> rights rm_cap)"
      have b1: "s' = s"
        using b0 p2 remove_cap_right_def by auto
      have b2: "get_domain_cap_set_from_domain_id s d 
                = get_domain_cap_set_from_domain_id s' d"
        using b1 get_domain_cap_set_from_domain_id_def by auto
      then show ?thesis by auto
    qed
    }
  then show ?thesis by auto
  qed

  lemma remove_cap_right_notchg_policy:
  assumes p0: "reachable0 s"
    and   p1: "\<not>(interferes did s d)"
    and   p2: "s' = fst (remove_cap_right s did rm_cap right_to_rm)"
  shows   "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v s' d)"
  proof -
  {
    have a0: "d \<noteq> did"
      using p1 interferes_def by auto
    have "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v s' d)"
      proof (cases "rm_cap \<in>  get_domain_cap_set_from_domain_id s did 
              \<and> REMOVE \<in> rights rm_cap
              \<and> right_to_rm \<in> rights rm_cap")
      assume b0: "rm_cap \<in>  get_domain_cap_set_from_domain_id s did 
              \<and> REMOVE \<in> rights rm_cap
              \<and> right_to_rm \<in> rights rm_cap"
      have a1: "d \<noteq> target rm_cap"
        by (metis b0 interferes_def p1)
      have "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v s' d)"
        proof (cases " REMOVE = right_to_rm
                  \<and> {REMOVE} = rights rm_cap")
          assume c0: "REMOVE = right_to_rm
                  \<and> {REMOVE} = rights rm_cap"
          let ?cs_dst = "get_domain_cap_set_from_domain_id s did"
          let ?cs_rest = "{c. c\<in>?cs_dst \<and> c\<noteq>rm_cap}"
          have c1: "((caps s') did) = ?cs_rest"
            using b0 c0 p2 remove_cap_right_def by auto
          have c2: "\<forall>v. v\<noteq>did
                    \<longrightarrow> ((caps s') v) = ((caps s) v)"
            using b0 c0 p2 remove_cap_right_def by auto
          have c3: "\<forall>v. v\<noteq>did
                    \<longrightarrow> get_domain_cap_set_from_domain_id s v 
                      = get_domain_cap_set_from_domain_id s' v"
            using c2 get_domain_cap_set_from_domain_id_def by auto
          have c4: "get_domain_cap_set_from_domain_id s d 
                      = get_domain_cap_set_from_domain_id s' d"
            using c3 a0 by auto
          have c5: "get_domain_cap_set_from_domain_id s d 
                      = get_domain_cap_set_from_domain_id s' d"
            using c3 a0 by auto
          have c6: "\<forall>v. v\<noteq>did
                    \<longrightarrow> interferes v s d \<longleftrightarrow> interferes v s' d"
            using c3 c5 interferes_def by auto
          have c7: "((caps s') did) = (?cs_rest)"
            using b0 c0 p2 remove_cap_right_def by auto
          have c8: "get_domain_cap_set_from_domain_id s' did
                  = ?cs_rest"
            using c7 get_domain_cap_set_from_domain_id_def by auto
          have c9: "get_domain_cap_set_from_domain_id s' did 
                    \<subseteq> get_domain_cap_set_from_domain_id s did"
            using c8 by auto
          have c10: "\<not>(\<exists>c. c\<in>(get_domain_cap_set_from_domain_id s did) \<and> target c = d)"
            by (metis interferes_def p1)
          have c11: "\<not>(\<exists>c. c\<in>(get_domain_cap_set_from_domain_id s' did) \<and> target c = d)"
            using c10 c9 by auto
          have c12: "\<not>(interferes did s' d)"
            using a0 c11 interferes_def by auto
          have c13: "interferes did s' d = interferes did s d"
            using c12 p1 by auto
          have c14: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v s' d)"
            using c6 c13 by auto
          then show ?thesis by auto
        next
          assume c0: "\<not>(REMOVE = right_to_rm
                      \<and> {REMOVE} = rights rm_cap)"
          let ?cs_dst = "get_domain_cap_set_from_domain_id s did"
          let ?cs_rest = "{c. c\<in>?cs_dst \<and> c\<noteq>rm_cap}"
          let ?new_cap = "\<lparr> target = target rm_cap,
                            rights = (rights rm_cap) - {right_to_rm}\<rparr>"
          have c1: "((caps s') did) = (insert ?new_cap ?cs_rest)"
            using b0 c0 p2 remove_cap_right_def by auto
          have c2: "\<forall>v. v\<noteq>did
                    \<longrightarrow> ((caps s') v) = ((caps s) v)"
            using b0 c0 p2 remove_cap_right_def by auto
          have c3: "\<forall>v. v\<noteq>did
                    \<longrightarrow> get_domain_cap_set_from_domain_id s v 
                      = get_domain_cap_set_from_domain_id s' v"
            using c2 get_domain_cap_set_from_domain_id_def by auto
          have c4: "get_domain_cap_set_from_domain_id s d 
                      = get_domain_cap_set_from_domain_id s' d"
            using c3 a0 by auto
          have c5: "get_domain_cap_set_from_domain_id s d 
                      = get_domain_cap_set_from_domain_id s' d"
            using c3 a0 by auto
          have c6: "\<forall>v. v\<noteq>did
                    \<longrightarrow> interferes v s d \<longleftrightarrow> interferes v s' d"
            using c3 c5 interferes_def by auto
          have c7: "get_domain_cap_set_from_domain_id s' did 
                      = (insert ?new_cap ?cs_rest)"
            using c1 get_domain_cap_set_from_domain_id_def by auto
          have c8: "\<not>(\<exists>c. c\<in>(get_domain_cap_set_from_domain_id s did) \<and> target c = d)"
            by (metis interferes_def p1)
          have c9: "\<not>(\<exists>c. c\<in>(get_domain_cap_set_from_domain_id s' did) \<and> target c = d)"
            using c8 c7 a1 by auto
          have c10: "\<not>(interferes did s' d)"
            using a0 c9 interferes_def by auto
          have c11: "interferes did s' d = interferes did s d"
            using c10 p1 by auto
          have c12: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v s' d)"
            using c6 c11 by auto
          then show ?thesis by auto
        qed
      then show ?thesis by auto
    next
      assume b0: "\<not>(rm_cap \<in>  get_domain_cap_set_from_domain_id s did 
                    \<and> REMOVE \<in> rights rm_cap
                    \<and> right_to_rm \<in> rights rm_cap)"
      have b1: "s' = s"
        using b0 p2 remove_cap_right_def by auto
      have b2: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v s' d)"
        using b1 interferes_def by auto
      then show ?thesis by auto
    qed
    }
  then show ?thesis by auto
  qed

  lemma remove_cap_right_notchg_dom_eps:
  assumes p0: "reachable0 s"
    and   p2: "s' = fst (remove_cap_right s did rm_cap right_to_rm)"
  shows   "get_endpoints_of_domain s d = get_endpoints_of_domain s' d"
  proof -
  {
    have "get_endpoints_of_domain s d = get_endpoints_of_domain s' d"
      proof (cases "rm_cap \<in>  get_domain_cap_set_from_domain_id s did 
              \<and> REMOVE \<in> rights rm_cap
              \<and> right_to_rm \<in> rights rm_cap")
      assume b0: "rm_cap \<in>  get_domain_cap_set_from_domain_id s did 
              \<and> REMOVE \<in> rights rm_cap
              \<and> right_to_rm \<in> rights rm_cap"
      have "get_endpoints_of_domain s d = get_endpoints_of_domain s' d"
        proof (cases " REMOVE = right_to_rm
                  \<and> {REMOVE} = rights rm_cap")
          assume c0: "REMOVE = right_to_rm
                  \<and> {REMOVE} = rights rm_cap"
          let ?cs_dst = "get_domain_cap_set_from_domain_id s did"
          let ?cs_rest = "{c. c\<in>?cs_dst \<and> c\<noteq>rm_cap}"
          have c1: "((caps s') did) = ?cs_rest"
            using b0 c0 p2 remove_cap_right_def by auto
          have c2: "get_endpoints_of_domain s d = get_endpoints_of_domain s' d"
            using b0 c0 p2 remove_cap_right_def get_endpoints_of_domain_def by auto
          then show ?thesis by auto
        next
          assume c0: "\<not>(REMOVE = right_to_rm
                      \<and> {REMOVE} = rights rm_cap)"
          let ?cs_dst = "get_domain_cap_set_from_domain_id s did"
          let ?cs_rest = "{c. c\<in>?cs_dst \<and> c\<noteq>rm_cap}"
          let ?new_cap = "\<lparr> target = target rm_cap,
                            rights = (rights rm_cap) - {right_to_rm}\<rparr>"
          have c1: "((caps s') did) = (insert ?new_cap ?cs_rest)"
            using b0 c0 p2 remove_cap_right_def by auto
          have c2: "get_endpoints_of_domain s d = get_endpoints_of_domain s' d"
            using b0 c0 p2 remove_cap_right_def get_endpoints_of_domain_def by auto
          then show ?thesis by auto
        qed
      then show ?thesis by auto
    next
      assume b0: "\<not>(rm_cap \<in>  get_domain_cap_set_from_domain_id s did 
                    \<and> REMOVE \<in> rights rm_cap
                    \<and> right_to_rm \<in> rights rm_cap)"
      have b1: "s' = s"
        using b0 p2 remove_cap_right_def by auto
      have b2: "get_endpoints_of_domain s d = get_endpoints_of_domain s' d"
        using b1 get_endpoints_of_domain_def by auto
      then show ?thesis by auto
    qed
    }
  then show ?thesis by auto
  qed

  lemma remove_cap_right_notchg_ep_msgs:
  assumes p0: "reachable0 s"
    and   p2: "s' = fst (remove_cap_right s did rm_cap right_to_rm)"
  shows   "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id s' ep )"
  proof -
  {
    have "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id s' ep )"
      proof (cases "rm_cap \<in>  get_domain_cap_set_from_domain_id s did 
              \<and> REMOVE \<in> rights rm_cap
              \<and> right_to_rm \<in> rights rm_cap")
      assume b0: "rm_cap \<in>  get_domain_cap_set_from_domain_id s did 
              \<and> REMOVE \<in> rights rm_cap
              \<and> right_to_rm \<in> rights rm_cap"
      have "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id s' ep )"
        proof (cases " REMOVE = right_to_rm
                  \<and> {REMOVE} = rights rm_cap")
          assume c0: "REMOVE = right_to_rm
                  \<and> {REMOVE} = rights rm_cap"
          let ?cs_dst = "get_domain_cap_set_from_domain_id s did"
          let ?cs_rest = "{c. c\<in>?cs_dst \<and> c\<noteq>rm_cap}"
          have c1: "((caps s') did) = ?cs_rest"
            using b0 c0 p2 remove_cap_right_def by auto
          have c2: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id s' ep )"
            using b0 c0 p2 remove_cap_right_def get_endpoints_of_domain_def
                  get_msg_set_from_endpoint_id_def by auto
          then show ?thesis by auto
        next
          assume c0: "\<not>(REMOVE = right_to_rm
                      \<and> {REMOVE} = rights rm_cap)"
          let ?cs_dst = "get_domain_cap_set_from_domain_id s did"
          let ?cs_rest = "{c. c\<in>?cs_dst \<and> c\<noteq>rm_cap}"
          let ?new_cap = "\<lparr> target = target rm_cap,
                            rights = (rights rm_cap) - {right_to_rm}\<rparr>"
          have c1: "((caps s') did) = (insert ?new_cap ?cs_rest)"
            using b0 c0 p2 remove_cap_right_def by auto
          have c2: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id s' ep )"
            using b0 c0 p2 remove_cap_right_def get_endpoints_of_domain_def
                  get_msg_set_from_endpoint_id_def by auto
          then show ?thesis by auto
        qed
      then show ?thesis by auto
    next
      assume b0: "\<not>(rm_cap \<in>  get_domain_cap_set_from_domain_id s did 
                    \<and> REMOVE \<in> rights rm_cap
                    \<and> right_to_rm \<in> rights rm_cap)"
      have b1: "s' = s"
        using b0 p2 remove_cap_right_def by auto
      have b2: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id s' ep )"
        using b1 get_endpoints_of_domain_def by auto
      then show ?thesis by auto
    qed
    }
  then show ?thesis by auto
  qed

  lemma remove_cap_right_lcl_resp:
  assumes p0: "reachable0 s"
    and   p1: "\<not>(interferes did s d)"
    and   p2: "s' = fst (remove_cap_right s did rm_cap right_to_rm)"
  shows   "s \<sim> d \<sim> s'"
  proof -
  {
    have a0: "did \<noteq> d"
      using p1 interferes_def by auto
    have a1: "get_domain_cap_set_from_domain_id s d 
             = get_domain_cap_set_from_domain_id s' d"
      using p0 p1 p2 remove_cap_right_notchg_domain_cap_set by auto
    have a2: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v s' d)"
      using p0 p1 p2 remove_cap_right_notchg_policy by auto
    have a3: "get_endpoints_of_domain s d = get_endpoints_of_domain s' d"
      using p0 p1 p2 remove_cap_right_notchg_dom_eps by auto
    have a4: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id s' ep )"
      using p0 p1 p2 remove_cap_right_notchg_ep_msgs by auto
    have a5: "s \<sim> d \<sim> s'"
      using a1 a2 a3 a4 by auto
    }
    then show ?thesis by auto
  qed

  lemma remove_cap_right_lcl_resp_e:
  assumes p0: "reachable0 s"
    and   p1: "a = (Remove_Cap_Right did dst_cap right_to_rm)"
    and   p2: "\<not>(interferes (the (domain_of_event a)) s d)"
    and   p3: "s' = exec_event s a"
  shows   "s \<sim> d \<sim> s'"
  proof -
  {
    have a0: "(the (domain_of_event a)) = did"
      using p1 domain_of_event_def by auto
    have a1: "s' = fst (remove_cap_right s did dst_cap right_to_rm)"
      using p1 p3 exec_event_def by auto
    have a2: "\<not>(interferes did s d)"
      using p2 a0 by auto
    have a3: "s \<sim> d \<sim> s'"
      using a1 a2 p0 remove_cap_right_lcl_resp by blast
  }
  then show ?thesis by auto
  qed

  lemma remove_cap_right_lcrsp_e: "dynamic_local_respect_e (Remove_Cap_Right did dst_cap right_to_rm)"
  proof -
    { 
      have "\<forall>d s. reachable0 s 
            \<and> \<not>(interferes (the (domain_of_event (Remove_Cap_Right did dst_cap right_to_rm))) s d) 
            \<longrightarrow> (s \<sim> d \<sim> (exec_event s (Remove_Cap_Right did dst_cap right_to_rm)))"
        proof -
        {
          fix d s
          assume p1: "reachable0 s "
          assume p2: " \<not>(interferes (the (domain_of_event (Remove_Cap_Right did dst_cap right_to_rm))) s d)"
          have "(s \<sim> d \<sim> (exec_event s (Remove_Cap_Right did dst_cap right_to_rm)))"
            using p1 p2 remove_cap_right_lcl_resp_e by blast
        }
        then show ?thesis by blast
        qed
      }
    then show ?thesis 
      using dynamic_local_respect_e_def by blast
  qed

subsubsection{*proving the "dynamic local respect" property*}

  definition dynamic_local_respect_c :: "bool" where
        "dynamic_local_respect_c \<equiv> \<forall>a d s. reachable0 s 
                                  \<and> \<not>(interferes (the (domain_of_event a)) s d) 
                                  \<longrightarrow> (s \<sim> d \<sim> (exec_event s a))"

  theorem dynamic_local_respect:dynamic_local_respect
    proof -
      {
        fix e
        have "dynamic_local_respect_e e"
          proof (induct e)
            case (Client_Lookup_Endpoint_Name x x1)
              show ?case
              using client_lookup_endpoint_name_lcrsp_e by blast
            case (Send_Queuing_Message x1a x2 x3a) 
              show ?case
              using send_queuing_message_lcl_lcrsp_e by blast
            case (Receive_Queuing_Message x) 
              show ?case
              using receive_queuing_message_lcrsp_e by blast
            case (Get_My_Endpoints_Set x) 
              show ?case
              using get_my_endpoints_set_lcrsp_e by blast
            case (Get_Caps x) 
              show ?case
              using get_caps_lcrsp_e by blast
            case (Grant_Endpoint_Cap x1a x2 x3a) 
              show ?case
              using grant_endpoint_cap_lcrsp_e by blast
            case (Remove_Cap_Right x1a x2 x3a) 
              show ?case
              using remove_cap_right_lcrsp_e by blast
            qed
        }
    then show ?thesis 
      using dynamic_local_respect_all_evt by blast
    qed
                                                                           
subsection{* Concrete unwinding condition of "weakly step consistent" *}

subsubsection{*proving "client lookup endpoint name" satisfying the "weakly step consistent" property*}  

  lemma client_lookup_endpoint_name_wsc:
  assumes p0: "reachable0 s"
    and   p1: "reachable0 t"
    and   p2: "s \<sim> d \<sim> t"
    and   p3: "interferes did s d"
    and   p4: "s \<sim> did \<sim> t "
    and   p5: "s' = fst (client_lookup_endpoint_name sysconf s did ename)"
    and   p6: "t' = fst (client_lookup_endpoint_name sysconf t did ename)"
  shows   "s' \<sim> d \<sim> t'"
  proof -
  {
    have a0: "s = s'"
      using p5 client_lookup_endpoint_name_def by auto
    have a1: "t = t'"
      using p6 client_lookup_endpoint_name_def by auto
    have a2: "s' \<sim> d \<sim> t'"
      using a0 a1 p2 by auto
  }
  then show ?thesis by auto
  qed

  lemma client_lookup_endpoint_name_wsc_e:
  assumes p0: "reachable0 s"
    and   p1: "reachable0 t"
    and   p2: "a = (Client_Lookup_Endpoint_Name did ename)"
    and   p3: "s \<sim> d \<sim> t"
    and   p4: "interferes (the (domain_of_event a)) s d"
    and   p5: "s \<sim> did \<sim> t "
    and   p6: "s' = exec_event s a"
    and   p7: "t' = exec_event t a" 
  shows   "s' \<sim> d \<sim> t'"
  proof -
  {
    have a0: "(the (domain_of_event a)) = did"
      using p2 domain_of_event_def by auto
    have a1: "s' = fst (client_lookup_endpoint_name sysconf s did ename)"
      using p2 p6 exec_event_def by auto
    have a2: "t' = fst (client_lookup_endpoint_name sysconf t did ename)"
      using p2 p7 exec_event_def by auto
    have a3: "(interferes did s d)"
      using p4 a0 by auto
    have a4: "s' \<sim> d \<sim> t'"
      using a1 a2 a3 p0 p1 p3 p5 client_lookup_endpoint_name_wsc by blast
  }
  then show ?thesis by auto
  qed

  lemma client_lookup_endpoint_name_dwsc_e: "dynamic_weakly_step_consistent_e (Client_Lookup_Endpoint_Name did ename)"
  proof -
    { 
      have "\<forall>d s t. reachable0 s \<and> reachable0 t 
            \<and> (s \<sim> d \<sim> t) 
            \<and> (interferes (the (domain_of_event (Client_Lookup_Endpoint_Name did ename))) s d) 
            \<and> (s \<sim> (the (domain_of_event (Client_Lookup_Endpoint_Name did ename))) \<sim> t) 
            \<longrightarrow> ((exec_event s (Client_Lookup_Endpoint_Name did ename)) \<sim> d \<sim> (exec_event t (Client_Lookup_Endpoint_Name did ename)))"
        proof -
        {
          fix d s t
          assume p1: "reachable0 s "
          assume p2: "reachable0 t "
          assume p3: "(s \<sim> d \<sim> t) "
          assume p4: "(interferes (the (domain_of_event (Client_Lookup_Endpoint_Name did ename))) s d) "
          assume p5: "(s \<sim> (the (domain_of_event (Client_Lookup_Endpoint_Name did ename))) \<sim> t) "
          have "((exec_event s (Client_Lookup_Endpoint_Name did ename)) \<sim> d \<sim> (exec_event t (Client_Lookup_Endpoint_Name did ename)))"
            by (metis Event.simps(50) client_lookup_endpoint_name_wsc_e domain_of_event_def option.sel p1 p2 p3 p4 p5)
        }
        then show ?thesis by blast
        qed
      }
    then show ?thesis 
      using dynamic_weakly_step_consistent_e_def by blast
  qed

subsubsection{*proving "send queuing message" satisfying the "weakly step consistent" property*}

  lemma send_queuing_message_wsc_domain_cap_set:
  assumes p0: "reachable0 s"
    and   p1: "reachable0 t"
    and   p2: "s \<sim> d \<sim> t"
    and   p3: "interferes did s d"
    and   p4: "s \<sim> did \<sim> t"
    and   p5: "s' = fst (send_queuing_message s did eid m)"
    and   p6: "t' = fst (send_queuing_message t did eid m)"
  shows   "get_domain_cap_set_from_domain_id s' d = get_domain_cap_set_from_domain_id t' d"
  proof -
  {
    have a0: "get_endpoints_of_domain s d = get_endpoints_of_domain t d"
      by (meson p2 vpeq1_def)
    have a1: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v t d)"
      by (meson p2 vpeq1_def)
    have a2: "interferes did t d"
      using p3 a1 by auto
    have a3: "get_domain_cap_set_from_domain_id s d = get_domain_cap_set_from_domain_id t d"
      by (meson p2 vpeq1_def) 
    have "get_domain_cap_set_from_domain_id s' d = get_domain_cap_set_from_domain_id t' d"
      proof (cases "eid \<in> get_endpoints_of_domain s d")
        assume b0: "eid \<in> get_endpoints_of_domain s d"
        have b1: "eid \<in> {x. (domain_endpoint s) x = Some d}"
          using b0 get_endpoints_of_domain_def by auto
        have b2: "(domain_endpoint s) eid = Some d"
          using b1 by auto
        have b3: "get_domain_id_from_endpoint s eid = Some d "
          using b2 get_domain_id_from_endpoint_def by auto
        have b4: "get_domain_id_from_endpoint s eid \<noteq> None "
          using b3 by auto
        have b5: "eid \<in> get_endpoints_of_domain t d"
          using b0 a0 by auto
        have b6: "eid \<in> {x. (domain_endpoint t) x = Some d}"
          using b5 get_endpoints_of_domain_def by auto
        have b7: "(domain_endpoint t) eid = Some d"
          using b6 by auto
        have b8: "get_domain_id_from_endpoint t eid = Some d "
          using b7 get_domain_id_from_endpoint_def by auto
        have b9: "get_domain_id_from_endpoint t eid \<noteq> None "
          using b8 by auto
        have b10: "(the (get_domain_id_from_endpoint s eid)) = d"
          using b3 by auto
        have b11: "(the (get_domain_id_from_endpoint t eid)) = d"
          using b8 by auto
        have b12: "interferes did s (the (get_domain_id_from_endpoint s eid))"
          using p3 b10 by auto
        have b13: "interferes did t (the (get_domain_id_from_endpoint t eid))"
          using a2 b11 by auto
        have b14: "get_domain_cap_set_from_domain_id s d = get_domain_cap_set_from_domain_id s' d"
          using b9 b12 p5 get_domain_cap_set_from_domain_id_def send_queuing_message_def by auto
        have b15: "get_domain_cap_set_from_domain_id t d = get_domain_cap_set_from_domain_id t' d"
          using b10 b13 p6 get_domain_cap_set_from_domain_id_def send_queuing_message_def by auto
        have b16: "get_domain_cap_set_from_domain_id s' d = get_domain_cap_set_from_domain_id t' d"
          using b14 b15 a3 by auto
        then show ?thesis by auto
      next
        assume b0: "eid \<notin> get_endpoints_of_domain s d"
        have b1: "get_domain_cap_set_from_domain_id s d = get_domain_cap_set_from_domain_id s' d"
          using p5 get_domain_cap_set_from_domain_id_def send_queuing_message_def by auto
        have b2: "get_domain_cap_set_from_domain_id t d = get_domain_cap_set_from_domain_id t' d"
          using p6 get_domain_cap_set_from_domain_id_def send_queuing_message_def by auto
        have b16: "get_domain_cap_set_from_domain_id s' d = get_domain_cap_set_from_domain_id t' d"
          using b1 b2 a3 by auto
        then show ?thesis by auto
      qed
    }
    then show ?thesis by auto
  qed

  lemma send_queuing_message_wsc_policy:
  assumes p0: "reachable0 s"
    and   p1: "reachable0 t"
    and   p2: "s \<sim> d \<sim> t"
    and   p3: "interferes did s d"
    and   p4: "s \<sim> did \<sim> t"
    and   p5: "s' = fst (send_queuing_message s did eid m)"
    and   p6: "t' = fst (send_queuing_message t did eid m)"
  shows   "(\<forall>v. interferes v s' d \<longleftrightarrow> interferes v t' d)"
  proof -
  {
    have a0: "get_endpoints_of_domain s d = get_endpoints_of_domain t d"
      by (meson p2 vpeq1_def)
    have a1: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v t d)"
      by (meson p2 vpeq1_def)
    have a2: "interferes did t d"
      using p3 a1 by auto
    have a3: "get_domain_cap_set_from_domain_id s d = get_domain_cap_set_from_domain_id t d"
      by (meson p2 vpeq1_def) 
    have a4: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v s' d)"
      using p0 p5 send_queuing_message_notchg_policy by auto
    have a5: "(\<forall>v. interferes v t d \<longleftrightarrow> interferes v t' d)"
      using p1 p6 send_queuing_message_notchg_policy by auto
    have a6: "(\<forall>v. interferes v s' d \<longleftrightarrow> interferes v t' d)"
      using a1 a4 a5 by auto
    }
    then show ?thesis by auto
  qed

  lemma send_queuing_message_wsc_dom_eps:
  assumes p0: "reachable0 s"
    and   p1: "reachable0 t"
    and   p2: "s \<sim> d \<sim> t"
    and   p3: "interferes did s d"
    and   p4: "s \<sim> did \<sim> t"
    and   p5: "s' = fst (send_queuing_message s did eid m)"
    and   p6: "t' = fst (send_queuing_message t did eid m)"
  shows   "get_endpoints_of_domain s' d = get_endpoints_of_domain t' d"
  proof -
  {
    have a0: "get_endpoints_of_domain s d = get_endpoints_of_domain t d"
      by (meson p2 vpeq1_def)
    have a1: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v t d)"
      by (meson p2 vpeq1_def)
    have a2: "interferes did t d"
      using p3 a1 by auto
    have a3: "get_domain_cap_set_from_domain_id s d = get_domain_cap_set_from_domain_id t d"
      by (meson p2 vpeq1_def) 
    have a4: "get_endpoints_of_domain s d = get_endpoints_of_domain s' d"
      using p0 p5 send_queuing_message_notchg_dom_eps by auto
    have a5: "get_endpoints_of_domain t d = get_endpoints_of_domain t' d"
      using p1 p6 send_queuing_message_notchg_dom_eps by auto
    have a6: "get_endpoints_of_domain s' d = get_endpoints_of_domain t' d"
      using a0 a4 a5 by auto
    }
    then show ?thesis by auto
  qed

  lemma send_queuing_message_wsc_ep_msgs:
  assumes p0: "reachable0 s"
    and   p1: "reachable0 t"
    and   p2: "s \<sim> d \<sim> t"
    and   p3: "interferes did s d"
    and   p4: "s \<sim> did \<sim> t"
    and   p5: "s' = fst (send_queuing_message s did eid m)"
    and   p6: "t' = fst (send_queuing_message t did eid m)"
  shows   "(\<forall>ep. ep\<in>get_endpoints_of_domain s' d 
            \<longrightarrow> get_msg_set_from_endpoint_id s' ep = get_msg_set_from_endpoint_id t' ep )"
  proof -
  {
    have a0: "get_endpoints_of_domain s d = get_endpoints_of_domain t d"
      by (meson p2 vpeq1_def)
    have a1: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v t d)"
      by (meson p2 vpeq1_def)
    have a2: "interferes did t d"
      using p3 a1 by auto
    have a3: "get_domain_cap_set_from_domain_id s d = get_domain_cap_set_from_domain_id t d"
      by (meson p2 vpeq1_def)
    have a4: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id t ep )"
      by (meson p2 vpeq1_def)
    have "(\<forall>ep. ep\<in>get_endpoints_of_domain s' d 
            \<longrightarrow> get_msg_set_from_endpoint_id s' ep = get_msg_set_from_endpoint_id t' ep )"
      proof (cases "eid \<in> get_endpoints_of_domain s d")
        assume b0: "eid \<in> get_endpoints_of_domain s d"
        have b1: "eid \<in> {x. (domain_endpoint s) x = Some d}"
          using b0 get_endpoints_of_domain_def by auto
        have b2: "(domain_endpoint s) eid = Some d"
          using b1 by auto
        have b3: "get_domain_id_from_endpoint s eid = Some d "
          using b2 get_domain_id_from_endpoint_def by auto
        have b4: "get_domain_id_from_endpoint s eid \<noteq> None "
          using b3 by auto
        have b5: "eid \<in> get_endpoints_of_domain t d"
          using b0 a0 by auto
        have b6: "eid \<in> {x. (domain_endpoint t) x = Some d}"
          using b5 get_endpoints_of_domain_def by auto
        have b7: "(domain_endpoint t) eid = Some d"
          using b6 by auto
        have b8: "get_domain_id_from_endpoint t eid = Some d "
          using b7 get_domain_id_from_endpoint_def by auto
        have b9: "get_domain_id_from_endpoint t eid \<noteq> None "
          using b8 by auto
        have b10: "(the (get_domain_id_from_endpoint s eid)) = d"
          using b3 by auto
        have b11: "(the (get_domain_id_from_endpoint t eid)) = d"
          using b8 by auto
        have b12: "interferes did s (the (get_domain_id_from_endpoint s eid))"
          using p3 b10 by auto
        have b13: "interferes did t (the (get_domain_id_from_endpoint t eid))"
          using a2 b11 by auto
        let ?new_msg_set_s = "insert m (get_msg_set_from_endpoint_id s eid)"
        let ?new_msg_set_t = "insert m (get_msg_set_from_endpoint_id t eid)"
        have b14: "(e_msgs s') eid = ?new_msg_set_s"
          using b4 b12 p5 send_queuing_message_def by auto
        have b15: "(e_msgs t') eid = ?new_msg_set_t"
          using b9 b13 p6 send_queuing_message_def by auto
        have b16: "\<forall>e. e\<noteq>eid
            \<longrightarrow> ((e_msgs s) e) = ((e_msgs s') e)"
          using b4 b12 p5 send_queuing_message_def by auto
        have b17: "\<forall>e. e\<noteq>eid
            \<longrightarrow> ((e_msgs t) e) = ((e_msgs t') e)"
          using b9 b13 p6 send_queuing_message_def by auto
        have b18: "\<forall>e. e\<noteq>eid
            \<longrightarrow> get_msg_set_from_endpoint_id s e = get_msg_set_from_endpoint_id s' e"
          using b16 get_msg_set_from_endpoint_id_def by auto
        have b19: "\<forall>e. e\<noteq>eid
            \<longrightarrow> get_msg_set_from_endpoint_id t e = get_msg_set_from_endpoint_id t' e"
          using b17 get_msg_set_from_endpoint_id_def by auto
        have b20: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d \<and> ep \<noteq> eid
            \<longrightarrow> get_msg_set_from_endpoint_id s' ep = get_msg_set_from_endpoint_id t' ep )"
          using a4 b19 b18 by auto
        have b21: "get_msg_set_from_endpoint_id s eid = get_msg_set_from_endpoint_id t eid"
          using a4 b0 b5 by auto
        have b22: "(e_msgs s') eid = (e_msgs t') eid"
          using b21 b14 b15 by auto
        have b23: "get_msg_set_from_endpoint_id s' eid = get_msg_set_from_endpoint_id t' eid"
          using b22 get_msg_set_from_endpoint_id_def by auto
        have b24: "get_endpoints_of_domain s d = get_endpoints_of_domain s' d"
          using p0 p5 send_queuing_message_notchg_dom_eps by auto
        have b25: "(\<forall>ep. ep\<in>get_endpoints_of_domain s' d 
            \<longrightarrow> get_msg_set_from_endpoint_id s' ep = get_msg_set_from_endpoint_id t' ep )"
          using b23 b24 b20 by auto
        then show ?thesis by auto
      next
        assume b0: "eid \<notin> get_endpoints_of_domain s d"
        have b1: "\<forall>e. e\<noteq>eid
            \<longrightarrow> ((e_msgs s) e) = ((e_msgs s') e)"
          using p5 send_queuing_message_def by auto
        have b2: "\<forall>e. e\<noteq>eid
            \<longrightarrow> ((e_msgs t) e) = ((e_msgs t') e)"
          using p6 send_queuing_message_def by auto    
        have b3: "\<forall>e. e\<noteq>eid
            \<longrightarrow> get_msg_set_from_endpoint_id s e = get_msg_set_from_endpoint_id s' e"
          using b1 get_msg_set_from_endpoint_id_def by auto
        have b4: "\<forall>e. e\<noteq>eid
            \<longrightarrow> get_msg_set_from_endpoint_id t e = get_msg_set_from_endpoint_id t' e"
          using b2 get_msg_set_from_endpoint_id_def by auto
        have b5: "\<forall>e. e\<in>get_endpoints_of_domain s d \<and> e\<noteq>eid
            \<longrightarrow> get_msg_set_from_endpoint_id s' e = get_msg_set_from_endpoint_id t' e"
          using b3 b4 a4 by auto
        have b6: "\<forall>e. e\<in>get_endpoints_of_domain s d
            \<longrightarrow> get_msg_set_from_endpoint_id s' e = get_msg_set_from_endpoint_id t' e"
          using b5 b0 by auto
        have b7: "get_endpoints_of_domain s d = get_endpoints_of_domain s' d"
          using p0 p5 send_queuing_message_notchg_dom_eps by auto
        have b8: "\<forall>e. e\<in>get_endpoints_of_domain s' d
            \<longrightarrow> get_msg_set_from_endpoint_id s' e = get_msg_set_from_endpoint_id t' e"
          using b7 b6 by auto
        then show ?thesis by auto
      qed
    }
    then show ?thesis by auto
  qed
   
  lemma send_queuing_message_wsc:
  assumes p0: "reachable0 s"
    and   p1: "reachable0 t"
    and   p2: "s \<sim> d \<sim> t"
    and   p3: "interferes did s d"
    and   p4: "s \<sim> did \<sim> t"
    and   p5: "s' = fst (send_queuing_message s did eid m)"
    and   p6: "t' = fst (send_queuing_message t did eid m)"
  shows   "s' \<sim> d \<sim> t'"
  proof -
  {
    have a0: "get_domain_cap_set_from_domain_id s' d = get_domain_cap_set_from_domain_id t' d"
      using p0 p1 p2 p3 p4 p5 p6 send_queuing_message_wsc_domain_cap_set by blast
    have a1: "(\<forall>v. interferes v s' d \<longleftrightarrow> interferes v t' d)"
      using p0 p1 p2 p3 p4 p5 p6 send_queuing_message_wsc_policy by blast
    have a2: "get_endpoints_of_domain s' d = get_endpoints_of_domain t' d"
      using p0 p1 p2 p3 p4 p5 p6 send_queuing_message_wsc_dom_eps by blast
    have a3: "(\<forall>ep. ep\<in>get_endpoints_of_domain s' d 
            \<longrightarrow> get_msg_set_from_endpoint_id s' ep = get_msg_set_from_endpoint_id t' ep )"
      using p0 p1 p2 p3 p4 p5 p6 send_queuing_message_wsc_ep_msgs by blast
    have a4: "s' \<sim> d \<sim> t'"
      using a0 a1 a2 a3 vpeq1_def by auto
  }
  then show ?thesis by auto
  qed


  lemma send_queuing_message_wsc_e:
  assumes p0: "reachable0 s"
    and   p1: "reachable0 t"
    and   p2: "a = (Send_Queuing_Message did eid m)"
    and   p3: "s \<sim> d \<sim> t"
    and   p4: "interferes (the (domain_of_event a)) s d"
    and   p5: "s \<sim> did \<sim> t "
    and   p6: "s' = exec_event s a"
    and   p7: "t' = exec_event t a" 
  shows   "s' \<sim> d \<sim> t'"
  proof -
  {
    have a0: "(the (domain_of_event a)) = did"
      using p2 domain_of_event_def by auto
    have a1: "s' = fst (send_queuing_message s did eid m)"
      using p2 p6 exec_event_def by auto
    have a2: "t' = fst (send_queuing_message t did eid m)"
      using p2 p7 exec_event_def by auto
    have a3: "(interferes did s d)"
      using p4 a0 by auto
    have a4: "s' \<sim> d \<sim> t'"
      using a1 a2 a3 p0 p1 p3 p5 send_queuing_message_wsc by blast
  }
  then show ?thesis by auto
  qed

  lemma send_queuing_message_dwsc_e: "dynamic_weakly_step_consistent_e (Send_Queuing_Message did eid m)"
  proof -
    { 
      have "\<forall>d s t. reachable0 s \<and> reachable0 t 
            \<and> (s \<sim> d \<sim> t) 
            \<and> (interferes (the (domain_of_event (Send_Queuing_Message did eid m))) s d) 
            \<and> (s \<sim> (the (domain_of_event (Send_Queuing_Message did eid m))) \<sim> t) 
            \<longrightarrow> ((exec_event s (Send_Queuing_Message did eid m)) \<sim> d \<sim> (exec_event t (Send_Queuing_Message did eid m)))"
        proof -
        {
          fix d s t
          assume p1: "reachable0 s "
          assume p2: "reachable0 t "
          assume p3: "(s \<sim> d \<sim> t) "
          assume p4: "(interferes (the (domain_of_event (Send_Queuing_Message did eid m))) s d) "
          assume p5: "(s \<sim> (the (domain_of_event (Send_Queuing_Message did eid m))) \<sim> t) "
          have "((exec_event s (Send_Queuing_Message did eid m)) \<sim> d \<sim> (exec_event t (Send_Queuing_Message did eid m)))"
            by (metis Event.simps(51) domain_of_event_def option.sel p1 p2 p3 p4 p5 send_queuing_message_wsc_e)
        }
        then show ?thesis by blast
        qed
      }
    then show ?thesis 
      using dynamic_weakly_step_consistent_e_def by blast
  qed

subsubsection{*proving "receive queuing message" satisfying the "weakly step consistent" property*}

  lemma receive_queuing_message_wsc_domain_cap_set:
  assumes p0: "reachable0 s"
    and   p1: "reachable0 t"
    and   p2: "s \<sim> d \<sim> t"
    and   p3: "interferes did s d"
    and   p4: "s \<sim> did \<sim> t"
    and   p5: "s' = fst (receive_queuing_message s did eid)"
    and   p6: "t' = fst (receive_queuing_message t did eid)"
  shows   "get_domain_cap_set_from_domain_id s' d = get_domain_cap_set_from_domain_id t' d"
  proof -
  {
    have a0: "get_endpoints_of_domain s d = get_endpoints_of_domain t d"
      by (meson p2 vpeq1_def)
    have a1: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v t d)"
      by (meson p2 vpeq1_def)
    have a2: "interferes did t d"
      using p3 a1 by auto
    have a3: "get_domain_cap_set_from_domain_id s d = get_domain_cap_set_from_domain_id t d"
      by (meson p2 vpeq1_def) 
    have a4: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id t ep )"
      by (meson p2 vpeq1_def) 
    have a5: "get_endpoints_of_domain s did = get_endpoints_of_domain t did"
      by (meson p4 vpeq1_def)
    have a6: "get_domain_cap_set_from_domain_id s' d = get_domain_cap_set_from_domain_id t' d"
      proof (cases "get_domain_id_from_endpoint s eid = Some did")
        assume b0: "get_domain_id_from_endpoint s eid = Some did"
        have b1: "((domain_endpoint s) eid) = Some did"
          using b0 get_domain_id_from_endpoint_def by auto
        have b2: "{x. (domain_endpoint s) x = Some did} = {x. (domain_endpoint t) x = Some did}"
          using a5 b1 get_endpoints_of_domain_def by auto 
        have b3: "((domain_endpoint t) eid) = Some did"
          using b1 b2 by auto
        have b4: "get_domain_id_from_endpoint t eid = Some did"
          using b3 get_domain_id_from_endpoint_def by auto
        have b5: "get_domain_cap_set_from_domain_id s d = get_domain_cap_set_from_domain_id s' d"
          using b0 p5 get_domain_cap_set_from_domain_id_def receive_queuing_message_def by auto
        have b6: "get_domain_cap_set_from_domain_id t d = get_domain_cap_set_from_domain_id t' d"
          using b4 p6 get_domain_cap_set_from_domain_id_def receive_queuing_message_def by auto
        have b7: "get_domain_cap_set_from_domain_id s' d = get_domain_cap_set_from_domain_id t' d"
          using b5 b6 a3 by auto
        then show ?thesis by auto
      next
        assume b0: "get_domain_id_from_endpoint s eid \<noteq> Some did"
        have b1: "((domain_endpoint s) eid) \<noteq> Some did"
          using b0 get_domain_id_from_endpoint_def by auto
        have b2: "{x. (domain_endpoint s) x = Some did} = {x. (domain_endpoint t) x = Some did}"
          using a5 b1 get_endpoints_of_domain_def by auto 
        have b3: "((domain_endpoint t) eid) \<noteq> Some did"
          using b1 b2 by auto
        have b4: "get_domain_id_from_endpoint t eid \<noteq> Some did"
          using b3 get_domain_id_from_endpoint_def by auto
        have b5: "get_domain_cap_set_from_domain_id s d = get_domain_cap_set_from_domain_id s' d"
          using b0 p5 get_domain_cap_set_from_domain_id_def receive_queuing_message_def by auto
        have b6: "get_domain_cap_set_from_domain_id t d = get_domain_cap_set_from_domain_id t' d"
          using b4 p6 get_domain_cap_set_from_domain_id_def receive_queuing_message_def by auto
        have b7: "get_domain_cap_set_from_domain_id s' d = get_domain_cap_set_from_domain_id t' d"
          using b5 b6 a3 by auto
        then show ?thesis by auto
      qed
    }
    then show ?thesis by auto
  qed  

  lemma receive_queuing_message_wsc_policy:
  assumes p0: "reachable0 s"
    and   p1: "reachable0 t"
    and   p2: "s \<sim> d \<sim> t"
    and   p3: "interferes did s d"
    and   p4: "s \<sim> did \<sim> t"
    and   p5: "s' = fst (receive_queuing_message s did eid)"
    and   p6: "t' = fst (receive_queuing_message t did eid)"
  shows   "(\<forall>v. interferes v s' d \<longleftrightarrow> interferes v t' d)"
  proof -
  {
    have a0: "get_endpoints_of_domain s d = get_endpoints_of_domain t d"
      by (meson p2 vpeq1_def)
    have a1: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v t d)"
      by (meson p2 vpeq1_def)
    have a2: "interferes did t d"
      using p3 a1 by auto
    have a3: "get_domain_cap_set_from_domain_id s d = get_domain_cap_set_from_domain_id t d"
      by (meson p2 vpeq1_def) 
    have a4: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id t ep )"
      by (meson p2 vpeq1_def) 
    have a5: "get_endpoints_of_domain s did = get_endpoints_of_domain t did"
      by (meson p4 vpeq1_def)
    have a6: "(\<forall>v. interferes v s' d \<longleftrightarrow> interferes v t' d)"
      proof (cases "get_domain_id_from_endpoint s eid = Some did")
        assume b0: "get_domain_id_from_endpoint s eid = Some did"
        have b1: "((domain_endpoint s) eid) = Some did"
          using b0 get_domain_id_from_endpoint_def by auto
        have b2: "{x. (domain_endpoint s) x = Some did} = {x. (domain_endpoint t) x = Some did}"
          using a5 b1 get_endpoints_of_domain_def by auto 
        have b3: "((domain_endpoint t) eid) = Some did"
          using b1 b2 by auto
        have b4: "get_domain_id_from_endpoint t eid = Some did"
          using b3 get_domain_id_from_endpoint_def by auto
        have b5: "get_domain_cap_set_from_domain_id s d = get_domain_cap_set_from_domain_id s' d"
          using b0 p5 get_domain_cap_set_from_domain_id_def receive_queuing_message_def by auto
        have b6: "get_domain_cap_set_from_domain_id t d = get_domain_cap_set_from_domain_id t' d"
          using b4 p6 get_domain_cap_set_from_domain_id_def receive_queuing_message_def by auto
        have b7: "get_domain_cap_set_from_domain_id s' d = get_domain_cap_set_from_domain_id t' d"
          using b5 b6 a3 by auto
        have b8: "\<forall>v. get_domain_cap_set_from_domain_id s v 
           = get_domain_cap_set_from_domain_id s' v"
          using b0 p5 get_domain_cap_set_from_domain_id_def receive_queuing_message_def by auto
        have b9: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v s' d)"
          using b5 b8 interferes_def by auto
        have b10: "\<forall>v. get_domain_cap_set_from_domain_id t v 
           = get_domain_cap_set_from_domain_id t' v"
          using b4 p6 get_domain_cap_set_from_domain_id_def receive_queuing_message_def by auto
        have b11: "(\<forall>v. interferes v t d \<longleftrightarrow> interferes v t' d)"
          using b6 b10 interferes_def by auto
        have b12: "(\<forall>v. interferes v s' d \<longleftrightarrow> interferes v t' d)"
          using b9 b11 a1 by auto
        then show ?thesis by auto
      next
        assume b0: "get_domain_id_from_endpoint s eid \<noteq> Some did"
        have b1: "((domain_endpoint s) eid) \<noteq> Some did"
          using b0 get_domain_id_from_endpoint_def by auto
        have b2: "{x. (domain_endpoint s) x = Some did} = {x. (domain_endpoint t) x = Some did}"
          using a5 b1 get_endpoints_of_domain_def by auto 
        have b3: "((domain_endpoint t) eid) \<noteq> Some did"
          using b1 b2 by auto
        have b4: "get_domain_id_from_endpoint t eid \<noteq> Some did"
          using b3 get_domain_id_from_endpoint_def by auto
        have b5: "get_domain_cap_set_from_domain_id s d = get_domain_cap_set_from_domain_id s' d"
          using b0 p5 get_domain_cap_set_from_domain_id_def receive_queuing_message_def by auto
        have b6: "get_domain_cap_set_from_domain_id t d = get_domain_cap_set_from_domain_id t' d"
          using b4 p6 get_domain_cap_set_from_domain_id_def receive_queuing_message_def by auto
        have b7: "get_domain_cap_set_from_domain_id s' d = get_domain_cap_set_from_domain_id t' d"
          using b5 b6 a3 by auto
        have b8: "\<forall>v. get_domain_cap_set_from_domain_id s v 
           = get_domain_cap_set_from_domain_id s' v"
          using b0 p5 get_domain_cap_set_from_domain_id_def receive_queuing_message_def by auto
        have b9: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v s' d)"
          using b5 b8 interferes_def by auto
        have b10: "\<forall>v. get_domain_cap_set_from_domain_id t v 
           = get_domain_cap_set_from_domain_id t' v"
          using b4 p6 get_domain_cap_set_from_domain_id_def receive_queuing_message_def by auto
        have b11: "(\<forall>v. interferes v t d \<longleftrightarrow> interferes v t' d)"
          using b6 b10 interferes_def by auto
        have b12: "(\<forall>v. interferes v s' d \<longleftrightarrow> interferes v t' d)"
          using b9 b11 a1 by auto
        then show ?thesis by auto
      qed
    }
    then show ?thesis by auto
  qed

  lemma receive_queuing_message_wsc_dom_eps:
  assumes p0: "reachable0 s"
    and   p1: "reachable0 t"
    and   p2: "s \<sim> d \<sim> t"
    and   p3: "interferes did s d"
    and   p4: "s \<sim> did \<sim> t"
    and   p5: "s' = fst (receive_queuing_message s did eid)"
    and   p6: "t' = fst (receive_queuing_message t did eid)"
  shows   "get_endpoints_of_domain s' d = get_endpoints_of_domain t' d"
  proof -
  {
    have a0: "get_endpoints_of_domain s d = get_endpoints_of_domain t d"
      by (meson p2 vpeq1_def)
    have a1: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v t d)"
      by (meson p2 vpeq1_def)
    have a2: "interferes did t d"
      using p3 a1 by auto
    have a3: "get_domain_cap_set_from_domain_id s d = get_domain_cap_set_from_domain_id t d"
      by (meson p2 vpeq1_def) 
    have a4: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id t ep )"
      by (meson p2 vpeq1_def) 
    have a5: "get_endpoints_of_domain s did = get_endpoints_of_domain t did"
      by (meson p4 vpeq1_def)
    have a6: "get_endpoints_of_domain s' d = get_endpoints_of_domain t' d"
      proof (cases "get_domain_id_from_endpoint s eid = Some did")
        assume b0: "get_domain_id_from_endpoint s eid = Some did"
        have b1: "((domain_endpoint s) eid) = Some did"
          using b0 get_domain_id_from_endpoint_def by auto
        have b2: "{x. (domain_endpoint s) x = Some did} = {x. (domain_endpoint t) x = Some did}"
          using a5 b1 get_endpoints_of_domain_def by auto 
        have b3: "((domain_endpoint t) eid) = Some did"
          using b1 b2 by auto
        have b4: "get_domain_id_from_endpoint t eid = Some did"
          using b3 get_domain_id_from_endpoint_def by auto
        have b5: "get_endpoints_of_domain s d = get_endpoints_of_domain s' d"
          using b0 p5 get_endpoints_of_domain_def receive_queuing_message_def by auto
        have b6: "get_endpoints_of_domain t d = get_endpoints_of_domain t' d"
          using b4 p6 get_endpoints_of_domain_def receive_queuing_message_def by auto
        have b7: "get_endpoints_of_domain s' d = get_endpoints_of_domain t' d"
          using b5 b6 a0 by auto
        then show ?thesis by auto
      next
        assume b0: "get_domain_id_from_endpoint s eid \<noteq> Some did"
        have b1: "((domain_endpoint s) eid) \<noteq> Some did"
          using b0 get_domain_id_from_endpoint_def by auto
        have b2: "{x. (domain_endpoint s) x = Some did} = {x. (domain_endpoint t) x = Some did}"
          using a5 b1 get_endpoints_of_domain_def by auto 
        have b3: "((domain_endpoint t) eid) \<noteq> Some did"
          using b1 b2 by auto
        have b4: "get_domain_id_from_endpoint t eid \<noteq> Some did"
          using b3 get_domain_id_from_endpoint_def by auto
        have b5: "get_endpoints_of_domain s d = get_endpoints_of_domain s' d"
          using b0 p5 get_endpoints_of_domain_def receive_queuing_message_def by auto
        have b6: "get_endpoints_of_domain t d = get_endpoints_of_domain t' d"
          using b4 p6 get_endpoints_of_domain_def receive_queuing_message_def by auto
        have b7: "get_endpoints_of_domain s' d = get_endpoints_of_domain t' d"
          using b5 b6 a0 by auto
        then show ?thesis by auto
      qed
    }
    then show ?thesis by auto
  qed

  lemma receive_queuing_message_wsc_ep_msgs:
  assumes p0: "reachable0 s"
    and   p1: "reachable0 t"
    and   p2: "s \<sim> d \<sim> t"
    and   p3: "interferes did s d"
    and   p4: "s \<sim> did \<sim> t"
    and   p5: "s' = fst (receive_queuing_message s did eid)"
    and   p6: "t' = fst (receive_queuing_message t did eid)"
  shows   "(\<forall>ep. ep\<in>get_endpoints_of_domain s' d 
            \<longrightarrow> get_msg_set_from_endpoint_id s' ep = get_msg_set_from_endpoint_id t' ep )"
  proof -
  {
    have a0: "get_endpoints_of_domain s d = get_endpoints_of_domain t d"
      by (meson p2 vpeq1_def)
    have a1: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v t d)"
      by (meson p2 vpeq1_def)
    have a2: "interferes did t d"
      using p3 a1 by auto
    have a3: "get_domain_cap_set_from_domain_id s d = get_domain_cap_set_from_domain_id t d"
      by (meson p2 vpeq1_def) 
    have a4: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id t ep )"
      by (meson p2 vpeq1_def) 
    have a5: "get_endpoints_of_domain s did = get_endpoints_of_domain t did"
      by (meson p4 vpeq1_def)
    have a6: "(\<forall>ep. ep\<in>get_endpoints_of_domain s did 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id t ep )"
      by (meson p4 vpeq1_def) 
    have "(\<forall>ep. ep\<in>get_endpoints_of_domain s' d 
            \<longrightarrow> get_msg_set_from_endpoint_id s' ep = get_msg_set_from_endpoint_id t' ep )"
      proof (cases "get_domain_id_from_endpoint s eid = Some did")
        assume b0: "get_domain_id_from_endpoint s eid = Some did"
        have b1: "((domain_endpoint s) eid) = Some did"
          using b0 get_domain_id_from_endpoint_def by auto
        have b2: "{x. (domain_endpoint s) x = Some did} = {x. (domain_endpoint t) x = Some did}"
          using a5 b1 get_endpoints_of_domain_def by auto 
        have b3: "((domain_endpoint t) eid) = Some did"
          using b1 b2 by auto
        have b4: "get_domain_id_from_endpoint t eid = Some did"
          using b3 get_domain_id_from_endpoint_def by auto
        have "(\<forall>ep. ep\<in>get_endpoints_of_domain s' d 
            \<longrightarrow> get_msg_set_from_endpoint_id s' ep = get_msg_set_from_endpoint_id t' ep )"
          proof (cases "d \<noteq> did")
          assume c0: "d \<noteq> did"
          have c1: "\<forall>e. e\<noteq>eid
            \<longrightarrow> ((e_msgs s) e) = ((e_msgs s') e)"
            using b0 p5 receive_queuing_message_def by auto
          have c2: "get_domain_id_from_endpoint s eid \<noteq> Some d"
            using c0 b0 by auto
          have c3: "((domain_endpoint s) eid) \<noteq> Some d"
            using c2 get_domain_id_from_endpoint_def by auto
          have c4: "eid \<notin> {x. (domain_endpoint s) x = Some d}"
            using c3 by auto
          have c5: "eid \<notin> get_endpoints_of_domain s d"
            using c4 get_endpoints_of_domain_def by auto
          have c6: "\<forall>e. e\<in>get_endpoints_of_domain s d
            \<longrightarrow> ((e_msgs s) e) = ((e_msgs s') e)"
            using c1 c5 by auto
          have c7: "\<forall>e. e\<in>get_endpoints_of_domain s d
            \<longrightarrow> get_msg_set_from_endpoint_id s e 
              = get_msg_set_from_endpoint_id s' e"
            using c6 get_msg_set_from_endpoint_id_def by auto
          have c8: "\<forall>e. e\<noteq>eid
            \<longrightarrow> ((e_msgs t) e) = ((e_msgs t') e)"
            using b4 p6 receive_queuing_message_def by auto
          have c9: "get_domain_id_from_endpoint t eid \<noteq> Some d"
            using c0 b4 by auto
          have c10: "((domain_endpoint t) eid) \<noteq> Some d"
            using c9 get_domain_id_from_endpoint_def by auto
          have c11: "eid \<notin> {x. (domain_endpoint t) x = Some d}"
            using c10 by auto
          have c12: "eid \<notin> get_endpoints_of_domain t d"
            using c11 get_endpoints_of_domain_def by auto
          have c13: "\<forall>e. e\<in>get_endpoints_of_domain t d
            \<longrightarrow> ((e_msgs t) e) = ((e_msgs t') e)"
            using c8 c12 by auto
          have c14: "\<forall>e. e\<in>get_endpoints_of_domain t d
            \<longrightarrow> get_msg_set_from_endpoint_id t e 
              = get_msg_set_from_endpoint_id t' e"
            using c13 get_msg_set_from_endpoint_id_def by auto
          have c15: "\<forall>e. e\<in>get_endpoints_of_domain s d
            \<longrightarrow> get_msg_set_from_endpoint_id t e 
              = get_msg_set_from_endpoint_id t' e"
            using c14 a0 by auto
          have c16: "\<forall>e. e\<in>get_endpoints_of_domain s d
            \<longrightarrow> get_msg_set_from_endpoint_id s' e 
              = get_msg_set_from_endpoint_id t' e"
            using c15 c7 a4 by auto
          have c17: "get_endpoints_of_domain s d = get_endpoints_of_domain s' d"
            using p0 p5 receive_queuing_message_notchg_dom_eps by auto
          have c18: "\<forall>e. e\<in>get_endpoints_of_domain s' d
            \<longrightarrow> get_msg_set_from_endpoint_id s' e 
              = get_msg_set_from_endpoint_id t' e"
            using c16 c17 by auto
          then show ?thesis by auto
        next
          assume c0: "\<not> d \<noteq> did"
          have c1: "\<forall>e. e\<noteq>eid
            \<longrightarrow> ((e_msgs s) e) = ((e_msgs s') e)"
            using b0 p5 receive_queuing_message_def by auto
          have c2: "\<forall>e. e\<noteq>eid 
            \<longrightarrow> ((e_msgs t) e) = ((e_msgs t') e)"
            using b4 p6 receive_queuing_message_def by auto
          have c3: "\<forall>e. e\<noteq>eid \<and> e\<in>get_endpoints_of_domain s d
            \<longrightarrow> ((e_msgs s') e) = ((e_msgs t') e)"
            using c1 c2 a4 get_msg_set_from_endpoint_id_def by auto
          let ?msg_set_s = "get_msg_set_from_endpoint_id s eid"
          let ?m_s = "SOME x. x\<in>?msg_set_s"
          let ?new_msg_set_s = "?msg_set_s - {?m_s}"
          let ?msg_set_t = "get_msg_set_from_endpoint_id t eid"
          let ?m_t = "SOME x. x\<in>?msg_set_t"
          let ?new_msg_set_t = "?msg_set_t - {?m_t}"
          have c4: "((e_msgs s') eid) = ?new_msg_set_s"
            using b0 p5 receive_queuing_message_def by auto
          have c5: "eid \<in> get_endpoints_of_domain s did"
            using b1 get_endpoints_of_domain_def by auto
          have c6: "get_msg_set_from_endpoint_id s eid 
                  = get_msg_set_from_endpoint_id t eid"
            using a6 c5 by auto
          have c7: "?msg_set_s = ?msg_set_t"
            using c6 by auto
          have c8: "?m_s = ?m_t"
            using c7 by auto
          have c9: "?new_msg_set_s = ?new_msg_set_t"
            using c7 c8 by auto
          have c10: "((e_msgs t') eid) = ?new_msg_set_t"
            using b4 p6 receive_queuing_message_def by auto
          have c11: "((e_msgs s') eid) = ((e_msgs t') eid)"
            using c4 c9 c10 by auto
          have c12: "get_msg_set_from_endpoint_id s' eid 
                   = get_msg_set_from_endpoint_id t' eid"
            using c11 get_msg_set_from_endpoint_id_def by auto
          have c13: "\<forall>e. e\<in>get_endpoints_of_domain s d
                      \<longrightarrow> ((e_msgs s') e) = ((e_msgs t') e)"
            using c3 c11 by auto
          have c14: "\<forall>e. e\<in>get_endpoints_of_domain s d
                        \<longrightarrow> get_msg_set_from_endpoint_id s' e  
                        = get_msg_set_from_endpoint_id t' e"
            using c13 get_msg_set_from_endpoint_id_def by auto
          have c15: "get_endpoints_of_domain s d = get_endpoints_of_domain s' d"
            using p0 p5 receive_queuing_message_notchg_dom_eps by auto
          have c16: "\<forall>e. e\<in>get_endpoints_of_domain s' d
                        \<longrightarrow> get_msg_set_from_endpoint_id s' e  
                        = get_msg_set_from_endpoint_id t' e"
            using c14 c15 by auto
          then show ?thesis by auto
        qed
        then show ?thesis by auto
      next
        assume b0: "get_domain_id_from_endpoint s eid \<noteq> Some did"
        have b1: "((domain_endpoint s) eid) \<noteq> Some did"
          using b0 get_domain_id_from_endpoint_def by auto
        have b2: "{x. (domain_endpoint s) x = Some did} = {x. (domain_endpoint t) x = Some did}"
          using a5 b1 get_endpoints_of_domain_def by auto 
        have b3: "((domain_endpoint t) eid) \<noteq> Some did"
          using b1 b2 by auto
        have b4: "get_domain_id_from_endpoint t eid \<noteq> Some did"
          using b3 get_domain_id_from_endpoint_def by auto
        have b5: "\<forall>e. ((e_msgs s) e) = ((e_msgs s') e)"
          using b0 p5 receive_queuing_message_def by auto
        have b6: "\<forall>e. ((e_msgs t) e) = ((e_msgs t') e)"
          using b4 p6 receive_queuing_message_def by auto
        have b7: "\<forall>e. e\<in>get_endpoints_of_domain s d
                   \<longrightarrow> get_msg_set_from_endpoint_id s' e  
                     = get_msg_set_from_endpoint_id t' e"
          using b5 b6 a4 get_msg_set_from_endpoint_id_def by auto
        have b8: "get_endpoints_of_domain s d = get_endpoints_of_domain s' d"
          using p0 p5 receive_queuing_message_notchg_dom_eps by auto
        have b9: "\<forall>e. e\<in>get_endpoints_of_domain s' d
                   \<longrightarrow> get_msg_set_from_endpoint_id s' e  
                     = get_msg_set_from_endpoint_id t' e"
          using b7 b8 by auto
        then show ?thesis by auto
      qed
    }
    then show ?thesis by auto
  qed

  lemma receive_queuing_message_wsc:
  assumes p0: "reachable0 s"
    and   p1: "reachable0 t"
    and   p2: "s \<sim> d \<sim> t"
    and   p3: "interferes did s d"
    and   p4: "s \<sim> did \<sim> t"
    and   p5: "s' = fst (receive_queuing_message s did eid)"
    and   p6: "t' = fst (receive_queuing_message t did eid)"
  shows   "s' \<sim> d \<sim> t'"
  proof -
  {
    have a0: "get_domain_cap_set_from_domain_id s' d = get_domain_cap_set_from_domain_id t' d"
      using p0 p1 p2 p3 p4 p5 p6 receive_queuing_message_wsc_domain_cap_set by blast
    have a1: "(\<forall>v. interferes v s' d \<longleftrightarrow> interferes v t' d)"
      using p0 p1 p2 p3 p4 p5 p6 receive_queuing_message_wsc_policy by blast
    have a2: "get_endpoints_of_domain s' d = get_endpoints_of_domain t' d"
      using p0 p1 p2 p3 p4 p5 p6 receive_queuing_message_wsc_dom_eps by blast
    have a3: "(\<forall>ep. ep\<in>get_endpoints_of_domain s' d 
            \<longrightarrow> get_msg_set_from_endpoint_id s' ep = get_msg_set_from_endpoint_id t' ep )"
      using p0 p1 p2 p3 p4 p5 p6 receive_queuing_message_wsc_ep_msgs by blast
    have a4: "s' \<sim> d \<sim> t'"
      using a0 a1 a2 a3 vpeq1_def by auto
  }
  then show ?thesis by auto
  qed


  lemma receive_queuing_message_wsc_e:
  assumes p0: "reachable0 s"
    and   p1: "reachable0 t"
    and   p2: "a = (Receive_Queuing_Message did eid)"
    and   p3: "s \<sim> d \<sim> t"
    and   p4: "interferes (the (domain_of_event a)) s d"
    and   p5: "s \<sim> did \<sim> t "
    and   p6: "s' = exec_event s a"
    and   p7: "t' = exec_event t a" 
  shows   "s' \<sim> d \<sim> t'"
  proof -
  {
    have a0: "(the (domain_of_event a)) = did"
      using p2 domain_of_event_def by auto
    have a1: "s' = fst (receive_queuing_message s did eid)"
      using p2 p6 exec_event_def by auto
    have a2: "t' = fst (receive_queuing_message t did eid)"
      using p2 p7 exec_event_def by auto
    have a3: "(interferes did s d)"
      using p4 a0 by auto
    have a4: "s' \<sim> d \<sim> t'"
      using a1 a2 a3 p0 p1 p3 p5 receive_queuing_message_wsc by blast
  }
  then show ?thesis by auto
  qed

  lemma receive_queuing_message_dwsc_e: "dynamic_weakly_step_consistent_e (Receive_Queuing_Message did eid)"
  proof -
    { 
      have "\<forall>d s t. reachable0 s \<and> reachable0 t 
            \<and> (s \<sim> d \<sim> t) 
            \<and> (interferes (the (domain_of_event (Receive_Queuing_Message did eid))) s d) 
            \<and> (s \<sim> (the (domain_of_event (Receive_Queuing_Message did eid))) \<sim> t) 
            \<longrightarrow> ((exec_event s (Receive_Queuing_Message did eid)) \<sim> d \<sim> (exec_event t (Receive_Queuing_Message did eid)))"
        proof -
        {
          fix d s t
          assume p1: "reachable0 s "
          assume p2: "reachable0 t "
          assume p3: "(s \<sim> d \<sim> t) "
          assume p4: "(interferes (the (domain_of_event (Receive_Queuing_Message did eid))) s d) "
          assume p5: "(s \<sim> (the (domain_of_event (Receive_Queuing_Message did eid))) \<sim> t) "
          have "((exec_event s (Receive_Queuing_Message did eid)) \<sim> d \<sim> (exec_event t (Receive_Queuing_Message did eid)))"
            by (metis Event.simps(52) domain_of_event_def option.sel p1 p2 p3 p4 p5 receive_queuing_message_wsc_e)
        }
        then show ?thesis by blast
        qed
      }
    then show ?thesis 
      using dynamic_weakly_step_consistent_e_def by blast
  qed

subsubsection{*proving "get my endpoints set" satisfying the "weakly step consistent" property*}

  lemma get_my_endpoints_set_wsc:
  assumes p0: "reachable0 s"
    and   p1: "reachable0 t"
    and   p2: "s \<sim> d \<sim> t"
    and   p3: "interferes did s d"
    and   p4: "s \<sim> did \<sim> t "
    and   p5: "s' = fst (get_my_endpoints_set s did)"
    and   p6: "t' = fst (get_my_endpoints_set t did)"
  shows   "s' \<sim> d \<sim> t'"
  proof -
  {
    have a0: "s = s'"
      using p5 get_my_endpoints_set_def by auto
    have a1: "t = t'"
      using p6 get_my_endpoints_set_def by auto
    have a2: "s' \<sim> d \<sim> t'"
      using a0 a1 p2 by auto
  }
  then show ?thesis by auto
  qed


  lemma get_my_endpoints_set_wsc_e:
  assumes p0: "reachable0 s"
    and   p1: "reachable0 t"
    and   p2: "a = (Get_My_Endpoints_Set did)"
    and   p3: "s \<sim> d \<sim> t"
    and   p4: "interferes (the (domain_of_event a)) s d"
    and   p5: "s \<sim> did \<sim> t "
    and   p6: "s' = exec_event s a"
    and   p7: "t' = exec_event t a" 
  shows   "s' \<sim> d \<sim> t'"
  proof -
  {
    have a0: "(the (domain_of_event a)) = did"
      using p2 domain_of_event_def by auto
    have a1: "s' = fst (get_my_endpoints_set s did)"
      using p2 p6 exec_event_def by auto
    have a2: "t' = fst (get_my_endpoints_set t did)"
      using p2 p7 exec_event_def by auto
    have a3: "(interferes did s d)"
      using p4 a0 by auto
    have a4: "s' \<sim> d \<sim> t'"
      using a1 a2 a3 p0 p1 p3 p5 get_my_endpoints_set_wsc by blast
  }
  then show ?thesis by auto
  qed

  lemma get_my_endpoints_set_dwsc_e: "dynamic_weakly_step_consistent_e (Get_My_Endpoints_Set did)"
  proof -
    { 
      have "\<forall>d s t. reachable0 s \<and> reachable0 t 
            \<and> (s \<sim> d \<sim> t) 
            \<and> (interferes (the (domain_of_event (Get_My_Endpoints_Set did))) s d) 
            \<and> (s \<sim> (the (domain_of_event (Get_My_Endpoints_Set did))) \<sim> t) 
            \<longrightarrow> ((exec_event s (Get_My_Endpoints_Set did)) \<sim> d \<sim> (exec_event t (Get_My_Endpoints_Set did)))"
        proof -
        {
          fix d s t
          assume p1: "reachable0 s "
          assume p2: "reachable0 t "
          assume p3: "(s \<sim> d \<sim> t) "
          assume p4: "(interferes (the (domain_of_event (Get_My_Endpoints_Set did))) s d) "
          assume p5: "(s \<sim> (the (domain_of_event (Get_My_Endpoints_Set did))) \<sim> t) "
          have "((exec_event s (Get_My_Endpoints_Set did)) \<sim> d \<sim> (exec_event t (Get_My_Endpoints_Set did)))"
            by (metis Event.simps(53) domain_of_event_def option.sel p1 p2 p3 p4 p5 get_my_endpoints_set_wsc_e)
        }
        then show ?thesis by blast
        qed
      }
    then show ?thesis 
      using dynamic_weakly_step_consistent_e_def by blast
  qed


subsubsection{*proving "get caps" satisfying the "weakly step consistent" property*}

  lemma get_caps_wsc:
  assumes p0: "reachable0 s"
    and   p1: "reachable0 t"
    and   p2: "s \<sim> d \<sim> t"
    and   p3: "interferes did s d"
    and   p4: "s \<sim> did \<sim> t "
    and   p5: "s' = fst (get_caps s did)"
    and   p6: "t' = fst (get_caps t did)"
  shows   "s' \<sim> d \<sim> t'"
  proof -
  {
    have a0: "s = s'"
      using p5 get_caps_def by auto
    have a1: "t = t'"
      using p6 get_caps_def by auto
    have a2: "s' \<sim> d \<sim> t'"
      using a0 a1 p2 by auto
  }
  then show ?thesis by auto
  qed


  lemma get_caps_wsc_e:
  assumes p0: "reachable0 s"
    and   p1: "reachable0 t"
    and   p2: "a = (Get_Caps did)"
    and   p3: "s \<sim> d \<sim> t"
    and   p4: "interferes (the (domain_of_event a)) s d"
    and   p5: "s \<sim> did \<sim> t "
    and   p6: "s' = exec_event s a"
    and   p7: "t' = exec_event t a" 
  shows   "s' \<sim> d \<sim> t'"
  proof -
  {
    have a0: "(the (domain_of_event a)) = did"
      using p2 domain_of_event_def by auto
    have a1: "s' = fst (get_caps s did)"
      using p2 p6 exec_event_def by auto
    have a2: "t' = fst (get_caps t did)"
      using p2 p7 exec_event_def by auto
    have a3: "(interferes did s d)"
      using p4 a0 by auto
    have a4: "s' \<sim> d \<sim> t'"
      using a1 a2 a3 p0 p1 p3 p5 get_caps_wsc by blast
  }
  then show ?thesis by auto
  qed

  lemma get_caps_dwsc_e: "dynamic_weakly_step_consistent_e (Get_Caps did)"
  proof -
    { 
      have "\<forall>d s t. reachable0 s \<and> reachable0 t 
            \<and> (s \<sim> d \<sim> t) 
            \<and> (interferes (the (domain_of_event (Get_Caps did))) s d) 
            \<and> (s \<sim> (the (domain_of_event (Get_Caps did))) \<sim> t) 
            \<longrightarrow> ((exec_event s (Get_Caps did)) \<sim> d \<sim> (exec_event t (Get_Caps did)))"
        proof -
        {
          fix d s t
          assume p1: "reachable0 s "
          assume p2: "reachable0 t "
          assume p3: "(s \<sim> d \<sim> t) "
          assume p4: "(interferes (the (domain_of_event (Get_Caps did))) s d) "
          assume p5: "(s \<sim> (the (domain_of_event (Get_Caps did))) \<sim> t) "
          have "((exec_event s (Get_Caps did)) \<sim> d \<sim> (exec_event t (Get_Caps did)))"
            by (metis Event.simps(54) domain_of_event_def option.sel p1 p2 p3 p4 p5 get_caps_wsc_e)
        }
        then show ?thesis by blast
        qed
      }
    then show ?thesis 
      using dynamic_weakly_step_consistent_e_def by blast
  qed

subsubsection{*proving "grant endpoint cap" satisfying the "weakly step consistent" property*}

  lemma grant_endpoint_cap_wsc_domain_cap_set:
  assumes p0: "reachable0 s"
    and   p1: "reachable0 t"
    and   p2: "s \<sim> d \<sim> t"
    and   p3: "interferes did s d"
    and   p4: "s \<sim> did \<sim> t "
    and   p5: "s' = fst (grant_endpoint_cap s did grant_cap dst_cap)"
    and   p6: "t' = fst (grant_endpoint_cap t did grant_cap dst_cap)"
  shows   "get_domain_cap_set_from_domain_id s' d = get_domain_cap_set_from_domain_id t' d"
  proof -
  {
    have a0: "get_endpoints_of_domain s d = get_endpoints_of_domain t d"
      by (meson p2 vpeq1_def)
    have a1: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v t d)"
      by (meson p2 vpeq1_def)
    have a2: "interferes did t d"
      using p3 a1 by auto
    have a3: "get_domain_cap_set_from_domain_id s d = get_domain_cap_set_from_domain_id t d"
      by (meson p2 vpeq1_def) 
    have a4: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id t ep )"
      by (meson p2 vpeq1_def) 
    have a5: "get_endpoints_of_domain s did = get_endpoints_of_domain t did"
      by (meson p4 vpeq1_def)
    have a6: "(\<forall>ep. ep\<in>get_endpoints_of_domain s did 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id t ep )"
      by (meson p4 vpeq1_def)
    have a7: "get_domain_cap_set_from_domain_id s did = get_domain_cap_set_from_domain_id t did"
      by (meson p4 vpeq1_def) 
    have "get_domain_cap_set_from_domain_id s' d = get_domain_cap_set_from_domain_id t' d"
      proof (cases "grant_cap\<in>get_domain_cap_set_from_domain_id s did 
                    \<and> GRANT\<in>rights grant_cap
                    \<and> target grant_cap \<noteq> target dst_cap
                    \<and> dst_cap\<in>get_domain_cap_set_from_domain_id s did")
      assume b0: "grant_cap\<in>get_domain_cap_set_from_domain_id s did 
                  \<and> GRANT\<in>rights grant_cap
                  \<and> target grant_cap \<noteq> target dst_cap
                  \<and> dst_cap\<in>get_domain_cap_set_from_domain_id s did"
      have b1: "grant_cap\<in>get_domain_cap_set_from_domain_id t did 
                  \<and> GRANT\<in>rights grant_cap
                  \<and> target grant_cap \<noteq> target dst_cap
                  \<and> dst_cap\<in>get_domain_cap_set_from_domain_id t did"
        using a7 b0 by blast
      let ?did_dst = "target grant_cap"
      let ?cs_dst_s = "get_domain_cap_set_from_domain_id s ?did_dst"
      let ?cs_dst_t = "get_domain_cap_set_from_domain_id t ?did_dst"
      have b2: "\<forall>v. v\<noteq>?did_dst
              \<longrightarrow> (caps s) v = (caps s') v"
        using b0 p5 grant_endpoint_cap_def get_domain_cap_set_from_domain_id_def by auto
      have b3: "\<forall>v. v\<noteq>?did_dst
              \<longrightarrow> (caps t) v = (caps t') v"
        using b1 p6 grant_endpoint_cap_def get_domain_cap_set_from_domain_id_def by auto
      have b4: "(caps s') ?did_dst = insert dst_cap ?cs_dst_s"
        using b0 p5 grant_endpoint_cap_def get_domain_cap_set_from_domain_id_def by auto
      have b5: "(caps t') ?did_dst = insert dst_cap ?cs_dst_t"
        using b1 p6 grant_endpoint_cap_def get_domain_cap_set_from_domain_id_def by auto
      have "get_domain_cap_set_from_domain_id s' d = get_domain_cap_set_from_domain_id t' d"
        proof (cases "d = ?did_dst")
          assume c0: "d = ?did_dst"
          have c1: "?cs_dst_s = ?cs_dst_t"
            using a3 c0 by auto
          have c2: "(caps s') ?did_dst = (caps t') ?did_dst"
            using b4 b5 c1 by auto
          have c3: "get_domain_cap_set_from_domain_id s' d 
                    = get_domain_cap_set_from_domain_id t' d"
            using c2 c0 get_domain_cap_set_from_domain_id_def by auto
          then show ?thesis by auto
        next
          assume c0: "d \<noteq> ?did_dst"
          have c1: "(caps s) d = (caps t) d"
            using a3 get_domain_cap_set_from_domain_id_def by auto
          have c2: "(caps s) d = (caps s') d"
            using c0 b2 by auto
          have c3: "(caps t) d = (caps t') d"
            using c0 b3 by auto
          have c4: "(caps s') d = (caps t') d"
            using c1 c2 c3 by auto
          have c5: "get_domain_cap_set_from_domain_id s' d 
                    = get_domain_cap_set_from_domain_id t' d"
            using c4 get_domain_cap_set_from_domain_id_def by auto
          then show ?thesis by auto
        qed
      then show ?thesis by auto
    next
      assume b0: "\<not>(grant_cap\<in>get_domain_cap_set_from_domain_id s did 
                  \<and> GRANT\<in>rights grant_cap
                  \<and> target grant_cap \<noteq> target dst_cap
                  \<and> dst_cap\<in>get_domain_cap_set_from_domain_id s did)"
      have b1: "\<not>(grant_cap\<in>get_domain_cap_set_from_domain_id t did 
                  \<and> GRANT\<in>rights grant_cap
                  \<and> target grant_cap \<noteq> target dst_cap
                  \<and> dst_cap\<in>get_domain_cap_set_from_domain_id t did)"
        using a7 b0 by auto
      have b2: "s = s'"
        using b0 p5 grant_endpoint_cap_def get_domain_cap_set_from_domain_id_def by auto
      have b3: "t = t'"
        using b1 p6 grant_endpoint_cap_def get_domain_cap_set_from_domain_id_def by auto
      have b4: "get_domain_cap_set_from_domain_id s' d 
                    = get_domain_cap_set_from_domain_id s d"
        using b2 get_domain_cap_set_from_domain_id_def by auto
      have b5: "get_domain_cap_set_from_domain_id t' d 
                    = get_domain_cap_set_from_domain_id t d"
        using b3 get_domain_cap_set_from_domain_id_def by auto
      have b6: "get_domain_cap_set_from_domain_id s' d 
                    = get_domain_cap_set_from_domain_id t' d"
        using b4 b5 a3 by auto
      then show ?thesis by auto
    qed
    }
  then show ?thesis by auto
  qed

  lemma grant_endpoint_cap_wsc_policy:
  assumes p0: "reachable0 s"
    and   p1: "reachable0 t"
    and   p2: "s \<sim> d \<sim> t"
    and   p3: "interferes did s d"
    and   p4: "s \<sim> did \<sim> t "
    and   p5: "s' = fst (grant_endpoint_cap s did grant_cap dst_cap)"
    and   p6: "t' = fst (grant_endpoint_cap t did grant_cap dst_cap)"
  shows   "(\<forall>v. interferes v s' d \<longleftrightarrow> interferes v t' d)"
  proof -
  {
    have a0: "get_endpoints_of_domain s d = get_endpoints_of_domain t d"
      by (meson p2 vpeq1_def)
    have a1: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v t d)"
      by (meson p2 vpeq1_def)
    have a2: "interferes did t d"
      using p3 a1 by auto
    have a3: "get_domain_cap_set_from_domain_id s d = get_domain_cap_set_from_domain_id t d"
      by (meson p2 vpeq1_def) 
    have a4: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id t ep )"
      by (meson p2 vpeq1_def) 
    have a5: "get_endpoints_of_domain s did = get_endpoints_of_domain t did"
      by (meson p4 vpeq1_def)
    have a6: "(\<forall>ep. ep\<in>get_endpoints_of_domain s did 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id t ep )"
      by (meson p4 vpeq1_def)
    have a7: "get_domain_cap_set_from_domain_id s did = get_domain_cap_set_from_domain_id t did"
      by (meson p4 vpeq1_def) 
    have "(\<forall>v. interferes v s' d \<longleftrightarrow> interferes v t' d)"
      proof (cases "grant_cap\<in>get_domain_cap_set_from_domain_id s did 
                    \<and> GRANT\<in>rights grant_cap
                    \<and> target grant_cap \<noteq> target dst_cap
                    \<and> dst_cap\<in>get_domain_cap_set_from_domain_id s did")
      assume b0: "grant_cap\<in>get_domain_cap_set_from_domain_id s did 
                  \<and> GRANT\<in>rights grant_cap
                  \<and> target grant_cap \<noteq> target dst_cap
                  \<and> dst_cap\<in>get_domain_cap_set_from_domain_id s did"
      have b1: "grant_cap\<in>get_domain_cap_set_from_domain_id t did 
                  \<and> GRANT\<in>rights grant_cap
                  \<and> target grant_cap \<noteq> target dst_cap
                  \<and> dst_cap\<in>get_domain_cap_set_from_domain_id t did"
        using a7 b0 by blast
      let ?did_dst = "target grant_cap"
      let ?cs_dst_s = "get_domain_cap_set_from_domain_id s ?did_dst"
      let ?cs_dst_t = "get_domain_cap_set_from_domain_id t ?did_dst"
      have b2: "\<forall>v. v\<noteq>?did_dst
              \<longrightarrow> (caps s) v = (caps s') v"
        using b0 p5 grant_endpoint_cap_def get_domain_cap_set_from_domain_id_def by auto
      have b3: "\<forall>v. v\<noteq>?did_dst
              \<longrightarrow> (caps t) v = (caps t') v"
        using b1 p6 grant_endpoint_cap_def get_domain_cap_set_from_domain_id_def by auto
      have b4: "(caps s') ?did_dst = insert dst_cap ?cs_dst_s"
        using b0 p5 grant_endpoint_cap_def get_domain_cap_set_from_domain_id_def by auto
      have b5: "(caps t') ?did_dst = insert dst_cap ?cs_dst_t"
        using b1 p6 grant_endpoint_cap_def get_domain_cap_set_from_domain_id_def by auto
      let ?dst_cap_d = "target dst_cap"
      have b6: "dst_cap \<in> get_domain_cap_set_from_domain_id s' ?did_dst"
        using b4 get_domain_cap_set_from_domain_id_def by auto
      have b7: "interferes ?did_dst s' ?dst_cap_d"
        using b6 interferes_def by auto
      have b8: "dst_cap \<in> get_domain_cap_set_from_domain_id t' ?did_dst"
        using b5 get_domain_cap_set_from_domain_id_def by auto
      have b9: "interferes ?did_dst t' ?dst_cap_d"
        using b8 interferes_def by auto
      have b10: "?did_dst \<noteq> ?dst_cap_d"
        using b0 by auto
      have b11: "\<forall>v. v\<noteq>?did_dst
              \<longrightarrow> get_domain_cap_set_from_domain_id s v 
                = get_domain_cap_set_from_domain_id s' v"
        using b2 get_domain_cap_set_from_domain_id_def by auto
      have b12: "\<forall>v. v\<noteq>?did_dst
              \<longrightarrow> interferes v s d = interferes v s' d"
        using b11 interferes_def by auto
      have b13: "\<forall>v. v\<noteq>?did_dst
              \<longrightarrow> get_domain_cap_set_from_domain_id t v 
                = get_domain_cap_set_from_domain_id t' v"
        using b3 get_domain_cap_set_from_domain_id_def by auto
      have b14: "\<forall>v. v\<noteq>?did_dst
              \<longrightarrow> interferes v t d = interferes v t' d"
        using b13 interferes_def by auto
      have b15: "\<forall>v. v\<noteq>?did_dst
              \<longrightarrow> interferes v s' d = interferes v t' d"
        using b12 b14 a1 by auto
      have "(\<forall>v. interferes v s' d \<longleftrightarrow> interferes v t' d)"
        proof (cases "d = ?dst_cap_d")
          assume c0: "d = ?dst_cap_d"
          have c1: "interferes ?did_dst s' ?dst_cap_d = interferes ?did_dst t' ?dst_cap_d"
            using b7 b9 by auto
          have c2: "interferes ?did_dst s' d = interferes ?did_dst t' d"
            using c1 c0 by auto
          have c3: "\<forall>v. v=?did_dst
              \<longrightarrow> interferes v s' d = interferes v t' d"
            using c2 by auto
          have c4: "(\<forall>v. interferes v s' d \<longleftrightarrow> interferes v t' d)"
            using c3 b15 by blast
          then show ?thesis by auto
        next
          assume c0: "d \<noteq> ?dst_cap_d"
          have c1: "get_domain_cap_set_from_domain_id s' ?did_dst
                  = insert dst_cap (get_domain_cap_set_from_domain_id s ?did_dst)"
            using b4 get_domain_cap_set_from_domain_id_def by auto
          have c2: "get_domain_cap_set_from_domain_id t' ?did_dst
                  = insert dst_cap (get_domain_cap_set_from_domain_id t ?did_dst)"
            using b5 get_domain_cap_set_from_domain_id_def by auto
          have c3: "interferes ?did_dst s' d = interferes ?did_dst s d"
            using c1 c0 interferes_def by auto
          have c4: "interferes ?did_dst t' d = interferes ?did_dst t d"
            using c2 c0 interferes_def by auto
          have c5: "interferes ?did_dst s' d = interferes ?did_dst t' d"
            using c3 c4 a1 by auto
          have c6: "\<forall>v. v=?did_dst
              \<longrightarrow> interferes v s' d = interferes v t' d"
            using c5 by auto
          have c7: "(\<forall>v. interferes v s' d \<longleftrightarrow> interferes v t' d)"
            using c6 b15 by blast
          then show ?thesis by auto
        qed
      then show ?thesis by auto
    next
      assume b0: "\<not>(grant_cap\<in>get_domain_cap_set_from_domain_id s did 
                  \<and> GRANT\<in>rights grant_cap
                  \<and> target grant_cap \<noteq> target dst_cap
                  \<and> dst_cap\<in>get_domain_cap_set_from_domain_id s did)"
      have b1: "\<not>(grant_cap\<in>get_domain_cap_set_from_domain_id t did 
                  \<and> GRANT\<in>rights grant_cap
                  \<and> target grant_cap \<noteq> target dst_cap
                  \<and> dst_cap\<in>get_domain_cap_set_from_domain_id t did)"
        using a7 b0 by auto
      have b2: "s = s'"
        using b0 p5 grant_endpoint_cap_def get_domain_cap_set_from_domain_id_def by auto
      have b3: "t = t'"
        using b1 p6 grant_endpoint_cap_def get_domain_cap_set_from_domain_id_def by auto
      have b4: "(\<forall>v. interferes v s' d \<longleftrightarrow> interferes v t' d)"
        using a1 b2 b3 by auto
      then show ?thesis by auto
    qed
    }
  then show ?thesis by auto
  qed

  lemma grant_endpoint_cap_wsc_dom_eps:
  assumes p0: "reachable0 s"
    and   p1: "reachable0 t"
    and   p2: "s \<sim> d \<sim> t"
    and   p3: "interferes did s d"
    and   p4: "s \<sim> did \<sim> t "
    and   p5: "s' = fst (grant_endpoint_cap s did grant_cap dst_cap)"
    and   p6: "t' = fst (grant_endpoint_cap t did grant_cap dst_cap)"
  shows   "get_endpoints_of_domain s' d = get_endpoints_of_domain t' d"
  proof -
  {
    have a0: "get_endpoints_of_domain s d = get_endpoints_of_domain t d"
      by (meson p2 vpeq1_def)
    have a1: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v t d)"
      by (meson p2 vpeq1_def)
    have a2: "interferes did t d"
      using p3 a1 by auto
    have a3: "get_domain_cap_set_from_domain_id s d = get_domain_cap_set_from_domain_id t d"
      by (meson p2 vpeq1_def) 
    have a4: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id t ep )"
      by (meson p2 vpeq1_def) 
    have a5: "get_endpoints_of_domain s did = get_endpoints_of_domain t did"
      by (meson p4 vpeq1_def)
    have a6: "(\<forall>ep. ep\<in>get_endpoints_of_domain s did 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id t ep )"
      by (meson p4 vpeq1_def)
    have a7: "get_domain_cap_set_from_domain_id s did = get_domain_cap_set_from_domain_id t did"
      by (meson p4 vpeq1_def) 
    have "get_endpoints_of_domain s' d = get_endpoints_of_domain t' d"
      proof (cases "grant_cap\<in>get_domain_cap_set_from_domain_id s did 
                    \<and> GRANT\<in>rights grant_cap
                    \<and> target grant_cap \<noteq> target dst_cap
                    \<and> dst_cap\<in>get_domain_cap_set_from_domain_id s did")
      assume b0: "grant_cap\<in>get_domain_cap_set_from_domain_id s did 
                  \<and> GRANT\<in>rights grant_cap
                  \<and> target grant_cap \<noteq> target dst_cap
                  \<and> dst_cap\<in>get_domain_cap_set_from_domain_id s did"
      have b1: "grant_cap\<in>get_domain_cap_set_from_domain_id t did 
                  \<and> GRANT\<in>rights grant_cap
                  \<and> target grant_cap \<noteq> target dst_cap
                  \<and> dst_cap\<in>get_domain_cap_set_from_domain_id t did"
        using a7 b0 by blast
      have b2: "get_endpoints_of_domain s' d = get_endpoints_of_domain s d"
        using b0 p5 grant_endpoint_cap_def get_endpoints_of_domain_def by auto
      have b3: "get_endpoints_of_domain t' d = get_endpoints_of_domain t d"
        using b1 p6 grant_endpoint_cap_def get_endpoints_of_domain_def by auto
      have b4: "get_endpoints_of_domain s' d = get_endpoints_of_domain t' d"
        using b2 b3 a0 by auto
      then show ?thesis by auto
    next
      assume b0: "\<not>(grant_cap\<in>get_domain_cap_set_from_domain_id s did 
                  \<and> GRANT\<in>rights grant_cap
                  \<and> target grant_cap \<noteq> target dst_cap
                  \<and> dst_cap\<in>get_domain_cap_set_from_domain_id s did)"
      have b1: "\<not>(grant_cap\<in>get_domain_cap_set_from_domain_id t did 
                  \<and> GRANT\<in>rights grant_cap
                  \<and> target grant_cap \<noteq> target dst_cap
                  \<and> dst_cap\<in>get_domain_cap_set_from_domain_id t did)"
        using a7 b0 by auto
      have b2: "s = s'"
        using b0 p5 grant_endpoint_cap_def get_domain_cap_set_from_domain_id_def by auto
      have b3: "t = t'"
        using b1 p6 grant_endpoint_cap_def get_domain_cap_set_from_domain_id_def by auto
      have b4: "get_endpoints_of_domain s' d 
                    = get_endpoints_of_domain s d"
        using b2 get_domain_cap_set_from_domain_id_def by auto
      have b5: "get_endpoints_of_domain t' d 
                    = get_endpoints_of_domain t d"
        using b3 get_domain_cap_set_from_domain_id_def by auto
      have b6: "get_endpoints_of_domain s' d 
                    = get_endpoints_of_domain t' d"
        using b4 b5 a0 by auto
      then show ?thesis by auto
    qed
    }
  then show ?thesis by auto
  qed

  lemma grant_endpoint_cap_wsc_ep_msgs:
  assumes p0: "reachable0 s"
    and   p1: "reachable0 t"
    and   p2: "s \<sim> d \<sim> t"
    and   p3: "interferes did s d"
    and   p4: "s \<sim> did \<sim> t "
    and   p5: "s' = fst (grant_endpoint_cap s did grant_cap dst_cap)"
    and   p6: "t' = fst (grant_endpoint_cap t did grant_cap dst_cap)"
  shows   "(\<forall>ep. ep\<in>get_endpoints_of_domain s' d 
            \<longrightarrow> get_msg_set_from_endpoint_id s' ep = get_msg_set_from_endpoint_id t' ep )"
  proof -
  {
    have a0: "get_endpoints_of_domain s d = get_endpoints_of_domain t d"
      by (meson p2 vpeq1_def)
    have a1: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v t d)"
      by (meson p2 vpeq1_def)
    have a2: "interferes did t d"
      using p3 a1 by auto
    have a3: "get_domain_cap_set_from_domain_id s d = get_domain_cap_set_from_domain_id t d"
      by (meson p2 vpeq1_def) 
    have a4: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id t ep )"
      by (meson p2 vpeq1_def) 
    have a5: "get_endpoints_of_domain s did = get_endpoints_of_domain t did"
      by (meson p4 vpeq1_def)
    have a6: "(\<forall>ep. ep\<in>get_endpoints_of_domain s did 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id t ep )"
      by (meson p4 vpeq1_def)
    have a7: "get_domain_cap_set_from_domain_id s did = get_domain_cap_set_from_domain_id t did"
      by (meson p4 vpeq1_def) 
    have "(\<forall>ep. ep\<in>get_endpoints_of_domain s' d 
            \<longrightarrow> get_msg_set_from_endpoint_id s' ep = get_msg_set_from_endpoint_id t' ep )"
      proof (cases "grant_cap\<in>get_domain_cap_set_from_domain_id s did 
                    \<and> GRANT\<in>rights grant_cap
                    \<and> target grant_cap \<noteq> target dst_cap
                    \<and> dst_cap\<in>get_domain_cap_set_from_domain_id s did")
      assume b0: "grant_cap\<in>get_domain_cap_set_from_domain_id s did 
                  \<and> GRANT\<in>rights grant_cap
                  \<and> target grant_cap \<noteq> target dst_cap
                  \<and> dst_cap\<in>get_domain_cap_set_from_domain_id s did"
      have b1: "grant_cap\<in>get_domain_cap_set_from_domain_id t did 
                  \<and> GRANT\<in>rights grant_cap
                  \<and> target grant_cap \<noteq> target dst_cap
                  \<and> dst_cap\<in>get_domain_cap_set_from_domain_id t did"
        using a7 b0 by blast
      have b2: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s' ep = get_msg_set_from_endpoint_id s ep )"
        using b0 p5 grant_endpoint_cap_def get_msg_set_from_endpoint_id_def by auto
      have b3: "(\<forall>ep. ep\<in>get_endpoints_of_domain t d 
            \<longrightarrow> get_msg_set_from_endpoint_id t' ep = get_msg_set_from_endpoint_id t ep )"
        using b1 p6 grant_endpoint_cap_def get_msg_set_from_endpoint_id_def by auto
      have b4: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id t' ep = get_msg_set_from_endpoint_id t ep )"
        using b3 a0 by auto
      have b5: "get_endpoints_of_domain s d = get_endpoints_of_domain s' d"
        using p0 p5 grant_endpoint_cap_notchg_dom_eps by auto
      have b6: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s' ep = get_msg_set_from_endpoint_id t' ep )"
        using b2 b4 a4 by auto
      have b7: "(\<forall>ep. ep\<in>get_endpoints_of_domain s' d 
            \<longrightarrow> get_msg_set_from_endpoint_id s' ep = get_msg_set_from_endpoint_id t' ep )"
        using b5 b6 by auto
      then show ?thesis by auto
    next
      assume b0: "\<not>(grant_cap\<in>get_domain_cap_set_from_domain_id s did 
                  \<and> GRANT\<in>rights grant_cap
                  \<and> target grant_cap \<noteq> target dst_cap
                  \<and> dst_cap\<in>get_domain_cap_set_from_domain_id s did)"
      have b1: "\<not>(grant_cap\<in>get_domain_cap_set_from_domain_id t did 
                  \<and> GRANT\<in>rights grant_cap
                  \<and> target grant_cap \<noteq> target dst_cap
                  \<and> dst_cap\<in>get_domain_cap_set_from_domain_id t did)"
        using a7 b0 by auto
      have b2: "s = s'"
        using b0 p5 grant_endpoint_cap_def get_domain_cap_set_from_domain_id_def by auto
      have b3: "t = t'"
        using b1 p6 grant_endpoint_cap_def get_domain_cap_set_from_domain_id_def by auto
      have b4: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s' ep = get_msg_set_from_endpoint_id s ep )"
        using b2 get_domain_cap_set_from_domain_id_def by auto
      have b5: "(\<forall>ep. ep\<in>get_endpoints_of_domain t d 
            \<longrightarrow> get_msg_set_from_endpoint_id t' ep = get_msg_set_from_endpoint_id t ep )"
        using b3 get_domain_cap_set_from_domain_id_def by auto
      have b6: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id t' ep = get_msg_set_from_endpoint_id t ep )"
        using b5 a0 by auto
      have b7: "get_endpoints_of_domain s d = get_endpoints_of_domain s' d"
        using p0 p5 grant_endpoint_cap_notchg_dom_eps by auto
      have b8: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s' ep = get_msg_set_from_endpoint_id t' ep )"
        using b4 b6 a4 by auto
      have b9: "(\<forall>ep. ep\<in>get_endpoints_of_domain s' d 
            \<longrightarrow> get_msg_set_from_endpoint_id s' ep = get_msg_set_from_endpoint_id t' ep )"
        using b7 b8 by auto
      then show ?thesis by auto
    qed
    }
  then show ?thesis by auto
  qed

  lemma grant_endpoint_cap_wsc:
  assumes p0: "reachable0 s"
    and   p1: "reachable0 t"
    and   p2: "s \<sim> d \<sim> t"
    and   p3: "interferes did s d"
    and   p4: "s \<sim> did \<sim> t "
    and   p5: "s' = fst (grant_endpoint_cap s did grant_cap dst_cap)"
    and   p6: "t' = fst (grant_endpoint_cap t did grant_cap dst_cap)"
  shows   "s' \<sim> d \<sim> t'"
  proof -
  {
    have a0: "get_domain_cap_set_from_domain_id s' d = get_domain_cap_set_from_domain_id t' d"
      using p0 p1 p2 p3 p4 p5 p6 grant_endpoint_cap_wsc_domain_cap_set by blast
    have a1: "(\<forall>v. interferes v s' d \<longleftrightarrow> interferes v t' d)"
      using p0 p1 p2 p3 p4 p5 p6 grant_endpoint_cap_wsc_policy by blast
    have a2: "get_endpoints_of_domain s' d = get_endpoints_of_domain t' d"
      using p0 p1 p2 p3 p4 p5 p6 grant_endpoint_cap_wsc_dom_eps by blast
    have a3: "(\<forall>ep. ep\<in>get_endpoints_of_domain s' d 
            \<longrightarrow> get_msg_set_from_endpoint_id s' ep = get_msg_set_from_endpoint_id t' ep )"
      using p0 p1 p2 p3 p4 p5 p6 grant_endpoint_cap_wsc_ep_msgs by blast
    have a4: "s' \<sim> d \<sim> t'"
      using a0 a1 a2 a3 vpeq1_def by auto
  }
  then show ?thesis by auto
  qed

  lemma grant_endpoint_cap_wsc_e:
  assumes p0: "reachable0 s"
    and   p1: "reachable0 t"
    and   p2: "a = (Grant_Endpoint_Cap did grant_cap dst_cap)"
    and   p3: "s \<sim> d \<sim> t"
    and   p4: "interferes (the (domain_of_event a)) s d"
    and   p5: "s \<sim> did \<sim> t "
    and   p6: "s' = exec_event s a"
    and   p7: "t' = exec_event t a" 
  shows   "s' \<sim> d \<sim> t'"
  proof -
  {
    have a0: "(the (domain_of_event a)) = did"
      using p2 domain_of_event_def by auto
    have a1: "s' = fst (grant_endpoint_cap s did grant_cap dst_cap)"
      using p2 p6 exec_event_def by auto
    have a2: "t' = fst (grant_endpoint_cap t did grant_cap dst_cap)"
      using p2 p7 exec_event_def by auto
    have a3: "(interferes did s d)"
      using p4 a0 by auto
    have a4: "s' \<sim> d \<sim> t'"
      using a1 a2 a3 p0 p1 p3 p5 grant_endpoint_cap_wsc by blast
  }
  then show ?thesis by auto
  qed

  lemma grant_endpoint_cap_dwsc_e: "dynamic_weakly_step_consistent_e (Grant_Endpoint_Cap did grant_cap dst_cap)"
  proof -
    { 
      have "\<forall>d s t. reachable0 s \<and> reachable0 t 
            \<and> (s \<sim> d \<sim> t) 
            \<and> (interferes (the (domain_of_event (Grant_Endpoint_Cap did grant_cap dst_cap))) s d) 
            \<and> (s \<sim> (the (domain_of_event (Grant_Endpoint_Cap did grant_cap dst_cap))) \<sim> t) 
            \<longrightarrow> ((exec_event s (Grant_Endpoint_Cap did grant_cap dst_cap)) \<sim> d \<sim> (exec_event t (Grant_Endpoint_Cap did grant_cap dst_cap)))"
        proof -
        {
          fix d s t
          assume p1: "reachable0 s "
          assume p2: "reachable0 t "
          assume p3: "(s \<sim> d \<sim> t) "
          assume p4: "(interferes (the (domain_of_event (Grant_Endpoint_Cap did grant_cap dst_cap))) s d) "
          assume p5: "(s \<sim> (the (domain_of_event (Grant_Endpoint_Cap did grant_cap dst_cap))) \<sim> t) "
          have "((exec_event s (Grant_Endpoint_Cap did grant_cap dst_cap)) \<sim> d \<sim> (exec_event t (Grant_Endpoint_Cap did grant_cap dst_cap)))"
            by (metis Event.simps(55) domain_of_event_def option.sel p1 p2 p3 p4 p5 grant_endpoint_cap_wsc_e)
        }
        then show ?thesis by blast
        qed
      }
    then show ?thesis 
      using dynamic_weakly_step_consistent_e_def by blast
  qed

subsubsection{*proving "remove cap right" satisfying the "weakly step consistent" property*}

  lemma remove_cap_right_wsc_domain_cap_set:
  assumes p0: "reachable0 s"
    and   p1: "reachable0 t"
    and   p2: "s \<sim> d \<sim> t"
    and   p3: "interferes did s d"
    and   p4: "s \<sim> did \<sim> t "
    and   p5: "s' = fst (remove_cap_right s did rm_cap right_to_rm)"
    and   p6: "t' = fst (remove_cap_right t did rm_cap right_to_rm)"
  shows   "get_domain_cap_set_from_domain_id s' d 
            = get_domain_cap_set_from_domain_id t' d"
  proof -
  {
    have a0: "get_endpoints_of_domain s d = get_endpoints_of_domain t d"
      by (meson p2 vpeq1_def)
    have a1: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v t d)"
      by (meson p2 vpeq1_def)
    have a2: "interferes did t d"
      using p3 a1 by auto
    have a3: "get_domain_cap_set_from_domain_id s d 
              = get_domain_cap_set_from_domain_id t d"
      by (meson p2 vpeq1_def) 
    have a4: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id t ep )"
      by (meson p2 vpeq1_def) 
    have a5: "get_endpoints_of_domain s did = get_endpoints_of_domain t did"
      by (meson p4 vpeq1_def)
    have a6: "(\<forall>ep. ep\<in>get_endpoints_of_domain s did 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id t ep )"
      by (meson p4 vpeq1_def)
    have a7: "get_domain_cap_set_from_domain_id s did 
              = get_domain_cap_set_from_domain_id t did"
      by (meson p4 vpeq1_def) 
    have "get_domain_cap_set_from_domain_id s' d 
            = get_domain_cap_set_from_domain_id t' d"
      proof (cases "rm_cap \<in>  get_domain_cap_set_from_domain_id s did 
              \<and> REMOVE \<in> rights rm_cap
              \<and> right_to_rm \<in> rights rm_cap")
      assume b0: "rm_cap \<in>  get_domain_cap_set_from_domain_id s did 
              \<and> REMOVE \<in> rights rm_cap
              \<and> right_to_rm \<in> rights rm_cap"
      have b1: "rm_cap \<in>  get_domain_cap_set_from_domain_id t did 
              \<and> REMOVE \<in> rights rm_cap
              \<and> right_to_rm \<in> rights rm_cap"
        using a7 b0 by auto
      have "get_domain_cap_set_from_domain_id s' d 
              = get_domain_cap_set_from_domain_id t' d"
        proof (cases " REMOVE = right_to_rm
                  \<and> {REMOVE} = rights rm_cap")
          assume c0: "REMOVE = right_to_rm
                  \<and> {REMOVE} = rights rm_cap"
          let ?cs_dst_s = "get_domain_cap_set_from_domain_id s did"
          let ?cs_rest_s = "{c. c\<in>?cs_dst_s \<and> c\<noteq>rm_cap}"
          let ?cs_dst_t = "get_domain_cap_set_from_domain_id t did"
          let ?cs_rest_t = "{c. c\<in>?cs_dst_t \<and> c\<noteq>rm_cap}"
          have c1: "((caps s') did) = ?cs_rest_s"
            using b0 c0 p5 remove_cap_right_def by auto  
          have c2: "((caps t') did) = ?cs_rest_t"
            using b1 c0 p6 remove_cap_right_def by auto
          have c3: "?cs_rest_s = ?cs_rest_t"
            using a7 by auto
          have c4: "((caps s') did) = ((caps t') did)"
            using c1 c2 c3 by auto
          have c5: "\<forall>v. v\<noteq>did
                    \<longrightarrow> ((caps s') v) = ((caps s) v)"
            using b0 c0 p5 remove_cap_right_def by auto
          have c6: "\<forall>v. v\<noteq>did
                    \<longrightarrow> ((caps t') v) = ((caps t) v)"
            using b1 c0 p6 remove_cap_right_def by auto
          have c7: "\<forall>v. v\<noteq>did \<and> v=d
                    \<longrightarrow> ((caps s') v) = ((caps t') v)"
            using c5 c6 a3 get_domain_cap_set_from_domain_id_def by auto
          have c8: "d\<noteq>did
                    \<longrightarrow> ((caps s') d) = ((caps t') d)"
            using c7 by auto
          have c9: "((caps s') d) = ((caps t') d)"
            using c4 c8 by auto
          have c10: "get_domain_cap_set_from_domain_id s' d 
                    = get_domain_cap_set_from_domain_id t' d"
            using c9 get_domain_cap_set_from_domain_id_def by auto
          then show ?thesis by auto
        next
          assume c0: "\<not>(REMOVE = right_to_rm
                      \<and> {REMOVE} = rights rm_cap)"
          let ?cs_dst_s = "get_domain_cap_set_from_domain_id s did"
          let ?cs_rest_s = "{c. c\<in>?cs_dst_s \<and> c\<noteq>rm_cap}"
          let ?cs_dst_t = "get_domain_cap_set_from_domain_id t did"
          let ?cs_rest_t = "{c. c\<in>?cs_dst_t \<and> c\<noteq>rm_cap}"
          let ?new_cap = "\<lparr> target = target rm_cap,
                            rights = (rights rm_cap) - {right_to_rm}\<rparr>"
          have c1: "((caps s') did) = (insert ?new_cap ?cs_rest_s)"
            using b0 c0 p5 remove_cap_right_def by auto
          have c2: "((caps t') did) = (insert ?new_cap ?cs_rest_t)"
            using b1 c0 p6 remove_cap_right_def by auto
          have c3: "?cs_rest_s = ?cs_rest_t"
            using a7 by auto
          have c4: "((caps s') did) = ((caps t') did)"
            using c1 c2 c3 by auto
          have c5: "\<forall>v. v\<noteq>did
                    \<longrightarrow> ((caps s') v) = ((caps s) v)"
            using b0 c0 p5 remove_cap_right_def by auto
          have c6: "\<forall>v. v\<noteq>did
                    \<longrightarrow> ((caps t') v) = ((caps t) v)"
            using b1 c0 p6 remove_cap_right_def by auto
          have c7: "\<forall>v. v\<noteq>did \<and> v=d
                    \<longrightarrow> ((caps s') v) = ((caps t') v)"
            using c5 c6 a3 get_domain_cap_set_from_domain_id_def by auto
          have c8: "d\<noteq>did
                    \<longrightarrow> ((caps s') d) = ((caps t') d)"
            using c7 by auto
          have c9: "((caps s') d) = ((caps t') d)"
            using c4 c8 by auto
          have c10: "get_domain_cap_set_from_domain_id s' d 
                    = get_domain_cap_set_from_domain_id t' d"
            using c9 get_domain_cap_set_from_domain_id_def by auto
          then show ?thesis by auto
        qed
      then show ?thesis by auto
    next
      assume b0: "\<not>(rm_cap \<in>  get_domain_cap_set_from_domain_id s did 
                    \<and> REMOVE \<in> rights rm_cap
                    \<and> right_to_rm \<in> rights rm_cap)"
      have b1: "\<not>(rm_cap \<in>  get_domain_cap_set_from_domain_id t did 
                    \<and> REMOVE \<in> rights rm_cap
                    \<and> right_to_rm \<in> rights rm_cap)"
        using b0 a7 by auto
      have b2: "s' = s"
        using b0 p5 remove_cap_right_def by auto
      have b3: "get_domain_cap_set_from_domain_id s d 
                = get_domain_cap_set_from_domain_id s' d"
        using b2 get_domain_cap_set_from_domain_id_def by auto
      have b4: "t' = t"
        using b1 p6 remove_cap_right_def by auto
      have b5: "get_domain_cap_set_from_domain_id t d 
                = get_domain_cap_set_from_domain_id t' d"
        using b4 get_domain_cap_set_from_domain_id_def by auto
      have b6: "get_domain_cap_set_from_domain_id s' d 
                = get_domain_cap_set_from_domain_id t' d"
        using a3 b3 b5 by auto
      then show ?thesis by auto
    qed
    }
  then show ?thesis by auto
  qed

  lemma remove_cap_right_wsc_policy:
  assumes p0: "reachable0 s"
    and   p1: "reachable0 t"
    and   p2: "s \<sim> d \<sim> t"
    and   p3: "interferes did s d"
    and   p4: "s \<sim> did \<sim> t "
    and   p5: "s' = fst (remove_cap_right s did rm_cap right_to_rm)"
    and   p6: "t' = fst (remove_cap_right t did rm_cap right_to_rm)"
  shows   "(\<forall>v. interferes v s' d \<longleftrightarrow> interferes v t' d)"
  proof -
  {
    have a0: "get_endpoints_of_domain s d = get_endpoints_of_domain t d"
      by (meson p2 vpeq1_def)
    have a1: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v t d)"
      by (meson p2 vpeq1_def)
    have a2: "interferes did t d"
      using p3 a1 by auto
    have a3: "get_domain_cap_set_from_domain_id s d 
              = get_domain_cap_set_from_domain_id t d"
      by (meson p2 vpeq1_def) 
    have a4: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id t ep )"
      by (meson p2 vpeq1_def) 
    have a5: "get_endpoints_of_domain s did = get_endpoints_of_domain t did"
      by (meson p4 vpeq1_def)
    have a6: "(\<forall>ep. ep\<in>get_endpoints_of_domain s did 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id t ep )"
      by (meson p4 vpeq1_def)
    have a7: "get_domain_cap_set_from_domain_id s did 
              = get_domain_cap_set_from_domain_id t did"
      by (meson p4 vpeq1_def) 
    have "(\<forall>v. interferes v s' d \<longleftrightarrow> interferes v t' d)"
      proof (cases "rm_cap \<in>  get_domain_cap_set_from_domain_id s did 
              \<and> REMOVE \<in> rights rm_cap
              \<and> right_to_rm \<in> rights rm_cap")
      assume b0: "rm_cap \<in>  get_domain_cap_set_from_domain_id s did 
              \<and> REMOVE \<in> rights rm_cap
              \<and> right_to_rm \<in> rights rm_cap"
      have b1: "rm_cap \<in>  get_domain_cap_set_from_domain_id t did 
              \<and> REMOVE \<in> rights rm_cap
              \<and> right_to_rm \<in> rights rm_cap"
        using a7 b0 by auto
      have "(\<forall>v. interferes v s' d \<longleftrightarrow> interferes v t' d)"
        proof (cases " REMOVE = right_to_rm
                  \<and> {REMOVE} = rights rm_cap")
          assume c0: "REMOVE = right_to_rm
                  \<and> {REMOVE} = rights rm_cap"
          let ?cs_dst_s = "get_domain_cap_set_from_domain_id s did"
          let ?cs_rest_s = "{c. c\<in>?cs_dst_s \<and> c\<noteq>rm_cap}"
          let ?cs_dst_t = "get_domain_cap_set_from_domain_id t did"
          let ?cs_rest_t = "{c. c\<in>?cs_dst_t \<and> c\<noteq>rm_cap}"
          have c1: "((caps s') did) = ?cs_rest_s"
            using b0 c0 p5 remove_cap_right_def by auto  
          have c2: "((caps t') did) = ?cs_rest_t"
            using b1 c0 p6 remove_cap_right_def by auto
          have c3: "?cs_rest_s = ?cs_rest_t"
            using a7 by auto
          have c4: "((caps s') did) = ((caps t') did)"
            using c1 c2 c3 by auto
          have c5: "\<forall>v. v\<noteq>did
                    \<longrightarrow> ((caps s') v) = ((caps s) v)"
            using b0 c0 p5 remove_cap_right_def by auto
          have c6: "\<forall>v. v\<noteq>did
                    \<longrightarrow> ((caps t') v) = ((caps t) v)"
            using b1 c0 p6 remove_cap_right_def by auto
          have c7: "\<forall>v. v\<noteq>did \<and> v=d
                    \<longrightarrow> ((caps s') v) = ((caps t') v)"
            using c5 c6 a3 get_domain_cap_set_from_domain_id_def by auto
          have c8: "d\<noteq>did
                    \<longrightarrow> ((caps s') d) = ((caps t') d)"
            using c7 by auto
          have c9: "((caps s') d) = ((caps t') d)"
            using c4 c8 by auto
          have c10: "get_domain_cap_set_from_domain_id s' d 
                    = get_domain_cap_set_from_domain_id t' d"
            using c9 get_domain_cap_set_from_domain_id_def by auto
          have c11: "\<forall>v. v\<noteq>did
                    \<longrightarrow> interferes v s d \<longleftrightarrow> interferes v s' d"
            using c5 get_domain_cap_set_from_domain_id_def interferes_def by auto
          have c12: "\<forall>v. v\<noteq>did
                    \<longrightarrow> interferes v t d \<longleftrightarrow> interferes v t' d"
            using c6 get_domain_cap_set_from_domain_id_def interferes_def by auto
          have c13: "\<forall>v. v\<noteq>did 
                    \<longrightarrow> interferes v s' d \<longleftrightarrow> interferes v t' d"
            using c11 c12 a1 by auto
          have c14: "interferes did s' d \<longleftrightarrow> interferes did t' d"
            using c4 get_domain_cap_set_from_domain_id_def interferes_def by auto
          have c15: "(\<forall>v. interferes v s' d \<longleftrightarrow> interferes v t' d)"
            using c13 c14 by auto
          then show ?thesis by auto
        next
          assume c0: "\<not>(REMOVE = right_to_rm
                      \<and> {REMOVE} = rights rm_cap)"
          let ?cs_dst_s = "get_domain_cap_set_from_domain_id s did"
          let ?cs_rest_s = "{c. c\<in>?cs_dst_s \<and> c\<noteq>rm_cap}"
          let ?cs_dst_t = "get_domain_cap_set_from_domain_id t did"
          let ?cs_rest_t = "{c. c\<in>?cs_dst_t \<and> c\<noteq>rm_cap}"
          let ?new_cap = "\<lparr> target = target rm_cap,
                            rights = (rights rm_cap) - {right_to_rm}\<rparr>"
          have c1: "((caps s') did) = (insert ?new_cap ?cs_rest_s)"
            using b0 c0 p5 remove_cap_right_def by auto
          have c2: "((caps t') did) = (insert ?new_cap ?cs_rest_t)"
            using b1 c0 p6 remove_cap_right_def by auto
          have c3: "?cs_rest_s = ?cs_rest_t"
            using a7 by auto
          have c4: "((caps s') did) = ((caps t') did)"
            using c1 c2 c3 by auto
          have c5: "\<forall>v. v\<noteq>did
                    \<longrightarrow> ((caps s') v) = ((caps s) v)"
            using b0 c0 p5 remove_cap_right_def by auto
          have c6: "\<forall>v. v\<noteq>did
                    \<longrightarrow> ((caps t') v) = ((caps t) v)"
            using b1 c0 p6 remove_cap_right_def by auto
          have c7: "\<forall>v. v\<noteq>did \<and> v=d
                    \<longrightarrow> ((caps s') v) = ((caps t') v)"
            using c5 c6 a3 get_domain_cap_set_from_domain_id_def by auto
          have c8: "d\<noteq>did
                    \<longrightarrow> ((caps s') d) = ((caps t') d)"
            using c7 by auto
          have c9: "((caps s') d) = ((caps t') d)"
            using c4 c8 by auto
          have c10: "get_domain_cap_set_from_domain_id s' d 
                    = get_domain_cap_set_from_domain_id t' d"
            using c9 get_domain_cap_set_from_domain_id_def by auto
          have c11: "\<forall>v. v\<noteq>did
                    \<longrightarrow> interferes v s d \<longleftrightarrow> interferes v s' d"
            using c5 get_domain_cap_set_from_domain_id_def interferes_def by auto
          have c12: "\<forall>v. v\<noteq>did
                    \<longrightarrow> interferes v t d \<longleftrightarrow> interferes v t' d"
            using c6 get_domain_cap_set_from_domain_id_def interferes_def by auto
          have c13: "\<forall>v. v\<noteq>did 
                    \<longrightarrow> interferes v s' d \<longleftrightarrow> interferes v t' d"
            using c11 c12 a1 by auto
          have c14: "interferes did s' d \<longleftrightarrow> interferes did t' d"
            using c4 c10 get_domain_cap_set_from_domain_id_def interferes_def by auto
          have c15: "(\<forall>v. interferes v s' d \<longleftrightarrow> interferes v t' d)"
            using c13 c14 by auto
          then show ?thesis by auto
        qed
      then show ?thesis by auto
    next
      assume b0: "\<not>(rm_cap \<in>  get_domain_cap_set_from_domain_id s did 
                    \<and> REMOVE \<in> rights rm_cap
                    \<and> right_to_rm \<in> rights rm_cap)"
      have b1: "\<not>(rm_cap \<in>  get_domain_cap_set_from_domain_id t did 
                    \<and> REMOVE \<in> rights rm_cap
                    \<and> right_to_rm \<in> rights rm_cap)"
        using b0 a7 by auto
      have b2: "s' = s"
        using b0 p5 remove_cap_right_def by auto
      have b3: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v s' d)"
        using b2 get_domain_cap_set_from_domain_id_def by auto
      have b4: "t' = t"
        using b1 p6 remove_cap_right_def by auto
      have b5: "(\<forall>v. interferes v t d \<longleftrightarrow> interferes v t' d)"
        using b4 get_domain_cap_set_from_domain_id_def by auto
      have b6: "(\<forall>v. interferes v s' d \<longleftrightarrow> interferes v t' d)"
        using a1 b3 b5 by auto
      then show ?thesis by auto
    qed
    }
  then show ?thesis by auto
  qed

  lemma remove_cap_right_wsc_dom_eps:
  assumes p0: "reachable0 s"
    and   p1: "reachable0 t"
    and   p2: "s \<sim> d \<sim> t"
    and   p3: "interferes did s d"
    and   p4: "s \<sim> did \<sim> t "
    and   p5: "s' = fst (remove_cap_right s did rm_cap right_to_rm)"
    and   p6: "t' = fst (remove_cap_right t did rm_cap right_to_rm)"
  shows   "get_endpoints_of_domain s' d = get_endpoints_of_domain t' d"
  proof -
  {
    have a0: "get_endpoints_of_domain s d = get_endpoints_of_domain t d"
      by (meson p2 vpeq1_def)
    have a1: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v t d)"
      by (meson p2 vpeq1_def)
    have a2: "interferes did t d"
      using p3 a1 by auto
    have a4: "get_endpoints_of_domain s d = get_endpoints_of_domain s' d"
      using p0 p5 remove_cap_right_notchg_dom_eps by auto
    have a5: "get_endpoints_of_domain t d = get_endpoints_of_domain t' d"
      using p1 p6 remove_cap_right_notchg_dom_eps by auto
    have a6: "get_endpoints_of_domain s' d = get_endpoints_of_domain t' d"
      using a0 a4 a5 by auto
  }
  then show ?thesis by auto
  qed

  lemma remove_cap_right_wsc_ep_msgs:
  assumes p0: "reachable0 s"
    and   p1: "reachable0 t"
    and   p2: "s \<sim> d \<sim> t"
    and   p3: "interferes did s d"
    and   p4: "s \<sim> did \<sim> t "
    and   p5: "s' = fst (remove_cap_right s did rm_cap right_to_rm)"
    and   p6: "t' = fst (remove_cap_right t did rm_cap right_to_rm)"
  shows   "(\<forall>ep. ep\<in>get_endpoints_of_domain s' d 
            \<longrightarrow> get_msg_set_from_endpoint_id s' ep = get_msg_set_from_endpoint_id t' ep )"
  proof -
  {
    have a0: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id t ep )"
      by (meson p2 vpeq1_def)
    have a1: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v t d)"
      by (meson p2 vpeq1_def)
    have a2: "interferes did t d"
      using p3 a1 by auto
    have a4: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s ep = get_msg_set_from_endpoint_id s' ep )"
      using p0 p5 remove_cap_right_notchg_ep_msgs by auto
    have a5: "(\<forall>ep. ep\<in>get_endpoints_of_domain t d 
            \<longrightarrow> get_msg_set_from_endpoint_id t ep = get_msg_set_from_endpoint_id t' ep )"
      using p1 p6 remove_cap_right_notchg_ep_msgs by auto
    have a6: "get_endpoints_of_domain s d = get_endpoints_of_domain t d"
      by (meson p2 vpeq1_def)
    have a7: "(\<forall>ep. ep\<in>get_endpoints_of_domain s d 
            \<longrightarrow> get_msg_set_from_endpoint_id s' ep = get_msg_set_from_endpoint_id t' ep )"
      using a0 a4 a5 a6 by auto
    have a8: "get_endpoints_of_domain s d = get_endpoints_of_domain s' d"
      using p0 p5 remove_cap_right_notchg_dom_eps by auto 
    have a9: "(\<forall>ep. ep\<in>get_endpoints_of_domain s' d 
            \<longrightarrow> get_msg_set_from_endpoint_id s' ep = get_msg_set_from_endpoint_id t' ep )"
      using a7 a8 by auto
  }
  then show ?thesis by auto
  qed

  lemma remove_cap_right_wsc:
  assumes p0: "reachable0 s"
    and   p1: "reachable0 t"
    and   p2: "s \<sim> d \<sim> t"
    and   p3: "interferes did s d"
    and   p4: "s \<sim> did \<sim> t "
    and   p5: "s' = fst (remove_cap_right s did rm_cap right_to_rm)"
    and   p6: "t' = fst (remove_cap_right t did rm_cap right_to_rm)"
  shows   "s' \<sim> d \<sim> t'"
  proof -
  {
    have a0: "get_domain_cap_set_from_domain_id s' d = get_domain_cap_set_from_domain_id t' d"
      using p0 p1 p2 p3 p4 p5 p6 remove_cap_right_wsc_domain_cap_set by blast
    have a1: "(\<forall>v. interferes v s' d \<longleftrightarrow> interferes v t' d)"
      using p0 p1 p2 p3 p4 p5 p6 remove_cap_right_wsc_policy by blast
    have a2: "get_endpoints_of_domain s' d = get_endpoints_of_domain t' d"
      using p0 p1 p2 p3 p4 p5 p6 remove_cap_right_wsc_dom_eps by blast
    have a3: "(\<forall>ep. ep\<in>get_endpoints_of_domain s' d 
            \<longrightarrow> get_msg_set_from_endpoint_id s' ep = get_msg_set_from_endpoint_id t' ep )"
      using p0 p1 p2 p3 p4 p5 p6 remove_cap_right_wsc_ep_msgs by blast
    have a4: "s' \<sim> d \<sim> t'"
      using a0 a1 a2 a3 vpeq1_def by auto
  }
  then show ?thesis by auto
  qed

  lemma remove_cap_right_wsc_e:
  assumes p0: "reachable0 s"
    and   p1: "reachable0 t"
    and   p2: "a = (Remove_Cap_Right did dst_cap right_to_rm)"
    and   p3: "s \<sim> d \<sim> t"
    and   p4: "interferes (the (domain_of_event a)) s d"
    and   p5: "s \<sim> did \<sim> t "
    and   p6: "s' = exec_event s a"
    and   p7: "t' = exec_event t a" 
  shows   "s' \<sim> d \<sim> t'"
  proof -
  {
    have a0: "(the (domain_of_event a)) = did"
      using p2 domain_of_event_def by auto
    have a1: "s' = fst (remove_cap_right s did dst_cap right_to_rm)"
      using p2 p6 exec_event_def by auto
    have a2: "t' = fst (remove_cap_right t did dst_cap right_to_rm)"
      using p2 p7 exec_event_def by auto
    have a3: "(interferes did s d)"
      using p4 a0 by auto
    have a4: "s' \<sim> d \<sim> t'"
      using a1 a2 a3 p0 p1 p3 p5 remove_cap_right_wsc by blast
  }
  then show ?thesis by auto
  qed

  lemma remove_cap_right_dwsc_e: "dynamic_weakly_step_consistent_e (Remove_Cap_Right did dst_cap right_to_rm)"
  proof -
    { 
      have "\<forall>d s t. reachable0 s \<and> reachable0 t 
            \<and> (s \<sim> d \<sim> t) 
            \<and> (interferes (the (domain_of_event (Remove_Cap_Right did dst_cap right_to_rm))) s d) 
            \<and> (s \<sim> (the (domain_of_event (Remove_Cap_Right did dst_cap right_to_rm))) \<sim> t) 
            \<longrightarrow> ((exec_event s (Remove_Cap_Right did dst_cap right_to_rm)) \<sim> d \<sim> (exec_event t (Remove_Cap_Right did dst_cap right_to_rm)))"
        proof -
        {
          fix d s t
          assume p1: "reachable0 s "
          assume p2: "reachable0 t "
          assume p3: "(s \<sim> d \<sim> t) "
          assume p4: "(interferes (the (domain_of_event (Remove_Cap_Right did dst_cap right_to_rm))) s d) "
          assume p5: "(s \<sim> (the (domain_of_event (Remove_Cap_Right did dst_cap right_to_rm))) \<sim> t) "
          have "((exec_event s (Remove_Cap_Right did dst_cap right_to_rm)) \<sim> d \<sim> (exec_event t (Remove_Cap_Right did dst_cap right_to_rm)))"
            by (metis Event.simps(56) domain_of_event_def option.sel p1 p2 p3 p4 p5 remove_cap_right_wsc_e)
        }
        then show ?thesis by blast
        qed
      }
    then show ?thesis 
      using dynamic_weakly_step_consistent_e_def by blast
  qed
         
subsubsection{*proving the "dynamic step consistent" property*}


  theorem dynamic_weakly_step_consistent:dynamic_weakly_step_consistent
    proof -
      {
        fix e
        have "dynamic_weakly_step_consistent_e e"
          proof (induct e)
            case (Client_Lookup_Endpoint_Name x x1)
              show ?case
              using client_lookup_endpoint_name_dwsc_e by blast
            case (Send_Queuing_Message x1a x2 x3a) 
              show ?case
              using send_queuing_message_dwsc_e by blast
            case (Receive_Queuing_Message x) 
              show ?case
              using receive_queuing_message_dwsc_e by blast
            case (Get_My_Endpoints_Set x) 
              show ?case
              using get_my_endpoints_set_dwsc_e by blast
            case (Get_Caps x) 
              show ?case
              using get_caps_dwsc_e by blast
            case (Grant_Endpoint_Cap x1a x2 x3a) 
              show ?case
              using grant_endpoint_cap_dwsc_e by blast
            case (Remove_Cap_Right x1a x2 x3a) 
              show ?case
              using remove_cap_right_dwsc_e by blast
            qed
        }
    then show ?thesis 
      using dynamic_weakly_step_consistent_all_evt by blast
    qed

  theorem noninfluence_sat: noninfluence
    using dynamic_local_respect uc_eq_noninf dynamic_weakly_step_consistent weak_with_step_cons by blast

  theorem weak_noninfluence_sat: weak_noninfluence using noninf_impl_weak noninfluence_sat by blast

  theorem nonleakage_sat: nonleakage
    using noninf_impl_nonlk noninfluence_sat by blast

  theorem noninterference_r_sat: noninterference_r
    using noninf_impl_nonintf_r noninfluence_sat by blast
    
  theorem noninterference_sat: noninterference
    using noninterference_r_sat nonintf_r_impl_noninterf by blast
    
  theorem weak_noninterference_r_sat: weak_noninterference_r
    using noninterference_r_sat nonintf_r_impl_wk_nonintf_r by blast
    
  theorem weak_noninterference_sat: weak_noninterference
    using noninterference_sat nonintf_impl_weak by blast
end