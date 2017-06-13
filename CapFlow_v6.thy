theory CapFlow_v6
imports Dynamic_model_v6
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

record cap = 
  target :: domain_id
  rights :: "right set"

record Endpoint_Concig = 
  e_max_buf_size :: "endpoint_id \<rightharpoonup> max_buffer_size"
  e_name :: "endpoint_id \<rightharpoonup> endpoint_name"
  e_listener :: "endpoint_id \<rightharpoonup> domain_id"
  
record Domain_Config =                          
  d_name :: "domain_id \<rightharpoonup> domain_name"
  d_ep_id :: "domain_id \<rightharpoonup> endpoint_id"

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
               | Receive_Queuing_Message domain_id
               | Get_My_Endpointid domain_id
               | Get_Caps domain_id
               | Grant_Endpoint_Cap domain_id cap cap
               | Get_Takable_Cap domain_id cap
               | Take_Endpoint_Cap domain_id cap cap

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

definition get_endpoint_id_from_domain_id :: "Sys_Config \<Rightarrow> domain_id \<Rightarrow> endpoint_id option"
  where "get_endpoint_id_from_domain_id sc did \<equiv> 
            let
              dm_conf = (domconf sc)
            in
            if((d_ep_id dm_conf) did \<noteq> None )
            then
              ((d_ep_id dm_conf) did )
            else
              None"

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
            if(the((d_ep_id dm_conf) did) = eid )
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

definition get_ep_name_of_domain :: "Sys_Config \<Rightarrow> domain_id \<Rightarrow> endpoint_name option"
  where "get_ep_name_of_domain sc did \<equiv> 
            let
              dm_conf = (domconf sc);
              ep_conf = (commconf sc);
              eid = the((d_ep_id dm_conf) did)
            in
            if((e_name ep_conf) eid \<noteq> None )
            then
              ((e_name ep_conf) eid )
            else
              None"

definition get_ep_max_bufsize_of_domain :: "Sys_Config \<Rightarrow> domain_id \<Rightarrow> max_buffer_size option"
  where "get_ep_max_bufsize_of_domain sc did \<equiv> 
            let
              dm_conf = (domconf sc);
              ep_conf = (commconf sc);
              eid = the((d_ep_id dm_conf) did)
            in
            if((e_max_buf_size ep_conf) eid \<noteq> None )
            then
              ((e_max_buf_size ep_conf) eid )
            else
              None"

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

definition get_endpoint_id_from_domain_id_by_st :: "State \<Rightarrow> domain_id \<Rightarrow> endpoint_id option"
  where "get_endpoint_id_from_domain_id_by_st s did \<equiv> 
            let
              dom_ep = domain_endpoint s
            in
              if(\<exists>eid. the(dom_ep eid) = did)
              then
                Some (SOME eid.  the(dom_ep eid) = did)
              else
                None
              "

definition get_domain_id_from_endpoint_id_by_st :: "State \<Rightarrow> endpoint_id \<Rightarrow> domain_id option"
  where "get_domain_id_from_endpoint_id_by_st s eid \<equiv> 
            let
              dom_ep = domain_endpoint s
            in
              dom_ep eid
              "

definition get_endpoint_msg_set_from_domain_id :: "State \<Rightarrow> domain_id \<Rightarrow> Message set"
  where "get_endpoint_msg_set_from_domain_id s did \<equiv> 
            let
              dom_ep = domain_endpoint s;
              eid = get_endpoint_id_from_domain_id_by_st s did;
              msg_of_ep = e_msgs s
            in
                msg_of_ep (the (eid))
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
            if(get_domain_id_from_endpoint_id_by_st s eid \<noteq> None 
               \<and> interferes did s (the (get_domain_id_from_endpoint_id_by_st s eid)))
            then
              (s\<lparr>
                  e_msgs := emsgs(eid := new_msg_set)
                \<rparr>, False)
            else
              (s, False)"

definition receive_queuing_message :: "State \<Rightarrow> domain_id \<Rightarrow> (State \<times> Message option)"
  where "receive_queuing_message s did \<equiv> 
            if(get_endpoint_id_from_domain_id_by_st s did \<noteq> None)
            then
              let
                eid = the(get_endpoint_id_from_domain_id_by_st s did);
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

definition get_my_endpointid :: "State \<Rightarrow> domain_id \<Rightarrow> (State \<times> endpoint_id option)"
  where "get_my_endpointid s did \<equiv> 
            if(get_endpoint_id_from_domain_id_by_st s did \<noteq> None)
            then
              (s, get_endpoint_id_from_domain_id_by_st s did)
            else
              (s, None)
            "

definition get_caps :: "State \<Rightarrow> domain_id \<Rightarrow> (State \<times> cap set)"
  where "get_caps s did \<equiv> 
            (s, get_domain_cap_set_from_domain_id s did)"

definition grant_endpoint_cap :: "State \<Rightarrow> domain_id \<Rightarrow> cap \<Rightarrow> cap \<Rightarrow> (State \<times> bool)"
  where "grant_endpoint_cap s did grant_cap dst_cap \<equiv> 
            if(grant_cap\<in>get_domain_cap_set_from_domain_id s did 
              \<and> GRANT\<in>rights grant_cap
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
              \<and> dst_cap \<in> get_domain_cap_set_from_domain_id s (target take_cap)  )
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

definition system_init :: "Sys_Config \<Rightarrow> State"
  where "system_init sc \<equiv> \<lparr>
                            caps = (\<lambda> x. {}),
                            e_msgs = (\<lambda> x. {}),
                            e_buf_size = (\<lambda> x. None),
                            domain_endpoint = d_ep_id(domconf sc)
                           \<rparr>"  

subsubsection{* Instantiation and Its Proofs of Security Model  *}

consts sysconf :: "Sys_Config" 
definition sys_config_witness :: Sys_Config 
  where 
    "sys_config_witness \<equiv> \<lparr>
                            domconf  = \<lparr> 
                                         d_name = (\<lambda> x. None),
                                         d_ep_id = (\<lambda> x. None)
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
             | Receive_Queuing_Message did \<Rightarrow> fst (receive_queuing_message s did)
             | Get_My_Endpointid did \<Rightarrow> fst (get_my_endpointid s did)
             | Get_Caps did \<Rightarrow>fst (get_caps s did)
             | Grant_Endpoint_Cap did grant_cap dst_cap \<Rightarrow> fst (grant_endpoint_cap s did grant_cap dst_cap)
             | Get_Takable_Cap did take_cap \<Rightarrow> fst (get_takable_caps s did take_cap)
             | Take_Endpoint_Cap did take_cap dst_cap \<Rightarrow> fst (take_endpoint_cap s did take_cap dst_cap)
              "

definition domain_of_event :: "Event \<Rightarrow> domain_id option"
  where "domain_of_event e \<equiv> 
    case e of  Client_Lookup_Endpoint_Name did ename \<Rightarrow> Some did
             | Send_Queuing_Message did eid m \<Rightarrow> Some did
             | Receive_Queuing_Message did \<Rightarrow> Some did
             | Get_My_Endpointid did \<Rightarrow> Some did
             | Get_Caps did \<Rightarrow> Some did
             | Grant_Endpoint_Cap did grant_cap dst_cap \<Rightarrow> Some did
             | Get_Takable_Cap did take_cap \<Rightarrow> Some did
             | Take_Endpoint_Cap did take_cap dst_cap \<Rightarrow> Some did
              "

definition vpeq1 :: "State \<Rightarrow> domain_id \<Rightarrow> State \<Rightarrow> bool" ("(_ \<sim> _ \<sim> _)") 
  where
    "vpeq1 s d t \<equiv> 
       let
         cs1 = get_domain_cap_set_from_domain_id s d;
         cs2 = get_domain_cap_set_from_domain_id t d;
         dom_ep1 = get_endpoint_id_from_domain_id_by_st s d;
         dom_ep2 = get_endpoint_id_from_domain_id_by_st t d;
         dom_ms1 = get_endpoint_msg_set_from_domain_id s d;
         dom_ms2 = get_endpoint_msg_set_from_domain_id t d
       in
       if(cs1 = cs2
          \<and> (\<forall>v. interferes v s d \<longleftrightarrow> interferes v t d)
          \<and> dom_ep1 = dom_ep2
          \<and> dom_ms1 = dom_ms2)
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
        case (Get_My_Endpointid x) show ?case
          apply (induct x)
          by (simp add: exec_event_def) +
        next
        case (Get_Caps x ) show ?case
          apply (induct x)
          by (simp add: exec_event_def) +
        case (Grant_Endpoint_Cap x1a x2 x3a ) show ?case
          apply (induct x1a)
          by (simp add: exec_event_def) +
        case (Get_Takable_Cap x1a x2 ) show ?case
          apply (induct x1a)
          by (simp add: exec_event_def) +
        case (Take_Endpoint_Cap x1a x2 ) show ?case
          apply (induct x1a)
          by (simp add: exec_event_def) +
      qed
    }
  then show ?thesis by auto
  qed

declare  Let_def [cong]

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

subsubsection{*proving "send queuing message" satisfying the "local respect" property*}

  lemma send_queuing_message_notchg_domain_cap_set:
  assumes p0: "reachable0 s"
    and   p1: "\<not>(interferes did s d)"
    and   p2: "s' = fst (send_queuing_message s did eid m)"
  shows   "get_domain_cap_set_from_domain_id s d 
           = get_domain_cap_set_from_domain_id s' d"
  proof (cases "(get_domain_id_from_endpoint_id_by_st s eid \<noteq> None 
               \<and> interferes did s (the (get_domain_id_from_endpoint_id_by_st s eid)))")
    assume b0: "(get_domain_id_from_endpoint_id_by_st s eid \<noteq> None 
           \<and> interferes did s (the (get_domain_id_from_endpoint_id_by_st s eid)))"
    have b1: "get_domain_cap_set_from_domain_id s d 
           = get_domain_cap_set_from_domain_id s' d"
      using b0 p2 send_queuing_message_def get_domain_cap_set_from_domain_id_def by auto
    then show ?thesis by auto
  next
    assume b0: "\<not> (get_domain_id_from_endpoint_id_by_st s eid \<noteq> None 
              \<and> interferes did s (the (get_domain_id_from_endpoint_id_by_st s eid)))"
    have b1: "s = s'"
      using b0 p2 send_queuing_message_def by auto
    have b2: "get_domain_cap_set_from_domain_id s d 
           = get_domain_cap_set_from_domain_id s' d"
      using b1 get_domain_cap_set_from_domain_id_def by auto
    then show ?thesis by auto
  qed

  lemma send_queuing_message_notchg_policy:
  assumes p0: "reachable0 s"
    and   p1: "\<not>(interferes did s d)"
    and   p2: "s' = fst (send_queuing_message s did eid m)"
  shows   "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v s' d)"
  proof (cases "(get_domain_id_from_endpoint_id_by_st s eid \<noteq> None 
               \<and> interferes did s (the (get_domain_id_from_endpoint_id_by_st s eid)))")
    assume b0: "(get_domain_id_from_endpoint_id_by_st s eid \<noteq> None 
           \<and> interferes did s (the (get_domain_id_from_endpoint_id_by_st s eid)))"
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
    assume b0: "\<not> (get_domain_id_from_endpoint_id_by_st s eid \<noteq> None 
              \<and> interferes did s (the (get_domain_id_from_endpoint_id_by_st s eid)))"
    have b1: "s = s'"
      using b0 p2 send_queuing_message_def by auto
    have b2: "(\<forall>v. interferes v s d \<longleftrightarrow> interferes v s' d)"
      using b1 interferes_def by auto
    then show ?thesis by auto
  qed

  lemma send_queuing_message_notchg_dom_ep:
  assumes p0: "reachable0 s"
    and   p1: "\<not>(interferes did s d)"
    and   p2: "s' = fst (send_queuing_message s did eid m)"
  shows   "get_endpoint_id_from_domain_id_by_st s d 
           = get_endpoint_id_from_domain_id_by_st s' d"
  proof (cases "(get_domain_id_from_endpoint_id_by_st s eid \<noteq> None 
               \<and> interferes did s (the (get_domain_id_from_endpoint_id_by_st s eid)))")
    assume b0: "(get_domain_id_from_endpoint_id_by_st s eid \<noteq> None 
           \<and> interferes did s (the (get_domain_id_from_endpoint_id_by_st s eid)))"
    have b1: "get_domain_cap_set_from_domain_id s d 
           = get_domain_cap_set_from_domain_id s' d"
      using b0 p2 send_queuing_message_def get_domain_cap_set_from_domain_id_def by auto
    have b2: "domain_endpoint s = domain_endpoint s'"
      using b0 p2 send_queuing_message_def by auto
    have b3: "get_endpoint_id_from_domain_id_by_st s d 
           = get_endpoint_id_from_domain_id_by_st s' d"
      using b2 get_endpoint_id_from_domain_id_by_st_def by auto
    then show ?thesis by auto
  next
    assume b0: "\<not> (get_domain_id_from_endpoint_id_by_st s eid \<noteq> None 
              \<and> interferes did s (the (get_domain_id_from_endpoint_id_by_st s eid)))"
    have b1: "s = s'"
      using b0 p2 send_queuing_message_def by auto
    have b2: "get_endpoint_id_from_domain_id_by_st s d 
           = get_endpoint_id_from_domain_id_by_st s' d"
      using b1 get_endpoint_id_from_domain_id_by_st_def by auto
    then show ?thesis by auto
  qed

  lemma send_queuing_message_notchg_ep_msgs:
  assumes p0: "reachable0 s"
    and   p1: "\<not>(interferes did s d)"
    and   p2: "s' = fst (send_queuing_message s did eid m)"
  shows   "get_endpoint_msg_set_from_domain_id s d 
           = get_endpoint_msg_set_from_domain_id s' d"
  proof (cases "(get_domain_id_from_endpoint_id_by_st s eid \<noteq> None 
               \<and> interferes did s (the (get_domain_id_from_endpoint_id_by_st s eid)))")
    assume b0: "(get_domain_id_from_endpoint_id_by_st s eid \<noteq> None 
           \<and> interferes did s (the (get_domain_id_from_endpoint_id_by_st s eid)))"
    have b1: "get_domain_cap_set_from_domain_id s d 
           = get_domain_cap_set_from_domain_id s' d"
      using b0 p2 send_queuing_message_def get_domain_cap_set_from_domain_id_def by auto
    have b2: "domain_endpoint s = domain_endpoint s'"
      using b0 p2 send_queuing_message_def by auto
    have b3: "\<forall>v. v\<noteq>eid
            \<longrightarrow> ((e_msgs s) v) = ((e_msgs s') v)"
      using b0 p2 send_queuing_message_def get_endpoint_msg_set_from_domain_id_def by auto
    have b4: "domain_endpoint s = domain_endpoint s'"
      using b0 p2 send_queuing_message_def by auto
    have b5: "\<forall>w. get_endpoint_id_from_domain_id_by_st s w
           = get_endpoint_id_from_domain_id_by_st s' w"
      using b2 get_endpoint_id_from_domain_id_by_st_def by auto
    have b6: "\<forall>w. the (get_endpoint_id_from_domain_id_by_st s w)\<noteq>eid
            \<longrightarrow> ((e_msgs s) (the(get_endpoint_id_from_domain_id_by_st s w))) 
              = ((e_msgs s') (the(get_endpoint_id_from_domain_id_by_st s w)))"
      using b3 b5 get_endpoint_msg_set_from_domain_id_def  by auto
    have b7: "\<forall>w. the (get_endpoint_id_from_domain_id_by_st s w)\<noteq>eid
            \<longrightarrow> ((e_msgs s) (the(get_endpoint_id_from_domain_id_by_st s w))) 
              = ((e_msgs s') (the(get_endpoint_id_from_domain_id_by_st s' w)))"
      using b6 b5 by auto 
    have b8: "\<forall>w. the (get_endpoint_id_from_domain_id_by_st s w)\<noteq>eid 
            \<longrightarrow> get_endpoint_msg_set_from_domain_id s w
              = get_endpoint_msg_set_from_domain_id s' w"
      using b7 get_endpoint_msg_set_from_domain_id_def by auto
    have b9: "(the (get_domain_id_from_endpoint_id_by_st s eid)) \<noteq> d"
      using b0 p1 by auto
    have b10: "the ((domain_endpoint s) eid) \<noteq> d"
      using b9 get_domain_id_from_endpoint_id_by_st_def by auto
    
    have b11: "(get_endpoint_id_from_domain_id_by_st s d) \<noteq> Some eid"
      using b10 get_endpoint_id_from_domain_id_by_st_def by auto
    have b10: "the (get_endpoint_id_from_domain_id_by_st s d) \<noteq> eid"
      using b9 get_endpoint_id_from_domain_id_by_st_def by auto
    have b8: "\<forall>w. the (get_domain_id_from_endpoint_id_by_st s eid)\<noteq>w
            \<longrightarrow> get_endpoint_msg_set_from_domain_id s w
              = get_endpoint_msg_set_from_domain_id s' w"
      using b7 get_endpoint_msg_set_from_domain_id_def by auto
    have b10: "\<forall>w. w = (the ((domain_endpoint s) eid))
            \<longrightarrow> the (get_endpoint_id_from_domain_id_by_st s w) = eid "
      using get_domain_id_from_endpoint_id_by_st_def get_endpoint_id_from_domain_id_by_st_def by auto
    then show ?thesis by auto
  next
    assume b0: "\<not> (get_domain_id_from_endpoint_id_by_st s eid \<noteq> None 
              \<and> interferes did s (the (get_domain_id_from_endpoint_id_by_st s eid)))"
    have b1: "s = s'"
      using b0 p2 send_queuing_message_def by auto
    have b2: "get_endpoint_msg_set_from_domain_id s d 
           = get_endpoint_msg_set_from_domain_id s' d"
      using b1 get_endpoint_id_from_domain_id_by_st_def by auto
    then show ?thesis by auto
  qed

end