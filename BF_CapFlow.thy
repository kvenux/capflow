
theory BF_CapFlow
imports Dynamic_model_v6 CapFlow_v6_0

begin

subsection {* Definitions *}

subsubsection {* Data type, basic components, and state *}

type_synonym systime_t = nat
type_synonym cte = nat
type_synonym lpaddr_t = nat
type_synonym dispatcher_handle_t = nat
type_synonym genpaddr_t = nat
type_synonym pasid_t = nat
type_synonym gensize_t = nat
type_synonym lvaddr_t = nat
type_synonym coreid_t = nat
type_synonym capaddr_t = nat

datatype sched_state = SCHED_RR | SCHED_RBED

datatype
  task_type =  TASK_TYPE_BEST_EFFORT
              |TASK_TYPE_SOFT_REALTIME
              |TASK_TYPE_HARD_REALTIME    

datatype
  sys_err =  SYS_ERR_OK
              |SYS_ERR_CAP_NOT_FOUND
              |SYS_ERR_LMP_TARGET_DISABLED   
              |SYS_ERR_LMP_BUF_OVERFLOW

datatype
  objtype =  ObjType_IPI
            |ObjType_KernelControlBlock
            |ObjType_PerfMon
            |ObjType_ID
            |ObjType_Notify_IPI
            |ObjType_IO
            |ObjType_IRQSrc
            |ObjType_IRQDest
            |ObjType_IRQTable
            |ObjType_Kernel
            |ObjType_DevFrame_Mapping
            |ObjType_DevFrame
            |ObjType_Frame_Mapping
            |ObjType_Frame
            |ObjType_EndPoint
            |ObjType_Dispatcher
            |ObjType_FCNode
            |ObjType_L2CNode
            |ObjType_L1CNode
            |ObjType_RAM
            |ObjType_PhysAddr
            |ObjType_Null

datatype cap_state = DISTCAP_STATE_FOREIGN | DISTCAP_STATE_BUSY

record dcb = disabled :: bool
             is_vm_guest :: bool
             domain_id_dcb :: domain_id
             t_type :: task_type
             wakeup_time :: systime_t
             release_time :: systime_t
             etime :: systime_t
             last_dispatch :: systime_t
             wcet :: systime_t
             period :: systime_t
             deadline :: systime_t
             weight :: nat
             cspace :: cte
             vspace :: lpaddr_t
             disp :: dispatcher_handle_t

record PhysAddr = base :: genpaddr_t
                  pasid :: pasid_t
                  bytes :: gensize_t

record RAM = base :: genpaddr_t
                  pasid :: pasid_t
                  bytes :: gensize_t

record L1CNode =  cnode :: lpaddr_t
                  rightsmask :: right
                  allocated_bytes :: gensize_t

record L2CNode =  cnode :: lpaddr_t
                  rightsmask :: right

record FCNode =   cnode :: genpaddr_t
                  bits :: nat
                  rightsmask :: right
                  core_id :: coreid_t
                  guard_size :: nat
                  guard :: capaddr_t

record Dispatcher = dcb_d :: dcb

record EndPoint = listener :: domain_id
                  epoffset :: lvaddr_t
                  epbuflen :: nat

record Frame =    base :: genpaddr_t
                  pasid :: pasid_t
                  bytes :: gensize_t

record DevFrame = base :: genpaddr_t
                  pasid :: pasid_t
                  bytes :: gensize_t

record capability_u =
                  physaddr :: PhysAddr
                  ram :: RAM
                  l1cnode :: L1CNode
                  l2cnode :: L2CNode
                  fcnode :: FCNode
                  dispatcher :: Dispatcher
                  endpoint :: EndPoint
                  frame :: Frame
                  devframe :: DevFrame

record capability = type :: objtype
                    rights :: right
                    union_of_cap :: capability_u
                    state_of_cap :: cap_state

record StateR = State + 
                dispatchers :: "domain_id \<rightharpoonup> dcb"
                cspaces :: "domain_id \<Rightarrow> capability set"

definition abstract_state :: "StateR \<Rightarrow> State" ("\<Up>_" [50])        


  where "abstract_state r = \<lparr>caps = caps r,
                            e_msgs = e_msgs r,
                            e_buf_size = e_buf_size r,
                            domain_endpoint = domain_endpoint r
                           \<rparr>"

definition abstract_state_rev :: "StateR \<Rightarrow> State \<Rightarrow> StateR" ("_\<Down>_" [50])
  where "abstract_state_rev r' r = r'\<lparr>caps := caps r,
                            e_msgs := e_msgs r,
                            e_buf_size := e_buf_size r,
                            domain_endpoint := domain_endpoint r\<rparr>"

datatype EventR = Client_Lookup_Endpoint_Name domain_id endpoint_name
               | Send_Queuing_Message domain_id endpoint_id Message
               | Receive_Queuing_Message domain_id endpoint_id
               | Get_My_Endpoints_Set domain_id
               | Get_Caps domain_id
               | Grant_Endpoint_Cap domain_id cap cap
               | Remove_Cap_Right domain_id cap right
               | Sys_Dispatcher_Properties domain_id task_type systime_t systime_t systime_t nat systime_t
               | Sys_Dispatcher_Setup domain_id cte lpaddr_t dispatcher_handle_t bool
               | Dispatcher_Dump_Ptables domain_id
               | Dispatcher_Dump_Capabilities domain_id
               | Capability_Copy domain_id capability
               | Capability_Retype domain_id capability objtype
               | Capability_Mint domain_id capability nat nat
               | Capability_Delete domain_id capability
               | Capability_Get_State domain_id capability

subsubsection {* Utility Functions used for Event Specification *} 


subsubsection {* Events Specification *}

definition client_lookup_endpoint_nameR :: "Sys_Config \<Rightarrow> StateR 
              \<Rightarrow> domain_id \<Rightarrow> endpoint_name \<Rightarrow> (StateR \<times> endpoint_id option)" 
  where "client_lookup_endpoint_nameR sc sr did ename \<equiv> 
                                          let 
                                            ret = (client_lookup_endpoint_name sc (\<Up>sr) did ename) 
                                          in
                                            (sr\<Down>(fst ret),snd ret)"

definition send_queuing_messageR :: "StateR \<Rightarrow> domain_id \<Rightarrow> endpoint_id \<Rightarrow> Message \<Rightarrow> (StateR \<times> bool)"
  where "send_queuing_messageR sr did eid m \<equiv>
                                          let 
                                            ret = (send_queuing_message (\<Up>sr) did eid m) 
                                          in
                                            (sr\<Down>(fst ret),snd ret)"

definition receive_queuing_messageR :: "StateR \<Rightarrow> domain_id \<Rightarrow> endpoint_id \<Rightarrow> (StateR \<times> Message option)"
  where "receive_queuing_messageR sr did eid \<equiv> 
                                          let 
                                            ret = (receive_queuing_message (\<Up>sr) did eid) 
                                          in
                                            (sr\<Down>(fst ret),snd ret)"

definition get_my_endpoints_setR :: "StateR \<Rightarrow> domain_id \<Rightarrow> (StateR \<times> endpoint_id set)"
  where "get_my_endpoints_setR sr did \<equiv> 
                                  let 
                                    ret = (get_my_endpoints_set (\<Up>sr) did) 
                                  in
                                    (sr\<Down>(fst ret),snd ret)"

definition get_capsR :: "StateR \<Rightarrow> domain_id \<Rightarrow> (StateR \<times> cap set)"
  where "get_capsR sr did \<equiv> 
                      let 
                        ret = (get_caps (\<Up>sr) did) 
                      in
                        (sr\<Down>(fst ret),snd ret)"

definition grant_endpoint_capR :: "StateR \<Rightarrow> domain_id \<Rightarrow> cap \<Rightarrow> cap \<Rightarrow> (StateR \<times> bool)"
  where "grant_endpoint_capR sr did grant_cap dst_cap \<equiv> 
                      let 
                        ret = (grant_endpoint_cap (\<Up>sr) did grant_cap dst_cap) 
                      in
                        (sr\<Down>(fst ret),snd ret)"

definition remove_cap_rightR :: "StateR \<Rightarrow> domain_id \<Rightarrow> cap \<Rightarrow> right \<Rightarrow> (StateR
 \<times> bool)"
  where "remove_cap_rightR sr did rm_cap right_to_rm \<equiv> 
                                          let 
                                            ret = (remove_cap_right (\<Up>sr) did rm_cap right_to_rm) 
                                          in
                                            (sr\<Down>(fst ret),snd ret)"

definition sys_dispatcher_properties :: "StateR \<Rightarrow> domain_id \<Rightarrow> task_type \<Rightarrow> systime_t  \<Rightarrow> systime_t 
                                        \<Rightarrow> systime_t \<Rightarrow> nat \<Rightarrow> systime_t \<Rightarrow> (StateR \<times> bool )" where
  "sys_dispatcher_properties sr did p_type p_deadline p_wcet p_period p_release p_weight \<equiv>   
                   let
                    new_dispatchers = dispatchers sr;
                    t_dcb = the(new_dispatchers did);
                    new_dcb =t_dcb\<lparr> 
                                    wcet := p_wcet,
                                    t_type := p_type,
                                    deadline := p_deadline,
                                    period := p_period,
                                    release_time := p_release,
                                    weight := p_weight,
                                    is_vm_guest := is_vm_guest t_dcb,
                                    domain_id_dcb := domain_id_dcb t_dcb,
                                    wakeup_time := wakeup_time t_dcb,
                                    release_time := release_time t_dcb\<rparr>
                  in
                    (sr\<lparr>
                      dispatchers := new_dispatchers(did := Some new_dcb)
                      \<rparr>, True)"

definition sys_dispatcher_setup :: "StateR \<Rightarrow> domain_id \<Rightarrow> cte \<Rightarrow> lpaddr_t  \<Rightarrow> dispatcher_handle_t 
                                        \<Rightarrow> bool \<Rightarrow> (StateR \<times> bool )" where
  "sys_dispatcher_setup sr did p_cptr p_vptr p_dptr p_run \<equiv>
                  if(p_run = True)
                  then
                    let
                      new_dispatchers = dispatchers sr;
                      t_dcb = the (new_dispatchers did);
                      new_dcb = t_dcb
                                  \<lparr> 
                                    cspace := p_cptr,
                                    vspace := p_vptr,
                                    disp := p_dptr,
                                    disabled := True
                                  \<rparr>
                    in
                      (sr\<lparr>
                        dispatchers := new_dispatchers(did := Some new_dcb)
                        \<rparr>, True)
                  else
                    let
                      new_dispatchers = dispatchers sr;
                      t_dcb = the(new_dispatchers did);
                      new_dcb = t_dcb
                                  \<lparr> 
                                    cspace := p_cptr,
                                    vspace := p_vptr,
                                    disp := p_dptr
                                  \<rparr>
                    in
                      (sr\<lparr>
                        dispatchers := new_dispatchers(did := Some new_dcb)
                        \<rparr>, True)"

definition dispatcher_dump_ptables :: "StateR \<Rightarrow> domain_id \<Rightarrow> (StateR \<times> bool )" where
  "dispatcher_dump_ptables sr did  \<equiv> (sr, True)"

definition dispatcher_dump_capabilities :: "StateR \<Rightarrow> domain_id \<Rightarrow> (StateR \<times> cap set )" where
  "dispatcher_dump_capabilities sr did  \<equiv> let 
                                            ret = (get_caps (\<Up>sr) did) 
                                           in
                                            (sr\<Down>(fst ret),snd ret)"

(*
definition dispatcher_get_all_ep :: "StateR \<Rightarrow> domain_id \<Rightarrow> (StateR \<times> cap set )" where
  "dispatcher_get_all_ep sr did  \<equiv> let 
                                            ret = (get_caps (\<Up>sr) did) 
                                           in
                                            (sr\<Down>(fst ret),snd ret)"
*)

definition capability_copy :: "StateR \<Rightarrow> domain_id \<Rightarrow> capability \<Rightarrow> (StateR \<times> bool )" where
  "capability_copy sr did c \<equiv> 
                  let
                    c_space = cspaces sr;
                    c_set = c_space did
                  in
                    (sr\<lparr>
                      cspaces := c_space(did := insert c c_set)
                      \<rparr>, True)"

definition capability_retype :: "StateR \<Rightarrow> domain_id \<Rightarrow> capability \<Rightarrow> objtype \<Rightarrow> (StateR \<times> bool )" where
  "capability_retype sr did cap_retype dst_type \<equiv> 
                  let
                    c_space = cspaces sr;
                    c_set = c_space did;
                    c_set_rest =  {c. c\<in>c_set \<and> c\<noteq>cap_retype};
                    retyped_cap = cap_retype\<lparr>
                      type := dst_type
                      \<rparr>
                  in
                    (sr\<lparr>
                      cspaces := c_space(did := insert retyped_cap c_set_rest)
                      \<rparr>, True)"

definition capability_mint :: "StateR \<Rightarrow> domain_id \<Rightarrow> capability \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (StateR \<times> bool )" where
  "capability_mint sr did cap_mint param1 param2 \<equiv> 
                  let
                    c_space = cspaces sr;
                    c_set = c_space did;
                    c_set_rest =  {c. c\<in>c_set \<and> c\<noteq>cap_mint};
                    cap_u = union_of_cap cap_mint;
                    cap_endpoint = endpoint cap_u;
                    cap_endpoint_minted = cap_endpoint\<lparr>
                      epoffset := param1,
                      epbuflen := param2
                    \<rparr>;
                    cap_u_minted = cap_u\<lparr>
                      endpoint := cap_endpoint_minted
                    \<rparr>;
                    cap_minted = cap_mint\<lparr>
                      union_of_cap := cap_u_minted
                    \<rparr>
                  in
                    if(type cap_mint = ObjType_EndPoint)
                    then
                      (sr
                      \<lparr>
                        cspaces := c_space(did := insert cap_minted c_set_rest)
                      \<rparr>, True)
                    else
                      (sr, False)"

definition capability_delete :: "StateR \<Rightarrow> domain_id \<Rightarrow> capability \<Rightarrow> (StateR \<times> bool )" where
  "capability_delete sr did cap_del \<equiv> 
                    let
                    c_space = cspaces sr;
                    c_set = c_space did;
                    c_set_rest =  {c. c\<in>c_set \<and> c\<noteq>cap_del}
                  in
                    (sr
                      \<lparr>
                        cspaces := c_space(did := c_set_rest)
                      \<rparr>, True)"

definition capability_get_state :: "StateR \<Rightarrow> domain_id \<Rightarrow> capability \<Rightarrow> (StateR \<times> cap_state )" where
  "capability_get_state sr did cap_dst \<equiv> 
                    let
                    c_space = cspaces sr;
                    c_set = c_space did
                  in
                    (sr, state_of_cap cap_dst)"

definition system_initR :: "Sys_Config \<Rightarrow> StateR"
  where "system_initR sc \<equiv> let s0 = system_init sc in 
                              \<lparr> caps = caps s0,
                                e_msgs = e_msgs s0,
                                e_buf_size = e_buf_size s0,
                                domain_endpoint = domain_endpoint s0,
                                dispatchers = (\<lambda> x. None),
                                cspaces = (\<lambda> x. {})
                               \<rparr>"

declare abstract_state_def[cong del] and abstract_state_rev_def[cong del] and 
        client_lookup_endpoint_nameR_def [cong del] and 
        send_queuing_messageR_def[cong del] and
        receive_queuing_messageR_def[cong del] and
        get_my_endpoints_setR_def[cong del] and
        get_capsR_def[cong del] and
        grant_endpoint_capR_def[cong del] and
        remove_cap_rightR_def[cong del]

declare abstract_state_def[cong] and abstract_state_rev_def[cong] and 
        client_lookup_endpoint_nameR_def [cong ] and 
        send_queuing_messageR_def[cong ] and
        receive_queuing_messageR_def[cong ] and
        get_my_endpoints_setR_def[cong ] and
        get_capsR_def[cong ] and
        grant_endpoint_capR_def[cong ] and
        remove_cap_rightR_def[cong ]

subsection{* Instantiation and Its Proofs of Security Model  *}

consts s0r :: StateR

specification (s0r) 
  s0r_init: "s0r = system_initR sysconf"
  by simp

definition exec_eventR :: "StateR \<Rightarrow> EventR \<Rightarrow> StateR" 
  where "exec_eventR s e  \<equiv>
    case e of  Client_Lookup_Endpoint_Name did ename 
             \<Rightarrow> fst (client_lookup_endpoint_nameR sysconf s did ename)
             | Send_Queuing_Message did eid m 
             \<Rightarrow> fst (send_queuing_messageR s did eid m)
             | Receive_Queuing_Message did eid 
             \<Rightarrow> fst (receive_queuing_messageR s did eid)
             | Get_My_Endpoints_Set did 
             \<Rightarrow> fst (get_my_endpoints_setR s did)
             | Get_Caps did 
             \<Rightarrow> fst (get_capsR s did)
             | Grant_Endpoint_Cap did grant_cap dst_cap 
             \<Rightarrow> fst (grant_endpoint_capR s did grant_cap dst_cap)
             | Remove_Cap_Right did dst_cap right_to_rm 
             \<Rightarrow> fst (remove_cap_rightR s did dst_cap right_to_rm)
             | Sys_Dispatcher_Properties did p_type p_deadline p_wcet p_period p_release p_weight
             \<Rightarrow> fst (sys_dispatcher_properties s did p_type p_deadline p_wcet p_period p_release p_weight)
             | Sys_Dispatcher_Setup did p_cptr p_vptr p_dptr p_run
             \<Rightarrow> fst (sys_dispatcher_setup s did p_cptr p_vptr p_dptr p_run)
             | Dispatcher_Dump_Ptables did 
             \<Rightarrow> fst (dispatcher_dump_ptables s did)
             | Dispatcher_Dump_Capabilities did 
             \<Rightarrow> fst (dispatcher_dump_capabilities s did)
             | Capability_Copy did c
             \<Rightarrow> fst (capability_copy s did c)
             | Capability_Retype did cap_retype dst_type
             \<Rightarrow> fst (capability_retype s did cap_retype dst_type)
             | Capability_Mint did cap_mint param1 param2
             \<Rightarrow> fst (capability_mint s did cap_mint param1 param2)
             | Capability_Delete did cap_del
             \<Rightarrow> fst (capability_delete s did cap_del)
             | Capability_Get_State did cap_dst
             \<Rightarrow> fst (capability_get_state s did cap_dst)
             "

definition domain_of_eventR :: "EventR \<Rightarrow> domain_id option"
  where "domain_of_eventR e \<equiv> 
    case e of  Client_Lookup_Endpoint_Name did ename \<Rightarrow> Some did
             | Send_Queuing_Message did eid m \<Rightarrow> Some did
             | Receive_Queuing_Message did eid \<Rightarrow> Some did
             | Get_My_Endpoints_Set did \<Rightarrow> Some did
             | Get_Caps did \<Rightarrow> Some did
             | Grant_Endpoint_Cap did grant_cap dst_cap \<Rightarrow> Some did
             | Remove_Cap_Right did dst_cap right_to_rm  \<Rightarrow> Some did
             | Sys_Dispatcher_Properties did p_type p_deadline p_wcet p_period p_release p_weight \<Rightarrow> Some did
             | Sys_Dispatcher_Setup did p_cptr p_vptr p_dptr p_run \<Rightarrow> Some did
             | Dispatcher_Dump_Ptables did \<Rightarrow> Some did 
             | Dispatcher_Dump_Capabilities did \<Rightarrow> Some did 
             | Capability_Copy did c \<Rightarrow> Some did
             | Capability_Retype did cap_retype dst_type \<Rightarrow> Some did
             | Capability_Mint did cap_mint param1 param2 \<Rightarrow> Some did
             | Capability_Delete did cap_del \<Rightarrow> Some did
             | Capability_Get_State did cap_dst \<Rightarrow> Some did
              "

definition vpeq_dispatcher :: "StateR \<Rightarrow> domain_id \<Rightarrow> StateR \<Rightarrow> bool" ("(_ \<sim>. _ .\<sim>\<^sub>\<Delta> _)")
  where "vpeq_dispatcher s d t \<equiv> dispatchers s d = dispatchers t d
                                 \<and> cspaces s d = cspaces t d" 

lemma vpeq_dispatcher_transitive_lemma : 
  "\<forall> s t r d. (vpeq_dispatcher s d t) \<and> (vpeq_dispatcher t d r) \<longrightarrow> (vpeq_dispatcher s d r)"
  using vpeq_dispatcher_def by auto

lemma vpeq_dispatcher_symmetric_lemma : "\<forall> s t d. (vpeq_dispatcher s d t) \<longrightarrow> (vpeq_dispatcher t d s)"
  using vpeq_dispatcher_def by auto

lemma vpeq_dispatcher_reflexive_lemma : "\<forall> s d. (vpeq_dispatcher s d s)"
  using vpeq_dispatcher_def by auto

definition vpeqR :: "StateR \<Rightarrow> domain_id \<Rightarrow> StateR \<Rightarrow> bool" ("(_ \<sim>. _ .\<sim> _)")
  where "vpeqR s d t \<equiv>  ((\<Up>s) \<sim>d\<sim> (\<Up>t)) \<and> (s\<sim>.d.\<sim>\<^sub>\<Delta>t)"                         


declare vpeqR_def[cong] and vpeq_dispatcher_def[cong]


lemma vpeqR_transitive_lemma : "\<forall> s t r d. (vpeqR s d t) \<and> (vpeqR t d r) \<longrightarrow> (vpeqR s d r)"
    apply(clarsimp cong del: vpeq1_def)
    using vpeq1_transitive_lemma vpeq_dispatcher_transitive_lemma by blast

lemma vpeqR_symmetric_lemma : "\<forall> s t d. (vpeqR s d t) \<longrightarrow> (vpeqR t d s)"
  apply(clarsimp cong del: vpeq1_def)
  using vpeq1_symmetric_lemma vpeq_dispatcher_symmetric_lemma by blast

lemma vpeqR_reflexive_lemma : "\<forall> s d. (vpeqR s d s)"  
  using vpeq1_reflexive_lemma vpeq_dispatcher_reflexive_lemma by auto

lemma vpeqR_vpeq1 : "vpeqR s d t \<Longrightarrow> vpeq1 (\<Up>s) d (\<Up>t)"
  using vpeqR_def by blast

definition interferesR :: "domain_id \<Rightarrow> StateR \<Rightarrow> domain_id \<Rightarrow> bool"
  where "interferesR w s v \<equiv> interferes w (\<Up>s) v"

lemma interfR_reflexive_lemma : "\<forall>d s. interferesR d s d" 
  using interferes_def interferesR_def by auto

lemma policy_respectR_lemma : "\<forall>v u s t. (s \<sim>. u .\<sim>t)
                              \<longrightarrow> (interferesR v s u = interferesR v t u)"
  using interferesR_def vpeqR_def by auto

lemma reachable_l2: "\<forall> s a. (SM.reachable0 s0r exec_eventR) s \<longrightarrow> (\<exists>s'. s' = exec_eventR s a)"
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

interpretation SM_enabled 
    s0r exec_eventR domain_of_eventR vpeqR interferesR
   using vpeqR_transitive_lemma vpeqR_symmetric_lemma vpeqR_reflexive_lemma
          interfR_reflexive_lemma policy_respectR_lemma reachable_l2
          SM.intro[of vpeqR interferesR]
          SM_enabled_axioms.intro[of s0r exec_eventR]
          SM_enabled.intro[of vpeqR interferesR s0r exec_eventR] by blast

subsection{* Proofs of refinement *}

subsubsection{* Refinement of existing events at upper level *}

lemma client_lookup_endpoint_name_ref_lemma: 
    "\<forall>s. fst (client_lookup_endpoint_name sc (\<Up>s) did ename) 
          = \<Up>(fst (client_lookup_endpoint_nameR sc s did ename))"
    by auto

lemma send_queuing_message_ref_lemma: 
    "\<forall>s. fst (send_queuing_message (\<Up>sr) did eid m) 
          = \<Up>(fst (send_queuing_messageR sr did eid m ))"
    by auto

lemma receive_queuing_message_ref_lemma: 
    "\<forall>s. fst (receive_queuing_message (\<Up>sr) did eid) 
            = \<Up>(fst (receive_queuing_messageR sr did eid))"
    by auto

lemma get_my_endpoints_set_ref_lemma: 
    "\<forall>s. fst (get_my_endpoints_set (\<Up>sr) did) = \<Up>(fst (get_my_endpoints_setR sr did))"
    by auto

lemma get_caps_ref_lemma: 
    "\<forall>s. fst (get_caps (\<Up>sr) did) = \<Up>(fst (get_capsR sr did))"
    by auto

lemma grant_endpoint_cap_ref_lemma: 
    "\<forall>s. fst (grant_endpoint_cap (\<Up>sr) did grant_cap dst_cap) 
              = \<Up>(fst (grant_endpoint_capR sr did grant_cap dst_cap))"
    by auto

lemma remove_cap_right_ref_lemma: 
    "\<forall>s. fst (remove_cap_right (\<Up>sr) did rm_cap right_to_rm) 
              = \<Up>(fst (remove_cap_rightR sr did rm_cap right_to_rm))"
    by auto

subsubsection{* new events introduced at this level dont change abstract state *}



subsubsection{* proof of refinement *}

  lemma s0_ref_lemma : "(\<Up>s0r) = s0t" 
     by (simp add:  s0t_init s0r_init system_initR_def ) 


subsection{* Existing events preserve "local respect" on new state variables *} 

subsubsection{*proving "client lookup endpoint name"*}

  lemma crt_smpl_portR_presrv_lcrsp_new:
      assumes p3:"s' = fst (client_lookup_endpoint_nameR sc s did ename)"
      shows   "s \<sim>. d .\<sim>\<^sub>\<Delta> s'" using p3 by fastforce    

end