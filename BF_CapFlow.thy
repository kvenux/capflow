
theory BF_CapFlow
imports Dynamic_model CapFlow

begin
declare [[ smt_timeout = 90 ]]

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

definition event_enabledR :: "StateR \<Rightarrow> EventR \<Rightarrow> bool"
  where "event_enabledR s e \<equiv> True"

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

primrec runR :: "StateR \<Rightarrow> EventR list \<Rightarrow> StateR" 
  where runR_Nil: "runR s [] = s" |
        runR_Cons: "runR s (a#as) = runR (exec_eventR s a) as "

definition eR :: "EventR \<Rightarrow> Event option" where
  "eR e \<equiv>  case e of  Client_Lookup_Endpoint_Name did ename \<Rightarrow> Some (Event.Client_Lookup_Endpoint_Name did ename)
             | Send_Queuing_Message did eid m \<Rightarrow> Some (Event.Send_Queuing_Message did eid m)
             | Receive_Queuing_Message did eid \<Rightarrow> Some (Event.Receive_Queuing_Message did eid)
             | Get_My_Endpoints_Set did \<Rightarrow> Some (Event.Get_My_Endpoints_Set did)
             | Get_Caps did \<Rightarrow> Some (Event.Get_Caps did)
             | Grant_Endpoint_Cap did grant_cap dst_cap \<Rightarrow> Some (Event.Grant_Endpoint_Cap did grant_cap dst_cap)
             | Remove_Cap_Right did dst_cap right_to_rm  \<Rightarrow> Some (Event.Remove_Cap_Right did dst_cap right_to_rm)
             | Sys_Dispatcher_Properties did p_type p_deadline p_wcet p_period p_release p_weight \<Rightarrow> None
             | Sys_Dispatcher_Setup did p_cptr p_vptr p_dptr p_run \<Rightarrow> None
             | Dispatcher_Dump_Ptables did \<Rightarrow> None
             | Capability_Copy did c \<Rightarrow> None
             | Capability_Retype did cap_retype dst_type \<Rightarrow> None
             | Capability_Mint did cap_mint param1 param2 \<Rightarrow> None
             | Capability_Delete did cap_del \<Rightarrow> None
             | Capability_Get_State did cap_dst \<Rightarrow> None
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

subsection{* Unwinding conditions on new state variables *}

  definition dynamic_step_consistent_new :: "bool" where 
    "dynamic_step_consistent_new \<equiv>  \<forall>a d s t. reachable0 s \<and> reachable0 t \<and> (s \<sim>. d .\<sim> t) \<and> 
                              interferesR (the (domain_of_eventR a)) s d \<longrightarrow> (s \<sim>. (the (domain_of_eventR a)) .\<sim> t)
                              \<longrightarrow> ((exec_eventR s a) \<sim>. d .\<sim> (exec_eventR t a))"

  definition dynamic_weakly_step_consistent_new :: "bool" where 
        "dynamic_weakly_step_consistent_new \<equiv>  \<forall>a d s t. reachable0 s \<and> reachable0 t \<and> (s \<sim>. d .\<sim> t) \<and>
                              interferesR (the (domain_of_eventR a)) s d \<and> (s \<sim>. (the (domain_of_eventR a)) .\<sim> t)
                              \<longrightarrow> ((exec_eventR s a) \<sim>. d .\<sim> (exec_eventR t a))"

  definition dynamic_local_respect_new :: "bool" where
        "dynamic_local_respect_new \<equiv> \<forall>a d s. reachable0 s \<and> \<not>interferesR (the (domain_of_eventR a)) s d 
                              \<longrightarrow> (s \<sim>. d .\<sim> (exec_eventR s a)) "

  definition dynamic_step_consistent_new_e :: "EventR \<Rightarrow> bool" where 
    "dynamic_step_consistent_new_e a \<equiv>  \<forall> d s t. reachable0 s \<and> reachable0 t \<and> (s \<sim>. d .\<sim> t) \<and> 
                              interferesR (the (domain_of_eventR a)) s d \<longrightarrow> (s \<sim>. (the (domain_of_eventR a)) .\<sim> t)
                              \<longrightarrow> ((exec_eventR s a) \<sim>. d .\<sim> (exec_eventR t a))"
  
  definition dynamic_weakly_step_consistent_new_e :: "EventR \<Rightarrow> bool" where 
        "dynamic_weakly_step_consistent_new_e a \<equiv>  \<forall>d s t. reachable0 s \<and> reachable0 t \<and> (s \<sim>. d .\<sim> t) \<and>
                              interferesR (the (domain_of_eventR a)) s d \<and> (s \<sim>. (the (domain_of_eventR a)) .\<sim> t)
                              \<longrightarrow> ((exec_eventR s a) \<sim>. d .\<sim> (exec_eventR t a))"

  definition dynamic_local_respect_new_e :: "EventR \<Rightarrow> bool" where
        "dynamic_local_respect_new_e a \<equiv> \<forall>d s. reachable0 s \<and> \<not>interferesR (the (domain_of_eventR a)) s d 
                              \<longrightarrow> (s \<sim>. d .\<sim> (exec_eventR s a)) "

  declare dynamic_step_consistent_new_def[cong del] and dynamic_weakly_step_consistent_new_def[cong del] 
        and dynamic_local_respect_new_def[cong del] and dynamic_step_consistent_new_e_def[cong del] 
        and dynamic_weakly_step_consistent_new_e_def[cong del] and dynamic_local_respect_new_e_def[cong del] 

  declare dynamic_step_consistent_new_def[cong] and dynamic_weakly_step_consistent_new_def[cong] 
        and dynamic_local_respect_new_def[cong] and dynamic_step_consistent_new_e_def[cong] 
        and dynamic_weakly_step_consistent_new_e_def[cong] and dynamic_local_respect_new_e_def[cong] 

  declare dynamic_step_consistent_new_def[cong del] and dynamic_weakly_step_consistent_new_def[cong del] 
        and dynamic_local_respect_new_def[cong del] and dynamic_step_consistent_new_e_def[cong del]
        and dynamic_weakly_step_consistent_new_e_def[cong del] and dynamic_local_respect_new_e_def[cong del]


  lemma dynamic_step_consistent_new_all_evt : "dynamic_step_consistent_new = (\<forall>a. dynamic_step_consistent_new_e a)"
    by (simp add:dynamic_step_consistent_new_def dynamic_step_consistent_new_e_def)


  lemma dynamic_weakly_step_consistent_new_all_evt : "dynamic_weakly_step_consistent_new = (\<forall>a. dynamic_weakly_step_consistent_new_e a)"
    by (simp add:dynamic_weakly_step_consistent_new_def dynamic_weakly_step_consistent_new_e_def)


  lemma dynamic_local_respect_new_all_evt : "dynamic_local_respect_new = (\<forall>a. dynamic_local_respect_new_e a)"
    by (simp add:dynamic_local_respect_new_def dynamic_local_respect_new_e_def)


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

lemma sys_dispatcher_properties_nchastate_lemma: 
    "\<forall>s. (\<Up>s) = \<Up>(fst (sys_dispatcher_properties s did p_type p_deadline p_wcet p_period p_release p_weight))" 
     using sys_dispatcher_properties_def by auto

lemma sys_dispatcher_setup_nchastate_lemma: 
    "\<forall>s. (\<Up>s) = \<Up>(fst (sys_dispatcher_setup s did p_cptr p_vptr p_dptr p_run))" 
     using sys_dispatcher_setup_def by auto

lemma dispatcher_dump_ptables_nchastate_lemma: 
    "\<forall>s. (\<Up>s) = \<Up>(fst (dispatcher_dump_ptables s did))" 
     using dispatcher_dump_ptables_def by auto

lemma capability_copy_nchastate_lemma: 
    "\<forall>s. (\<Up>s) = \<Up>(fst (capability_copy s did c))" 
     using capability_copy_def by auto

lemma capability_retype_nchastate_lemma: 
    "\<forall>s. (\<Up>s) = \<Up>(fst (capability_retype s did cap_retype dst_type))" 
     using capability_retype_def by auto

lemma capability_mint_nchastate_lemma: 
    "\<forall>s. (\<Up>s) = \<Up>(fst (capability_mint s did cap_mint param1 param2))" 
     using capability_mint_def by auto

lemma capability_delete_nchastate_lemma: 
    "\<forall>s. (\<Up>s) = \<Up>(fst (capability_delete s did cap_del))" 
     using capability_delete_def by auto

lemma capability_get_state_nchastate_lemma: 
    "\<forall>s. (\<Up>s) = \<Up>(fst (capability_get_state s did cap_dst))" 
     using capability_get_state_def by auto  
                                                
subsubsection{* proof of refinement *}

  lemma s0_ref_lemma : "(\<Up>s0r) = s0t" 
     by (simp add:  s0t_init s0r_init system_initR_def ) 

  lemma refine_exec_event : "t = exec_eventR s e \<Longrightarrow> (eR e = None \<longrightarrow> (\<Up>s) = (\<Up>t)) 
    \<and> (eR e \<noteq> None \<longrightarrow> (\<Up>t) = exec_event (\<Up>s) (the (eR e)))"
  proof -
      assume p0: "t = exec_eventR s e"
      then show "(eR e = None \<longrightarrow> (\<Up>s) = (\<Up>t)) \<and> (eR e \<noteq> None \<longrightarrow> (\<Up>t) = exec_event (\<Up>s) (the (eR e)))"
      proof(induct e)
        case (Client_Lookup_Endpoint_Name did ename)
          let ?e = "Event.Client_Lookup_Endpoint_Name did ename"
          let ?er = "Client_Lookup_Endpoint_Name did ename"
          have "(\<Up>t) = exec_event (\<Up>s) ?e"
            using client_lookup_endpoint_name_ref_lemma exec_eventR_def exec_event_def Client_Lookup_Endpoint_Name.prems  
              by (auto cong del: abstract_state_def)
          then show ?case using eR_def by auto
      next
        case (Send_Queuing_Message did eid m)
          let ?e = "Event.Send_Queuing_Message did eid m"
          let ?er = "Send_Queuing_Message did eid m"
          have "(\<Up>t) = exec_event (\<Up>s) ?e"
            using send_queuing_message_ref_lemma exec_eventR_def exec_event_def Send_Queuing_Message.prems  
              by (auto cong del: abstract_state_def)
          then show ?case using eR_def by auto
      next
        case (Receive_Queuing_Message did eid)
          let ?e = "Event.Receive_Queuing_Message did eid"
          let ?er = "Receive_Queuing_Message did eid"
          have "(\<Up>t) = exec_event (\<Up>s) ?e"
            using receive_queuing_message_ref_lemma exec_eventR_def exec_event_def Receive_Queuing_Message.prems  
              by (auto cong del: abstract_state_def)
          then show ?case using eR_def by auto
      next
        case (Get_My_Endpoints_Set did)
          let ?e = "Event.Get_My_Endpoints_Set did"
          let ?er = "Get_My_Endpoints_Set did"
          have "(\<Up>t) = exec_event (\<Up>s) ?e"
            using get_my_endpoints_set_ref_lemma exec_eventR_def exec_event_def Get_My_Endpoints_Set.prems  
              by (auto cong del: abstract_state_def)
          then show ?case using eR_def by auto
      next
        case (Get_Caps did)
          let ?e = "Event.Get_Caps did"
          let ?er = "Get_Caps did"
          have "(\<Up>t) = exec_event (\<Up>s) ?e"
            using get_caps_ref_lemma exec_eventR_def exec_event_def Get_Caps.prems  
              by (auto cong del: abstract_state_def)
          then show ?case using eR_def by auto
      next
        case (Grant_Endpoint_Cap did grant_cap dst_cap)
          let ?e = "Event.Grant_Endpoint_Cap did grant_cap dst_cap"
          let ?er = "Grant_Endpoint_Cap did grant_cap dst_cap"
          have "(\<Up>t) = exec_event (\<Up>s) ?e"
            using grant_endpoint_cap_ref_lemma exec_eventR_def exec_event_def Grant_Endpoint_Cap.prems  
              by (auto cong del: abstract_state_def)
          then show ?case using eR_def by auto
      next
        case (Remove_Cap_Right did dst_cap right_to_rm)
          let ?e = "Event.Remove_Cap_Right did dst_cap right_to_rm"
          let ?er = "Remove_Cap_Right did dst_cap right_to_rm"
          have "(\<Up>t) = exec_event (\<Up>s) ?e"
            using remove_cap_right_ref_lemma exec_eventR_def exec_event_def Remove_Cap_Right.prems  
              by (auto cong del: abstract_state_def)
          then show ?case using eR_def by auto
      next
        case (Sys_Dispatcher_Properties did p_type p_deadline p_wcet p_period p_release p_weight)
          let ?er = "Sys_Dispatcher_Properties did p_type p_deadline p_wcet p_period p_release p_weight"
          show ?case using eR_def exec_eventR_def Sys_Dispatcher_Properties.prems sys_dispatcher_properties_nchastate_lemma
            by (metis (no_types, lifting)  EventR.simps(233))
      next
        case (Sys_Dispatcher_Setup did p_cptr p_vptr p_dptr p_run)
          let ?er = "Sys_Dispatcher_Setup did p_cptr p_vptr p_dptr p_run"
          show ?case using eR_def exec_eventR_def Sys_Dispatcher_Setup.prems sys_dispatcher_setup_nchastate_lemma
            by (metis (no_types, lifting)  EventR.simps(234))
      next
        case (Dispatcher_Dump_Ptables did)
          let ?er = "Dispatcher_Dump_Ptables did "
          show ?case using eR_def exec_eventR_def Dispatcher_Dump_Ptables.prems dispatcher_dump_ptables_nchastate_lemma
            by (metis (no_types, lifting)  EventR.simps(235))
      next
        case (Capability_Copy did c)
          let ?er = "Capability_Copy did c"
          show ?case using eR_def exec_eventR_def Capability_Copy.prems capability_copy_nchastate_lemma
            by (metis (no_types, lifting)  EventR.simps(236))
      next
        case (Capability_Retype did cap_retype dst_type)
          let ?er = "Capability_Retype did cap_retype dst_type"
          show ?case using eR_def exec_eventR_def Capability_Retype.prems capability_retype_nchastate_lemma
            by (metis (no_types, lifting)  EventR.simps(237))
      next
        case (Capability_Mint did cap_mint param1 param2)
          let ?er = "Capability_Mint did cap_mint param1 param2"
          show ?case using eR_def exec_eventR_def Capability_Mint.prems capability_mint_nchastate_lemma
            by (metis (no_types, lifting)  EventR.simps(238))
      next
        case (Capability_Delete did cap_del)
          let ?er = "Capability_Delete did cap_del"
          show ?case using eR_def exec_eventR_def Capability_Delete.prems capability_delete_nchastate_lemma
            by (metis (no_types, lifting)  EventR.simps(239))
      next
        case (Capability_Get_State did cap_dst)
          let ?er = "Capability_Get_State did cap_dst"
          show ?case using eR_def exec_eventR_def Capability_Get_State.prems capability_get_state_nchastate_lemma
            by (metis (no_types, lifting)  EventR.simps(240))    
    qed
  qed

  lemma reachR_reach1: 
     "\<forall>s as s'. CapFlow.reachable0 (\<Up>s) \<and> 
                 reachable0 s \<and> s' = run s as \<longrightarrow> 
                CapFlow.reachable0 (\<Up>s')"
  proof -
  {
    fix as
    have "\<forall>s s'. CapFlow.reachable0 (\<Up>s) \<and> reachable0 s \<and> s' = run s as 
                        \<longrightarrow> CapFlow.reachable0 (\<Up>s')"
    proof(induct as)
      case Nil show ?case using run_def by fastforce
    next
      case (Cons b bs)
      assume a0: "\<forall>s s'. CapFlow.reachable0 (\<Up>s) \<and> reachable0 s \<and> s' = run s bs 
                        \<longrightarrow> CapFlow.reachable0 (\<Up>s')"
      show ?case 
      proof -
      {
        fix s s'
        assume b0: "CapFlow.reachable0 (\<Up>s) \<and> reachable0 s \<and> s' = run s (b # bs)"
        have b3: "\<forall>s1. s1 = exec_eventR s b \<longrightarrow> CapFlow.reachable0 (\<Up>s1)"
        proof -
        {
          fix s1
          assume c0: "s1 = exec_eventR s b"
          then have "CapFlow.reachable0 (\<Up>s1)"
            using CapFlow.reachableStep b0 refine_exec_event by metis
        }
        then show ?thesis by auto
        qed
        from b0 have "\<exists>s1. s1 = exec_eventR s b \<and> s' = run s1 bs" 
          using run_def by (simp add: relcomp.simps)
        then obtain s1 where b4: "s1 = exec_eventR s b \<and> s' = run s1 bs" by auto
        with b3 have b5: "CapFlow.reachable0 (\<Up>s1)" by simp
        have b6: "reachable0 s1" using reachableStep b0 b4 by blast 
        with b4 b5 a0 have "CapFlow.reachable0 (\<Up>s')" using run_def by auto
      } then show ?thesis by auto
      qed
    qed
  } then show ?thesis by auto
  qed

lemma reachR_reach: "reachable0 s \<Longrightarrow> CapFlow.reachable0 (\<Up>s)" 
  using reachR_reach1 reachable0_def reachable_s0 CapFlow.reachable_s0 s0_ref_lemma
    by (metis  reachable_def)

primrec rmtau :: "'a option list => 'a list"
  where "rmtau [] = []" |
        "rmtau (a#as) = (if a \<noteq> None then
                          the a # rmtau as
                         else rmtau as)"

lemma refine_sound_helper: "\<forall>es st sr. (st = (\<Up>sr)) \<longrightarrow> 
                (\<Up>(BF_CapFlow.run sr es)) = (CapFlow.run st (rmtau (map eR es)))"
  proof -
  {
    fix es
    have "\<forall>st sr. (st = (\<Up>sr)) \<longrightarrow> 
                (\<Up>(BF_CapFlow.run sr es)) = (CapFlow.run st (rmtau (map eR es)))"
    proof(induct es)
      case Nil show ?case
      proof -
      {
        fix st sr
        assume a0: "st = \<Up>sr"
        have a1: "BF_CapFlow.run sr [] = sr"
          using BF_CapFlow.run.run_Nil by simp
        have a2: "CapFlow.run st (rmtau (map eR [])) = st"
          using CapFlow.run.run_Nil by simp
        have a3: "(\<Up>(BF_CapFlow.run sr [])) = (CapFlow.run st (rmtau (map eR [])))"
          using a0 a1 a2 by auto
      }
      then show ?case by auto
      qed
      next
        case (Cons a as)
        assume a0: "\<forall>st sr. (st = (\<Up>sr)) \<longrightarrow> 
                (\<Up>(BF_CapFlow.run sr as)) = (CapFlow.run st (rmtau (map eR as)))"
        show ?case
        proof -
        {
          fix st sr
          assume b0: "st = \<Up>sr"
          have "(\<Up>(BF_CapFlow.run sr (a # as))) = CapFlow.run st (rmtau (map eR (a # as)))"
          proof (cases "eR a = None")
            assume c0: "eR a = None"
            have c1: "rmtau (map eR (a # as)) = rmtau (map eR as)" 
              using rmtau_def c0 by simp
            have c2: "BF_CapFlow.run sr (a # as) = BF_CapFlow.run (exec_eventR sr a) (as)"
              by simp
            have c3: "(\<Up>(exec_eventR sr a)) = \<Up>(sr)"
              by (metis c0 refine_exec_event)
            have c4: "(\<Up>(BF_CapFlow.run (exec_eventR sr a) (as))) = (\<Up>(BF_CapFlow.run sr (as)))"
              using a0 c3 by auto
            have c5: "(\<Up>(BF_CapFlow.run sr (as))) = (CapFlow.run st (rmtau (map eR as)))"
              using a0 b0 by blast
            have c6: "(\<Up>(BF_CapFlow.run sr (a # as))) = CapFlow.run st (rmtau (map eR (a # as)))"
              using c5 c1 c4 by auto
            then show ?thesis by auto
          next
            assume c0: "eR a \<noteq> None"
            have c1: "rmtau (map eR (a # as)) = (the (eR a)) # (rmtau (map eR as))" 
              using rmtau_def c0 by simp
            have c2: "(\<Up>(BF_CapFlow.run sr (as))) = (CapFlow.run st (rmtau (map eR as)))"
              using a0 b0 by blast
            have c3: "BF_CapFlow.run sr (a # as) = BF_CapFlow.run (exec_eventR sr a) (as)"
              by simp
            have c4: "(CapFlow.run st (rmtau (map eR (a # as)))) 
                      = (CapFlow.run st ((the (eR a)) # (rmtau (map eR as))))"
              using c1 by auto
            have c5: "(CapFlow.run st ((the (eR a)) # (rmtau (map eR as)))) = 
                      (CapFlow.run (CapFlow.exec_event st (the (eR a))) (rmtau (map eR as)))"
              by simp
            have c6: "(\<Up>(exec_eventR sr a)) = (CapFlow.exec_event st (the (eR a)))"
              using b0 c0 refine_exec_event by blast
            have c7: "(\<Up>(BF_CapFlow.run (exec_eventR sr a) (as))) = 
                      (CapFlow.run (CapFlow.exec_event st (the (eR a))) (rmtau (map eR as)))"
              using a0 c6 by auto
            have c8: "(\<Up>(BF_CapFlow.run sr (a # as))) = CapFlow.run st (rmtau (map eR (a # as)))"
              using c7 c3 c4 by auto
            then show ?thesis by auto
          qed
        }
        then show ?thesis by auto
      qed
    qed
    }
    then show ?thesis by auto
  qed       

  theorem refine_sound: "(\<Up>(BF_CapFlow.run s0r es)) = (CapFlow.run s0t (rmtau (map eR es)))"
    using refine_sound_helper s0_ref_lemma by fastforce 

subsubsection{* unwinding conditions of refinement*}

  lemma dynamic_weakly_step_consistent_new_evt_ref: 
    "\<forall>e. eR e = None \<and> dynamic_weakly_step_consistent_new_e e \<longrightarrow> dynamic_weakly_step_consistent_e e"
      by (metis dynamic_weakly_step_consistent_e_def dynamic_weakly_step_consistent_new_e_def)

  lemma dynamic_local_respect_new_evt_ref: 
    "\<forall>e. eR e = None \<and> dynamic_local_respect_new_e e \<longrightarrow> dynamic_local_respect_e e"
      by (metis dynamic_local_respect_e_def dynamic_local_respect_new_e_def)

  lemma dynamic_weakly_step_consistent_evt_ref: 
    "\<forall>e. eR e \<noteq> None \<and> CapFlow.dynamic_weakly_step_consistent_e (the (eR e)) 
          \<and> BF_CapFlow.dynamic_weakly_step_consistent_new_e e \<longrightarrow> BF_CapFlow.dynamic_weakly_step_consistent_e e"
      using BF_CapFlow.dynamic_weakly_step_consistent_e_def dynamic_weakly_step_consistent_new_e_def 
      by blast    

  lemma dynamic_local_respect_evt_ref: 
    "\<forall>e. eR e \<noteq> None \<and> CapFlow.dynamic_local_respect_e (the (eR e)) 
          \<and> BF_CapFlow.dynamic_local_respect_new_e e \<longrightarrow> BF_CapFlow.dynamic_local_respect_e e"
      using BF_CapFlow.dynamic_local_respect_e_def dynamic_local_respect_new_e_def by blast   

  lemma abs_sc_new_imp: "\<lbrakk>CapFlow.dynamic_weakly_step_consistent; 
            BF_CapFlow.dynamic_weakly_step_consistent_new\<rbrakk> 
        \<Longrightarrow> BF_CapFlow.dynamic_weakly_step_consistent"
      using BF_CapFlow.dynamic_weakly_step_consistent_all_evt 
        CapFlow.dynamic_weakly_step_consistent_all_evt dynamic_weakly_step_consistent_evt_ref 
        dynamic_weakly_step_consistent_new_all_evt dynamic_weakly_step_consistent_new_evt_ref 
        by blast

  lemma abs_lr_new_imp: "\<lbrakk>CapFlow.dynamic_local_respect; BF_CapFlow.dynamic_local_respect_new\<rbrakk> 
        \<Longrightarrow> BF_CapFlow.dynamic_local_respect"
      using BF_CapFlow.dynamic_local_respect_all_evt CapFlow.dynamic_local_respect_all_evt 
        dynamic_local_respect_evt_ref dynamic_local_respect_new_all_evt 
        dynamic_local_respect_new_evt_ref by blast

  theorem noninfl_refinement: "\<lbrakk>CapFlow.dynamic_local_respect; BF_CapFlow.dynamic_weakly_step_consistent; 
              dynamic_weakly_step_consistent_new; BF_CapFlow.dynamic_local_respect_new\<rbrakk> \<Longrightarrow> noninfluence"
      using BF_CapFlow.uc_eq_noninf BF_CapFlow.weak_with_step_cons abs_lr_new_imp by blast

subsection{* Existing events preserve "dynamic local respect" on new state variables *} 

subsubsection{*proving "client lookup endpoint name"*}

  lemma client_lookup_endpoint_nameR_presrv_lcrsp_new:
      assumes p3:"s' = fst (client_lookup_endpoint_nameR sc s did ename)"
      shows   "s \<sim>. d .\<sim>\<^sub>\<Delta> s'" using p3 by fastforce

  lemma client_lookup_endpoint_nameR_presrv_lcrsp_new_helper: 
    assumes p0: "a = Client_Lookup_Endpoint_Name did ep_name"
    shows "\<forall>d s. reachable0 s \<and> \<not>interferesR (the (domain_of_eventR a)) s d 
                              \<longrightarrow> (s \<sim>. d .\<sim> (exec_eventR s a))"
    proof -
    {
      fix s d
      assume p1: "reachable0 s"
      assume p2: "\<not>interferesR (the (domain_of_eventR a)) s d "
      have a0: "domain_of_eventR a = Some did"
        using p0 domain_of_eventR_def by auto
      have a2: "exec_eventR s a = fst (client_lookup_endpoint_nameR sysconf s did ep_name)"
        using p0 exec_eventR_def by auto
      let ?s'= "fst (client_lookup_endpoint_nameR sysconf s did ep_name)"
      have a4: "\<not>CapFlow.interferes (the (domain_of_eventR a)) (\<Up>s) d"
        using p2 interferesR_def by auto
      let ?a' = "CapFlow.Event.Client_Lookup_Endpoint_Name did ep_name"
      let ?ss' = "CapFlow.exec_event (\<Up>s) ?a'"
      have a5: "CapFlow.reachable0 (\<Up>s)"
        using reachR_reach p1 by auto
      have a6: "the (domain_of_event ?a') = did"
        using domain_of_event_def by auto
      have a7: "\<not>(interferes did (\<Up>s) d)"
        using a4 a0 a6 by auto
      have a8: "(\<Up>s) \<sim> d \<sim> ?ss'"
        using a5 a6 a7 client_lookup_endpoint_name_lcl_resp_e by presburger
      have a9: "?ss' = fst (client_lookup_endpoint_name sysconf (\<Up>s) did ep_name)"
        using CapFlow.exec_event_def by auto
      have a10:  "(s \<sim>. d .\<sim> (exec_eventR s a))"
        by (metis a2 a8 a9 client_lookup_endpoint_nameR_presrv_lcrsp_new client_lookup_endpoint_name_ref_lemma vpeqR_def)
      }
    then show ?thesis by auto
  qed

  lemma client_lookup_endpoint_nameR_presrv_lcrsp_new_e: 
        "dynamic_local_respect_new_e (Client_Lookup_Endpoint_Name did ep_name)"
    by (meson client_lookup_endpoint_nameR_presrv_lcrsp_new_helper dynamic_local_respect_new_e_def)


subsubsection{*proving "send queuing message"*}

  lemma send_queuing_messageR_presrv_lcrsp_new:
      assumes p3:"s' = fst (send_queuing_messageR s did eid m)"
      shows   "s \<sim>. d .\<sim>\<^sub>\<Delta> s'" using p3 by fastforce

  lemma send_queuing_messageR_presrv_lcrsp_new_helper: 
    assumes p0: "a = Send_Queuing_Message did eid m"
    shows "\<forall>d s. reachable0 s \<and> \<not>interferesR (the (domain_of_eventR a)) s d 
                              \<longrightarrow> (s \<sim>. d .\<sim> (exec_eventR s a))"
    proof -
    {
      fix s d
      assume p1: "reachable0 s"
      assume p2: "\<not>interferesR (the (domain_of_eventR a)) s d "
      have a0: "domain_of_eventR a = Some did"
        using p0 domain_of_eventR_def by auto
      have a2: "exec_eventR s a = fst (send_queuing_messageR s did eid m)"
        using p0 exec_eventR_def by auto
      let ?s'= "fst (send_queuing_messageR s did eid m)"
      have a4: "\<not>CapFlow.interferes (the (domain_of_eventR a)) (\<Up>s) d"
        using p2 interferesR_def by auto
      let ?a' = "CapFlow.Event.Send_Queuing_Message did eid m"
      let ?ss' = "CapFlow.exec_event (\<Up>s) ?a'"
      have a5: "CapFlow.reachable0 (\<Up>s)"
        using reachR_reach p1 by auto
      have a6: "the (domain_of_event ?a') = did"
        using domain_of_event_def by auto
      have a7: "\<not>(interferes did (\<Up>s) d)"
        using a4 a0 a6 by auto
      have a8: "(\<Up>s) \<sim> d \<sim> ?ss'"
        using a5 a6 a7 send_queuing_message_lcl_resp_e by presburger
      have a9: "?ss' = fst (send_queuing_message (\<Up>s) did eid m)"
        using CapFlow.exec_event_def by auto
      have a10:  "(s \<sim>. d .\<sim> (exec_eventR s a))"
        by (metis a2 a8 a9 send_queuing_messageR_presrv_lcrsp_new send_queuing_message_ref_lemma vpeqR_def)
      }
    then show ?thesis by auto
  qed

  lemma send_queuing_messageR_presrv_lcrsp_new_e: 
        "dynamic_local_respect_new_e (Send_Queuing_Message did eid m)"
    by (meson send_queuing_messageR_presrv_lcrsp_new_helper dynamic_local_respect_new_e_def)

subsubsection{*proving "receive queuing message"*}

  lemma receive_queuing_messageR_presrv_lcrsp_new:
      assumes p3:"s' = fst (receive_queuing_messageR s did eid)"
      shows   "s \<sim>. d .\<sim>\<^sub>\<Delta> s'" using p3 by fastforce

  lemma receive_queuing_messageR_presrv_lcrsp_new_helper: 
    assumes p0: "a = Receive_Queuing_Message did eid"
    shows "\<forall>d s. reachable0 s \<and> \<not>interferesR (the (domain_of_eventR a)) s d 
                              \<longrightarrow> (s \<sim>. d .\<sim> (exec_eventR s a))"
    proof -
    {
      fix s d
      assume p1: "reachable0 s"
      assume p2: "\<not>interferesR (the (domain_of_eventR a)) s d "
      have a0: "domain_of_eventR a = Some did"
        using p0 domain_of_eventR_def by auto
      have a2: "exec_eventR s a = fst (receive_queuing_messageR s did eid)"
        using p0 exec_eventR_def by auto
      let ?s'= "fst (receive_queuing_messageR s did eid)"
      have a4: "\<not>CapFlow.interferes (the (domain_of_eventR a)) (\<Up>s) d"
        using p2 interferesR_def by auto
      let ?a' = "CapFlow.Event.Receive_Queuing_Message did eid"
      let ?ss' = "CapFlow.exec_event (\<Up>s) ?a'"
      have a5: "CapFlow.reachable0 (\<Up>s)"
        using reachR_reach p1 by auto
      have a6: "the (domain_of_event ?a') = did"
        using domain_of_event_def by auto
      have a7: "\<not>(interferes did (\<Up>s) d)"
        using a4 a0 a6 by auto
      have a8: "(\<Up>s) \<sim> d \<sim> ?ss'"
        using a5 a6 a7 receive_queuing_message_lcl_resp_e by presburger
      have a9: "?ss' = fst (receive_queuing_message (\<Up>s) did eid)"
        using CapFlow.exec_event_def by auto
      have a10:  "(s \<sim>. d .\<sim> (exec_eventR s a))"
        by (metis a2 a8 a9 receive_queuing_messageR_presrv_lcrsp_new receive_queuing_message_ref_lemma vpeqR_def)
      }
    then show ?thesis by auto
  qed

  lemma receive_queuing_messageR_presrv_lcrsp_new_e: 
        "dynamic_local_respect_new_e (Receive_Queuing_Message   did eid)"
    by (meson receive_queuing_messageR_presrv_lcrsp_new_helper dynamic_local_respect_new_e_def)

subsubsection{*proving "get my endpoints set"*}

  lemma get_my_endpoints_setR_presrv_lcrsp_new:
      assumes p3:"s' = fst (get_my_endpoints_setR s did)"
      shows   "s \<sim>. d .\<sim>\<^sub>\<Delta> s'" using p3 by fastforce

  lemma get_my_endpoints_setR_presrv_lcrsp_new_helper: 
    assumes p0: "a = Get_My_Endpoints_Set did"
    shows "\<forall>d s. reachable0 s \<and> \<not>interferesR (the (domain_of_eventR a)) s d 
                              \<longrightarrow> (s \<sim>. d .\<sim> (exec_eventR s a))"
    proof -
    {
      fix s d
      assume p1: "reachable0 s"
      assume p2: "\<not>interferesR (the (domain_of_eventR a)) s d "
      have a0: "domain_of_eventR a = Some did"
        using p0 domain_of_eventR_def by auto
      have a2: "exec_eventR s a = fst (get_my_endpoints_setR s did)"
        using p0 exec_eventR_def by auto
      let ?s'= "fst (get_my_endpoints_setR s did)"
      have a4: "\<not>CapFlow.interferes (the (domain_of_eventR a)) (\<Up>s) d"
        using p2 interferesR_def by auto
      let ?a' = "CapFlow.Event.Get_My_Endpoints_Set did"
      let ?ss' = "CapFlow.exec_event (\<Up>s) ?a'"
      have a5: "CapFlow.reachable0 (\<Up>s)"
        using reachR_reach p1 by auto
      have a6: "the (domain_of_event ?a') = did"
        using domain_of_event_def by auto
      have a7: "\<not>(interferes did (\<Up>s) d)"
        using a4 a0 a6 by auto
      have a8: "(\<Up>s) \<sim> d \<sim> ?ss'"
        using a5 a6 a7 get_my_endpoints_set_lcl_resp_e by presburger
      have a9: "?ss' = fst (get_my_endpoints_set (\<Up>s) did)"
        using CapFlow.exec_event_def by auto
      have a10:  "(s \<sim>. d .\<sim> (exec_eventR s a))"
        by (metis a2 a8 a9 get_my_endpoints_setR_presrv_lcrsp_new get_my_endpoints_set_ref_lemma vpeqR_def)
      }
    then show ?thesis by auto
  qed

  lemma get_my_endpoints_setR_presrv_lcrsp_new_e: 
        "dynamic_local_respect_new_e (Get_My_Endpoints_Set did)"
    by (meson get_my_endpoints_setR_presrv_lcrsp_new_helper dynamic_local_respect_new_e_def)

subsubsection{*proving "get cap set"*}

  lemma get_capsR_presrv_lcrsp_new:
      assumes p3:"s' = fst (get_capsR s did)"
      shows   "s \<sim>. d .\<sim>\<^sub>\<Delta> s'" using p3 by fastforce

  lemma get_capsR_presrv_lcrsp_new_helper: 
    assumes p0: "a = Get_Caps did"
    shows "\<forall>d s. reachable0 s \<and> \<not>interferesR (the (domain_of_eventR a)) s d 
                              \<longrightarrow> (s \<sim>. d .\<sim> (exec_eventR s a))"
    proof -
    {
      fix s d
      assume p1: "reachable0 s"
      assume p2: "\<not>interferesR (the (domain_of_eventR a)) s d "
      have a0: "domain_of_eventR a = Some did"
        using p0 domain_of_eventR_def by auto
      have a2: "exec_eventR s a = fst (get_capsR s did)"
        using p0 exec_eventR_def by auto
      let ?s'= "fst (get_capsR s did)"
      have a4: "\<not>CapFlow.interferes (the (domain_of_eventR a)) (\<Up>s) d"
        using p2 interferesR_def by auto
      let ?a' = "CapFlow.Event.Get_Caps did"
      let ?ss' = "CapFlow.exec_event (\<Up>s) ?a'"
      have a5: "CapFlow.reachable0 (\<Up>s)"
        using reachR_reach p1 by auto
      have a6: "the (domain_of_event ?a') = did"
        using domain_of_event_def by auto
      have a7: "\<not>(interferes did (\<Up>s) d)"
        using a4 a0 a6 by auto
      have a8: "(\<Up>s) \<sim> d \<sim> ?ss'"
        using a5 a6 a7 get_caps_lcl_resp_e by presburger
      have a9: "?ss' = fst (get_caps (\<Up>s) did)"
        using CapFlow.exec_event_def by auto
      have a10:  "(s \<sim>. d .\<sim> (exec_eventR s a))"
        by (metis a2 a8 a9 get_capsR_presrv_lcrsp_new get_caps_ref_lemma vpeqR_def)
      }
    then show ?thesis by auto
  qed

  lemma get_capsR_presrv_lcrsp_new_e: 
        "dynamic_local_respect_new_e (Get_Caps did)"
    by (meson get_capsR_presrv_lcrsp_new_helper dynamic_local_respect_new_e_def)

subsubsection{*proving "grant endpoint cap"*}

  lemma grant_endpoint_capR_presrv_lcrsp_new:
      assumes p3:"s' = fst (grant_endpoint_capR s did grant_cap dst_cap)"
      shows   "s \<sim>. d .\<sim>\<^sub>\<Delta> s'" using p3 by fastforce

  lemma grant_endpoint_capR_presrv_lcrsp_new_helper: 
    assumes p0: "a = Grant_Endpoint_Cap did grant_cap dst_cap"
    shows "\<forall>d s. reachable0 s \<and> \<not>interferesR (the (domain_of_eventR a)) s d 
                              \<longrightarrow> (s \<sim>. d .\<sim> (exec_eventR s a))"
    proof -
    {
      fix s d
      assume p1: "reachable0 s"
      assume p2: "\<not>interferesR (the (domain_of_eventR a)) s d "
      have a0: "domain_of_eventR a = Some did"
        using p0 domain_of_eventR_def by auto
      have a2: "exec_eventR s a = fst (grant_endpoint_capR s did grant_cap dst_cap)"
        using p0 exec_eventR_def by auto
      let ?s'= "fst (grant_endpoint_capR s did grant_cap dst_cap)"
      have a4: "\<not>CapFlow.interferes (the (domain_of_eventR a)) (\<Up>s) d"
        using p2 interferesR_def by auto
      let ?a' = "CapFlow.Event.Grant_Endpoint_Cap did grant_cap dst_cap"
      let ?ss' = "CapFlow.exec_event (\<Up>s) ?a'"
      have a5: "CapFlow.reachable0 (\<Up>s)"
        using reachR_reach p1 by auto
      have a6: "the (domain_of_event ?a') = did"
        using domain_of_event_def by auto
      have a7: "\<not>(interferes did (\<Up>s) d)"
        using a4 a0 a6 by auto
      have a8: "(\<Up>s) \<sim> d \<sim> ?ss'"
        using a5 a6 a7 grant_endpoint_cap_lcl_resp_e by presburger
      have a9: "?ss' = fst (grant_endpoint_cap (\<Up>s) did grant_cap dst_cap)"
        using CapFlow.exec_event_def by auto
      have a10:  "(s \<sim>. d .\<sim> (exec_eventR s a))"
        by (metis a2 a8 a9 grant_endpoint_capR_presrv_lcrsp_new grant_endpoint_cap_ref_lemma vpeqR_def)
      }
    then show ?thesis by auto
  qed

  lemma grant_endpoint_capR_presrv_lcrsp_new_e: 
        "dynamic_local_respect_new_e (Grant_Endpoint_Cap did grant_cap dst_cap)"
    by (meson grant_endpoint_capR_presrv_lcrsp_new_helper dynamic_local_respect_new_e_def)

subsubsection{*proving "remove cap right"*}

  lemma remove_cap_rightR_presrv_lcrsp_new:
      assumes p3:"s' = fst (remove_cap_rightR s did dst_cap right_to_rm)"
      shows   "s \<sim>. d .\<sim>\<^sub>\<Delta> s'" using p3 by fastforce

  lemma remove_cap_rightR_presrv_lcrsp_new_helper: 
    assumes p0: "a = Remove_Cap_Right did dst_cap right_to_rm "
    shows "\<forall>d s. reachable0 s \<and> \<not>interferesR (the (domain_of_eventR a)) s d 
                              \<longrightarrow> (s \<sim>. d .\<sim> (exec_eventR s a))"
    proof -
    {
      fix s d
      assume p1: "reachable0 s"
      assume p2: "\<not>interferesR (the (domain_of_eventR a)) s d "
      have a0: "domain_of_eventR a = Some did"
        using p0 domain_of_eventR_def by auto
      have a2: "exec_eventR s a = fst (remove_cap_rightR s did dst_cap right_to_rm)"
        using p0 exec_eventR_def by auto
      let ?s'= "fst (remove_cap_rightR s did dst_cap right_to_rm)"
      have a4: "\<not>CapFlow.interferes (the (domain_of_eventR a)) (\<Up>s) d"
        using p2 interferesR_def by auto
      let ?a' = "CapFlow.Event.Remove_Cap_Right did dst_cap right_to_rm "
      let ?ss' = "CapFlow.exec_event (\<Up>s) ?a'"
      have a5: "CapFlow.reachable0 (\<Up>s)"
        using reachR_reach p1 by auto
      have a6: "the (domain_of_event ?a') = did"
        using domain_of_event_def by auto
      have a7: "\<not>(interferes did (\<Up>s) d)"
        using a4 a0 a6 by auto
      have a8: "(\<Up>s) \<sim> d \<sim> ?ss'"
        using a5 a6 a7 remove_cap_right_lcl_resp_e by presburger
      have a9: "?ss' = fst (remove_cap_right (\<Up>s) did dst_cap right_to_rm)"
        using CapFlow.exec_event_def by auto
      have a10:  "(s \<sim>. d .\<sim> (exec_eventR s a))"
        by (metis a2 a8 a9 remove_cap_rightR_presrv_lcrsp_new remove_cap_right_ref_lemma vpeqR_def)
      }
    then show ?thesis by auto
  qed    

  lemma remove_cap_rightR_presrv_lcrsp_new_e: 
        "dynamic_local_respect_new_e (Remove_Cap_Right did dst_cap right_to_rm )"
    by (meson remove_cap_rightR_presrv_lcrsp_new_helper dynamic_local_respect_new_e_def)

subsection{* New events preserve "dynamic local respect" on new state variables *} 

subsubsection{*proving "system dispatcher set properties"*}

lemma sys_dispatcher_properties_vpeq_dispatcher:
    assumes 
           p1: "did \<noteq> d"
      and  p2: "s' = fst (sys_dispatcher_properties s did p_type p_deadline p_wcet p_period p_release p_weight)"
    shows "s \<sim>. d .\<sim>\<^sub>\<Delta> s'" 
    using  p1 p2 sys_dispatcher_properties_def  by auto   

lemma sys_dispatcher_properties_presrv_lcrsp_new_helper: 
    assumes p0: "a = Sys_Dispatcher_Properties did p_type p_deadline p_wcet p_period p_release p_weight"
    shows "\<forall>d s. reachable0 s \<and> \<not>interferesR (the (domain_of_eventR a)) s d 
                              \<longrightarrow> (s \<sim>. d .\<sim> (exec_eventR s a))"
    proof -
    {
      fix s d
      assume p1: "reachable0 s"
      assume p2: "\<not>interferesR (the (domain_of_eventR a)) s d "
      have a0: "the (domain_of_eventR a) =  did"
        using p0 domain_of_eventR_def by auto 
      have a1: "did \<noteq> d"
        using a0 p2 interferesR_def interferes_def by auto
      let ?s' = "fst (sys_dispatcher_properties s did p_type p_deadline p_wcet p_period p_release p_weight)"
      have a2: "(\<Up>s) \<sim> d \<sim> (\<Up>?s')"
        using sys_dispatcher_properties_nchastate_lemma by auto
      have a3: "s \<sim>. d .\<sim>\<^sub>\<Delta> ?s'"
        using a1 sys_dispatcher_properties_vpeq_dispatcher by blast
      have a4: "?s' = exec_eventR s a"
        using exec_eventR_def p0 by auto
      have a5: "(s \<sim>. d .\<sim> (exec_eventR s a))"
        using a4 a2 a3 vpeqR_def by auto
      }
    then show ?thesis by auto
  qed 

  lemma sys_dispatcher_properties_presrv_lcrsp_new_e: 
        "dynamic_local_respect_new_e (Sys_Dispatcher_Properties did p_type p_deadline p_wcet 
            p_period p_release p_weight)"
    by (meson sys_dispatcher_properties_presrv_lcrsp_new_helper dynamic_local_respect_new_e_def)

subsubsection{*proving "system dispatcher setup"*}

lemma sys_dispatcher_setup_vpeq_dispatcher:
    assumes 
           p1: "did \<noteq> d"
      and  p2: "s' = fst (sys_dispatcher_setup s did p_cptr p_vptr p_dptr p_run)"
    shows "s \<sim>. d .\<sim>\<^sub>\<Delta> s'"
    proof (cases "p_run = True")
      assume a0: "p_run = True"
      have "s \<sim>. d .\<sim>\<^sub>\<Delta> s'"
        using  p1 p2 sys_dispatcher_setup_def a0 by auto
      then show ?thesis by auto
    next
      assume a1: "p_run \<noteq> True"
      have "s \<sim>. d .\<sim>\<^sub>\<Delta> s'"
        using  p1 p2 sys_dispatcher_setup_def a1 by auto
      then show ?thesis by auto
    qed

lemma sys_dispatcher_setup_presrv_lcrsp_new_helper: 
    assumes p0: "a = Sys_Dispatcher_Setup did p_cptr p_vptr p_dptr p_run"
    shows "\<forall>d s. reachable0 s \<and> \<not>interferesR (the (domain_of_eventR a)) s d 
                              \<longrightarrow> (s \<sim>. d .\<sim> (exec_eventR s a))"
    proof -
    {
      fix s d
      assume p1: "reachable0 s"
      assume p2: "\<not>interferesR (the (domain_of_eventR a)) s d "
      have a0: "the (domain_of_eventR a) =  did"
        using p0 domain_of_eventR_def by auto 
      have a1: "did \<noteq> d"
        using a0 p2 interferesR_def interferes_def by auto
      let ?s' = "fst (sys_dispatcher_setup s did p_cptr p_vptr p_dptr p_run)"
      have a2: "(\<Up>s) \<sim> d \<sim> (\<Up>?s')"
        using sys_dispatcher_setup_nchastate_lemma by auto
      have a3: "s \<sim>. d .\<sim>\<^sub>\<Delta> ?s'"
        using a1 sys_dispatcher_setup_vpeq_dispatcher by blast
      have a4: "?s' = exec_eventR s a"
        using exec_eventR_def p0 by auto
      have a5: "(s \<sim>. d .\<sim> (exec_eventR s a))"
        using a4 a2 a3 vpeqR_def by auto
      }
    then show ?thesis by auto
  qed 

  lemma sys_dispatcher_setup_presrv_lcrsp_new_e: 
        "dynamic_local_respect_new_e (Sys_Dispatcher_Setup did p_cptr p_vptr p_dptr p_run)"
    by (meson sys_dispatcher_setup_presrv_lcrsp_new_helper dynamic_local_respect_new_e_def)

subsubsection{*proving "dispatcher dump ptables"*}

lemma dispatcher_dump_ptables_vpeq_dispatcher:
    assumes 
           p1: "did \<noteq> d"
      and  p2: "s' = fst (dispatcher_dump_ptables s did)"
    shows "s \<sim>. d .\<sim>\<^sub>\<Delta> s'" 
    using  p1 p2 dispatcher_dump_ptables_def  by auto   

lemma dispatcher_dump_ptables_presrv_lcrsp_new_helper: 
    assumes p0: "a = Dispatcher_Dump_Ptables did "
    shows "\<forall>d s. reachable0 s \<and> \<not>interferesR (the (domain_of_eventR a)) s d 
                              \<longrightarrow> (s \<sim>. d .\<sim> (exec_eventR s a))"
    proof -
    {
      fix s d
      assume p1: "reachable0 s"
      assume p2: "\<not>interferesR (the (domain_of_eventR a)) s d "
      have a0: "the (domain_of_eventR a) =  did"
        using p0 domain_of_eventR_def by auto 
      have a1: "did \<noteq> d"
        using a0 p2 interferesR_def interferes_def by auto
      let ?s' = "fst (dispatcher_dump_ptables s did)"
      have a2: "(\<Up>s) \<sim> d \<sim> (\<Up>?s')"
        using dispatcher_dump_ptables_nchastate_lemma by auto
      have a3: "s \<sim>. d .\<sim>\<^sub>\<Delta> ?s'"
        using a1 dispatcher_dump_ptables_vpeq_dispatcher by blast
      have a4: "?s' = exec_eventR s a"
        using exec_eventR_def p0 by auto
      have a5: "(s \<sim>. d .\<sim> (exec_eventR s a))"
        using a4 a2 a3 vpeqR_def by auto
      }
    then show ?thesis by auto
  qed 

  lemma dispatcher_dump_ptables_presrv_lcrsp_new_e: 
        "dynamic_local_respect_new_e (Dispatcher_Dump_Ptables did )"
    by (meson dispatcher_dump_ptables_presrv_lcrsp_new_helper dynamic_local_respect_new_e_def)

subsubsection{*proving "capability copy"*}

lemma capability_copy_vpeq_dispatcher:
    assumes 
           p1: "did \<noteq> d"
      and  p2: "s' = fst (capability_copy s did c)"
    shows "s \<sim>. d .\<sim>\<^sub>\<Delta> s'" 
    using  p1 p2 capability_copy_def  by auto   

lemma capability_copy_presrv_lcrsp_new_helper: 
    assumes p0: "a = Capability_Copy did c"
    shows "\<forall>d s. reachable0 s \<and> \<not>interferesR (the (domain_of_eventR a)) s d 
                              \<longrightarrow> (s \<sim>. d .\<sim> (exec_eventR s a))"
    proof -
    {
      fix s d
      assume p1: "reachable0 s"
      assume p2: "\<not>interferesR (the (domain_of_eventR a)) s d "
      have a0: "the (domain_of_eventR a) =  did"
        using p0 domain_of_eventR_def by auto 
      have a1: "did \<noteq> d"
        using a0 p2 interferesR_def interferes_def by auto
      let ?s' = "fst (capability_copy s did c)"
      have a2: "(\<Up>s) \<sim> d \<sim> (\<Up>?s')"
        using capability_copy_nchastate_lemma by auto
      have a3: "s \<sim>. d .\<sim>\<^sub>\<Delta> ?s'"
        using a1 capability_copy_vpeq_dispatcher by blast
      have a4: "?s' = exec_eventR s a"
        using exec_eventR_def p0 by auto
      have a5: "(s \<sim>. d .\<sim> (exec_eventR s a))"
        using a4 a2 a3 vpeqR_def by auto
      }
    then show ?thesis by auto
  qed 

  lemma capability_copy_presrv_lcrsp_new_e: 
        "dynamic_local_respect_new_e (Capability_Copy did c)"
    by (meson capability_copy_presrv_lcrsp_new_helper dynamic_local_respect_new_e_def)

subsubsection{*proving "capability retype"*}

lemma capability_retype_vpeq_dispatcher:
    assumes 
           p1: "did \<noteq> d"
      and  p2: "s' = fst (capability_retype s did cap_retype dst_type)"
    shows "s \<sim>. d .\<sim>\<^sub>\<Delta> s'" 
    using  p1 p2 capability_retype_def  by auto   

lemma capability_retype_presrv_lcrsp_new_helper: 
    assumes p0: "a = Capability_Retype did cap_retype dst_type"
    shows "\<forall>d s. reachable0 s \<and> \<not>interferesR (the (domain_of_eventR a)) s d 
                              \<longrightarrow> (s \<sim>. d .\<sim> (exec_eventR s a))"
    proof -
    {
      fix s d
      assume p1: "reachable0 s"
      assume p2: "\<not>interferesR (the (domain_of_eventR a)) s d "
      have a0: "the (domain_of_eventR a) =  did"
        using p0 domain_of_eventR_def by auto 
      have a1: "did \<noteq> d"
        using a0 p2 interferesR_def interferes_def by auto
      let ?s' = "fst (capability_retype s did cap_retype dst_type)"
      have a2: "(\<Up>s) \<sim> d \<sim> (\<Up>?s')"
        using capability_retype_nchastate_lemma by auto
      have a3: "s \<sim>. d .\<sim>\<^sub>\<Delta> ?s'"
        using a1 capability_retype_vpeq_dispatcher by blast
      have a4: "?s' = exec_eventR s a"
        using exec_eventR_def p0 by auto
      have a5: "(s \<sim>. d .\<sim> (exec_eventR s a))"
        using a4 a2 a3 vpeqR_def by auto
      }
    then show ?thesis by auto
  qed 

  lemma capability_retype_presrv_lcrsp_new_e: 
        "dynamic_local_respect_new_e (Capability_Retype did cap_retype dst_type)"
    by (meson capability_retype_presrv_lcrsp_new_helper dynamic_local_respect_new_e_def)

subsubsection{*proving "capability mint"*}

lemma capability_mint_vpeq_dispatcher:
    assumes 
           p1: "did \<noteq> d"
      and  p2: "s' = fst (capability_mint s did cap_mint param1 param2)"
    shows "s \<sim>. d .\<sim>\<^sub>\<Delta> s'"
    proof (cases "type cap_mint = ObjType_EndPoint")
      assume a0: "type cap_mint = ObjType_EndPoint"
      have "s \<sim>. d .\<sim>\<^sub>\<Delta> s'"
        using  p1 p2 capability_mint_def a0 by auto
      then show ?thesis by auto
    next
      assume a0: "type cap_mint \<noteq> ObjType_EndPoint"
      have "s \<sim>. d .\<sim>\<^sub>\<Delta> s'"
        using  p1 p2 capability_mint_def a0 by auto
      then show ?thesis by auto
    qed

lemma capability_mint_presrv_lcrsp_new_helper: 
    assumes p0: "a = Capability_Mint did cap_mint param1 param2"
    shows "\<forall>d s. reachable0 s \<and> \<not>interferesR (the (domain_of_eventR a)) s d 
                              \<longrightarrow> (s \<sim>. d .\<sim> (exec_eventR s a))"
    proof -
    {
      fix s d
      assume p1: "reachable0 s"
      assume p2: "\<not>interferesR (the (domain_of_eventR a)) s d "
      have a0: "the (domain_of_eventR a) =  did"
        using p0 domain_of_eventR_def by auto 
      have a1: "did \<noteq> d"
        using a0 p2 interferesR_def interferes_def by auto
      let ?s' = "fst (capability_mint s did cap_mint param1 param2)"
      have a2: "(\<Up>s) \<sim> d \<sim> (\<Up>?s')"
        using capability_mint_nchastate_lemma by auto
      have a3: "s \<sim>. d .\<sim>\<^sub>\<Delta> ?s'"
        using a1 capability_mint_vpeq_dispatcher by blast
      have a4: "?s' = exec_eventR s a"
        using exec_eventR_def p0 by auto
      have a5: "(s \<sim>. d .\<sim> (exec_eventR s a))"
        using a4 a2 a3 vpeqR_def by auto
      }
    then show ?thesis by auto
  qed 

  lemma capability_mint_presrv_lcrsp_new_e: 
        "dynamic_local_respect_new_e (Capability_Mint did cap_mint param1 param2)"
    by (meson capability_mint_presrv_lcrsp_new_helper dynamic_local_respect_new_e_def)

subsubsection{*proving "capability delete"*}

lemma capability_delete_vpeq_dispatcher:
    assumes 
           p1: "did \<noteq> d"
      and  p2: "s' = fst (capability_delete s did cap_del)"
    shows "s \<sim>. d .\<sim>\<^sub>\<Delta> s'" 
    using  p1 p2 capability_delete_def  by auto   

lemma capability_delete_presrv_lcrsp_new_helper: 
    assumes p0: "a = Capability_Delete did cap_del"
    shows "\<forall>d s. reachable0 s \<and> \<not>interferesR (the (domain_of_eventR a)) s d 
                              \<longrightarrow> (s \<sim>. d .\<sim> (exec_eventR s a))"
    proof -
    {
      fix s d
      assume p1: "reachable0 s"
      assume p2: "\<not>interferesR (the (domain_of_eventR a)) s d "
      have a0: "the (domain_of_eventR a) =  did"
        using p0 domain_of_eventR_def by auto 
      have a1: "did \<noteq> d"
        using a0 p2 interferesR_def interferes_def by auto
      let ?s' = "fst (capability_delete s did cap_del)"
      have a2: "(\<Up>s) \<sim> d \<sim> (\<Up>?s')"
        using capability_delete_nchastate_lemma by auto
      have a3: "s \<sim>. d .\<sim>\<^sub>\<Delta> ?s'"
        using a1 capability_delete_vpeq_dispatcher by blast
      have a4: "?s' = exec_eventR s a"
        using exec_eventR_def p0 by auto
      have a5: "(s \<sim>. d .\<sim> (exec_eventR s a))"
        using a4 a2 a3 vpeqR_def by auto
      }
    then show ?thesis by auto
  qed 

  lemma capability_delete_presrv_lcrsp_new_e: 
        "dynamic_local_respect_new_e (Capability_Delete did cap_del)"
    by (meson capability_delete_presrv_lcrsp_new_helper dynamic_local_respect_new_e_def)

subsubsection{*proving "dispatcher dump ptables"*}

lemma capability_get_state_vpeq_dispatcher:
    assumes 
           p1: "did \<noteq> d"
      and  p2: "s' = fst (capability_get_state s did cap_dst)"
    shows "s \<sim>. d .\<sim>\<^sub>\<Delta> s'" 
    using  p1 p2 capability_get_state_def  by auto   

lemma capability_get_state_presrv_lcrsp_new_helper: 
    assumes p0: "a = Capability_Get_State did cap_dst"
    shows "\<forall>d s. reachable0 s \<and> \<not>interferesR (the (domain_of_eventR a)) s d 
                              \<longrightarrow> (s \<sim>. d .\<sim> (exec_eventR s a))"
    proof -
    {
      fix s d
      assume p1: "reachable0 s"
      assume p2: "\<not>interferesR (the (domain_of_eventR a)) s d "
      have a0: "the (domain_of_eventR a) =  did"
        using p0 domain_of_eventR_def by auto 
      have a1: "did \<noteq> d"
        using a0 p2 interferesR_def interferes_def by auto
      let ?s' = "fst (capability_get_state s did cap_dst)"
      have a2: "(\<Up>s) \<sim> d \<sim> (\<Up>?s')"
        using capability_get_state_nchastate_lemma by auto
      have a3: "s \<sim>. d .\<sim>\<^sub>\<Delta> ?s'"
        using a1 capability_get_state_vpeq_dispatcher by blast
      have a4: "?s' = exec_eventR s a"
        using exec_eventR_def p0 by auto
      have a5: "(s \<sim>. d .\<sim> (exec_eventR s a))"
        using a4 a2 a3 vpeqR_def by auto
      }
    then show ?thesis by auto
  qed 

  lemma capability_get_state_presrv_lcrsp_new_e: 
        "dynamic_local_respect_new_e (Capability_Get_State did cap_dst)"
    by (meson capability_get_state_presrv_lcrsp_new_helper dynamic_local_respect_new_e_def)

subsection{* Proving the "dynamic local respect" property on new variables *}

  theorem dynamic_local_respect_new:dynamic_local_respect_new
  proof -
      { 
        fix e
        have "dynamic_local_respect_new_e e"
          apply(induct e)
          using client_lookup_endpoint_nameR_presrv_lcrsp_new_e
                send_queuing_messageR_presrv_lcrsp_new_e
                receive_queuing_messageR_presrv_lcrsp_new_e
                get_my_endpoints_setR_presrv_lcrsp_new_e
                get_capsR_presrv_lcrsp_new_e
                grant_endpoint_capR_presrv_lcrsp_new_e
                remove_cap_rightR_presrv_lcrsp_new_e
                sys_dispatcher_properties_presrv_lcrsp_new_e
                sys_dispatcher_setup_presrv_lcrsp_new_e
                dispatcher_dump_ptables_presrv_lcrsp_new_e
                capability_copy_presrv_lcrsp_new_e
                capability_retype_presrv_lcrsp_new_e
                capability_mint_presrv_lcrsp_new_e
                capability_delete_presrv_lcrsp_new_e                  
                capability_get_state_presrv_lcrsp_new_e
           apply simp
           apply (simp add: send_queuing_messageR_presrv_lcrsp_new_e)
           apply (simp add: receive_queuing_messageR_presrv_lcrsp_new_e)
           apply (simp add: get_my_endpoints_setR_presrv_lcrsp_new_e)
           apply (simp add: get_capsR_presrv_lcrsp_new_e)
           apply (simp add: grant_endpoint_capR_presrv_lcrsp_new_e)
           apply (simp add: remove_cap_rightR_presrv_lcrsp_new_e)
           apply (simp add: sys_dispatcher_properties_presrv_lcrsp_new_e)
           apply (simp add: sys_dispatcher_setup_presrv_lcrsp_new_e)
           apply (simp add: dispatcher_dump_ptables_presrv_lcrsp_new_e)
           apply (simp add: capability_copy_presrv_lcrsp_new_e)
           apply (simp add: capability_retype_presrv_lcrsp_new_e)
           apply (simp add: capability_mint_presrv_lcrsp_new_e)
           apply (simp add: capability_delete_presrv_lcrsp_new_e)
           by (simp add: capability_get_state_presrv_lcrsp_new_e)
        }
      then show ?thesis using dynamic_local_respect_new_all_evt by simp
    qed    


subsection{* Existing events preserve "dynamic step consistent" on new state variables *} 

subsubsection{*proving "client lookup endpoint name"*}

  lemma client_lookup_endpoint_nameR_presrv_wk_stp_cons_new:
      assumes 
              p1:"s \<sim>. d .\<sim> t"
        and   p2:"s' = fst (client_lookup_endpoint_nameR sysconf s did ename)"
        and   p3:"t' = fst (client_lookup_endpoint_nameR sysconf t did ename)"
      shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'" 
    using p1 p2 p3 by fastforce

  lemma client_lookup_endpoint_nameR_presrv_wk_stp_cons_new_helper: 
    assumes p0: "a = Client_Lookup_Endpoint_Name did ep_name"
    shows "\<forall>d s t. reachable0 s \<and> reachable0 t \<and> (s \<sim>. d .\<sim> t) \<and>
             interferesR (the (domain_of_eventR a)) s d \<and> (s \<sim>. (the (domain_of_eventR a)) .\<sim> t)
             \<longrightarrow> ((exec_eventR s a) \<sim>. d .\<sim> (exec_eventR t a))"
    proof -
    {
      fix d s t
      assume p1: "reachable0 s"
      assume p2: "reachable0 t"
      assume p3: "s \<sim>. d .\<sim> t"
      assume p4: "interferesR (the (domain_of_eventR a)) s d "
      assume p5: "(s \<sim>. (the (domain_of_eventR a)) .\<sim> t)"
      have a0: "domain_of_eventR a = Some did"
        using p0 domain_of_eventR_def by auto
      have a1: "exec_eventR s a = fst (client_lookup_endpoint_nameR sysconf s did ep_name)"
        using p0 exec_eventR_def by auto
      have a2: "exec_eventR t a = fst (client_lookup_endpoint_nameR sysconf t did ep_name)"
        using p0 exec_eventR_def by auto
      let ?s'= "fst (client_lookup_endpoint_nameR sysconf s did ep_name)"
      let ?t'= "fst (client_lookup_endpoint_nameR sysconf t did ep_name)"
      have a3: "CapFlow.interferes (the (domain_of_eventR a)) (\<Up>s) d"
        using p4 interferesR_def by auto
      let ?a' = "CapFlow.Event.Client_Lookup_Endpoint_Name did ep_name"
      let ?ss' = "CapFlow.exec_event (\<Up>s) ?a'"
      let ?tt' = "CapFlow.exec_event (\<Up>t) ?a'"
      have a4: "CapFlow.reachable0 (\<Up>s)"
        using reachR_reach p1 by auto
      have a5: "CapFlow.reachable0 (\<Up>t)"
        using reachR_reach p2 by auto
      have a6: "the (domain_of_event ?a') = did"
        using domain_of_event_def by auto
      have a7: "(interferes did (\<Up>s) d)"
        using a3 a0 a6 by auto
      have a8: "(\<Up>s) \<sim> d \<sim> (\<Up>t)"
        using p3 vpeqR_def by blast
      have a9: "((\<Up>s) \<sim> (the (domain_of_eventR a)) \<sim> (\<Up>t))"
        using p5 vpeqR_def by blast
      have a10: "(?ss' \<sim> d \<sim> ?tt')"
        by (metis a0 a4 a5 a6 a7 a8 a9 client_lookup_endpoint_name_wsc_e option.sel)
      have a11: "?ss' = fst (client_lookup_endpoint_name sysconf (\<Up>s) did ep_name)"
        using CapFlow.exec_event_def by auto
      have a12: "?tt' = fst (client_lookup_endpoint_name sysconf (\<Up>t) did ep_name)"
        using CapFlow.exec_event_def by auto
      have a13: "?ss' = \<Up>((exec_eventR s a))"
        using a1 a11 by auto
      have a14: "?tt' = \<Up>((exec_eventR t a))"
        using a2 a12 by auto
      have a15: "((\<Up>(exec_eventR s a)) \<sim> d \<sim> (\<Up>(exec_eventR t a)))"
        using a13 a14 a10 by auto
      have a16: "((exec_eventR s a) \<sim>. d .\<sim>\<^sub>\<Delta> (exec_eventR t a))"
        using a1 a2 client_lookup_endpoint_nameR_presrv_wk_stp_cons_new p3 by blast
      have a17: "((exec_eventR s a) \<sim>. d .\<sim> (exec_eventR t a))"
        using a15 a16 vpeqR_def by auto
      }
    then show ?thesis by blast
  qed

  lemma client_lookup_endpoint_nameR_presrv_wk_stp_cons_new_e: 
        "dynamic_weakly_step_consistent_new_e (Client_Lookup_Endpoint_Name did ep_name)"
    by (meson client_lookup_endpoint_nameR_presrv_wk_stp_cons_new_helper dynamic_weakly_step_consistent_new_e_def)


subsubsection{*proving "send queuing message"*}

  lemma send_queuing_messageR_presrv_wk_stp_cons_new:
      assumes 
              p1:"s \<sim>. d .\<sim> t"
        and   p2:"s' = fst (send_queuing_messageR s did eid m)"
        and   p3:"t' = fst (send_queuing_messageR t did eid m)"
      shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'" 
    using p1 p2 p3 by fastforce

  lemma send_queuing_messageR_presrv_wk_stp_cons_new_helper: 
    assumes p0: "a = Send_Queuing_Message did eid m"
    shows "\<forall>d s t. reachable0 s \<and> reachable0 t \<and> (s \<sim>. d .\<sim> t) \<and>
             interferesR (the (domain_of_eventR a)) s d \<and> (s \<sim>. (the (domain_of_eventR a)) .\<sim> t)
             \<longrightarrow> ((exec_eventR s a) \<sim>. d .\<sim> (exec_eventR t a))"
    proof -
    {
      fix d s t
      assume p1: "reachable0 s"
      assume p2: "reachable0 t"
      assume p3: "s \<sim>. d .\<sim> t"
      assume p4: "interferesR (the (domain_of_eventR a)) s d "
      assume p5: "(s \<sim>. (the (domain_of_eventR a)) .\<sim> t)"
      have a0: "domain_of_eventR a = Some did"
        using p0 domain_of_eventR_def by auto
      have a1: "exec_eventR s a = fst (send_queuing_messageR s did eid m)"
        using p0 exec_eventR_def by auto
      have a2: "exec_eventR t a = fst (send_queuing_messageR t did eid m)"
        using p0 exec_eventR_def by auto
      let ?s'= "fst (send_queuing_messageR s did eid m)"
      let ?t'= "fst (send_queuing_messageR t did eid m)"
      have a3: "CapFlow.interferes (the (domain_of_eventR a)) (\<Up>s) d"
        using p4 interferesR_def by auto
      let ?a' = "CapFlow.Event.Send_Queuing_Message did eid m"
      let ?ss' = "CapFlow.exec_event (\<Up>s) ?a'"
      let ?tt' = "CapFlow.exec_event (\<Up>t) ?a'"
      have a4: "CapFlow.reachable0 (\<Up>s)"
        using reachR_reach p1 by auto
      have a5: "CapFlow.reachable0 (\<Up>t)"
        using reachR_reach p2 by auto
      have a6: "the (domain_of_event ?a') = did"
        using domain_of_event_def by auto
      have a7: "(interferes did (\<Up>s) d)"
        using a3 a0 a6 by auto
      have a8: "(\<Up>s) \<sim> d \<sim> (\<Up>t)"
        using p3 vpeqR_def by blast
      have a9: "((\<Up>s) \<sim> (the (domain_of_eventR a)) \<sim> (\<Up>t))"
        using p5 vpeqR_def by blast
      have a10: "(?ss' \<sim> d \<sim> ?tt')"
        by (metis a0 a4 a5 a6 a7 a8 a9 send_queuing_message_wsc_e option.sel)
      have a11: "?ss' = fst (send_queuing_message (\<Up>s) did eid m)"
        using CapFlow.exec_event_def by auto
      have a12: "?tt' = fst (send_queuing_message (\<Up>t) did eid m)"
        using CapFlow.exec_event_def by auto
      have a13: "?ss' = \<Up>((exec_eventR s a))"
        using a1 a11 by auto
      have a14: "?tt' = \<Up>((exec_eventR t a))"
        using a2 a12 by auto
      have a15: "((\<Up>(exec_eventR s a)) \<sim> d \<sim> (\<Up>(exec_eventR t a)))"
        using a13 a14 a10 by auto
      have a16: "((exec_eventR s a) \<sim>. d .\<sim>\<^sub>\<Delta> (exec_eventR t a))"
        using a1 a2 send_queuing_messageR_presrv_wk_stp_cons_new p3 by blast
      have a17: "((exec_eventR s a) \<sim>. d .\<sim> (exec_eventR t a))"
        using a15 a16 vpeqR_def by auto
      }
    then show ?thesis by blast
  qed

  lemma send_queuing_messageR_presrv_wk_stp_cons_new_e: 
        "dynamic_weakly_step_consistent_new_e (Send_Queuing_Message did eid m)"
    by (meson send_queuing_messageR_presrv_wk_stp_cons_new_helper dynamic_weakly_step_consistent_new_e_def)

subsubsection{*proving "receive queuing message"*}

  lemma receive_queuing_messageR_presrv_wk_stp_cons_new:
      assumes 
              p1:"s \<sim>. d .\<sim> t"
        and   p2:"s' = fst (receive_queuing_messageR s did eid)"
        and   p3:"t' = fst (receive_queuing_messageR t did eid)"
      shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'" 
    using p1 p2 p3 by fastforce

  lemma receive_queuing_messageR_presrv_wk_stp_cons_new_helper: 
    assumes p0: "a = Receive_Queuing_Message did eid"
    shows "\<forall>d s t. reachable0 s \<and> reachable0 t \<and> (s \<sim>. d .\<sim> t) \<and>
             interferesR (the (domain_of_eventR a)) s d \<and> (s \<sim>. (the (domain_of_eventR a)) .\<sim> t)
             \<longrightarrow> ((exec_eventR s a) \<sim>. d .\<sim> (exec_eventR t a))"
    proof -
    {
      fix d s t
      assume p1: "reachable0 s"
      assume p2: "reachable0 t"
      assume p3: "s \<sim>. d .\<sim> t"
      assume p4: "interferesR (the (domain_of_eventR a)) s d "
      assume p5: "(s \<sim>. (the (domain_of_eventR a)) .\<sim> t)"
      have a0: "domain_of_eventR a = Some did"
        using p0 domain_of_eventR_def by auto
      have a1: "exec_eventR s a = fst (receive_queuing_messageR s did eid)"
        using p0 exec_eventR_def by auto
      have a2: "exec_eventR t a = fst (receive_queuing_messageR t did eid)"
        using p0 exec_eventR_def by auto
      let ?s'= "fst (receive_queuing_messageR s did eid)"
      let ?t'= "fst (receive_queuing_messageR t did eid)"
      have a3: "CapFlow.interferes (the (domain_of_eventR a)) (\<Up>s) d"
        using p4 interferesR_def by auto
      let ?a' = "CapFlow.Event.Receive_Queuing_Message did eid"
      let ?ss' = "CapFlow.exec_event (\<Up>s) ?a'"
      let ?tt' = "CapFlow.exec_event (\<Up>t) ?a'"
      have a4: "CapFlow.reachable0 (\<Up>s)"
        using reachR_reach p1 by auto
      have a5: "CapFlow.reachable0 (\<Up>t)"
        using reachR_reach p2 by auto
      have a6: "the (domain_of_event ?a') = did"
        using domain_of_event_def by auto
      have a7: "(interferes did (\<Up>s) d)"
        using a3 a0 a6 by auto
      have a8: "(\<Up>s) \<sim> d \<sim> (\<Up>t)"
        using p3 vpeqR_def by blast
      have a9: "((\<Up>s) \<sim> (the (domain_of_eventR a)) \<sim> (\<Up>t))"
        using p5 vpeqR_def by blast
      have a10: "(?ss' \<sim> d \<sim> ?tt')"
        by (metis a0 a4 a5 a6 a7 a8 a9 receive_queuing_message_wsc_e option.sel)
      have a11: "?ss' = fst (receive_queuing_message (\<Up>s) did eid)"
        using CapFlow.exec_event_def by auto
      have a12: "?tt' = fst (receive_queuing_message (\<Up>t) did eid)"
        using CapFlow.exec_event_def by auto
      have a13: "?ss' = \<Up>((exec_eventR s a))"
        using a1 a11 by auto
      have a14: "?tt' = \<Up>((exec_eventR t a))"
        using a2 a12 by auto
      have a15: "((\<Up>(exec_eventR s a)) \<sim> d \<sim> (\<Up>(exec_eventR t a)))"
        using a13 a14 a10 by auto
      have a16: "((exec_eventR s a) \<sim>. d .\<sim>\<^sub>\<Delta> (exec_eventR t a))"
        using a1 a2 receive_queuing_messageR_presrv_wk_stp_cons_new p3 by blast
      have a17: "((exec_eventR s a) \<sim>. d .\<sim> (exec_eventR t a))"
        using a15 a16 vpeqR_def by auto
      }
    then show ?thesis by blast
  qed

  lemma receive_queuing_messageR_presrv_wk_stp_cons_new_e: 
        "dynamic_weakly_step_consistent_new_e (Receive_Queuing_Message did eid)"
    by (meson receive_queuing_messageR_presrv_wk_stp_cons_new_helper dynamic_weakly_step_consistent_new_e_def)

subsubsection{*proving "get my endpoint"*}

  lemma get_my_endpoints_setR_presrv_wk_stp_cons_new:
      assumes 
              p1:"s \<sim>. d .\<sim> t"
        and   p2:"s' = fst (get_my_endpoints_setR s did)"
        and   p3:"t' = fst (get_my_endpoints_setR t did)"
      shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'" 
    using p1 p2 p3 by fastforce

  lemma get_my_endpoints_setR_presrv_wk_stp_cons_new_helper: 
    assumes p0: "a = Get_My_Endpoints_Set did"
    shows "\<forall>d s t. reachable0 s \<and> reachable0 t \<and> (s \<sim>. d .\<sim> t) \<and>
             interferesR (the (domain_of_eventR a)) s d \<and> (s \<sim>. (the (domain_of_eventR a)) .\<sim> t)
             \<longrightarrow> ((exec_eventR s a) \<sim>. d .\<sim> (exec_eventR t a))"
    proof -
    {
      fix d s t
      assume p1: "reachable0 s"
      assume p2: "reachable0 t"
      assume p3: "s \<sim>. d .\<sim> t"
      assume p4: "interferesR (the (domain_of_eventR a)) s d "
      assume p5: "(s \<sim>. (the (domain_of_eventR a)) .\<sim> t)"
      have a0: "domain_of_eventR a = Some did"
        using p0 domain_of_eventR_def by auto
      have a1: "exec_eventR s a = fst (get_my_endpoints_setR s did)"
        using p0 exec_eventR_def by auto
      have a2: "exec_eventR t a = fst (get_my_endpoints_setR t did)"
        using p0 exec_eventR_def by auto
      let ?s'= "fst (get_my_endpoints_setR s did)"
      let ?t'= "fst (get_my_endpoints_setR t did)"
      have a3: "CapFlow.interferes (the (domain_of_eventR a)) (\<Up>s) d"
        using p4 interferesR_def by auto
      let ?a' = "CapFlow.Event.Get_My_Endpoints_Set did"
      let ?ss' = "CapFlow.exec_event (\<Up>s) ?a'"
      let ?tt' = "CapFlow.exec_event (\<Up>t) ?a'"
      have a4: "CapFlow.reachable0 (\<Up>s)"
        using reachR_reach p1 by auto
      have a5: "CapFlow.reachable0 (\<Up>t)"
        using reachR_reach p2 by auto
      have a6: "the (domain_of_event ?a') = did"
        using domain_of_event_def by auto
      have a7: "(interferes did (\<Up>s) d)"
        using a3 a0 a6 by auto
      have a8: "(\<Up>s) \<sim> d \<sim> (\<Up>t)"
        using p3 vpeqR_def by blast
      have a9: "((\<Up>s) \<sim> (the (domain_of_eventR a)) \<sim> (\<Up>t))"
        using p5 vpeqR_def by blast
      have a10: "(?ss' \<sim> d \<sim> ?tt')"
        by (metis a0 a4 a5 a6 a7 a8 a9 get_my_endpoints_set_wsc_e option.sel)
      have a11: "?ss' = fst (get_my_endpoints_set (\<Up>s) did)"
        using CapFlow.exec_event_def by auto
      have a12: "?tt' = fst (get_my_endpoints_set (\<Up>t) did)"
        using CapFlow.exec_event_def by auto
      have a13: "?ss' = \<Up>((exec_eventR s a))"
        using a1 a11 by auto
      have a14: "?tt' = \<Up>((exec_eventR t a))"
        using a2 a12 by auto
      have a15: "((\<Up>(exec_eventR s a)) \<sim> d \<sim> (\<Up>(exec_eventR t a)))"
        using a13 a14 a10 by auto
      have a16: "((exec_eventR s a) \<sim>. d .\<sim>\<^sub>\<Delta> (exec_eventR t a))"
        using a1 a2 get_my_endpoints_setR_presrv_wk_stp_cons_new p3 by blast
      have a17: "((exec_eventR s a) \<sim>. d .\<sim> (exec_eventR t a))"
        using a15 a16 vpeqR_def by auto
      }
    then show ?thesis by blast
  qed

  lemma get_my_endpoints_setR_presrv_wk_stp_cons_new_e: 
        "dynamic_weakly_step_consistent_new_e (Get_My_Endpoints_Set did)"
    by (meson get_my_endpoints_setR_presrv_wk_stp_cons_new_helper dynamic_weakly_step_consistent_new_e_def)

subsubsection{*proving "get cap set"*}

  lemma get_capsR_presrv_wk_stp_cons_new:
      assumes 
              p1:"s \<sim>. d .\<sim> t"
        and   p2:"s' = fst (get_capsR s did)"
        and   p3:"t' = fst (get_capsR t did)"
      shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'" 
    using p1 p2 p3 by fastforce

  lemma get_capsR_presrv_wk_stp_cons_new_helper: 
    assumes p0: "a = Get_Caps did"
    shows "\<forall>d s t. reachable0 s \<and> reachable0 t \<and> (s \<sim>. d .\<sim> t) \<and>
             interferesR (the (domain_of_eventR a)) s d \<and> (s \<sim>. (the (domain_of_eventR a)) .\<sim> t)
             \<longrightarrow> ((exec_eventR s a) \<sim>. d .\<sim> (exec_eventR t a))"
    proof -
    {
      fix d s t
      assume p1: "reachable0 s"
      assume p2: "reachable0 t"
      assume p3: "s \<sim>. d .\<sim> t"
      assume p4: "interferesR (the (domain_of_eventR a)) s d "
      assume p5: "(s \<sim>. (the (domain_of_eventR a)) .\<sim> t)"
      have a0: "domain_of_eventR a = Some did"
        using p0 domain_of_eventR_def by auto
      have a1: "exec_eventR s a = fst (get_capsR s did)"
        using p0 exec_eventR_def by auto
      have a2: "exec_eventR t a = fst (get_capsR t did)"
        using p0 exec_eventR_def by auto
      let ?s'= "fst (get_capsR s did)"
      let ?t'= "fst (get_capsR t did)"
      have a3: "CapFlow.interferes (the (domain_of_eventR a)) (\<Up>s) d"
        using p4 interferesR_def by auto
      let ?a' = "CapFlow.Event.Get_Caps did"
      let ?ss' = "CapFlow.exec_event (\<Up>s) ?a'"
      let ?tt' = "CapFlow.exec_event (\<Up>t) ?a'"
      have a4: "CapFlow.reachable0 (\<Up>s)"
        using reachR_reach p1 by auto
      have a5: "CapFlow.reachable0 (\<Up>t)"
        using reachR_reach p2 by auto
      have a6: "the (domain_of_event ?a') = did"
        using domain_of_event_def by auto
      have a7: "(interferes did (\<Up>s) d)"
        using a3 a0 a6 by auto
      have a8: "(\<Up>s) \<sim> d \<sim> (\<Up>t)"
        using p3 vpeqR_def by blast
      have a9: "((\<Up>s) \<sim> (the (domain_of_eventR a)) \<sim> (\<Up>t))"
        using p5 vpeqR_def by blast
      have a10: "(?ss' \<sim> d \<sim> ?tt')"
        by (metis a0 a4 a5 a6 a7 a8 a9 get_caps_wsc_e option.sel)
      have a11: "?ss' = fst (get_caps (\<Up>s) did)"
        using CapFlow.exec_event_def by auto
      have a12: "?tt' = fst (get_caps (\<Up>t) did)"
        using CapFlow.exec_event_def by auto
      have a13: "?ss' = \<Up>((exec_eventR s a))"
        using a1 a11 by auto
      have a14: "?tt' = \<Up>((exec_eventR t a))"
        using a2 a12 by auto
      have a15: "((\<Up>(exec_eventR s a)) \<sim> d \<sim> (\<Up>(exec_eventR t a)))"
        using a13 a14 a10 by auto
      have a16: "((exec_eventR s a) \<sim>. d .\<sim>\<^sub>\<Delta> (exec_eventR t a))"
        using a1 a2 get_capsR_presrv_wk_stp_cons_new p3 by blast
      have a17: "((exec_eventR s a) \<sim>. d .\<sim> (exec_eventR t a))"
        using a15 a16 vpeqR_def by auto
      }
    then show ?thesis by blast
  qed

  lemma get_capsR_presrv_wk_stp_cons_new_e: 
        "dynamic_weakly_step_consistent_new_e (Get_Caps did)"
    by (meson get_capsR_presrv_wk_stp_cons_new_helper dynamic_weakly_step_consistent_new_e_def)


subsubsection{*proving "grant endpoint cap"*}

  lemma grant_endpoint_capR_presrv_wk_stp_cons_new:
      assumes 
              p1:"s \<sim>. d .\<sim> t"
        and   p2:"s' = fst (grant_endpoint_capR s did grant_cap dst_cap)"
        and   p3:"t' = fst (grant_endpoint_capR t did grant_cap dst_cap)"
      shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'" 
    using p1 p2 p3 by fastforce

  lemma grant_endpoint_capR_presrv_wk_stp_cons_new_helper: 
    assumes p0: "a = Grant_Endpoint_Cap did grant_cap dst_cap"
    shows "\<forall>d s t. reachable0 s \<and> reachable0 t \<and> (s \<sim>. d .\<sim> t) \<and>
             interferesR (the (domain_of_eventR a)) s d \<and> (s \<sim>. (the (domain_of_eventR a)) .\<sim> t)
             \<longrightarrow> ((exec_eventR s a) \<sim>. d .\<sim> (exec_eventR t a))"
    proof -
    {
      fix d s t
      assume p1: "reachable0 s"
      assume p2: "reachable0 t"
      assume p3: "s \<sim>. d .\<sim> t"
      assume p4: "interferesR (the (domain_of_eventR a)) s d "
      assume p5: "(s \<sim>. (the (domain_of_eventR a)) .\<sim> t)"
      have a0: "domain_of_eventR a = Some did"
        using p0 domain_of_eventR_def by auto
      have a1: "exec_eventR s a = fst (grant_endpoint_capR s did grant_cap dst_cap)"
        using p0 exec_eventR_def by auto
      have a2: "exec_eventR t a = fst (grant_endpoint_capR t did grant_cap dst_cap)"
        using p0 exec_eventR_def by auto
      let ?s'= "fst (grant_endpoint_capR s did grant_cap dst_cap)"
      let ?t'= "fst (grant_endpoint_capR t did grant_cap dst_cap)"
      have a3: "CapFlow.interferes (the (domain_of_eventR a)) (\<Up>s) d"
        using p4 interferesR_def by auto
      let ?a' = "CapFlow.Event.Grant_Endpoint_Cap did grant_cap dst_cap"
      let ?ss' = "CapFlow.exec_event (\<Up>s) ?a'"
      let ?tt' = "CapFlow.exec_event (\<Up>t) ?a'"
      have a4: "CapFlow.reachable0 (\<Up>s)"
        using reachR_reach p1 by auto
      have a5: "CapFlow.reachable0 (\<Up>t)"
        using reachR_reach p2 by auto
      have a6: "the (domain_of_event ?a') = did"
        using domain_of_event_def by auto
      have a7: "(interferes did (\<Up>s) d)"
        using a3 a0 a6 by auto
      have a8: "(\<Up>s) \<sim> d \<sim> (\<Up>t)"
        using p3 vpeqR_def by blast
      have a9: "((\<Up>s) \<sim> (the (domain_of_eventR a)) \<sim> (\<Up>t))"
        using p5 vpeqR_def by blast
      have a10: "(?ss' \<sim> d \<sim> ?tt')"
        by (metis a0 a4 a5 a6 a7 a8 a9 grant_endpoint_cap_wsc_e option.sel)
      have a11: "?ss' = fst (grant_endpoint_cap (\<Up>s) did grant_cap dst_cap)"
        using CapFlow.exec_event_def by auto
      have a12: "?tt' = fst (grant_endpoint_cap (\<Up>t) did grant_cap dst_cap)"
        using CapFlow.exec_event_def by auto
      have a13: "?ss' = \<Up>((exec_eventR s a))"
        using a1 a11 by auto
      have a14: "?tt' = \<Up>((exec_eventR t a))"
        using a2 a12 by auto
      have a15: "((\<Up>(exec_eventR s a)) \<sim> d \<sim> (\<Up>(exec_eventR t a)))"
        using a13 a14 a10 by auto
      have a16: "((exec_eventR s a) \<sim>. d .\<sim>\<^sub>\<Delta> (exec_eventR t a))"
        using a1 a2 grant_endpoint_capR_presrv_wk_stp_cons_new p3 by blast
      have a17: "((exec_eventR s a) \<sim>. d .\<sim> (exec_eventR t a))"
        using a15 a16 vpeqR_def by auto
      }
    then show ?thesis by blast
  qed

  lemma grant_endpoint_capR_presrv_wk_stp_cons_new_e: 
        "dynamic_weakly_step_consistent_new_e (Grant_Endpoint_Cap did grant_cap dst_cap)"
    by (meson grant_endpoint_capR_presrv_wk_stp_cons_new_helper dynamic_weakly_step_consistent_new_e_def)

subsubsection{*proving "remove capability right"*}

  lemma remove_cap_rightR_presrv_wk_stp_cons_new:
      assumes 
              p1:"s \<sim>. d .\<sim> t"
        and   p2:"s' = fst (remove_cap_rightR s did dst_cap right_to_rm)"
        and   p3:"t' = fst (remove_cap_rightR t did dst_cap right_to_rm)"
      shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'" 
    using p1 p2 p3 by fastforce

  lemma remove_cap_rightR_presrv_wk_stp_cons_new_helper: 
    assumes p0: "a = Remove_Cap_Right did dst_cap right_to_rm"
    shows "\<forall>d s t. reachable0 s \<and> reachable0 t \<and> (s \<sim>. d .\<sim> t) \<and>
             interferesR (the (domain_of_eventR a)) s d \<and> (s \<sim>. (the (domain_of_eventR a)) .\<sim> t)
             \<longrightarrow> ((exec_eventR s a) \<sim>. d .\<sim> (exec_eventR t a))"
    proof -
    {
      fix d s t
      assume p1: "reachable0 s"
      assume p2: "reachable0 t"
      assume p3: "s \<sim>. d .\<sim> t"
      assume p4: "interferesR (the (domain_of_eventR a)) s d "
      assume p5: "(s \<sim>. (the (domain_of_eventR a)) .\<sim> t)"
      have a0: "domain_of_eventR a = Some did"
        using p0 domain_of_eventR_def by auto
      have a1: "exec_eventR s a = fst (remove_cap_rightR s did dst_cap right_to_rm)"
        using p0 exec_eventR_def by auto
      have a2: "exec_eventR t a = fst (remove_cap_rightR t did dst_cap right_to_rm)"
        using p0 exec_eventR_def by auto
      let ?s'= "fst (remove_cap_rightR s did dst_cap right_to_rm)"
      let ?t'= "fst (remove_cap_rightR t did dst_cap right_to_rm)"
      have a3: "CapFlow.interferes (the (domain_of_eventR a)) (\<Up>s) d"
        using p4 interferesR_def by auto
      let ?a' = "CapFlow.Event.Remove_Cap_Right did dst_cap right_to_rm"
      let ?ss' = "CapFlow.exec_event (\<Up>s) ?a'"
      let ?tt' = "CapFlow.exec_event (\<Up>t) ?a'"
      have a4: "CapFlow.reachable0 (\<Up>s)"
        using reachR_reach p1 by auto
      have a5: "CapFlow.reachable0 (\<Up>t)"
        using reachR_reach p2 by auto
      have a6: "the (domain_of_event ?a') = did"
        using domain_of_event_def by auto
      have a7: "(interferes did (\<Up>s) d)"
        using a3 a0 a6 by auto
      have a8: "(\<Up>s) \<sim> d \<sim> (\<Up>t)"
        using p3 vpeqR_def by blast
      have a9: "((\<Up>s) \<sim> (the (domain_of_eventR a)) \<sim> (\<Up>t))"
        using p5 vpeqR_def by blast
      have a10: "(?ss' \<sim> d \<sim> ?tt')"
        by (metis a0 a4 a5 a6 a7 a8 a9 remove_cap_right_wsc_e option.sel)
      have a11: "?ss' = fst (remove_cap_right (\<Up>s) did dst_cap right_to_rm)"
        using CapFlow.exec_event_def by auto
      have a12: "?tt' = fst (remove_cap_right (\<Up>t) did dst_cap right_to_rm)"
        using CapFlow.exec_event_def by auto
      have a13: "?ss' = \<Up>((exec_eventR s a))"
        using a1 a11 by auto
      have a14: "?tt' = \<Up>((exec_eventR t a))"
        using a2 a12 by auto
      have a15: "((\<Up>(exec_eventR s a)) \<sim> d \<sim> (\<Up>(exec_eventR t a)))"
        using a13 a14 a10 by auto
      have a16: "((exec_eventR s a) \<sim>. d .\<sim>\<^sub>\<Delta> (exec_eventR t a))"
        using a1 a2 remove_cap_rightR_presrv_wk_stp_cons_new p3 by blast
      have a17: "((exec_eventR s a) \<sim>. d .\<sim> (exec_eventR t a))"
        using a15 a16 vpeqR_def by auto
      }
    then show ?thesis by blast
  qed

  lemma remove_cap_rightR_presrv_wk_stp_cons_new_e: 
        "dynamic_weakly_step_consistent_new_e (Remove_Cap_Right did dst_cap right_to_rm)"
    by (meson remove_cap_rightR_presrv_wk_stp_cons_new_helper dynamic_weakly_step_consistent_new_e_def)

subsection{* New events preserve "step consistent" on new state variables *} 

subsubsection{*proving "system dispatcher set properties"*}

  lemma sys_dispatcher_properties_wk_stp_cons_new:
    assumes p0: "a = Sys_Dispatcher_Properties did p_type p_deadline p_wcet p_period p_release p_weight"
      and   p1:"reachable0 s"        
      and   p2:"reachable0 t"
      and   p3:"(s \<sim>. d .\<sim> t)"
      and   p4:"interferesR (the (domain_of_eventR a)) s d"        
      and   p5:"(s \<sim>. (the (domain_of_eventR a)) .\<sim> t)"
    shows   "(exec_eventR s a) \<sim>. d .\<sim> (exec_eventR t a)"
    proof -
    {
      let ?s' = "(exec_eventR s a)"
      let ?t' = "(exec_eventR t a)"
      have b0: "?s' = fst (sys_dispatcher_properties s did p_type p_deadline p_wcet p_period p_release p_weight)"
        using p0 exec_eventR_def by auto
      have b1: "?t' = fst (sys_dispatcher_properties t did p_type p_deadline p_wcet p_period p_release p_weight)"
        using p0 exec_eventR_def by auto
      have a0: "s \<sim>. d .\<sim>\<^sub>\<Delta> t"
        using p3 vpeqR_def by auto
      have a1: "dispatchers s d = dispatchers t d"
        using a0 vpeq_dispatcher_def by auto
      have a2: "cspaces s d = cspaces t d"
        using a0 vpeq_dispatcher_def by auto
      have a3: "dispatchers ?s' d = dispatchers ?t' d"
        using a1 sys_dispatcher_properties_def b0 b1 by auto
      have a4: "cspaces ?s' d = cspaces ?t' d"
        using a2 sys_dispatcher_properties_def b0 b1 by auto
      have a5: "?s' \<sim>. d .\<sim>\<^sub>\<Delta> ?t'"
        using a3 a4 vpeq_dispatcher_def by auto
      have a6: "(\<Up>s) = (\<Up>?s')"
        using sys_dispatcher_properties_nchastate_lemma b0 by auto
      have a7: "(\<Up>t) = (\<Up>?t')"
        using sys_dispatcher_properties_nchastate_lemma b1 by auto
      have a8: "(\<Up>s) \<sim> d \<sim> (\<Up>t)"
        using p3 vpeqR_def by blast
      have a9: "(\<Up>?s') \<sim> d \<sim> (\<Up>?t')"
        using a6 a7 a8 by auto
      have a10: "?s' \<sim>. d .\<sim> ?t'"
        using a5 a9 vpeqR_def by auto
    }
    then show ?thesis by auto
  qed

  lemma sys_dispatcher_properties_stp_cons_new_e:
        "dynamic_weakly_step_consistent_new_e (Sys_Dispatcher_Properties did p_type p_deadline p_wcet 
            p_period p_release p_weight)"
    by (meson sys_dispatcher_properties_wk_stp_cons_new dynamic_weakly_step_consistent_new_e_def)

subsubsection{*proving "system dispatcher setup"*}

  lemma sys_dispatcher_setup_wk_stp_cons_new:
    assumes p0: "a = Sys_Dispatcher_Setup did p_cptr p_vptr p_dptr p_run"
      and   p1:"reachable0 s"        
      and   p2:"reachable0 t"
      and   p3:"(s \<sim>. d .\<sim> t)"
      and   p4:"interferesR (the (domain_of_eventR a)) s d"        
      and   p5:"(s \<sim>. (the (domain_of_eventR a)) .\<sim> t)"
    shows   "(exec_eventR s a) \<sim>. d .\<sim> (exec_eventR t a)"
    proof -
    {
      let ?s' = "(exec_eventR s a)"
      let ?t' = "(exec_eventR t a)"
      have b0: "?s' = fst (sys_dispatcher_setup s did p_cptr p_vptr p_dptr p_run)"
        using p0 exec_eventR_def by auto
      have b1: "?t' = fst (sys_dispatcher_setup t did p_cptr p_vptr p_dptr p_run)"
        using p0 exec_eventR_def by auto
      have a0: "s \<sim>. d .\<sim>\<^sub>\<Delta> t"
        using p3 vpeqR_def by auto
      have a1: "dispatchers s d = dispatchers t d"
        using a0 vpeq_dispatcher_def by auto
      have a2: "cspaces s d = cspaces t d"
        using a0 vpeq_dispatcher_def by auto
      have a3: "dispatchers ?s' d = dispatchers ?t' d"
        using a1 sys_dispatcher_setup_def b0 b1 by auto
      have a4: "cspaces ?s' d = cspaces ?t' d"
        using a2 sys_dispatcher_setup_def b0 b1 by auto
      have a5: "?s' \<sim>. d .\<sim>\<^sub>\<Delta> ?t'"
        using a3 a4 vpeq_dispatcher_def by auto
      have a6: "(\<Up>s) = (\<Up>?s')"
        using sys_dispatcher_setup_nchastate_lemma b0 by auto
      have a7: "(\<Up>t) = (\<Up>?t')"
        using sys_dispatcher_setup_nchastate_lemma b1 by auto
      have a8: "(\<Up>s) \<sim> d \<sim> (\<Up>t)"
        using p3 vpeqR_def by blast
      have a9: "(\<Up>?s') \<sim> d \<sim> (\<Up>?t')"
        using a6 a7 a8 by auto
      have a10: "?s' \<sim>. d .\<sim> ?t'"
        using a5 a9 vpeqR_def by auto
    }
    then show ?thesis by auto
  qed

  lemma sys_dispatcher_setup_wk_stp_cons_new_e:
        "dynamic_weakly_step_consistent_new_e (Sys_Dispatcher_Setup did p_cptr p_vptr p_dptr p_run)"
    by (meson sys_dispatcher_setup_wk_stp_cons_new dynamic_weakly_step_consistent_new_e_def)

subsubsection{*proving "dispatcher dump ptables"*}

  lemma dispatcher_dump_ptables_wk_stp_cons_new:
    assumes p0: "a = Dispatcher_Dump_Ptables did"
      and   p1:"reachable0 s"        
      and   p2:"reachable0 t"
      and   p3:"(s \<sim>. d .\<sim> t)"
      and   p4:"interferesR (the (domain_of_eventR a)) s d"        
      and   p5:"(s \<sim>. (the (domain_of_eventR a)) .\<sim> t)"
    shows   "(exec_eventR s a) \<sim>. d .\<sim> (exec_eventR t a)"
    proof -
    {
      let ?s' = "(exec_eventR s a)"
      let ?t' = "(exec_eventR t a)"
      have b0: "?s' = fst (dispatcher_dump_ptables s did )"
        using p0 exec_eventR_def by auto
      have b1: "?t' = fst (dispatcher_dump_ptables t did )"
        using p0 exec_eventR_def by auto
      have a0: "s \<sim>. d .\<sim>\<^sub>\<Delta> t"
        using p3 vpeqR_def by auto
      have a1: "dispatchers s d = dispatchers t d"
        using a0 vpeq_dispatcher_def by auto
      have a2: "cspaces s d = cspaces t d"
        using a0 vpeq_dispatcher_def by auto
      have a3: "dispatchers ?s' d = dispatchers ?t' d"
        using a1 dispatcher_dump_ptables_def b0 b1 by auto
      have a4: "cspaces ?s' d = cspaces ?t' d"
        using a2 dispatcher_dump_ptables_def b0 b1 by auto
      have a5: "?s' \<sim>. d .\<sim>\<^sub>\<Delta> ?t'"
        using a3 a4 vpeq_dispatcher_def by auto
      have a6: "(\<Up>s) = (\<Up>?s')"
        using dispatcher_dump_ptables_nchastate_lemma b0 by auto
      have a7: "(\<Up>t) = (\<Up>?t')"
        using dispatcher_dump_ptables_nchastate_lemma b1 by auto
      have a8: "(\<Up>s) \<sim> d \<sim> (\<Up>t)"
        using p3 vpeqR_def by blast
      have a9: "(\<Up>?s') \<sim> d \<sim> (\<Up>?t')"
        using a6 a7 a8 by auto
      have a10: "?s' \<sim>. d .\<sim> ?t'"
        using a5 a9 vpeqR_def by auto
    }
    then show ?thesis by auto
  qed

  lemma dispatcher_dump_ptables_wk_stp_cons_new_e:
        "dynamic_weakly_step_consistent_new_e (Dispatcher_Dump_Ptables did)"
    by (meson dispatcher_dump_ptables_wk_stp_cons_new dynamic_weakly_step_consistent_new_e_def)

subsubsection{*proving "capability copy"*}

  lemma capability_copy_wk_stp_cons_new:
    assumes p0: "a = Capability_Copy did c"
      and   p1:"reachable0 s"        
      and   p2:"reachable0 t"
      and   p3:"(s \<sim>. d .\<sim> t)"
      and   p4:"interferesR (the (domain_of_eventR a)) s d"        
      and   p5:"(s \<sim>. (the (domain_of_eventR a)) .\<sim> t)"
    shows   "(exec_eventR s a) \<sim>. d .\<sim> (exec_eventR t a)"
    proof -
    {
      let ?s' = "(exec_eventR s a)"
      let ?t' = "(exec_eventR t a)"
      have b0: "?s' = fst (capability_copy s did c)"
        using p0 exec_eventR_def by auto
      have b1: "?t' = fst (capability_copy t did c)"
        using p0 exec_eventR_def by auto
      have a0: "s \<sim>. d .\<sim>\<^sub>\<Delta> t"
        using p3 vpeqR_def by auto
      have a1: "dispatchers s d = dispatchers t d"
        using a0 vpeq_dispatcher_def by auto
      have a2: "cspaces s d = cspaces t d"
        using a0 vpeq_dispatcher_def by auto
      have a3: "dispatchers ?s' d = dispatchers ?t' d"
        using a1 capability_copy_def b0 b1 by auto
      have a4: "cspaces ?s' d = cspaces ?t' d"
        using a2 capability_copy_def b0 b1 by auto
      have a5: "?s' \<sim>. d .\<sim>\<^sub>\<Delta> ?t'"
        using a3 a4 vpeq_dispatcher_def by auto
      have a6: "(\<Up>s) = (\<Up>?s')"
        using capability_copy_nchastate_lemma b0 by auto
      have a7: "(\<Up>t) = (\<Up>?t')"
        using capability_copy_nchastate_lemma b1 by auto
      have a8: "(\<Up>s) \<sim> d \<sim> (\<Up>t)"
        using p3 vpeqR_def by blast
      have a9: "(\<Up>?s') \<sim> d \<sim> (\<Up>?t')"
        using a6 a7 a8 by auto
      have a10: "?s' \<sim>. d .\<sim> ?t'"
        using a5 a9 vpeqR_def by auto
    }
    then show ?thesis by auto
  qed

  lemma capability_copy_wk_stp_cons_new_e:
        "dynamic_weakly_step_consistent_new_e (Capability_Copy did c)"
    by (meson capability_copy_wk_stp_cons_new dynamic_weakly_step_consistent_new_e_def)

subsubsection{*proving "capability retype"*}

  lemma capability_retype_wk_stp_cons_new:
    assumes p0: "a = Capability_Retype did cap_retype dst_type"
      and   p1:"reachable0 s"        
      and   p2:"reachable0 t"
      and   p3:"(s \<sim>. d .\<sim> t)"
      and   p4:"interferesR (the (domain_of_eventR a)) s d"        
      and   p5:"(s \<sim>. (the (domain_of_eventR a)) .\<sim> t)"
    shows   "(exec_eventR s a) \<sim>. d .\<sim> (exec_eventR t a)"
    proof -
    {
      let ?s' = "(exec_eventR s a)"
      let ?t' = "(exec_eventR t a)"
      have b0: "?s' = fst (capability_retype s did cap_retype dst_type)"
        using p0 exec_eventR_def by auto
      have b1: "?t' = fst (capability_retype t did cap_retype dst_type)"
        using p0 exec_eventR_def by auto
      have a0: "s \<sim>. d .\<sim>\<^sub>\<Delta> t"
        using p3 vpeqR_def by auto
      have a1: "dispatchers s d = dispatchers t d"
        using a0 vpeq_dispatcher_def by auto
      have a2: "cspaces s d = cspaces t d"
        using a0 vpeq_dispatcher_def by auto
      have a3: "dispatchers ?s' d = dispatchers ?t' d"
        using a1 capability_retype_def b0 b1 by auto
      have a4: "cspaces ?s' d = cspaces ?t' d"
        using a2 capability_retype_def b0 b1 by auto
      have a5: "?s' \<sim>. d .\<sim>\<^sub>\<Delta> ?t'"
        using a3 a4 vpeq_dispatcher_def by auto
      have a6: "(\<Up>s) = (\<Up>?s')"
        using capability_retype_nchastate_lemma b0 by auto
      have a7: "(\<Up>t) = (\<Up>?t')"
        using capability_retype_nchastate_lemma b1 by auto
      have a8: "(\<Up>s) \<sim> d \<sim> (\<Up>t)"
        using p3 vpeqR_def by blast
      have a9: "(\<Up>?s') \<sim> d \<sim> (\<Up>?t')"
        using a6 a7 a8 by auto
      have a10: "?s' \<sim>. d .\<sim> ?t'"
        using a5 a9 vpeqR_def by auto
    }
    then show ?thesis by auto
  qed

  lemma capability_retype_wk_stp_cons_new_e:
        "dynamic_weakly_step_consistent_new_e (Capability_Retype did cap_retype dst_type)"
    by (meson capability_retype_wk_stp_cons_new dynamic_weakly_step_consistent_new_e_def)

subsubsection{*proving "capability mint"*}

  lemma capability_mint_wk_stp_cons_new:
    assumes p0: "a = Capability_Mint did cap_mint param1 param2"
      and   p1:"reachable0 s"        
      and   p2:"reachable0 t"
      and   p3:"(s \<sim>. d .\<sim> t)"
      and   p4:"interferesR (the (domain_of_eventR a)) s d"        
      and   p5:"(s \<sim>. (the (domain_of_eventR a)) .\<sim> t)"
    shows   "(exec_eventR s a) \<sim>. d .\<sim> (exec_eventR t a)"
    proof -
    {
      let ?s' = "(exec_eventR s a)"
      let ?t' = "(exec_eventR t a)"
      have b0: "?s' = fst (capability_mint s did cap_mint param1 param2)"
        using p0 exec_eventR_def by auto
      have b1: "?t' = fst (capability_mint t did cap_mint param1 param2)"
        using p0 exec_eventR_def by auto
      have a0: "s \<sim>. d .\<sim>\<^sub>\<Delta> t"
        using p3 vpeqR_def by auto
      have a1: "dispatchers s d = dispatchers t d"
        using a0 vpeq_dispatcher_def by auto
      have a2: "cspaces s d = cspaces t d"
        using a0 vpeq_dispatcher_def by auto
      have a3: "dispatchers ?s' d = dispatchers ?t' d"
        using a1 capability_mint_def b0 b1 by auto
      have a4: "cspaces ?s' d = cspaces ?t' d"
        using a2 capability_mint_def b0 b1 by auto
      have a5: "?s' \<sim>. d .\<sim>\<^sub>\<Delta> ?t'"
        using a3 a4 vpeq_dispatcher_def by auto
      have a6: "(\<Up>s) = (\<Up>?s')"
        using capability_mint_nchastate_lemma b0 by auto
      have a7: "(\<Up>t) = (\<Up>?t')"
        using capability_mint_nchastate_lemma b1 by auto
      have a8: "(\<Up>s) \<sim> d \<sim> (\<Up>t)"
        using p3 vpeqR_def by blast
      have a9: "(\<Up>?s') \<sim> d \<sim> (\<Up>?t')"
        using a6 a7 a8 by auto
      have a10: "?s' \<sim>. d .\<sim> ?t'"
        using a5 a9 vpeqR_def by auto
    }
    then show ?thesis by auto
  qed

  lemma capability_mint_wk_stp_cons_new_e:
        "dynamic_weakly_step_consistent_new_e (Capability_Mint did cap_mint param1 param2)"
    by (meson capability_mint_wk_stp_cons_new dynamic_weakly_step_consistent_new_e_def)

subsubsection{*proving "capability delete"*}

  lemma capability_delete_wk_stp_cons_new:
    assumes p0: "a = Capability_Delete did cap_del"
      and   p1:"reachable0 s"        
      and   p2:"reachable0 t"
      and   p3:"(s \<sim>. d .\<sim> t)"
      and   p4:"interferesR (the (domain_of_eventR a)) s d"        
      and   p5:"(s \<sim>. (the (domain_of_eventR a)) .\<sim> t)"
    shows   "(exec_eventR s a) \<sim>. d .\<sim> (exec_eventR t a)"
    proof -
    {
      let ?s' = "(exec_eventR s a)"
      let ?t' = "(exec_eventR t a)"
      have b0: "?s' = fst (capability_delete s did cap_del)"
        using p0 exec_eventR_def by auto
      have b1: "?t' = fst (capability_delete t did cap_del)"
        using p0 exec_eventR_def by auto
      have a0: "s \<sim>. d .\<sim>\<^sub>\<Delta> t"
        using p3 vpeqR_def by auto
      have a1: "dispatchers s d = dispatchers t d"
        using a0 vpeq_dispatcher_def by auto
      have a2: "cspaces s d = cspaces t d"
        using a0 vpeq_dispatcher_def by auto
      have a3: "dispatchers ?s' d = dispatchers ?t' d"
        using a1 capability_delete_def b0 b1 by auto
      have a4: "cspaces ?s' d = cspaces ?t' d"
        using a2 capability_delete_def b0 b1 by auto
      have a5: "?s' \<sim>. d .\<sim>\<^sub>\<Delta> ?t'"
        using a3 a4 vpeq_dispatcher_def by auto
      have a6: "(\<Up>s) = (\<Up>?s')"
        using capability_delete_nchastate_lemma b0 by auto
      have a7: "(\<Up>t) = (\<Up>?t')"
        using capability_delete_nchastate_lemma b1 by auto
      have a8: "(\<Up>s) \<sim> d \<sim> (\<Up>t)"
        using p3 vpeqR_def by blast
      have a9: "(\<Up>?s') \<sim> d \<sim> (\<Up>?t')"
        using a6 a7 a8 by auto
      have a10: "?s' \<sim>. d .\<sim> ?t'"
        using a5 a9 vpeqR_def by auto
    }
    then show ?thesis by auto
  qed

  lemma capability_delete_wk_stp_cons_new_e:
        "dynamic_weakly_step_consistent_new_e (Capability_Delete did cap_del)"
    by (meson capability_delete_wk_stp_cons_new dynamic_weakly_step_consistent_new_e_def)

subsubsection{*proving "capability get state"*}

  lemma capability_get_state_wk_stp_cons_new:
    assumes p0: "a = Capability_Get_State did cap_dst"
      and   p1:"reachable0 s"        
      and   p2:"reachable0 t"
      and   p3:"(s \<sim>. d .\<sim> t)"
      and   p4:"interferesR (the (domain_of_eventR a)) s d"        
      and   p5:"(s \<sim>. (the (domain_of_eventR a)) .\<sim> t)"
    shows   "(exec_eventR s a) \<sim>. d .\<sim> (exec_eventR t a)"
    proof -
    {
      let ?s' = "(exec_eventR s a)"
      let ?t' = "(exec_eventR t a)"
      have b0: "?s' = fst (capability_get_state s did cap_dst)"
        using p0 exec_eventR_def by auto
      have b1: "?t' = fst (capability_get_state t did cap_dst)"
        using p0 exec_eventR_def by auto
      have a0: "s \<sim>. d .\<sim>\<^sub>\<Delta> t"
        using p3 vpeqR_def by auto
      have a1: "dispatchers s d = dispatchers t d"
        using a0 vpeq_dispatcher_def by auto
      have a2: "cspaces s d = cspaces t d"
        using a0 vpeq_dispatcher_def by auto
      have a3: "dispatchers ?s' d = dispatchers ?t' d"
        using a1 capability_get_state_def b0 b1 by auto
      have a4: "cspaces ?s' d = cspaces ?t' d"
        using a2 capability_get_state_def b0 b1 by auto
      have a5: "?s' \<sim>. d .\<sim>\<^sub>\<Delta> ?t'"
        using a3 a4 vpeq_dispatcher_def by auto
      have a6: "(\<Up>s) = (\<Up>?s')"
        using capability_get_state_nchastate_lemma b0 by auto
      have a7: "(\<Up>t) = (\<Up>?t')"
        using capability_get_state_nchastate_lemma b1 by auto
      have a8: "(\<Up>s) \<sim> d \<sim> (\<Up>t)"
        using p3 vpeqR_def by blast
      have a9: "(\<Up>?s') \<sim> d \<sim> (\<Up>?t')"
        using a6 a7 a8 by auto
      have a10: "?s' \<sim>. d .\<sim> ?t'"
        using a5 a9 vpeqR_def by auto
    }
    then show ?thesis by auto
  qed

  lemma capability_get_state_wk_stp_cons_new_e:
        "dynamic_weakly_step_consistent_new_e (Capability_Get_State did cap_dst)"
    by (meson capability_get_state_wk_stp_cons_new dynamic_weakly_step_consistent_new_e_def)


subsection{* Proving the "dynamic weakly step consistent" property on new variables *}

  theorem dynamic_weakly_step_consistent_new:dynamic_weakly_step_consistent_new
  proof -
      { 
        fix e
        have "dynamic_weakly_step_consistent_new_e e"
          apply(induct e)
          using client_lookup_endpoint_nameR_presrv_wk_stp_cons_new_e
                send_queuing_messageR_presrv_wk_stp_cons_new_e
                receive_queuing_messageR_presrv_wk_stp_cons_new_e
                get_my_endpoints_setR_presrv_wk_stp_cons_new_e
                get_capsR_presrv_wk_stp_cons_new_e
                grant_endpoint_capR_presrv_wk_stp_cons_new_e
                remove_cap_rightR_presrv_wk_stp_cons_new_e
                sys_dispatcher_properties_stp_cons_new_e
                sys_dispatcher_setup_wk_stp_cons_new_e
                dispatcher_dump_ptables_wk_stp_cons_new_e
                capability_copy_wk_stp_cons_new_e
                capability_retype_wk_stp_cons_new_e
                capability_mint_wk_stp_cons_new_e
                capability_delete_wk_stp_cons_new_e                  
                capability_get_state_wk_stp_cons_new_e
           apply simp
           apply (simp add: send_queuing_messageR_presrv_wk_stp_cons_new_e)
           apply (simp add: receive_queuing_messageR_presrv_wk_stp_cons_new_e)
           apply (simp add: get_my_endpoints_setR_presrv_wk_stp_cons_new_e)
           apply (simp add: get_capsR_presrv_wk_stp_cons_new_e)
           apply (simp add: grant_endpoint_capR_presrv_wk_stp_cons_new_e)
           apply (simp add: remove_cap_rightR_presrv_wk_stp_cons_new_e)
           apply (simp add: sys_dispatcher_properties_stp_cons_new_e)
           apply (simp add: sys_dispatcher_setup_wk_stp_cons_new_e)
           apply (simp add: dispatcher_dump_ptables_wk_stp_cons_new_e)
           apply (simp add: capability_copy_wk_stp_cons_new_e)
           apply (simp add: capability_retype_wk_stp_cons_new_e)
           apply (simp add: capability_mint_wk_stp_cons_new_e)
           apply (simp add: capability_delete_wk_stp_cons_new_e)
           by (simp add: capability_get_state_wk_stp_cons_new_e)
        }
      then show ?thesis using dynamic_weakly_step_consistent_new_all_evt by simp
    qed

subsection{* Information flow security of second-level specification *}
  theorem noninfluence_sat: noninfluence
    using noninfl_refinement dynamic_local_respect_new dynamic_weakly_step_consistent_new
      dynamic_local_respect dynamic_weakly_step_consistent
    using abs_sc_new_imp by blast 

  theorem weak_noninfluence_sat: weak_noninfluence
    using noninf_impl_weak noninfluence_sat by blast
    
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