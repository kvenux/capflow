
theory BF_CapFlow
imports Dynamic_model_v6 CapFlow_v6_0

begin

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

datatype
  capability_u =  PhysAddr 
                 |RAM
                 |L1CNode
                 |L2CNode
                 |FCNode
                 |Dispatcher
                 |EndPoint
                 |Frame
                 |DevFrame

record capability = type :: objtype
                    rights :: right
                    union_of_cap :: capability_u

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

subsubsection {* Utility Functions used for Event Specification *} 


subsubsection {* Events Definition *}

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

definition dispatcher_get_all_ep :: "StateR \<Rightarrow> domain_id \<Rightarrow> (StateR \<times> cap set )" where
  "dispatcher_get_all_ep sr did  \<equiv> let 
                                            ret = (get_caps (\<Up>sr) did) 
                                           in
                                            (sr\<Down>(fst ret),snd ret)"

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
                    target_union = union_of_cap cap_mint
                  in
                    case target_union of
                      (EndPoint) \<Rightarrow> (sr\<lparr>
                      cspaces := c_space(did := insert cap_mint c_set_rest)
                      \<rparr>, True)"

definition system_initR :: "Sys_Config \<Rightarrow> StateR"
  where "system_initR sc \<equiv> let s0 = system_init sc in 
                              \<lparr> caps = caps s0,
                                e_msgs = e_msgs s0,
                                e_buf_size = e_buf_size s0,
                                domain_endpoint = domain_endpoint s0,
                                dispatchers = (\<lambda> x. None),
                                cspaces = (\<lambda> x. {})
                               \<rparr>"

subsection{* Instantiation and Its Proofs of Security Model  *}

consts s0r :: StateR

specification (s0r) 
  s0r_init: "s0r = system_initR sysconf"
  by simp

end