
theory BF_CapFlow
imports Dynamic_model_v6 CapFlow_v6_0

begin

type_synonym systime_t = nat

datatype
  task_type =  TASK_TYPE_BEST_EFFORT
              |TASK_TYPE_SOFT_REALTIME
              |TASK_TYPE_HARD_REALTIME    

datatype
  sys_err =  SYS_ERR_OK
              |SYS_ERR_CAP_NOT_FOUND
              |SYS_ERR_LMP_TARGET_DISABLED   
              |SYS_ERR_LMP_BUF_OVERFLOW

record dcb = disabled :: bool
             is_vm_guest :: bool
             domain_id_dcb :: domain_id
             type :: task_type
             wakeup_time :: systime_t
             release_time :: systime_t
             etime :: systime_t
             last_dispatch :: systime_t
             wcet :: systime_t
             period :: systime_t
             deadline :: systime_t
             weight :: nat


record StateR = State + 
                dispatchers :: "domain_id \<Rightarrow> dcb"

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

definition sys_dispatcher_properties :: "StateR \<Rightarrow> domain_id \<Rightarrow> systime_t \<Rightarrow> (StateR \<times> bool )" where
  "sys_dispatcher_properties sr did p_type p_deadline p_wcet p_period p_release p_weight p_wcet \<equiv>   
                  let
                    new_dispatchers = dispatchers sr;
                    t_dcb = new_dispatchers did;
                    new_dcb = t_dcb
                                \<lparr> wcet := p_wcet,
                                  is_vm_guest := is_vm_guest t_dcb,
                                  domain_id_dcb := domain_id_dcb t_dcb,
                                  wakeup_time := wakeup_time t_dcb,
                                  release_time := release_time t_dcb\<rparr>
                  in
                    (sr\<lparr>
                      dispatchers := new_dispatchers(did := new_dcb)
                      \<rparr>, True)"

end