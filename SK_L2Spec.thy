(*
A refinement based formal specification and information flow security proofs 
for ARINC 653 compliant separation kernels
created by Yongwang ZHAO
School of Computer Science and Engineering, Nanyang Technological University, Singapore
School of Computer Science and Engineering, Beihang University, China
zhaoyongwang@gmail.com, ywzhao@ntu.edu.sg, zhaoyw@buaa.edu.cn
*)

section {* Second-level specification and security proofs *}

theory SK_L2Spec
imports SK_SecurityModel SK_TopSpec

begin

declare [[ smt_timeout = 90 ]]

subsection {* Definitions *}

subsubsection {* Data type, basic components, and state *}

type_synonym process_id = nat
datatype process_state =  DORMANT | READY | WAITING | SUSPEND | RUNNING

type_synonym proc_priority_type = nat

record Proc_State = state :: process_state
                    priority :: proc_priority_type

record StateR = State + 
                procs :: "partition_id \<rightharpoonup> (process_id set)"
                cur_proc_part :: "partition_id \<rightharpoonup> process_id"
                proc_state :: "partition_id \<times> process_id \<rightharpoonup> Proc_State"

definition abstract_state :: "StateR \<Rightarrow> State" ("\<Up>_" [50])        
  where "abstract_state r = \<lparr>current = current r,
                            partitions = partitions r,
                            comm = comm r,
                            part_ports = part_ports r
                           \<rparr>"

definition abstract_state_rev :: "StateR \<Rightarrow> State \<Rightarrow> StateR" ("_\<Down>_" [50])
  where "abstract_state_rev r' r = r'\<lparr>current := current r,
                            partitions := partitions r,
                            comm := comm r,
                            part_ports := part_ports r\<rparr>"

subsubsection {* Events *}

datatype Hypercall' = Create_Sampling_Port port_name
                     | Write_Sampling_Message port_id Message
                     | Read_Sampling_Message port_id
                     | Get_Sampling_Portid port_name
                     | Get_Sampling_Portstatus port_id
                     | Create_Queuing_Port port_name
                     | Send_Queuing_Message port_id Message
                     | Receive_Queuing_Message port_id
                     | Get_Queuing_Portid port_name
                     | Get_Queuing_Portstatus port_id
                     | Clear_Queuing_Port port_id
                     | Set_Partition_Mode partition_mode_type
                     | Get_Partition_Status
                     | Create_Process proc_priority_type
                     | Start_Process process_id
                     | Stop_Process process_id
                     | Resume_Process process_id
                     | Suspend_Process process_id
                     | Set_Priority process_id proc_priority_type
                     | Get_Process_Status process_id

datatype System_EventR = Schedule
                        | Transfer_Sampling_Message Channel_Type
                        | Transfer_Queuing_Message Channel_Type
                        | Schedule_Process

datatype EventR = hyperc' Hypercall' | sys' System_EventR 

subsubsection{* Event specification *}

definition create_sampling_portR :: "Sys_Config \<Rightarrow> StateR \<Rightarrow> port_name \<Rightarrow> (StateR \<times> port_id option)" where
  "create_sampling_portR sc s p \<equiv> let s'= (create_sampling_port sc (\<Up>s) p) in (s\<Down>(fst s'),snd s')"

definition write_sampling_messageR :: "StateR \<Rightarrow> port_id \<Rightarrow> Message \<Rightarrow> (StateR \<times> bool)" where
  "write_sampling_messageR s p m \<equiv> let s'= (write_sampling_message (\<Up>s) p m) in (s\<Down>(fst s'),snd s')"

definition read_sampling_messageR :: "StateR \<Rightarrow> port_id \<Rightarrow> (StateR \<times> Message option)" where
  "read_sampling_messageR s pid \<equiv> let s'= (read_sampling_message (\<Up>s) pid) in (s\<Down>(fst s'),snd s')"

definition get_sampling_port_idR :: "Sys_Config \<Rightarrow> StateR \<Rightarrow> port_name \<Rightarrow> (StateR \<times> port_id option)" where
  "get_sampling_port_idR sc s pname \<equiv> let s'= (get_sampling_port_id sc (\<Up>s) pname) in (s\<Down>(fst s'),snd s')"

definition get_sampling_port_statusR :: "Sys_Config \<Rightarrow> StateR \<Rightarrow> port_id \<Rightarrow> (StateR \<times> Port_Type option)" where
  "get_sampling_port_statusR sc s pid \<equiv> let s'= (get_sampling_port_status sc (\<Up>s) pid) in (s\<Down>(fst s'),snd s')"

definition create_queuing_portR :: "Sys_Config \<Rightarrow> StateR \<Rightarrow> port_name \<Rightarrow> (StateR \<times> port_id option)" where
  "create_queuing_portR sc s p \<equiv> let s'= (create_queuing_port sc (\<Up>s) p) in (s\<Down>(fst s'),snd s')"

definition send_queuing_message_maylostR :: "Sys_Config \<Rightarrow> StateR \<Rightarrow> port_id \<Rightarrow> Message \<Rightarrow> (StateR \<times> bool)" where
  "send_queuing_message_maylostR sc s p m \<equiv> 
        let s'= (send_queuing_message_maylost sc (\<Up>s) p m) in (s\<Down>(fst s'),snd s')"

definition receive_queuing_messageR :: "StateR \<Rightarrow> port_id \<Rightarrow> (StateR \<times> Message option)" where
  "receive_queuing_messageR s pid \<equiv> let s'= (receive_queuing_message (\<Up>s) pid) in (s\<Down>(fst s'),snd s')"

definition get_queuing_port_idR :: "Sys_Config \<Rightarrow> StateR \<Rightarrow> port_name \<Rightarrow> (StateR \<times> port_id option)" where
  "get_queuing_port_idR sc s pname \<equiv> let s'= (get_queuing_port_id sc (\<Up>s) pname) in (s\<Down>(fst s'),snd s')"

definition get_queuing_port_statusR :: "Sys_Config \<Rightarrow> StateR \<Rightarrow> port_id \<Rightarrow> (StateR \<times> Port_Type option)" where
  "get_queuing_port_statusR sc s pid \<equiv> let s'= (get_queuing_port_status sc (\<Up>s) pid) in (s\<Down>(fst s'),snd s')"

definition clear_queuing_portR :: "StateR \<Rightarrow> port_id \<Rightarrow> StateR" where
  "clear_queuing_portR s pid \<equiv> let s'= (clear_queuing_port (\<Up>s) pid) in (s\<Down>s')"

definition setRun2Ready :: "StateR \<Rightarrow> StateR" where
  "setRun2Ready s \<equiv> if is_a_partition sysconf (current s) \<and> cur_proc_part s (current s) \<noteq> None then
                      let prs = proc_state s;
                          cur = the ((cur_proc_part s) (current s));
                          stt = the (prs (current s, cur)) in
                       s\<lparr>cur_proc_part := ((cur_proc_part s)) (current s := None),
                          proc_state := prs((current s, cur) := Some (stt\<lparr>state:=READY\<rparr>))\<rparr>
                     else s"

definition schedule_process :: "StateR \<Rightarrow> StateR set" where
  "schedule_process s \<equiv> if is_a_partition sysconf (current s) 
                            \<and> part_mode (the ((partitions s) (current s))) = NORMAL then
                          (let s' = setRun2Ready s;
                              readyprs = {p. p\<in>the (procs s' (current s')) \<and> 
                                 state (the (proc_state s' (current s',p))) = READY};
                              selp = SOME p. p\<in>{x. state (the (proc_state s' (current s',x))) = READY \<and>
                                                   (\<forall>y\<in>readyprs. priority (the (proc_state s' (current s',x))) \<ge>
                                                                priority (the (proc_state s' (current s',y))))};
                              st = the ((proc_state s') (current s', selp));
                              proc_st = proc_state s';
                              cur_pr = cur_proc_part s' in
                                  {s'\<lparr>proc_state := proc_st ((current s', selp) := Some (st\<lparr>state := RUNNING\<rparr>)),
                                     cur_proc_part := cur_pr(current s' := Some selp)\<rparr>})
                         else
                          {s}"

definition scheduleR :: "Sys_Config \<Rightarrow> StateR \<Rightarrow> StateR set" where
  "scheduleR sc s \<equiv> \<Union>s'\<in>schedule sc (\<Up>s). {s\<Down>s'}" 

definition get_partition_statusR :: 
    "Sys_Config \<Rightarrow> StateR \<Rightarrow> (StateR \<times> (Partition_Conf option) \<times> (Partition_State_Type option))" where
      "get_partition_statusR sc s \<equiv> let s'= (get_partition_status sc (\<Up>s)) in (s\<Down>(fst s'),snd s')"

definition remove_partition_resources :: "StateR \<Rightarrow> partition_id \<Rightarrow> StateR" where
  "remove_partition_resources s part \<equiv> 
          let proc_state' = (\<lambda>(pt, p). if pt = part then None else (proc_state s) (pt,p));
              procs' = (procs s)(part := None) in
                s\<lparr>procs := procs', proc_state:=proc_state'\<rparr>" 

definition set_procs_to_normal :: "StateR \<Rightarrow> partition_id \<Rightarrow> StateR" where
  "set_procs_to_normal s part \<equiv> if is_a_partition sysconf part then
                                    let prs = proc_state s;
                                        proc_state' = (\<lambda>(pt, p). 
                                              (let pst = prs (pt,p) in
                                                if pt = part \<and> state (the pst) = WAITING 
                                                then Some ((the pst)\<lparr>state:=READY\<rparr>)
                                                else prs (pt,p))) in
                                     s\<lparr>proc_state := proc_state'\<rparr>
                                   else s"

definition set_partition_modeR :: "Sys_Config \<Rightarrow> StateR \<Rightarrow> partition_mode_type \<Rightarrow> StateR" where
  "set_partition_modeR sc s m \<equiv> 
      (if (partconf sc) (current s) \<noteq> None \<and> (partitions s) (current s) \<noteq> None \<and>
          \<not> (part_mode (the ((partitions s) (current s))) = COLD_START \<and> m = WARM_START) then
        let pts = partitions s;
            pstate = the (pts (current s));
            s' = (if m = NORMAL then 
                    set_procs_to_normal s (current s) 
                  else if part_mode (the ((partitions s) (current s))) = NORMAL then
                    remove_partition_resources s (current s) 
                  else s )
        in s'\<lparr>partitions := pts(current s' := Some (pstate\<lparr>part_mode := m\<rparr>))\<rparr>
      else
        s)"


definition transf_sampling_msgR :: "StateR \<Rightarrow> Channel_Type \<Rightarrow> StateR" where
  "transf_sampling_msgR s c \<equiv> 
          let s'= (transf_sampling_msg (\<Up>s) c) in (s\<Down>s')"

definition transf_queuing_msg_maylostR :: "Sys_Config \<Rightarrow> StateR \<Rightarrow> Channel_Type \<Rightarrow> StateR" where
  "transf_queuing_msg_maylostR sc s c \<equiv>
          let s'= (transf_queuing_msg_maylost sc (\<Up>s) c) in (s\<Down>s')"

definition create_process :: "StateR \<Rightarrow> proc_priority_type \<Rightarrow> (StateR \<times> process_id option)" where
  "create_process s pri \<equiv> if part_mode (the ((partitions s) (current s))) = WARM_START 
                            \<or> part_mode (the ((partitions s) (current s))) = COLD_START
                           then 
                            let pid = (SOME p. p \<notin> the ((procs s) (current s)));
                                procs' = (procs s) ((current s) := Some ((the ((procs s) (current s))) \<union> {pid}));
                                proc_state' = (proc_state s) ((current s,pid) := Some \<lparr>state = DORMANT, priority = pri\<rparr>) in
                            (s\<lparr>procs:=procs', proc_state:=proc_state'\<rparr>, Some pid)
                           else (s, None)"

definition set_process_priority :: "StateR \<Rightarrow> process_id \<Rightarrow> proc_priority_type \<Rightarrow> StateR" where
  "set_process_priority s p pri \<equiv> 
        if (proc_state s) (current s, p) \<noteq> None \<and> (state (the ((proc_state s) (current s, p)))) \<noteq> DORMANT then
            let st = state (the ((proc_state s) (current s, p)));
                proc_state' = (proc_state s) ((current s,p) := Some \<lparr>state = st, priority = pri\<rparr>) in
                s\<lparr>proc_state:=proc_state'\<rparr>
         else s"

definition start_process :: "StateR \<Rightarrow> process_id \<Rightarrow> StateR" where
  "start_process s p \<equiv> if p \<in> the ((procs s) (current s)) \<and> (proc_state s) (current s, p) \<noteq> None 
                        \<and> (state (the ((proc_state s) (current s, p)))) = DORMANT then
                          let st = (if part_mode (the ((partitions s) (current s))) = NORMAL
                                    then READY 
                                    else WAITING);
                              pst = (the ((proc_state s) (current s, p)));
                              proc_state' = (proc_state s) ((current s, p) := Some (pst \<lparr>state := st\<rparr>)) in
                                s\<lparr>proc_state:=proc_state'\<rparr>
                        else s"

definition stop_process :: "StateR \<Rightarrow> process_id \<Rightarrow> StateR" where 
  "stop_process s p \<equiv> if p \<in> the ((procs s) (current s)) \<and> (proc_state s) (current s, p) \<noteq> None 
                        \<and> (state (the ((proc_state s) (current s, p)))) \<noteq> DORMANT then
                         let pri = priority (the ((proc_state s) (current s, p)));
                             proc_state' = (proc_state s) ((current s, p) := Some \<lparr>state = DORMANT,priority = pri\<rparr>) in
                                s\<lparr>proc_state:=proc_state'\<rparr>
                       else s"

definition suspend_process :: "StateR \<Rightarrow> process_id \<Rightarrow> StateR" where 
  "suspend_process s p \<equiv> if p \<in> the ((procs s) (current s)) \<and> (proc_state s) (current s, p) \<noteq> None 
                           \<and> (state (the ((proc_state s) (current s, p)))) \<noteq> DORMANT
                           \<and> (state (the ((proc_state s) (current s, p)))) \<noteq> SUSPEND then
                           let pri = priority (the ((proc_state s) (current s, p)));
                             proc_state' = (proc_state s) ((current s, p) := Some \<lparr>state = SUSPEND,priority = pri\<rparr>) in
                                s\<lparr>proc_state:=proc_state'\<rparr>
                          else s"

definition resume_process :: "StateR \<Rightarrow> process_id \<Rightarrow> StateR" where 
  "resume_process s p \<equiv> if p \<in> the ((procs s) (current s)) \<and> (proc_state s) (current s, p) \<noteq> None 
                           \<and> (state (the ((proc_state s) (current s, p)))) = SUSPEND then
                           let pri = priority (the ((proc_state s) (current s, p)));
                               proc_state' = (proc_state s) ((current s, p) := Some \<lparr>state = READY,priority = pri\<rparr>) in
                                  s\<lparr>proc_state:=proc_state'\<rparr>
                          else s"

definition get_process_status :: "StateR \<Rightarrow> process_id \<Rightarrow> (StateR \<times> (Proc_State option))" where
  "get_process_status s p \<equiv> (s,(proc_state s) (current s, p))"



definition system_initR :: "Sys_Config \<Rightarrow> StateR"
  where "system_initR sc \<equiv> let s0 = system_init sc in 
                              \<lparr>current = current s0,
                                partitions = partitions s0,
                                comm = comm s0,
                                part_ports = part_ports s0,
                                procs = (\<lambda> x. None),
                                cur_proc_part = (\<lambda> x. None),
                                proc_state = (\<lambda> x. None)
                               \<rparr>"
declare abstract_state_def[cong del] and abstract_state_rev_def[cong del] and 
        create_sampling_portR_def [cong del] and write_sampling_messageR_def[cong del] and
        read_sampling_messageR_def[cong del] and get_sampling_port_idR_def[cong del] and
        get_sampling_port_statusR_def[cong del] and create_queuing_portR_def[cong del] and
        send_queuing_message_maylostR_def[cong del] and receive_queuing_messageR_def[cong del] and
        get_queuing_port_idR_def[cong del] and get_queuing_port_statusR_def[cong del] and
        clear_queuing_portR_def[cong del] and setRun2Ready_def[cong del] and schedule_process_def[cong del] and
        scheduleR_def[cong del] and get_partition_statusR_def[cong del] and remove_partition_resources_def[cong del] and
        set_procs_to_normal_def[cong del] and set_partition_modeR_def[cong] and transf_sampling_msgR_def[cong del] and
        transf_queuing_msg_maylostR_def[cong del] and create_process_def[cong] and set_process_priority_def[cong del] and
        start_process_def[cong del] and stop_process_def[cong] and suspend_process_def[cong del] and 
        resume_process_def[cong del]  and get_process_status_def[cong del] and set_partition_mode_def[cong del]

declare abstract_state_def[cong] and abstract_state_rev_def[cong] and 
        create_sampling_portR_def [cong] and write_sampling_messageR_def[cong] and
        read_sampling_messageR_def[cong] and get_sampling_port_idR_def[cong] and
        get_sampling_port_statusR_def[cong] and create_queuing_portR_def[cong] and
        send_queuing_message_maylostR_def[cong] and receive_queuing_messageR_def[cong] and
        get_queuing_port_idR_def[cong] and get_queuing_port_statusR_def[cong] and
        clear_queuing_portR_def[cong] and setRun2Ready_def[cong] and schedule_process_def[cong] and
        scheduleR_def[cong] and get_partition_statusR_def[cong] and remove_partition_resources_def[cong] and
        set_procs_to_normal_def[cong] and set_partition_modeR_def[cong] and transf_sampling_msgR_def[cong] and
        transf_queuing_msg_maylostR_def[cong] and create_process_def[cong] and set_process_priority_def[cong] and
        start_process_def[cong] and stop_process_def[cong] and suspend_process_def[cong] and 
        resume_process_def[cong] and get_process_status_def[cong] and set_partition_mode_def[cong] and schedule_def[cong]

subsection{* Instantiation and Its Proofs of Security Model  *}

consts s0r :: StateR

specification (s0r) 
  s0r_init: "s0r = system_initR sysconf"
  by simp

primrec event_enabledR :: "StateR \<Rightarrow> EventR \<Rightarrow> bool"
    where event_enabledR_hc: "event_enabledR s (hyperc' h) = (is_a_partition sysconf (current s) 
                                        \<and> part_mode (the (partitions s (current s))) \<noteq> IDLE)" |
          event_enabledR_sys: "event_enabledR s (sys' h) =  (case h of Schedule \<Rightarrow> True |
                                                 Transfer_Sampling_Message c \<Rightarrow> (current s = transmitter sysconf) |
                                                 Transfer_Queuing_Message c \<Rightarrow> (current s = transmitter sysconf) |
                                                 Schedule_Process \<Rightarrow> (is_a_partition sysconf (current s) 
                                                              \<and> part_mode (the (partitions s (current s))) = NORMAL))" 

definition exec_eventR :: "EventR \<Rightarrow> (StateR \<times> StateR) set" where
  "exec_eventR e = {(s,s'). s'\<in> (if event_enabledR s e then (
      case e of hyperc' (Create_Sampling_Port pname) \<Rightarrow> {fst (create_sampling_portR sysconf s pname)} |
                hyperc' (Write_Sampling_Message p m) \<Rightarrow> {fst (write_sampling_messageR s p m)} |
                hyperc' (Read_Sampling_Message p) \<Rightarrow> {fst (read_sampling_messageR s p)} |
                hyperc' (Get_Sampling_Portid pname) \<Rightarrow> {fst (get_sampling_port_idR sysconf s pname)} |
                hyperc' (Get_Sampling_Portstatus p) \<Rightarrow> {fst (get_sampling_port_statusR sysconf s p)} |
                hyperc' (Create_Queuing_Port pname) \<Rightarrow> {fst (create_queuing_portR sysconf s pname)} |
                hyperc' (Send_Queuing_Message p m) \<Rightarrow> {fst (send_queuing_message_maylostR sysconf s p m)} |
                hyperc' (Receive_Queuing_Message p) \<Rightarrow> {fst (receive_queuing_messageR s p)} |
                hyperc' (Get_Queuing_Portid pname) \<Rightarrow> {fst (get_queuing_port_idR sysconf s pname)} |
                hyperc' (Get_Queuing_Portstatus p) \<Rightarrow> {fst (get_queuing_port_statusR sysconf s p)} |
                hyperc' (Clear_Queuing_Port p) \<Rightarrow> {clear_queuing_portR s p} |
                hyperc' (Set_Partition_Mode m) \<Rightarrow> {set_partition_modeR sysconf s m} |
                hyperc' (Get_Partition_Status) \<Rightarrow> {fst (get_partition_statusR sysconf s)} |
                hyperc' (Create_Process pri) \<Rightarrow> {fst (create_process s pri)} |
                hyperc' (Start_Process p) \<Rightarrow> {start_process s p} |
                hyperc' (Stop_Process p) \<Rightarrow> {stop_process s p} |
                hyperc' (Resume_Process p) \<Rightarrow> {resume_process s p} |
                hyperc' (Suspend_Process p) \<Rightarrow> {suspend_process s p} |
                hyperc' (Set_Priority p pri) \<Rightarrow> {set_process_priority s p pri} |
                hyperc' (Get_Process_Status p) \<Rightarrow> {fst (get_process_status s p)} |
                sys' Schedule \<Rightarrow> scheduleR sysconf s |
                sys' (Transfer_Sampling_Message c) \<Rightarrow> {transf_sampling_msgR s c} |
                sys' (Transfer_Queuing_Message c) \<Rightarrow> {transf_queuing_msg_maylostR sysconf s c} |
                sys' (Schedule_Process) \<Rightarrow> schedule_process s )
                    else {s})}"

definition eR :: "EventR \<Rightarrow> Event option" where
  "eR e \<equiv> 
      case e of hyperc' (Create_Sampling_Port pname) \<Rightarrow> Some (hyperc (Hypercall.Create_Sampling_Port pname)) |
                hyperc' (Write_Sampling_Message p m) \<Rightarrow> Some (hyperc (Hypercall.Write_Sampling_Message p m)) |
                hyperc' (Read_Sampling_Message p) \<Rightarrow> Some (hyperc (Hypercall.Read_Sampling_Message p)) |
                hyperc' (Get_Sampling_Portid pname) \<Rightarrow> Some (hyperc (Hypercall.Get_Sampling_Portid pname)) |
                hyperc' (Get_Sampling_Portstatus p) \<Rightarrow> Some (hyperc (Hypercall.Get_Sampling_Portstatus p)) |
                hyperc' (Create_Queuing_Port pname) \<Rightarrow> Some (hyperc (Hypercall.Create_Queuing_Port pname)) |
                hyperc' (Send_Queuing_Message p m) \<Rightarrow> Some (hyperc (Hypercall.Send_Queuing_Message p m)) |
                hyperc' (Receive_Queuing_Message p) \<Rightarrow> Some (hyperc (Hypercall.Receive_Queuing_Message p)) |
                hyperc' (Get_Queuing_Portid pname) \<Rightarrow> Some (hyperc (Hypercall.Get_Queuing_Portid pname)) |
                hyperc' (Get_Queuing_Portstatus p) \<Rightarrow> Some (hyperc (Hypercall.Get_Queuing_Portstatus p)) |
                hyperc' (Clear_Queuing_Port p) \<Rightarrow> Some (hyperc (Hypercall.Clear_Queuing_Port p)) |
                hyperc' (Set_Partition_Mode m) \<Rightarrow> Some (hyperc (Hypercall.Set_Partition_Mode m)) |
                hyperc' (Get_Partition_Status) \<Rightarrow> Some (hyperc (Hypercall.Get_Partition_Status)) |
                hyperc' (Create_Process pri) \<Rightarrow> None |
                hyperc' (Start_Process p) \<Rightarrow> None |
                hyperc' (Stop_Process p) \<Rightarrow> None |
                hyperc' (Resume_Process p) \<Rightarrow> None |
                hyperc' (Suspend_Process p) \<Rightarrow> None |
                hyperc' (Set_Priority p pri) \<Rightarrow> None |
                hyperc' (Get_Process_Status p) \<Rightarrow> None |
                sys' Schedule \<Rightarrow>  Some (sys (System_Event.Schedule)) |
                sys' (Transfer_Sampling_Message c) \<Rightarrow> Some (sys (System_Event.Transfer_Sampling_Message c)) |
                sys' (Transfer_Queuing_Message c) \<Rightarrow> Some (sys (System_Event.Transfer_Queuing_Message c)) |
                sys' (Schedule_Process) \<Rightarrow> None "

primrec domain_of_eventR :: "StateR \<Rightarrow> EventR \<Rightarrow> domain_id option"
  where domain_of_eventR_hc: "domain_of_eventR s (hyperc' h) = Some (current s)" |
        domain_of_eventR_sys: "domain_of_eventR s (sys' h) =  (case h of Schedule \<Rightarrow> Some (scheduler sysconf) |
                                                 Transfer_Sampling_Message c \<Rightarrow> Some (transmitter sysconf) |
                                                 Transfer_Queuing_Message c \<Rightarrow> Some (transmitter sysconf) |
                                                 Schedule_Process \<Rightarrow> Some (current s) )" 

lemma domain_domainR : "eR e \<noteq> None \<Longrightarrow> domain_of_eventR s e = domain_of_event (\<Up>s) (the (eR e))"
  proof(induct e)
    case (hyperc' x) then show ?case
      proof(induct x) qed(simp add:eR_def)+          
  next
    case (sys' x) then show ?case 
      proof(induct x) qed(simp add:eR_def)+
  qed
    
definition vpeq_part_procs :: "StateR \<Rightarrow> domain_id \<Rightarrow> StateR \<Rightarrow> bool" ("(_ \<sim>. _ .\<sim>\<^sub>\<Delta> _)")
  where "vpeq_part_procs s d t \<equiv> if is_a_partition sysconf d then 
                                      ((procs s) d = (procs t) d) \<and>
                                      (\<forall>p. (proc_state s) (d,p) = (proc_state t) (d,p)) \<and>
                                      (cur_proc_part s) d = (cur_proc_part t) d 
                                  else True" 

lemma vpeq_part_procs_transitive_lemma : 
  "\<forall> s t r d. (vpeq_part_procs s d t) \<and> (vpeq_part_procs t d r) \<longrightarrow> (vpeq_part_procs s d r)"
  using vpeq_part_procs_def by auto
  
lemma vpeq_part_procs_symmetric_lemma : "\<forall> s t d. (vpeq_part_procs s d t) \<longrightarrow> (vpeq_part_procs t d s)"
  using vpeq_part_procs_def by auto

lemma vpeq_part_procs_reflexive_lemma : "\<forall> s d. (vpeq_part_procs s d s)"
  using vpeq_part_procs_def by auto

definition vpeqR :: "StateR \<Rightarrow> domain_id \<Rightarrow> StateR \<Rightarrow> bool" ("(_ \<sim>. _ .\<sim> _)")
  where "vpeqR s d t \<equiv>  ((\<Up>s) \<sim>d\<sim> (\<Up>t)) \<and> (s\<sim>.d.\<sim>\<^sub>\<Delta>t)"

declare vpeqR_def[cong] and vpeq_part_procs_def[cong]

lemma vpeqR_transitive_lemma : "\<forall> s t r d. (vpeqR s d t) \<and> (vpeqR t d r) \<longrightarrow> (vpeqR s d r)"
    apply(clarsimp cong del: vpeq1_def)
    using vpeq1_transitive_lemma vpeq_part_procs_transitive_lemma by blast

lemma vpeqR_symmetric_lemma : "\<forall> s t d. (vpeqR s d t) \<longrightarrow> (vpeqR t d s)"
  apply(clarsimp cong del: vpeq1_def)
  using vpeq1_symmetric_lemma vpeq_part_procs_symmetric_lemma by blast

lemma vpeqR_reflexive_lemma : "\<forall> s d. (vpeqR s d s)"  
  using vpeq1_reflexive_lemma vpeq_part_procs_reflexive_lemma by auto

lemma vpeqR_vpeq1 : "vpeqR s d t \<Longrightarrow> vpeq1 (\<Up>s) d (\<Up>t)"
  by fastforce

lemma sched_currentR_lemma : 
  "\<forall>s t a. vpeqR s (scheduler sysconf) t \<longrightarrow> (domain_of_eventR s a) = (domain_of_eventR t a)"  
    using vpeqR_def vpeq1_def abstract_state_def vpeq_sched_def 
    by (metis (no_types, lifting) EventR.exhaust State.select_convs(1) domain_of_eventR.simps) 

lemma scheproc_hasnexts: "schedule_process s \<noteq> {}"
  apply(case_tac "is_a_partition sysconf (current s) \<and> part_mode (the ((partitions s) (current s))) = NORMAL")    
  by auto
  
lemma reachable_l2: "\<forall>s a. (SM.reachable0 s0r exec_eventR) s \<longrightarrow> (\<exists>s'. (s, s') \<in> exec_eventR a)"
  proof -
  {
    fix s a
    assume p0: "(SM.reachable0 s0r exec_eventR) s"
    have "\<exists>s'. (s, s') \<in> exec_eventR a"
      proof(induct a)
        case (hyperc' x) show ?case 
          proof(induct x) qed(auto simp add:exec_eventR_def)
        next
        case (sys' x) then show ?case
          proof(induct x) 
            case (Schedule) show ?case using exec_eventR_def  by fastforce
            case (Transfer_Sampling_Message c) show ?case  using exec_eventR_def  by fastforce
            case (Transfer_Queuing_Message c) show ?case  using exec_eventR_def  by fastforce
            case (Schedule_Process) show ?case using exec_eventR_def scheproc_hasnexts by fastforce
          qed
      qed        
  }
  then show ?thesis by auto
  qed


interpretation SM_enabled 
    s0r exec_eventR domain_of_eventR "scheduler sysconf" vpeqR interference1
  using vpeqR_transitive_lemma vpeqR_symmetric_lemma vpeqR_reflexive_lemma sched_currentR_lemma
        schedeler_intf_all_help no_intf_sched_help reachable_l2 nintf_reflx
        SM.intro[of vpeqR "scheduler sysconf" domain_of_eventR interference1]
        SM_enabled_axioms.intro [of s0r exec_eventR]
        SM_enabled.intro[of domain_of_eventR "scheduler sysconf" vpeqR interference1 s0r exec_eventR] by blast

subsection{* Unwinding conditions on new state variables *}
  definition weak_step_consistent_new :: "bool" where
    "weak_step_consistent_new \<equiv> \<forall>a d s t. reachable0 s \<and> reachable0 t \<and> (s \<sim>. d .\<sim> t) \<and> (s \<sim>. (scheduler sysconf) .\<sim> t) \<and> 
                            ((the (domain_of_eventR s a)) \<leadsto> d) \<and> (s \<sim>. (the (domain_of_eventR s a)) .\<sim> t) \<longrightarrow>
                            (\<forall> s' t'. (s,s') \<in> exec_eventR a \<and> (t,t') \<in> exec_eventR a \<longrightarrow> (s' \<sim>.d.\<sim>\<^sub>\<Delta> t'))"

  definition step_consistent_new :: "bool" where
    "step_consistent_new \<equiv> \<forall>a d s t. reachable0 s \<and> reachable0 t \<and> (s \<sim>. d .\<sim> t) \<and> (s \<sim>. (scheduler sysconf) .\<sim> t) \<and> 
                            ((the (domain_of_eventR s a)) \<leadsto> d) \<longrightarrow> (s \<sim>. (the (domain_of_eventR s a)) .\<sim> t) \<longrightarrow>
                            (\<forall> s' t'. (s,s') \<in> exec_eventR a \<and> (t,t') \<in> exec_eventR a \<longrightarrow> (s' \<sim>.d.\<sim>\<^sub>\<Delta> t'))"

  definition local_respect_new :: "bool" where
    "local_respect_new \<equiv> \<forall> a d s s'. reachable0 s \<and> ((the (domain_of_eventR s a)) \<setminus>\<leadsto> d) \<and> (s,s')\<in>exec_eventR a 
                                    \<longrightarrow> (s \<sim>. d .\<sim>\<^sub>\<Delta> s')"

  definition weak_step_consistent_new_e :: "EventR \<Rightarrow> bool" where
    "weak_step_consistent_new_e a \<equiv> \<forall>d s t. reachable0 s \<and> reachable0 t \<and> (s \<sim>. d .\<sim> t) \<and> (s \<sim>. (scheduler sysconf) .\<sim> t) \<and> 
                            ((the (domain_of_eventR s a)) \<leadsto> d) \<and> (s \<sim>. (the (domain_of_eventR s a)) .\<sim> t) \<longrightarrow>
                            (\<forall> s' t'. (s,s') \<in> exec_eventR a \<and> (t,t') \<in> exec_eventR a \<longrightarrow> (s' \<sim>.d.\<sim>\<^sub>\<Delta> t'))"

  definition step_consistent_new_e :: "EventR \<Rightarrow> bool" where
    "step_consistent_new_e a \<equiv> \<forall>d s t. reachable0 s \<and> reachable0 t \<and> (s \<sim>. d .\<sim> t) \<and> (s \<sim>. (scheduler sysconf) .\<sim> t) \<and> 
                            ((the (domain_of_eventR s a)) \<leadsto> d) \<longrightarrow> (s \<sim>. (the (domain_of_eventR s a)) .\<sim> t) \<longrightarrow>
                            (\<forall> s' t'. (s,s') \<in> exec_eventR a \<and> (t,t') \<in> exec_eventR a \<longrightarrow> (s' \<sim>.d.\<sim>\<^sub>\<Delta> t'))"

  definition local_respect_new_e :: "EventR \<Rightarrow> bool" where
    "local_respect_new_e a \<equiv> \<forall>d s s'. reachable0 s \<and> ((the (domain_of_eventR s a)) \<setminus>\<leadsto> d) \<and> (s,s')\<in>exec_eventR a 
                                    \<longrightarrow> (s \<sim>. d .\<sim>\<^sub>\<Delta> s')"

declare weak_step_consistent_new_def[cong del] and step_consistent_new_def[cong del] and local_respect_new_def[cong del] and
        weak_step_consistent_new_e_def[cong del] and step_consistent_new_e_def[cong del] and local_respect_new_e_def[cong del] 

declare weak_step_consistent_new_def[cong] and step_consistent_new_def[cong] and local_respect_new_def[cong] and
        weak_step_consistent_new_e_def[cong] and step_consistent_new_e_def[cong] and local_respect_new_e_def[cong] 

declare weak_step_consistent_new_def[cong del] and step_consistent_new_def[cong del] and local_respect_new_def[cong del] and
        weak_step_consistent_new_e_def[cong del] and step_consistent_new_e_def[cong del] and local_respect_new_e_def[cong del]

  lemma weak_step_consistent_new_all_evt : "weak_step_consistent_new = (\<forall>a. weak_step_consistent_new_e a)"
    by (simp add:weak_step_consistent_new_def weak_step_consistent_new_e_def)

  lemma step_consistent_new_all_evt : "step_consistent_new = (\<forall>a. step_consistent_new_e a)"
    by (simp add:step_consistent_new_def step_consistent_new_e_def)

  lemma local_respect_new_all_evt : "local_respect_new = (\<forall>a. local_respect_new_e a)"
    by (simp add:local_respect_new_def local_respect_new_e_def)

subsection{* Proofs of refinement *}

subsubsection{* Refinement of existing events at upper level *}

  lemma create_sampling_port_ref_lemma: 
    "\<forall>s. fst (create_sampling_port sc (\<Up>s) p) = \<Up>(fst (create_sampling_portR sc s p))"
    by auto

  lemma write_sampling_message_ref_lemma: 
    "\<forall>s. fst (write_sampling_message (\<Up>s) p m) = \<Up>(fst (write_sampling_messageR s p m))"
    by simp
  
  lemma read_sampling_message_ref_lemma: 
    "\<forall>s. fst (read_sampling_message (\<Up>s) p) = \<Up>(fst (read_sampling_messageR s p))"
    by simp

  lemma get_sampling_port_id_ref_lemma: 
    "\<forall>s. fst (get_sampling_port_id sc (\<Up>s) p) = \<Up>(fst (get_sampling_port_idR sc s p))"
    by simp

  lemma get_sampling_port_status_ref_lemma: 
    "\<forall>s. fst (get_sampling_port_status sc (\<Up>s) p) = \<Up>(fst (get_sampling_port_statusR sc s p))"
    by simp
  
  lemma create_queuing_port_ref_lemma: 
    "\<forall>s. fst (create_queuing_port sc (\<Up>s) p) = \<Up>(fst (create_queuing_portR sc s p))"
    by auto 

  lemma send_queuing_message_maylost_ref_lemma: 
    "\<forall>s. fst (send_queuing_message_maylost sc (\<Up>s) p m) = \<Up>(fst (send_queuing_message_maylostR sc s p m))"
    by simp 

  lemma receive_queuing_message_ref_lemma: 
    "\<forall>s. fst (receive_queuing_message (\<Up>s) p) = \<Up>(fst (receive_queuing_messageR s p))"
      by auto

  lemma get_queuing_port_id_ref_lemma: 
    "\<forall>s. fst (get_queuing_port_id sc (\<Up>s) p) = \<Up>(fst (get_queuing_port_idR sc s p))"
      by auto

  lemma get_queuing_port_status_ref_lemma: 
    "\<forall>s. fst (get_queuing_port_status sc (\<Up>s) p) = \<Up>(fst (get_queuing_port_statusR sc s p))"
      by auto

  lemma clear_queuing_port_ref_lemma: 
    "\<forall>s. clear_queuing_port (\<Up>s) p = \<Up>(clear_queuing_portR s p)"
      by auto

  lemma schedule_ref_lemma: "\<forall>s s'. (s' \<in> scheduleR sc s) \<longrightarrow> (\<Up>s') \<in> (schedule sc (\<Up>s))"
     by auto

  lemma get_partition_status_ref_lemma: 
    "\<forall>s. fst (get_partition_status sc (\<Up>s)) = \<Up>(fst (get_partition_statusR sc s))"
     by simp

  lemma set_partition_mode_ref_lemma: "\<forall>s. set_partition_mode sc (\<Up>s) m = \<Up>(set_partition_modeR sc s m)"
    proof -
    {
      fix s
      let ?s' = "set_partition_modeR sc s m"
      let ?us' = "\<Up>(?s')"
      let ?t = "\<Up>s"
      let ?t' = "set_partition_mode sc ?t m"
      have a0: "current ?t' = current ?us'" 
        using set_partition_mode_def 
          by auto
      moreover
      have "partitions ?t' = partitions ?us'"
        proof -
          have b0: "partitions s = partitions ?t \<and> current s = current ?t"
            by simp
          {
            fix p
            have "partitions ?t' p = partitions ?us' p"
              proof(cases "(partconf sc) (current s) \<noteq> None \<and> (partitions s) (current s) \<noteq> None \<and>
                    \<not> (part_mode (the ((partitions s) (current s))) = COLD_START \<and> m = WARM_START)")
                assume c0: "(partconf sc) (current s) \<noteq> None \<and> (partitions s) (current s) \<noteq> None \<and>
                    \<not> (part_mode (the ((partitions s) (current s))) = COLD_START \<and> m = WARM_START)"
                with b0 have c1: "(partconf sc) (current ?t) \<noteq> None \<and> (partitions ?t) (current ?t) \<noteq> None \<and>
                    \<not> (part_mode (the ((partitions ?t) (current ?t))) = COLD_START \<and> m = WARM_START)"
                  by simp
                show ?thesis 
                  proof(cases "current ?t = p")
                    assume d0: "current ?t = p"                      
                    with c1 have "partitions ?t' p = Some ((the (partitions ?t p)) \<lparr>part_mode := m\<rparr>)" 
                      by auto 
                    moreover
                    from b0 c0 d0 have "partitions ?s' p = Some ((the (partitions s p)) \<lparr>part_mode := m\<rparr>)"
                      by auto
                    ultimately show ?thesis by (auto cong del: set_partition_mode_def)
                  next
                    assume d0: "current ?t \<noteq> p"                    
                    with c1 have "partitions ?t' p = partitions ?t p" 
                      by auto 
                    moreover
                    from b0 c0 d0 have "partitions ?s' p = partitions s p"
                       by auto 
                    ultimately show ?thesis by auto
                  qed
              next
                assume c0: "\<not> ((partconf sc) (current s) \<noteq> None \<and> (partitions s) (current s) \<noteq> None \<and>
                    \<not> (part_mode (the ((partitions s) (current s))) = COLD_START \<and> m = WARM_START))"
                thus ?thesis  by auto
              qed                  
          }
          then show ?thesis by auto
      qed
      thus ?thesis  by auto
    } qed



  lemma transf_sampling_msg_ref_lemma: "\<forall>s. transf_sampling_msg (\<Up>s) c = \<Up>(transf_sampling_msgR s c)"
    by auto

  lemma transf_queuing_msg_maylost_ref_lemma: 
    "\<forall>s. transf_queuing_msg_maylost sc (\<Up>s) c = \<Up>(transf_queuing_msg_maylostR sc s c)"
      by auto

subsubsection{* new events introduced at this level dont change abstract state *}
  lemma setrun2ready_nchastate_lemma: 
    "s' = setRun2Ready s \<Longrightarrow> (\<Up>s) = (\<Up>s')" 
    by auto

  lemma schedule_process_nchastate_lemma: 
    "\<forall>s'\<in>(schedule_process s). (\<Up>s) = (\<Up>s')" 
     proof -
     {
       fix s'
       assume p0: "s'\<in>(schedule_process s)"
       
       let ?s' = "setRun2Ready s"
        let ?readyprs = "{p. p\<in>the (procs ?s' (current ?s')) \<and> 
                                state (the (proc_state ?s' (current ?s',p))) = READY}"
        have "(\<Up>s) = (\<Up>s')"
          proof(cases "is_a_partition sysconf (current s)  \<and> part_mode (the ((partitions s) (current s))) = NORMAL")
            assume a0: "is_a_partition sysconf (current s)  \<and> part_mode (the ((partitions s) (current s))) = NORMAL"
            let ?s' = "setRun2Ready s"
            have b2: "(\<Up>s) = (\<Up>?s')" using setrun2ready_nchastate_lemma by blast
            have b3: "(\<Up>?s') = (\<Up>s')" using  a0 p0 by auto               
            with b2 show ?thesis by (auto cong del: abstract_state_def setRun2Ready_def)
        next
          assume a0: "\<not> (is_a_partition sysconf (current s)  \<and> part_mode (the ((partitions s) (current s))) = NORMAL)"
          then show ?thesis using p0 by auto
        qed
    }
    then show ?thesis  by (auto cong del: abstract_state_def )
    qed


  lemma create_process_nchastate_lemma: 
    "\<forall>s. (\<Up>s) = \<Up>(fst (create_process s pri))" 
     by auto

  lemma set_process_priority_nchastate_lemma: 
    "\<forall>s. (\<Up>s) = \<Up>(set_process_priority s p pri)" 
      by auto

  lemma start_process_nchastate_lemma: 
    "\<forall>s. (\<Up>s) = \<Up>(start_process s p)" 
      by auto

  lemma stop_process_nchastate_lemma: 
    "\<forall>s. (\<Up>s) = \<Up>(stop_process s p)" 
      by auto

  lemma suspend_process_nchastate_lemma: 
    "\<forall>s. (\<Up>s) = \<Up>(suspend_process s p)" 
      by auto
  
  lemma resume_process_nchastate_lemma: 
    "\<forall>s. (\<Up>s) = \<Up>(resume_process s p)" 
     by auto

  lemma get_process_status_nchastate_lemma: 
    "\<forall>s. (\<Up>s) = \<Up>(fst (get_process_status s p))" 
     by auto

subsubsection{* proof of refinement *}
  
  lemma s0_ref_lemma : "(\<Up>s0r) = s0t" 
     by (simp add:  s0t_init s0r_init system_initR_def ) 

  lemma refine_exec_event : "(s,t)\<in>exec_eventR e \<Longrightarrow> (eR e = None \<longrightarrow> (\<Up>s) = (\<Up>t)) 
    \<and> (eR e \<noteq> None \<longrightarrow> (\<Up>s,\<Up>t)\<in>exec_event (the (eR e)))"
    proof -
      assume p0: "(s,t)\<in>exec_eventR e"
      then show "(eR e = None \<longrightarrow> (\<Up>s) = (\<Up>t)) \<and> (eR e \<noteq> None \<longrightarrow> (\<Up>s,\<Up>t)\<in>exec_event (the (eR e)))"
      proof(induct e)
        case (hyperc' x) then show ?case
          proof(induct x)
            case (Create_Sampling_Port y) 
              let ?e = "Hypercall.Create_Sampling_Port y"
              let ?er = "Create_Sampling_Port y"
              have "event_enabledR s (hyperc' ?er) = event_enabled (\<Up>s) (hyperc ?e)"
                 by auto
              then have "((\<Up>s),(\<Up>t)) \<in> exec_event (hyperc ?e)" 
                  using create_sampling_port_ref_lemma exec_eventR_def exec_event_def 
                  Create_Sampling_Port.prems  
                  by (auto cong del: abstract_state_def)
              then show ?case using eR_def by auto
          next
            case (Write_Sampling_Message x1 y)
              let ?e = "Hypercall.Write_Sampling_Message x1 y"
              let ?er = "Write_Sampling_Message x1 y"
              have "event_enabledR s (hyperc' ?er) = event_enabled (\<Up>s) (hyperc ?e)"
                using event_enabled_def abstract_state_def by auto
              then have "((\<Up>s),(\<Up>t)) \<in> exec_event (hyperc ?e)" 
                  using write_sampling_message_ref_lemma exec_eventR_def exec_event_def 
                     Write_Sampling_Message.prems
                   by (auto cong del: abstract_state_def) 
              then show ?case using eR_def by auto
          next
            case (Read_Sampling_Message y)
              let ?e = "Hypercall.Read_Sampling_Message y"
              let ?er = "Read_Sampling_Message y"
              have "event_enabledR s (hyperc' ?er) = event_enabled (\<Up>s) (hyperc ?e)"
                using event_enabled_def abstract_state_def by auto
              then have "((\<Up>s),(\<Up>t)) \<in> exec_event (hyperc ?e)" 
                  using read_sampling_message_ref_lemma exec_eventR_def exec_event_def 
                     Read_Sampling_Message.prems by (auto cong del: abstract_state_def)
              then show ?case using eR_def by auto
          next
            case (Get_Sampling_Portid y)
              let ?e = "Hypercall.Get_Sampling_Portid y"
              let ?er = "Get_Sampling_Portid y"
              have "event_enabledR s (hyperc' ?er) = event_enabled (\<Up>s) (hyperc ?e)"
                using event_enabled_def abstract_state_def by auto
              then have "((\<Up>s),(\<Up>t)) \<in> exec_event (hyperc ?e)" 
                  using get_sampling_port_id_ref_lemma exec_eventR_def exec_event_def 
                     Get_Sampling_Portid by (auto cong del: abstract_state_def) 
              then show ?case using eR_def by auto
          next
            case (Get_Sampling_Portstatus y)
              let ?e = "Hypercall.Get_Sampling_Portstatus y"
              let ?er = "Get_Sampling_Portstatus y"
              have "event_enabledR s (hyperc' ?er) = event_enabled (\<Up>s) (hyperc ?e)"
                using event_enabled_def abstract_state_def by auto
              then have "((\<Up>s),(\<Up>t)) \<in> exec_event (hyperc ?e)" 
                  using get_sampling_port_status_ref_lemma exec_eventR_def exec_event_def 
                     Get_Sampling_Portstatus.prems by (auto cong del: abstract_state_def)
              then show ?case using eR_def by auto
          next
            case (Create_Queuing_Port y)
              let ?e = "Hypercall.Create_Queuing_Port y"
              let ?er = "Create_Queuing_Port y"
              have "event_enabledR s (hyperc' ?er) = event_enabled (\<Up>s) (hyperc ?e)"
                using event_enabled_def abstract_state_def by auto
              then have "((\<Up>s),(\<Up>t)) \<in> exec_event (hyperc ?e)" 
                  using create_queuing_port_ref_lemma exec_eventR_def exec_event_def 
                     Create_Queuing_Port.prems by (auto cong del: abstract_state_def)
              then show ?case using eR_def by auto
          next
            case (Send_Queuing_Message x1 y1)
              let ?e = "Hypercall.Send_Queuing_Message x1 y1"
              let ?er = "Send_Queuing_Message x1 y1"
              have "event_enabledR s (hyperc' ?er) = event_enabled (\<Up>s) (hyperc ?e)"
                using event_enabled_def abstract_state_def by auto
              then have "((\<Up>s),(\<Up>t)) \<in> exec_event (hyperc ?e)" 
                  using send_queuing_message_maylost_ref_lemma exec_eventR_def exec_event_def 
                     Send_Queuing_Message.prems by (auto cong del: abstract_state_def)
              then show ?case using eR_def by auto
          next
             case (Receive_Queuing_Message x1)
              let ?e = "Hypercall.Receive_Queuing_Message x1"
              let ?er = "Receive_Queuing_Message x1"
              have "event_enabledR s (hyperc' ?er) = event_enabled (\<Up>s) (hyperc ?e)"
                using event_enabled_def abstract_state_def by auto
              then have "((\<Up>s),(\<Up>t)) \<in> exec_event (hyperc ?e)" 
                  using receive_queuing_message_ref_lemma exec_eventR_def exec_event_def 
                     Receive_Queuing_Message.prems by (auto cong del: abstract_state_def)
              then show ?case using eR_def by auto
          next
            case (Get_Queuing_Portid x1)
              let ?e = "Hypercall.Get_Queuing_Portid x1"
              let ?er = "Get_Queuing_Portid x1"
              have "event_enabledR s (hyperc' ?er) = event_enabled (\<Up>s) (hyperc ?e)"
                using event_enabled_def abstract_state_def by auto
              then have "((\<Up>s),(\<Up>t)) \<in> exec_event (hyperc ?e)" 
                  using get_queuing_port_id_ref_lemma exec_eventR_def exec_event_def 
                     Get_Queuing_Portid.prems by (auto cong del: abstract_state_def) 
              then show ?case using eR_def by auto
          next
            case (Get_Queuing_Portstatus x1)
              let ?e = "Hypercall.Get_Queuing_Portstatus x1"
              let ?er = "Get_Queuing_Portstatus x1"
              have "event_enabledR s (hyperc' ?er) = event_enabled (\<Up>s) (hyperc ?e)"
                using event_enabled_def abstract_state_def by auto
              then have "((\<Up>s),(\<Up>t)) \<in> exec_event (hyperc ?e)" 
                  using get_queuing_port_status_ref_lemma exec_eventR_def exec_event_def 
                     Get_Queuing_Portstatus.prems by (auto cong del: abstract_state_def) 
              then show ?case using eR_def by auto
          next
            case (Clear_Queuing_Port x1)
              let ?e = "Hypercall.Clear_Queuing_Port x1"
              let ?er = "Clear_Queuing_Port x1"
              have "event_enabledR s (hyperc' ?er) = event_enabled (\<Up>s) (hyperc ?e)"
                using event_enabled_def abstract_state_def by auto
              then have "((\<Up>s),(\<Up>t)) \<in> exec_event (hyperc ?e)" 
                  using clear_queuing_port_ref_lemma exec_eventR_def exec_event_def 
                     Clear_Queuing_Port.prems by (auto cong del: abstract_state_def)
              then show ?case using eR_def by auto
          next
            case (Set_Partition_Mode x1)
              let ?e = "Hypercall.Set_Partition_Mode x1"
              let ?er = "Set_Partition_Mode x1"
              have "event_enabledR s (hyperc' ?er) = event_enabled (\<Up>s) (hyperc ?e)"
                using event_enabled_def abstract_state_def by auto
              then have "((\<Up>s),(\<Up>t)) \<in> exec_event (hyperc ?e)" 
                  using set_partition_mode_ref_lemma exec_eventR_def exec_event_def 
                     Set_Partition_Mode.prems 
                     by (auto cong del: set_partition_modeR_def 
                              abstract_state_def event_enabledR_def 
                               event_enabled_def set_partition_mode_def)
              then show ?case using eR_def by auto
          next
            case (Get_Partition_Status)
              let ?e = "Hypercall.Get_Partition_Status"
              let ?er = "Get_Partition_Status"
              have "event_enabledR s (hyperc' ?er) = event_enabled (\<Up>s) (hyperc ?e)"
                using event_enabled_def abstract_state_def by auto
              then have "((\<Up>s),(\<Up>t)) \<in> exec_event (hyperc ?e)" 
                  using get_partition_status_ref_lemma exec_eventR_def exec_event_def 
                     Get_Partition_Status.prems by (auto cong del: abstract_state_def) 
              then show ?case using eR_def by auto
          next
            case (Create_Process x1) 
              let ?er = "Create_Process x1"
              show ?case using eR_def exec_eventR_def Create_Process.prems create_process_nchastate_lemma                  
                by (metis (no_types, lifting) EventR.simps(5) Hypercall'.simps(413) 
                    mem_Collect_eq old.prod.case singletonD)
          next
            case (Start_Process x1)
              let ?er = "Start_Process x1"
              show ?case using eR_def exec_eventR_def Start_Process.prems start_process_nchastate_lemma
                by (metis (no_types, lifting) EventR.simps(5) Hypercall'.simps(414) 
                    mem_Collect_eq old.prod.case singletonD)
          next
            case (Stop_Process x1)
              let ?er = "Stop_Process x1"
              show ?case using eR_def exec_eventR_def Stop_Process.prems stop_process_nchastate_lemma
                by (metis (no_types, lifting) EventR.simps(5) Hypercall'.simps(415) 
                    mem_Collect_eq old.prod.case singletonD)
          next
            case (Resume_Process x1)
              let ?er = "Resume_Process x1"
              show ?case using eR_def exec_eventR_def Resume_Process.prems resume_process_nchastate_lemma
                by (metis (no_types, lifting) EventR.simps(5) Hypercall'.simps(416) 
                    mem_Collect_eq old.prod.case singletonD)
          next
            case (Suspend_Process x1)
              let ?er = "Suspend_Process x1"
              show ?case using eR_def exec_eventR_def Suspend_Process.prems suspend_process_nchastate_lemma
                by (metis (no_types, lifting) EventR.simps(5) Hypercall'.simps(417) 
                    mem_Collect_eq old.prod.case singletonD)
          next
            case (Set_Priority x1 y1)
              let ?er = "Set_Priority x1 y1"
              show ?case using eR_def exec_eventR_def Set_Priority.prems set_process_priority_nchastate_lemma
                by (metis (no_types, lifting) EventR.simps(5) Hypercall'.simps(418) 
                    mem_Collect_eq old.prod.case singletonD)
          next
            case (Get_Process_Status x1)
              let ?er = "Get_Process_Status x1"
              show ?case using eR_def exec_eventR_def Get_Process_Status.prems get_process_status_nchastate_lemma
                by (metis (no_types, lifting) EventR.simps(5) Hypercall'.simps(419) 
                    mem_Collect_eq old.prod.case singletonD)
          qed
      next
        case (sys' x) then show ?case 
          proof(induct x)
            case (Schedule)
              let ?e = "System_Event.Schedule"
              let ?er = "Schedule"
              have "event_enabledR s (sys' ?er) = event_enabled (\<Up>s) (sys ?e)"
                by auto
              then have "((\<Up>s),(\<Up>t)) \<in> exec_event (sys ?e)" 
                  using schedule_ref_lemma exec_eventR_def exec_event_def 
                     Schedule.prems by (auto cong del:  scheduleR_def) 
              then show ?case using eR_def by auto
          next
            case (Transfer_Sampling_Message x1)
              let ?e = "System_Event.Transfer_Sampling_Message x1"
              let ?er = "Transfer_Sampling_Message x1"
              have "event_enabledR s (sys' ?er) = event_enabled (\<Up>s) (sys ?e)"
                 by auto
              then have "((\<Up>s),(\<Up>t)) \<in> exec_event (sys ?e)" 
                  using transf_sampling_msg_ref_lemma exec_eventR_def exec_event_def 
                     Transfer_Sampling_Message.prems by auto 
              then show ?case using eR_def by auto
          next
            case (Transfer_Queuing_Message x1)
              let ?e = "System_Event.Transfer_Queuing_Message x1"
              let ?er = "Transfer_Queuing_Message x1"
              have "event_enabledR s (sys' ?er) = event_enabled (\<Up>s) (sys ?e)"
                 by auto
              then have "((\<Up>s),(\<Up>t)) \<in> exec_event (sys ?e)" 
                  using transf_queuing_msg_maylost_ref_lemma exec_eventR_def exec_event_def 
                     Transfer_Queuing_Message.prems  by auto 
              then show ?case using eR_def by auto
          next
            case (Schedule_Process)
              let ?er = "Schedule_Process"
              show ?case using eR_def exec_eventR_def Schedule_Process.prems schedule_process_nchastate_lemma
                by (metis (no_types, lifting) EventR.simps(6) System_EventR.simps(18) 
                   prod.simps(2) mem_Collect_eq singletonD) 
        qed
      qed
  qed

  lemma reachR_reach1: 
     "\<forall>s as s'. SK_TopSpec.reachable0 (\<Up>s) \<and> 
                 reachable0 s \<and> s'\<in>execute as s  \<longrightarrow> 
                SK_TopSpec.reachable0 (\<Up>s')"
  proof -
  {
    fix as
    have "\<forall>s s'. SK_TopSpec.reachable0 (\<Up>s) \<and> reachable0 s \<and> s'\<in>execute as s
                        \<longrightarrow> SK_TopSpec.reachable0 (\<Up>s')"
    proof(induct as)
      case Nil show ?case using execute_def by fastforce
    next
      case (Cons b bs)
      assume a0: "\<forall>s s'. SK_TopSpec.reachable0 (\<Up>s) \<and> reachable0 s \<and> s'\<in>execute bs s
                      \<longrightarrow> SK_TopSpec.reachable0 (\<Up>s')"
      show ?case 
      proof -
      {
        fix s s'
        assume b0: "SK_TopSpec.reachable0 (\<Up>s) \<and> reachable0 s \<and> s'\<in>execute (b # bs) s"
        have b2: "current s = current (\<Up>s) \<and> partitions s = partitions (\<Up>s)" by (simp add:abstract_state_def)
        have b3: "\<forall>s1. (s,s1)\<in>exec_eventR b \<longrightarrow> SK_TopSpec.reachable0 (\<Up>s1)"
        proof -
        {
          fix s1
          assume c0: "(s,s1)\<in>exec_eventR b"
          then have "SK_TopSpec.reachable0 (\<Up>s1)"
            using SK_TopSpec.reachableStep b0 refine_exec_event by metis 
        }
        then show ?thesis by auto
        qed
        from b0 have "\<exists>s1. (s,s1)\<in>exec_eventR b \<and> (s1,s')\<in>run bs" using execute_def 
          by (simp add: relcomp.simps)
        then obtain s1 where b4: "(s,s1)\<in>exec_eventR b \<and> (s1,s')\<in>run bs" by auto
        with b3 have b5: "SK_TopSpec.reachable0 (\<Up>s1)" by simp
        have b6: "SK_L2Spec.reachable0 s1" using SK_L2Spec.reachableStep b0 b4 by blast 
        with b4 b5 a0 have "SK_TopSpec.reachable0 (\<Up>s')" using execute_def by auto
      } then show ?thesis by auto
      qed
    qed
  } then show ?thesis by auto
  qed


lemma reachR_reach: "reachable0 s \<Longrightarrow> SK_TopSpec.reachable0 (\<Up>s)" 
  using reachR_reach1 SK_L2Spec.reachable0_def reachable_s0 SK_TopSpec.reachable_s0 s0_ref_lemma
    by (metis Image_singleton_iff execute_def reachable_def)

primrec rmtau :: "'a option list => 'a list"
  where "rmtau [] = []" |
        "rmtau (a#as) = (if a \<noteq> None then
                          the a # rmtau as
                         else rmtau as)"

lemma refine_sound_helper: "\<forall>es st sr. st = \<Up>sr \<longrightarrow> 
          (image abstract_state (execute es sr)) \<subseteq> (SK_TopSpec.execute (rmtau (map eR es)) st)"
  proof -
  {
    fix es
    have "\<forall>st sr. st = \<Up>sr \<longrightarrow> 
          (image abstract_state (execute es sr)) \<subseteq> (SK_TopSpec.execute (rmtau (map eR es)) st)"
    proof(induct es)
      case Nil show ?case
      proof -
      {
        fix st sr
        assume a0: "st = \<Up>sr"
        then have "abstract_state ` SK_L2Spec.execute [] sr = {st}" 
          using SK_L2Spec.execute_def by auto            
        moreover
        from a0 have "SK_TopSpec.execute (rmtau (map eR [])) st = {st}" 
          using SK_TopSpec.execute_def SK_L2Spec.run.run_Nil by simp
        ultimately have "abstract_state ` SK_L2Spec.execute [] sr \<subseteq> SK_TopSpec.execute (rmtau (map eR [])) st" 
          by blast
      } then show ?thesis by auto qed
      next
        case (Cons a as)
        assume a0: "\<forall>st sr. st = \<Up>sr \<longrightarrow> 
              abstract_state ` SK_L2Spec.execute as sr \<subseteq> SK_TopSpec.execute (rmtau (map eR as)) st"
        show ?case
        proof -
        {
          fix st sr
          assume b0: "st = \<Up>sr"
          have b1: "SK_L2Spec.execute (a # as) sr = Image (exec_eventR a O run as) {sr}" 
            using SK_L2Spec.execute_def SK_L2Spec.run.run_Cons by simp
          
          have "abstract_state ` SK_L2Spec.execute (a # as) sr \<subseteq> SK_TopSpec.execute (rmtau (map eR (a # as))) st"
          proof(cases "eR a = None")
            assume c0: "eR a = None"
            then have c1:"rmtau (map eR (a # as)) = rmtau (map eR as)" 
              using rmtau_def by simp
            let ?nextsr = "SK_L2Spec.next_states sr a"
            have c2:"Image (exec_eventR a O run as) {sr} = Image (run as) ?nextsr" 
              using SK_L2Spec.next_states_def by auto
            {
              fix s
              assume d0: "s\<in>abstract_state ` SK_L2Spec.execute (a # as) sr"
              with b1 c2 have "\<exists>s'\<in>?nextsr. s\<in>abstract_state ` Image (run as) {s'}"
                by auto  
              then obtain s' where d1:"s'\<in>?nextsr \<and> s\<in>abstract_state ` Image (run as) {s'}" by auto
              from c0 d1 have d2: "st = \<Up>s'" using refine_exec_event SK_L2Spec.next_states_def 
                b0 by auto 
              with a0 have "abstract_state ` SK_L2Spec.execute as s' \<subseteq> SK_TopSpec.execute (rmtau (map eR as)) st"
                by simp
              with c1 d1 have "s\<in>SK_TopSpec.execute (rmtau (map eR (a # as))) st" 
                using SK_L2Spec.execute_def subsetCE by auto 
            }
            then show ?thesis by blast
          next
            assume c0: "eR a \<noteq> None"
            then have c1:"rmtau (map eR (a # as)) = (the (eR a)) # (rmtau (map eR as))" 
              using rmtau_def by simp
            let ?nextsr = "SK_L2Spec.next_states sr a"
            let ?nextst = "SK_TopSpec.next_states st (the (eR a))"
            have c2:"Image (exec_eventR a O run as) {sr} = Image (run as) ?nextsr" 
              using SK_L2Spec.next_states_def by auto
            have c3:"Image (exec_event (the (eR a)) O SK_TopSpec.run (rmtau (map eR as))) {st} 
                  = Image (SK_TopSpec.run (rmtau (map eR as))) ?nextst" 
              using SK_TopSpec.next_states_def by auto
            {
              fix s
              assume d0: "s\<in>abstract_state ` SK_L2Spec.execute (a # as) sr"
              with b1 c2 have "\<exists>s'\<in>?nextsr. s\<in>abstract_state ` Image (run as) {s'}"
                using Image_singleton_iff SK_L2Spec.next_states_def imageE 
                  image_eqI mem_Collect_eq relcomp.cases by auto
              then obtain s' where d1:"s'\<in>?nextsr \<and> s\<in>abstract_state ` Image (run as) {s'}" by auto
              from c0 d1 have "\<exists>st'\<in>?nextst. st' = \<Up>s'" using refine_exec_event SK_L2Spec.next_states_def 
                b0 by (simp add: SK_TopSpec.next_states_def) 
              then obtain st' where d2: "st'\<in>?nextst \<and> st' = \<Up>s'" by auto
              from a0 d1 d2 have "abstract_state ` SK_L2Spec.execute as s' \<subseteq> SK_TopSpec.execute (rmtau (map eR as)) st'"
                by simp
              with c1 c2 c3 d1 d2 have "s\<in>SK_TopSpec.execute (rmtau (map eR (a # as))) st" 
                using SK_L2Spec.execute_def ImageI Image_singleton_iff SK_TopSpec.execute_def 
                  SK_TopSpec.run.run_Cons subsetCE by auto  
            }
            then show ?thesis by fastforce
          qed
        }
        then show ?thesis by blast
        qed
      qed
    }
    then show ?thesis by auto
    qed

theorem refine_sound: "(image abstract_state (execute es s0r)) \<subseteq> (SK_TopSpec.execute (rmtau (map eR es)) s0t)"
  using refine_sound_helper s0_ref_lemma by fastforce 

subsubsection{* unwinding conditions of refinement*}

  lemma weak_step_consistent_new_evt_ref: 
    "\<forall>e. eR e = None \<and> weak_step_consistent_new_e e \<longrightarrow> SK_L2Spec.weak_step_consistent_e e"
      by (metis SK_L2Spec.weak_step_consistent_e_def refine_exec_event vpeqR_def 
          weak_step_consistent_new_e_def)
    
  lemma local_respect_new_evt_ref: 
    "\<forall>e. eR e = None \<and> local_respect_new_e e \<longrightarrow> SK_L2Spec.local_respect_e e"
      using SK_L2Spec.local_respect_e_def SK_TopSpec.non_interference_def 
        local_respect_new_e_def non_interference1_def refine_exec_event 
        vpeqR_def vpeqR_reflexive_lemma by metis
   
  lemma weak_step_consistent_evt_ref: 
    "\<forall>e. eR e \<noteq> None \<and> SK_TopSpec.weak_step_consistent_e (the (eR e)) 
          \<and> weak_step_consistent_new_e e \<longrightarrow> SK_L2Spec.weak_step_consistent_e e"    
    by (smt SK_L2Spec.weak_step_consistent_e_def SK_TopSpec.step_consistent_def 
        SK_TopSpec.weak_with_step_cons domain_domainR local_respect reachR_reach 
        refine_exec_event vpeqR_def vpeqR_vpeq1 weak_step_consistent weak_step_consistent_new_e_def)
    
  lemma local_respect_evt_ref: 
    "\<forall>e. eR e \<noteq> None \<and> SK_TopSpec.local_respect_e (the (eR e)) 
          \<and> local_respect_new_e e \<longrightarrow> SK_L2Spec.local_respect_e e"
    using SK_L2Spec.local_respect_e_def SK_TopSpec.local_respect_e_def 
          SK_TopSpec.non_interference_def domain_domainR local_respect_new_e_def 
          non_interference1_def reachR_reach refine_exec_event vpeqR_def by metis

  lemma abs_sc_new_imp: "\<lbrakk>SK_TopSpec.weak_step_consistent; weak_step_consistent_new\<rbrakk> 
        \<Longrightarrow> SK_L2Spec.weak_step_consistent"
    using SK_L2Spec.weak_step_consistent_all_evt SK_TopSpec.weak_step_consistent_all_evt 
            weak_step_consistent_evt_ref weak_step_consistent_new_all_evt 
              weak_step_consistent_new_evt_ref by blast 

  lemma abs_lr_new_imp: "\<lbrakk>SK_TopSpec.local_respect; local_respect_new\<rbrakk> \<Longrightarrow> SK_L2Spec.local_respect"
    using SK_L2Spec.local_respect_all_evt SK_TopSpec.local_respect_all_evt 
      local_respect_evt_ref local_respect_new_all_evt local_respect_new_evt_ref by blast
    
  theorem noninfl_refinement: "\<lbrakk>SK_TopSpec.local_respect; SK_TopSpec.weak_step_consistent; 
              weak_step_consistent_new; local_respect_new\<rbrakk> \<Longrightarrow> noninfluence"
    using SK_L2Spec.UnwindingTheorem1 SK_L2Spec.noninf_eq_noninf_gen 
            abs_lr_new_imp abs_sc_new_imp by metis 
    
subsection{* Existing events preserve "local respect" on new state variables *} 

subsubsection{*proving "create sampling port"*}

  lemma crt_smpl_portR_presrv_lcrsp_new:
      assumes p3:"s' = fst (create_sampling_portR sysconf s pname)"
      shows   "s \<sim>. d .\<sim>\<^sub>\<Delta> s'" using p3 by fastforce    

  lemma crt_smpl_portR_presrv_lcrsp_new_e: "local_respect_new_e (hyperc' (Create_Sampling_Port pn))"
    using crt_smpl_portR_presrv_lcrsp_new local_respect_new_e_def exec_eventR_def 
    by fastforce 

subsubsection{*proving "write sampling message"*}

  lemma write_smpl_msgR_presrv_lcrsp_new:
    assumes p3:"s' = fst (write_sampling_messageR s pid m)"
    shows   "s \<sim>. d .\<sim>\<^sub>\<Delta> s'"
    using p3  by fastforce 
  

  lemma write_smpl_msgR_presrv_lcrsp_new_e: "local_respect_new_e (hyperc' (Write_Sampling_Message p m))"
    using write_smpl_msgR_presrv_lcrsp_new local_respect_new_e_def exec_eventR_def 
    by fastforce 

subsubsection{*proving "read sampling message"*}

  lemma read_smpl_msgR_presrv_lcrsp_new:
      assumes p3:"s' = fst (read_sampling_messageR s pid)"
      shows   "s \<sim>. d .\<sim>\<^sub>\<Delta> s'"
    using p3  by fastforce 

  lemma read_smpl_msgR_presrv_lcrsp_new_e: "local_respect_new_e (hyperc' (Read_Sampling_Message p))"
    using read_smpl_msgR_presrv_lcrsp_new local_respect_new_e_def exec_eventR_def 
    by fastforce

subsubsection{*proving "get sampling portid"*}

  lemma get_smpl_pidR_presrv_lcrsp_new:
      assumes p3:"s' = fst (get_sampling_port_idR sysconf s pname)"
      shows   "s \<sim>. d .\<sim>\<^sub>\<Delta> s'"
     using p3 by fastforce

  lemma get_smpl_pidR_presrv_lcrsp_new_e: "local_respect_new_e (hyperc' (Get_Sampling_Portid p))"
    using get_smpl_pidR_presrv_lcrsp_new local_respect_new_e_def exec_eventR_def 
    by fastforce

subsubsection{*proving "get sampling port status"*}
  lemma get_smpl_pstsR_presrv_lcrsp_new:
      assumes p3:"s' = fst (get_sampling_port_statusR sysconf s pid)"
      shows   "s \<sim>. d .\<sim>\<^sub>\<Delta> s'"
      using p3 by fastforce

  lemma get_smpl_pstsR_presrv_lcrsp_new_e: "local_respect_new_e (hyperc' (Get_Sampling_Portstatus p))"
    using get_smpl_pstsR_presrv_lcrsp_new local_respect_new_e_def exec_eventR_def 
      by fastforce

subsubsection{*proving "create queuing port"*}
  lemma crt_que_portR_presrv_lcrsp_new:
  assumes p3:"s' = fst (create_queuing_portR sysconf s pname)"
  shows   "s \<sim>. d .\<sim>\<^sub>\<Delta> s'"
  using p3 by fastforce
   
  lemma crt_que_portR_presrv_lcrsp_new_e: "local_respect_new_e (hyperc' (Create_Queuing_Port p))"
    using crt_que_portR_presrv_lcrsp_new local_respect_new_e_def exec_eventR_def 
    by fastforce

subsubsection{*proving "send queuing message(may lost)"*}
  lemma snd_que_msg_lstR_presrv_lcrsp_new:
    assumes p3:"s' = fst (send_queuing_message_maylostR sysconf s pid m)"
    shows   "s \<sim>. d .\<sim>\<^sub>\<Delta> s'"
    using p3 by fastforce
  

  lemma snd_que_msg_lstR_presrv_lcrsp_new_e: "local_respect_new_e (hyperc' (Send_Queuing_Message p m))"
    using snd_que_msg_lstR_presrv_lcrsp_new local_respect_new_e_def exec_eventR_def 
     by fastforce

subsubsection{*proving "receive queuing message"*}
  lemma rec_que_msgR_presrv_lcrsp_new:
      assumes p3:"s' = fst (receive_queuing_messageR s pid)"
      shows   "s \<sim>. d .\<sim>\<^sub>\<Delta> s'"
      using p3 by fastforce

  lemma rec_que_msgR_presrv_lcrsp_new_e: "local_respect_new_e (hyperc' (Receive_Queuing_Message p))"
    using rec_que_msgR_presrv_lcrsp_new local_respect_new_e_def exec_eventR_def 
     by fastforce

subsubsection{*proving "get queuing portid"*}
  lemma get_que_pidR_presrv_lcrsp_new:
      assumes p3:"s' = fst (get_queuing_port_idR sysconf s pname)"
      shows   "s \<sim>. d .\<sim>\<^sub>\<Delta> s'"
      using p3 by fastforce

  lemma get_que_pidR_presrv_lcrsp_new_e: "local_respect_new_e (hyperc' (Get_Queuing_Portid p))"
    using get_que_pidR_presrv_lcrsp_new local_respect_new_e_def exec_eventR_def 
    by fastforce

subsubsection{*proving "get queuing port status"*}
  lemma get_que_pstsR_presrv_lcrsp_new:
      assumes p3:"s' = fst (get_queuing_port_statusR sysconf s pid)"
      shows   "s \<sim>. d .\<sim>\<^sub>\<Delta> s'"
    using p3 by fastforce

  lemma get_que_pstsR_presrv_lcrsp_new_e: "local_respect_new_e (hyperc' (Get_Queuing_Portstatus p))"
    using get_que_pstsR_presrv_lcrsp_new local_respect_new_e_def exec_eventR_def 
    by fastforce

subsubsection{*proving "clear queuing port"*}
  lemma clr_que_portR_presrv_lcrsp_new:
      assumes p3:"s' = clear_queuing_portR s pid"
      shows   "s \<sim>. d .\<sim>\<^sub>\<Delta> s'"
      using p3 by fastforce

  lemma clr_que_portR_presrv_lcrsp_new_e: "local_respect_new_e (hyperc' (Clear_Queuing_Port p))"
    using clr_que_portR_presrv_lcrsp_new local_respect_new_e_def exec_eventR_def 
    by fastforce

subsubsection{*proving "get partition statue"*}
  lemma get_part_statusR_presrv_lcrsp_new:
      assumes p3:"s' = fst (get_partition_statusR sysconf s)"
      shows   "s \<sim>. d .\<sim>\<^sub>\<Delta> s'"
   using p3 by fastforce 
   

  lemma get_part_statusR_presrv_lcrsp_new_e: "local_respect_new_e (hyperc' Get_Partition_Status)"
    using get_part_statusR_presrv_lcrsp_new local_respect_new_e_def exec_eventR_def
      vpeq_part_procs_reflexive_lemma by (fastforce cong del: vpeq_part_procs_def) 

subsubsection{*proving "set partition mode"*}
  lemma set_procs_to_normal_presrv_lcrsp_new:
    assumes p3: "current s \<noteq> d"
      and   p4: "s' = set_procs_to_normal s (current s)"
      shows   "s \<sim>. d .\<sim>\<^sub>\<Delta> s'"
      using p3 p4   by auto 


  lemma remove_partition_resources_presrv_lcrsp_new:
    assumes p3: "current s \<noteq> d"
      and   p4: "s' = remove_partition_resources s (current s)"
      shows   "s \<sim>. d .\<sim>\<^sub>\<Delta> s'" 
      using p3 p4  by auto 

  lemma set_part_modeR_presrv_lcrsp_new:
    assumes 
         p3: "current s \<noteq> d"
      and   p4: "s' = set_partition_modeR sysconf s m"
      shows   "s \<sim>. d .\<sim>\<^sub>\<Delta> s'"
    using p3 p4 by auto

  lemma set_part_modeR_presrv_lcrsp_new_e: "local_respect_new_e (hyperc' (Set_Partition_Mode p))"
    using set_part_modeR_presrv_lcrsp_new local_respect_new_e_def 
      exec_eventR_def nintf_neq domain_of_eventR_hc event_enabledR_hc   
   by (fastforce cong del: set_partition_modeR_def non_interference1_def )
    
subsubsection{*proving "schedule" *}
  lemma scheduleR_presrv_lcrsp_new:
      assumes p2:"(scheduler sysconf) \<setminus>\<leadsto> d"       
      shows   "s \<sim>. d .\<sim>\<^sub>\<Delta> s'"
    using p2 schedeler_intf_all_help by auto

  lemma scheduleR_presrv_lcrsp_new_e: "local_respect_new_e (sys' Schedule)"
    using scheduleR_presrv_lcrsp_new local_respect_new_e_def 
      exec_eventR_def nintf_neq domain_of_eventR_hc event_enabledR_hc  
    by (auto cong del: non_interference1_def)

subsubsection{*proving "Transfer Sampling Message"*}
  lemma trans_smpl_msgR_presrv_lcrsp_new:
      assumes p3:"s' = transf_sampling_msgR s c"
      shows   "s \<sim>. d .\<sim>\<^sub>\<Delta> s'"
   using p3 by fastforce

  lemma trans_smpl_msgR_presrv_lcrsp_new_e: "local_respect_new_e (sys' (Transfer_Sampling_Message c))"
    using trans_smpl_msgR_presrv_lcrsp_new local_respect_new_e_def 
      exec_eventR_def nintf_neq 
      domain_of_eventR_hc event_enabledR_hc  
   by (fastforce cong del: non_interference1_def)

subsubsection{*proving "Transfer Queuing Message"*}
  lemma trans_que_msg_mlostR_presrv_lcrsp_new:
      assumes p3:"s' = transf_queuing_msg_maylostR sysconf s c"
      shows   "s \<sim>. d .\<sim>\<^sub>\<Delta> s'" 
    using p3 by fastforce

  lemma trans_que_msg_mlostR_presrv_lcrsp_new_e: "local_respect_new_e (sys' (Transfer_Queuing_Message c))"
    using trans_que_msg_mlostR_presrv_lcrsp_new local_respect_new_e_def 
      exec_eventR_def nintf_neq domain_of_eventR_hc event_enabledR_hc 
    by (fastforce cong del: non_interference1_def) 

subsection{* New events preserve "local respect" on new state variables *} 
lemma create_process_vpeq_part_procs:
    assumes 
           p3: "current s \<noteq> d"
      and  p4: "s' = fst (create_process s pri)"
    shows "s \<sim>. d .\<sim>\<^sub>\<Delta> s'" 
    using  p3 p4  by auto   

lemma create_process_presrv_lcrsp_new_e: "local_respect_new_e (hyperc' (Create_Process p))"
  using create_process_vpeq_part_procs local_respect_new_e_def 
    exec_eventR_def nintf_neq 
    domain_of_eventR_hc event_enabledR_hc  
   by (auto cong del: create_process_def non_interference1_def) 

lemma set_process_priority_vpeq_part_procs:
    assumes 
           p3: "current s \<noteq> d"
      and  p4: "s' = set_process_priority s p pri"
    shows "s \<sim>. d .\<sim>\<^sub>\<Delta> s'" 
   using  p3 p4 by auto

lemma set_process_priority_presrv_lcrsp_new_e: "local_respect_new_e (hyperc' (Set_Priority p pri))"
  using set_process_priority_vpeq_part_procs local_respect_new_e_def 
    exec_eventR_def nintf_neq vpeq_part_procs_def
  by (auto cong del:  non_interference1_def set_process_priority_def)

lemma start_process_vpeq_part_procs:
    assumes p3: "current s \<noteq> d"
      and  p4: "s' = start_process s p"
    shows "s \<sim>. d .\<sim>\<^sub>\<Delta> s'" 
    using  p3 p4 by auto

lemma start_process_presrv_lcrsp_new_e: "local_respect_new_e (hyperc' (Start_Process p))"
  using start_process_vpeq_part_procs local_respect_new_e_def 
    exec_eventR_def nintf_neq  
   by (auto cong del: non_interference1_def start_process_def)

lemma stop_process_vpeq_part_procs:
    assumes 
           p3: "current s \<noteq> d"
      and  p4: "s' = stop_process s p"
    shows "s \<sim>. d .\<sim>\<^sub>\<Delta> s'" 
    using p3 p4 by auto

lemma stop_process_presrv_lcrsp_new_e: "local_respect_new_e (hyperc' (Stop_Process p))"
  using stop_process_vpeq_part_procs local_respect_new_e_def 
    exec_eventR_def nintf_neq  
   by (auto cong del: stop_process_def non_interference1_def)

lemma suspend_process_vpeq_part_procs:
    assumes 
           p3: "current s \<noteq> d"
      and  p4: "s' = suspend_process s p"
    shows "s \<sim>. d .\<sim>\<^sub>\<Delta> s'" 
    using  p3 p4 by auto
    
lemma suspend_process_presrv_lcrsp_new_e: "local_respect_new_e (hyperc' (Suspend_Process p))"
  using suspend_process_vpeq_part_procs local_respect_new_e_def 
    exec_eventR_def nintf_neq  
   by (auto cong del: suspend_process_def non_interference1_def)

lemma resume_process_vpeq_part_procs:
    assumes p3: "current s \<noteq> d"
      and  p4: "s' = resume_process s p"
    shows "s \<sim>. d .\<sim>\<^sub>\<Delta> s'" 
    using p3 p4 by auto


lemma resume_process_presrv_lcrsp_new_e: "local_respect_new_e (hyperc' (Resume_Process p))"
  using resume_process_vpeq_part_procs local_respect_new_e_def 
    exec_eventR_def nintf_neq vpeq_part_procs_def 
   by (auto cong del: resume_process_def non_interference1_def)

lemma get_process_status_vpeq_part_procs:
    assumes 
            p3: "current s \<noteq> d"
      and  p4: "s' = fst (get_process_status s p)"
    shows "s \<sim>. d .\<sim>\<^sub>\<Delta> s'" 
  using p3 p4 by auto


lemma get_process_status_presrv_lcrsp_new_e: "local_respect_new_e (hyperc' (Get_Process_Status p))"
  using get_process_status_vpeq_part_procs local_respect_new_e_def 
    exec_eventR_def nintf_neq  
 by (auto cong del: get_process_status_def non_interference1_def)


lemma schedule_process_vpeq_part_procs:
     assumes p3: "current s \<noteq> d"
      and  p4: "s' \<in> schedule_process s"
    shows "s \<sim>. d .\<sim>\<^sub>\<Delta> s'" 
    proof -
      let ?s' = "setRun2Ready s"
      let ?readyprs = "{p. p\<in>the (procs ?s' (current ?s')) \<and> 
                              state (the (proc_state ?s' (current ?s',p))) = READY}"
      show ?thesis 
        proof(cases "is_a_partition sysconf (current s) \<and> part_mode (the ((partitions s) (current s))) = NORMAL")
          assume a0: "is_a_partition sysconf (current s) \<and> part_mode (the ((partitions s) (current s))) = NORMAL"
          let ?s' = "setRun2Ready s"
          let ?readyprs = "{p. p\<in>the (procs ?s' (current ?s')) \<and> 
                                  state (the (proc_state ?s' (current ?s',p))) = READY}"
          let ?selp = "SOME p. p\<in>{x. state (the (proc_state ?s' (current ?s',x))) = READY \<and>
                                                         (\<forall>y\<in>?readyprs. priority (the (proc_state ?s' (current ?s',x))) \<ge>
                                                                      priority (the (proc_state ?s' (current ?s',y))))}"
          let ?st = "the ((proc_state ?s') (current ?s', ?selp))"
          let ?proc_st = "proc_state ?s'"
          let ?cur_pr = "cur_proc_part ?s'"
          from a0 have a1: "schedule_process s = {?s'\<lparr>proc_state := ?proc_st ((current ?s', ?selp) := Some (?st\<lparr>state := RUNNING\<rparr>)),
                                           cur_proc_part := ?cur_pr(current ?s' := Some ?selp)\<rparr>}"
            by auto
          then have b2: "vpeq_part_procs s d ?s'" using p3   by auto
          have b4: "current s = current ?s'"  by auto
          then have b3: "vpeq_part_procs ?s' d s'"
            using p3 a1 p4 by(auto cong del: schedule_process_def setRun2Ready_def)                                    
          with b2 show ?thesis using  vpeq_part_procs_transitive_lemma by blast 
      next
        assume a0: "\<not> (is_a_partition sysconf (current s) \<and> part_mode (the ((partitions s) (current s))) = NORMAL)"
        then show ?thesis using  p4  by auto
      qed
  qed

lemma schedule_process_presrv_lcrsp_new_e: "local_respect_new_e (sys' Schedule_Process)"
  using schedule_process_vpeq_part_procs local_respect_new_e_def 
    exec_eventR_def nintf_neq domain_of_eventR_hc   
   by (auto cong del: non_interference1_def schedule_process_def)

subsection{* Proving the "local respect" property on new variables *}
  theorem local_respect_new:local_respect_new
  proof -
      {
        fix e
        have "local_respect_new_e e"
          apply(induct e)
          using crt_smpl_portR_presrv_lcrsp_new_e write_smpl_msgR_presrv_lcrsp_new_e 
                  read_smpl_msgR_presrv_lcrsp_new_e get_smpl_pidR_presrv_lcrsp_new_e
                  get_smpl_pstsR_presrv_lcrsp_new_e crt_que_portR_presrv_lcrsp_new_e
                  snd_que_msg_lstR_presrv_lcrsp_new_e rec_que_msgR_presrv_lcrsp_new_e
                  get_que_pidR_presrv_lcrsp_new_e get_que_pstsR_presrv_lcrsp_new_e
                  clr_que_portR_presrv_lcrsp_new_e set_part_modeR_presrv_lcrsp_new_e
                  get_part_statusR_presrv_lcrsp_new_e create_process_presrv_lcrsp_new_e     
                  start_process_presrv_lcrsp_new_e stop_process_presrv_lcrsp_new_e 
                  resume_process_presrv_lcrsp_new_e suspend_process_presrv_lcrsp_new_e
                  set_process_priority_presrv_lcrsp_new_e get_process_status_presrv_lcrsp_new_e
          apply(rule Hypercall'.induct)
          using scheduleR_presrv_lcrsp_new_e trans_smpl_msgR_presrv_lcrsp_new_e
                  trans_que_msg_mlostR_presrv_lcrsp_new_e schedule_process_presrv_lcrsp_new_e 
          by(rule System_EventR.induct)
      }
      then show ?thesis using local_respect_new_all_evt by simp
    qed

subsection{* Existing events preserve "step consistent" on new state variables *} 

  lemma crt_smpl_portR_presrv_wk_stp_cons_new:
      assumes 
              p1:"s \<sim>. d .\<sim> t"
        and   p2:"s' = fst (create_sampling_portR sysconf s pname)"
        and   p3:"t' = fst (create_sampling_portR sysconf t pname)"
      shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'" 
    using p1 p2 p3 by fastforce

  lemma crt_smpl_portR_presrv_wk_stp_cons_new_e: "weak_step_consistent_new_e (hyperc' (Create_Sampling_Port pn))"
    using crt_smpl_portR_presrv_wk_stp_cons_new weak_step_consistent_new_e_def 
      exec_eventR_def domain_of_eventR_def event_enabledR_def same_part_mode sched_vpeq
        non_interference1_def non_interference_def singletonD 
          by (smt EventR.case(1) Hypercall'.case(1) State.select_convs(1) State.select_convs(2) 
                abstract_state_def domain_of_eventR_hc event_enabledR_hc mem_Collect_eq 
                singletonD vpeqR_def option.sel prod.simps(2))

  lemma wrt_smpl_msgR_presrv_wk_stp_cons_new:
      assumes p1:"s \<sim>. d .\<sim> t"
        and   p2:"s' = fst (write_sampling_messageR s pid m)"
        and   p3:"t' = fst (write_sampling_messageR t pid m)"
      shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'"
   using p1 p2 p3 by fastforce

  lemma wrt_smpl_msgR_presrv_wk_stp_cons_new_e: "weak_step_consistent_new_e (hyperc' (Write_Sampling_Message p m))"
    using wrt_smpl_msgR_presrv_wk_stp_cons_new weak_step_consistent_new_e_def 
      exec_eventR_def domain_of_eventR_def event_enabledR_def same_part_mode sched_vpeq 
      non_interference1_def non_interference_def singletonD event_enabledR_hc domain_of_eventR_hc
      abstract_state_def vpeqR_def
          by (smt EventR.case(1) Hypercall'.case(2) State.select_convs(1) State.select_convs(2) 
                abstract_state_def mem_Collect_eq singletonD  option.sel prod.simps(2))

  lemma read_smpl_msgR_presrv_wk_stp_cons_new:
      assumes p1:"s \<sim>. d .\<sim> t"
        and   p2:"s' = fst (read_sampling_messageR s pid)"
        and   p3:"t' = fst (read_sampling_messageR t pid)"
      shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'"  
   using p1 p2 p3 by fastforce

  lemma read_smpl_msgR_presrv_wk_stp_cons_new_e: "weak_step_consistent_new_e (hyperc' (Read_Sampling_Message p))"
    using read_smpl_msgR_presrv_wk_stp_cons_new weak_step_consistent_new_e_def 
      exec_eventR_def domain_of_eventR_def event_enabledR_def same_part_mode sched_vpeq 
      non_interference1_def non_interference_def singletonD 
          by (smt EventR.case(1) Hypercall'.case(3) State.select_convs(1) State.select_convs(2) 
                abstract_state_def domain_of_eventR_hc event_enabledR_hc mem_Collect_eq 
                singletonD vpeqR_def option.sel prod.simps(2))

  lemma get_smpl_pidR_presrv_wk_stp_cons_new:
      assumes p1:"s \<sim>. d .\<sim> t"
        and   p2:"s' = fst (get_sampling_port_idR sysconf s pname)"
        and   p3:"t' = fst (get_sampling_port_idR sysconf t pname)"
      shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'" 
    using p1 p2 p3 by fastforce


  lemma get_smpl_pidR_presrv_wk_stp_cons_new_e: "weak_step_consistent_new_e (hyperc' (Get_Sampling_Portid p))"
    using get_smpl_pidR_presrv_wk_stp_cons_new weak_step_consistent_new_e_def 
      exec_eventR_def domain_of_eventR_def event_enabledR_def same_part_mode sched_vpeq 
      non_interference1_def non_interference_def singletonD 
          by (smt EventR.case(1) Hypercall'.case(4) State.select_convs(1) State.select_convs(2) 
                abstract_state_def domain_of_eventR_hc event_enabledR_hc mem_Collect_eq 
                singletonD vpeqR_def option.sel prod.simps(2))

  lemma get_smpl_pstsR_presrv_wk_stp_cons_new:
      assumes p1:"s \<sim>. d .\<sim> t"
        and   p2:"s' = fst (get_sampling_port_statusR sysconf s pid)"
        and   p3:"t' = fst (get_sampling_port_statusR sysconf t pid)"
      shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'" 
     using p1 p2 p3 by fastforce

  lemma get_smpl_pstsR_presrv_wk_stp_cons_new_e: "weak_step_consistent_new_e (hyperc' (Get_Sampling_Portstatus p))"
    using get_smpl_pstsR_presrv_wk_stp_cons_new weak_step_consistent_new_e_def 
      exec_eventR_def domain_of_eventR_def event_enabledR_def same_part_mode sched_vpeq 
      non_interference1_def non_interference_def singletonD 
          by (smt EventR.case(1) Hypercall'.case(5) State.select_convs(1) State.select_convs(2) 
                abstract_state_def domain_of_eventR_hc event_enabledR_hc mem_Collect_eq 
                singletonD vpeqR_def option.sel prod.simps(2))

  lemma crt_que_portR_presrv_wk_stp_cons_new:
      assumes p1:"s \<sim>. d .\<sim> t"
        and   p2:"s' = fst (create_queuing_portR sysconf s pname)"
        and   p3:"t' = fst (create_queuing_portR sysconf t pname)"
      shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'"
     using p1 p2 p3 by auto

  lemma crt_que_portR_presrv_wk_stp_cons_new_e: "weak_step_consistent_new_e (hyperc' (Create_Queuing_Port p))"
    using crt_que_portR_presrv_wk_stp_cons_new weak_step_consistent_new_e_def 
      exec_eventR_def domain_of_eventR_def event_enabledR_def same_part_mode sched_vpeq 
      non_interference1_def non_interference_def singletonD 
          by (smt EventR.case(1) Hypercall'.case(6) State.select_convs(1) State.select_convs(2) 
                abstract_state_def domain_of_eventR_hc event_enabledR_hc mem_Collect_eq 
                singletonD vpeqR_def option.sel prod.simps(2))

  lemma snd_que_msg_lstR_presrv_wk_stp_cons_new:
      assumes 
              p1:"s \<sim>. d .\<sim> t"
        and   p2:"s' = fst (send_queuing_message_maylostR sysconf s pid m)"
        and   p3:"t' = fst (send_queuing_message_maylostR sysconf t pid m)"
      shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'"
     using p1 p2 p3 by auto

  lemma snd_que_msg_lstR_presrv_wk_stp_cons_new_e: "weak_step_consistent_new_e (hyperc' (Send_Queuing_Message p m))"
    using snd_que_msg_lstR_presrv_wk_stp_cons_new weak_step_consistent_new_e_def 
      exec_eventR_def domain_of_eventR_def event_enabledR_def same_part_mode sched_vpeq 
      non_interference1_def non_interference_def singletonD 
          by (smt EventR.case(1) Hypercall'.case(7) State.select_convs(1) State.select_convs(2) 
                abstract_state_def domain_of_eventR_hc event_enabledR_hc mem_Collect_eq 
                singletonD vpeqR_def option.sel prod.simps(2))

  lemma rec_que_msgR_presrv_wk_stp_cons_new:
      assumes p1:"s \<sim>. d .\<sim> t"                
        and   p2:"s' = fst (receive_queuing_messageR s pid)"
        and   p3:"t' = fst (receive_queuing_messageR t pid)"
      shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'"
    using p1 p2 p3 by auto

  lemma rec_que_msgR_presrv_wk_stp_cons_new_e: "weak_step_consistent_new_e (hyperc' (Receive_Queuing_Message p))"
    using rec_que_msgR_presrv_wk_stp_cons_new weak_step_consistent_new_e_def 
      exec_eventR_def domain_of_eventR_def event_enabledR_def same_part_mode sched_vpeq 
      non_interference1_def non_interference_def singletonD 
          by (smt EventR.case(1) Hypercall'.case(8) State.select_convs(1) State.select_convs(2) 
                abstract_state_def domain_of_eventR_hc event_enabledR_hc mem_Collect_eq 
                singletonD vpeqR_def option.sel prod.simps(2))

  lemma get_que_pidR_presrv_wk_stp_cons_new:
      assumes p1:"s \<sim>. d .\<sim> t"
        and   p2:"s' = fst (get_queuing_port_idR sysconf s pname)"
        and   p3:"t' = fst (get_queuing_port_idR sysconf t pname)"
      shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'" using p1 p2 p3 by auto

  lemma get_que_pidR_presrv_wk_stp_cons_new_e: "weak_step_consistent_new_e (hyperc' (Get_Queuing_Portid p))"
    using get_que_pidR_presrv_wk_stp_cons_new weak_step_consistent_new_e_def 
      exec_eventR_def domain_of_eventR_def event_enabledR_def same_part_mode sched_vpeq 
          by (smt EventR.case(1) Hypercall'.case(9) State.select_convs(1) State.select_convs(2) 
                abstract_state_def domain_of_eventR_hc event_enabledR_hc mem_Collect_eq 
                singletonD vpeqR_def option.sel prod.simps(2))

  lemma get_que_pstsR_presrv_wk_stp_cons_new:
      assumes p1:"s \<sim>. d .\<sim> t"
        and   p2:"s' = fst (get_queuing_port_statusR sysconf s pid)"
        and   p3:"t' = fst (get_queuing_port_statusR sysconf t pid)"
      shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'" using p1 p2 p3 by auto

  lemma get_que_pstsR_presrv_wk_stp_cons_new_e: "weak_step_consistent_new_e (hyperc' (Get_Queuing_Portstatus p))"
    using get_que_pstsR_presrv_wk_stp_cons_new weak_step_consistent_new_e_def 
      exec_eventR_def domain_of_eventR_def event_enabledR_def same_part_mode sched_vpeq 
      non_interference1_def non_interference_def singletonD 
          by (smt EventR.case(1) Hypercall'.case(10) State.select_convs(1) State.select_convs(2) 
                abstract_state_def domain_of_eventR_hc event_enabledR_hc mem_Collect_eq 
                singletonD vpeqR_def option.sel prod.simps(2))

  lemma clr_que_portR_presrv_wk_stp_cons_new:
      assumes p1:"s \<sim>. d .\<sim> t"
        and   p2:"s' = clear_queuing_portR s pid"
        and   p3:"t' = clear_queuing_portR t pid"
      shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'"
      using p1 p2 p3 by auto

  lemma clr_que_portR_presrv_wk_stp_cons_new_e: "weak_step_consistent_new_e (hyperc' (Clear_Queuing_Port p))"
    using clr_que_portR_presrv_wk_stp_cons_new weak_step_consistent_new_e_def 
      exec_eventR_def domain_of_eventR_def event_enabledR_def same_part_mode sched_vpeq 
          by (smt EventR.case(1) Hypercall'.case(11) State.select_convs(1) State.select_convs(2) 
                abstract_state_def domain_of_eventR_hc event_enabledR_hc mem_Collect_eq 
                singletonD vpeqR_def option.sel prod.simps(2))

  lemma get_part_statusR_presrv_wk_stp_cons_new:
      assumes p1:"s \<sim>. d .\<sim> t"
        and   p2:"s' = fst (get_partition_statusR sysconf s)"
        and   p3:"t' = fst (get_partition_statusR sysconf t)"
      shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'" using p1 p2 p3 by auto

  lemma get_part_statusR_presrv_wk_stp_cons_new_e: "weak_step_consistent_new_e (hyperc' Get_Partition_Status)"
    using get_part_statusR_presrv_wk_stp_cons_new weak_step_consistent_new_e_def 
      exec_eventR_def domain_of_eventR_def event_enabledR_def same_part_mode sched_vpeq 
          by (smt EventR.case(1) Hypercall'.case(13) State.select_convs(1) State.select_convs(2) 
                abstract_state_def domain_of_eventR_hc event_enabledR_hc mem_Collect_eq 
                singletonD vpeqR_def option.sel prod.simps(2))

  lemma scheduleR_presrv_wk_stp_cons_new:
      assumes p1:"s \<sim>. d .\<sim> t"
        and   p2:"s' \<in> scheduleR sysconf s"
        and   p3:"t' \<in> scheduleR sysconf t"
      shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'" using p1 p2 p3 by auto


  lemma scheduleR_presrv_wk_stp_cons_new_e: "weak_step_consistent_new_e (sys' Schedule)"
    using scheduleR_presrv_wk_stp_cons_new weak_step_consistent_new_e_def 
      exec_eventR_def same_part_mode sched_vpeq 
          by (smt EventR.case(2) System_EventR.case(1) State.select_convs(1) State.select_convs(2) 
                abstract_state_def domain_of_eventR_sys event_enabledR_sys mem_Collect_eq 
                singletonD vpeqR_def option.sel prod.simps(2))

  lemma trans_smpl_msgR_presrv_wk_stp_cons_new:
      assumes 
              p1:"s \<sim>. d .\<sim> t"
        and   p2:"s' = transf_sampling_msgR s c"
        and   p3:"t' = transf_sampling_msgR t c"
      shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'" using p1 p2 p3 by auto
    

  lemma trans_smpl_msgR_presrv_wk_stp_cons_new_e: "weak_step_consistent_new_e (sys' (Transfer_Sampling_Message c))"
    using trans_smpl_msgR_presrv_wk_stp_cons_new weak_step_consistent_new_e_def 
      exec_eventR_def same_part_mode is_a_transmitter_def vpeq1_def vpeq_sched_def
          by (smt EventR.case(2) System_EventR.case(2) State.select_convs(1) State.select_convs(2) 
                abstract_state_def domain_of_eventR_sys event_enabledR_sys mem_Collect_eq 
                singletonD vpeqR_def option.sel prod.simps(2))

  lemma trans_que_msg_mlostR_presrv_wk_stp_cons_new:
      assumes p1:"s \<sim>. d .\<sim> t"
        and   p2:"s' = transf_queuing_msg_maylostR sysconf s c"
        and   p3:"t' = transf_queuing_msg_maylostR sysconf t c"
      shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'" using p1 p2 p3 by auto

  lemma trans_que_msg_mlostR_presrv_wk_stp_cons_new_e: "weak_step_consistent_new_e (sys' (Transfer_Queuing_Message c))"
    using trans_que_msg_mlostR_presrv_wk_stp_cons_new weak_step_consistent_new_e_def 
      exec_eventR_def same_part_mode is_a_transmitter_def vpeq1_def vpeq_sched_def 
          by (smt EventR.case(2) System_EventR.case(3) State.select_convs(1) State.select_convs(2) 
                abstract_state_def domain_of_eventR_sys event_enabledR_sys mem_Collect_eq 
                singletonD vpeqR_def option.sel prod.simps(2))

  lemma set_procs_to_normal_presrv_wk_stp_cons_new:
    assumes p1:"is_a_partition sysconf d"      
      and   p2:"s \<sim>. d .\<sim> t"
      and   p3:"s \<sim>. (scheduler sysconf) .\<sim> t"
      and   p4:"s' = set_procs_to_normal s (current s)"
      and   p5:"t' = set_procs_to_normal t (current t)"
    shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'"  
    proof -
      from p1 p2 have a0: "(partitions s) d = (partitions t) d"         
        using part_imp_not_sch part_imp_not_tras by force            
      then show ?thesis using p1 p2 p3 p4 p5  by auto
    qed


  lemma remove_partition_resources_presrv_wk_stp_cons_new:
    assumes p1:"is_a_partition sysconf d"
      and   p2:"s \<sim>. d .\<sim> t"
      and   p3:"s \<sim>. (scheduler sysconf) .\<sim> t"
      and   p4:"s' = remove_partition_resources s (current s)"
      and   p5:"t' = remove_partition_resources t (current t)"
    shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'" 
    proof -
      from p1 p2 have a0: "(partitions s) d = (partitions t) d" 
         using part_imp_not_sch part_imp_not_tras by force            
       show ?thesis using p1 p2 p3  p4 p5 by auto      
    qed

  lemma set_part_modeR_presrv_wk_stp_cons_new:
    assumes p1:"is_a_partition sysconf (current s)"
      and   p2:"reachable0 s \<and> reachable0 t"
      and   p3:"s \<sim>. d .\<sim> t"
      and   p4:"s \<sim>. (scheduler sysconf) .\<sim> t"
      and   p5:"(current s) \<leadsto> d"
      and   p6:"s \<sim>. (current s) .\<sim> t"
      and   p7:"s' = set_partition_modeR sysconf s m"
      and   p8:"t' = set_partition_modeR sysconf t m"
   shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'"
   proof(cases "is_a_partition sysconf d")
      assume a0:"is_a_partition sysconf d"
      show ?thesis
      proof(cases "current s = d")
        assume b0: "current s = d"
        with p3 a0 have b1: "(partitions s) d = (partitions t) d" 
          using part_imp_not_sch part_imp_not_tras by force
          thus ?thesis using p3 p1 a0 b0 p8 p2 p4 p6 p7 by auto        
      next
        assume b0: "current s \<noteq> d"
        with p1 p2 p7 a0 have b1: "vpeq_part_procs s d s'"
          by auto 
        from p1 p2 p3 p8 a0 p4 b0 have b2: "vpeq_part_procs t d t'"
          by auto 
        from p3 b1 a0 b2 show ?thesis by auto
      qed
  next
    assume b1:"\<not> is_a_partition sysconf d"
    show ?thesis using b1 by auto
  qed
            
  lemma set_part_modeR_presrv_wk_stp_cons_new_e: "weak_step_consistent_new_e (hyperc' (Set_Partition_Mode p))"
    using set_part_modeR_presrv_wk_stp_cons_new weak_step_consistent_new_e_def 
      exec_eventR_def same_part_mode sched_vpeq singletonD EventR.case(1) Hypercall'.case(12)
          by (smt State.select_convs(1) State.select_convs(2) 
                abstract_state_def domain_of_eventR_hc event_enabledR_hc mem_Collect_eq 
                singletonD vpeqR_def option.sel prod.simps(2))


subsection{* New events preserve "step consistent" on new state variables *} 
subsubsection{*proving "Create process"*}
  lemma create_process_presrv_wk_stp_cons_new:
      assumes p1:"is_a_partition sysconf (current s)"        
        and   p2:"s \<sim>. d .\<sim> t"
        and   p3:"s \<sim>. (scheduler sysconf) .\<sim> t"        
        and   p4:"s \<sim>. (current s) .\<sim> t"
        and   p5:"s' = fst (create_process s pri)"
        and   p6:"t' = fst (create_process t pri)"
      shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'"
      proof(cases "is_a_partition sysconf d")
        assume a0:"is_a_partition sysconf d"
        from p3 have a1: "current s = current t" by auto
        show ?thesis 
          proof(cases "current s = d")
            assume b0: "current s = d"
            with p2 a0 have b1: "(partitions s) d = (partitions t) d" 
              using part_imp_not_sch part_imp_not_tras by force              
              thus ?thesis using p1  p2 p3 p4  p6 p5 by fastforce             
          next
            assume b0: "current s \<noteq> d"
            with p5 have b1: "vpeq_part_procs s d s'" 
              using create_process_vpeq_part_procs[OF b0 p5] by (simp cong del: )
            moreover from p6 a0 a1 b0 have b2: "vpeq_part_procs t d t'"
              using create_process_vpeq_part_procs[OF b0] by simp
            ultimately  show ?thesis using p2  by auto 
          qed
      next
        assume b1:"\<not> is_a_partition sysconf d"
        then show ?thesis by auto
      qed

  lemma create_process_presrv_wk_stp_cons_new_e: "weak_step_consistent_new_e (hyperc' (Create_Process p))"
    using create_process_presrv_wk_stp_cons_new weak_step_consistent_new_e_def exec_eventR_def 
       same_part_mode sched_vpeq
          by (smt EventR.case(1) Hypercall'.case(14) State.select_convs(1) State.select_convs(2) 
                abstract_state_def domain_of_eventR_hc event_enabledR_hc mem_Collect_eq 
                singletonD vpeqR_def option.sel prod.simps(2))


subsubsection{*proving "set process priority"*}
  lemma set_process_priority_presrv_wk_stp_cons_new:
      assumes p1:"is_a_partition sysconf (current s)"
        and   p2:"reachable0 s \<and> reachable0 t"
        and   p3:"s \<sim>. d .\<sim> t"
        and   p4:"s \<sim>. (scheduler sysconf) .\<sim> t"
        and   p5:"s \<sim>. (current s) .\<sim> t"
        and   p6:"s' = set_process_priority s pr pri"
        and   p7:"t' = set_process_priority t pr pri"
      shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'"
      proof(cases "is_a_partition sysconf d")
        assume a0:"is_a_partition sysconf d"
        from p3 p4 have a1: "current s = current t" 
          by auto
        show ?thesis
          proof(cases "current s = d")
            assume b0: "current s = d"
            with p3 a0 have b1: "(partitions s) d = (partitions t) d" 
              using part_imp_not_sch part_imp_not_tras by force       
            thus ?thesis using  p1 a0 b0 p5  p4 p6 p7 by auto
          next
            assume b0: "current s \<noteq> d"
            with p1 p2 p6 a0 have b1: "vpeq_part_procs s d s'" 
              by auto
            from p1 p2 p7 a0 a1 b0 have b2: "vpeq_part_procs t d t'"
              by auto
            from p3 b1 a0 b2 show ?thesis by auto
          qed
      next
        assume b1:"\<not> is_a_partition sysconf d"
        then show ?thesis by auto
      qed

  lemma set_process_priority_presrv_wk_stp_cons_new_e: "weak_step_consistent_new_e (hyperc' (Set_Priority p pri))"
    using set_process_priority_presrv_wk_stp_cons_new weak_step_consistent_new_e_def 
      exec_eventR_def same_part_mode sched_vpeq domain_of_eventR_hc event_enabledR_hc 
          by (smt EventR.case(1) Hypercall'.case(19) State.select_convs(1) State.select_convs(2) 
                abstract_state_def mem_Collect_eq old.prod.case singletonD vpeqR_def option.sel prod.simps(2))

subsubsection{*proving "start process"*}
  lemma start_process_presrv_wk_stp_cons_new:
      assumes p1:"is_a_partition sysconf (current s)"
        and   p2:"reachable0 s \<and> reachable0 t"
        and   p3:"s \<sim>. d .\<sim> t"
        and   p4:"s \<sim>. (scheduler sysconf) .\<sim> t"       
        and   p5:"s \<sim>. (current s) .\<sim> t"
        and   p6:"s' = start_process s pr"
        and   p7:"t' = start_process t pr"
      shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'" 
 proof(cases "is_a_partition sysconf d")
      assume a0:"is_a_partition sysconf d"
      from p3 p4 have a1: "current s = current t" 
        by auto
      show ?thesis
        proof(cases "current s = d")
          assume b0: "current s = d"
          with p3 a0 have b1: "(partitions s) d = (partitions t) d" 
            using part_imp_not_sch part_imp_not_tras by force       
          thus ?thesis using  p1 a0 b0 p5  p4 p6 p7 by auto
        next
          assume b0: "current s \<noteq> d"
          with p1 p2 p6 a0 have b1: "vpeq_part_procs s d s'" 
            by auto
          from p1 p2 p7 a0 a1 b0 have b2: "vpeq_part_procs t d t'"
            by auto
          from p3 b1 a0 b2 show ?thesis by auto
        qed
    next
      assume b1:"\<not> is_a_partition sysconf d"
      then show ?thesis by auto
    qed
     

  lemma start_process_presrv_wk_stp_cons_new_e: "weak_step_consistent_new_e (hyperc' (Start_Process p))"
    using start_process_presrv_wk_stp_cons_new weak_step_consistent_new_e_def 
      exec_eventR_def same_part_mode sched_vpeq
          by (smt EventR.case(1) Hypercall'.case(15) State.select_convs(1) State.select_convs(2) 
                abstract_state_def domain_of_eventR_hc event_enabledR_hc mem_Collect_eq 
                singletonD vpeqR_def option.sel prod.simps(2))

subsubsection{*proving "stop process"*}
  lemma stop_process_presrv_wk_stp_cons_new:
  assumes p1:"is_a_partition sysconf (current s)"
    and   p2:"reachable0 s \<and> reachable0 t"
    and   p3:"s \<sim>. d .\<sim> t"
    and   p4:"s \<sim>. (scheduler sysconf) .\<sim> t"
    and   p5:"s \<sim>. (current s) .\<sim> t"
    and   p6:"s' = stop_process s pr"
    and   p7:"t' = stop_process t pr"
  shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'"
  using p1 p2 p3 p4 p5 p6 p7 by auto
  
  lemma stop_process_presrv_wk_stp_cons_new_e: "weak_step_consistent_new_e (hyperc' (Stop_Process p))"
    using stop_process_presrv_wk_stp_cons_new weak_step_consistent_new_e_def 
      exec_eventR_def same_part_mode sched_vpeq
          by (smt EventR.case(1) Hypercall'.case(16) State.select_convs(1) State.select_convs(2) 
                abstract_state_def domain_of_eventR_hc event_enabledR_hc mem_Collect_eq 
                singletonD vpeqR_def option.sel prod.simps(2))

subsubsection{*proving "suspend process"*}
  lemma suspend_process_presrv_wk_stp_cons_new:
    assumes p1:"is_a_partition sysconf (current s)"
      and   p2:"reachable0 s \<and> reachable0 t"
      and   p3:"s \<sim>. d .\<sim> t"
      and   p4:"s \<sim>. (scheduler sysconf) .\<sim> t"     
      and   p5:"s \<sim>. (current s) .\<sim> t"
      and   p6:"s' = suspend_process s pr"
      and   p7:"t' = suspend_process t pr"
    shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'"
using p1 p2 p3 p4 p5 p6 p7 by auto

  lemma suspend_process_presrv_wk_stp_cons_new_e: "weak_step_consistent_new_e (hyperc' (Suspend_Process p))"
    using suspend_process_presrv_wk_stp_cons_new weak_step_consistent_new_e_def 
      exec_eventR_def same_part_mode sched_vpeq
          by (smt EventR.case(1) Hypercall'.case(18) State.select_convs(1) State.select_convs(2) 
                abstract_state_def domain_of_eventR_hc event_enabledR_hc mem_Collect_eq 
                singletonD vpeqR_def option.sel prod.simps(2))

subsubsection{*proving "resume process"*}
  lemma resume_process_presrv_wk_stp_cons_new:
  assumes p1:"is_a_partition sysconf (current s)"
    and   p2:"reachable0 s \<and> reachable0 t"
    and   p3:"s \<sim>. d .\<sim> t"
    and   p4:"s \<sim>. (scheduler sysconf) .\<sim> t"
    and   p5:"s \<sim>. (current s) .\<sim> t"
    and   p6:"s' = resume_process s pr"
    and   p7:"t' = resume_process t pr"
  shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'"
  using p1 p2 p3 p4 p5 p6 p7 by auto

  lemma resume_process_presrv_wk_stp_cons_new_e: "weak_step_consistent_new_e (hyperc' (Resume_Process p))"
    using resume_process_presrv_wk_stp_cons_new weak_step_consistent_new_e_def 
      exec_eventR_def same_part_mode sched_vpeq
          by (smt EventR.case(1) Hypercall'.case(17) State.select_convs(1) State.select_convs(2) 
                abstract_state_def domain_of_eventR_hc event_enabledR_hc mem_Collect_eq 
                singletonD vpeqR_def option.sel prod.simps(2))

subsubsection{*proving "get process status"*}
  lemma get_process_status_presrv_wk_stp_cons_new:
      assumes p1:"s \<sim>. d .\<sim> t"
        and   p2:"s' = fst (get_process_status s pr)"
        and   p3:"t' = fst (get_process_status t pr)"
      shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'"
    proof -
      have a0:"s' = s" using p2 by auto 
      have a1:"t' = t" using p3 by auto 
      then show ?thesis using a0 p1 by auto
    qed

  lemma get_process_status_presrv_wk_stp_cons_new_e: "weak_step_consistent_new_e (hyperc' (Get_Process_Status p))"
    using get_process_status_presrv_wk_stp_cons_new weak_step_consistent_new_e_def 
      exec_eventR_def domain_of_eventR_def event_enabledR_def same_part_mode sched_vpeq 
      non_interference1_def non_interference_def singletonD 
          by (smt EventR.case(1) Hypercall'.case(20) State.select_convs(1) State.select_convs(2) 
                abstract_state_def domain_of_eventR_hc event_enabledR_hc mem_Collect_eq 
                singletonD vpeqR_def option.sel prod.simps(2))

subsubsection{*proving "schedule process"*}
  lemma setrun2ready_presrv_wk_stp_cons_new:
      assumes 
              p1:"s \<sim>. d .\<sim> t"
        and   p2:"s \<sim>. (scheduler sysconf) .\<sim> t"        
        and   p3:"s' = setRun2Ready s"
        and   p4:"t' = setRun2Ready t"
      shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'"
     using  p1 p2 p3 p4 by auto

  lemma schedule_process_presrv_wk_stp_cons_new:
    assumes p1:"is_a_partition sysconf (current s)"
      and   p2:"reachable0 s \<and> reachable0 t"
      and   p3:"s \<sim>. d .\<sim> t"
      and   p4:"s \<sim>. (scheduler sysconf) .\<sim> t"
      and   p5:"(current s) \<leadsto> d"
      and   p6:"s \<sim>. (current s) .\<sim> t"
      and   p7:"s' \<in> schedule_process s"
      and   p8:"t' \<in> schedule_process t"
    shows   "s' \<sim>. d .\<sim>\<^sub>\<Delta> t'"
   
    proof(cases "is_a_partition sysconf d")
      assume a0:"is_a_partition sysconf d"
      from p3 p4 have a1: "current s = current t" 
        using sched_currentR_lemma domain_of_eventR_hc
          by auto
      show ?thesis
      proof(cases "current s = d")
        assume b0: "current s = d"
        with p3 a0 have b1: "(partitions s) d = (partitions t) d" 
          using part_imp_not_sch part_imp_not_tras by force 
        from p3 a0 have b2: "vpeq_part_procs s d t" by (simp add: vpeqR_def)
        with p1 b0 have b3: "(procs s) d = (procs t) d \<and>
                       (\<forall>p. (proc_state s) (d,p) = (proc_state t) (d,p))\<and>
                       (cur_proc_part s) d = (cur_proc_part t) d" 
          by auto
        with p7 p8 have r1: "procs s' d = procs t' d" 
          using schedule_process_def setRun2Ready_def by (smt StateR.select_convs(1) StateR.surjective 
            StateR.update_convs(2) StateR.update_convs(3)  singletonD) 
        moreover
        have r2: "(cur_proc_part s') d = (cur_proc_part t') d \<and> (\<forall>p. (proc_state s') (d,p) = (proc_state t') (d,p))"
        proof -
          let ?cons = "is_a_partition sysconf (current s) 
                    \<and> part_mode (the ((partitions s) (current s))) = NORMAL"
          let ?cont = "is_a_partition sysconf (current t) 
                    \<and> part_mode (the ((partitions t) (current t))) = NORMAL"
          have b9: "?cons = ?cont" using a1 b0 b1 by auto 
          show ?thesis 
          proof(cases "?cons")
            assume c0: "?cons"            
            then have c1: "?cont" using b9 by simp
            let ?s' = "setRun2Ready s"
            let ?readyprs = "{p. p\<in>the (procs ?s' (current ?s')) \<and> 
                                    state (the (proc_state ?s' (current ?s',p))) = READY}"
            let ?selp = "SOME p. p\<in>{x. state (the (proc_state ?s' (current ?s',x))) = READY \<and>
                                                   (\<forall>y\<in>?readyprs. priority (the (proc_state ?s' (current ?s',x))) \<ge>
                                                                priority (the (proc_state ?s' (current ?s',y))))}"
            let ?st = "the ((proc_state ?s') (current ?s', ?selp))"
            let ?proc_st = "proc_state ?s'"
            let ?cur_pr = "cur_proc_part ?s'"
            from c0 have c2: "schedule_process s = {?s'\<lparr>proc_state := ?proc_st ((current ?s', ?selp) := Some (?st\<lparr>state := RUNNING\<rparr>)),
                                             cur_proc_part := ?cur_pr(current ?s' := Some ?selp)\<rparr>}"
              using schedule_process_def [of s] by auto
            
            let ?t' = "setRun2Ready t"
            let ?readyprst = "{p. p\<in>the (procs ?t' (current ?t')) \<and> 
                                    state (the (proc_state ?t' (current ?t',p))) = READY}"
            let ?selpt = "SOME p. p\<in>{x. state (the (proc_state ?t' (current ?t',x))) = READY \<and>
                                                     (\<forall>y\<in>?readyprst. priority (the (proc_state ?t' (current ?t',x))) \<ge>
                                                                  priority (the (proc_state ?t' (current ?t',y))))}"
            let ?stt = "the ((proc_state ?t') (current ?t', ?selpt))"
            let ?proc_stt = "proc_state ?t'"
            let ?cur_prt = "cur_proc_part ?t'"
            from c1 have c3: "schedule_process t = {?t'\<lparr>proc_state := ?proc_stt ((current ?t', ?selpt) := Some (?stt\<lparr>state := RUNNING\<rparr>)),
                                             cur_proc_part := ?cur_prt(current ?t' := Some ?selpt)\<rparr>}"
              using schedule_process_def [of t] by auto
            have c4: "?s' \<sim>. d .\<sim>\<^sub>\<Delta> ?t'"
              using b0 p1 p2 p4 p6 setrun2ready_presrv_wk_stp_cons_new 
              by (fastforce cong del:setRun2Ready_def vpeq_part_procs_def)
            then have c5: "((procs ?s') d = (procs ?t') d) \<and>
                        (\<forall>p. (proc_state ?s') (d,p) = (proc_state ?t') (d,p)) \<and>
                        (cur_proc_part ?s') d = (cur_proc_part ?t') d"
              using a0 by auto                         
            have c7: "current ?s' = current ?t'" using a1 
              by fastforce 
            have c8: "current s = current ?s'" using a1 setrun2ready_nchastate_lemma by fastforce                                                             
            then  show ?thesis using  p7 p8 c2 a0 c3 c5 a0 c7 c8 b0 a1 
             by (fastforce cong del: setRun2Ready_def)
          next
            assume c0: "\<not> ?cons"
            thus ?thesis using p7 p8 p3 b3 b9 by auto 
          qed        
        qed
        ultimately show ?thesis
          by auto
      next
        assume b0: "current s \<noteq> d"                        
        from  p8 p7 a0 a1 b0 p3   
        show ?thesis using schedule_process_vpeq_part_procs
          by (auto cong del: setRun2Ready_def)
      qed
    next
      assume b1:"\<not> is_a_partition sysconf d"
      then show ?thesis by auto
    qed

  lemma schedule_process_presrv_wk_stp_cons_new_e: "weak_step_consistent_new_e (sys' Schedule_Process)"
    using schedule_process_presrv_wk_stp_cons_new weak_step_consistent_new_e_def 
      exec_eventR_def same_part_mode sched_vpeq 
          by (smt EventR.case(2) System_EventR.case(4) State.select_convs(1) State.select_convs(2) 
                abstract_state_def domain_of_eventR_sys event_enabledR_sys mem_Collect_eq 
                singletonD vpeqR_def option.sel prod.simps(2))

subsection{* Proving the "step consistent" property on new state variables *}
  theorem weak_step_consistent_new:weak_step_consistent_new
    proof -
      {
        fix e
        have "weak_step_consistent_new_e e"
          apply(induct e)
          using crt_smpl_portR_presrv_wk_stp_cons_new_e wrt_smpl_msgR_presrv_wk_stp_cons_new_e 
                 read_smpl_msgR_presrv_wk_stp_cons_new_e get_smpl_pidR_presrv_wk_stp_cons_new_e
                 get_smpl_pstsR_presrv_wk_stp_cons_new_e crt_que_portR_presrv_wk_stp_cons_new_e 
                 snd_que_msg_lstR_presrv_wk_stp_cons_new_e rec_que_msgR_presrv_wk_stp_cons_new_e 
                 get_que_pidR_presrv_wk_stp_cons_new_e get_que_pstsR_presrv_wk_stp_cons_new_e
                 clr_que_portR_presrv_wk_stp_cons_new_e set_part_modeR_presrv_wk_stp_cons_new_e 
                 get_part_statusR_presrv_wk_stp_cons_new_e create_process_presrv_wk_stp_cons_new_e 
                 start_process_presrv_wk_stp_cons_new_e stop_process_presrv_wk_stp_cons_new_e
                 resume_process_presrv_wk_stp_cons_new_e suspend_process_presrv_wk_stp_cons_new_e 
                 set_process_priority_presrv_wk_stp_cons_new_e get_process_status_presrv_wk_stp_cons_new_e 
          apply(rule Hypercall'.induct)
          using scheduleR_presrv_wk_stp_cons_new_e trans_smpl_msgR_presrv_wk_stp_cons_new_e
              trans_que_msg_mlostR_presrv_wk_stp_cons_new_e schedule_process_presrv_wk_stp_cons_new_e
              by (rule System_EventR.induct)
      }
      then show ?thesis using weak_step_consistent_new_all_evt by simp
    qed

subsection{* Information flow security of second-level specification *}
  theorem noninfluence_sat: noninfluence
    using noninfl_refinement local_respect_new weak_step_consistent_new
      local_respect weak_step_consistent by blast

  theorem noninfluence_gen_sat: noninfluence_gen
    using noninf_eq_noninf_gen noninfluence_sat by blast 

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
