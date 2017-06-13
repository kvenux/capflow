(*
A refinement based formal specification and information flow security proofs 
for ARINC 653 compliant separation kernels
created by Yongwang ZHAO
School of Computer Science and Engineering, Nanyang Technological University, Singapore
School of Computer Science and Engineering, Beihang University, China
zhaoyongwang@gmail.com, ywzhao@ntu.edu.sg, zhaoyw@buaa.edu.cn
*)

section {* Top-level Specification and security proofs *}

theory SK_TopSpec
imports SK_SecurityModel
begin

declare [[ smt_timeout = 90 ]]

subsection {* Definitions *}

subsubsection {* Data type, basic components, and system configuration *}

type_synonym max_buffer_size = nat
type_synonym buffer_size = nat
typedecl Message

type_synonym partition_id = nat
type_synonym partition_name = string
type_synonym domain_id = nat
type_synonym channel_id = nat
type_synonym channel_name = string
datatype port_direction = SOURCE | DESTINATION
type_synonym port_name = string
type_synonym port_id = nat
datatype Port_Type = Queuing port_id port_name max_buffer_size port_direction "Message set"
                    | Sampling port_id port_name port_direction "Message option"
                                             
datatype Channel_Type = Channel_Sampling channel_name port_name "port_name set" 
                      | Channel_Queuing channel_name port_name port_name

record Communication_Config = 
          ports_conf :: "Port_Type set"
          channels_conf :: "Channel_Type set"

datatype partition_type = USER_PARTITION | SYSTEM_PARTITION
datatype partition_mode_type =  IDLE | WARM_START | COLD_START | NORMAL

datatype Partition_Conf = PartConf partition_id partition_name partition_type "port_name set" 

type_synonym Partitions = "partition_id \<rightharpoonup> Partition_Conf"
                                                                           
record Sys_Config = partconf :: Partitions
                    commconf :: Communication_Config
                    scheduler :: domain_id 
                    transmitter :: domain_id

subsubsection {* System state *}

type_synonym Ports = "port_id \<rightharpoonup> Port_Type"    

type_synonym Channels = "channel_id \<rightharpoonup> Channel_Type"
          
record Communication_State = 
          ports :: Ports         

record Partition_State_Type = 
                  part_mode :: partition_mode_type

type_synonym Partitions_State = "partition_id \<rightharpoonup> Partition_State_Type"

record State =
          current :: domain_id 
          partitions :: Partitions_State
          comm :: Communication_State                                 
          part_ports :: "port_id \<rightharpoonup> partition_id"          
                                                                       
subsubsection {* Events *}
                                                             
datatype Hypercall = Create_Sampling_Port port_name
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

typedecl Exception
typedecl PartitionAction
datatype System_Event = Schedule
                        | Transfer_Sampling_Message Channel_Type
                        | Transfer_Queuing_Message Channel_Type

datatype Event = hyperc Hypercall | sys System_Event

subsubsection {* Utility Functions used for Event Specification *}             

primrec get_partname_by_type :: "Partition_Conf \<Rightarrow> partition_name"
  where "get_partname_by_type (PartConf _ pn _ _) = pn"
                                                                           
primrec get_partid_by_type :: "Partition_Conf \<Rightarrow> partition_id"
  where "get_partid_by_type (PartConf pid _ _ _) = pid"

definition is_a_samplingport :: "State \<Rightarrow> port_id \<Rightarrow> bool" 
  where "is_a_samplingport s pid \<equiv> case ((ports (comm s)) pid) of 
                                        Some (Sampling _ _ _ _) \<Rightarrow> True | 
                                        _ \<Rightarrow> False"

definition is_a_queuingport :: "State \<Rightarrow> port_id \<Rightarrow> bool" 
  where "is_a_queuingport s pid \<equiv> case ((ports (comm s)) pid) of 
                                        Some (Queuing _ _ _ _ _) \<Rightarrow> True | 
                                        _ \<Rightarrow> False"

definition is_source_port :: "State \<Rightarrow> port_id \<Rightarrow> bool"
  where "is_source_port s pid \<equiv> 
          case ((ports (comm s)) pid) of 
              Some (Queuing _ _ _ SOURCE _) \<Rightarrow> True |
              Some (Sampling _ _ SOURCE _) \<Rightarrow> True |
              _ \<Rightarrow> False"

definition is_dest_port :: "State \<Rightarrow> port_id \<Rightarrow> bool"
  where "is_dest_port s pid \<equiv> 
            case ((ports (comm s)) pid) of 
                Some (Queuing _ _ _ DESTINATION _) \<Rightarrow> True |
                Some (Sampling _ _ DESTINATION _) \<Rightarrow> True |
                _ \<Rightarrow> False"

definition is_a_port_of_partition :: "State \<Rightarrow> port_id \<Rightarrow> partition_id \<Rightarrow> bool"
  where "is_a_port_of_partition s port part \<equiv> (part_ports s) port = Some part"

definition is_samplingport_name :: "Port_Type \<Rightarrow> port_name \<Rightarrow> bool" 
where
"is_samplingport_name p n 
   \<equiv> case p of 
       (Queuing _ name _ _ _)        \<Rightarrow> False
     | (Sampling _ name _ _) \<Rightarrow> name=n
"

definition is_queuingport_name :: "Port_Type \<Rightarrow> port_name \<Rightarrow> bool" 
where
"is_queuingport_name p n 
   \<equiv> case p of 
       (Queuing _ name _ _ _) \<Rightarrow> name = n
     | (Sampling _ name _ _) \<Rightarrow> False
"

definition is_port_name :: "Port_Type \<Rightarrow> port_name \<Rightarrow> bool" 
where
"is_port_name p n 
   \<equiv> case p of 
       (Queuing _ name _ _ _) \<Rightarrow> name = n
     | (Sampling _ name _ _) \<Rightarrow> name = n
"

definition get_samplingport_conf :: "Sys_Config \<Rightarrow> port_name \<Rightarrow> Port_Type option"
  where "get_samplingport_conf sc pname \<equiv> 
                  (if (\<exists>p. p \<in> ports_conf (commconf sc) \<and> is_samplingport_name p pname) 
                    then Some (SOME p . p \<in> ports_conf (commconf sc) \<and> is_samplingport_name p pname)
                    else None)"
                                                   
definition get_queuingport_conf :: "Sys_Config \<Rightarrow> port_name \<Rightarrow> Port_Type option"
  where "get_queuingport_conf sc pname \<equiv> 
              (if (\<exists>p. p \<in> ports_conf (commconf sc) \<and> is_queuingport_name p pname) 
                then Some (SOME p . p \<in> ports_conf (commconf sc) \<and> is_queuingport_name p pname)
                else None)"

definition get_portid_by_name :: "State \<Rightarrow> port_name \<Rightarrow> port_id option"
  where "get_portid_by_name s pn \<equiv> 
                  (if (\<exists>pid. is_port_name (the (ports (comm s) pid)) pn) 
                    then Some (SOME pid . is_port_name (the (ports (comm s) pid)) pn)
                    else None)"

definition get_portids_by_names :: "State \<Rightarrow> port_name set \<Rightarrow> (port_id option) set"
  where "get_portids_by_names s ps \<equiv>  {x. (\<exists>y. y \<in> ps \<and> x = get_portid_by_name s y)}"

definition get_portname_by_id :: "State \<Rightarrow> port_id \<Rightarrow> port_name option"
  where "get_portname_by_id s pid \<equiv> 
          let p = ports (comm s) pid in
            case p of Some (Queuing _ name _ _ _) \<Rightarrow> Some name
                    | Some (Sampling _ name _ _) \<Rightarrow> Some name
                    | None \<Rightarrow> None"

definition get_portname_by_type :: "Port_Type \<Rightarrow> port_name"
  where "get_portname_by_type pt \<equiv> case pt of (Queuing _ name _ _ _) \<Rightarrow> name
                                            | (Sampling _ name _ _) \<Rightarrow> name"

definition get_portid_in_type :: "Port_Type \<Rightarrow> port_id"
  where "get_portid_in_type pt \<equiv> case pt of (Queuing pid _ _ _ _) \<Rightarrow> pid
                                            | (Sampling pid _ _ _) \<Rightarrow> pid"
                                                                      
primrec get_partition_cfg_ports :: "Partition_Conf \<Rightarrow> port_name set"
  where "get_partition_cfg_ports (PartConf _ _ _ pset) = pset "


definition get_partition_cfg_ports_byid :: "Sys_Config \<Rightarrow> partition_id \<Rightarrow> port_name set"
  where "get_partition_cfg_ports_byid sc p \<equiv> 
              if (partconf sc) p = None 
              then {} 
              else get_partition_cfg_ports (the ((partconf sc) p) )"

definition get_ports_of_partition :: "State \<Rightarrow> partition_id \<Rightarrow> port_id set"
  where "get_ports_of_partition s p = {x. (part_ports s) x = Some p}"

primrec get_msg_from_samplingport :: "Port_Type \<Rightarrow> Message option"
  where "get_msg_from_samplingport (Sampling _ _ _ msg) = msg" |
        "get_msg_from_samplingport (Queuing _ _ _ _ _) = None"

primrec get_msgs_from_queuingport :: "Port_Type \<Rightarrow> (Message set) option"
  where "get_msgs_from_queuingport (Sampling _ _ _ _) = None" |
        "get_msgs_from_queuingport (Queuing _ _ _ _ msgs) = Some msgs"

definition get_port_byid :: "State \<Rightarrow> port_id \<Rightarrow> Port_Type option"
  where "get_port_byid s pid \<equiv>  ports (comm s) pid"

definition get_the_msg_of_samplingport :: "State \<Rightarrow> port_id \<Rightarrow> Message option"
  where "get_the_msg_of_samplingport s pid \<equiv> 
            let ps = get_port_byid s pid in
                 if ps = None then None else get_msg_from_samplingport (the ps)"

definition get_the_msgs_of_queuingport :: "State \<Rightarrow> port_id \<Rightarrow> (Message set) option"
  where "get_the_msgs_of_queuingport s pid \<equiv>
            let ps = get_port_byid s pid in
                 if ps = None then None else get_msgs_from_queuingport (the ps)"

definition get_port_conf_byid :: "Sys_Config \<Rightarrow> State \<Rightarrow> port_id \<Rightarrow> Port_Type option"
  where "get_port_conf_byid sc s pid \<equiv> ports (comm s) pid"

primrec is_channel_srcname :: "Channel_Type \<Rightarrow> port_name \<Rightarrow> bool"
  where "is_channel_srcname (Channel_Sampling _ n _) name = (name = n)" | 
        "is_channel_srcname (Channel_Queuing _ n _) name = (name = n)"

primrec is_channel_destname :: "Channel_Type \<Rightarrow> port_name \<Rightarrow> bool"
  where "is_channel_destname (Channel_Sampling _ _ ns) name = (name \<in> ns)" | 
        "is_channel_destname (Channel_Queuing _ _ n) name = (name = n)"

definition get_channel_bysrcport_id :: "Sys_Config \<Rightarrow> State \<Rightarrow> port_id \<Rightarrow> Channel_Type option"
  where "get_channel_bysrcport_id sc s pid \<equiv> 
          let nm = get_portname_by_id s pid in
              if \<exists>x. x\<in> channels_conf (commconf sc) \<and> is_channel_srcname x (the nm) then
                let c' = SOME c. c\<in>channels_conf (commconf sc) \<and> is_channel_srcname c (the nm) in
                  Some c'
              else None"

definition get_destports_bysrcport :: "Sys_Config \<Rightarrow> State \<Rightarrow> port_id \<Rightarrow> (port_id option) set"
  where "get_destports_bysrcport sc s pid \<equiv> 
          let c = get_channel_bysrcport_id sc s pid in
            case c of Some (Channel_Sampling _ _ ps) \<Rightarrow> get_portids_by_names s ps| 
                      Some (Channel_Queuing _ _ p) \<Rightarrow> insert (get_portid_by_name s p) {}| 
                      None \<Rightarrow> {}"

definition update_sampling_port_msg :: "State \<Rightarrow> port_id \<Rightarrow> Message \<Rightarrow> State"
  where "update_sampling_port_msg s pid m \<equiv>  
            case ((ports (comm s)) pid) of 
              Some (Sampling spid name d msg) \<Rightarrow> 
                (let cs = comm s;
                     pts = ports cs
                 in s\<lparr>comm := 
                      cs\<lparr> ports := pts(pid := Some (Sampling spid name d (Some m))) \<rparr> 
                     \<rparr> 
                ) 
              |
              _ \<Rightarrow> s"

definition st_msg_destspl_ports :: "(port_id \<Rightarrow> Port_Type option) \<Rightarrow> 
                        (port_id option) set \<Rightarrow> Message \<Rightarrow> 
                        (port_id \<Rightarrow> Port_Type option)" 
  where "st_msg_destspl_ports f a b \<equiv> 
        % x. (case f x of Some (Sampling spid name d msg) \<Rightarrow> Some (Sampling spid name d (Some b)) |
                      _ \<Rightarrow> f x)"

definition update_sampling_ports_msg :: "State \<Rightarrow> (port_id option) set \<Rightarrow> Message \<Rightarrow> State"
  where "update_sampling_ports_msg s st m = 
            (let cs = comm s;
                 pts = ports cs
             in s\<lparr>comm := 
                  cs\<lparr> ports := st_msg_destspl_ports pts st m \<rparr> 
                 \<rparr> 
            )  "

definition insert_msg2queuing_port :: "State \<Rightarrow> port_id
        \<Rightarrow> Message \<Rightarrow> State"
  where "insert_msg2queuing_port s pid m \<equiv>
            case ((ports (comm s)) pid) of 
                Some (Queuing spid name maxs d msgs)
                  \<Rightarrow> (let cs = comm s;
                        pts = ports cs
                        in s\<lparr>comm := 
                              cs\<lparr> ports := pts( pid := Some (Queuing spid name maxs d (insert m msgs))) \<rparr>
                            \<rparr>
                     )
                | _ \<Rightarrow> s"

definition replace_msg2queuing_port :: "State \<Rightarrow> port_id \<Rightarrow> Message \<Rightarrow> State"
  where "replace_msg2queuing_port s pid m \<equiv> s"

definition remove_msg_from_queuingport :: "State \<Rightarrow> port_id \<Rightarrow> (State \<times> Message option)"
  where "remove_msg_from_queuingport s pid \<equiv>
            case ((ports (comm s)) pid) of 
                Some (Queuing spid name maxs d msgs)
                  \<Rightarrow> (let cs = comm s;
                          pts = ports cs;
                          m = SOME x. x\<in>msgs
                        in (s\<lparr>comm := 
                              cs\<lparr> ports := pts( pid := Some (Queuing spid name maxs d (msgs - {m}))) \<rparr>
                            \<rparr>,Some m)
                     )
                | _ \<Rightarrow> (s,None)"

definition clear_msg_queuingport :: "Port_Type \<Rightarrow> Port_Type"
  where "clear_msg_queuingport pt \<equiv> (case pt of (Queuing spid name maxs d _) \<Rightarrow> (Queuing spid name maxs d {}) |
                                                 _ \<Rightarrow> pt)"

definition is_a_partition :: "Sys_Config \<Rightarrow> domain_id \<Rightarrow> bool"
  where "is_a_partition sc nid \<equiv> (partconf sc) nid \<noteq> None"

definition is_a_transmitter :: "Sys_Config \<Rightarrow> domain_id \<Rightarrow> bool"
  where "is_a_transmitter sc nid \<equiv> (transmitter sc) = nid"

definition is_a_scheduler :: "Sys_Config \<Rightarrow> domain_id \<Rightarrow> bool"
  where "is_a_scheduler sc nid \<equiv> (scheduler sc) = nid"

definition is_a_syspart :: "Sys_Config \<Rightarrow> partition_id \<Rightarrow> bool"
  where "is_a_syspart sc pid \<equiv> let p = (partconf sc) pid in
                                    case p of Some (PartConf _ _ SYSTEM_PARTITION _) \<Rightarrow> True | 
                                              _ \<Rightarrow> False"

definition is_a_normpart :: "Sys_Config \<Rightarrow> partition_id \<Rightarrow> bool"
  where "is_a_normpart sc pid \<equiv> let p = (partconf sc) pid in
                                    case p of Some (PartConf _ _ USER_PARTITION _) \<Rightarrow> True | 
                                              _ \<Rightarrow> False"

definition is_there_a_channel_2parts :: "Sys_Config \<Rightarrow> partition_id \<Rightarrow> partition_id \<Rightarrow> bool"
  where "is_there_a_channel_2parts sc p1 p2 \<equiv> 
              let ps1 = get_partition_cfg_ports_byid sc p1;
                  ps2 = get_partition_cfg_ports_byid sc p2 in
                    (\<exists>c. c\<in> channels_conf (commconf sc) \<and> 
                          (case c of (Channel_Sampling _ sp dps) \<Rightarrow> sp\<in>ps1 \<and> ps2\<inter>dps\<noteq>{} | 
                                      (Channel_Queuing _ sp dp) \<Rightarrow> sp\<in>ps1 \<and> dp\<in>ps2
                          )
                    )"

definition part_intf_transmitter :: "Sys_Config \<Rightarrow> partition_id \<Rightarrow> bool"
  where "part_intf_transmitter sc p \<equiv> (let pns = get_partition_cfg_ports (the ((partconf sc) p)) in
                                      (\<exists>ch pn. ch\<in>channels_conf (commconf sc) \<and> pn\<in>pns \<longrightarrow> 
                                            is_channel_srcname ch pn \<or> is_channel_destname ch pn))"

definition transmitter_intf_part :: "Sys_Config \<Rightarrow> partition_id \<Rightarrow> bool"
  where "transmitter_intf_part sc p \<equiv> (let pns = get_partition_cfg_ports (the ((partconf sc) p)) in
                                      (\<exists>ch pn. ch\<in>channels_conf (commconf sc) \<and> 
                                                pn\<in>pns \<longrightarrow> is_channel_destname ch pn ))"

primrec get_max_bufsize_of_port :: "Port_Type \<Rightarrow> max_buffer_size"
  where "get_max_bufsize_of_port (Queuing _ _ n _ _) = n" |
        "get_max_bufsize_of_port (Sampling _ _ _ _) = 1"

primrec get_current_bufsize_port :: "Port_Type \<Rightarrow> buffer_size"
  where "get_current_bufsize_port (Queuing _ _ _ _ ms) = card ms" |
        "get_current_bufsize_port (Sampling _ _ _ m) = (if m = None then 0 else 1)"

definition is_full_portqueuing :: "Sys_Config \<Rightarrow> State \<Rightarrow> port_id \<Rightarrow> bool"
  where "is_full_portqueuing sc s p \<equiv> 
        let conf = get_port_conf_byid sc s p; 
              st = get_port_byid s p in
                get_max_bufsize_of_port (the conf) = get_current_bufsize_port (the st)"

definition is_empty_port :: "State \<Rightarrow> port_id \<Rightarrow> bool"
  where "is_empty_port s p \<equiv> 
        let st = get_port_byid s p in
              get_current_bufsize_port (the st) = 0"

definition get_port_buf_size :: "State \<Rightarrow> port_id \<Rightarrow> buffer_size"
  where "get_port_buf_size s p \<equiv> 
        let st = get_port_byid s p in
              get_current_bufsize_port (the st)"

definition is_empty_portqueuing :: "State \<Rightarrow> port_id \<Rightarrow> bool"
  where "is_empty_portqueuing s p \<equiv> 
      let st = get_port_byid s p in
            get_current_bufsize_port (the st) = 0"

definition is_empty_portsampling :: "State \<Rightarrow> port_id \<Rightarrow> bool"
  where "is_empty_portsampling s p \<equiv> 
            let st = get_port_byid s p in
                get_current_bufsize_port (the st) = 0"

definition has_msg_inportqueuing :: "State \<Rightarrow> port_id \<Rightarrow> bool"
  where "has_msg_inportqueuing s pid \<equiv> 
            case ((ports (comm s)) pid) of 
                Some (Queuing _ _ _ _ msgs)
                  \<Rightarrow> card msgs \<noteq> 0
                | _ \<Rightarrow> False"

definition get_partconf_byid :: "Sys_Config \<Rightarrow> partition_id \<Rightarrow> Partition_Conf option"
  where "get_partconf_byid sc pid \<equiv> (partconf sc) pid"

definition get_partstate_byid :: "State \<Rightarrow> partition_id \<Rightarrow> Partition_State_Type option"
  where "get_partstate_byid s pid \<equiv> (partitions s) pid"

subsubsection{* Event specification *}

definition create_sampling_port :: "Sys_Config \<Rightarrow> State \<Rightarrow> port_name \<Rightarrow> (State \<times> port_id option)" where
  "create_sampling_port sc s p \<equiv> 
            if (get_samplingport_conf sc p = None                      
                 \<or> get_portid_by_name s p \<noteq> None                
                \<or> p \<notin> get_partition_cfg_ports_byid sc (current s))
            then (s,None)
            else
              let cs = comm s;                 
                  pts = ports cs; 
                  partpts = part_ports s;
                  part = current s;
                  newid = get_portid_in_type (the (get_samplingport_conf sc p)) in                  
              (s\<lparr>comm := cs\<lparr> ports := pts(newid := get_samplingport_conf sc p)\<rparr>,
                part_ports := partpts(newid := Some part)
               \<rparr>, Some newid)
        "

definition write_sampling_message :: "State \<Rightarrow> port_id \<Rightarrow> Message \<Rightarrow> (State \<times> bool)" where
  "write_sampling_message s p m \<equiv> 
              (if(\<not> is_a_samplingport s p
                \<or> \<not> is_source_port s p
                \<or> \<not> is_a_port_of_partition s p (current s))
              then (s, False)
              else (update_sampling_port_msg s p m, True))"

definition read_sampling_message :: "State \<Rightarrow> port_id \<Rightarrow> (State \<times> Message option)" where
  "read_sampling_message s pid \<equiv> 
              (if (\<not> is_a_samplingport s pid
                \<or> \<not> is_a_port_of_partition s pid (current s)
                \<or> \<not> is_dest_port s pid)
              then (s, None)
              else if is_empty_portsampling s pid then
                (s, None)
              else
                (s, get_the_msg_of_samplingport s pid)
              )"

definition get_sampling_port_id :: "Sys_Config \<Rightarrow> State \<Rightarrow> port_name \<Rightarrow> (State \<times> port_id option)" where
  "get_sampling_port_id sc s pname \<equiv> 
          (if (pname \<notin> get_partition_cfg_ports_byid sc (current s))
          then (s, None)                             
          else (s, get_portid_by_name s pname))"

definition get_sampling_port_status :: "Sys_Config \<Rightarrow> State \<Rightarrow> port_id \<Rightarrow> (State \<times> Port_Type option)" where
  "get_sampling_port_status sc s pid \<equiv> (s, get_port_conf_byid sc s pid)"

definition create_queuing_port :: "Sys_Config \<Rightarrow> State \<Rightarrow> port_name \<Rightarrow> (State \<times> port_id option)" where
  "create_queuing_port sc s p \<equiv>          
            if (get_queuingport_conf sc p = None
                 \<or> get_portid_by_name s p \<noteq> None
                \<or> p \<notin> get_partition_cfg_ports_byid sc (current s))
            then (s,None)
            else
              let cs = comm s; 
                  pts = ports cs; 
                  part = current s;
                  partpts = part_ports s;
                  newid = get_portid_in_type (the (get_queuingport_conf sc p)) in
              (s\<lparr>comm :=
                cs\<lparr> ports := pts(newid := get_queuingport_conf sc p)\<rparr>,
                 part_ports := partpts(newid := Some part)
               \<rparr>, Some newid)"

definition send_queuing_message_maylost :: "Sys_Config \<Rightarrow> State \<Rightarrow> port_id \<Rightarrow> Message \<Rightarrow> (State \<times> bool)" where
  "send_queuing_message_maylost sc s p m \<equiv> 
              (if(\<not> is_a_queuingport s p
                \<or> \<not> is_source_port s p
                \<or> \<not> is_a_port_of_partition s p (current s))
              then (s, False)
              else if is_full_portqueuing sc s p then
                (replace_msg2queuing_port s p m, True)
              else
                (insert_msg2queuing_port s p m, True))"

definition receive_queuing_message :: "State \<Rightarrow> port_id \<Rightarrow> (State \<times> Message option)" where
  "receive_queuing_message s pid \<equiv> 
              (if (\<not> is_a_queuingport s pid 
                \<or> \<not> is_a_port_of_partition s pid (current s)
                \<or> \<not> is_dest_port s pid 
                \<or> is_empty_portqueuing s pid)
              then (s, None)
              else remove_msg_from_queuingport s pid
              )"

definition get_queuing_port_id :: "Sys_Config \<Rightarrow> State \<Rightarrow> port_name \<Rightarrow> (State \<times> port_id option)" where
  "get_queuing_port_id sc s pname \<equiv> 
          (if (pname \<notin> get_partition_cfg_ports_byid sc (current s))
          then (s, None) 
          else (s, get_portid_by_name s pname))"         

definition get_queuing_port_status :: "Sys_Config \<Rightarrow> State \<Rightarrow> port_id \<Rightarrow> (State \<times> Port_Type option)" where
  "get_queuing_port_status sc s pid \<equiv> (s, get_port_conf_byid sc s pid)"

definition clear_queuing_port :: "State \<Rightarrow> port_id \<Rightarrow> State" where
  "clear_queuing_port s pid \<equiv> 
          (if (\<not> is_a_queuingport s pid
                \<or> \<not> is_a_port_of_partition s pid (current s)
                \<or> \<not> is_dest_port s pid)
          then s
          else 
            let cs = comm s;
                pts = ports cs;
                pt = (ports cs) pid
              in s\<lparr>comm := 
                    cs\<lparr> ports := pts( pid := Some (clear_msg_queuingport (the pt))) \<rparr>
                  \<rparr>
           
          )"

definition schedule :: "Sys_Config \<Rightarrow> State \<Rightarrow> State set" where
  "schedule sc s \<equiv> {s\<lparr>current:= SOME p. p\<in>{x. (partconf sc) x \<noteq> None \<or> x = transmitter sc}\<rparr>}"

definition get_partition_status :: "Sys_Config \<Rightarrow> State \<Rightarrow> (State \<times> (Partition_Conf option) \<times> (Partition_State_Type option))" where
  "get_partition_status sc s \<equiv> (s, (get_partconf_byid sc (current s), get_partstate_byid s (current s)))"

definition set_partition_mode :: "Sys_Config \<Rightarrow> State \<Rightarrow> partition_mode_type \<Rightarrow> State" where
  "set_partition_mode sc s m \<equiv> 
      (if (partconf sc) (current s) \<noteq> None \<and> (partitions s) (current s) \<noteq> None \<and>
          \<not> (part_mode (the ((partitions s) (current s))) = COLD_START \<and> m = WARM_START) then
        let pts = partitions s;
            pstate = the (pts (current s))
        in s\<lparr>partitions := pts(current s := Some (pstate\<lparr>part_mode := m\<rparr>))\<rparr>
      else
        s)
  "

primrec transf_sampling_msg :: "State \<Rightarrow> Channel_Type \<Rightarrow> State" where
  "transf_sampling_msg s (Channel_Sampling _ sn dns) = 
          (let sp = get_portid_by_name s sn;
              dps = get_portids_by_names s dns in
                if sp\<noteq>None \<and> card dps = card dns then 
                  let m = the (get_the_msg_of_samplingport s (the sp)) in
                    update_sampling_ports_msg s dps m
                else
                  s
            )" |
  "transf_sampling_msg s (Channel_Queuing _ _ _) = s"

primrec transf_queuing_msg_maylost :: "Sys_Config \<Rightarrow> State \<Rightarrow> Channel_Type \<Rightarrow> State" where
  "transf_queuing_msg_maylost sc s (Channel_Queuing _ sn dn) = 
          (let sp = get_portid_by_name s sn;
                dp = get_portid_by_name s dn in
                  if sp \<noteq> None \<and> dp \<noteq> None \<and> has_msg_inportqueuing s (the sp) then
                    let sm = remove_msg_from_queuingport s (the sp) in
                      if is_full_portqueuing sc (fst sm) (the dp) then
                        replace_msg2queuing_port (fst sm) (the dp) (the (snd sm))
                      else
                        insert_msg2queuing_port (fst sm) (the dp) (the (snd sm)) 
                  else s
                )" |
  "transf_queuing_msg_maylost sc s (Channel_Sampling _ _ _) = s"

definition system_init :: "Sys_Config \<Rightarrow> State"
  where "system_init sc \<equiv> \<lparr>current=(SOME x. (partconf sc) x\<noteq>None),
                            partitions=(\<lambda> p. (
                                            case ((partconf sc) p) of 
                                                None \<Rightarrow> None |
                                                (Some (PartConf _ _ _ _)) \<Rightarrow> Some (\<lparr>part_mode=IDLE\<rparr>) 
                                              )                             
                                        ),                                  
                            comm = \<lparr>ports=(\<lambda> x. None)\<rparr>,
                            part_ports = (\<lambda> x. None)
                           \<rparr>"                                 

subsection{* Instantiation and Its Proofs of Security Model  *}

consts sysconf :: "Sys_Config" 

definition sys_config_witness :: Sys_Config 
where 
"sys_config_witness \<equiv> \<lparr> partconf = Map.empty, 
                        commconf = \<lparr> ports_conf = {}, channels_conf = {}\<rparr>, 
                        scheduler = 0, 
                        transmitter = 1 \<rparr>" 

specification (sysconf) 
  part_id_conf:"\<forall>p. (partconf sysconf) p \<noteq> None \<longrightarrow> get_partid_by_type (the ((partconf sysconf) p)) = p"
  part_not_sch:"(partconf sysconf) x \<noteq> None \<Longrightarrow> x\<noteq>scheduler sysconf" 
  part_not_trans : "(partconf sysconf) x \<noteq> None \<Longrightarrow> x\<noteq>transmitter sysconf" 
  sch_not_part : "scheduler sysconf = x \<Longrightarrow> (partconf sysconf) x = None"
  trans_not_part : "transmitter sysconf = x \<Longrightarrow> (partconf sysconf) x = None"
  sch_not_trans : "scheduler sysconf \<noteq> transmitter sysconf"
  port_name_diff:"\<forall>p1 p2. p1 \<in> ports_conf (commconf sysconf) \<and> p2 \<in> ports_conf (commconf sysconf) 
                           \<longrightarrow> get_portname_by_type p1 \<noteq> get_portname_by_type p2"
  port_partition:"\<forall>p1 p2. get_partition_cfg_ports_byid sysconf p1 \<inter> get_partition_cfg_ports_byid sysconf p2 = {}"
    apply (intro exI[of _ "sys_config_witness"] allI impI, simp) 
    apply (rule conjI, simp add: sys_config_witness_def)+
    by (simp add: get_partition_cfg_ports_byid_def sys_config_witness_def)

consts s0t :: State
definition s0t_witness :: State
  where "s0t_witness \<equiv> system_init sysconf"

specification (s0t) 
  s0t_init: "s0t = system_init sysconf"
  by simp               
                                   
primrec event_enabled :: "State \<Rightarrow> Event \<Rightarrow> bool"
  where "event_enabled s (hyperc h) = (is_a_partition sysconf (current s) 
                                      \<and> part_mode (the (partitions s (current s))) \<noteq> IDLE)" |
        "event_enabled s (sys h) =  (case h of Schedule \<Rightarrow> True |
                                               Transfer_Sampling_Message c \<Rightarrow> (current s = transmitter sysconf) |
                                               Transfer_Queuing_Message c \<Rightarrow> (current s = transmitter sysconf))" 

definition exec_event :: "Event \<Rightarrow> (State \<times> State) set" where   
  "exec_event e = {(s,s'). s'\<in> (if event_enabled s e then (
      case e of hyperc (Create_Sampling_Port pname) \<Rightarrow> {fst (create_sampling_port sysconf s pname)} |
                hyperc (Write_Sampling_Message p m) \<Rightarrow> {fst (write_sampling_message s p m)} |
                hyperc (Read_Sampling_Message p) \<Rightarrow> {fst (read_sampling_message s p)} |
                hyperc (Get_Sampling_Portid pname) \<Rightarrow> {fst (get_sampling_port_id sysconf s pname)} |
                hyperc (Get_Sampling_Portstatus p) \<Rightarrow> {fst (get_sampling_port_status sysconf s p)} |
                hyperc (Create_Queuing_Port pname) \<Rightarrow> {fst (create_queuing_port sysconf s pname)} |
                hyperc (Send_Queuing_Message p m) \<Rightarrow> {fst (send_queuing_message_maylost sysconf s p m)} |
                hyperc (Receive_Queuing_Message p) \<Rightarrow> {fst (receive_queuing_message s p)} |
                hyperc (Get_Queuing_Portid pname) \<Rightarrow> {fst (get_queuing_port_id sysconf s pname)} |
                hyperc (Get_Queuing_Portstatus p) \<Rightarrow> {fst (get_queuing_port_status sysconf s p)} |
                hyperc (Clear_Queuing_Port p) \<Rightarrow> {clear_queuing_port s p} |
                hyperc (Set_Partition_Mode m) \<Rightarrow> {set_partition_mode sysconf s m} |
                hyperc (Get_Partition_Status) \<Rightarrow> {fst (get_partition_status sysconf s)} |
                sys Schedule \<Rightarrow>  schedule sysconf s |
                sys (Transfer_Sampling_Message c) \<Rightarrow> {transf_sampling_msg s c} |
                sys (Transfer_Queuing_Message c) \<Rightarrow> {transf_queuing_msg_maylost sysconf s c} )
                    else {s})}"                                                                  

primrec domain_of_event :: "State \<Rightarrow> Event \<Rightarrow> domain_id option"
where "domain_of_event s (hyperc h) = Some (current s)" |
      "domain_of_event s (sys h) =  (case h of Schedule \<Rightarrow> Some (scheduler sysconf) |
                                               Transfer_Sampling_Message c \<Rightarrow> Some (transmitter sysconf) |
                                               Transfer_Queuing_Message c \<Rightarrow> Some (transmitter sysconf) )"

definition interference1 :: "domain_id \<Rightarrow> domain_id \<Rightarrow> bool" ("(_ \<leadsto> _)")
    where                                                                                                  
      "interference1 d1 d2 \<equiv>             
          if d1 = d2 then True
          else if is_a_scheduler sysconf d1 then True 
          else if \<not>(is_a_scheduler sysconf d1) \<and> (is_a_scheduler sysconf d2) then False
          else if is_a_partition sysconf d1 \<and> is_a_transmitter sysconf d2 then part_intf_transmitter sysconf d1
          else if is_a_transmitter sysconf d1 \<and> is_a_partition sysconf d2 then transmitter_intf_part sysconf d2
          else False"

definition non_interference1 :: "domain_id \<Rightarrow> domain_id \<Rightarrow> bool" ("(_ \<setminus>\<leadsto> _)")
      where "(u \<setminus>\<leadsto>  v) \<equiv> \<not> (u \<leadsto> v)"

declare non_interference1_def [cong] and interference1_def [cong] and domain_of_event_def[cong] and
       event_enabled_def[cong] and is_a_partition_def[cong] and is_a_transmitter_def[cong] and
       is_a_scheduler_def[cong] and is_a_syspart_def[cong] and is_a_normpart_def[cong] and
      transmitter_intf_part_def[cong] and part_intf_transmitter_def[cong]

lemma nintf_neq: "u \<setminus>\<leadsto>  v \<Longrightarrow> u \<noteq> v"  by auto

lemma nintf_reflx: "interference1 u u" by auto
 
definition vpeq_part_comm :: "State \<Rightarrow> partition_id \<Rightarrow> State \<Rightarrow> bool"
  where "vpeq_part_comm s d t \<equiv>  
          (let ps1 = get_ports_of_partition s d;
                ps2 = get_ports_of_partition t d in
                  (ps1 = ps2) \<and> 
                  (\<forall>p. p\<in>ps1 \<longrightarrow> 
                   (is_a_queuingport s p = is_a_queuingport t p) \<and>
                   (is_dest_port s p = is_dest_port t p) \<and>
                   (if is_dest_port s p then
                      get_port_buf_size s p = get_port_buf_size t p
                    else True)
                  )
          )" 

definition vpeq_part :: "State \<Rightarrow> partition_id \<Rightarrow> State \<Rightarrow> bool"
  where "vpeq_part s d t \<equiv> (partitions s) d = (partitions t) d \<and> vpeq_part_comm s d t" 

definition vpeq_transmitter :: "State \<Rightarrow> domain_id \<Rightarrow> State \<Rightarrow> bool"
  where "vpeq_transmitter s d t \<equiv>  comm s = comm t \<and> part_ports s = part_ports t"

definition vpeq_sched :: "State \<Rightarrow> domain_id \<Rightarrow> State \<Rightarrow> bool"
  where "vpeq_sched s d t \<equiv> current s = current t"

definition vpeq1  :: "State \<Rightarrow> domain_id \<Rightarrow> State \<Rightarrow> bool" ("(_ \<sim> _ \<sim> _)") 
  where "vpeq1 s d t \<equiv>  
         (if d = scheduler sysconf then 
            (vpeq_sched s d t)
          else if d = transmitter sysconf then
            (vpeq_transmitter s d t)
          else if is_a_partition sysconf d then 
            (vpeq_part s d t)
          else True)"

declare vpeq_part_comm_def [cong] and 
        vpeq_part_def [cong] and Let_def [cong] and vpeq_transmitter_def[cong] and
        vpeq_sched_def[cong] and vpeq1_def[cong] 

lemma vpeq_part_comm_transitive_lemma : 
  "\<forall> s t r d. vpeq_part_comm s d t \<and> vpeq_part_comm t d r \<longrightarrow> vpeq_part_comm s d r" 
    by auto

lemma vpeq_part_comm_symmetric_lemma:"\<forall> s t d. vpeq_part_comm s d t \<longrightarrow> vpeq_part_comm t d s" 
  by auto

lemma vpeq_part_comm_reflexive_lemma:"\<forall> s d. vpeq_part_comm s d s"
  by auto

lemma vpeq_part_transitive_lemma : "\<forall> s t r d. vpeq_part s d t \<and> vpeq_part t d r \<longrightarrow> vpeq_part s d r"
  by auto

lemma vpeq_part_symmetric_lemma:"\<forall> s t d. vpeq_part s d t \<longrightarrow> vpeq_part t d s"
  by auto

lemma vpeq_part_reflexive_lemma:"\<forall> s d. vpeq_part s d s"
  by auto

lemma vpeq_transmitter_transitive_lemma : 
  "\<forall> s t r d. vpeq_transmitter s d t \<and> vpeq_transmitter t d r 
                                          \<longrightarrow> vpeq_transmitter s d r"
 by simp

lemma vpeq_transmitter_symmetric_lemma:"\<forall> s t d. vpeq_transmitter s d t \<longrightarrow> vpeq_transmitter t d s"
  by simp
                                                        
lemma vpeq_transmitter_reflexive_lemma:"\<forall> s d. vpeq_transmitter s d s"
  by auto

lemma vpeq_scheduler_transitive_lemma : "\<forall> s t r d. vpeq_sched s d t \<and> vpeq_sched t d r \<longrightarrow> vpeq_sched s d r"
 by simp

lemma vpeq_scheduler_symmetric_lemma:"\<forall> s t d. vpeq_sched s d t \<longrightarrow> vpeq_sched t d s"
  by simp

lemma vpeq_scheduler_reflexive_lemma:"\<forall> s d. vpeq_sched s d s"
  by simp

lemma vpeq1_transitive_lemma : "\<forall> s t r d. (vpeq1 s d t) \<and> (vpeq1 t d r) \<longrightarrow> (vpeq1 s d r)"
  by auto

lemma vpeq1_symmetric_lemma : "\<forall> s t d. (vpeq1 s d t) \<longrightarrow> (vpeq1 t d s)"
  by auto

lemma vpeq1_reflexive_lemma : "\<forall> s d. (vpeq1 s d s)"
  by auto

lemma sched_current_lemma : "\<forall>s t a. vpeq1 s (scheduler sysconf) t \<longrightarrow> (domain_of_event s a) = (domain_of_event t a)"
  by (metis (full_types) Event.exhaust domain_of_event.simps(1) domain_of_event.simps(2) vpeq1_def vpeq_sched_def)
  
lemma schedeler_intf_all_help : "\<forall>d. interference1 (scheduler sysconf) d"
  by auto 

lemma no_intf_sched_help : "\<forall>d. interference1 d (scheduler sysconf) \<longrightarrow> d = (scheduler sysconf)"
  by auto 

lemma reachable_top: "\<forall>s a. (SM.reachable0 s0t exec_event) s \<longrightarrow> (\<exists>s'. (s, s') \<in> exec_event a)"
  proof -
  {
    fix s a
    assume p0: "(SM.reachable0 s0t exec_event) s"
    have "\<exists>s'. (s, s') \<in> exec_event a"
      proof(induct a)
        case (hyperc x) show ?case 
          apply (induct x)
          by (simp add:exec_event_def)+
        next
        case (sys x) then show ?case
          apply (induct x)
          by (simp add:exec_event_def schedule_def)+
      qed        
  }
  then show ?thesis by auto
  qed

interpretation SM_enabled 
    s0t exec_event domain_of_event "scheduler sysconf" vpeq1 interference1 
  using vpeq1_transitive_lemma vpeq1_symmetric_lemma vpeq1_reflexive_lemma sched_current_lemma
        schedeler_intf_all_help no_intf_sched_help reachable_top nintf_reflx
        SM.intro[of vpeq1 "scheduler sysconf" domain_of_event interference1]
        SM_enabled_axioms.intro [of s0t exec_event] 
        SM_enabled.intro[of domain_of_event "scheduler sysconf" vpeq1 interference1 s0t exec_event] by blast

subsection{* Correctness for top-level specification *}
subsubsection{* Correctness lemmas *}
    lemma create_sampling_port_cor:"\<lbrakk>r = create_sampling_port sysconf s p; (snd r) \<noteq> None\<rbrakk> 
      \<Longrightarrow> (ports (comm (fst r))) (the (snd r)) \<noteq> None"
        by (metis create_sampling_port_def get_samplingport_conf_def port_name_diff snd_conv)
    
    lemma create_sampling_port_prepost:
      assumes p1:"get_samplingport_conf sysconf p \<noteq> None"
        and   p2:"get_portid_by_name s p = None"
        and   p3:"p \<in> get_partition_cfg_ports_byid sysconf (current s)"
        and   p4:"r = create_sampling_port sysconf s p"
       shows  "(ports (comm (fst r))) (the (snd r)) \<noteq> None"
       by (metis create_sampling_port_cor create_sampling_port_def option.distinct(2) p1 p2 p3 p4 sndI)
      
    lemma write_sampling_message_cor:
      assumes p1:"r = write_sampling_message s pid m"
        and   p2:"(snd r) \<noteq> False"
        shows "the (get_the_msg_of_samplingport (fst r) pid) = m"
      proof -
        let ?sp = "(ports (comm (fst r))) pid"
        let ?s' = "fst r"
        have a1:"r = (update_sampling_port_msg s pid m, True)" 
          by (metis eq_snd_iff p1 p2 write_sampling_message_def)         
        have a2:"is_a_samplingport s pid" using p1 p2 write_sampling_message_def by fastforce 
        then have a3:"get_port_byid s pid \<noteq> None" 
          unfolding is_a_samplingport_def get_port_byid_def by (metis option.case_eq_if)
        show ?thesis
          proof(induct "(ports (comm s)) pid")
            case None show ?thesis using None.hyps a3 get_port_byid_def by auto 
          next
            case (Some pt)
            have b0:"(ports (comm s)) pid = Some pt" by (simp add: Some.hyps)
            show ?thesis
            proof(induct "the ((ports (comm s)) pid)")
              case (Queuing x1 x2 x3 x4 x5) 
              have "the ((ports (comm s)) pid) = Queuing x1 x2 x3 x4 x5" by (simp add: Queuing.hyps) 
                  with a2 show ?thesis by (simp add: b0 is_a_samplingport_def) 
            next
              case (Sampling x1 x2 x3 x4) 
                have c0:"the (ports (comm ?s') pid) = Sampling x1 x2 x3 (Some m)"
                  by (smt Communication_State.select_convs(1) Communication_State.surjective 
                    Communication_State.update_convs(1) Port_Type.simps(6) Sampling.hyps 
                    State.select_convs(3) State.surjective State.update_convs(3) a1 b0 
                    fstI fun_upd_same option.case_eq_if option.distinct(2) option.sel update_sampling_port_msg_def)
                then have c1:"get_the_msg_of_samplingport ?s' pid = get_msg_from_samplingport (the (get_port_byid ?s' pid))"
                  unfolding get_the_msg_of_samplingport_def get_port_byid_def
                    by (smt Communication_State.select_convs(1) Communication_State.surjective 
                      Communication_State.update_convs(1) Port_Type.simps(6) Sampling.hyps 
                      State.select_convs(3) State.surjective State.update_convs(3) a1 b0 
                      fstI fun_upd_same option.case_eq_if option.distinct(2) update_sampling_port_msg_def) 
                then show ?thesis by (simp add: c0 get_port_byid_def)  
            qed
          qed
        qed

    lemma write_sampling_message_prepost:
      assumes p1:"r = write_sampling_message s pid m"
        and   p2:"is_a_samplingport s pid"
        and   p3:"is_source_port s pid"
        and   p4:"is_a_port_of_partition s pid (current s)"
        shows "the (get_the_msg_of_samplingport (fst r) pid) = m"
      by (metis p1 p2 p3 p4 sndI write_sampling_message_cor write_sampling_message_def)
       

    lemma read_sampling_message_cor:
      assumes p1:"r = read_sampling_message s pid"
        shows "fst r = s \<and> (((snd r) \<noteq> None) \<longrightarrow> (snd r) = get_the_msg_of_samplingport s pid)"     
      by (simp add: p1 read_sampling_message_def)
      
    lemma read_sampling_message_prepost:
      assumes p1:"r = read_sampling_message s pid"
          and p2:"is_a_samplingport s pid"
          and p3:"is_dest_port s pid"
          and p4:"is_a_port_of_partition s pid (current s)"
          and p5:"\<not> is_empty_portsampling s pid"
        shows "(snd r) = get_the_msg_of_samplingport s pid"
        by (simp add: p1 p2 p3 p4 p5 read_sampling_message_def)
        
    lemma get_sampling_port_id_cor:
      assumes p1:"r = get_sampling_port_id sysconf s pname"
        shows "fst r = s \<and> (((snd r) \<noteq> None) \<longrightarrow> (snd r) = get_portid_by_name s pname)"
      proof(rule conjI)
        show "fst r = s" by (simp add: get_sampling_port_id_def p1) 
        show "((snd r) \<noteq> None) \<longrightarrow> (snd r) = get_portid_by_name s pname"
          by (simp add: get_sampling_port_id_def p1) 
      qed

    lemma get_sampling_port_id_prepost:
      assumes p1:"r = get_sampling_port_id sysconf s pname"
        and   p2:"pname \<in> get_partition_cfg_ports_byid sysconf (current s)"
        shows "(snd r) = get_portid_by_name s pname"
        by (simp add: get_sampling_port_id_def p1 p2)

    lemma get_sampling_port_status_prepost:
      assumes p1:"r = get_sampling_port_status sysconf s pid"
        shows "fst r = s \<and> ((snd r) = get_port_conf_byid sc s pid)"
        using get_port_conf_byid_def get_sampling_port_status_def p1 by auto
        
    lemma create_queuing_ports_cor:"\<lbrakk>r = create_queuing_port sysconf s p; (snd r) \<noteq> None\<rbrakk> 
      \<Longrightarrow> (ports (comm (fst r))) (the (snd r)) \<noteq> None"
        by (metis create_queuing_port_def get_queuingport_conf_def port_name_diff snd_conv)  

    lemma create_queuing_ports_prepost:
      assumes p1:"r = create_queuing_port sysconf s p"
          and p2:"get_queuingport_conf sysconf p \<noteq> None"
          and p3:"get_portid_by_name s p = None"
          and p4:"p \<in> get_partition_cfg_ports_byid sysconf (current s)"
        shows "(ports (comm (fst r))) (the (snd r)) \<noteq> None"
        by (metis create_queuing_port_def create_queuing_ports_cor option.distinct(1) p1 p2 p3 p4 sndI)

    lemma send_queuing_message_maylost_cor:
     assumes p1:"r = send_queuing_message_maylost sysconf s pid m"
      and   p2:"(snd r) \<noteq> False"
      shows "(is_full_portqueuing sysconf s pid \<longrightarrow> ((fst r) = s)) 
            \<and> (\<not> is_full_portqueuing sysconf s pid \<longrightarrow> m \<in> (the (get_the_msgs_of_queuingport (fst r) pid)) )"
    proof(rule conjI)
      show "is_full_portqueuing sysconf s pid \<longrightarrow> ((fst r) = s)" 
        using p1 p2 unfolding send_queuing_message_maylost_def
        by (simp add: replace_msg2queuing_port_def)
      show "\<not> is_full_portqueuing sysconf s pid \<longrightarrow> m \<in> (the (get_the_msgs_of_queuingport (fst r) pid)) "
      proof -
      {
        assume a0:"\<not> is_full_portqueuing sysconf s pid"
        have a1:"is_a_queuingport s pid" using p1 p2 send_queuing_message_maylost_def by fastforce
        let ?s' = "fst r"
        have "m \<in> (the (get_the_msgs_of_queuingport (fst r) pid))"
        proof -
          have b0:"?s' = insert_msg2queuing_port s pid m" 
            using p1 p2 a0 unfolding send_queuing_message_maylost_def by auto
          then show ?thesis
          proof(induct "(ports (comm s)) pid")
            case None show ?thesis using None.hyps a1 is_a_queuingport_def by auto 
          next
            case (Some pt)
            have c0:"(ports (comm s)) pid = Some pt" by (simp add: Some.hyps)
            show ?thesis
            proof(induct "the ((ports (comm s)) pid)")
              case (Sampling x1 x2 x3 x4) 
              have "the ((ports (comm s)) pid) = Sampling x1 x2 x3 x4" by (simp add: Sampling.hyps) 
              with a1 show ?thesis by (simp add: c0 is_a_queuingport_def) 
            next
              case (Queuing x1 x2 x3 x4 x5)
              have a1:"the ((ports (comm s)) pid) = Queuing x1 x2 x3 x4 x5" by (simp add: Queuing.hyps) 
              with b0 c0 have a2:"(ports (comm ?s')) pid = Some (Queuing x1 x2 x3 x4 (insert m x5))"
                unfolding insert_msg2queuing_port_def by (smt Communication_State.select_convs(1) 
                  Communication_State.surjective Communication_State.update_convs(1) Port_Type.simps(5) 
                  State.ext_inject State.surjective State.update_convs(3) fun_upd_same option.sel option.simps(5)) 
              then show ?thesis unfolding get_the_msgs_of_queuingport_def Let_def get_port_byid_def by simp
            qed
          qed
        qed
      }
      then show ?thesis by auto
      qed
    qed
           
   lemma send_queuing_message_maylost_prepost:
     assumes p1:"r = send_queuing_message_maylost sysconf s pid m"
      and   p2:"is_a_queuingport s pid"
      and   p3:"is_source_port s pid"
      and   p4:"is_a_port_of_partition s pid (current s)"
      and   p5:"\<not> is_full_portqueuing sysconf s pid"
      shows "m \<in> (the (get_the_msgs_of_queuingport (fst r) pid))"
      by (metis p1 p2 p3 p4 p5 send_queuing_message_maylost_cor send_queuing_message_maylost_def sndI)

   lemma receive_queuing_message_cor:
     assumes p1:"r = receive_queuing_message s pid"
      and   p2:"(snd r) \<noteq> None"
      shows "the (snd r) \<notin> (the (get_the_msgs_of_queuingport (fst r) pid))"
    proof -
      from p1 p2 have a1:"is_a_queuingport s pid" by (metis receive_queuing_message_def snd_conv) 
      from p2 have a2:"r = remove_msg_from_queuingport s pid" using p1 receive_queuing_message_def by auto[1]
      then show ?thesis
      proof(induct "(ports (comm s)) pid")
        case None show ?thesis using None.hyps a1 is_a_queuingport_def by auto 
      next
        case (Some pt)
        have b1:"(ports (comm s)) pid = Some pt" by (simp add: Some.hyps) 
        show ?thesis
        proof(induct "the ((ports (comm s)) pid)")
          case (Sampling x1 x2 x3 x4)
          have c1:"pt = Sampling x1 x2 x3 x4" by (simp add: Sampling.hyps b1) 
          then show ?thesis using a1 b1 is_a_queuingport_def by auto 
        next
          case (Queuing x1 x2 x3 x4 x5)
          have c1:"pt = Queuing x1 x2 x3 x4 x5" by (simp add: Queuing.hyps b1) 
          then have "(ports (comm (fst r))) pid = Some (Queuing x1 x2 x3 x4 (x5 - {the (snd r)}))"
            by (smt Communication_State.select_convs(1) Communication_State.surjective 
              Communication_State.update_convs(1) Port_Type.case(1) Queuing.hyps State.ext_inject 
              State.surjective State.update_convs(3) a1 a2 fstI fun_upd_same is_a_queuingport_def 
              option.case_eq_if option.sel remove_msg_from_queuingport_def sndI)
          then show ?thesis by (simp add: get_port_byid_def get_the_msgs_of_queuingport_def) 
        qed
      qed
    qed

    lemma receive_queuing_message_prepost:
       assumes p1:"r = receive_queuing_message s pid"
        and   p2:"is_a_queuingport s pid"
        and   p3:"is_dest_port s pid"
        and   p4:"is_a_port_of_partition s pid (current s)"
        and   p5:"\<not> is_empty_portqueuing s pid"
        shows "the (snd r) \<notin> (the (get_the_msgs_of_queuingport (fst r) pid))"
    proof -
      from p1 p2 p3 p4 p5 have a0:"r = remove_msg_from_queuingport s pid"
        by (simp add: receive_queuing_message_def) 
      then show ?thesis
      proof(induct "(ports (comm s)) pid")
        case None show ?thesis using None.hyps is_dest_port_def p3 by auto 
      next
        case (Some x) 
        have a1:"x = the ((ports (comm s)) pid)" by (metis Some.hyps option.sel) 
        then show ?thesis
        proof(induct "the ((ports (comm s)) pid)")
          case (Queuing x1 x2 x3 x4 x5)
          have b1:"x = Queuing x1 x2 x3 x4 x5" by (simp add: Queuing.hyps a1) 
          then have "(ports (comm (fst r))) pid = Some (Queuing x1 x2 x3 x4 (x5 - {the (snd r)}))"
          proof -
            have "Some (Queuing x1 x2 x3 x4 x5) = ports (comm s) pid"
              using Some.hyps b1 by blast
            hence "remove_msg_from_queuingport s pid = (case Some (Queuing x1 x2 x3 x4 x5) of None 
                      \<Rightarrow> (s, None) | Some (Queuing n cs na p M) \<Rightarrow> 
                          (s\<lparr>comm := comm s \<lparr>ports := ports (comm s)(pid \<mapsto> Queuing n cs na p (M - {SOME m. m \<in> M}))\<rparr>\<rparr>, 
                          Some (SOME m. m \<in> M)) | Some (Sampling n cs p z) \<Rightarrow> (s, None))"
              by (metis remove_msg_from_queuingport_def)
            thus ?thesis
              by (simp add: Some(2))
           qed 
           then show ?thesis by (simp add: get_port_byid_def get_the_msgs_of_queuingport_def) 
        next
          case (Sampling x1 x2 x3 x4)
          have c1:"x = Sampling x1 x2 x3 x4" by (simp add: Sampling.hyps a1) 
          then show ?thesis
          proof -
            have "case Some x of None \<Rightarrow> False | Some (Queuing n cs na p M) \<Rightarrow> True 
                | Some (Sampling n cs p z) \<Rightarrow> False"
              using Some.hyps is_a_queuingport_def p2 by presburger
            thus ?thesis
              using c1 by force
          qed                 
        qed
      qed
    qed

    lemma get_queuing_port_id_cor:
      assumes p1:"r = get_queuing_port_id sysconf s pname"
        shows "fst r = s \<and> (((snd r) \<noteq> None) \<longrightarrow> (snd r) = get_portid_by_name s pname)"
    proof(rule conjI)
      show "fst r = s" by (simp add: get_queuing_port_id_def p1) 
      show "((snd r) \<noteq> None) \<longrightarrow> (snd r) = get_portid_by_name s pname"
        by (simp add: get_queuing_port_id_def p1) 
    qed
    
    lemma get_queuing_port_id_prepost:
      assumes p1:"r = get_queuing_port_id sysconf s pname"
          and p2:"pname \<in> get_partition_cfg_ports_byid sysconf (current s)"
        shows "(snd r) = get_portid_by_name s pname"
        by (simp add: get_queuing_port_id_def p1 p2)

    lemma get_queuing_port_status_prepost:
      assumes p1:"r = get_queuing_port_status sysconf s pid"
        shows "fst r = s \<and> ((snd r) = get_port_conf_byid sc s pid)"
        using get_port_conf_byid_def get_queuing_port_status_def p1 by auto

  lemma clear_queuing_port_cor:
     assumes p1:"r = clear_queuing_port s pid"
      and   p2:"r \<noteq> s"
      shows "the (get_the_msgs_of_queuingport r pid) = {}"
  proof -
    from p1 p2 have a1:"is_a_queuingport s pid" by (metis clear_queuing_port_def) 
    then show ?thesis
    proof(induct "(ports (comm s)) pid")
      case None show ?thesis using None.hyps a1 is_a_queuingport_def by auto 
     next
      case (Some pt)
      have b1:"(ports (comm s)) pid = Some pt" by (simp add: Some.hyps) 
      show ?thesis
      proof(induct "the ((ports (comm s)) pid)")
        case (Sampling x1 x2 x3 x4)
        have c1:"pt = Sampling x1 x2 x3 x4" by (simp add: Sampling.hyps b1) 
        then show ?thesis using a1 b1 is_a_queuingport_def by auto 
      next
        case (Queuing x1 x2 x3 x4 x5)
        have c1:"pt = Queuing x1 x2 x3 x4 x5" by (simp add: Queuing.hyps b1) 
        with p1 a1 b1 c1 have "(ports (comm r)) pid = Some (Queuing x1 x2 x3 x4 {})"
          unfolding clear_queuing_port_def clear_msg_queuingport_def 
            by (smt Communication_State.select_convs(1) 
            Communication_State.surjective Communication_State.update_convs(1) 
            Port_Type.simps(5) Queuing.hyps State.select_convs(3) State.surjective 
            State.update_convs(3) fun_upd_same p2) 
        then show ?thesis by (simp add: get_port_byid_def get_the_msgs_of_queuingport_def)  
      qed
    qed
  qed

  lemma clear_queuing_port_prepost:
     assumes p1:"r = clear_queuing_port s pid"
      and   p2:"is_a_queuingport s pid"
      and   p3:"is_dest_port s pid"
      and   p4:"is_a_port_of_partition s pid (current s)"
      shows "the (get_the_msgs_of_queuingport r pid) = {}"
     proof(induct "(ports (comm s)) pid")
       case None show ?thesis using None.hyps is_a_queuingport_def p2 by auto  
     next
      case (Some pt)
      have b1:"(ports (comm s)) pid = Some pt" by (simp add: Some.hyps) 
      show ?thesis
      proof(induct "the ((ports (comm s)) pid)")
        case (Sampling x1 x2 x3 x4)
        have c1:"pt = Sampling x1 x2 x3 x4" by (simp add: Sampling.hyps b1) 
        then show ?thesis using b1 is_a_queuingport_def p2 by auto  
      next
        case (Queuing x1 x2 x3 x4 x5)
        have c1:"pt = Queuing x1 x2 x3 x4 x5" by (simp add: Queuing.hyps b1) 
        with p1 p2 b1 c1 have "(ports (comm r)) pid = Some (Queuing x1 x2 x3 x4 {})"
          unfolding clear_queuing_port_def clear_msg_queuingport_def
          proof -
            assume "r = (if \<not> is_a_queuingport s pid \<or> \<not> is_a_port_of_partition s pid (current s) 
                          \<or> \<not> is_dest_port s pid then s 
                         else let cs = comm s; pts = ports cs; pt = ports cs pid 
                            in s\<lparr>comm := cs \<lparr>ports := pts(pid \<mapsto> case the pt of 
                                  Queuing spid name maxs d x \<Rightarrow> Queuing spid name maxs d {} | 
                                  Sampling spid list port_direction option \<Rightarrow> the pt)\<rparr>\<rparr>)"
            hence "r = s \<lparr>comm := comm s \<lparr>ports := ports (comm s)(pid \<mapsto> case the (ports (comm s) pid) of 
                          Queuing n cs na p M \<Rightarrow> Queuing n cs na p {} | 
                          Sampling n cs p z \<Rightarrow> the (ports (comm s) pid))\<rparr>\<rparr>"
              by (metis (full_types) p2 p3 p4)
            hence "ports (comm r) pid = Some (case the (ports (comm s) pid) of 
                  Queuing n cs na p M \<Rightarrow> Queuing n cs na p {} | 
                  Sampling n cs p z \<Rightarrow> the (ports (comm s) pid))"
              by simp
            thus ?thesis
              by (metis (no_types) Port_Type.simps(5) Queuing.hyps)
          qed            
        then show ?thesis by (simp add: get_port_byid_def get_the_msgs_of_queuingport_def)  
      qed
    qed


subsubsection{* Invariants: port consistent *}

    definition get_ports_util :: "(port_id \<rightharpoonup> 'a) \<Rightarrow> port_id set"
      where "get_ports_util f \<equiv> {x. f x \<noteq> None}"

    definition port_consistent :: "State \<Rightarrow> bool"
      where "port_consistent s \<equiv> \<forall>p. ((part_ports s) p \<noteq> None) = ((ports (comm s)) p \<noteq> None) \<and>
                                      ((ports (comm s)) p \<noteq> None \<longrightarrow> p = get_portid_in_type (the ((ports (comm s)) p))) \<and>
                                      ((ports (comm s)) p \<noteq> None \<longrightarrow> get_portname_by_type (the ((ports (comm s)) p)) 
                                        \<in> get_partition_cfg_ports_byid sysconf (the ((part_ports s) p)) )"
                                     
    lemma pt_cons_s0 : "port_consistent s0t"       
      by(clarsimp simp:port_consistent_def s0t_init system_init_def)

    lemma crt_smpl_port_presrv_pt_cons:
    assumes p1:"port_consistent s"
      and   p2:"s' = fst (create_sampling_port sysconf s pname)"
    shows   "port_consistent s'"
    proof -
    {
      fix p
      have "(part_ports s' p \<noteq> None) = (ports (comm s') p \<noteq> None) 
            \<and> ((ports (comm s')) p \<noteq> None \<longrightarrow> p = get_portid_in_type (the ((ports (comm s')) p)))
            \<and> ((ports (comm s')) p \<noteq> None \<longrightarrow> get_portname_by_type (the ((ports (comm s')) p)) 
                                      \<in> get_partition_cfg_ports_byid sysconf (the ((part_ports s') p)) )" 
      proof(cases "get_samplingport_conf sysconf pname = None 
                    \<or> get_portid_by_name s pname \<noteq> None 
                    \<or> pname \<notin> get_partition_cfg_ports_byid sysconf (current s)")
        assume b0:"get_samplingport_conf sysconf pname = None 
                    \<or> get_portid_by_name s pname \<noteq> None 
                    \<or> pname \<notin> get_partition_cfg_ports_byid sysconf (current s)"
        have "s' = s" using b0 create_sampling_port_def p2 by auto 
        then show ?thesis using p1 port_consistent_def by blast  
      next
        assume b1:"\<not> (get_samplingport_conf sysconf pname = None 
                    \<or> get_portid_by_name s pname \<noteq> None 
                    \<or> pname \<notin> get_partition_cfg_ports_byid sysconf (current s))"
        then show ?thesis 
          proof(cases "p=get_portid_in_type (the (get_samplingport_conf sysconf pname))")
            assume c0:"p=get_portid_in_type (the (get_samplingport_conf sysconf pname))"
            show ?thesis using b1 port_partition by fastforce 
          next
            assume c1:"p \<noteq> get_portid_in_type (the (get_samplingport_conf sysconf pname))"
            show ?thesis
            proof(cases "part_ports s p \<noteq> None")
              assume d0:"part_ports s p \<noteq> None"
              have d1:"(ports (comm s)) p \<noteq> None" using d0 p1 port_consistent_def by auto 
              have d7:"p = get_portid_in_type (the ((ports (comm s)) p))" using d1 p1 port_consistent_def by auto 
              have d3:"part_ports s' p \<noteq> None" using b1 port_partition by fastforce 
              have d4:"(ports (comm s')) p \<noteq> None" using b1 port_partition by fastforce 
              have d6:"p = get_portid_in_type (the ((ports (comm s')) p))"
              proof -
                obtain pp :: "Sys_Config \<Rightarrow> char list \<Rightarrow> Port_Type" where
                  "pp sysconf pname \<in> ports_conf (commconf sysconf)"
                  by (meson b1 get_samplingport_conf_def)
                then show ?thesis
                  by (metis port_name_diff)
              qed
              have d8:"(ports (comm s')) p = (ports (comm s)) p"
                using b1 port_partition by auto
              have d9:"(part_ports s') p = (part_ports s) p"
                using b1 port_partition by fastforce
              have d10:"get_portname_by_type (the ((ports (comm s')) p)) 
                              \<in> get_partition_cfg_ports_byid sysconf (the ((part_ports s') p))"
                       using d1 d8 d9 p1 port_consistent_def by auto
              then show ?thesis using d3 d4 d6 p1 port_consistent_def by auto 
            next
              assume e0:"\<not> (part_ports s p \<noteq> None)"
              have e1:"(ports (comm s)) p = None" using e0 p1 port_consistent_def by blast  
              have e3:"part_ports s' p = None"
                using b1 port_partition by auto
              have e4:"(ports (comm s')) p = None" using b1 port_partition by auto
              then show ?thesis by (simp add: e1 e3 e4)  
            qed            
          qed
      qed
    }
    then show ?thesis unfolding port_consistent_def by blast
    qed

    lemma write_smpl_msg_presrv_pt_cons:
    "\<lbrakk>port_consistent s; s' = fst (write_sampling_message s pid msg)\<rbrakk> \<Longrightarrow> port_consistent s'"
      apply(clarsimp simp:exec_event_def)
      apply(clarsimp simp:write_sampling_message_def 
                        update_sampling_port_msg_def)
      apply(case_tac "ports (comm s) pid")
      apply simp
      apply(case_tac "a")
      apply simp 
      by (metis Int_absorb empty_iff option.distinct(1) port_consistent_def port_partition)

    lemma crt_que_port_presrv_pt_cons:
      assumes p1:"port_consistent s"
        and   p2:"s' = fst (create_queuing_port sysconf s pname)"
      shows   "port_consistent s'"
      proof -
      {
        fix p
        have "(part_ports s' p \<noteq> None) = (ports (comm s') p \<noteq> None) 
              \<and> ((ports (comm s')) p \<noteq> None \<longrightarrow> p = get_portid_in_type (the ((ports (comm s')) p)))
              \<and> ((ports (comm s')) p \<noteq> None \<longrightarrow> get_portname_by_type (the ((ports (comm s')) p)) 
                                        \<in> get_partition_cfg_ports_byid sysconf (the ((part_ports s') p)) )"
        proof(cases "get_queuingport_conf sysconf pname = None 
                      \<or> get_portid_by_name s pname \<noteq> None
                      \<or> pname \<notin> get_partition_cfg_ports_byid sysconf (current s)")
          assume b0:"get_queuingport_conf sysconf pname = None 
                      \<or> get_portid_by_name s pname \<noteq> None
                      \<or> pname \<notin> get_partition_cfg_ports_byid sysconf (current s)"
          then show ?thesis using create_queuing_port_def eq_fst_iff 
              p1 p2 port_consistent_def by auto
        next
          assume b1:"\<not> (get_queuingport_conf sysconf pname = None 
                      \<or> get_portid_by_name s pname \<noteq> None
                      \<or> pname \<notin> get_partition_cfg_ports_byid sysconf (current s))"
          then show ?thesis
          proof(cases "p=get_portid_in_type (the (get_queuingport_conf sysconf pname))")
            assume c0:"p=get_portid_in_type (the (get_queuingport_conf sysconf pname))"
            show ?thesis using b1 port_partition by fastforce 
          next
            assume c1:"p \<noteq> get_portid_in_type (the (get_queuingport_conf sysconf pname))"
            show ?thesis
            proof(cases "part_ports s p \<noteq> None")
              assume d0:"part_ports s p \<noteq> None"
              have d1:"(ports (comm s)) p \<noteq> None" using d0 p1 port_consistent_def by auto 
              have d3:"part_ports s' p \<noteq> None"  using b1 port_partition by fastforce 
              have d7:"p = get_portid_in_type (the ((ports (comm s)) p))" 
                using d1 p1 port_consistent_def by auto 
              have d4:"(ports (comm s')) p \<noteq> None" using b1 port_partition by auto 
              have d6:"p = get_portid_in_type (the ((ports (comm s')) p))"
                using b1 port_partition by auto
              have d8:"(ports (comm s')) p = (ports (comm s)) p"
                using b1 port_partition by auto
              have d9:"(part_ports s') p = (part_ports s) p"
                using b1 port_partition by auto
              have d10:"get_portname_by_type (the ((ports (comm s')) p)) 
                              \<in> get_partition_cfg_ports_byid sysconf (the ((part_ports s') p))"
                using d1 d8 d9 p1 port_consistent_def by auto
              then show ?thesis using d3 d4 d6 p1 port_consistent_def by auto 
            next
              assume e0:"\<not> (part_ports s p \<noteq> None)"
              have e1:"(ports (comm s)) p = None" using e0 p1 port_consistent_def by auto  
              have e3:"part_ports s' p = None" using b1 port_partition by auto 
              have e4:"(ports (comm s')) p = None" using b1 port_partition by auto 
              then show ?thesis by (simp add: e1 e3 e4) 
            qed
          qed
        qed
      }
      then show ?thesis unfolding port_consistent_def by blast
      qed

      lemma st_msg_destspl_ports_nchg_ports : 
      assumes   p1:"nports = st_msg_destspl_ports oports pids m"
      shows   "\<forall>x. (oports x \<noteq> None) = (nports x \<noteq> None)"
      proof - 
      {
        fix x
        have "(oports x \<noteq> None) = (nports x \<noteq> None)"
        proof(cases "oports x = None")
          assume a0:"oports x = None"
          with p1 have "nports x = None" unfolding st_msg_destspl_ports_def by simp
          with a0 show ?thesis by simp
        next
          assume b0:"oports x \<noteq> None"
          show ?thesis
            proof(induct "the (oports x)")
              case (Queuing x1 x2 x3 x4 x5) 
              have c1:"oports x = Some (Queuing x1 x2 x3 x4 x5)" by (simp add: Queuing.hyps b0)  
              with p1 have "nports x = Some (Queuing x1 x2 x3 x4 x5)" 
                unfolding st_msg_destspl_ports_def by simp
              with c1 show ?case by simp
            next
              case (Sampling x1 x2 x3 x4)
              have c1:"oports x = Some (Sampling x1 x2 x3 x4)" by (simp add: Sampling.hyps b0)  
              with p1 have "nports x = Some (Sampling x1 x2 x3 (Some m))" 
                unfolding st_msg_destspl_ports_def by simp
              with c1 show ?case by simp
            qed
        qed
      }
      then show ?thesis by auto
      qed

     lemma update_sampling_ports_msg_nchg_ports:
      assumes   p1:"s' = update_sampling_ports_msg s pts m"
      shows   "\<forall>x. ((ports (comm s)) x \<noteq> None) = ((ports (comm s')) x \<noteq> None) \<and>
                    ((part_ports s) x \<noteq> None) = ((part_ports s') x \<noteq> None)"
     proof - 
       {fix x
       have " ((part_ports s) x \<noteq> None) = ((part_ports s') x \<noteq> None)"
         by (metis State.ext_inject State.surjective State.update_convs(3) p1 update_sampling_ports_msg_def)
       also have "((ports (comm s)) x \<noteq> None) = ((ports (comm s')) x \<noteq> None)"
       proof -
         fix x :: nat
         have "\<lparr>ports = ports (comm s'), \<dots> = Communication_State.more (comm s')\<rparr> 
          = comm (update_sampling_ports_msg s pts m)"
           by (metis Communication_State.surjective p1)
         then have "\<lparr>ports = st_msg_destspl_ports (ports (comm 
           \<lparr>current = current s, partitions = partitions s, comm = comm s, part_ports = part_ports s, \<dots> = State.more s\<rparr>)) 
           pts m, \<dots> = Communication_State.more (comm s)\<rparr> = \<lparr>ports = ports (comm s'), \<dots> = Communication_State.more (comm s')\<rparr>"
           by (metis (no_types) Communication_State.surjective Communication_State.update_convs(1) 
             State.ext_inject State.surjective State.update_convs(3) update_sampling_ports_msg_def)
         then have "(ports (comm s) x \<noteq> None) \<noteq> (ports (comm s') x = None)"
           by (metis (no_types) Communication_State.ext_inject State.surjective st_msg_destspl_ports_nchg_ports)
         then show "(ports (comm s) x \<noteq> None) = (ports (comm s') x \<noteq> None)"
           by satx
      qed 
      ultimately have "((ports (comm s)) x \<noteq> None) = ((ports (comm s')) x \<noteq> None) \<and>
                    ((part_ports s) x \<noteq> None) = ((part_ports s') x \<noteq> None)" by auto
      } thus ?thesis by blast      
    qed


    lemma trans_spl_msg_presrv_pt_cons:"port_consistent s \<Longrightarrow> port_consistent (transf_sampling_msg s ch)"
    proof -
    {
      assume a0:"port_consistent s"
      show ?thesis
      proof(induct ch)
        case (Channel_Sampling cn sn dns) show ?case
        proof(clarsimp simp:transf_sampling_msg_def Let_def,rule conjI,rule impI)
          show "(\<exists>y. get_portid_by_name s sn = Some y) \<and> card (get_portids_by_names s dns) = card dns \<Longrightarrow>
                  port_consistent (update_sampling_ports_msg s (get_portids_by_names s dns)
                     (the (get_the_msg_of_samplingport s (the (get_portid_by_name s sn)))))"
          proof -
          {
            let ?s' = "update_sampling_ports_msg s (get_portids_by_names s dns)
                      (the (get_the_msg_of_samplingport s (the (get_portid_by_name s sn))))"
            from a0 have b0:"\<forall>p. ((part_ports s p \<noteq> None) = (ports (comm s) p \<noteq> None)) 
                      \<and> ((ports (comm s)) p \<noteq> None \<longrightarrow> p = get_portid_in_type (the ((ports (comm s)) p)))
                      \<and> ((ports (comm s)) p \<noteq> None \<longrightarrow> get_portname_by_type (the ((ports (comm s)) p)) 
                              \<in> get_partition_cfg_ports_byid sysconf (the ((part_ports s) p)) )"
                      using port_consistent_def by auto 
            have b1:"\<forall>x. ((ports (comm s)) x \<noteq> None) = ((ports (comm ?s')) x \<noteq> None) \<and>
              ((part_ports s) x \<noteq> None) = ((part_ports ?s') x \<noteq> None)"
              using update_sampling_ports_msg_nchg_ports by presburger 
            have b2:"\<forall>x. ((ports (comm ?s')) x \<noteq> None \<longrightarrow> x = get_portid_in_type (the ((ports (comm ?s')) x)))"
              using b0 b1 port_partition by fastforce
            have b3:"\<forall>x. ((ports (comm ?s')) x \<noteq> None \<longrightarrow> get_portname_by_type (the ((ports (comm ?s')) x)) 
                              \<in> get_partition_cfg_ports_byid sysconf (the ((part_ports ?s') x)) )"
                     by (metis Int_absorb b0 emptyE port_partition update_sampling_ports_msg_nchg_ports) 
            with b0 b1 b2 have "port_consistent ?s'" using port_consistent_def by metis
          }
          then show ?thesis by auto
          qed
          show "(get_portid_by_name s sn = None \<longrightarrow> port_consistent s) \<and>
                (card (get_portids_by_names s dns) \<noteq> card dns \<longrightarrow> port_consistent s)"
            by (simp add: a0) 
        qed
        case (Channel_Queuing cn sn dn) show ?case by (simp add: a0) 
      qed
    }
    qed

    lemma remove_msg_from_queuingport_presv_port_cons:
    assumes   p1:"s' = fst (remove_msg_from_queuingport s pt)"
      and     p2:"port_consistent s"
    shows   "port_consistent s'"
    proof(induct "(ports (comm s)) pt")
      case None  show ?thesis by (simp add: None.hyps option.case_eq_if p1 p2 remove_msg_from_queuingport_def)   
    next
      case (Some t) 
      have a0:"(ports (comm s)) pt = Some t" by (simp add: Some.hyps)
      show ?thesis  
      proof(induct "the ((ports (comm s)) pt)")
        case (Queuing x1 x2 x3 x4 x5)
        from p2 have "\<forall>p. ((part_ports s) p \<noteq> None) = ((ports (comm s)) p \<noteq> None) \<and>
                            ((ports (comm s)) p \<noteq> None \<longrightarrow> p = get_portid_in_type (the ((ports (comm s)) p))) \<and> 
                                  ((ports (comm s)) p \<noteq> None \<longrightarrow> get_portname_by_type (the ((ports (comm s)) p)) 
                                    \<in> get_partition_cfg_ports_byid sysconf (the ((part_ports s) p)) )"
          using port_consistent_def by auto 
        then show ?thesis by (metis a0 disjoint_iff_not_equal option.distinct(1) port_partition)        
      next
        case (Sampling x1 x2 x3 x4)
        have "Some (Sampling x1 x2 x3 x4) = ports (comm s) pt" by (simp add: Sampling.hyps a0) 
        then have "s' = s" unfolding remove_msg_from_queuingport_def
          by (metis (no_types, lifting) Port_Type.simps(6) eq_fst_iff option.simps(5) 
            p1 remove_msg_from_queuingport_def) 
        with p2 show ?thesis by simp
      qed
    qed

    lemma recv_que_msg_presv_port_cons:
      "\<lbrakk>s' = fst (receive_queuing_message s pt); port_consistent s\<rbrakk> \<Longrightarrow> port_consistent s'"
        apply(clarsimp simp:exec_event_def)
        apply(clarsimp simp:receive_queuing_message_def remove_msg_from_queuingport_def)
        apply(case_tac "ports (comm s) pt")
        apply simp
        apply(case_tac "a")
        apply (metis (full_types) remove_msg_from_queuingport_def 
          remove_msg_from_queuingport_presv_port_cons)
        by simp

    lemma insert_msg2queuing_port_presv_port_cons:
    assumes   p1:"s' = insert_msg2queuing_port s pt m"
      and     p2:"port_consistent s"
    shows   "port_consistent s'"
    proof(induct "(ports (comm s)) pt")
      case None  show ?thesis by (simp add: None.hyps insert_msg2queuing_port_def option.case_eq_if p1 p2)    
    next
      case (Some t) 
      have a0:"(ports (comm s)) pt = Some t" by (simp add: Some.hyps)
      show ?thesis  
      proof(induct "the ((ports (comm s)) pt)")
        case (Queuing x1 x2 x3 x4 x5)
        from p2 have b1:"\<forall>p. ((part_ports s) p \<noteq> None) = ((ports (comm s)) p \<noteq> None) \<and>
                            ((ports (comm s)) p \<noteq> None \<longrightarrow> p = get_portid_in_type (the ((ports (comm s)) p))) \<and> 
                                  ((ports (comm s)) p \<noteq> None \<longrightarrow> get_portname_by_type (the ((ports (comm s)) p)) 
                                    \<in> get_partition_cfg_ports_byid sysconf (the ((part_ports s) p)) )"
          using port_consistent_def by auto 
        show ?thesis by (metis a0 b1 disjoint_iff_not_equal option.distinct(1) port_partition)          
      next
        case (Sampling x1 x2 x3 x4)
        have "Some (Sampling x1 x2 x3 x4) = ports (comm s) pt" by (simp add: Sampling.hyps a0) 
        then have "s' = s" unfolding insert_msg2queuing_port_def
          by (metis Port_Type.simps(6) insert_msg2queuing_port_def option.simps(5) p1)
        with p2 show ?thesis by simp
      qed
    qed

    lemma send_que_msg_presv_port_cons:
      "\<lbrakk>s' = fst (send_queuing_message_maylost sysconf s pt m); port_consistent s\<rbrakk> \<Longrightarrow> port_consistent s'"
        apply(clarsimp simp:exec_event_def)
        apply(clarsimp simp:send_queuing_message_maylost_def 
            replace_msg2queuing_port_def insert_msg2queuing_port_def)
        apply(case_tac "ports (comm s) pt")
        apply simp
        apply(case_tac "a")
        apply (metis (full_types) insert_msg2queuing_port_def 
            insert_msg2queuing_port_presv_port_cons)
        by simp

    lemma trans_que_msg_presrv_pt_cons:"port_consistent s \<Longrightarrow> port_consistent (transf_queuing_msg_maylost sysconf s ch)"
    proof -
    {
      assume a0:"port_consistent s"
      show ?thesis
      proof(induct ch)
        case (Channel_Queuing cn sn dn) show ?case
        proof -
        {
          let ?sm = "remove_msg_from_queuingport s (the (get_portid_by_name s sn))"
          let ?s0 = "fst ?sm"
          let ?s1 = "replace_msg2queuing_port ?s0 (the (get_portid_by_name s dn)) (the (snd ?sm))"
          let ?s2 = "insert_msg2queuing_port ?s0 (the (get_portid_by_name s dn)) (the (snd ?sm))"
          let ?s3 = "transf_queuing_msg_maylost sysconf s ch"
          have b1:"port_consistent ?s0" by (simp add: a0 remove_msg_from_queuingport_presv_port_cons)  
          then have b2:"port_consistent ?s1" by (simp add: replace_msg2queuing_port_def)  
          with b2 have b5:"port_consistent ?s2" by (simp add: b1 insert_msg2queuing_port_presv_port_cons) 
          then show ?thesis 
            by (clarsimp simp:transf_queuing_msg_maylost_def a0 b2)
        }
        qed
        case (Channel_Sampling cn sn dns) show ?case by (simp add: a0) 
      qed
    }
    qed

    lemma clr_que_port_presrv_pt_cons:
    assumes   p1:"s' = clear_queuing_port s pid"
      and     p2:"port_consistent s"
    shows   "port_consistent s'"
    proof -
    {
      fix p
      have "((part_ports s') p \<noteq> None) = ((ports (comm s')) p \<noteq> None) \<and>
              ((ports (comm s')) p \<noteq> None \<longrightarrow> p = get_portid_in_type (the ((ports (comm s')) p))) \<and>
              ((ports (comm s')) p \<noteq> None \<longrightarrow> get_portname_by_type (the ((ports (comm s')) p)) 
                \<in> get_partition_cfg_ports_byid sysconf (the ((part_ports s') p)) )"
      proof(cases "\<not> is_a_queuingport s pid 
                    \<or> \<not> is_a_port_of_partition s pid (current s)
                    \<or> \<not> is_dest_port s pid")
        assume a0:"\<not> is_a_queuingport s pid 
                    \<or> \<not> is_a_port_of_partition s pid (current s)
                    \<or> \<not> is_dest_port s pid"
        with p1 have "s' = s" unfolding clear_queuing_port_def by auto
        with p2 show ?thesis using port_consistent_def by auto 
      next
        assume a1:"\<not>(\<not> is_a_queuingport s pid
                    \<or> \<not> is_a_port_of_partition s pid (current s)
                    \<or> \<not> is_dest_port s pid)"
        then show ?thesis by (metis a1 emptyE inf.idem is_a_port_of_partition_def 
              option.distinct(1) p2 port_consistent_def port_partition)              
      qed
    }
    then show ?thesis using port_consistent_def by blast
    qed

    lemma set_part_mode_presrv_pt_cons:
    assumes   p1:"s' = set_partition_mode sysconf s m"
      and     p2:"port_consistent s"
    shows   "port_consistent s'" 
    proof -
    {
      fix p
      have "((part_ports s') p \<noteq> None) = ((ports (comm s')) p \<noteq> None) \<and>
              ((ports (comm s')) p \<noteq> None \<longrightarrow> p = get_portid_in_type (the ((ports (comm s')) p))) \<and>
              ((ports (comm s')) p \<noteq> None \<longrightarrow> get_portname_by_type (the ((ports (comm s')) p)) 
                \<in> get_partition_cfg_ports_byid sysconf (the ((part_ports s') p)) )"
      proof(cases "(partconf sysconf) (current s) \<noteq> None \<and> (partitions s) (current s) \<noteq> None \<and>
                  \<not> (part_mode (the ((partitions s) (current s))) = COLD_START \<and> m = WARM_START)")
        assume a0:"(partconf sysconf) (current s) \<noteq> None \<and> (partitions s) (current s) \<noteq> None \<and>
                  \<not> (part_mode (the ((partitions s) (current s))) = COLD_START \<and> m = WARM_START)"
        show ?thesis using port_consistent_def
          using a0 p1 p2 set_partition_mode_def by force 
      next
        assume a1:"\<not>((partconf sysconf) (current s) \<noteq> None \<and> (partitions s) (current s) \<noteq> None \<and>
                  \<not> (part_mode (the ((partitions s) (current s))) = COLD_START \<and> m = WARM_START))"
        then have "s' = s" using p1 set_partition_mode_def by auto 
        then show ?thesis using p2 port_consistent_def by auto 
       qed
    }
    then show ?thesis using port_consistent_def by blast
    qed
          
    lemma pt_cons_execevt : "port_consistent s \<Longrightarrow> \<forall>s'. (s,s')\<in>exec_event a \<longrightarrow> port_consistent s'"
    proof -
    {
      assume a1:"port_consistent s"
      {
        fix s'
        assume p0: "(s,s')\<in>exec_event a"
        then have "port_consistent s'"
        proof(cases "event_enabled s a = True")
          assume b0:"event_enabled s a \<noteq> True"
          with a1 p0 show ?thesis using exec_event_def by simp
        next
          assume b1:"event_enabled s a = True"
          with p0 show ?thesis
          proof(induct a)
            case (hyperc x) then show ?case  
              apply (induct x)
              using a1 crt_smpl_port_presrv_pt_cons exec_event_def apply auto[1]
              using a1 write_smpl_msg_presrv_pt_cons exec_event_def apply auto[1]
              using a1 read_sampling_message_def exec_event_def apply auto[1]
              using a1 get_sampling_port_id_def exec_event_def apply auto[1]
              using a1 get_sampling_port_status_def exec_event_def apply auto[1]
              using a1 crt_que_port_presrv_pt_cons exec_event_def apply auto[1]
              using a1 send_que_msg_presv_port_cons exec_event_def apply auto[1]
              using a1 recv_que_msg_presv_port_cons exec_event_def apply auto[1]
              using a1 get_queuing_port_id_def exec_event_def apply auto[1]
              using a1 get_queuing_port_status_def exec_event_def apply auto[1]
              using a1 clr_que_port_presrv_pt_cons exec_event_def apply auto[1]
              using a1 set_part_mode_presrv_pt_cons exec_event_def apply auto[1]
              using a1 get_partition_status_def exec_event_def apply auto[1]
              done
            next
            case (sys x) then show ?case
              using a1 port_consistent_def exec_event_def schedule_def 
                    trans_spl_msg_presrv_pt_cons trans_que_msg_presrv_pt_cons
                    by (induct x, auto)
          qed
        qed
      }
      then show ?thesis by auto
    }
    qed

    lemma pt_cons_exec : "\<forall>s s' as. port_consistent s \<and> s' \<in> execute as s \<longrightarrow> port_consistent s'"
      proof -
      {
        fix as
        have "\<forall>s s'. port_consistent s \<and> s' \<in> execute as s \<longrightarrow> port_consistent s'"
        proof(induct as)
          case Nil show ?case by (auto simp add: execute_def) 
          case (Cons b bs) 
            assume a0:"\<forall>s s'. port_consistent s \<and> s' \<in> execute bs s \<longrightarrow> port_consistent s'"
            show ?case
              proof -
              {
                fix s s'
                assume b0:"port_consistent s"
                assume b1:"s' \<in> execute (b # bs) s"
                then have "port_consistent s'"
                  proof -
                  {
                    from b1 have "\<exists>s1. (s,s1)\<in>exec_event b \<and> (s1,s')\<in>run bs" 
                      using execute_def run_Cons Image_singleton mem_Collect_eq relcompEpair by auto 
                    then obtain s1 where c0: "(s,s1)\<in>exec_event b \<and> (s1,s')\<in>run bs" by auto
                    with a0 b0 have "port_consistent s1" using exec_event_def pt_cons_execevt by blast
                    then show ?thesis using a0 c0 execute_def by blast
                  }
                  qed
              }
              then show ?thesis by auto
              qed
         qed
      }
      then show ?thesis by auto
      qed

    lemma port_cons_reach_state : "reachable0 s \<Longrightarrow> port_consistent s"
      using pt_cons_exec pt_cons_s0 reachable_def reachable0_def
        by (simp add: Image_singleton execute_def)

subsubsection{* Deadlock free *}

    lemma deadlock_free : "reachable0 s \<Longrightarrow> (\<exists>e. event_enabled s e)"
      by (metis System_Event.case(1) event_enabled.simps(2)) 


subsection{* Some lemmas of security proofs *}

    lemma que_port_not_samp : "is_a_queuingport s p \<Longrightarrow> \<not> is_a_samplingport s p"
      apply(clarsimp simp:is_a_queuingport_def is_a_samplingport_def)      
      by (smt Port_Type.case(1) Port_Type.case(2) Port_Type.exhaust option.case_eq_if)
      

    lemma samp_port_not_que : "is_a_samplingport s p \<Longrightarrow> \<not> is_a_queuingport s p"
      using que_port_not_samp by auto

    lemma src_port_not_dest : "is_source_port s p \<Longrightarrow> \<not> is_dest_port s p"
      apply(clarsimp simp:is_source_port_def is_dest_port_def) 
      by (smt Port_Type.exhaust Port_Type.simps(5) Port_Type.simps(6) 
          option.case_eq_if port_direction.exhaust port_direction.simps(3) port_direction.simps(4))
      
    lemma dest_port_not_src : "is_dest_port s p \<Longrightarrow> \<not> is_source_port s p"
      using src_port_not_dest by auto

    lemma sche_imp_not_part:"is_a_scheduler sysconf d \<Longrightarrow> \<not> (is_a_partition sysconf d)"      
      using sch_not_part by auto

    lemma part_imp_not_sch : "is_a_partition sysconf d \<Longrightarrow> \<not> (is_a_scheduler sysconf d)"
      by (auto simp add: sch_not_part)

    lemma part_imp_not_tras : "is_a_partition sysconf d \<Longrightarrow> \<not> (is_a_transmitter sysconf d)"
      by (auto simp add: trans_not_part)
                                            
    lemma trans_imp_not_part : "is_a_transmitter sysconf d \<Longrightarrow> \<not> (is_a_partition sysconf d)"      
      by (simp add: trans_not_part)

    lemma sche_imp_not_trans:"is_a_scheduler sysconf d \<Longrightarrow> \<not> (is_a_transmitter sysconf d)"
      using sch_not_trans by auto

    lemma trans_imp_not_sche:"is_a_transmitter sysconf d \<Longrightarrow> \<not> (is_a_scheduler sysconf d)"
      using sch_not_trans by auto

    lemma crt_imp_sche:"\<lbrakk>\<forall>v .v\<in> the ((domv sysconf) (scheduler sysconf)) \<longrightarrow> (val (vars s)) v = (val (vars t)) v;
                        current s = current t\<rbrakk> \<Longrightarrow> (s \<sim> (scheduler sysconf)\<sim> t)"
      by auto

    lemma trans_hasnoports : "get_partition_cfg_ports_byid sysconf (transmitter sysconf) = {}"
       by (meson get_partition_cfg_ports_byid_def is_a_partition_def is_a_transmitter_def part_imp_not_tras)

    lemma sched_hasnoports : "get_partition_cfg_ports_byid sysconf (scheduler sysconf) = {}"
       by (meson get_partition_cfg_ports_byid_def is_a_partition_def is_a_scheduler_def part_imp_not_sch)

  lemma part_ports_imp_portofpart:"part_ports s = part_ports s' \<longrightarrow> 
                                  get_ports_of_partition s d = get_ports_of_partition s' d"
  proof - 
  {
    assume a0:"part_ports s = part_ports s'"
    have "get_ports_of_partition s d = get_ports_of_partition s' d"
    proof -
      have "\<forall>p. p\<in>get_ports_of_partition s d \<longrightarrow> p\<in> get_ports_of_partition s' d" 
      proof -
      {
        fix p
        assume "p\<in>get_ports_of_partition s d"
        then have "(part_ports s) p = Some d" by (simp add: get_ports_of_partition_def) 
        with a0 have "(part_ports s') p = Some d" by simp
        then have "p\<in>get_ports_of_partition s' d" by (simp add: get_ports_of_partition_def) 
      }
      then show ?thesis by auto
      qed
      moreover
      have "\<forall>p. p\<in>get_ports_of_partition s' d \<longrightarrow> p\<in> get_ports_of_partition s d"
      proof -
      {
        fix p
        assume "p\<in>get_ports_of_partition s' d"
        then have "(part_ports s') p = Some d" by (simp add: get_ports_of_partition_def) 
        with a0 have "(part_ports s) p = Some d" by simp
        then have "p\<in>get_ports_of_partition s d" by (simp add: get_ports_of_partition_def) 
      }
      then show ?thesis by auto
      qed
      then show ?thesis using calculation by blast
    qed
  }
  then show ?thesis by auto
  qed

  lemma no_cfgport_impl_noports : "\<lbrakk>reachable0 s; get_partition_cfg_ports_byid sysconf d = {}\<rbrakk> 
                                \<Longrightarrow> get_ports_of_partition s d = {}"
  proof-
    assume p0:"reachable0 s"
    assume p1:"get_partition_cfg_ports_byid sysconf d = {}"
    show "get_ports_of_partition s d = {}" 
    proof -
      from p0 have b0:"port_consistent s" by (simp add: port_cons_reach_state) 
      then have b2:"\<forall>x. (part_ports s) x \<noteq> Some d"
      proof -
      {
        fix x
        have "(part_ports s) x = Some d \<longrightarrow> False"
          proof -
          {
            assume c0:"(part_ports s) x = Some d"
            have c1:"(ports (comm s)) x \<noteq> None" using b0 c0 port_consistent_def by auto 
            have "get_portname_by_type (the ((ports (comm s)) x)) 
                                \<in> get_partition_cfg_ports_byid sysconf (the ((part_ports s) x))"
              using b0 c1 port_consistent_def by auto 
            then have "False" by (simp add: c0 p1)
          }
          then show ?thesis by auto
          qed
      }
      then show ?thesis by auto
      qed
      then have "\<not>(\<exists>x. (part_ports s) x = Some d)" by auto
      then show ?thesis unfolding get_ports_of_partition_def by auto
    qed
  qed

  lemma rm_msg_queport_dec_size1:"is_a_queuingport s p \<and> \<not> is_empty_port s p
  \<longrightarrow> get_port_buf_size s p = get_port_buf_size (fst (remove_msg_from_queuingport s p)) p + 1"
  proof -
  {
    assume a0:"is_a_queuingport s p"
    assume a1:"\<not> is_empty_port s p"
    have "get_port_buf_size s p = get_port_buf_size (fst (remove_msg_from_queuingport s p)) p + 1"
    proof(induct "(ports (comm s)) p")
      case None show ?case using None.hyps a0 is_a_queuingport_def by auto 
    next
      case (Some x) 
      have b0:"x = the ((ports (comm s)) p)" by (metis Some.hyps option.sel) 
      show ?case
      proof(induct "the ((ports (comm s)) p)")
        case (Queuing x1 x2 x3 x4 x5) 
          have c0:"(ports (comm s)) p = Some (Queuing x1 x2 x3 x4 x5)" using Queuing.hyps Some.hyps b0 by auto 
          let ?s' = "fst (remove_msg_from_queuingport s p)"
          let ?msgs = "the (get_msgs_from_queuingport (the ((ports (comm s)) p)))"
          let ?msgs' = "the (get_msgs_from_queuingport (the ((ports (comm ?s')) p)))"
          let ?m = "SOME x. x\<in>?msgs"
          let ?m1 = "SOME x. x\<in>x5"
          from c0 have c1:"(ports (comm ?s')) p = Some (Queuing x1 x2 x3 x4 (x5-{?m1}))" 
            unfolding remove_msg_from_queuingport_def by simp
          then have c2:"?msgs' = x5-{?m1}" unfolding get_msgs_from_queuingport_def by simp
          have c3:"x5 = ?msgs" by (metis Queuing.hyps get_msgs_from_queuingport.simps(2) option.sel) 
          then have c4:"?m1 = ?m" by simp
          from a1 have c5:"card x5 \<noteq> 0" unfolding is_empty_port_def get_current_bufsize_port_def
            by (metis Queuing.hyps a1 get_current_bufsize_port.simps(1) get_port_byid_def is_empty_port_def) 
          then have c6:"card x5 > 0" by blast 
          then have c7:"?m \<in> x5" using c0 some_in_eq by fastforce 
          with c2 c3 c4 c5 c6 have "card ?msgs = card ?msgs' + 1"
            by (metis One_nat_def Suc_pred add.right_neutral add_Suc_right card_Diff_singleton card_infinite) 
  
          then show ?case unfolding get_port_buf_size_def get_current_bufsize_port_def
            by (metis Port_Type.simps(7) Queuing.hyps c1 c2 c3 get_port_byid_def option.sel) 
      next
        case (Sampling x1 x2 x3 x4)
          show ?case by (smt Port_Type.simps(6) Sampling.hyps a0 case_optionE is_a_queuingport_def option.sel) 
      qed
    qed
  }
  then show ?thesis by simp
  qed

  lemma rm_msg_queport_dec_size0:"is_a_queuingport s p \<and> is_empty_port s p
      \<longrightarrow> get_port_buf_size s p = get_port_buf_size (fst (remove_msg_from_queuingport s p)) p"
  proof -
  {
    assume a0:"is_a_queuingport s p"
    assume a1:"is_empty_port s p"
    have "get_port_buf_size s p = get_port_buf_size (fst (remove_msg_from_queuingport s p)) p"
    proof(induct "(ports (comm s)) p")
      case None show ?case using None.hyps a0 is_a_queuingport_def by auto 
    next
      case (Some x) 
      have b0:"x = the ((ports (comm s)) p)" by (metis Some.hyps option.sel) 
      show ?case
      proof(induct "the ((ports (comm s)) p)")
        case (Queuing x1 x2 x3 x4 x5) 
        have c0:"(ports (comm s)) p = Some (Queuing x1 x2 x3 x4 x5)" using Queuing.hyps Some.hyps b0 by auto 
        let ?s' = "fst (remove_msg_from_queuingport s p)"
        let ?msgs = "the (get_msgs_from_queuingport (the ((ports (comm s)) p)))"
        let ?msgs' = "the (get_msgs_from_queuingport (the ((ports (comm ?s')) p)))"
        let ?m = "SOME x. x\<in>?msgs"
        let ?m1 = "SOME x. x\<in>x5"
        from c0 have c1:"(ports (comm ?s')) p = Some (Queuing x1 x2 x3 x4 (x5-{?m1}))" 
          unfolding remove_msg_from_queuingport_def Let_def by simp
        then have c2:"?msgs' = x5-{?m1}" unfolding get_msgs_from_queuingport_def by simp
        have c3:"x5 = ?msgs" by (metis Queuing.hyps get_msgs_from_queuingport.simps(2) option.sel) 
        then have c4:"?m1 = ?m" by simp
        from a1 have c5:"card x5 = 0" unfolding is_empty_port_def get_current_bufsize_port_def
          by (metis Queuing.hyps a1 get_current_bufsize_port.simps(1) get_port_byid_def is_empty_port_def) 
        with c2 have c7:"card ?msgs' = 0" using card_eq_0_iff by fastforce         
        then show ?case unfolding get_port_buf_size_def get_current_bufsize_port_def
          by (metis Port_Type.simps(7) Queuing.hyps c1 c2 c5 get_port_byid_def option.sel)
      next
        case (Sampling x1 x2 x3 x4)
        show ?case by (smt Port_Type.simps(6) Sampling.hyps a0 case_optionE is_a_queuingport_def option.sel) 
      qed
    qed
  }
  then show ?thesis by simp
  qed

  lemma clr_queport_size0:"is_a_queuingport s p \<and> is_a_port_of_partition s p (current s) \<and> is_dest_port s p
                  \<longrightarrow> get_port_buf_size (clear_queuing_port s p) p = 0"
  proof -
  {
    let ?s' = "clear_queuing_port s p"
    assume a0:"is_a_queuingport s p"
    assume a1:"is_a_port_of_partition s p (current s)"
    assume a2:"is_dest_port s p"
    have "get_port_buf_size ?s' p = 0"
    proof(cases "\<not> is_a_queuingport s p 
                \<or> \<not> is_a_port_of_partition s p (current s) 
                \<or> \<not> is_dest_port s p")
      assume b0:"\<not> is_a_queuingport s p 
                \<or> \<not> is_a_port_of_partition s p (current s)
                \<or> \<not> is_dest_port s p"
      with a0 a1 a2 show ?thesis by simp
    next
      assume b0:"\<not>(\<not> is_a_queuingport s p
                \<or> \<not> is_a_port_of_partition s p (current s)
                \<or> \<not> is_dest_port s p)"
      then have b1:"(ports (comm ?s')) p = Some (clear_msg_queuingport (the ((ports (comm s)) p)))" 
        unfolding clear_queuing_port_def by (smt Communication_State.select_convs(1) 
          Communication_State.surjective Communication_State.update_convs(1) 
          State.select_convs(3) State.surjective State.update_convs(3) fun_upd_same) 
      show ?thesis
      proof(induct "the ((ports (comm s)) p)")
        case (Queuing x1 x2 x3 x4 x5)
          have "the ((ports (comm ?s')) p) = Queuing x1 x2 x3 x4 {}"
            by (metis Port_Type.simps(5) Queuing.hyps b1 clear_msg_queuingport_def option.sel) 
          then show ?case unfolding get_current_bufsize_port_def get_port_buf_size_def
          Let_def get_port_byid_def by simp
      next
        case (Sampling x1 x2 x3 x4)
        with a0 show ?case  by (metis Port_Type.simps(6) is_a_queuingport_def option.case_eq_if) 
      qed
    qed
  }
  then show ?thesis by auto
  qed


  lemma same_part_mode: 
    assumes p1: "is_a_partition sysconf (current s)"
          and   p2: "s \<sim> scheduler sysconf \<sim> t"
          and   p3: "s \<sim> current s \<sim> t"
        shows "part_mode (the (partitions s (current s))) = part_mode (the (partitions t (current t)))"
  proof -
    from p1 p3 have "vpeq_part s (current s) t" 
      using  part_imp_not_sch part_imp_not_tras by fastforce
    moreover
    from p2 have "current s = current t" by auto
    ultimately show ?thesis  by auto
  qed

subsection{* Concrete unwinding condition of "local respect" *}    
subsubsection{*proving "create sampling port" satisfying the "local respect" property*}

  lemma crt_smpl_port_notchg_current:
    "\<lbrakk>is_a_partition sysconf (current s); s' = fst (create_sampling_port sysconf s pname)\<rbrakk> 
      \<Longrightarrow> current s = current s'"
    by (clarsimp simp:create_sampling_port_def)

        
  text{*the state before and after executing the action "create sampling port" is observ equal to scheduler*}
  lemma crt_smpl_port_sm_sche:"\<lbrakk>is_a_partition sysconf (current s); 
                                s' = fst (create_sampling_port sysconf s pname)\<rbrakk>
                                      \<Longrightarrow> (s\<sim>(scheduler sysconf)\<sim>s')"
   using crt_smpl_port_notchg_current 
         vpeq1_def vpeq_sched_def  is_a_scheduler_def part_imp_not_sch by metis

  lemma crt_sampl_port_notchg_partstate:
  "\<lbrakk>is_a_partition sysconf (current s); is_a_partition sysconf d; 
   s' = fst (create_sampling_port sysconf s pname)\<rbrakk>
                           \<Longrightarrow> (partitions s) d = (partitions s') d"
  by (clarsimp simp:create_sampling_port_def)

  lemma crt_sampl_port_notchg_partportsinotherdom:
  assumes p1:"is_a_partition sysconf (current s)"
    and   p3:"(current s) \<noteq> d"
    and   p4:"s' = fst (create_sampling_port sysconf s pname)"
  shows   "get_ports_of_partition s d = get_ports_of_partition s' d"
  proof -
  {
    have "\<forall>p. p\<in>get_ports_of_partition s d \<longrightarrow> p\<in>get_ports_of_partition s' d"
    proof-
    {
      fix p
      assume a0:"p\<in>get_ports_of_partition s d"
      have a1:"p\<in>get_ports_of_partition s' d"
      proof(cases "pname \<in> get_partition_cfg_ports_byid sysconf (current s)")
        assume b0:"pname \<in> get_partition_cfg_ports_byid sysconf (current s)"
        have b1:"p \<noteq> get_portid_in_type (the (get_samplingport_conf sysconf pname))" 
          using b0 port_partition by auto 
        then show ?thesis using b0 port_partition by auto 
      next
        assume c0:"\<not>(pname \<in> get_partition_cfg_ports_byid sysconf (current s))"
        then have c1:"s' = s" by (simp add: create_sampling_port_def p4) 
        then show ?thesis by (simp add: a0) 
      qed
    }
    then show ?thesis by auto
    qed
    moreover
    have "\<forall>p. p\<in>get_ports_of_partition s' d \<longrightarrow> p\<in>get_ports_of_partition s d"
    proof-
    {
      fix p
      assume a0:"p\<in>get_ports_of_partition s' d"
      have "p\<in>get_ports_of_partition s d" 
      proof(cases "pname \<in> get_partition_cfg_ports_byid sysconf (current s)")
        assume b0:"pname \<in> get_partition_cfg_ports_byid sysconf (current s)"
        have b1:"p \<noteq> get_portid_in_type (the (get_samplingport_conf sysconf pname))" 
          using b0 port_partition by auto 
        then show ?thesis using b0 port_partition by auto 
      next
        assume c0:"\<not>(pname \<in> get_partition_cfg_ports_byid sysconf (current s))"
        then have c1:"s' = s" by (simp add: create_sampling_port_def p4) 
        then show ?thesis using a0 by auto  
      qed
    }
    then show ?thesis by auto
    qed
    then show ?thesis using calculation by blast
  }
  qed

  lemma crt_sampl_port_notchg_portsinotherdom:
  assumes p1:"is_a_partition sysconf (current s)"
    and   p3:"(current s) \<noteq> d"
    and   p4:"s' = fst (create_sampling_port sysconf s pname)"
  shows " \<forall>p. p\<in> get_ports_of_partition s d \<longrightarrow> ports (comm s) p = ports (comm s') p"
  proof -
  {
    fix p
    have "p \<in> get_ports_of_partition s d \<longrightarrow> ports (comm s) p = ports (comm s') p "
    proof -
    {
      assume a0:"p \<in> get_ports_of_partition s d"
      have "ports (comm s) p = ports (comm (fst (create_sampling_port sysconf s pname))) p"
      proof(cases "pname \<in> get_partition_cfg_ports_byid sysconf (current s)")
        assume b0:"pname \<in> get_partition_cfg_ports_byid sysconf (current s)"
        have b1:"p \<noteq> get_portid_in_type (the (get_samplingport_conf sysconf pname))" 
          using b0 port_partition by auto 
        then show ?thesis using b0 port_partition by auto 
      next
        assume c0:"\<not>(pname \<in> get_partition_cfg_ports_byid sysconf (current s))"
        then have c1:"s' = s" by (simp add: create_sampling_port_def p4) 
        then show ?thesis using p4 by auto  
      qed
    }
    then show ?thesis by (simp add: p4)
    qed
  }
  then show ?thesis by auto    

  qed

  lemma crt_sampl_port_notchg_comminotherdom:
  assumes   p0:"reachable0 s"
      and   p1:"is_a_partition sysconf (current s)"
    and   p3:"(current s) \<noteq> d"
    and   p4:"s' = fst (create_sampling_port sysconf s pname)"
  shows   "vpeq_part_comm s d s'"
  proof-
    have "get_ports_of_partition s d = get_ports_of_partition s' d"
       using crt_sampl_port_notchg_partportsinotherdom p0 p1 p3 p4 by auto            
    also have "\<forall>p. p \<in> get_ports_of_partition s d \<longrightarrow>
              is_a_queuingport s p = is_a_queuingport s' p \<and>
              is_dest_port s p = is_dest_port s' p \<and> 
              (if is_dest_port s p then get_port_buf_size s p = get_port_buf_size s' p else True)"         
    unfolding is_a_queuingport_def is_dest_port_def 
    using  crt_sampl_port_notchg_portsinotherdom 
          p1 p3 p4 get_port_byid_def p1 p3 p4 get_port_buf_size_def by auto
        
     ultimately show ?thesis by auto
  qed
  
declare is_a_partition_def [cong del] 
  lemma crt_smpl_port_sm_nitfpart:"\<lbrakk>reachable0 s; is_a_partition sysconf (current s); is_a_partition sysconf d;
                                  ((current s) \<setminus>\<leadsto> d); s' = fst (create_sampling_port sysconf s pname)\<rbrakk>
                                        \<Longrightarrow> (s \<sim> d \<sim> s')"
  apply(clarsimp)        
  using  trans_imp_not_part sche_imp_not_part                 
  apply (simp add: crt_sampl_port_notchg_partstate)
  by (metis create_sampling_port_def fst_conv get_samplingport_conf_def port_name_diff)
    
declare is_a_partition_def [cong] 

  lemma crt_smpl_port_presrv_lcrsp:
  assumes p0:"reachable0 s"
    and   p1:"is_a_partition sysconf (current s)"
    and   p2:"(current s) \<setminus>\<leadsto> d"
    and   p3:"s' = fst (create_sampling_port sysconf s pname)"
  shows   "s \<sim> d \<sim> s'"
  proof(cases "is_a_scheduler sysconf d")
    assume a0:"is_a_scheduler sysconf d"
    show ?thesis using crt_smpl_port_sm_sche[OF p1 p3] a0 by auto
  next
    assume a1:"\<not> is_a_scheduler sysconf d"
    show ?thesis
    proof(cases "is_a_partition sysconf d")
      assume b0:"is_a_partition sysconf d"
      show ?thesis using b0 crt_smpl_port_sm_nitfpart p0 p1 p2 p3 by blast
    next
      assume b1:"\<not> is_a_partition sysconf d"
      show ?thesis
      proof(cases "is_a_transmitter sysconf d")
        assume c0:"is_a_transmitter sysconf d"
        show ?thesis
        proof -
        {
          have "vpeq_transmitter s d s'" unfolding vpeq_transmitter_def
          proof-
            show "comm s = comm s' \<and>  part_ports s = part_ports s'" 
            proof(rule conjI)
            {
              show "comm s = comm s'"
              proof -
              {
                from p1 p2 have "\<not> part_intf_transmitter sysconf (current s)" 
                  using interference1_def by (meson a1 c0 non_interference1_def)
                then have "get_partition_cfg_ports (the ((partconf sysconf) (current s))) = {}" 
                  using get_partition_cfg_ports_byid_def  p1 port_partition by fastforce
                then have "pname \<notin> get_partition_cfg_ports_byid sysconf (current s)" 
                  by (simp add: get_partition_cfg_ports_byid_def)
                then have "s = s'"by (simp add: create_sampling_port_def p3)
              }
              then show ?thesis by auto
              qed
              show "part_ports s = part_ports s'"
              proof - 
              {
                from p1 p2 c0 have d0:"\<not> part_intf_transmitter sysconf (current s)" 
                  using interference1_def non_interference1_def by (meson a1) 
                then have d1:"get_partition_cfg_ports_byid sysconf (current s) = {}" using port_partition by blast 
                then have d2:"s=s'" by (smt create_sampling_port_def empty_iff fst_conv p3) 
              }
              then show ?thesis by auto
              qed
            }
            qed
          qed
        }
        then show ?thesis using a1 b1 is_a_scheduler_def vpeq1_def by auto
        qed
      next
        assume c1:"\<not> is_a_transmitter sysconf d"
        show ?thesis using a1 b1 c1 is_a_scheduler_def is_a_transmitter_def vpeq1_def by auto
      qed
    qed
  qed

  lemma crt_smpl_port_presrv_lcrsp_e: "local_respect_e (hyperc (Create_Sampling_Port pn))"
    using crt_smpl_port_presrv_lcrsp  prod.simps(2) exec_event_def 
      mem_Collect_eq  singletonD vpeq_reflexive_lemma 
   by (auto cong del: vpeq1_def)
   
subsubsection{*proving "write sampling message" satisfying the "local respect" property*}

  lemma wrt_smpl_msg_notchg_current:
  "\<lbrakk>is_a_partition sysconf (current s); s' = fst (write_sampling_message s pid m)\<rbrakk> 
    \<Longrightarrow> current s = current s'"
    apply(clarsimp simp:write_sampling_message_def update_sampling_port_msg_def)
    apply(case_tac "ports (comm s) pid")
    apply simp
    apply(case_tac "a")    
    by auto


  text{*the state before and after executing the action "write sampling message" is observ equal to scheduler*}
  lemma wrt_smpl_msg_sm_sche:"\<lbrakk>is_a_partition sysconf (current s); 
                                s' = fst (write_sampling_message s pid m)\<rbrakk>
                                      \<Longrightarrow> (s\<sim>(scheduler sysconf)\<sim>s')"
   using wrt_smpl_msg_notchg_current part_imp_not_sch by (meson vpeq1_def vpeq_sched_def)

  lemma wrt_smpl_msg_notchg_partstate:
                "\<lbrakk>is_a_partition sysconf (current s); is_a_partition sysconf d; 
                s' = fst (write_sampling_message s pid m)\<rbrakk>
                      \<Longrightarrow> (partitions s) d = (partitions s') d"
    apply(clarsimp simp:write_sampling_message_def update_sampling_port_msg_def)
    apply(case_tac "ports (comm s) pid")
    apply simp
    apply(case_tac "a")
    by auto        

  lemma wrt_smpl_msg_notchg_partports:
      "\<lbrakk>is_a_partition sysconf (current s); s' = fst (write_sampling_message s pid m)\<rbrakk>\<Longrightarrow>
          part_ports s = part_ports s'"
     apply(clarsimp simp:write_sampling_message_def update_sampling_port_msg_def)
      apply(case_tac "ports (comm s) pid")
      apply simp
      apply(case_tac "a")
      by  auto

  lemma wrt_smpl_msg_notchg_portinotherdom:
  assumes p1:"is_a_partition sysconf (current s)"
    and   p3:"(current s) \<noteq> d"
    and   p4:"s' = fst (write_sampling_message s pid m)"
  shows " \<forall>p. p\<in> get_ports_of_partition s d \<longrightarrow> ports (comm s) p = ports (comm s') p"
  proof -
  {
    
    fix p
    have "p \<in> get_ports_of_partition s d \<longrightarrow> ports (comm s) p = ports (comm s') p "
    proof -
    {
      assume a0:"p \<in> get_ports_of_partition s d"
      have a1:"(part_ports s) p = Some d" using a0 get_ports_of_partition_def by auto 
      have "ports (comm s) p = ports (comm s') p" 
      proof(cases "p = pid")
        assume b0:"p = pid"
        have b1:"(part_ports s) pid = Some d" using a1 b0 by auto 
        have b2:"\<not> is_a_port_of_partition s pid (current s)" using b1 is_a_port_of_partition_def p3 by auto 
        have b3:"s' = s" by (simp add: b2 p4 write_sampling_message_def) 
        then show ?thesis by auto
      next
        assume c0:"p \<noteq> pid"
        show ?thesis 
          using p4 apply(clarsimp simp:write_sampling_message_def update_sampling_port_msg_def)
          apply(case_tac "ports (comm s) pid")
          apply simp
          apply(case_tac "a")
          using c0 by auto
      qed
    }
    then show ?thesis by (simp add: p4)
    qed
  } then show ?thesis by auto
  qed
 

lemma wrt_smpl_msg_notchg_comminotherdom:
  assumes   p0:"reachable0 s"
      and   p1:"is_a_partition sysconf (current s)"
    and   p3:"(current s) \<noteq> d"
    and   p4:"s' = fst (write_sampling_message s pid m)"
  shows   "vpeq_part_comm s d s'"
  proof-
    from p4 have r0: "part_ports s = part_ports s'"
     apply(clarsimp simp:write_sampling_message_def update_sampling_port_msg_def)
      apply(case_tac "ports (comm s) pid")
      apply simp
      apply(case_tac "a")
      by auto
    then have "get_ports_of_partition s d = get_ports_of_partition s' d"
        using part_ports_imp_portofpart by blast
    moreover have  "\<forall>p. p \<in> get_ports_of_partition s d \<longrightarrow>
              is_a_queuingport s p = is_a_queuingport s' p \<and>
              is_dest_port s p = is_dest_port s' p \<and> 
              (if is_dest_port s p then get_port_buf_size s p = get_port_buf_size s' p else True)"
     using is_a_queuingport_def get_port_buf_size_def 
             is_dest_port_def get_port_byid_def p1 p3 p4 wrt_smpl_msg_notchg_portinotherdom by auto
     ultimately show ?thesis by auto
  qed

  lemma wrt_smpl_msg_sm_nitfpart:"\<lbrakk>reachable0 s; is_a_partition sysconf (current s); is_a_partition sysconf d;
                                  ((current s) \<setminus>\<leadsto> d); s' = fst (write_sampling_message s pid m)\<rbrakk>
                                        \<Longrightarrow> (s \<sim> d \<sim> s')"            
  using  trans_imp_not_part sche_imp_not_part 
  apply(clarsimp cong del: is_a_partition_def interference1_def non_interference1_def vpeq_part_comm_def)
  by (metis nintf_neq  wrt_smpl_msg_notchg_comminotherdom wrt_smpl_msg_notchg_partstate)
        
        
  lemma write_smpl_msg_presrv_lcrsp:
  assumes p0:"reachable0 s"
    and   p1:"is_a_partition sysconf (current s)"
    and   p2:"(current s) \<setminus>\<leadsto> d"
    and   p3:"s' = fst (write_sampling_message s pid m)"
  shows   "s \<sim> d \<sim> s'"
  proof(cases "is_a_scheduler sysconf d")
    assume a0:"is_a_scheduler sysconf d"
    then show ?thesis using is_a_scheduler_def wrt_smpl_msg_sm_sche[OF p1 p3] by auto
  next
    assume a1:"\<not> is_a_scheduler sysconf d"
    show ?thesis
    proof(cases "is_a_partition sysconf d")
      assume b0:"is_a_partition sysconf d"
      show ?thesis using b0 wrt_smpl_msg_sm_nitfpart p0 p1 p2 p3 by blast
    next
      assume b1:"\<not> is_a_partition sysconf d"
      show ?thesis
      proof(cases "is_a_transmitter sysconf d")
        assume c0:"is_a_transmitter sysconf d"
        have "comm s = comm s' \<and>  part_ports s = part_ports s'" 
        proof(rule conjI)
        {
          from p1 p2 have "\<not> part_intf_transmitter sysconf (current s)" 
            using interference1_def by (smt a1 c0 non_interference1_def)
          then have d1:"get_partition_cfg_ports (the ((partconf sysconf) (current s))) = {}" 
            using get_partition_cfg_ports_byid_def  p1 port_partition by fastforce
          then have d2:"get_partition_cfg_ports_byid sysconf (current s) = {}"
            by (simp add: get_partition_cfg_ports_byid_def) 
          then have "\<not> is_a_port_of_partition s pid (current s)" 
          proof(cases "(ports (comm s)) pid = None")
            assume e0:"(ports (comm s)) pid = None"
            from p0 have e1:"port_consistent s" by (simp add: port_cons_reach_state) 
            with e0 have e1:"(part_ports s) pid = None" unfolding port_consistent_def by auto
            show ?thesis by (simp add: e1 is_a_port_of_partition_def) 
          next
            assume e0:"\<not>((ports (comm s)) pid = None)"
            from p0 have e1:"port_consistent s" by (simp add: port_cons_reach_state) 
            then have "get_portname_by_type (the ((ports (comm s)) pid)) \<in>
                get_partition_cfg_ports_byid sysconf (the ((part_ports s) pid)) "
                using e0 port_consistent_def by blast
            with d2 have "current s \<noteq> the ((part_ports s) pid)" by auto
            then show ?thesis using is_a_port_of_partition_def by auto
          qed
          then have d0:"s = s'" by (smt write_sampling_message_def fst_conv p3) 
          then show "comm s = comm s'" by simp
          with d0 show "part_ports s = part_ports s'" by simp
        }
        qed
        then show ?thesis using a1 b1  by auto        
      next
        assume c1:"\<not> is_a_transmitter sysconf d"
        show ?thesis using a1 b1 c1  by auto
      qed
    qed
  qed

  lemma write_smpl_msg_presrv_lcrsp_e: "local_respect_e (hyperc (Write_Sampling_Message pid m))"
    using write_smpl_msg_presrv_lcrsp  prod.simps(2)  exec_event_def 
      mem_Collect_eq singletonD vpeq_reflexive_lemma 
     by (auto cong del: vpeq1_def)

subsubsection{*proving "read sampling message" satisfying the "local respect" property*}

  lemma read_smpl_msg_presrv_lcrsp:
      assumes p0:"reachable0 s"
        and   p1:"is_a_partition sysconf (current s)"
        and   p2:"(current s) \<setminus>\<leadsto> d"
        and   p3:"s' = fst (read_sampling_message s pid)"
      shows   "s \<sim> d \<sim> s'"
   using vpeq_reflexive_lemma  p3 read_sampling_message_def by auto  
    

  lemma read_smpl_msg_presrv_lcrsp_e: 
    "local_respect_e (hyperc (Read_Sampling_Message pid))"
    using read_smpl_msg_presrv_lcrsp  exec_event_def 
       prod.simps(2) vpeq_reflexive_lemma
    by (auto cong del:  vpeq1_def)

subsubsection{*proving "get sampling portid" satisfying the "local respect" property*}

  lemma get_smpl_pid_presrv_lcrsp:
      assumes p0:"reachable0 s"
        and   p1:"is_a_partition sysconf (current s)"
        and   p2:"(current s) \<setminus>\<leadsto> d"
        and   p3:"s' = fst (get_sampling_port_id sysconf s pname)"
      shows   "s \<sim> d \<sim> s'"
    using p3 get_sampling_port_id_def  vpeq_reflexive_lemma by auto
    

  lemma get_smpl_pid_presrv_lcrsp_e: "local_respect_e (hyperc (Get_Sampling_Portid pid))"
    using get_smpl_pid_presrv_lcrsp  exec_event_def  
       prod.simps(2)  vpeq_reflexive_lemma
     by (auto cong del: vpeq1_def) 

subsubsection{*proving "get sampling port status" satisfying the "local respect" property*}
  lemma get_smpl_psts_presrv_lcrsp:
      assumes p0:"reachable0 s"
        and   p1:"is_a_partition sysconf (current s)"
        and   p2:"(current s) \<setminus>\<leadsto> d"
        and   p3:"s' = fst (get_sampling_port_status sysconf s pid)"
      shows   "s \<sim> d \<sim> s'"
    using p3 get_sampling_port_status_def vpeq_reflexive_lemma by auto
    

  lemma get_smpl_psts_presrv_lcrsp_e: "local_respect_e (hyperc (Get_Sampling_Portstatus pid))"
    using get_smpl_psts_presrv_lcrsp  exec_event_def  
        prod.simps(2)  vpeq_reflexive_lemma by (auto cong del: vpeq1_def) 

subsubsection{*proving "create queuing port" satisfying the "local respect" property*}
  lemma crt_que_port_notchg_current:
    "\<lbrakk>is_a_partition sysconf (current s); s' = fst (create_queuing_port sysconf s pname)\<rbrakk> 
      \<Longrightarrow> current s = current s'"
    by (clarsimp simp:create_queuing_port_def )    

  text{*the state before and after executing the action "create queuing port" is observ equal to scheduler*}
  lemma crt_que_port_sm_sche:"\<lbrakk>is_a_partition sysconf (current s); 
                                s' = fst (create_queuing_port sysconf s pname)\<rbrakk>
                                      \<Longrightarrow> (s\<sim>(scheduler sysconf)\<sim>s')"
  using crt_que_port_notchg_current part_imp_not_sch by fastforce
   
      

  lemma crt_que_port_notchg_partstate:
                "\<lbrakk>is_a_partition sysconf (current s); is_a_partition sysconf d; 
                s' = fst (create_queuing_port sysconf s pname)\<rbrakk>
                                         \<Longrightarrow> (partitions s) d = (partitions s') d"
   by (clarsimp simp:create_queuing_port_def )

  lemma crt_que_port_notchg_partportsinotherdom:
  assumes p0:"reachable0 s"
    and   p1:"is_a_partition sysconf (current s)"
    and   p3:"(current s) \<noteq> d"
    and   p4:"s' = fst (create_queuing_port sysconf s pname)"
  shows   "get_ports_of_partition s d = get_ports_of_partition s' d"
  proof -
  {
    have "\<forall>p. p\<in>get_ports_of_partition s d \<longrightarrow> p\<in>get_ports_of_partition s' d"
    proof-
    {
      fix p
      assume a0:"p\<in>get_ports_of_partition s d"
      have a1:"p\<in>get_ports_of_partition s' d"
      proof(cases "pname \<in> get_partition_cfg_ports_byid sysconf (current s)")
        assume b0:"pname \<in> get_partition_cfg_ports_byid sysconf (current s)"
        have b1:"p \<noteq> get_portid_in_type (the (get_queuingport_conf sysconf pname))" 
          using b0 port_partition by auto 
        then show ?thesis using b0 port_partition by auto 
      next
        assume c0:"\<not>(pname \<in> get_partition_cfg_ports_byid sysconf (current s))"
        then have c1:"s' = s" by (simp add: create_queuing_port_def p4) 
        then show ?thesis by (simp add: a0) 
      qed
    }
    then show ?thesis by auto
    qed
    moreover
    have "\<forall>p. p\<in>get_ports_of_partition s' d \<longrightarrow> p\<in>get_ports_of_partition s d"
    proof-
    {
      fix p
      assume a0:"p\<in>get_ports_of_partition s' d"
      have "p\<in>get_ports_of_partition s d" 
      proof(cases "pname \<in> get_partition_cfg_ports_byid sysconf (current s)")
        assume b0:"pname \<in> get_partition_cfg_ports_byid sysconf (current s)"
        have b1:"p \<noteq> get_portid_in_type (the (get_queuingport_conf sysconf pname))" 
          using b0 port_partition by auto 
        then show ?thesis using b0 port_partition by auto 
      next
        assume c0:"\<not>(pname \<in> get_partition_cfg_ports_byid sysconf (current s))"
        then have c1:"s' = s" by (simp add: create_queuing_port_def p4) 
        then show ?thesis using a0 by auto  
      qed
    }
    then show ?thesis by auto
    qed
    then show ?thesis using calculation by blast
  }
  qed
       
  lemma crt_que_port_notchg_portsinotherdom:
  assumes p1:"is_a_partition sysconf (current s)"
    and   p3:"(current s) \<noteq> d"
    and   p4:"s' = fst (create_queuing_port sysconf s pname)"
  shows " \<forall>p. p\<in> get_ports_of_partition s d \<longrightarrow> ports (comm s) p = ports (comm s') p"
  proof -
  {    
    fix p
    assume a0:"p \<in> get_ports_of_partition s d"
    have "ports (comm s) p = ports (comm s') p "
    proof -
    {      
      have "ports (comm s) p = ports (comm (fst (create_queuing_port sysconf s pname))) p"
      proof(cases "pname \<in> get_partition_cfg_ports_byid sysconf (current s)")
        assume b0:"pname \<in> get_partition_cfg_ports_byid sysconf (current s)"
        have b1:"p \<noteq> get_portid_in_type (the (get_queuingport_conf sysconf pname))" 
          using b0 port_partition by auto 
        then show ?thesis using b0 port_partition by auto 
      next
        assume c0:"\<not>(pname \<in> get_partition_cfg_ports_byid sysconf (current s))"
        then have c1:"s' = s" by (simp add: create_queuing_port_def p4) 
        then show ?thesis using p4 by auto  
      qed
    }
    then show ?thesis by (simp add: p4)
    qed
  } then show ?thesis by auto
  qed
 

  lemma crt_que_port_notchg_comminotherdom:
  assumes   p0:"reachable0 s"
      and   p1:"is_a_partition sysconf (current s)"
    and   p3:"(current s) \<noteq> d"
    and   p4:"s' = fst (create_queuing_port sysconf s pname)"
  shows   "vpeq_part_comm s d s'"       
  proof-
   have "get_ports_of_partition s d = get_ports_of_partition s' d"
      using crt_que_port_notchg_partportsinotherdom p0 p1 p3 p4 by auto        
   also have "\<forall>p. p \<in> get_ports_of_partition s d \<longrightarrow>
            is_a_queuingport s p = is_a_queuingport s' p \<and>
            is_dest_port s p = is_dest_port s' p \<and> 
            (if is_dest_port s p then get_port_buf_size s p = get_port_buf_size s' p else True)"
   proof -
   {
     fix p
     have "p \<in> get_ports_of_partition s d \<longrightarrow>
          is_a_queuingport s p = is_a_queuingport s' p \<and>
          is_dest_port s p = is_dest_port s' p \<and> 
          (if is_dest_port s p then get_port_buf_size s p = get_port_buf_size s' p else True)"
     using  get_port_buf_size_def is_a_queuingport_def 
             is_dest_port_def 
             crt_que_port_notchg_portsinotherdom get_port_byid_def p1 p3 p4 by auto
   }
   then show ?thesis by auto
   qed
   ultimately show ?thesis by auto
 qed

  lemma crt_que_port_sm_nitfpart:"\<lbrakk>reachable0 s; is_a_partition sysconf (current s); is_a_partition sysconf d;
                                  ((current s) \<setminus>\<leadsto> d); s' = fst (create_queuing_port sysconf s pname)\<rbrakk>
                                        \<Longrightarrow> (s \<sim> d \<sim> s')"
      apply(clarsimp simp:vpeq1_def cong del: is_a_partition_def vpeq_part_comm_def)      
      using trans_imp_not_part sche_imp_not_part 
      apply (simp add: crt_que_port_notchg_partstate)        
      by (metis create_queuing_port_def fst_conv get_queuingport_conf_def port_name_diff)

        
    lemma crt_que_port_presrv_lcrsp:
    assumes p0:"reachable0 s"
      and   p1:"is_a_partition sysconf (current s)"
      and   p2:"(current s) \<setminus>\<leadsto> d"
      and   p3:"s' = fst (create_queuing_port sysconf s pname)"
    shows   "s \<sim> d \<sim> s'"
    proof(cases "is_a_scheduler sysconf d")
      assume a0:"is_a_scheduler sysconf d"
      show ?thesis using a0 crt_que_port_sm_sche[OF p1 p3]  by auto 
    next
      assume a1:"\<not> is_a_scheduler sysconf d"
      show ?thesis
      proof(cases "is_a_partition sysconf d")
        assume b0:"is_a_partition sysconf d"
        show ?thesis using b0 crt_que_port_sm_nitfpart p0 p1 p2 p3 by blast
      next
        assume b1:"\<not> is_a_partition sysconf d"
        show ?thesis
        proof(cases "is_a_transmitter sysconf d")
          assume c0:"is_a_transmitter sysconf d"          
          have "vpeq_transmitter s d s'" unfolding vpeq_transmitter_def
          proof-
            show "comm s = comm s' \<and>  part_ports s = part_ports s'" 
            proof(rule conjI)
            {
              show "comm s = comm s'"
              proof -
              {
              from p1 p2 have "\<not> part_intf_transmitter sysconf (current s)" 
                using interference1_def by (smt a1 c0 non_interference1_def)
              then have "get_partition_cfg_ports (the ((partconf sysconf) (current s))) = {}" 
                using get_partition_cfg_ports_byid_def is_a_partition_def p1 port_partition by fastforce
              then have "pname \<notin> get_partition_cfg_ports_byid sysconf (current s)" 
                by (simp add: get_partition_cfg_ports_byid_def)
              then have "s = s'" by (simp add: create_queuing_port_def p3) 
              }
              then show ?thesis by auto
              qed
              show "part_ports s = part_ports s'"
              proof - 
              {
                from p1 p2 c0 have d0:"\<not> part_intf_transmitter sysconf (current s)" 
                  using interference1_def non_interference1_def by (meson a1) 
                then have d1:"get_partition_cfg_ports_byid sysconf (current s) = {}" using port_partition by blast 
                then have d2:"s=s'" by (smt create_queuing_port_def empty_iff fst_conv p3) 
              }
              then show ?thesis by auto
              qed
            }
            qed
          qed
        
          then show ?thesis using a1 b1 is_a_scheduler_def vpeq1_def by auto          
        next
          assume c1:"\<not> is_a_transmitter sysconf d"
          show ?thesis using a1 b1 c1 is_a_scheduler_def is_a_transmitter_def vpeq1_def by auto
        qed
      qed
    qed

  lemma crt_que_port_presrv_lcrsp_e: "local_respect_e (hyperc (Create_Queuing_Port p))"
    using crt_que_port_presrv_lcrsp  exec_event_def mem_Collect_eq 
       prod.simps(2) singletonD vpeq_reflexive_lemma 
    by (auto cong del: is_a_partition_def   vpeq1_def) 

subsubsection{*proving "send queuing message(may lost)" satisfying the "local respect" property*}

    lemma snd_que_msg_lst_notchg_current:
      "\<lbrakk>is_a_partition sysconf (current s); s' = fst (send_queuing_message_maylost sysconf s pid m)\<rbrakk> 
        \<Longrightarrow> current s = current s'"        
        apply (simp add: insert_msg2queuing_port_def 
                  send_queuing_message_maylost_def replace_msg2queuing_port_def)
        apply(case_tac "ports (comm s) pid")
        apply simp
        apply(case_tac "a")        
        by auto
        
             
    lemma snd_que_msg_lst_sm_sche:"\<lbrakk>is_a_partition sysconf (current s); 
                                  s' = fst (send_queuing_message_maylost sysconf s pid m)\<rbrakk>
                                        \<Longrightarrow> (s\<sim>(scheduler sysconf)\<sim>s')"        
      apply (auto simp add: insert_msg2queuing_port_def vpeq_reflexive_lemma 
                  replace_msg2queuing_port_def send_queuing_message_maylost_def)                                   
      apply(case_tac "ports (comm s) pid")
      apply (simp add: vpeq_reflexive_lemma)
      apply(case_tac "a")
      by (auto simp add: vpeq_reflexive_lemma)
        
    lemma snd_que_msg_lst_notchg_partstate:
                  "\<lbrakk>is_a_partition sysconf (current s); is_a_partition sysconf d; 
                  s' = fst (send_queuing_message_maylost sysconf s pid m)\<rbrakk>
                                           \<Longrightarrow> (partitions s) d = (partitions s') d"
        
    apply(clarsimp simp:insert_msg2queuing_port_def 
           replace_msg2queuing_port_def send_queuing_message_maylost_def)
    apply(case_tac "ports (comm s) pid")
    apply simp
    apply(case_tac "a")        
    by auto
  
  lemma snd_que_msg_lst_notchg_partports:
  assumes p1:"is_a_partition sysconf (current s)"
    and   p2:"s' = fst (send_queuing_message_maylost sysconf s pid m)"
  shows   "part_ports s = part_ports s'"
  proof(cases "\<not> is_a_queuingport s pid 
                        \<or> \<not> is_source_port s pid 
                        \<or> \<not> is_a_port_of_partition s pid (current s)")
    assume b0:"\<not> is_a_queuingport s pid 
                \<or> \<not> is_source_port s pid 
                \<or> \<not> is_a_port_of_partition s pid (current s)"
    with p2 show ?thesis using send_queuing_message_maylost_def by auto 
  next
    assume b1:"\<not>(\<not> is_a_queuingport s pid 
                \<or> \<not> is_source_port s pid
                \<or> \<not> is_a_port_of_partition s pid (current s))"
    show ?thesis
    proof(cases "is_full_portqueuing sysconf s pid")
      assume c0:"is_full_portqueuing sysconf s pid"
      with b1 have c1:"s' = s" by (simp add: p2 replace_msg2queuing_port_def 
                                  send_queuing_message_maylost_def) 
      then show ?thesis by auto 
    next
      assume d0:"\<not> is_full_portqueuing sysconf s pid"
      have d1:"s' = insert_msg2queuing_port s pid m" 
        using b1 d0 p2 send_queuing_message_maylost_def by auto 
      with b1 show ?thesis
        proof(induct "(ports (comm s)) pid")
          case None show ?case using None.hyps d1 insert_msg2queuing_port_def by auto  
        next
          case (Some x) 
          have e0:"(ports (comm s)) pid = Some x" by (simp add: Some.hyps)
          show ?case
          proof(induct "the ((ports (comm s)) pid)")
            case (Queuing x1 x2 x3 x4 x5)
            show ?case by (smt Communication_State.select_convs(1) Communication_State.surjective 
              Communication_State.update_convs(2) Port_Type.simps(5) Queuing.hyps 
              State.select_convs(3) State.select_convs(4) State.surjective State.update_convs(3)
              d1 insert_msg2queuing_port_def option.case_eq_if)  
          next
            case (Sampling x1 x2 x3 x4)
            show ?case using Sampling.hyps d1 e0 insert_msg2queuing_port_def by auto 
          qed
        qed
     qed
   qed

  lemma snd_que_msg_lst_notchg_portsinotherdom:
  assumes p1:"is_a_partition sysconf (current s)"
    and   p3:"(current s) \<noteq> d"
    and   p4:"s' = fst (send_queuing_message_maylost sysconf s pid m)"
  shows " \<forall>p. p\<in> get_ports_of_partition s d \<longrightarrow> ports (comm s) p = ports (comm s') p"
  proof -
  {
    fix p
    have "p \<in> get_ports_of_partition s d \<longrightarrow> ports (comm s) p = ports (comm s') p "
    proof -
    {
      assume a0:"p \<in> get_ports_of_partition s d"
      have a1:"(part_ports s) p = Some d" using a0 get_ports_of_partition_def by auto 
      have "ports (comm s) p = ports (comm s') p"
      proof(cases "p = pid")
        assume b0:"p = pid"
        have b1:"(part_ports s) pid = Some d" using a1 b0 by auto 
        have b2:"\<not> is_a_port_of_partition s pid (current s)" using b1 is_a_port_of_partition_def p3 by auto 
        have b3:"s' = s" by (simp add: b2 p4 send_queuing_message_maylost_def) 
        then show ?thesis by auto
      next
        assume c0:"p \<noteq> pid"
        show ?thesis
        proof(cases "\<not> is_a_queuingport s pid 
                    \<or> \<not> is_source_port s pid 
                    \<or> \<not> is_a_port_of_partition s pid (current s)")
          assume b0:"\<not> is_a_queuingport s pid
                      \<or> \<not> is_source_port s pid
                      \<or> \<not> is_a_port_of_partition s pid (current s)"
          show ?thesis using a1 b0 p4 send_queuing_message_maylost_def by auto 
        next
          assume b1:"\<not>(\<not> is_a_queuingport s pid
                      \<or> \<not> is_source_port s pid
                      \<or> \<not> is_a_port_of_partition s pid (current s))"
          show ?thesis
          proof(cases "is_full_portqueuing sysconf s pid")
            assume c0:"is_full_portqueuing sysconf s pid"
            with b1 have c1:"s' = s" by (simp add: p4 replace_msg2queuing_port_def 
                                        send_queuing_message_maylost_def) 
            then show ?thesis using a1 by auto 
          next
            assume d0:"\<not> is_full_portqueuing sysconf s pid"
            have d1:"s' = insert_msg2queuing_port s pid m" 
              using b1 d0 p4 send_queuing_message_maylost_def by auto 
            with b1 show ?thesis
              proof(induct "(ports (comm s)) pid")
                case None show ?case
                  by (simp add: None.hyps d1 insert_msg2queuing_port_def option.case_eq_if) 
              next
                case (Some x) 
                have e0:"(ports (comm s)) pid = Some x" by (simp add: Some.hyps)
                show ?case
                proof(induct "the ((ports (comm s)) pid)")
                  case (Queuing x1 x2 x3 x4 x5)
                  have f0:"the ((ports (comm s)) pid) = Queuing x1 x2 x3 x4 x5" 
                    by (simp add: Queuing.hyps)
                  show ?case by (smt Communication_State.ext_inject Communication_State.surjective 
                    Communication_State.update_convs(1) Port_Type.simps(5) State.select_convs(3) 
                    State.surjective State.update_convs(3) c0 d1 f0 fun_upd_other 
                    insert_msg2queuing_port_def option.case_eq_if) 
                next
                  case (Sampling x1 x2 x3 x4)
                   have f0:"the ((ports (comm s)) pid) = Sampling x1 x2 x3 x4" 
                    by (simp add: Sampling)
                  show ?case using d1 e0 f0 insert_msg2queuing_port_def by auto 
                qed
              qed
           qed
         qed
      qed
    }
    then show ?thesis by (simp add: p4)
    qed
  }
  then show ?thesis by auto
  qed
  
  lemma get_port_size_eq:
  assumes a0: "p \<noteq> pid"
  shows "get_port_buf_size s p = get_port_buf_size (fst (send_queuing_message_maylost sysconf s pid m)) p"
   apply (simp add: insert_msg2queuing_port_def replace_msg2queuing_port_def send_queuing_message_maylost_def)                                  
   apply(case_tac "ports (comm s) pid")
   apply simp
   apply(case_tac "a")                                  
   using a0 get_port_byid_def get_port_buf_size_def  by auto
   
  lemma snd_que_msg_lst_notchg_comminotherdom:
  assumes   p0:"reachable0 s"
    and   p1:"is_a_partition sysconf (current s)"
    and   p3:"(current s) \<noteq> d"
    and   p4:"s' = fst (send_queuing_message_maylost sysconf s pid m)"
  shows   "vpeq_part_comm s d s'"
  proof-
    from p4 have r0:"part_ports s = part_ports s'" using p1 snd_que_msg_lst_notchg_partports by blast
    then have "get_ports_of_partition s d = get_ports_of_partition s' d" 
     using part_ports_imp_portofpart by blast         
    also have "\<forall>p. p \<in> get_ports_of_partition s d \<longrightarrow>
              is_a_queuingport s p = is_a_queuingport s' p \<and>
              is_dest_port s p = is_dest_port s' p \<and> 
              (if is_dest_port s p then get_port_buf_size s p = get_port_buf_size s' p else True)"
    proof -
    {
     fix p
     have "p \<in> get_ports_of_partition s d \<longrightarrow>
          is_a_queuingport s p = is_a_queuingport s' p \<and>
          is_dest_port s p = is_dest_port s' p \<and> 
          (if is_dest_port s p then get_port_buf_size s p = get_port_buf_size s' p else True)"
     proof(rule impI)
     {
       assume a0:"p \<in> get_ports_of_partition s d"       
       have "is_a_queuingport s p = is_a_queuingport s' p"
         unfolding is_a_queuingport_def using snd_que_msg_lst_notchg_portsinotherdom
              a0 p1 p3 p4 interference1_def non_interference1_def by auto              
       moreover have "is_dest_port s p = is_dest_port s' p \<and> 
              (if is_dest_port s p then get_port_buf_size s p = get_port_buf_size s' p else True) "
       proof(rule conjI)
       {
         show "is_dest_port s p = is_dest_port s' p"
          unfolding is_dest_port_def using snd_que_msg_lst_notchg_portsinotherdom
            a0 p1 p3 p4 interference1_def non_interference1_def by smt
         show "if is_dest_port s p then get_port_buf_size s p = get_port_buf_size s' p else True"              
         proof -
         {
          assume c0:"is_dest_port s p"
          have "get_port_buf_size s p = get_port_buf_size s' p"
          proof(cases "p = pid")
            assume d0:"p = pid"
            with c0 have "is_dest_port s pid" by simp
            then have d1:"\<not> is_source_port s pid" by (simp add: dest_port_not_src) 
            with p4 have "s' = s" unfolding send_queuing_message_maylost_def by simp
            then show ?thesis by simp
          next
            assume d0: "p \<noteq> pid"                      
            with p4 get_port_size_eq show ?thesis by simp
          qed
        } then show ?thesis by auto
          qed    
        }
        qed
       
        ultimately  show "is_a_queuingport s p = is_a_queuingport s' p \<and>
              is_dest_port s p = is_dest_port s' p \<and> 
              (if is_dest_port s p then get_port_buf_size s p = get_port_buf_size s' p else True)"
        by auto    
    } qed
   }
   then show ?thesis by auto qed
   ultimately show ?thesis by auto 
 qed

  lemma snd_que_msg_lst_sm_nitfpart:"\<lbrakk>reachable0 s; is_a_partition sysconf (current s); is_a_partition sysconf d;
                                  ((current s) \<setminus>\<leadsto> d); s' = fst (send_queuing_message_maylost sysconf s pid m)\<rbrakk>
                                        \<Longrightarrow> (s \<sim> d \<sim> s')"             
    apply(clarsimp cong del: is_a_partition_def)
    apply(rule conjI)
    using trans_imp_not_part  trans_imp_not_part apply fastforce
    apply(rule impI)
    apply(rule conjI)
    using  sche_imp_not_part apply fastforce
    apply(rule impI)        
    apply(rule conjI)
    apply (simp add: snd_que_msg_lst_notchg_partstate)
    by (meson snd_que_msg_lst_notchg_comminotherdom vpeq_part_comm_def)

      
        
  lemma snd_que_msg_lst_presrv_lcrsp:
  assumes p0:"reachable0 s"
    and   p1:"is_a_partition sysconf (current s)"
    and   p2:"(current s) \<setminus>\<leadsto> d"
    and   p3:"s' = fst (send_queuing_message_maylost sysconf s pid m)"
  shows   "s \<sim> d \<sim> s'"
  proof(cases "is_a_scheduler sysconf d")
    assume a0:"is_a_scheduler sysconf d"
    show ?thesis using a0 is_a_scheduler_def snd_que_msg_lst_sm_sche[OF p1 p3] by auto 
  next
    assume a1:"\<not> is_a_scheduler sysconf d"
    show ?thesis
    proof(cases "is_a_partition sysconf d")
      assume b0:"is_a_partition sysconf d"
      show ?thesis using b0 snd_que_msg_lst_sm_nitfpart p0 p1 p2 p3 by blast
    next
      assume b1:"\<not> is_a_partition sysconf d"
      show ?thesis
      proof(cases "is_a_transmitter sysconf d")
        assume c0:"is_a_transmitter sysconf d"
        show ?thesis
        proof -
        {
          have "comm s = comm s' \<and>  part_ports s = part_ports s'" 
          proof(rule conjI)
          {
            from p1 p2 have "\<not> part_intf_transmitter sysconf (current s)" 
              using interference1_def by (smt a1 c0 non_interference1_def)
            then have d1:"get_partition_cfg_ports (the ((partconf sysconf) (current s))) = {}" 
              using get_partition_cfg_ports_byid_def is_a_partition_def p1 port_partition by fastforce
            then have d2:"get_partition_cfg_ports_byid sysconf (current s) = {}"
              by (simp add: get_partition_cfg_ports_byid_def) 
            then have "\<not> is_a_port_of_partition s pid (current s)" 
            proof(cases "(ports (comm s)) pid = None")
              assume e0:"(ports (comm s)) pid = None"
              then show ?thesis using port_cons_reach_state[OF p0] 
                port_consistent_def is_a_port_of_partition_def by auto              
            next
              assume e0:"\<not>((ports (comm s)) pid = None)"
              then show ?thesis using port_cons_reach_state[OF p0] 
                port_consistent_def d2 is_a_port_of_partition_def by auto
            qed
            then have d0:"s = s'" by (auto simp add: send_queuing_message_maylost_def p3) 
            then show "comm s = comm s'" by simp
            with d0 show "part_ports s = part_ports s'" by simp
          }
          qed        
        }
        then show ?thesis using a1 b1 by auto
        qed
      next
        assume c1:"\<not> is_a_transmitter sysconf d"
        show ?thesis using a1 b1 c1 by auto
      qed
    qed
  qed

  lemma snd_que_msg_lst_presrv_lcrsp_e: "local_respect_e (hyperc (Send_Queuing_Message p m))"
    using snd_que_msg_lst_presrv_lcrsp  exec_event_def mem_Collect_eq 
        prod.simps(2) singletonD vpeq_reflexive_lemma 
    by (auto cong del: is_a_partition_def   vpeq1_def) 

subsubsection{*proving "receive queuing message" satisfying the "local respect" property*}

  lemma rec_que_msg_notchg_current:
      "\<lbrakk>is_a_partition sysconf (current s); s' = fst (receive_queuing_message s pid)\<rbrakk> 
        \<Longrightarrow> current s = current s'"
        apply(clarsimp simp:receive_queuing_message_def remove_msg_from_queuingport_def)
        apply(case_tac "ports (comm s) pid")
        apply simp
        apply(case_tac "a")
        by auto
        
             
    lemma rec_que_msg_sm_sche:"\<lbrakk>is_a_partition sysconf (current s); 
                                  s' = fst (receive_queuing_message s pid)\<rbrakk>
                                        \<Longrightarrow> (s\<sim>(scheduler sysconf)\<sim>s')"
       apply(clarsimp simp:receive_queuing_message_def remove_msg_from_queuingport_def cong del:  vpeq1_def)
        apply(case_tac "ports (comm s) pid")                
        apply (simp add: vpeq_reflexive_lemma cong del: vpeq1_def)                
        apply(case_tac "a")        
        using vpeq_reflexive_lemma by auto
        
    lemma rec_que_msg_notchg_partstate:
                  "\<lbrakk>is_a_partition sysconf (current s); is_a_partition sysconf d; 
                  s' = fst (receive_queuing_message s pid)\<rbrakk>
                                           \<Longrightarrow> (partitions s) d = (partitions s') d"
        apply(clarsimp simp:receive_queuing_message_def remove_msg_from_queuingport_def)
        apply(case_tac "ports (comm s) pid")
        apply simp
        apply(case_tac "a")
        by (auto simp add: vpeq_reflexive_lemma)
        
    lemma rec_que_msg_notchg_partports:
    assumes p1:"is_a_partition sysconf (current s)"
      and   p2:"s' = fst (receive_queuing_message s pid)"
    shows   "part_ports s = part_ports s'"
    
    proof(cases "(\<not> is_a_queuingport s pid
                    \<or> \<not> is_a_port_of_partition s pid (current s)
                    \<or> \<not> is_dest_port s pid
                    \<or> is_empty_portqueuing s pid)")
      assume b0:"(\<not> is_a_queuingport s pid
                \<or> \<not> is_a_port_of_partition s pid (current s)
                \<or> \<not> is_dest_port s pid 
                \<or> is_empty_portqueuing s pid)"
      show ?thesis using b0 p2 receive_queuing_message_def by auto 
    next
      assume b1:"\<not>(\<not> is_a_queuingport s pid
                \<or> \<not> is_a_port_of_partition s pid (current s)
                \<or> \<not> is_dest_port s pid 
                \<or> is_empty_portqueuing s pid)"
      have b2:"s' = fst (remove_msg_from_queuingport s pid)"
        using b1 p2 receive_queuing_message_def by auto 
      then show ?thesis
      proof(induct "(ports (comm s)) pid")
        case None show ?case using None.hyps b2 remove_msg_from_queuingport_def by auto  
      next
        case (Some x) 
        have e0:"(ports (comm s)) pid = Some x" by (simp add: Some.hyps)
        show ?case
          proof(induct "the ((ports (comm s)) pid)")
            case (Queuing x1 x2 x3 x4 x5)
            show ?case by (smt Port_Type.simps(5) Queuing.hyps State.select_convs(4) 
              State.surjective State.update_convs(3) b2 eq_fst_iff option.case_eq_if 
              remove_msg_from_queuingport_def)  
          next
            case (Sampling x1 x2 x3 x4)
            show ?case using Sampling.hyps b2 e0 remove_msg_from_queuingport_def by auto 
          qed
      qed
    qed
            
    lemma rec_que_msg_notchg_portsinotherdom:
    assumes p1:"is_a_partition sysconf (current s)"
      and   p3:"(current s) \<noteq> d"
      and   p4:"s' = fst (receive_queuing_message s pid)"
    shows " \<forall>p. p\<in> get_ports_of_partition s d \<longrightarrow> ports (comm s) p = ports (comm s') p"
    proof -
    {
      show ?thesis
      proof -
      {
        fix p
        have "p \<in> get_ports_of_partition s d \<longrightarrow> ports (comm s) p = ports (comm s') p "
        proof -
        {
          assume a0:"p \<in> get_ports_of_partition s d"
          have a1:"(part_ports s) p = Some d" using a0 get_ports_of_partition_def by auto 
          have "ports (comm s) p = ports (comm s') p"
          proof(cases "p = pid")
            assume b0:"p = pid"
            have b1:"(part_ports s) pid = Some d" using a1 b0 by auto 
            have b2:"\<not> is_a_port_of_partition s pid (current s)" using b1 is_a_port_of_partition_def p3 by auto 
            have b3:"s' = s" by (simp add: b2 p4 receive_queuing_message_def) 
            then show ?thesis by auto
          next
            assume c0:"p \<noteq> pid"
            show ?thesis
            proof(induct "(ports (comm s)) pid")
              case None show ?case
                by (simp add: None.hyps is_dest_port_def option.case_eq_if p4 receive_queuing_message_def)
            next
              case (Some x) 
              have e0:"(ports (comm s)) pid = Some x" by (simp add: Some.hyps)
              show ?case
              proof(induct "the ((ports (comm s)) pid)")
                case (Queuing x1 x2 x3 x4 x5)
                have f0:"the ((ports (comm s)) pid) = Queuing x1 x2 x3 x4 x5" 
                  by (simp add: Queuing.hyps)
                show ?case  by (smt Communication_State.ext_inject Communication_State.surjective 
                  Communication_State.update_convs(1) Port_Type.simps(5) State.select_convs(3) 
                  State.surjective State.update_convs(3) c0 f0 fst_conv fun_upd_other 
                  option.case_eq_if p4 receive_queuing_message_def remove_msg_from_queuingport_def)  
               next
                case (Sampling x1 x2 x3 x4)
                 have f0:"the ((ports (comm s)) pid) = Sampling x1 x2 x3 x4" 
                  by (simp add: Sampling)
                show ?case using e0 f0 p4 receive_queuing_message_def 
                  remove_msg_from_queuingport_def by auto 
               qed
            qed
          qed
        }
        then show ?thesis by (simp add: p4)
        qed
      }
      then show ?thesis by auto
      qed
    }
    qed

    lemma rec_que_msg_notchg_comminotherdom:
    assumes   p0:"reachable0 s"
      and   p1:"is_a_partition sysconf (current s)"
      and   p3:"(current s) \<noteq> d"
      and   p4:"s' = fst (receive_queuing_message s pid)"
    shows   "vpeq_part_comm s d s'"       
     proof -
       from p4 have r0:"part_ports s = part_ports s'" using p1 rec_que_msg_notchg_partports by simp 
       then have "get_ports_of_partition s d = get_ports_of_partition s' d"
        using part_ports_imp_portofpart  by blast            
       also have "\<forall>p. p \<in> get_ports_of_partition s d \<longrightarrow>
                is_a_queuingport s p = is_a_queuingport s' p \<and>
                is_dest_port s p = is_dest_port s' p \<and> 
                (if is_dest_port s p then get_port_buf_size s p = get_port_buf_size s' p else True)"
         using  is_a_queuingport_def is_dest_port_def get_port_buf_size_def 
                rec_que_msg_notchg_portsinotherdom get_port_byid_def p1 p3 p4 by auto                  
     ultimately show ?thesis by auto
     qed

    lemma rec_que_msg_sm_nitfpart:"\<lbrakk>reachable0 s; is_a_partition sysconf (current s); is_a_partition sysconf d;
                                    ((current s) \<setminus>\<leadsto> d); s' = fst (receive_queuing_message s pid)\<rbrakk>
                                          \<Longrightarrow> (s \<sim> d \<sim> s')"
      apply(clarsimp cong del: is_a_partition_def vpeq_part_comm_def)
      apply(rule conjI)
      using  trans_imp_not_part apply fastforce
      apply(rule impI)
      apply(rule conjI)
      using sche_imp_not_part apply fastforce
      apply(clarsimp simp:vpeq_part_def cong del: is_a_partition_def vpeq_part_comm_def)
      apply(rule conjI)
      apply (simp add: rec_que_msg_notchg_partstate  cong del: is_a_partition_def)
      using rec_que_msg_notchg_comminotherdom by metis

  lemma rec_que_msg_presrv_lcrsp:
      assumes p0:"reachable0 s"
        and   p1:"is_a_partition sysconf (current s)"
        and   p2:"(current s) \<setminus>\<leadsto> d"
        and   p3:"s' = fst (receive_queuing_message s pid)"
      shows   "s \<sim> d \<sim> s'"
  proof(cases "is_a_scheduler sysconf d")
    assume a0:"is_a_scheduler sysconf d"
    show ?thesis using a0 is_a_scheduler_def rec_que_msg_sm_sche[OF p1 p3] by auto 
  next
    assume a1:"\<not> is_a_scheduler sysconf d"
    show ?thesis
    proof(cases "is_a_partition sysconf d")
      assume b0:"is_a_partition sysconf d"
      show ?thesis using  b0 rec_que_msg_sm_nitfpart p0 p1 p2 p3 by blast
    next
      assume b1:"\<not> is_a_partition sysconf d"
      show ?thesis
      proof(cases "is_a_transmitter sysconf d")
        assume c0:"is_a_transmitter sysconf d"
        show ?thesis
        proof -
        {
          have "comm s = comm s' \<and>  part_ports s = part_ports s'" 
          proof-
          {
            from p1 p2 have "\<not> part_intf_transmitter sysconf (current s)" 
              using interference1_def by (smt a1 c0 non_interference1_def)
            then have d1:"get_partition_cfg_ports (the ((partconf sysconf) (current s))) = {}" 
              using get_partition_cfg_ports_byid_def is_a_partition_def p1 port_partition by fastforce
            then have d2:"get_partition_cfg_ports_byid sysconf (current s) = {}"
              by (simp add: get_partition_cfg_ports_byid_def) 
            then have "\<not> is_a_port_of_partition s pid (current s)" 
            proof(cases "(ports (comm s)) pid = None")
              assume e0:"(ports (comm s)) pid = None"
              thus ?thesis using port_cons_reach_state[OF p0] 
                port_consistent_def is_a_port_of_partition_def by auto 
            next
              assume e0:"\<not>((ports (comm s)) pid = None)"
              thus ?thesis using port_cons_reach_state[OF p0] 
                d2 port_consistent_def is_a_port_of_partition_def by auto 
            qed
            then show ?thesis by (auto simp add: receive_queuing_message_def p3)  
          }
          qed          
        }
        then show ?thesis using a1 b1 is_a_scheduler_def vpeq1_def by auto
        qed
      next
        assume c1:"\<not> is_a_transmitter sysconf d"
        show ?thesis using a1 b1 c1 is_a_scheduler_def is_a_transmitter_def vpeq1_def by auto
      qed
    qed
  qed

  lemma rec_que_msg_presrv_lcrsp_e: "local_respect_e (hyperc (Receive_Queuing_Message p))"
    using rec_que_msg_presrv_lcrsp  exec_event_def prod.simps(2)  vpeq_reflexive_lemma 
    by (auto cong del: is_a_partition_def  vpeq1_def) 
subsubsection{*proving "get queuing portid" satisfying the "local respect" property*}

  lemma get_que_pid_presrv_lcrsp:
      assumes p0:"reachable0 s"
        and   p1:"is_a_partition sysconf (current s)"
        and   p2:"(current s) \<setminus>\<leadsto> d"
        and   p3:"s' = fst (get_queuing_port_id sysconf s pname)"
      shows   "s \<sim> d \<sim> s'"
    proof -
      have a0:"s' = s" by (simp add: p3 get_queuing_port_id_def) 
      then show ?thesis using vpeq_reflexive_lemma by auto
    qed

  lemma get_que_pid_presrv_lcrsp_e: "local_respect_e (hyperc (Get_Queuing_Portid p))"
    using get_que_pid_presrv_lcrsp  exec_event_def prod.simps(2)  vpeq_reflexive_lemma 
   by (auto cong del:  vpeq1_def) 

subsubsection{*proving "get queuing port status" satisfying the "local respect" property*}

  lemma get_que_psts_presrv_lcrsp:
      assumes p0:"reachable0 s"
        and   p1:"is_a_partition sysconf (current s)"
        and   p2:"(current s) \<setminus>\<leadsto> d"
        and   p3:"s' = fst (get_queuing_port_status sysconf s pid)"
      shows   "s \<sim> d \<sim> s'"
    proof -
      have a0:"s' = s" by (simp add: p3 get_queuing_port_status_def) 
      then show ?thesis using vpeq_reflexive_lemma by auto
    qed

  lemma get_que_psts_presrv_lcrsp_e: "local_respect_e (hyperc (Get_Queuing_Portstatus p))"
    using get_que_psts_presrv_lcrsp exec_event_def prod.simps(2) vpeq_reflexive_lemma
   by (auto cong del:  vpeq1_def) 

subsubsection{*proving "clear queuing port" satisfying the "local respect" property*}
  
  lemma clr_que_port_notchg_current:
      "\<lbrakk>is_a_partition sysconf (current s); s' = clear_queuing_port s pid\<rbrakk> 
        \<Longrightarrow> current s = current s'"
        by (clarsimp simp:clear_queuing_port_def Let_def)

    lemma clr_que_port_sm_sche:"\<lbrakk>is_a_partition sysconf (current s); 
                                  s' = clear_queuing_port s pid\<rbrakk>
                                        \<Longrightarrow> (s\<sim>(scheduler sysconf)\<sim>s')"
       by (clarsimp simp:clear_queuing_port_def )

       
    lemma clr_que_port_notchg_partstate:
                  "\<lbrakk>is_a_partition sysconf (current s); is_a_partition sysconf d; 
                   s' = clear_queuing_port s pid\<rbrakk> \<Longrightarrow> (partitions s) d = (partitions s') d"
          by (clarsimp simp:clear_queuing_port_def)
        
    lemma clr_que_port_notchg_partports:
        assumes p1:"s' = clear_queuing_port s pid"
        shows   "part_ports s = part_ports s'"
        proof(cases "\<not> is_a_queuingport s pid
                \<or> \<not> is_a_port_of_partition s pid (current s)
                \<or> \<not> is_dest_port s pid")
          assume b0:"\<not> is_a_queuingport s pid
                \<or> \<not> is_a_port_of_partition s pid (current s)
                \<or> \<not> is_dest_port s pid"
          then show ?thesis using p1 clear_queuing_port_def by auto 
        next
          assume b1:"\<not>(\<not> is_a_queuingport s pid
                \<or> \<not> is_a_port_of_partition s pid (current s)
                \<or> \<not> is_dest_port s pid)"
          with p1 show ?thesis unfolding clear_queuing_port_def Let_def by simp
            
        qed
       
    lemma clr_que_port_notchg_portsinotherdom:
        assumes p1:"is_a_partition sysconf (current s)"
          and   p3:"(current s) \<noteq> d"
          and   p4:"s' = clear_queuing_port s pid"
        shows " \<forall>p. p\<in> get_ports_of_partition s d \<longrightarrow> ports (comm s) p = ports (comm s') p"
   proof -
    {
      fix p
      assume a0:"p \<in> get_ports_of_partition s d"
      have "p \<in> get_ports_of_partition s d \<longrightarrow> ports (comm s) p = ports (comm s') p "
      proof -
      {
        have a1:"(part_ports s) p = Some d" using a0 get_ports_of_partition_def by auto 
        have "ports (comm s) p = ports (comm s') p"
        proof(cases "\<not> is_a_queuingport s pid
                \<or> \<not> is_a_port_of_partition s pid (current s)
                \<or> \<not> is_dest_port s pid")
          assume b0:"\<not> is_a_queuingport s pid
                    \<or> \<not> is_a_port_of_partition s pid (current s)
                    \<or> \<not> is_dest_port s pid"
          with p4 have b1:"s' = s" unfolding clear_queuing_port_def by auto
          then show ?thesis using a1 by auto 
        next
          assume b1:"\<not>(\<not> is_a_queuingport s pid
                    \<or> \<not> is_a_port_of_partition s pid (current s)
                    \<or> \<not> is_dest_port s pid)"
          with p4 show ?thesis unfolding clear_queuing_port_def Let_def
            using a1 is_a_port_of_partition_def p3 by auto 
        qed
      }
      then show ?thesis by (simp add: p4)
      qed
    }
    then show ?thesis by auto
    qed
    


  lemma clr_que_port_notchg_comminotherdom:
    assumes   p0:"reachable0 s"
      and   p1:"is_a_partition sysconf (current s)"
      and   p3:"(current s) \<noteq> d"
      and   p4:"s' = clear_queuing_port s pid"
    shows   "vpeq_part_comm s d s'"
         
   proof -
     from p4 have r0: "part_ports s = part_ports s'" using clr_que_port_notchg_partports by blast
        
     then have "get_ports_of_partition s d = get_ports_of_partition s' d"
        using part_ports_imp_portofpart by blast
     
      moreover have"\<forall>p. p \<in> get_ports_of_partition s d \<longrightarrow>
              is_a_queuingport s p = is_a_queuingport s' p \<and>
              is_dest_port s p = is_dest_port s' p \<and> 
              (if is_dest_port s p then get_port_buf_size s p = get_port_buf_size s' p else True)"
     using  is_dest_port_def get_port_buf_size_def is_a_queuingport_def
                clr_que_port_notchg_portsinotherdom get_port_byid_def p1 p3 p4 by auto
     ultimately show ?thesis by auto
   qed

    lemma clr_que_port_sm_nitfpart:"\<lbrakk>reachable0 s; is_a_partition sysconf (current s); is_a_partition sysconf d;
                                    ((current s) \<setminus>\<leadsto> d); s' = clear_queuing_port s pid\<rbrakk>
                                          \<Longrightarrow> (s \<sim> d \<sim> s')"
        apply(clarsimp  cong del: is_a_partition_def interference1_def non_interference1_def vpeq_part_comm_def)
        apply(rule conjI)
        using trans_imp_not_part apply fastforce
        apply(rule impI)
        apply(rule conjI)
        using sche_imp_not_part apply fastforce
        apply(clarsimp cong del: is_a_partition_def interference1_def non_interference1_def vpeq_part_comm_def)
        apply(rule conjI)
        apply (simp add: clr_que_port_notchg_partstate 
                    cong del: vpeq_part_comm_def is_a_partition_def interference1_def non_interference1_def)
        using clr_que_port_notchg_comminotherdom nintf_neq by blast
        

  lemma clr_que_port_presrv_lcrsp:
      assumes p0:"reachable0 s"
        and   p1:"is_a_partition sysconf (current s)"
        and   p2:"(current s) \<setminus>\<leadsto> d"
        and   p3:"s' = clear_queuing_port s pid"
      shows   "s \<sim> d \<sim> s'"
    proof(cases "is_a_scheduler sysconf d")
      assume a0:"is_a_scheduler sysconf d"
      show ?thesis using a0 is_a_scheduler_def clr_que_port_sm_sche[OF p1 p3] by auto
    next
      assume a1:"\<not> is_a_scheduler sysconf d"
      show ?thesis
        proof(cases "is_a_partition sysconf d")
          assume b0:"is_a_partition sysconf d"
          show ?thesis  using  clr_que_port_sm_nitfpart [OF p0 p1 b0 p2 p3]  by blast
        next
          assume b1:"\<not> is_a_partition sysconf d"
          show ?thesis
          proof(cases "is_a_transmitter sysconf d")
            assume c0:"is_a_transmitter sysconf d"
            show ?thesis
              proof -
              {
                have "vpeq_transmitter s d s'" unfolding vpeq_transmitter_def
                proof-
                  show "comm s = comm s' \<and>  part_ports s = part_ports s'" 
                  proof(rule conjI)
                  {
                    from p1 p2 have "\<not> part_intf_transmitter sysconf (current s)" 
                      using interference1_def by (smt a1 c0 non_interference1_def)
                    then have d1:"get_partition_cfg_ports (the ((partconf sysconf) (current s))) = {}" 
                      using get_partition_cfg_ports_byid_def  p1 port_partition by fastforce
                    then have d2:"get_partition_cfg_ports_byid sysconf (current s) = {}"
                      by (simp add: get_partition_cfg_ports_byid_def) 
                    then have "\<not> is_a_port_of_partition s pid (current s)" 
                      proof(cases "(ports (comm s)) pid = None")
                        assume e0:"(ports (comm s)) pid = None"
                        from p0 have e1:"port_consistent s" by (simp add: port_cons_reach_state) 
                        with e0 have e1:"(part_ports s) pid = None" unfolding port_consistent_def by auto
                        show ?thesis by (simp add: e1 is_a_port_of_partition_def) 
                      next
                        assume e0:"\<not>((ports (comm s)) pid = None)"
                        from p0 have e1:"port_consistent s" by (simp add: port_cons_reach_state) 
                        then have "get_portname_by_type (the ((ports (comm s)) pid)) \<in>
                            get_partition_cfg_ports_byid sysconf (the ((part_ports s) pid)) "
                            using e0 port_consistent_def by blast
                        with d2 have "current s \<noteq> the ((part_ports s) pid)" by auto
                        then show ?thesis using is_a_port_of_partition_def by auto
                      qed
                    then have d0:"s = s'" by (smt clear_queuing_port_def fst_conv p3) 
                    then show "comm s = comm s'" by simp
                    with d0 show "part_ports s = part_ports s'" by simp
                  }
                  qed
                qed
              }
              then show ?thesis using a1 b1 is_a_scheduler_def vpeq1_def by auto
              qed
          next
            assume c1:"\<not> is_a_transmitter sysconf d"
            show ?thesis using a1 b1 c1 is_a_scheduler_def is_a_transmitter_def vpeq1_def by auto
          qed
        qed
    qed

  lemma clr_que_port_presrv_lcrsp_e: "local_respect_e (hyperc (Clear_Queuing_Port p))"
    using clr_que_port_presrv_lcrsp exec_event_def prod.simps(2)  vpeq_reflexive_lemma 
    by (auto cong del:   vpeq1_def) 

subsubsection{*proving "get partition statue" satisfying the "local respect" property*}
  lemma get_part_status_presrv_lcrsp:
      assumes p0:"reachable0 s"
        and   p1:"is_a_partition sysconf (current s)"
        and   p2:"(current s) \<setminus>\<leadsto> d"
        and   p3:"s' = fst (get_partition_status sysconf s)"
      shows   "s \<sim> d \<sim> s'"
    proof -
      have a0:"s' = s" by (simp add: p3 get_partition_status_def) 
      then show ?thesis using vpeq_reflexive_lemma by auto 
    qed

  lemma get_part_status_presrv_lcrsp_e: "local_respect_e (hyperc (Get_Partition_Status))"
    using get_part_status_presrv_lcrsp  exec_event_def prod.simps(2)  vpeq_reflexive_lemma 
    by (auto cong del: is_a_partition_def  vpeq1_def) 

subsubsection{*proving "set partition mode" satisfying the "local respect" property*}

  lemma set_part_mode_notchg_current:
      "\<lbrakk>is_a_partition sysconf (current s); s' = set_partition_mode sysconf s m\<rbrakk> 
        \<Longrightarrow> current s = current s'"
        apply(clarsimp simp:set_partition_mode_def)
        done

  lemma set_part_mode_sm_sche:"\<lbrakk>is_a_partition sysconf (current s); 
                                s' = set_partition_mode sysconf s m\<rbrakk>
                                      \<Longrightarrow> (s\<sim>(scheduler sysconf)\<sim>s')"
     using set_part_mode_notchg_current  part_imp_not_sch by fastforce

  lemma set_part_mode_notchg_partstate_inotherdom:
                "\<lbrakk>is_a_partition sysconf (current s); is_a_partition sysconf d; current s \<noteq> d;
                s' = set_partition_mode sysconf s m\<rbrakk>
                      \<Longrightarrow> (partitions s) d = (partitions s') d"
      apply(clarsimp simp:set_partition_mode_def)
      done
      
  lemma set_part_mode_notchg_port:
      "\<lbrakk>is_a_partition sysconf (current s); s' = set_partition_mode sysconf s m\<rbrakk>
      \<Longrightarrow> \<forall>p. p\<in> get_ports_of_partition s d \<longrightarrow> ports (comm s) p = ports (comm s') p"
      apply(clarsimp simp:set_partition_mode_def)
      done

  lemma set_part_mode_notchg_partports:
      "\<lbrakk>is_a_partition sysconf (current s); s' = set_partition_mode sysconf s m\<rbrakk>\<Longrightarrow>
          part_ports s = part_ports s'"
     apply(clarsimp simp:set_partition_mode_def)
     done

  lemma set_part_mode_notchg_comm:
      assumes   p0:"reachable0 s"
          and   p1:"is_a_partition sysconf (current s)"
        and   p3:"(current s) \<noteq> d"
        and   p4:"s' = set_partition_mode sysconf s m"
      shows   "vpeq_part_comm s d s'"
        using get_ports_of_partition_def no_cfgport_impl_noports p0 p1 p4 
          port_partition set_part_mode_notchg_partports by fastforce 

  lemma set_part_mode_notchg_comm2:
      "\<lbrakk>reachable0 s; is_a_partition sysconf (current s); (current s) \<noteq> d; s' = set_partition_mode sysconf s m\<rbrakk>
      \<Longrightarrow> comm s = comm s'"
    apply(clarsimp simp:set_partition_mode_def)
    done

  lemma set_part_mode_sm_nitfpart:"\<lbrakk>reachable0 s; is_a_partition sysconf (current s); is_a_partition sysconf d;
                                    ((current s) \<setminus>\<leadsto> d); s' = set_partition_mode sysconf s m\<rbrakk>
                                          \<Longrightarrow> (s \<sim> d \<sim> s')"
        apply(clarsimp cong del: is_a_partition_def non_interference1_def vpeq_part_comm_def)
        apply(rule conjI)
        using is_a_transmitter_def trans_imp_not_part apply blast
        apply(rule impI)
        apply(rule conjI)
        using is_a_scheduler_def sche_imp_not_part apply blast
        apply(clarsimp simp:vpeq_part_def cong del: is_a_partition_def non_interference1_def vpeq_part_comm_def)
        apply(rule conjI)
        using  set_part_mode_notchg_partstate_inotherdom apply fastforce
        using set_part_mode_notchg_comm nintf_neq by blast 

  lemma set_part_mode_presrv_lcrsp:
      assumes p0:"reachable0 s"
        and   p1:"is_a_partition sysconf (current s)"
        and   p2:"(current s) \<setminus>\<leadsto> d"
        and   p3:"s' = set_partition_mode sysconf s m"
      shows   "s \<sim> d \<sim> s'"
    proof(cases "is_a_scheduler sysconf d")
      assume a0:"is_a_scheduler sysconf d"
      show ?thesis using a0 set_part_mode_sm_sche[OF p1] is_a_scheduler_def p3 by auto 
    next
      assume a1:"\<not> is_a_scheduler sysconf d"
      show ?thesis
        proof(cases "is_a_partition sysconf d")
          assume b0:"is_a_partition sysconf d"
          show ?thesis using b0 set_part_mode_sm_nitfpart p0 p1 p2 p3 by blast
        next
          assume b1:"\<not> is_a_partition sysconf d"
          show ?thesis
          proof(cases "is_a_transmitter sysconf d")
            assume c0:"is_a_transmitter sysconf d"
            show ?thesis
              proof -
              {
                have "vpeq_transmitter s d s'" unfolding vpeq_transmitter_def
                proof-
                  show "comm s = comm s' \<and>  part_ports s = part_ports s'" 
                    using set_part_mode_notchg_partports set_part_mode_notchg_comm2
                      by (metis b1 p0 p1 p3) 
                qed
              }
              then show ?thesis using a1 b1 is_a_scheduler_def vpeq1_def by auto
              qed
          next
            assume c1:"\<not> is_a_transmitter sysconf d"
            show ?thesis using a1 b1 c1 is_a_scheduler_def is_a_transmitter_def vpeq1_def by auto
          qed
        qed
    qed

  lemma set_part_mode_presrv_lcrsp_e: "local_respect_e (hyperc (Set_Partition_Mode p))"
    using set_part_mode_presrv_lcrsp  exec_event_def prod.simps(2)  vpeq_reflexive_lemma 
     by (auto cong del:   vpeq1_def) 

subsubsection{*proving "schedule" satisfying the "local respect" property*}
  lemma schedule_presrv_lcrsp:
      assumes p0:"(scheduler sysconf) \<setminus>\<leadsto> d"        
      shows   "s \<sim> d \<sim> s'"
      using p0 by auto

  lemma schedule_presrv_lcrsp_e: "local_respect_e (sys Schedule)"
    using schedule_presrv_lcrsp exec_event_def prod.simps(2) vpeq_reflexive_lemma by auto

subsubsection{*proving "Transfer Sampling Message" satisfying the "local respect" property*}

  lemma trans_smpl_msg_notchg_current:
      "\<lbrakk>is_a_transmitter sysconf (current s); s' = transf_sampling_msg s c\<rbrakk> 
        \<Longrightarrow> current s = current s'"
        apply(induct c)
        apply (clarsimp simp:update_sampling_ports_msg_def Let_def)
        by simp
        
  lemma trans_smpl_msg_sm_sche:"\<lbrakk>is_a_transmitter sysconf (current s); 
                                s' = transf_sampling_msg s c\<rbrakk>
                                      \<Longrightarrow> (s\<sim>(scheduler sysconf)\<sim>s')"
     using trans_smpl_msg_notchg_current sch_not_trans vpeq1_def vpeq_sched_def by presburger 

  lemma trans_smpl_msg_notchg_partstate:
                "\<lbrakk>is_a_transmitter sysconf (current s); is_a_partition sysconf d; 
                 s' = transf_sampling_msg s c\<rbrakk> \<Longrightarrow> (partitions s) d = (partitions s') d"
     apply(induct c)
     apply (clarsimp simp:transf_sampling_msg_def Let_def)
     apply (clarsimp simp:update_sampling_ports_msg_def Let_def)
     by (simp add: vpeq_reflexive_lemma)

  lemma trans_smpl_msg_notchg_partports:
      "s' = transf_sampling_msg s c \<longrightarrow> part_ports s = part_ports s'"
      proof(induct c)
        case (Channel_Sampling name sn dns) show ?case
          proof(cases "get_portid_by_name s sn\<noteq>None \<and> card (get_portids_by_names s dns) = card dns")
          {
            assume a0:"get_portid_by_name s sn\<noteq>None \<and> card (get_portids_by_names s dns) = card dns"
            show ?thesis unfolding transf_sampling_msg_def update_sampling_ports_msg_def Let_def by simp
          }
          then show ?thesis by fastforce 
          qed
      next
        case (Channel_Queuing nm sn dn)
        show ?case by simp
      qed
            
  lemma trans_smpl_msg_notchg_portsinotherdom:
      assumes p1:"is_a_transmitter sysconf (current s)"
        and   p2:"reachable0 s"
        and   p3:"(current s) \<setminus>\<leadsto> d"
        and   p4:"s' = transf_sampling_msg s c"
      shows " \<forall>p. p\<in> get_ports_of_partition s d \<longrightarrow> ports (comm s) p = ports (comm s') p"
      proof(cases "is_a_scheduler sysconf d")
        assume a0:"is_a_scheduler sysconf d"
        with p2 have a3:"get_ports_of_partition s d = {}" 
          using no_cfgport_impl_noports is_a_scheduler_def sched_hasnoports by auto
        then show ?thesis by simp
      next
        assume a1:"\<not> is_a_scheduler sysconf d"
        show ?thesis
          proof(cases "is_a_partition sysconf d")
            assume b0:"is_a_partition sysconf d"
            with p1 p3 have b1:"\<not> transmitter_intf_part sysconf d"
              by (metis a1 interference1_def non_interference1_def trans_imp_not_part)
            then have b2:"get_partition_cfg_ports (the ((partconf sysconf) d)) = {}"
              using b0 get_partition_cfg_ports_byid_def is_a_partition_def port_partition by fastforce 
            then have b3:"get_partition_cfg_ports_byid sysconf d = {}"
              by (simp add: get_partition_cfg_ports_byid_def) 
            with p2 have b4:"get_ports_of_partition s d = {}" using no_cfgport_impl_noports by auto
            then show ?thesis by simp
          next
            assume b1:"\<not>is_a_partition sysconf d"
            show ?thesis
              proof(cases "is_a_transmitter sysconf d")
                assume c0:"is_a_transmitter sysconf d"
                with p1 p3 have "current s = d" by (simp add: is_a_transmitter_def) 
                with p3 show ?thesis using interference1_def non_interference1_def by auto  
              next
                assume c1:"\<not> is_a_transmitter sysconf d"
                with a1 b1 have c2:"get_partition_cfg_ports_byid sysconf d = {}"
                  by (simp add: get_partition_cfg_ports_byid_def is_a_partition_def) 
                with p2 have c2:"get_ports_of_partition s d = {}" using no_cfgport_impl_noports by auto
                then show ?thesis  by simp
              qed
          qed
       qed

  lemma trans_smpl_msg_notchg_comminotherdom:
    assumes   p0:"reachable0 s"
        and   p1:"is_a_transmitter sysconf (current s)"
      and   p3:"(current s) \<setminus>\<leadsto> d"
      and   p4:"s' = transf_sampling_msg s c"
    shows   "vpeq_part_comm s d s'"
     proof-
       from p3 have p5:"(current s) \<noteq> d" using non_interference1_def interference1_def by auto
       from p4 have "part_ports s = part_ports s'" using trans_smpl_msg_notchg_partports by blast
       then have "get_ports_of_partition s d = get_ports_of_partition s' d"
          using part_ports_imp_portofpart by blast
       
       moreover have"\<forall>p. p \<in> get_ports_of_partition s d \<longrightarrow>
                is_a_queuingport s p = is_a_queuingport s' p \<and>
                is_dest_port s p = is_dest_port s' p \<and> 
                (if is_dest_port s p then get_port_buf_size s p = get_port_buf_size s' p else True)"
       using  get_port_buf_size_def is_dest_port_def is_a_queuingport_def 
        trans_smpl_msg_notchg_portsinotherdom get_port_byid_def p0 p1 p3 p4 by auto
       ultimately show ?thesis by auto
     qed

  lemma trans_smpl_msg_sm_nitfpart:"\<lbrakk>reachable0 s; is_a_transmitter sysconf (current s); is_a_partition sysconf d;
                                  ((current s) \<setminus>\<leadsto> d); s' = transf_sampling_msg s c\<rbrakk>
                                        \<Longrightarrow> (s \<sim> d \<sim> s')"
      apply(clarsimp simp:vpeq1_def cong del: non_interference1_def is_a_transmitter_def 
          is_a_partition_def vpeq_part_comm_def)
      apply(rule conjI)
      using trans_imp_not_part apply fastforce
      apply(rule impI)
      apply(rule conjI)
      using  sche_imp_not_part apply fastforce
      apply(clarsimp simp:vpeq_part_def cong del: non_interference1_def 
          is_a_transmitter_def is_a_partition_def vpeq_part_comm_def)
      apply(rule conjI)
      apply (simp add: trans_smpl_msg_notchg_partstate vpeq_part_comm_def)
      using  trans_smpl_msg_notchg_comminotherdom nintf_neq by metis

  lemma trans_smpl_msg_presrv_lcrsp:
    assumes p0:"reachable0 s"
      and   p1:"current s = transmitter sysconf"
      and   p2:"(current s) \<setminus>\<leadsto> d"
      and   p3:"s' = transf_sampling_msg s c"
    shows   "s \<sim> d \<sim> s'"
  proof(cases "is_a_scheduler sysconf d")
    assume a0:"is_a_scheduler sysconf d"
    show ?thesis using a0  p1 p3 trans_smpl_msg_sm_sche by auto  
  next
    assume a1:"\<not> is_a_scheduler sysconf d"
    show ?thesis
      proof(cases "is_a_partition sysconf d")
        assume b0:"is_a_partition sysconf d"
        show ?thesis using p1  trans_smpl_msg_sm_nitfpart[OF p0 _ b0 p2 p3] by auto
      next
        assume b1:"\<not> is_a_partition sysconf d"
        show ?thesis
        proof(cases "is_a_transmitter sysconf d")
          assume c0:"is_a_transmitter sysconf d"
          with p1 p3 have "current s = d" by (simp add: is_a_transmitter_def) 
          with p3 show ?thesis using interference1_def non_interference1_def p2 by auto   
        next
          assume c1:"\<not> is_a_transmitter sysconf d"
          show ?thesis using a1 b1 c1 is_a_scheduler_def is_a_transmitter_def vpeq1_def by auto
        qed
      qed
  qed

  lemma trans_smpl_msg_presrv_lcrsp_e: "local_respect_e (sys (Transfer_Sampling_Message c))"
    using trans_smpl_msg_presrv_lcrsp  exec_event_def  
      prod.simps(2) vpeq_reflexive_lemma by (auto cong del: vpeq1_def)

subsubsection{*proving "Transfer Queuing Message" satisfying the "local respect" property*}
  lemma trans_que_msg_mlost_notchg_current:
      "is_a_transmitter sysconf (current s) \<Longrightarrow> current s = current (transf_queuing_msg_maylost sysconf s c)"
      proof(induct c)
        case (Channel_Queuing name sn dn) show ?case
          proof -
            let ?sp = "get_portid_by_name s sn"
            let ?dp = "get_portid_by_name s dn"
            let ?sm = "remove_msg_from_queuingport s (the ?sp)"
            let ?s1 = "fst ?sm"
            let ?s2 = "replace_msg2queuing_port ?s1 (the ?dp) (the (snd ?sm))"
            let ?s3 = "insert_msg2queuing_port ?s1 (the ?dp) (the (snd ?sm))"
            have a0:"current ?s1 = current s"
              proof(induct "(ports (comm s)) (the ?sp)")
                case None show ?thesis using None.hyps remove_msg_from_queuingport_def by auto 
              next
                case (Some x) show ?thesis
                  proof(induct "the ((ports (comm s)) (the ?sp))")
                    case (Queuing x1 x2 x3 x4 x5) show ?thesis
                      by (smt Port_Type.simps(5) Queuing.hyps State.ext_inject 
                        State.surjective State.update_convs(3) fstI option.case_eq_if 
                        remove_msg_from_queuingport_def)

                  next
                    case (Sampling x1 x2 x3 x4) show ?thesis
                        by (metis (no_types, lifting) Port_Type.simps(6) Sampling.hyps
                          fst_conv option.case_eq_if remove_msg_from_queuingport_def) 
                  qed
               qed
            have a1:"current ?s2 = current ?s1" by (simp add: replace_msg2queuing_port_def) 
            have a2:"current ?s3 = current ?s1" 
              proof(induct "(ports (comm ?s1)) (the ?dp)")
                case None show ?thesis by (simp add: None.hyps insert_msg2queuing_port_def option.case_eq_if) 
              next
                case (Some x) show ?thesis
                  proof(induct "the ((ports (comm ?s1)) (the ?dp))")
                    case (Queuing x1 x2 x3 x4 x5) show ?thesis
                        by (smt Port_Type.simps(5) Queuing.hyps State.select_convs(1) 
                            State.surjective State.update_convs(3) insert_msg2queuing_port_def option.case_eq_if) 
                  next
                    case (Sampling x1 x2 x3 x4) show ?thesis
                        by (smt Port_Type.simps(6) Sampling.hyps 
                            insert_msg2queuing_port_def option.case_eq_if) 
                  qed
              qed
            show ?thesis 
              proof(cases "?sp \<noteq> None \<and> ?dp \<noteq> None \<and> has_msg_inportqueuing s (the ?sp)")
                assume b0:"?sp \<noteq> None \<and> ?dp \<noteq> None \<and> has_msg_inportqueuing s (the ?sp)"
                show ?thesis
                  proof(cases "is_full_portqueuing sysconf (fst ?sm) (the ?dp)")
                    assume c0:"is_full_portqueuing sysconf (fst ?sm) (the ?dp)"
                    then have "transf_queuing_msg_maylost sysconf s (Channel_Queuing name sn dn) = ?s2"
                      by (smt b0 transf_queuing_msg_maylost.simps(1)) 
                    with a0 a1 show ?thesis by simp
                  next
                    assume c1:"\<not> is_full_portqueuing sysconf (fst ?sm) (the ?dp)"
                    then have "transf_queuing_msg_maylost sysconf s (Channel_Queuing name sn dn) = ?s3"
                      by (smt b0 transf_queuing_msg_maylost.simps(1))
                    with a0 a2 show ?thesis by simp  
                  qed
              next
                assume c0:"\<not>(?sp \<noteq> None \<and> ?dp \<noteq> None \<and> has_msg_inportqueuing s (the ?sp))"
                then have "transf_queuing_msg_maylost sysconf s (Channel_Queuing name sn dn) = s" 
                  by (smt transf_queuing_msg_maylost.simps(1))
                then show ?thesis by auto
              qed
        qed
      next
        case (Channel_Sampling name sn dns) show ?case by auto
      qed

   lemma trans_que_msg_mlost_sm_sche:"\<lbrakk>is_a_transmitter sysconf (current s); 
                                  s' = transf_queuing_msg_maylost sysconf s c\<rbrakk>
                                        \<Longrightarrow> (s\<sim>(scheduler sysconf)\<sim>s')"
       using trans_que_msg_mlost_notchg_current sch_not_trans by auto 

   lemma trans_que_msg_mlost_notchg_partstate:
              "\<lbrakk>is_a_transmitter sysconf (current s); is_a_partition sysconf d; 
              s' = transf_queuing_msg_maylost sysconf s c\<rbrakk> \<Longrightarrow> (partitions s) d = (partitions s') d"
       proof(induct c)
        case (Channel_Queuing name sn dn) show ?case
          proof -
            let ?sp = "get_portid_by_name s sn"
            let ?dp = "get_portid_by_name s dn"
            let ?sm = "remove_msg_from_queuingport s (the ?sp)"
            let ?s1 = "fst ?sm"
            let ?s2 = "replace_msg2queuing_port ?s1 (the ?dp) (the (snd ?sm))"
            let ?s3 = "insert_msg2queuing_port ?s1 (the ?dp) (the (snd ?sm))"
            have a0:"(partitions s) d = (partitions ?s1) d"
              proof(induct "(ports (comm s)) (the ?sp)")
                case None show ?thesis using None.hyps remove_msg_from_queuingport_def by auto 
              next
                case (Some x) show ?thesis
                  proof(induct "the ((ports (comm s)) (the ?sp))")
                    case (Queuing x1 x2 x3 x4 x5) show ?thesis
                      by (smt Port_Type.simps(5) Queuing.hyps State.ext_inject 
                        State.surjective State.update_convs(3) fstI option.case_eq_if 
                        remove_msg_from_queuingport_def)
                      
                  next
                    case (Sampling x1 x2 x3 x4) show ?thesis
                        by (metis (no_types, lifting) Port_Type.simps(6) Sampling.hyps
                          fst_conv option.case_eq_if remove_msg_from_queuingport_def) 
                  qed
               qed
            have a1:"(partitions ?s2) d = (partitions ?s1) d" by (simp add: replace_msg2queuing_port_def) 
            have a2:"(partitions ?s3) d = (partitions ?s1) d" 
              proof(induct "(ports (comm ?s1)) (the ?dp)")
                case None show ?thesis by (simp add: None.hyps insert_msg2queuing_port_def option.case_eq_if) 
              next
                case (Some x) show ?thesis
                  proof(induct "the ((ports (comm ?s1)) (the ?dp))")
                    case (Queuing x1 x2 x3 x4 x5) show ?thesis
                        by (smt Port_Type.simps(5) Queuing.hyps State.select_convs(2) 
                          State.surjective State.update_convs(3) insert_msg2queuing_port_def option.case_eq_if)
                  next
                    case (Sampling x1 x2 x3 x4) show ?thesis
                        by (smt Port_Type.simps(6) Sampling.hyps 
                            insert_msg2queuing_port_def option.case_eq_if) 
                  qed
              qed
            show ?thesis 
              proof(cases "?sp \<noteq> None \<and> ?dp \<noteq> None \<and> has_msg_inportqueuing s (the ?sp)")
                assume b0:"?sp \<noteq> None \<and> ?dp \<noteq> None \<and> has_msg_inportqueuing s (the ?sp)"
                show ?thesis
                  proof(cases "is_full_portqueuing sysconf (fst ?sm) (the ?dp)")
                    assume c0:"is_full_portqueuing sysconf (fst ?sm) (the ?dp)"
                    then have "transf_queuing_msg_maylost sysconf s (Channel_Queuing name sn dn) = ?s2"
                      by (smt b0 transf_queuing_msg_maylost.simps(1)) 
                    with a0 a1 show ?thesis by (simp add: Channel_Queuing.prems(3)) 
                  next
                    assume c1:"\<not> is_full_portqueuing sysconf (fst ?sm) (the ?dp)"
                    then have "transf_queuing_msg_maylost sysconf s (Channel_Queuing name sn dn) = ?s3"
                      by (smt b0 transf_queuing_msg_maylost.simps(1))
                    with a0 a2 show ?thesis by (simp add: Channel_Queuing.prems(3))  
                  qed
              next
                assume c0:"\<not>(?sp \<noteq> None \<and> ?dp \<noteq> None \<and> has_msg_inportqueuing s (the ?sp))"
                then have "transf_queuing_msg_maylost sysconf s (Channel_Queuing name sn dn) = s" 
                  by (smt transf_queuing_msg_maylost.simps(1))
                then show ?thesis by (simp add: Channel_Queuing.prems(3)) 
              qed
        qed
      next
        case (Channel_Sampling name sn dns) show ?case by (simp add: Channel_Sampling.prems(3)) 
      qed

    lemma trans_que_msg_mlost_notchg_partports:
      "s' = transf_queuing_msg_maylost sysconf s c \<Longrightarrow> 
        part_ports s = part_ports s'"
        proof(induct c)
          case (Channel_Queuing name sn dn) show ?case
            proof -
              let ?sp = "get_portid_by_name s sn"
              let ?dp = "get_portid_by_name s dn"
              let ?sm = "remove_msg_from_queuingport s (the ?sp)"
              let ?s1 = "fst ?sm"
              let ?s2 = "replace_msg2queuing_port ?s1 (the ?dp) (the (snd ?sm))"
              let ?s3 = "insert_msg2queuing_port ?s1 (the ?dp) (the (snd ?sm))"
              have b0:"part_ports s = part_ports ?s1"
                proof(induct "(ports (comm s)) (the ?sp)")
                  case None show ?thesis using None.hyps remove_msg_from_queuingport_def by auto 
                next
                  case (Some x) show ?thesis
                    proof(induct "the ((ports (comm s)) (the ?sp))")
                      case (Queuing x1 x2 x3 x4 x5) show ?thesis
                        by (smt Port_Type.simps(5) Queuing.hyps State.select_convs(4) State.surjective 
                          State.update_convs(3) fstI option.case_eq_if remove_msg_from_queuingport_def)
                    next
                      case (Sampling x1 x2 x3 x4) show ?thesis
                          by (metis (no_types, lifting) Port_Type.simps(6) Sampling.hyps
                            fst_conv option.case_eq_if remove_msg_from_queuingport_def) 
                    qed
                 qed
              have b1:"part_ports ?s2 = part_ports ?s1" 
                by (simp add: replace_msg2queuing_port_def) 
              have b2:"part_ports ?s3 = part_ports ?s1" 
                proof(induct "(ports (comm ?s1)) (the ?dp)")
                  case None show ?thesis by (simp add: None.hyps insert_msg2queuing_port_def option.case_eq_if) 
                next
                  case (Some x) show ?thesis
                    proof(induct "the ((ports (comm ?s1)) (the ?dp))")
                      case (Queuing x1 x2 x3 x4 x5) show ?thesis
                        by (smt Communication_State.select_convs(1) Communication_State.surjective 
                          Communication_State.update_convs(2) Port_Type.simps(5) Queuing.hyps 
                          State.select_convs(3) State.select_convs(4) State.surjective State.update_convs(3) 
                          insert_msg2queuing_port_def option.case_eq_if)
                    next
                      case (Sampling x1 x2 x3 x4) show ?thesis
                          by (smt Port_Type.simps(6) Sampling.hyps 
                              insert_msg2queuing_port_def option.case_eq_if) 
                    qed
                qed
              show ?thesis
                proof(cases "?sp \<noteq> None \<and> ?dp \<noteq> None \<and> has_msg_inportqueuing s (the ?sp)")
                  assume c0:"?sp \<noteq> None \<and> ?dp \<noteq> None \<and> has_msg_inportqueuing s (the ?sp)"
                  show ?thesis
                    proof(cases "is_full_portqueuing sysconf (fst ?sm) (the ?dp)")
                      assume d0:"is_full_portqueuing sysconf (fst ?sm) (the ?dp)"
                      then have "transf_queuing_msg_maylost sysconf s (Channel_Queuing name sn dn) = ?s2"
                        by (smt c0 transf_queuing_msg_maylost.simps(1)) 
                      with b0 b1 show ?thesis by (simp add: Channel_Queuing.prems(1)) 
                    next
                      assume c1:"\<not> is_full_portqueuing sysconf (fst ?sm) (the ?dp)"
                      then have "transf_queuing_msg_maylost sysconf s (Channel_Queuing name sn dn) = ?s3"
                        by (smt c0 transf_queuing_msg_maylost.simps(1))
                      with b0 b2 show ?thesis by (simp add: Channel_Queuing.prems(1))  
                    qed
                next
                  assume c0:"\<not>(?sp \<noteq> None \<and> ?dp \<noteq> None \<and> has_msg_inportqueuing s (the ?sp))"
                  then have "transf_queuing_msg_maylost sysconf s (Channel_Queuing name sn dn) = s" 
                    by (smt transf_queuing_msg_maylost.simps(1))
                  then show ?thesis by (simp add: Channel_Queuing.prems(1)) 
                qed
            qed
      next
        case (Channel_Sampling name sn dns) show ?case by (simp add: Channel_Sampling.prems(1)) 
      qed

    lemma trans_que_msg_mlost_notchg_portsinotherdom:
        assumes p1:"is_a_transmitter sysconf (current s)"
          and   p2:"reachable0 s"
          and   p3:"(current s) \<setminus>\<leadsto> d"
          and   p4:"s' = transf_queuing_msg_maylost sysconf s c"
        shows " \<forall>p. p\<in> get_ports_of_partition s d \<longrightarrow> ports (comm s) p = ports (comm s') p"
        proof(cases "is_a_scheduler sysconf d")
          assume a0:"is_a_scheduler sysconf d"
          with p2 have a3:"get_ports_of_partition s d = {}" 
            using no_cfgport_impl_noports  sched_hasnoports by auto
          then show ?thesis by simp
        next
          assume a1:"\<not> is_a_scheduler sysconf d"
          show ?thesis
            proof(cases "is_a_partition sysconf d")
              assume b0:"is_a_partition sysconf d"
              with p1 p3 have b1:"\<not> transmitter_intf_part sysconf d"
                by (metis a1 interference1_def non_interference1_def trans_imp_not_part)
              then have b2:"get_partition_cfg_ports (the ((partconf sysconf) d)) = {}"
                using b0 get_partition_cfg_ports_byid_def is_a_partition_def port_partition by fastforce 
              then have b3:"get_partition_cfg_ports_byid sysconf d = {}"
                by (simp add: get_partition_cfg_ports_byid_def) 
              with p2 have b4:"get_ports_of_partition s d = {}" using no_cfgport_impl_noports by auto
              then show ?thesis by simp
            next
              assume b1:"\<not>is_a_partition sysconf d"
              show ?thesis
                proof(cases "is_a_transmitter sysconf d")
                  assume c0:"is_a_transmitter sysconf d"
                  with p1 p3 have "current s = d" by (simp add: is_a_transmitter_def) 
                  with p3 show ?thesis using interference1_def non_interference1_def by auto   
                next
                  assume c1:"\<not> is_a_transmitter sysconf d"
                  with a1 b1 have c2:"get_partition_cfg_ports_byid sysconf d = {}"
                    by (simp add: get_partition_cfg_ports_byid_def is_a_partition_def) 
                  with p2 have c2:"get_ports_of_partition s d = {}" using no_cfgport_impl_noports by auto
                  then show ?thesis  by simp
                qed
            qed
         qed

    lemma trans_que_msg_mlost_notchg_comminotherdom:
      assumes   p0:"reachable0 s"
          and   p1:"is_a_transmitter sysconf (current s)"
        and   p3:"(current s) \<setminus>\<leadsto> d"
        and   p4:"s' = transf_queuing_msg_maylost sysconf s c"
      shows   "vpeq_part_comm s d s'"
     proof-
       from p3 have p5:"(current s) \<noteq> d" using non_interference1_def interference1_def by auto
       from p4 have "part_ports s = part_ports s'" using trans_que_msg_mlost_notchg_partports by blast
       then have "get_ports_of_partition s d = get_ports_of_partition s' d"
          using part_ports_imp_portofpart by blast
               
       moreover have "\<forall>p. p \<in> get_ports_of_partition s d \<longrightarrow>
                is_a_queuingport s p = is_a_queuingport s' p \<and>
                is_dest_port s p = is_dest_port s' p \<and> 
                (if is_dest_port s p then get_port_buf_size s p = get_port_buf_size s' p else True)"
       using  is_dest_port_def is_a_queuingport_def trans_que_msg_mlost_notchg_portsinotherdom get_port_byid_def 
              p0 p1 p3 p4 get_port_buf_size_def by auto  
    
       ultimately show ?thesis by auto
     qed
       
    
    lemma trans_que_msg_mlost_sm_nitfpart:
      "\<lbrakk>reachable0 s; is_a_transmitter sysconf (current s); is_a_partition sysconf d;
         ((current s) \<setminus>\<leadsto> d); s' = transf_queuing_msg_maylost sysconf s c\<rbrakk> \<Longrightarrow> (s \<sim> d \<sim> s')"
        apply(clarsimp simp:vpeq1_def cong del: is_a_transmitter_def 
            is_a_partition_def non_interference1_def vpeq_part_comm_def)
        apply(rule conjI)
        using  trans_imp_not_part apply fastforce
        apply(rule impI)
        apply(rule conjI)
        using  sche_imp_not_part apply fastforce
        apply(clarsimp cong del: is_a_transmitter_def is_a_partition_def non_interference1_def vpeq_part_comm_def)
        apply(rule conjI )
        apply (simp add: trans_que_msg_mlost_notchg_partstate)
        using trans_que_msg_mlost_notchg_comminotherdom by blast

    lemma trans_que_msg_mlost_presrv_lcrsp:
      assumes p0:"reachable0 s"
        and   p1:"current s = transmitter sysconf"
        and   p2:"(current s) \<setminus>\<leadsto> d"
        and   p3:"s' = transf_queuing_msg_maylost sysconf s c"
      shows   "s \<sim> d \<sim> s'"
    proof(cases "is_a_scheduler sysconf d")
      assume a0:"is_a_scheduler sysconf d"
      show ?thesis using a0 is_a_scheduler_def p1 p3 trans_que_msg_mlost_sm_sche using is_a_transmitter_def by auto  
    next
      assume a1:"\<not> is_a_scheduler sysconf d"
      show ?thesis
        proof(cases "is_a_partition sysconf d")
          assume b0:"is_a_partition sysconf d"
          show ?thesis using p1 trans_que_msg_mlost_sm_nitfpart[OF p0 _ b0 p2 p3] by auto  
        next
          assume b1:"\<not> is_a_partition sysconf d"
          show ?thesis
          proof(cases "is_a_transmitter sysconf d")
            assume c0:"is_a_transmitter sysconf d"
            with p1 p3 have "current s = d" by (simp add: is_a_transmitter_def) 
            with p3 show ?thesis using p2 by auto   
          next
            assume c1:"\<not> is_a_transmitter sysconf d"
            show ?thesis using a1 b1 c1  by auto
          qed
        qed
    qed

  lemma trans_que_msg_mlost_presrv_lcrsp_e: "local_respect_e (sys (Transfer_Queuing_Message c))"
    using trans_que_msg_mlost_presrv_lcrsp  exec_event_def  
       prod.simps(2)vpeq_reflexive_lemma by (auto cong del: vpeq1_def)

subsubsection{*proving the "local respect" property*}
  theorem local_respect:local_respect
    proof -
      {
        fix e
        have "local_respect_e e"
          apply(induct e)
          using crt_smpl_port_presrv_lcrsp_e write_smpl_msg_presrv_lcrsp_e
                  read_smpl_msg_presrv_lcrsp_e  get_smpl_pid_presrv_lcrsp_e 
                  get_smpl_psts_presrv_lcrsp_e crt_que_port_presrv_lcrsp_e 
                  snd_que_msg_lst_presrv_lcrsp_e rec_que_msg_presrv_lcrsp_e 
                  get_que_pid_presrv_lcrsp_e  get_que_psts_presrv_lcrsp_e 
                  clr_que_port_presrv_lcrsp_e  set_part_mode_presrv_lcrsp_e 
                  get_part_status_presrv_lcrsp_e 
          apply (rule Hypercall.induct)
          using schedule_presrv_lcrsp_e trans_smpl_msg_presrv_lcrsp_e 
                trans_que_msg_mlost_presrv_lcrsp_e
          by (rule System_Event.induct)
      }
      then show ?thesis using local_respect_all_evt by blast
    qed


subsection{* Concrete unwinding condition of "weakly step consistent" *}    
subsubsection{*proving "create sampling port" satisfying the "step consistent" property*}

  lemma crt_smpl_port_presrv_comm_part_ports:
    assumes   p1:"reachable0 s \<and> reachable0 t"
        and   p2:"s \<sim> (transmitter sysconf) \<sim> t"
        and   p5:"s \<sim> (scheduler sysconf) \<sim> t"
        and   p3:"s' = fst (create_sampling_port sysconf s pname)"
        and   p4:"t' = fst (create_sampling_port sysconf t pname)"
      shows   "comm s' = comm t' \<and> part_ports s' = part_ports t'"
      proof -
      {
        from p2 have a0:"vpeq_transmitter s (transmitter sysconf) t" using sch_not_trans  by auto 
        then have a1:"comm s = comm t \<and> part_ports s = part_ports t"  by auto
        from p1 have a2:"port_consistent s \<and> port_consistent t" by (simp add: port_cons_reach_state) 
        show ?thesis
          proof(cases "get_samplingport_conf sysconf pname = None 
                         \<or> get_portid_by_name s pname \<noteq> None
                         \<or> pname \<notin> get_partition_cfg_ports_byid sysconf (current s)")
            assume d0:"get_samplingport_conf sysconf pname = None 
                         \<or> get_portid_by_name s pname \<noteq> None
                         \<or> pname \<notin> get_partition_cfg_ports_byid sysconf (current s)"
            with p3 have d1:"s' = s" by (simp add: create_sampling_port_def) 
            have d2:"get_samplingport_conf sysconf pname = None 
                         \<or> get_portid_by_name t pname \<noteq> None
                         \<or> pname \<notin> get_partition_cfg_ports_byid sysconf (current t)"
                         by (meson disjoint_iff_not_equal port_partition)
            with p4 have d3:"t' = t" using create_sampling_port_def by auto 
            with a1 d1 show ?thesis by simp
          next
            let ?nid = "get_portid_in_type (the (get_samplingport_conf sysconf pname))"
            assume e0:"\<not>(get_samplingport_conf sysconf pname = None 
                         \<or> get_portid_by_name s pname \<noteq> None
                         \<or> pname \<notin> get_partition_cfg_ports_byid sysconf (current s))"
            with p3 have e1:"part_ports s' = (part_ports s)(?nid:= (Some (current s)))"
              using port_partition by auto 
            with p4 e0 have e2:"part_ports t' = (part_ports t)(?nid := (Some (current t)))"
              using port_partition by auto 
            with p3 e0 have e3:"ports (comm s') = (ports (comm s))(?nid := get_samplingport_conf sysconf pname)"
              using port_partition by auto
            with p4 e0 have e4:"ports (comm t') = (ports (comm t))(?nid := get_samplingport_conf sysconf pname)"
              using port_partition by auto
            with a1 e1 e2 e3 e4 show ?thesis using p5 sched_current_lemma e0 port_partition by fastforce
          qed
      }
      qed

  lemma crt_smpl_port_presrv_comm_of_current_part:
    assumes   p1:"reachable0 s \<and> reachable0 t"
        and   p2:"s \<sim> (scheduler sysconf) \<sim> t"
        and   p3:"s' = fst (create_sampling_port sysconf s pname)"
        and   p4:"t' = fst (create_sampling_port sysconf t pname)"
        and   p5:"(current s) = d"
        and   p6:"vpeq_part_comm s d t"
        and   p7:"is_a_partition sysconf d"
      shows   "vpeq_part_comm s' d t'"
      apply(clarsimp, rule conjI)
      proof -
      {
        from p6 have a1:"get_ports_of_partition s d = get_ports_of_partition t d" 
          by auto
        from p2 have a2:"current s = current t" by auto            
        show g0:"get_ports_of_partition s' d = get_ports_of_partition t' d"
        proof -
        {
          have "\<forall>p. p\<in>get_ports_of_partition s' d \<longrightarrow> p\<in>get_ports_of_partition t' d"
            proof-
            {
              fix p
              assume a0:"p\<in>get_ports_of_partition s' d"
              have a3:"p\<in>get_ports_of_partition t' d"
                 proof(cases "pname \<in> get_partition_cfg_ports_byid sysconf (current s)")
                  assume b0:"pname \<in> get_partition_cfg_ports_byid sysconf (current s)"
                  with a2 have b1:"pname \<in> get_partition_cfg_ports_byid sysconf (current t)" by simp
                  have b2:"p \<noteq> get_portid_in_type (the (get_samplingport_conf sysconf pname))" 
                    using b0 port_partition by auto 
                  then show ?thesis using b0 port_partition by auto 
                next
                  assume c0:"\<not>(pname \<in> get_partition_cfg_ports_byid sysconf (current s))"
                  with a2 have c1:"\<not>(pname \<in> get_partition_cfg_ports_byid sysconf (current t))" by simp
                  have c2:"s' = s" by (simp add: c0 create_sampling_port_def p3)
                  have c3:"t' = t" by (simp add: c1 create_sampling_port_def p4) 
                  then show ?thesis using a0 a1 c2 by auto  
                qed
            }
            then show ?thesis by auto
            qed
          moreover
          have "\<forall>p. p\<in>get_ports_of_partition t' d \<longrightarrow> p\<in>get_ports_of_partition s' d"
            proof-
            {
              fix p
              assume a0:"p\<in>get_ports_of_partition t' d"
              have a3:"p\<in>get_ports_of_partition s' d"
                 proof(cases "pname \<in> get_partition_cfg_ports_byid sysconf (current s)")
                  assume b0:"pname \<in> get_partition_cfg_ports_byid sysconf (current s)"
                  with a2 have b1:"pname \<in> get_partition_cfg_ports_byid sysconf (current t)" by simp
                  have b2:"p \<noteq> get_portid_in_type (the (get_samplingport_conf sysconf pname))" 
                    using b0 port_partition by auto 
                  then show ?thesis using b0 port_partition by auto 
                next
                  assume c0:"\<not>(pname \<in> get_partition_cfg_ports_byid sysconf (current s))"
                  with a2 have c1:"\<not>(pname \<in> get_partition_cfg_ports_byid sysconf (current t))" by simp
                  have c2:"s' = s" by (simp add: c0 create_sampling_port_def p3)
                  have c3:"t' = t" by (simp add: c1 create_sampling_port_def p4) 
                  then show ?thesis using a0 a1 c2 by auto  
                qed
            }
            then show ?thesis by auto
            qed
          then show ?thesis using calculation by blast 
        }
        qed
      next
        from p6 have a1:"get_ports_of_partition s d = get_ports_of_partition t d" 
            unfolding vpeq_part_comm_def Let_def by auto
        from p2 have a2:"current s = current t" by auto
        show "\<forall>p. (is_dest_port s' p \<longrightarrow> p \<in> get_ports_of_partition s' d \<longrightarrow>
         is_a_queuingport s' p = is_a_queuingport t' p \<and> is_dest_port t' p 
         \<and> get_port_buf_size s' p = get_port_buf_size t' p) \<and> (\<not> is_dest_port s' p \<longrightarrow>
         p \<in> get_ports_of_partition s' d \<longrightarrow> is_a_queuingport s' p = is_a_queuingport t' p \<and> \<not> is_dest_port t' p) " 
          proof -
          {
            fix p
            have "(is_dest_port s' p \<longrightarrow>
               p \<in> get_ports_of_partition s' d \<longrightarrow>
               is_a_queuingport s' p = is_a_queuingport t' p \<and> is_dest_port t' p 
               \<and> get_port_buf_size s' p = get_port_buf_size t' p) \<and> (\<not> is_dest_port s' p \<longrightarrow>
               p \<in> get_ports_of_partition s' d \<longrightarrow> is_a_queuingport s' p = is_a_queuingport t' p \<and> \<not> is_dest_port t' p)"
              proof(cases "pname \<in> get_partition_cfg_ports_byid sysconf (current s)")
              assume b0:"pname \<in> get_partition_cfg_ports_byid sysconf (current s)"
                with a2 have b1:"pname \<in> get_partition_cfg_ports_byid sysconf (current t)" by simp
                have b2:"p \<noteq> get_portid_in_type (the (get_samplingport_conf sysconf pname))" 
                  using b0 port_partition by auto 
                then show ?thesis using b0 port_partition by auto 
              next
                assume c0:"\<not>(pname \<in> get_partition_cfg_ports_byid sysconf (current s))"
                with a2 have c1:"\<not>(pname \<in> get_partition_cfg_ports_byid sysconf (current t))" by simp
                have c2:"s' = s" by (simp add: c0 create_sampling_port_def p3)
                have c3:"t' = t" by (simp add: c1 create_sampling_port_def p4) 
                then show ?thesis using c0 a1 c2 using p6  by auto   
              qed
          }
          then show ?thesis by auto
          qed
      }
      qed

  lemma crt_smpl_port_presrv_wk_stp_cons:
      assumes p1:"is_a_partition sysconf (current s)"
        and   p2:"reachable0 s \<and> reachable0 t"
        and   p3:"s \<sim> d \<sim> t"
        and   p4:"s \<sim> (scheduler sysconf) \<sim> t"
        and   p5:"(current s) \<leadsto> d"
        and   p6:"s \<sim> (current s) \<sim> t"
        and   p7:"s' = fst (create_sampling_port sysconf s pname)"
        and   p8:"t' = fst (create_sampling_port sysconf t pname)"
      shows   "s' \<sim> d \<sim> t'"
    proof(cases "is_a_scheduler sysconf d")
      assume a0:"is_a_scheduler sysconf d"
      show ?thesis using a0  p1 p5 sche_imp_not_part by (metis is_a_scheduler_def no_intf_sched_help)  
    next
      assume a1:"\<not> is_a_scheduler sysconf d"
      show ?thesis
        proof(cases "is_a_partition sysconf d")
          assume b0:"is_a_partition sysconf d"
          show ?thesis 
            proof(cases "current s = d")
              assume c0:"current s = d"
              have d0:"vpeq_part s' d t'"
                proof -
                {
                  
                  have e1:"partitions s' d = partitions t' d"
                    proof - 
                    {
                      from p3 b0 have f1:"partitions s d = partitions t d" 
                        using a1 part_imp_not_tras   by fastforce
                      from p7 have f2:"partitions s d = partitions s' d" 
                        using  b0 crt_sampl_port_notchg_partstate p1 by blast
                      from p8 have f3:"partitions t d = partitions t' d"
                        using b0 c0 crt_sampl_port_notchg_partstate p4 sched_current_lemma
                          by simp
                      with f1 f2 have "partitions s' d = partitions t' d" by auto
                    }
                    then show ?thesis by auto
                    qed
                  have e2:"vpeq_part_comm s' d t'"
                    proof -
                    {
                      from p3 a1 b0 have f1:"vpeq_part_comm s d t" 
                        using part_imp_not_tras by fastforce 
                      then have "vpeq_part_comm s' d t'"
                        using c0 crt_smpl_port_presrv_comm_of_current_part p1 p2 p4 p7 p8 by auto                        
                    }
                    then show ?thesis by auto
                    qed
                  with e1 have "vpeq_part s' d t'" by auto
                }
                then show ?thesis by auto
                qed
              then show ?thesis using a1 b0 c0                                                                
                using trans_imp_not_part by fastforce                                
            next
              assume c1:"current s \<noteq> d" 
              have d1:"vpeq_part s' d t'" 
              proof -
              {
                have e1:"partitions s' d = partitions t' d"
                  using a1  crt_sampl_port_notchg_partstate[OF p1 b0 p7]  
                     p3 p4 p7 p8 part_imp_not_tras sched_current_lemma
                     b0 c1  p1 p5 part_imp_not_sch by auto                      
                have e2:"vpeq_part_comm s' d t'"
                  by (metis a1 b0 create_sampling_port_def fst_conv get_samplingport_conf_def 
                      is_a_scheduler_def is_a_transmitter_def p3 p7 p8 part_imp_not_tras 
                      port_name_diff vpeq1_def vpeq_part_def)
               with e1 have "vpeq_part s' d t'"  by auto
              }
              then show ?thesis by auto
              qed
              show ?thesis  using a1 b0 c1                            
              using  trans_imp_not_part d1 by fastforce                              
            qed
        next
          assume b1:"\<not> is_a_partition sysconf d"
          show ?thesis
          proof(cases "is_a_transmitter sysconf d")
            assume c0:"is_a_transmitter sysconf d"
            show ?thesis 
               using a1 b1 p3 c0 crt_smpl_port_presrv_comm_part_ports[OF p2 _ p4 p7 p8] by auto                 
          next
            assume c1:"\<not> is_a_transmitter sysconf d"
            show ?thesis using a1 b1 c1 by auto
          qed
        qed
    qed

  lemma crt_smpl_port_presrv_wk_stp_cons_e: "weak_step_consistent_e (hyperc (Create_Sampling_Port p))"
    using crt_smpl_port_presrv_wk_stp_cons weak_step_consistent_e_def exec_event_def mem_Collect_eq
      non_interference1_def non_interference_def singletonD sched_vpeq same_part_mode
        by (smt Event.case(1) Hypercall.case(1) domain_of_event.simps(1) 
            event_enabled.simps(1) option.sel prod.simps(2)) 


subsubsection{*proving "write sampling message" satisfying the "step consistent" property*}

  lemma wrt_smpl_msg_presrv_comm_part_ports:
    assumes   p1:"reachable0 s \<and> reachable0 t"
        and   p2:"s \<sim> (transmitter sysconf) \<sim> t"
        and   p5:"s \<sim> (scheduler sysconf) \<sim> t"
        and   p3:"s' = fst (write_sampling_message s pid m)"
        and   p4:"t' = fst (write_sampling_message t pid m)"
      shows   "comm s' = comm t' \<and> part_ports s' = part_ports t'"
      proof -
      {
        from p2 have a0:"vpeq_transmitter s (transmitter sysconf) t" using sch_not_trans  by auto 
        then have a1:"comm s = comm t \<and> part_ports s = part_ports t"  by auto
        from p1 have a2:"port_consistent s \<and> port_consistent t" by (simp add: port_cons_reach_state) 
        show ?thesis
          proof(cases "\<not> is_a_samplingport s pid 
                        \<or> \<not> is_source_port s pid
                        \<or> \<not> is_a_port_of_partition s pid (current s)")
            assume d0:"\<not> is_a_samplingport s pid 
                        \<or> \<not> is_source_port s pid
                        \<or> \<not> is_a_port_of_partition s pid (current s)"
            with p3 have d1:"s' = s" by (simp add: write_sampling_message_def) 
            have d2:"\<not> is_a_samplingport t pid
                        \<or> \<not> is_source_port t pid
                        \<or> \<not> is_a_port_of_partition t pid (current t)"
              using a1 d0 is_a_port_of_partition_def is_a_samplingport_def 
                is_source_port_def p5 sched_current_lemma by simp                
            with p4 have d3:"t' = t" using write_sampling_message_def by auto 
            with a1 d1 show ?thesis by simp
          next
            assume e0:"\<not>(\<not> is_a_samplingport s pid 
                        \<or> \<not> is_source_port s pid
                        \<or> \<not> is_a_port_of_partition s pid (current s))"
            with p3 have e1:"part_ports s' = part_ports s"
              by (metis Int_absorb a2 empty_iff is_a_port_of_partition_def 
                option.distinct(1) port_consistent_def port_partition)  
            
            with p4 e0 have e2:"part_ports t' = part_ports t"
              by (metis Int_absorb a2 empty_iff is_a_port_of_partition_def 
                option.distinct(1) port_consistent_def port_partition)
            have f1:"s' = update_sampling_port_msg s pid m" using e0 p3 write_sampling_message_def by auto
            have f2:"t' = update_sampling_port_msg t pid m"
              using a1 e0 is_a_port_of_partition_def is_a_samplingport_def 
                is_source_port_def p4 p5 sched_current_lemma write_sampling_message_def
                by simp               
            with p3 p4 e0 have e5:"ports (comm s') = ports (comm t')"
              proof(induct "(ports (comm s)) pid")
                case None show ?case using None.hyps a1 f1 f2 update_sampling_port_msg_def by auto 
              next
                case (Some x) show ?case
                  proof(induct "the (ports (comm s) pid)")
                    case (Queuing x1 x2 x3 x4 x5) show ?case
                        by (smt Port_Type.simps(5) Queuing.hyps Some.hyps a1 f1 f2 
                            option.sel option.simps(5) update_sampling_port_msg_def) 
                  next
                    case (Sampling x1 x2 x3 x4) show ?case
                        by (smt Communication_State.surjective Communication_State.update_convs(1)
                          Port_Type.simps(6) Sampling.hyps State.select_convs(3) State.surjective 
                          State.update_convs(3) a1 f1 f2 option.case_eq_if update_sampling_port_msg_def) 
                  qed
              qed
            with a1 e1 e2 e5 show ?thesis using p5 sched_current_lemma by auto

          qed
      }
      qed

  lemma wrt_smpl_msg_presrv_comm_of_current_part:
  assumes   p1:"reachable0 s \<and> reachable0 t"
      and   p2:"s \<sim> (scheduler sysconf) \<sim> t"
      and   p3:"s' = fst (write_sampling_message s pid m)"
      and   p4:"t' = fst (write_sampling_message t pid m)"
      and   p5:"(current s) = d"
      and   p6:"vpeq_part_comm s d t" 
      and   p7:"is_a_partition sysconf d"
    shows   "vpeq_part_comm s' d t'"    
    proof-      
      from p6 have a1:"get_ports_of_partition s d = get_ports_of_partition t d" 
          by auto
      from p2 have a2:"current s = current t" by auto  
      from p3 p5 p7 have a3:"part_ports s = part_ports s'" using wrt_smpl_msg_notchg_partports by simp
      then have a4:"get_ports_of_partition s d = get_ports_of_partition s' d"
        using part_ports_imp_portofpart by blast 
      from p4 p5 p7 a2 have a5:"part_ports t = part_ports t'" using wrt_smpl_msg_notchg_partports by simp
      then have a6:"get_ports_of_partition t d = get_ports_of_partition t' d"
        using part_ports_imp_portofpart by blast 
      have g0:"get_ports_of_partition s' d = get_ports_of_partition t' d"
        using a1 a4 a6 by simp 
      moreover have "\<forall>p. p \<in> get_ports_of_partition s' d \<longrightarrow>
                is_a_queuingport s' p = is_a_queuingport t' p \<and>
                is_dest_port s' p = is_dest_port t' p \<and>
                (if is_dest_port s' p then get_port_buf_size s' p = get_port_buf_size t' p else True)" 
       using a4 by (metis  empty_iff inf.idem no_cfgport_impl_noports p1 port_partition) 
       ultimately show ?thesis by auto
   qed
   

  lemma wrt_smpl_msg_presrv_wk_stp_cons:
      assumes p1:"is_a_partition sysconf (current s)"
        and   p2:"reachable0 s \<and> reachable0 t"
        and   p3:"s \<sim> d \<sim> t"
        and   p4:"s \<sim> (scheduler sysconf) \<sim> t"
        and   p5:"(current s) \<leadsto> d"
        and   p6:"s \<sim> (current s) \<sim> t"
        and   p7:"s' = fst (write_sampling_message s pid m)"
        and   p8:"t' = fst (write_sampling_message t pid m)"
      shows   "s' \<sim> d \<sim> t'"
    proof(cases "is_a_scheduler sysconf d")
      assume a0:"is_a_scheduler sysconf d"
      show ?thesis by (smt a0 interference1_def p1 p5 sche_imp_not_part)  
    next
      assume a1:"\<not> is_a_scheduler sysconf d"
      show ?thesis
        proof(cases "is_a_partition sysconf d")
          assume b0:"is_a_partition sysconf d"
          show ?thesis 
            proof(cases "current s = d")
              assume c0:"current s = d"
              have d0:"vpeq_part s' d t'"
                proof -
                {
                  have e1:"partitions s' d = partitions t' d"
                    proof - 
                    {
                      from p3 b0 have f1:"partitions s d = partitions t d" 
                        using a1 part_imp_not_tras by fastforce
                      from p7 have f2:"partitions s d = partitions s' d"
                        using b0 wrt_smpl_msg_notchg_partstate p1 by auto
                      from p8 have f3:"partitions t d = partitions t' d"
                        using b0 c0 wrt_smpl_msg_notchg_partstate p4 sched_current_lemma  by simp
                      with f1 f2 have "partitions s' d = partitions t' d" by auto
                    }
                    then show ?thesis by auto
                    qed
                  have e2:"vpeq_part_comm s' d t'"
                    proof -
                    {
                      from p3 a1 b0 have f1:"vpeq_part_comm s d t" 
                        using  part_imp_not_tras by fastforce 
                      then have "vpeq_part_comm s' d t'"
                        using c0 wrt_smpl_msg_presrv_comm_of_current_part p1 p2 p4 p7 p8 by auto                        
                    }
                    then show ?thesis by auto
                    qed
                  with e1 have "vpeq_part s' d t'" using vpeq_part_def by auto
                }
                then show ?thesis by auto
                qed
              then show ?thesis  using a1 b0 c0                 
                using trans_imp_not_part by fastforce                
            next
              assume c1:"current s \<noteq> d" 
              have d1:"vpeq_part s' d t'" 
                proof -
                {
                  have e1:"partitions s' d = partitions t' d"
                    using a1 b0  p1 p3 p4 p7 p8 
                    part_not_trans  wrt_smpl_msg_notchg_partstate by auto                    
                  have e2:"vpeq_part_comm s' d t'"
                    proof -
                      from p3 a1 b0 have f1:"vpeq_part_comm s d t" 
                        using part_imp_not_tras by fastforce 
                      have f2:"vpeq_part_comm s d s'" using c1 p1 p2 p7 wrt_smpl_msg_notchg_comminotherdom by blast
                      have f3:"vpeq_part_comm t d t'"
                        using p1 p2 p4 p8 c1 sched_current_lemma wrt_smpl_msg_notchg_comminotherdom
                          by fastforce
                      then show ?thesis
                        using f1 f2 vpeq_part_comm_symmetric_lemma vpeq_part_comm_transitive_lemma by blast 
                    qed                    
                 with e1 have "vpeq_part s' d t'" using vpeq_part_def by auto
                }
                then show ?thesis by auto
                qed
              show ?thesis using a1 b0 c1                            
              using d1 trans_imp_not_part  by auto              
            qed
        next
          assume b1:"\<not> is_a_partition sysconf d"
          show ?thesis
          proof(cases "is_a_transmitter sysconf d")
            assume c0:"is_a_transmitter sysconf d"
            show ?thesis
              proof -
              {
                have "vpeq_transmitter s' d t'" unfolding vpeq_transmitter_def
                proof-
                  from p3 p7 p8
                  show "comm s' = comm t' \<and> part_ports s' = part_ports t' "
                    using c0 wrt_smpl_msg_presrv_comm_part_ports[OF p2 _ p4]  by auto
                qed
              }
              then show ?thesis using a1 b1 by auto
              qed
          next
            assume c1:"\<not> is_a_transmitter sysconf d"
            show ?thesis using a1 b1 c1 is_a_scheduler_def is_a_transmitter_def vpeq1_def by auto
          qed
        qed
    qed

  lemma wrt_smpl_msg_presrv_wk_stp_cons_e: "weak_step_consistent_e (hyperc (Write_Sampling_Message p m))"
    using wrt_smpl_msg_presrv_wk_stp_cons weak_step_consistent_e_def exec_event_def mem_Collect_eq
       non_interference_def singletonD sched_vpeq same_part_mode
        by (smt Event.case(1) Hypercall.case(2) domain_of_event.simps(1) event_enabled.simps(1) option.sel prod.simps(2)) 

subsubsection{*proving "read sampling message" satisfying the "step consistent" property*}

  lemma read_smpl_msg_presrv_wk_stp_cons:
      assumes p1:"s \<sim> d \<sim> t"
        and   p2:"s' = fst (read_sampling_message s pid)"
        and   p3:"t' = fst (read_sampling_message t pid)"
      shows   "s' \<sim> d \<sim> t'"
    proof -
      have a0:"s' = s" by (simp add: p2 read_sampling_message_def) 
      have a1:"t' = t" by (simp add: p3 read_sampling_message_def) 
      then show ?thesis using a0 p1 by blast  
    qed

  lemma read_smpl_msg_presrv_wk_stp_cons_e: "weak_step_consistent_e (hyperc (Read_Sampling_Message p))"
    using read_smpl_msg_presrv_wk_stp_cons weak_step_consistent_e_def exec_event_def mem_Collect_eq
      non_interference1_def non_interference_def singletonD sched_vpeq same_part_mode
        by (smt Event.case(1) Hypercall.case(3) domain_of_event.simps(1) 
            event_enabled.simps(1) option.sel prod.simps(2)) 

subsubsection{*proving "get sampling portid" satisfying the "step consistent" property*}

  lemma get_smpl_pid_presrv_wk_stp_cons:
      assumes p1:"s \<sim> d \<sim> t"
        and   p2:"s' = fst (get_sampling_port_id sysconf s pname)"
        and   p3:"t' = fst (get_sampling_port_id sysconf t pname)"
      shows   "s' \<sim> d \<sim> t'"
    proof -
      have a0:"s' = s" by (simp add: p2 get_sampling_port_id_def) 
      have a1:"t' = t" by (simp add: p3 get_sampling_port_id_def)
      then show ?thesis using a0 p1 by blast  
    qed

  lemma get_smpl_pid_presrv_wk_stp_cons_e: "weak_step_consistent_e (hyperc (Get_Sampling_Portid p))"
    using get_smpl_pid_presrv_wk_stp_cons weak_step_consistent_e_def exec_event_def mem_Collect_eq
       non_interference_def singletonD sched_vpeq same_part_mode
        by (smt Event.case(1) Hypercall.case(4) domain_of_event.simps(1) 
            event_enabled.simps(1) option.sel prod.simps(2))

subsubsection{*proving "get sampling port status" satisfying the "step consistent" property*}

  lemma get_smpl_psts_presrv_wk_stp_cons:
      assumes p1:"s \<sim> d \<sim> t"
        and   p2:"s' = fst (get_sampling_port_status sysconf s pid)"
        and   p3:"t' = fst (get_sampling_port_status sysconf t pid)"
      shows   "s' \<sim> d \<sim> t'"
    proof -
      have a0:"s' = s" by (simp add: p2 get_sampling_port_status_def) 
      have a1:"t' = t" by (simp add: p3 get_sampling_port_status_def)
      then show ?thesis using a0 p1 by blast  
    qed

  lemma get_smpl_psts_presrv_wk_stp_cons_e: "weak_step_consistent_e (hyperc (Get_Sampling_Portstatus p))"
    using get_smpl_psts_presrv_wk_stp_cons weak_step_consistent_e_def exec_event_def mem_Collect_eq
       non_interference_def singletonD sched_vpeq same_part_mode
        by (smt Event.case(1) Hypercall.case(5) domain_of_event.simps(1) event_enabled.simps(1) 
          option.sel prod.simps(2) vpeq1_def vpeq_sched_def) 
        

subsubsection{*proving "create queuing port" satisfying the "step consistent" property*}

  lemma crt_que_port_presrv_comm_part_ports:
    assumes   p1:"reachable0 s \<and> reachable0 t"
        and   p2:"s \<sim> (transmitter sysconf) \<sim> t"
        and   p5:"s \<sim> (scheduler sysconf) \<sim> t"
        and   p3:"s' = fst (create_queuing_port sysconf s pname)"
        and   p4:"t' = fst (create_queuing_port sysconf t pname)"
      shows   "comm s' = comm t' \<and> part_ports s' = part_ports t'"
      proof -
      {
        from p2 have a0:"vpeq_transmitter s (transmitter sysconf) t" using sch_not_trans  by auto 
        then have a1:"comm s = comm t \<and> part_ports s = part_ports t" by auto
        from p1 have a2:"port_consistent s \<and> port_consistent t" by (simp add: port_cons_reach_state) 
        show ?thesis
          proof(cases "get_queuingport_conf sysconf pname = None 
                         \<or> get_portid_by_name s pname \<noteq> None
                         \<or> pname \<notin> get_partition_cfg_ports_byid sysconf (current s)")
            assume d0:"get_queuingport_conf sysconf pname = None 
                         \<or> get_portid_by_name s pname \<noteq> None
                         \<or> pname \<notin> get_partition_cfg_ports_byid sysconf (current s)"
            with p3 have d1:"s' = s" by (simp add: create_queuing_port_def) 
            have d2:"get_queuingport_conf sysconf pname = None 
                         \<or> get_portid_by_name t pname \<noteq> None
                         \<or> pname \<notin> get_partition_cfg_ports_byid sysconf (current t)"
                         by (meson disjoint_iff_not_equal port_partition)
            with p4 have d3:"t' = t" using create_queuing_port_def by auto 
            with a1 d1 show ?thesis by simp
          next
            let ?nid = "get_portid_in_type (the (get_queuingport_conf sysconf pname))"
            assume e0:"\<not>(get_queuingport_conf sysconf pname = None 
                         \<or> get_portid_by_name s pname \<noteq> None
                         \<or> pname \<notin> get_partition_cfg_ports_byid sysconf (current s))"
            with p3 have e1:"part_ports s' = (part_ports s)(?nid:= (Some (current s)))"
              using port_partition by auto 
            with p4 e0 have e2:"part_ports t' = (part_ports t)(?nid := (Some (current t)))"
              using port_partition by auto 
            with p3 e0 have e3:"ports (comm s') = (ports (comm s))(?nid := get_queuingport_conf sysconf pname)"
              using port_partition by auto
            with p4 e0 have e4:"ports (comm t') = (ports (comm t))(?nid := get_queuingport_conf sysconf pname)"
              using port_partition by auto
            with a1 e1 e2 e3 e4 show ?thesis using p5 sched_current_lemma by auto
          qed
      }
      qed

  lemma crt_que_port_presrv_comm_of_current_part:
    assumes   p1:"reachable0 s \<and> reachable0 t"
        and   p2:"s \<sim> (scheduler sysconf) \<sim> t"
        and   p3:"s' = fst (create_queuing_port sysconf s pname)"
        and   p4:"t' = fst (create_queuing_port sysconf t pname)"
        and   p5:"(current s) = d"
        and   p6:"vpeq_part_comm s d t"
        and   p7:"is_a_partition sysconf d"
      shows   "vpeq_part_comm s' d t'"
      apply(clarsimp,rule conjI)
      proof -
      {
        from p6 have a1:"get_ports_of_partition s d = get_ports_of_partition t d" 
           by auto
        from p2 have a2:"current s = current t" using sched_current_lemma by auto               
        show g0:"get_ports_of_partition s' d = get_ports_of_partition t' d"
        proof -
        {
          have "\<forall>p. p\<in>get_ports_of_partition s' d \<longrightarrow> p\<in>get_ports_of_partition t' d"
            proof-
            {
              fix p
              assume a0:"p\<in>get_ports_of_partition s' d"
              have a3:"p\<in>get_ports_of_partition t' d"
                 proof(cases "pname \<in> get_partition_cfg_ports_byid sysconf (current s)")
                  assume b0:"pname \<in> get_partition_cfg_ports_byid sysconf (current s)"
                  with a2 have b1:"pname \<in> get_partition_cfg_ports_byid sysconf (current t)" by simp
                  have b2:"p \<noteq> get_portid_in_type (the (get_queuingport_conf sysconf pname))" 
                    using b0 port_partition by auto 
                  then show ?thesis using b0 port_partition by auto 
                next
                  assume c0:"\<not>(pname \<in> get_partition_cfg_ports_byid sysconf (current s))"
                  with a2 have c1:"\<not>(pname \<in> get_partition_cfg_ports_byid sysconf (current t))" by simp
                  have c2:"s' = s" by (simp add: c0 create_queuing_port_def p3)
                  have c3:"t' = t" by (simp add: c1 create_queuing_port_def p4) 
                  then show ?thesis using a0 a1 c2 by auto  
                qed
            }
            then show ?thesis by auto
            qed
          moreover
          have "\<forall>p. p\<in>get_ports_of_partition t' d \<longrightarrow> p\<in>get_ports_of_partition s' d"
            proof-
            {
              fix p
              assume a0:"p\<in>get_ports_of_partition t' d"
              have a3:"p\<in>get_ports_of_partition s' d"
                 proof(cases "pname \<in> get_partition_cfg_ports_byid sysconf (current s)")
                  assume b0:"pname \<in> get_partition_cfg_ports_byid sysconf (current s)"
                  with a2 have b1:"pname \<in> get_partition_cfg_ports_byid sysconf (current t)" by simp
                  have b2:"p \<noteq> get_portid_in_type (the (get_queuingport_conf sysconf pname))" 
                    using b0 port_partition by auto 
                  then show ?thesis using b0 port_partition by auto 
                next
                  assume c0:"\<not>(pname \<in> get_partition_cfg_ports_byid sysconf (current s))"
                  with a2 have c1:"\<not>(pname \<in> get_partition_cfg_ports_byid sysconf (current t))" by simp
                  have c2:"s' = s" by (simp add: c0 create_queuing_port_def p3)
                  have c3:"t' = t" by (simp add: c1 create_queuing_port_def p4) 
                  then show ?thesis using a0 a1 c2 by auto  
                qed
            }
            then show ?thesis by auto
            qed
          then show ?thesis using calculation by blast 
        }
        qed
      next
        from p6 have a1:"get_ports_of_partition s d = get_ports_of_partition t d" 
            by auto
        from p2 have a2:"current s = current t" using sched_current_lemma by auto     
        show "\<forall>p. (is_dest_port s' p \<longrightarrow>
         p \<in> get_ports_of_partition s' d \<longrightarrow>
         is_a_queuingport s' p = is_a_queuingport t' p \<and> is_dest_port t' p \<and> get_port_buf_size s' p = get_port_buf_size t' p) \<and>
        (\<not> is_dest_port s' p \<longrightarrow>
         p \<in> get_ports_of_partition s' d \<longrightarrow> is_a_queuingport s' p = is_a_queuingport t' p \<and> \<not> is_dest_port t' p) " 
          proof -
          {
            fix p
            have "(is_dest_port s' p \<longrightarrow>
               p \<in> get_ports_of_partition s' d \<longrightarrow>
               is_a_queuingport s' p = is_a_queuingport t' p \<and> is_dest_port t' p \<and> get_port_buf_size s' p = get_port_buf_size t' p) \<and>
              (\<not> is_dest_port s' p \<longrightarrow>
               p \<in> get_ports_of_partition s' d \<longrightarrow> is_a_queuingport s' p = is_a_queuingport t' p \<and> \<not> is_dest_port t' p)"
              proof(cases "pname \<in> get_partition_cfg_ports_byid sysconf (current s)")
              assume b0:"pname \<in> get_partition_cfg_ports_byid sysconf (current s)"
                with a2 have b1:"pname \<in> get_partition_cfg_ports_byid sysconf (current t)" by simp
                have b2:"p \<noteq> get_portid_in_type (the (get_queuingport_conf sysconf pname))" 
                  using b0 port_partition by auto 
                then show ?thesis using b0 port_partition by auto 
              next
                assume c0:"\<not>(pname \<in> get_partition_cfg_ports_byid sysconf (current s))"
                with a2 have c1:"\<not>(pname \<in> get_partition_cfg_ports_byid sysconf (current t))" by simp
                have c2:"s' = s" by (simp add: c0 create_queuing_port_def p3)
                have c3:"t' = t" by (simp add: c1 create_queuing_port_def p4) 
                then show ?thesis using c0 a1 c2 using p6  by auto   
              qed
          }
          then show ?thesis by auto
          qed
      }
      qed

  lemma crt_que_port_presrv_wk_stp_cons:
      assumes p1:"is_a_partition sysconf (current s)"
        and   p2:"reachable0 s \<and> reachable0 t"
        and   p3:"s \<sim> d \<sim> t"
        and   p4:"s \<sim> (scheduler sysconf) \<sim> t"
        and   p5:"(current s) \<leadsto> d"
        and   p6:"s \<sim> (current s) \<sim> t"
        and   p7:"s' = fst (create_queuing_port sysconf s pname)"
        and   p8:"t' = fst (create_queuing_port sysconf t pname)"
      shows   "s' \<sim> d \<sim> t'"
  proof(cases "is_a_scheduler sysconf d")
    assume a0:"is_a_scheduler sysconf d"
    show ?thesis by (smt a0 interference1_def p1 p5 sche_imp_not_part)  
  next
    assume a1:"\<not> is_a_scheduler sysconf d"
    show ?thesis
    proof(cases "is_a_partition sysconf d")
      assume b0:"is_a_partition sysconf d"
      show ?thesis 
      proof(cases "current s = d")
        assume c0:"current s = d"
        have d0:"vpeq_part s' d t'"
        proof -
        {
          have e1:"partitions s' d = partitions t' d"
          proof - 
          {
            from p3 b0 have f1:"partitions s d = partitions t d" 
              using a1 is_a_scheduler_def is_a_transmitter_def 
              part_imp_not_tras vpeq1_def vpeq_part_def by fastforce
            from p7 have f2:"partitions s d = partitions s' d"
              using b0 c0 crt_que_port_notchg_partstate by auto
            from p8 have f3:"partitions t d = partitions t' d"
              using b0 c0 crt_que_port_notchg_partstate p4 sched_current_lemma 
              by auto
            with f1 f2 have "partitions s' d = partitions t' d" by auto
          } then show ?thesis by auto
          qed
          have e2:"vpeq_part_comm s' d t'"
          proof -
          {
            from p3 a1 b0 have f1:"vpeq_part_comm s d t" 
              using part_imp_not_tras  by fastforce 
            then have "vpeq_part_comm s' d t'"
              using c0 crt_que_port_presrv_comm_of_current_part p1 p2 p4 p7 p8 by auto                        
          } then show ?thesis by auto qed
          with e1 have "vpeq_part s' d t'" by auto
        } then show ?thesis by auto qed
        then show ?thesis using a1 b0                              
          using  trans_imp_not_part by fastforce                
      next
        assume c1:"current s \<noteq> d" 
        have d1:"vpeq_part s' d t'" 
        proof -
        {
          have e1:"partitions s' d = partitions t' d"
            using a1 b0 crt_que_port_notchg_partstate
             p1 p3 p4 p7 p8 part_not_trans by auto
          have e2:"vpeq_part_comm s' d t'"
            using b0 c1 p1 p5 part_imp_not_sch part_imp_not_tras by auto                   
         with e1 have "vpeq_part s' d t'" by auto
        }
        then show ?thesis by auto qed
        show ?thesis using a1 b0 c1 trans_imp_not_part d1 by fastforce              
      qed
    next
      assume b1:"\<not> is_a_partition sysconf d"
      show ?thesis
      proof(cases "is_a_transmitter sysconf d")
        assume c0:"is_a_transmitter sysconf d"
        have "vpeq_transmitter s' d t'"
              using p3 p4 p7 p8 c0 crt_que_port_presrv_comm_part_ports[OF p2]  by auto                               
        then show ?thesis using a1 b1 is_a_scheduler_def vpeq1_def by auto              
      next
        assume c1:"\<not> is_a_transmitter sysconf d"
        show ?thesis using a1 b1 c1  is_a_transmitter_def vpeq1_def by auto
      qed
    qed
  qed

  lemma crt_que_port_presrv_wk_stp_cons_e: "weak_step_consistent_e (hyperc (Create_Queuing_Port p))"
    using crt_que_port_presrv_wk_stp_cons weak_step_consistent_e_def exec_event_def mem_Collect_eq
      non_interference1_def non_interference_def singletonD sched_vpeq same_part_mode
    by (smt Event.case(1) Hypercall.case(6) domain_of_event.simps(1) event_enabled.simps(1) option.sel prod.simps(2))

subsubsection{*proving "send queuing message" satisfying the "step consistent" property*}

  lemma snd_que_msg_lst_presrv_comm_part_ports:
    assumes   p1:"reachable0 s \<and> reachable0 t"
        and   p2:"s \<sim> (transmitter sysconf) \<sim> t"
        and   p5:"s \<sim> (scheduler sysconf) \<sim> t"
        and   p3:"s' = fst (send_queuing_message_maylost sysconf s pid m)"
        and   p4:"t' = fst (send_queuing_message_maylost sysconf t pid m)"
    shows   "comm s' = comm t' \<and> part_ports s' = part_ports t'"
  proof -
  {
    from p2 have a0:"vpeq_transmitter s (transmitter sysconf) t" using sch_not_trans vpeq1_def by auto 
    then have a1:"comm s = comm t \<and> part_ports s = part_ports t" unfolding vpeq_transmitter_def by auto
    from p1 have a2:"port_consistent s \<and> port_consistent t" by (simp add: port_cons_reach_state) 
    show ?thesis
    proof(cases "\<not> is_a_queuingport s pid
              \<or> \<not> is_source_port s pid
              \<or> \<not> is_a_port_of_partition s pid (current s)")
      assume b0:"\<not> is_a_queuingport s pid
              \<or> \<not> is_source_port s pid
              \<or> \<not> is_a_port_of_partition s pid (current s)"
      with p3 have b1:"s' = s" by (simp add: send_queuing_message_maylost_def) 
      have b2:"\<not> is_a_queuingport t pid
              \<or> \<not> is_source_port t pid 
              \<or> \<not> is_a_port_of_partition t pid (current t)"
              using a1 b0 is_a_port_of_partition_def is_a_queuingport_def 
              is_source_port_def p5 sched_current_lemma
              by (simp add: vpeq1_def vpeq_sched_def)
      with p4 have b3:"t' = t" using send_queuing_message_maylost_def by auto 
      with a1 b1 show ?thesis by simp
    next
      assume b1:"\<not>(\<not> is_a_queuingport s pid 
                \<or> \<not> is_source_port s pid
                \<or> \<not> is_a_port_of_partition s pid (current s))"
      show ?thesis
      proof(cases "is_full_portqueuing sysconf s pid")
        assume c0:"is_full_portqueuing sysconf s pid"
        with b1 have c1:"s' = s" by (simp add: p3 replace_msg2queuing_port_def 
                                    send_queuing_message_maylost_def) 
        with a1 c0 have c2:"is_full_portqueuing sysconf t pid"
          by (simp add: get_port_conf_byid_def get_port_byid_def is_full_portqueuing_def) 
        then have c3:"t' = t" by (simp add: p4 replace_msg2queuing_port_def 
                                    send_queuing_message_maylost_def) 
        with a1 c1 show ?thesis by auto 
      next
        assume c0:"\<not> is_full_portqueuing sysconf s pid"
        have c1:"s' = insert_msg2queuing_port s pid m" 
          using b1 c0 p3 send_queuing_message_maylost_def by auto 
        with a1 c0 have c2:"\<not> is_full_portqueuing sysconf t pid"
          by (simp add: get_port_conf_byid_def get_port_byid_def is_full_portqueuing_def) 
        then have c3:"t' = insert_msg2queuing_port t pid m" 
          using b1 c2 p4 send_queuing_message_maylost_def a1 is_a_port_of_partition_def 
            is_a_queuingport_def is_source_port_def old.prod.inject p5 
            prod.collapse vpeq1_def vpeq_sched_def by auto
        with b1 show ?thesis
        proof(induct "(ports (comm s)) pid")
          case None show ?case by (simp add: None.hyps a1 c1 c3 insert_msg2queuing_port_def option.case_eq_if)   
        next
          case (Some x) 
          have e0:"(ports (comm s)) pid = Some x" by (simp add: Some.hyps)
          show ?case
          proof(induct "the ((ports (comm s)) pid)")
            case (Queuing x1 x2 x3 x4 x5)
            show ?case
              by (smt Communication_State.surjective Communication_State.update_convs(1) 
                Port_Type.simps(5) Queuing.hyps State.select_convs(3) State.select_convs(4) 
                State.surjective State.update_convs(3) a1 c1 c3 insert_msg2queuing_port_def 
                option.case_eq_if)    
          next
            case (Sampling x1 x2 x3 x4)
            show ?case using Sampling.hyps a1 c1 c3 e0 insert_msg2queuing_port_def by auto  
          qed
        qed
      qed
    qed
  }
  qed



lemma is_dest_queuing_send:
   "t' = fst (send_queuing_message_maylost sysconf t pid m) \<Longrightarrow>       
   (is_dest_port t p = is_dest_port t' p) \<and> (is_a_queuingport t p = is_a_queuingport t' p)"
    apply(clarsimp simp:send_queuing_message_maylost_def replace_msg2queuing_port_def insert_msg2queuing_port_def)    
    apply(case_tac "ports (comm t) pid")
    apply simp
    apply(case_tac "a") 
    using is_a_queuingport_def is_dest_port_def               
    by auto

  lemma snd_que_msg_lst_presrv_comm_of_current_part:
  assumes   p1:"reachable0 s \<and> reachable0 t"
      and   p2:"s \<sim> (scheduler sysconf) \<sim> t"
      and   p3:"s' = fst (send_queuing_message_maylost sysconf s pid m)"
      and   p4:"t' = fst (send_queuing_message_maylost sysconf t pid m)"
      and   p5:"(current s) = d"
      and   p6:"vpeq_part_comm s d t" 
      and   p7:"is_a_partition sysconf d"
  shows   "vpeq_part_comm s' d t'"  
  proof-  
    from p6 have a1:"get_ports_of_partition s d = get_ports_of_partition t d" 
       by auto
    from p2 have a2:"current s = current t" using sched_current_lemma by simp  
    from p3 p5 p7 have a3:"part_ports s = part_ports s'" using snd_que_msg_lst_notchg_partports by simp
    then have a4:"get_ports_of_partition s d = get_ports_of_partition s' d"
      using part_ports_imp_portofpart by blast 
    from p4 p5 p7 a2 have a5:"part_ports t = part_ports t'" using snd_que_msg_lst_notchg_partports by simp
    then have a6:"get_ports_of_partition t d = get_ports_of_partition t' d"
      using part_ports_imp_portofpart by blast 
    have g0:"get_ports_of_partition s' d = get_ports_of_partition t' d"
      using a1 a4 a6 by simp 
    moreover have "\<forall>p. p \<in> get_ports_of_partition s' d \<longrightarrow>
              is_a_queuingport s' p = is_a_queuingport t' p \<and>
              is_dest_port s' p = is_dest_port t' p \<and>
              (if is_dest_port s' p then get_port_buf_size s' p = get_port_buf_size t' p else True)" 
    using a4 by (metis  empty_iff inf.idem no_cfgport_impl_noports p1 port_partition) 
    ultimately show  ?thesis by auto
  qed  

 lemma snd_que_msg_lst_presrv_wk_stp_cons:
    assumes p1:"is_a_partition sysconf (current s)"
      and   p2:"reachable0 s \<and> reachable0 t"
      and   p3:"s \<sim> d \<sim> t"
      and   p4:"s \<sim> (scheduler sysconf) \<sim> t"
      and   p5:"(current s) \<leadsto> d"
      and   p6:"s \<sim> (current s) \<sim> t"
      and   p7:"s' = fst (send_queuing_message_maylost sysconf s pid m)"
      and   p8:"t' = fst (send_queuing_message_maylost sysconf t pid m)"
    shows   "s' \<sim> d \<sim> t'"
  proof(cases "is_a_scheduler sysconf d")
    assume a0:"is_a_scheduler sysconf d"
    show ?thesis by (metis a0 interference1_def p1 p5 sche_imp_not_part)  
  next
    assume a1:"\<not> is_a_scheduler sysconf d"
    show ?thesis
    proof(cases "is_a_partition sysconf d")
      assume b0:"is_a_partition sysconf d"
      show ?thesis 
      proof(cases "current s = d")
        assume c0:"current s = d"
        have d0:"vpeq_part s' d t'"
        proof -
        {
          have e1:"partitions s' d = partitions t' d"
          proof - 
          {
            from p3 b0 have f1:"partitions s d = partitions t d" 
              using a1 part_imp_not_tras by fastforce
            from p7 have f2:"partitions s d = partitions s' d"
              using b0 c0 snd_que_msg_lst_notchg_partstate by auto
            from p8 have f3:"partitions t d = partitions t' d"
              using b0 c0 p4 sched_current_lemma snd_que_msg_lst_notchg_partstate 
              by auto
            with f1 f2 have "partitions s' d = partitions t' d" by auto
          }
          then show ?thesis by auto
          qed
          have e2:"vpeq_part_comm s' d t'"
            proof -
              from p3 a1 b0 have f1:"vpeq_part_comm s d t" 
                using part_imp_not_tras by fastforce 
              then show ?thesis
                using c0 p1 p2 p4 p7 p8 snd_que_msg_lst_presrv_comm_of_current_part by auto
            qed
          with e1 have "vpeq_part s' d t'" by auto
        }
        then show ?thesis by auto qed
        then show ?thesis                                  
          using  a1 b0 trans_imp_not_part by fastforce                
      next
        assume c1:"current s \<noteq> d" 
        have d1:"vpeq_part s' d t'" 
        proof -
        {
          have e1:"partitions s' d = partitions t' d"
            using a1 b0 is_a_partition_def  p1 p3 p4 p7 p8 
            part_not_trans snd_que_msg_lst_notchg_partstate  
            by auto               
          have e2:"vpeq_part_comm s' d t'"
            proof -
              from p3 a1 b0 have f1:"vpeq_part_comm s d t" 
                using  part_imp_not_tras by fastforce 
              have f2:"vpeq_part_comm s d s'" 
                using c1 p1 p2 p7 snd_que_msg_lst_notchg_comminotherdom by blast
              have f3:"vpeq_part_comm t d t'"
                using c1 p1 p2 p4 p8 sched_current_lemma 
                     snd_que_msg_lst_notchg_comminotherdom
                by (meson b0 interference1_def p5 part_imp_not_sch trans_imp_not_part) 
              then show ?thesis
                using f1 f2 vpeq_part_comm_symmetric_lemma vpeq_part_comm_transitive_lemma by blast 
            qed
            
          with e1 have "vpeq_part s' d t'"  by auto
        }
            then show ?thesis by auto
        qed
        show ?thesis using a1 b0 c1                    
          using trans_imp_not_part d1 by fastforce                    
      qed
    next
      assume b1:"\<not> is_a_partition sysconf d"
      show ?thesis
      proof(cases "is_a_transmitter sysconf d")
        assume c0:"is_a_transmitter sysconf d"
        show ?thesis
          proof -
          {
            have "vpeq_transmitter s' d t'" unfolding vpeq_transmitter_def
            proof-
              from p2 p3 p4 p7 p8
              show "comm s' = comm t' \<and> part_ports s' = part_ports t' "
                using c0 snd_que_msg_lst_presrv_comm_part_ports[OF p2 _ p4 p7 p8] by auto
            qed
          }
          then show ?thesis using a1 b1 by auto
          qed
      next
        assume c1:"\<not> is_a_transmitter sysconf d"
        show ?thesis using a1 b1 c1 by auto
      qed
    qed
  qed

  lemma snd_que_msg_lst_presrv_wk_stp_cons_e: "weak_step_consistent_e (hyperc (Send_Queuing_Message p m))"
    using snd_que_msg_lst_presrv_wk_stp_cons weak_step_consistent_e_def exec_event_def mem_Collect_eq
      non_interference1_def non_interference_def singletonD sched_vpeq same_part_mode vpeq1_def vpeq_sched_def
        by (smt Event.case(1) Hypercall.case(7) domain_of_event.simps(1) 
            event_enabled.simps(1) option.sel prod.simps(2))

subsubsection{*proving "receive queuing message" satisfying the "step consistent" property*}

  lemma rec_que_msg_presrv_comm_part_ports:
    assumes   p1:"reachable0 s \<and> reachable0 t"
        and   p2:"s \<sim> (transmitter sysconf) \<sim> t"
        and   p5:"s \<sim> (scheduler sysconf) \<sim> t"
        and   p3:"s' = fst (receive_queuing_message s pid)"
        and   p4:"t' = fst (receive_queuing_message t pid)"
      shows   "comm s' = comm t' \<and> part_ports s' = part_ports t'"
  proof -
  {
    from p2 have a0:"vpeq_transmitter s (transmitter sysconf) t" using sch_not_trans by auto 
    then have a1:"comm s = comm t \<and> part_ports s = part_ports t" by auto
    from p1 have a2:"port_consistent s \<and> port_consistent t" by (simp add: port_cons_reach_state) 
    show ?thesis
    proof(cases "\<not> is_a_queuingport s pid
              \<or> \<not> is_a_port_of_partition s pid (current s)
              \<or> \<not> is_dest_port s pid
              \<or> is_empty_portqueuing s pid")
      assume b0:"\<not> is_a_queuingport s pid
              \<or> \<not> is_a_port_of_partition s pid (current s)
              \<or> \<not> is_dest_port s pid 
              \<or> is_empty_portqueuing s pid"
      with p3 have b1:"s' = s" by (simp add: receive_queuing_message_def) 
      have b2:"\<not> is_a_queuingport t pid 
              \<or> \<not> is_a_port_of_partition t pid (current t) 
              \<or> \<not> is_dest_port t pid
              \<or> is_empty_portqueuing t pid"
        using a1 b0 get_port_byid_def is_a_port_of_partition_def is_a_queuingport_def 
        is_dest_port_def is_empty_portqueuing_def p5 sched_current_lemma by auto                    
      with p4 have b3:"t' = t" using receive_queuing_message_def by auto 
      with a1 b1 show ?thesis by simp
    next
      assume b1:"\<not>(\<not> is_a_queuingport s pid
              \<or> \<not> is_a_port_of_partition s pid (current s) 
              \<or> \<not> is_dest_port s pid 
              \<or> is_empty_portqueuing s pid)"
      then have b2:"s' = fst (remove_msg_from_queuingport s pid)" by (simp add: p3 receive_queuing_message_def) 
      with b1 have b3:"\<not>(\<not> is_a_queuingport t pid
                        \<or> \<not> is_a_port_of_partition t pid (current t)
                        \<or> \<not> is_dest_port t pid
                        \<or> is_empty_portqueuing t pid)"
          using a1 get_port_byid_def is_a_port_of_partition_def is_a_queuingport_def 
            is_dest_port_def is_empty_portqueuing_def p5 sched_current_lemma  by auto
      then have b4:"t' = fst (remove_msg_from_queuingport t pid)" by (simp add: p4 receive_queuing_message_def)             
      then show ?thesis
      proof(induct "(ports (comm s)) pid")
        case None show ?case using None.hyps a1 b2 b4 remove_msg_from_queuingport_def by auto    
      next
        case (Some x) 
        have e0:"(ports (comm s)) pid = Some x" by (simp add: Some.hyps)
        show ?case
          proof(induct "the ((ports (comm s)) pid)")
            case (Queuing x1 x2 x3 x4 x5)
            show ?case
              by (smt Communication_State.surjective Communication_State.update_convs(1) 
                Port_Type.simps(5) Queuing.hyps State.select_convs(3) State.select_convs(4) 
                State.surjective State.update_convs(3) a1 b2 b4 eq_fst_iff option.case_eq_if 
                remove_msg_from_queuingport_def) 
          next
            case (Sampling x1 x2 x3 x4)
            show ?case using Sampling.hyps a1 b2 b4 e0 remove_msg_from_queuingport_def by auto
          qed
      qed
    qed
  }
  qed

lemma is_dest_queuing_receive:
   "t' = fst (receive_queuing_message  t pid) \<Longrightarrow>       
   (is_dest_port t p = is_dest_port t' p) \<and> (is_a_queuingport t p = is_a_queuingport t' p)"
    apply(clarsimp simp:receive_queuing_message_def remove_msg_from_queuingport_def)    
    apply(case_tac "ports (comm t) pid")
    apply simp
    apply(case_tac "a")
    using  is_a_queuingport_def is_dest_port_def     
    by auto

lemma rec_que_msg_presrv_comm_of_current_part:
  assumes p1:"reachable0 s \<and> reachable0 t"
    and   p2:"s \<sim> (scheduler sysconf) \<sim> t"
    and   p3:"s' = fst (receive_queuing_message s pid)"
    and   p4:"t' = fst (receive_queuing_message t pid)"
    and   p5:"(current s) = d"
    and   p6:"vpeq_part_comm s d t" 
    and   p7:"is_a_partition sysconf d"
  shows   "vpeq_part_comm s' d t'"
  proof-  
    from p6 have a1:"get_ports_of_partition s d = get_ports_of_partition t d" 
        by auto
    from p2 have a2:"current s = current t" using  sched_current_lemma by simp  
    from p3 p5 p7 have a3:"part_ports s = part_ports s'" using rec_que_msg_notchg_partports by simp
    then have a4:"get_ports_of_partition s d = get_ports_of_partition s' d"
      using part_ports_imp_portofpart by blast 
    from p4 p5 p7 a2 have a5:"part_ports t = part_ports t'" using rec_que_msg_notchg_partports by simp
    then have a6:"get_ports_of_partition t d = get_ports_of_partition t' d"
      using part_ports_imp_portofpart by blast 
    have g0:"get_ports_of_partition s' d = get_ports_of_partition t' d"
      using a1 a4 a6 by simp 
    moreover have "\<forall>p. p \<in> get_ports_of_partition s' d \<longrightarrow>
              is_a_queuingport s' p = is_a_queuingport t' p \<and>
              is_dest_port s' p = is_dest_port t' p \<and>
              (if is_dest_port s' p then get_port_buf_size s' p = get_port_buf_size t' p else True)" 
    using p3 p4 is_dest_queuing_receive p6 a1 a4  
      by (metis  empty_iff inf.idem no_cfgport_impl_noports p1 port_partition) 
    ultimately show  ?thesis by auto
  qed  

  lemma rec_que_msg_presrv_wk_stp_cons:
    assumes p1:"is_a_partition sysconf (current s)"
      and   p2:"reachable0 s \<and> reachable0 t"
      and   p3:"s \<sim> d \<sim> t"
      and   p4:"s \<sim> (scheduler sysconf) \<sim> t"
      and   p5:"(current s) \<leadsto> d"
      and   p6:"s \<sim> (current s) \<sim> t"
      and   p7:"s' = fst (receive_queuing_message s pid)"
      and   p8:"t' = fst (receive_queuing_message t pid)"
    shows   "s' \<sim> d \<sim> t'"
  proof(cases "is_a_scheduler sysconf d")
    assume a0:"is_a_scheduler sysconf d"
    show ?thesis by (metis a0 interference1_def p1 p5 sche_imp_not_part)
  next
    assume a1:"\<not> is_a_scheduler sysconf d"
    show ?thesis
    proof(cases "is_a_partition sysconf d")
      assume b0:"is_a_partition sysconf d"
      show ?thesis 
      proof(cases "current s = d")
        assume c0:"current s = d"
        have d0:"vpeq_part s' d t'"
        proof -
        {
          have e1:"partitions s' d = partitions t' d"
          proof - 
          {
            from p3 b0 have f1:"partitions s d = partitions t d" 
              using a1 part_imp_not_tras by fastforce
            from p7 have f2:"partitions s d = partitions s' d"
              using b0 c0 rec_que_msg_notchg_partstate by auto
            from p8 have f3:"partitions t d = partitions t' d"
              using b0 c0 p4 sched_current_lemma rec_que_msg_notchg_partstate 
              by auto
            with f1 f2 have "partitions s' d = partitions t' d" by auto
          }
          then show ?thesis by auto qed
          have e2:"vpeq_part_comm s' d t'" using rec_que_msg_presrv_comm_of_current_part
            by (metis (no_types, lifting) a1 b0 c0 is_a_scheduler_def is_a_transmitter_def 
              p2 p3 p4 p7 p8 trans_imp_not_part vpeq1_def vpeq_part_def) 
            
          with e1 have "vpeq_part s' d t'" by auto
        } then show ?thesis by auto qed
        then show ?thesis  using a1 b0                            
          using  trans_imp_not_part by fastforce              
      next
        assume c1:"current s \<noteq> d" 
        have d1:"vpeq_part s' d t'" 
        proof -
        {
          have e1:"partitions s' d = partitions t' d"
            using a1 b0  p1 p3 p4 p7 p8 
            part_not_trans rec_que_msg_notchg_partstate  by auto 
            
          have e2:"vpeq_part_comm s' d t'"
          proof -
            from p3 a1 b0 have f1:"vpeq_part_comm s d t" 
              using part_imp_not_tras by fastforce 
            have f2:"vpeq_part_comm s d s'" 
              using c1 p1 p2 p7 rec_que_msg_notchg_comminotherdom by blast
            have f3:"vpeq_part_comm t d t'"
              using c1 p1 p2 p4 p8 rec_que_msg_notchg_comminotherdom sched_current_lemma
              by (meson b0 interference1_def p5 part_imp_not_sch trans_imp_not_part)                       
            then show ?thesis
              using f1 f2 vpeq_part_comm_symmetric_lemma vpeq_part_comm_transitive_lemma by blast 
          qed                   
          with e1 have "vpeq_part s' d t'" by auto
        } then show ?thesis by auto qed
        then show ?thesis using a1 b0 c1 trans_imp_not_part  by fastforce 
      qed
    next
      assume b1:"\<not> is_a_partition sysconf d"
      show ?thesis
      proof(cases "is_a_transmitter sysconf d")
        assume c0:"is_a_transmitter sysconf d"
        show ?thesis
        proof -
        {
          have "vpeq_transmitter s' d t'" unfolding vpeq_transmitter_def
          proof-
            from p2 p3 p4 p7 p8
            show "comm s' = comm t' \<and> part_ports s' = part_ports t' "
              using c0 rec_que_msg_presrv_comm_part_ports[OF p2]  by auto
          qed
        }
        then show ?thesis using a1 b1 is_a_scheduler_def vpeq1_def by auto
        qed
      next
        assume c1:"\<not> is_a_transmitter sysconf d"
        show ?thesis using a1 b1 c1 is_a_scheduler_def is_a_transmitter_def vpeq1_def by auto
      qed
    qed
  qed

  lemma rec_que_msg_presrv_wk_stp_cons_e: "weak_step_consistent_e (hyperc (Receive_Queuing_Message p))"
    using rec_que_msg_presrv_wk_stp_cons weak_step_consistent_e_def exec_event_def mem_Collect_eq
      non_interference1_def non_interference_def singletonD sched_vpeq same_part_mode
        by (smt Event.case(1) Hypercall.case(8) domain_of_event.simps(1) 
            event_enabled.simps(1) option.sel prod.simps(2))

subsubsection{*proving "get queuing portid" satisfying the "step consistent" property*}

  lemma get_que_pid_presrv_wk_stp_cons:
      assumes p1:"s \<sim> d \<sim> t"
        and   p2:"s' = fst (get_queuing_port_id sysconf s pname)"
        and   p3:"t' = fst (get_queuing_port_id sysconf t pname)"
      shows   "s' \<sim> d \<sim> t'"
    proof -
      have a0:"s' = s" by (simp add: p2 get_queuing_port_id_def) 
      have a1:"t' = t" by (simp add: p3 get_queuing_port_id_def)
      then show ?thesis using  a0 p1 by blast
    qed

  lemma get_que_pid_presrv_wk_stp_cons_e: "weak_step_consistent_e (hyperc (Get_Queuing_Portid p))"
    using get_que_pid_presrv_wk_stp_cons weak_step_consistent_e_def exec_event_def mem_Collect_eq
      non_interference1_def non_interference_def singletonD sched_vpeq same_part_mode
        by (smt Event.case(1) Hypercall.case(9) domain_of_event.simps(1) 
            event_enabled.simps(1) option.sel prod.simps(2))

subsubsection{*proving "get queuing port status" satisfying the "step consistent" property*}

  lemma get_que_psts_presrv_wk_stp_cons:
      assumes p1:"s \<sim> d \<sim> t"
        and   p2:"s' = fst (get_queuing_port_status sysconf s pid)"
        and   p3:"t' = fst (get_queuing_port_status sysconf t pid)"
      shows   "s' \<sim> d \<sim> t'"
    proof -
      have a0:"s' = s" by (simp add: p2 get_queuing_port_status_def) 
      have a1:"t' = t" by (simp add: p3 get_queuing_port_status_def)
      then show ?thesis using a0 p1 by blast
    qed

  lemma get_que_psts_presrv_wk_stp_cons_e: "weak_step_consistent_e (hyperc (Get_Queuing_Portstatus p))"
    using get_que_psts_presrv_wk_stp_cons weak_step_consistent_e_def exec_event_def mem_Collect_eq
      non_interference1_def non_interference_def singletonD sched_vpeq same_part_mode
        by (smt Event.case(1) Hypercall.case(10) domain_of_event.simps(1) event_enabled.simps(1) 
              option.sel prod.simps(2) vpeq1_def vpeq_sched_def)

subsubsection{*proving "clear queuing port" satisfying the "step consistent" property*}

  lemma clr_que_port_presrv_comm_part_ports:
  assumes   p1:"reachable0 s \<and> reachable0 t"
      and   p2:"s \<sim> (transmitter sysconf) \<sim> t"
      and   p5:"s \<sim> (scheduler sysconf) \<sim> t"
      and   p3:"s' = clear_queuing_port s pid"
      and   p4:"t' = clear_queuing_port t pid"
  shows   "comm s' = comm t' \<and> part_ports s' = part_ports t'"
  proof -
  {
    from p2 have a0:"vpeq_transmitter s (transmitter sysconf) t" using sch_not_trans  by auto 
    then have a1:"comm s = comm t \<and> part_ports s = part_ports t" by auto
    from p1 have a2:"port_consistent s \<and> port_consistent t" by (simp add: port_cons_reach_state) 
    show ?thesis
    proof(cases "\<not> is_a_queuingport s pid 
                \<or> \<not> is_a_port_of_partition s pid (current s)
                \<or> \<not> is_dest_port s pid")
      assume b0:"\<not> is_a_queuingport s pid 
                \<or> \<not> is_a_port_of_partition s pid (current s)
                \<or> \<not> is_dest_port s pid"
      with p3 have b1:"s' = s" by (simp add: clear_queuing_port_def) 
      have b2:"\<not> is_a_queuingport t pid
                \<or> \<not> is_a_port_of_partition t pid (current t) 
                \<or> \<not> is_dest_port t pid"
      using a1 b0 get_port_byid_def is_a_port_of_partition_def is_a_queuingport_def 
      is_dest_port_def is_empty_portqueuing_def p5 sched_current_lemma 
       by auto
              
      with p4 have b3:"t' = t" using clear_queuing_port_def by auto 
      with a1 b1 show ?thesis by simp
    next
      assume b0:"\<not>(\<not> is_a_queuingport s pid
                \<or> \<not> is_a_port_of_partition s pid (current s) 
                \<or> \<not> is_dest_port s pid)"
      then have b00:"\<not>(\<not> is_a_queuingport t pid
                \<or> \<not> is_a_port_of_partition t pid (current t)
                \<or> \<not> is_dest_port t pid)"
         using a1 is_a_port_of_partition_def is_a_queuingport_def 
              is_dest_port_def p5 sched_current_lemma by auto 
      with p3 have b1:"part_ports s' = part_ports s"
        by (metis Int_absorb a2 empty_iff is_a_port_of_partition_def 
          option.distinct(1) port_consistent_def port_partition)  
      
      with p4 b0 have b2:"part_ports t' = part_ports t"
        by (metis Int_absorb a2 empty_iff is_a_port_of_partition_def 
          option.distinct(1) port_consistent_def port_partition)
      
      with p3 b0 have b3:"ports (comm s') = (ports (comm s))
        (pid := Some (clear_msg_queuingport (the ((ports (comm s)) pid))))"
        by (metis (no_types, lifting) Communication_State.select_convs(1) 
          Communication_State.surjective Communication_State.update_convs(1) 
          State.select_convs(3) State.surjective State.update_convs(3) clear_queuing_port_def)
  
      with p4 b00 have b4:"ports (comm t') = (ports (comm t))
        (pid := Some (clear_msg_queuingport (the ((ports (comm t)) pid))))"
        by (metis (no_types, lifting) Communication_State.ext_inject Communication_State.surjective 
          Communication_State.update_convs(1) State.select_convs(3) State.surjective State.update_convs(3)
          clear_queuing_port_def)
      show ?thesis by (simp add: a1 b1 b2 b3 b4)
    qed
  }
  qed

lemma is_dest_queuing_clear:
   "t' = clear_queuing_port t pid \<Longrightarrow>       
   (is_dest_port t p = is_dest_port t' p) \<and> (is_a_queuingport t p = is_a_queuingport t' p)"
    apply(clarsimp simp:clear_queuing_port_def Let_def)
    apply(clarsimp simp:clear_msg_queuingport_def)
    apply(case_tac "ports (comm t) pid")
    apply (simp add: is_a_queuingport_def)
    apply(case_tac "a")
    by (auto simp add: is_a_queuingport_def is_dest_port_def)

  lemma clr_que_port_presrv_comm_of_current_part:
  assumes p1:"reachable0 s \<and> reachable0 t"
    and   p2:"s \<sim> (scheduler sysconf) \<sim> t"
    and   p3:"s' = clear_queuing_port s pid"
    and   p4:"t' = clear_queuing_port t pid"
    and   p5:"(current s) = d"
    and   p6:"vpeq_part_comm s d t" 
    and   p7:"is_a_partition sysconf d"
  shows   "vpeq_part_comm s' d t'"     
  proof-      
    from p6 have a1:"get_ports_of_partition s d = get_ports_of_partition t d" 
      by auto
    from p3 p5 p7 have a3:"part_ports s = part_ports s'" using clr_que_port_notchg_partports by blast
    then have a4:"get_ports_of_partition s d = get_ports_of_partition s' d"
      using part_ports_imp_portofpart by blast 
    from p4 p5 p7 have a5:"part_ports t = part_ports t'" using clr_que_port_notchg_partports by blast
    then have a6:"get_ports_of_partition t d = get_ports_of_partition t' d"
      using part_ports_imp_portofpart by blast 
    have g0:"get_ports_of_partition s' d = get_ports_of_partition t' d"
      using a1 a4 a6 by simp 
    also have "\<forall>p. p \<in> get_ports_of_partition s' d \<longrightarrow>
              is_a_queuingport s' p = is_a_queuingport t' p \<and>
              is_dest_port s' p = is_dest_port t' p \<and>
              (if is_dest_port s' p then get_port_buf_size s' p = get_port_buf_size t' p else True)" 
    using  a4 by (metis  empty_iff inf.idem no_cfgport_impl_noports p1 port_partition) 
    ultimately show  ?thesis by auto
 qed

  lemma clr_que_port_presrv_wk_stp_cons:
    assumes p1:"is_a_partition sysconf (current s)"
      and   p2:"reachable0 s \<and> reachable0 t"
      and   p3:"s \<sim> d \<sim> t"
      and   p4:"s \<sim> (scheduler sysconf) \<sim> t"
      and   p5:"(current s) \<leadsto> d"
      and   p6:"s \<sim> (current s) \<sim> t"
      and   p7:"s' = clear_queuing_port s pid"
      and   p8:"t' = clear_queuing_port t pid"
    shows   "s' \<sim> d \<sim> t'"
  proof(cases "is_a_scheduler sysconf d")
    assume a0:"is_a_scheduler sysconf d"
    show ?thesis by (metis a0 interference1_def p1 p5 sche_imp_not_part)  
  next
    assume a1:"\<not> is_a_scheduler sysconf d"
    show ?thesis
    proof(cases "is_a_partition sysconf d")
      assume b0:"is_a_partition sysconf d"
      show ?thesis 
      proof(cases "current s = d")
        assume c0:"current s = d"
        have d0:"vpeq_part s' d t'"
        proof -
        {
          have e1:"partitions s' d = partitions t' d"
            proof - 
            {
              from p3 b0 have f1:"partitions s d = partitions t d" 
                using a1 part_imp_not_tras by fastforce
              from p7 have f2:"partitions s d = partitions s' d"
                using b0 c0 clr_que_port_notchg_partstate by auto
              from p8 have f3:"partitions t d = partitions t' d"
                using b0 c0 p4 sched_current_lemma clr_que_port_notchg_partstate 
                by auto
              with f1 f2 have "partitions s' d = partitions t' d" by auto
            }
            then show ?thesis by auto
            qed
          have e2:"vpeq_part_comm s' d t'" using clr_que_port_presrv_comm_of_current_part
            by (metis (no_types, lifting) a1 b0 c0 is_a_scheduler_def is_a_transmitter_def 
              p2 p3 p4 p7 p8 trans_imp_not_part vpeq1_def vpeq_part_def) 
            
          with e1 have "vpeq_part s' d t'"  by auto
        }
        then show ?thesis by auto
        qed
        then show ?thesis using a1 b0 
          using trans_imp_not_part by fastforce                           
        next
          assume c1:"current s \<noteq> d" 
          have d1:"vpeq_part s' d t'" 
          proof -
          {
            have e1:"partitions s' d = partitions t' d"
              using a1 b0 clr_que_port_notchg_partstate
                p1 p3 p4 p7 p8 part_not_trans by auto 
              
            have e2:"vpeq_part_comm s' d t'"
            proof -
              from p3 a1 b0 have f1:"vpeq_part_comm s d t" 
                using  part_imp_not_tras  by fastforce 
              have f2:"vpeq_part_comm s d s'" using c1 p1 p2 p7 clr_que_port_notchg_comminotherdom by blast
              have f3:"vpeq_part_comm t d t'"
                using c1 p1 p2 p4 p8 clr_que_port_notchg_comminotherdom sched_current_lemma
                by (meson b0 interference1_def p5 part_imp_not_sch trans_imp_not_part)                     
              then show ?thesis
                using f1 f2 vpeq_part_comm_symmetric_lemma vpeq_part_comm_transitive_lemma by blast 
            qed                  
            with e1 have "vpeq_part s' d t'"  by auto
          }
          then show ?thesis by auto
          qed
          show ?thesis using a1 b0                        
            using  trans_imp_not_part d1 by fastforce
        qed
    next
      assume b1:"\<not> is_a_partition sysconf d"
      show ?thesis
      proof(cases "is_a_transmitter sysconf d")
        assume c0:"is_a_transmitter sysconf d"
        show ?thesis
          proof -
          {
            have "vpeq_transmitter s' d t'" unfolding vpeq_transmitter_def
            proof-
              from p2 p3 p4 p7 p8
              show "comm s' = comm t' \<and> part_ports s' = part_ports t' "
                using c0 clr_que_port_presrv_comm_part_ports[OF p2 _ p4 p7 p8] by auto 
            qed
          }
          then show ?thesis using a1 b1 is_a_scheduler_def vpeq1_def by auto
          qed
      next
        assume c1:"\<not> is_a_transmitter sysconf d"
        show ?thesis using a1 b1 c1 by auto
      qed
    qed
  qed

  lemma clr_que_port_presrv_wk_stp_cons_e: "weak_step_consistent_e (hyperc (Clear_Queuing_Port p))"
    using clr_que_port_presrv_wk_stp_cons weak_step_consistent_e_def exec_event_def mem_Collect_eq
      non_interference1_def non_interference_def singletonD sched_vpeq same_part_mode
        by (smt Event.case(1) Hypercall.case(11) domain_of_event.simps(1) event_enabled.simps(1) 
            option.sel prod.simps(2) vpeq1_def vpeq_sched_def)

subsubsection{*proving "set partition mode" satisfying the "step consistent" property*}

  lemma set_part_mode_presrv_wk_stp_cons:
    assumes p1:"is_a_partition sysconf (current s)"
      and   p2:"reachable0 s \<and> reachable0 t"
      and   p3:"s \<sim> d \<sim> t"
      and   p4:"s \<sim> (scheduler sysconf) \<sim> t"
      and   p5:"(current s) \<leadsto> d"
      and   p6:"s \<sim> (current s) \<sim> t"
      and   p7:"s' = set_partition_mode sysconf s m"
      and   p8:"t' = set_partition_mode sysconf t m"
    shows   "s' \<sim> d \<sim> t'"
  proof(cases "is_a_scheduler sysconf d")
    assume a0:"is_a_scheduler sysconf d"
    show ?thesis by (metis a0 interference1_def p1 p5 sche_imp_not_part)  
  next
    assume a1:"\<not> is_a_scheduler sysconf d"
    show ?thesis
    proof(cases "is_a_partition sysconf d")
      assume b0:"is_a_partition sysconf d"
      show ?thesis 
      proof(cases "current s = d")
        assume c0:"current s = d"
        have d0:"vpeq_part s' d t'"
        proof -
        {
          have e1:"partitions s' d = partitions t' d" 
          proof - 
          {
            from p3 b0 have f1:"partitions s d = partitions t d" 
              using a1 part_imp_not_tras by fastforce
            from p4 c0 have f2: "current t = d"
              using sched_current_lemma  by auto 
            then have "partitions s' d = partitions t' d" 
              using set_partition_mode_def p7 p8 c0 f1 f2 by auto
          }
          then show ?thesis by auto
          qed
          have e2:"vpeq_part_comm s' d t'" 
          proof -
          {
            from p3 a1 b0 have f1:"vpeq_part_comm s d t" 
              using part_imp_not_tras by fastforce 
            then have "vpeq_part_comm s' d t'"
              by (metis (mono_tags, lifting) emptyE inf.idem no_cfgport_impl_noports 
                  p1 p2 p4 p7 p8 part_ports_imp_portofpart port_partition 
                  set_part_mode_notchg_partports vpeq1_def vpeq_part_comm_def vpeq_sched_def) 
          }
          then show ?thesis by auto qed
          with e1 have "vpeq_part s' d t'"  by auto
        } then show ?thesis by auto qed
        then show ?thesis using a1 b0 trans_imp_not_part by fastforce            
      next
        assume c1:"current s \<noteq> d" 
        have d1:"vpeq_part s' d t'" 
        proof -
        {
          from p4 c1 have f2: "current t \<noteq> d"
                using sched_current_lemma vpeq1_def vpeq_sched_def by auto 
          have e1:"partitions s' d = partitions t' d"
            using a1 b0 f2  p1 p3 p4 p7 p8 
              part_not_trans set_part_mode_notchg_partstate_inotherdom  
            by auto
          have e2:"vpeq_part_comm s' d t'"
            by (metis (mono_tags, hide_lams) a1 b0 c1 is_a_partition_def is_a_scheduler_def 
              p1 p2 p3 p4 p7 p8 part_not_trans set_part_mode_notchg_comm vpeq1_def 
              vpeq_part_comm_symmetric_lemma vpeq_part_comm_transitive_lemma vpeq_part_def vpeq_sched_def)
         with e1 have "vpeq_part s' d t'" using vpeq_part_def by auto
        } then show ?thesis by auto qed
        show ?thesis  using a1 b0 trans_imp_not_part d1 by fastforce          
      qed
    next
      assume b1:"\<not> is_a_partition sysconf d"
      show ?thesis
      proof(cases "is_a_transmitter sysconf d")
        assume c0:"is_a_transmitter sysconf d"
        with p3 have c1: "vpeq_transmitter s d t" using vpeq1_def is_a_transmitter_def sch_not_trans by auto 
        show ?thesis
        proof -
        {
          have "vpeq_transmitter s' d t'" unfolding vpeq_transmitter_def
          proof(rule conjI)
            show "comm s' = comm t'"
              by (metis (mono_tags, lifting) c1 is_a_partition_def p1 p2 p4 
                p7 p8 sch_not_part set_part_mode_notchg_comm2 vpeq1_def 
                vpeq_sched_def vpeq_transmitter_def)
            show "part_ports s' = part_ports t'"
              using c1 p1 p4 p7 p8 sched_current_lemma 
              set_part_mode_notchg_partports vpeq_transmitter_def vpeq1_def vpeq_sched_def by auto   
          qed
          } then show ?thesis using a1 b1  by auto qed
      next
        assume c1:"\<not> is_a_transmitter sysconf d"
        show ?thesis using a1 b1 c1 is_a_scheduler_def is_a_transmitter_def vpeq1_def by auto
      qed
    qed
  qed

  lemma set_part_mode_presrv_wk_stp_cons_e: "weak_step_consistent_e (hyperc (Set_Partition_Mode p))"
    using set_part_mode_presrv_wk_stp_cons weak_step_consistent_e_def exec_event_def mem_Collect_eq
      non_interference1_def non_interference_def singletonD sched_vpeq same_part_mode
        by (smt Event.case(1) Hypercall.case(12) domain_of_event.simps(1) event_enabled.simps(1) 
            option.sel prod.simps(2) vpeq1_def vpeq_sched_def)

subsubsection{*proving "get partition status" satisfying the "step consistent" property*}

  lemma get_part_status_presrv_wk_stp_cons:
      assumes p1:"s \<sim> d \<sim> t"
        and   p2:"s' = fst (get_partition_status sysconf s)"
        and   p3:"t' = fst (get_partition_status sysconf t)"
      shows   "s' \<sim> d \<sim> t'"
    proof -
      have a0:"s' = s" by (simp add: p2 get_partition_status_def) 
      have a1:"t' = t" by (simp add: p3 get_partition_status_def)
      then show ?thesis using  a0 p1 by blast
    qed

  lemma get_part_status_presrv_wk_stp_cons_e: "weak_step_consistent_e (hyperc Get_Partition_Status)"
    using get_part_status_presrv_wk_stp_cons weak_step_consistent_e_def exec_event_def mem_Collect_eq
      non_interference1_def non_interference_def singletonD sched_vpeq same_part_mode
        by (smt Event.case(1) Hypercall.case(13) domain_of_event.simps(1) event_enabled.simps(1) 
            option.sel prod.simps(2) vpeq1_def vpeq_sched_def)

subsubsection{*proving "schedule" satisfying the "step consistent" property*}
  lemma schedule_presrv_wk_stp_cons:
    assumes p1:"reachable0 s \<and> reachable0 t"
      and   p3:"s \<sim> d \<sim> t"
      and   p5:"(scheduler sysconf) \<leadsto> d"
      and   p6:"s \<sim> (scheduler sysconf) \<sim> t"
      and   p7:"s' \<in> schedule sysconf s"
      and   p8:"t' \<in> schedule sysconf t"
    shows   "s' \<sim> d \<sim> t'"
  proof(cases "is_a_scheduler sysconf d")
    assume a0:"is_a_scheduler sysconf d"
    from p7 p8 have "current s' = current t'" unfolding schedule_def by simp
    with a0 show ?thesis using a0 p3 p7 p8 schedule_def by auto 
  next
    assume a1:"\<not> is_a_scheduler sysconf d"
    show ?thesis
    proof(cases "is_a_partition sysconf d")
      assume b0:"is_a_partition sysconf d"
      with p3 have b00:"vpeq_part s d t" unfolding vpeq1_def
        by (metis a1 is_a_scheduler_def is_a_transmitter_def trans_imp_not_part) 
      have b1:"vpeq_part s' d t'"
      proof -
      {
        have c1:"partitions s' d = partitions t' d"
        proof - 
        {
          from p3 b0 have f1:"partitions s d = partitions t d" 
            using a1 part_imp_not_tras by fastforce
          from p7 have f2:"partitions s d = partitions s' d"
            by (simp add: schedule_def)
          from p8 have f3:"partitions t d = partitions t' d"
            by (simp add: schedule_def)
          with f1 f2 have "partitions s' d = partitions t' d" by auto
        }
        then show ?thesis by auto
        qed
        have c2:"vpeq_part_comm s' d t'"  
        proof -
          from p7 have d1:"part_ports s = part_ports s'" by (simp add: schedule_def) 
          from p7 have d2:"comm s = comm s'" by (simp add: schedule_def) 
          with p7 d1 have d3:"vpeq_part_comm s d s'" unfolding vpeq_part_comm_def get_ports_of_partition_def
            is_a_queuingport_def is_dest_port_def get_port_buf_size_def get_port_byid_def 
            get_current_bufsize_port_def by simp
          from p8 have d4:"part_ports t = part_ports t'" by (simp add: schedule_def) 
          from p8 have d5:"comm t = comm t'" by (simp add: schedule_def) 
          with p8 d4 have "vpeq_part_comm t d t'" unfolding vpeq_part_comm_def get_ports_of_partition_def
            is_a_queuingport_def is_dest_port_def get_port_buf_size_def get_port_byid_def 
            get_current_bufsize_port_def by simp
          with b00 d1 d2 d3 d4 d5 show ?thesis
            by (meson vpeq_part_comm_symmetric_lemma vpeq_part_comm_transitive_lemma vpeq_part_def) 
        qed
        with c1 have "vpeq_part s' d t'" using vpeq_part_def by simp 
      }
      then show ?thesis by auto
      qed
      then show ?thesis
      using a1 b0  trans_imp_not_part  by auto 
    next
      assume b1:"\<not> is_a_partition sysconf d"
      show ?thesis using p3  p7 p8 sch_not_trans schedule_def a1 b1  by auto         
    qed
  qed

  lemma schedule_presrv_wk_stp_cons_e: "weak_step_consistent_e (sys Schedule)"
    using schedule_presrv_wk_stp_cons weak_step_consistent_e_def exec_event_def mem_Collect_eq
      non_interference1_def non_interference_def singletonD sched_vpeq same_part_mode
        by (smt Event.case(2) System_Event.case(1) domain_of_event.simps(2) event_enabled.simps(2) 
            option.sel prod.simps(2) vpeq1_def vpeq_sched_def)

subsubsection{*proving "Transfer Sampling Message" satisfying the "step consistent" property*}

  lemma trans_smpl_msg_presrv_comm_part_ports:
  assumes   p1:"reachable0 s \<and> reachable0 t"
      and   p2:"s \<sim> (transmitter sysconf) \<sim> t"
      and   p5:"s \<sim> (scheduler sysconf) \<sim> t"
      and   p3:"s' = transf_sampling_msg s c"
      and   p4:"t' = transf_sampling_msg t c"
  shows   "comm s' = comm t' \<and> part_ports s' = part_ports t'"
  proof -
  {
    from p2 have a0:"vpeq_transmitter s (transmitter sysconf) t" using sch_not_trans vpeq1_def by auto 
    then have a1:"comm s = comm t \<and> part_ports s = part_ports t" by auto
    from p1 have a2:"port_consistent s \<and> port_consistent t" by (simp add: port_cons_reach_state) 
    from p3 p4 show ?thesis
    proof(induct c)
      case (Channel_Sampling name sn dns) 
      show ?case
      proof(cases "get_portid_by_name s sn\<noteq>None \<and> card (get_portids_by_names s dns) = card dns")
        let ?pids = "the (get_portid_by_name s sn)"
        let ?pidt = "the (get_portid_by_name t sn)"
        let ?pidss = "get_portids_by_names s dns"
        let ?pidst = "get_portids_by_names t dns"
        let ?m = "the (get_the_msg_of_samplingport s ?pids)"
        let ?m' = "the (get_the_msg_of_samplingport t ?pidt)"
        let ?s' = "update_sampling_ports_msg s ?pidss ?m"
        let ?t' = "update_sampling_ports_msg t ?pidst ?m'"
        assume b0:"get_portid_by_name s sn\<noteq>None \<and> card (get_portids_by_names s dns) = card dns"
        with a1 have b1:"get_portid_by_name t sn\<noteq>None \<and> card (get_portids_by_names t dns) = card dns" 
          unfolding get_portid_by_name_def is_port_name_def get_portids_by_names_def by presburger 
        from b0 have b2:"s' = ?s'" using Channel_Sampling.prems(1) by auto 
        from b1 have b3:"t' = ?t'" using Channel_Sampling.prems(2) by auto 
        from a1 have b4:"?m = ?m'" unfolding get_the_msg_of_samplingport_def get_port_byid_def get_portid_by_name_def
          is_port_name_def get_msg_from_samplingport_def by auto
        from a1 have b5:"?pids = ?pidt" unfolding get_portid_by_name_def is_port_name_def by simp
        from a1 have b6:"?pidss = ?pidst" unfolding get_portids_by_names_def get_portid_by_name_def 
          is_port_name_def by simp
        with a1 b4 b5  have a7:"comm ?s' = comm ?t' \<and> part_ports ?s' = part_ports ?t'" 
          unfolding update_sampling_ports_msg_def  by simp
        with p3 p4 a1 b2 b3 show ?thesis by simp
      next
        assume b0:"\<not>(get_portid_by_name s sn\<noteq>None \<and> card (get_portids_by_names s dns) = card dns)"
        with a1 have b1:"\<not>(get_portid_by_name t sn\<noteq>None \<and> card (get_portids_by_names t dns) = card dns)" 
          unfolding get_portid_by_name_def is_port_name_def get_portids_by_names_def by presburger         
        with a1 b0 b1 Channel_Sampling show ?thesis by auto
      qed
    next
      case (Channel_Queuing nm sn dn)
      show ?case by (simp add: Channel_Queuing.prems(1) Channel_Queuing.prems(2) a1) 
    qed
  }
  qed

  lemma trans_smpl_msg_presrv_wk_stp_cons:
      assumes p1:"is_a_transmitter sysconf (current s)"
        and   p2:"reachable0 s \<and> reachable0 t"
        and   p3:"s \<sim> d \<sim> t"
        and   p4:"s \<sim> (scheduler sysconf) \<sim> t"
        and   p5:"(current s) \<leadsto> d"
        and   p6:"s \<sim> (current s) \<sim> t"
        and   p7:"s' = transf_sampling_msg s c"
        and   p8:"t' = transf_sampling_msg t c"
      shows   "s' \<sim> d \<sim> t'"
  proof(cases "is_a_scheduler sysconf d")
    assume a0:"is_a_scheduler sysconf d"
    show ?thesis using a0 no_intf_sched_help p1 p5 sch_not_trans by auto
  next
    assume a1:"\<not> is_a_scheduler sysconf d"
    have a2:"comm s' = comm t' \<and> part_ports s' = part_ports t'"
      using  p1 p6 is_a_transmitter_def trans_smpl_msg_presrv_comm_part_ports[OF p2 _ p4 p7 p8] 
      by metis
    show ?thesis
    proof(cases "is_a_partition sysconf d")
      assume b0:"is_a_partition sysconf d"
      show ?thesis 
      proof -
        have d0:"vpeq_part s' d t'"
        proof -
          have e1:"partitions s' d = partitions t' d"
            using a1 b0   p1 p3 p4 p7 p8 
            part_imp_not_tras sched_current_lemma trans_smpl_msg_notchg_partstate   
            by force                                       
          from a2 have e2:"vpeq_part_comm s' d t'"
            unfolding vpeq_part_comm_def  get_ports_of_partition_def is_a_queuingport_def 
            is_dest_port_def get_port_buf_size_def get_current_bufsize_port_def get_port_byid_def 
             by simp                
          with e1 show ?thesis by auto 
        qed
        then show ?thesis  using a1 b0                                 
          using trans_imp_not_part by fastforce
      qed
    next
      assume b1:"\<not> is_a_partition sysconf d"
      show ?thesis
      proof(cases "is_a_transmitter sysconf d")
        assume c0:"is_a_transmitter sysconf d"
        show ?thesis
        proof -
        {
          have "vpeq_transmitter s' d t'" unfolding vpeq_transmitter_def
          proof-
            from p3  p7 p8
            show "comm s' = comm t' \<and> part_ports s' = part_ports t' "
              using c0 trans_smpl_msg_presrv_comm_part_ports[OF p2 _ p4]  by auto 
          qed
        }
        then show ?thesis using a1 b1 is_a_scheduler_def vpeq1_def by auto
        qed
      next
        assume c1:"\<not> is_a_transmitter sysconf d"
        show ?thesis using a1 b1 c1 by auto
      qed
    qed
  qed

  lemma trans_smpl_msg_presrv_wk_stp_cons_e: "weak_step_consistent_e (sys (Transfer_Sampling_Message c))"
    using trans_smpl_msg_presrv_wk_stp_cons weak_step_consistent_e_def exec_event_def mem_Collect_eq
      non_interference1_def non_interference_def singletonD sched_vpeq same_part_mode
        by (smt Event.case(2) System_Event.case(2) domain_of_event.simps(2) event_enabled.simps(2) 
            option.sel prod.simps(2) is_a_transmitter_def vpeq1_def vpeq_sched_def)

subsubsection{*proving "Transfer Queuing Message" satisfying the "step consistent" property*}

  lemma trans_que_msg_mlost_presrv_comm_part_ports:
    assumes   p1:"reachable0 s \<and> reachable0 t"
        and   p2:"s \<sim> (transmitter sysconf) \<sim> t"
        and   p5:"s \<sim> (scheduler sysconf) \<sim> t"
        and   p3:"s' = transf_queuing_msg_maylost sysconf s c"
        and   p4:"t' = transf_queuing_msg_maylost sysconf t c"
      shows   "comm s' = comm t' \<and> part_ports s' = part_ports t'"
      proof -
      {
        from p2 have a0:"vpeq_transmitter s (transmitter sysconf) t" using sch_not_trans vpeq1_def by auto 
        then have a1:"comm s = comm t \<and> part_ports s = part_ports t" unfolding vpeq_transmitter_def by auto
        from p1 have a2:"port_consistent s \<and> port_consistent t" by (simp add: port_cons_reach_state) 
        from p3 p4 show ?thesis
          proof(induct c)
            case (Channel_Queuing nm sn dn) 
              show ?case
              proof(cases "get_portid_by_name s sn \<noteq> None \<and> get_portid_by_name s dn \<noteq> None 
                          \<and> has_msg_inportqueuing s (the (get_portid_by_name s sn))")
                let ?sps = "the (get_portid_by_name s sn)"
                let ?spt = "the (get_portid_by_name t sn)"
                let ?dps = "the (get_portid_by_name s dn)"
                let ?dpt = "the (get_portid_by_name t dn)"
                let ?s1 = "fst (remove_msg_from_queuingport s ?sps)"
                let ?t1 = "fst (remove_msg_from_queuingport t ?spt)"
                let ?ms = "snd (remove_msg_from_queuingport s ?sps)"
                let ?mt = "snd (remove_msg_from_queuingport t ?spt)"
                let ?s2 = "replace_msg2queuing_port ?s1 ?dps (the ?ms)"
                let ?t2 = "replace_msg2queuing_port ?t1 ?dpt (the ?mt)"
                let ?s3 = "insert_msg2queuing_port ?s1 ?dps (the ?ms)"
                let ?t3 = "insert_msg2queuing_port ?t1 ?dpt (the ?mt)"
                assume b0:"get_portid_by_name s sn \<noteq> None \<and> get_portid_by_name s dn \<noteq> None 
                          \<and> has_msg_inportqueuing s (the (get_portid_by_name s sn))"
                with a1 have b1:"get_portid_by_name t sn \<noteq> None \<and> get_portid_by_name t dn \<noteq> None 
                          \<and> has_msg_inportqueuing t (the (get_portid_by_name t sn))" 
                          by (metis get_portid_by_name_def has_msg_inportqueuing_def)

                from a1 have b2:"?sps = ?spt" unfolding get_portid_by_name_def is_port_name_def by simp
                from a1 have b3:"?dps = ?dpt" unfolding get_portid_by_name_def is_port_name_def by simp
                with b2 a1 have b4:"comm ?s1 = comm ?t1" 
                  apply(clarsimp simp:remove_msg_from_queuingport_def)
                  apply(case_tac "ports (comm t) ?spt")
                  apply(simp)
                  apply(case_tac "a")
                  apply (smt Communication_State.surjective Communication_State.update_convs(1) 
                    Port_Type.simps(5) State.select_convs(3) State.surjective State.update_convs(3) 
                    fstI option.simps(5))
                  by simp

                with b2 a1 have b5:"part_ports ?s1 = part_ports ?t1" 
                  apply(clarsimp simp:remove_msg_from_queuingport_def)
                  apply(case_tac "ports (comm t) ?spt")
                  apply(simp)
                  apply(case_tac "a")
                  apply (smt Port_Type.simps(5) State.select_convs(4) State.surjective 
                    State.update_convs(3) fstI option.simps(5))
                  by simp

                from a1 b2 b3 have b6:"?ms = ?mt" 
                apply(clarsimp simp:remove_msg_from_queuingport_def)
                  apply(case_tac "ports (comm t) ?spt")
                  apply(simp)
                  apply(case_tac "a")
                  apply (metis (no_types, lifting) Port_Type.simps(5) option.simps(5) prod.collapse prod.inject)
                  by simp

                from b4 b5 a1 have b7:"comm ?s2 = comm ?t2 \<and> part_ports ?s2 = part_ports ?t2" 
                  unfolding replace_msg2queuing_port_def by simp
 
                from b3 b4 b5 b6 a1 have b8:"comm ?s3 = comm ?t3" 
                  apply(clarsimp simp:insert_msg2queuing_port_def)
                  apply(case_tac "ports (comm ?t1) ?dpt")
                  apply(simp)
                  apply(case_tac "a")
                  apply (metis Int_absorb a2 empty_iff option.distinct(1) port_consistent_def 
                    port_partition remove_msg_from_queuingport_presv_port_cons)
                  by simp

                from b3 b4 b5 b6 a1 have b9:"part_ports ?s3 = part_ports ?t3" 
                  apply(clarsimp simp:insert_msg2queuing_port_def)
                  apply(case_tac "ports (comm ?t1) ?dpt")
                  apply(simp)
                  apply(case_tac "a")
                  apply (metis Int_absorb a2 empty_iff option.distinct(1) port_consistent_def 
                    port_partition remove_msg_from_queuingport_presv_port_cons)
                  by simp

                show ?thesis 
                  proof(cases "is_full_portqueuing sysconf ?s1 ?dps")
                    assume c0:"is_full_portqueuing sysconf ?s1 ?dps"
                    with b3 b4 have c1:"is_full_portqueuing sysconf ?t1 ?dpt" 
                      unfolding is_full_portqueuing_def Let_def get_port_conf_byid_def  
                      get_max_bufsize_of_port_def get_current_bufsize_port_def get_port_byid_def by auto 
                    from p3 b0 c0 have c2:"s' = ?s2" 
                      by (smt Channel_Queuing.prems(1) transf_queuing_msg_maylost.simps(1)) 
                    from p4 b1 c1 have c3:"t' = ?t2" 
                      by (smt Channel_Queuing.prems(2) transf_queuing_msg_maylost.simps(1)) 
                    
                    with b7 c2 show ?thesis by simp
                  next
                    assume c0:"\<not>is_full_portqueuing sysconf ?s1 ?dps"
                    with b3 b4 have c1:"\<not>is_full_portqueuing sysconf ?t1 ?dpt" 
                      unfolding is_full_portqueuing_def Let_def get_port_conf_byid_def  
                      get_max_bufsize_of_port_def get_current_bufsize_port_def get_port_byid_def by auto 
                    from p3 b0 c0 have c2:"s' = ?s3" 
                      by (smt Channel_Queuing.prems(1) transf_queuing_msg_maylost.simps(1))
                    from p4 b1 c1 have c3:"t' = ?t3" 
                      by (smt Channel_Queuing.prems(2) transf_queuing_msg_maylost.simps(1)) 
                    
                    with b8 b9 c2 show ?thesis by simp
                  qed
              next
                assume b0:"\<not>(get_portid_by_name s sn \<noteq> None \<and> get_portid_by_name s dn \<noteq> None 
                          \<and> has_msg_inportqueuing s (the (get_portid_by_name s sn)))"
                with a1 have b1:"\<not>(get_portid_by_name t sn \<noteq> None \<and> get_portid_by_name t dn \<noteq> None 
                          \<and> has_msg_inportqueuing t (the (get_portid_by_name t sn)))" 
                          by (metis get_portid_by_name_def has_msg_inportqueuing_def)
                with p3 b0 have b2:"s' = s" unfolding transf_queuing_msg_maylost_def 
                  Let_def Channel_Queuing.prems(1) by auto 
                with p4 b1 have b3:"t' = t" unfolding transf_queuing_msg_maylost_def 
                  Let_def Channel_Queuing.prems(2) by auto 
                with a1 b2 show ?thesis by simp
              qed
          next
            case (Channel_Sampling x1 x2 x3)
            show ?case by (simp add: Channel_Sampling.prems(1) Channel_Sampling.prems(2) a1) 
          qed
      }
      qed

  lemma trans_que_msg_mlost_presrv_wk_stp_cons:
    assumes p1:"is_a_transmitter sysconf (current s)"
      and   p2:"reachable0 s \<and> reachable0 t"
      and   p3:"s \<sim> d \<sim> t"
      and   p4:"s \<sim> (scheduler sysconf) \<sim> t"
      and   p5:"(current s) \<leadsto> d"
      and   p6:"s \<sim> (current s) \<sim> t"
      and   p7:"s' = transf_queuing_msg_maylost sysconf s c"
      and   p8:"t' = transf_queuing_msg_maylost sysconf t c"
    shows   "s' \<sim> d \<sim> t'"
  proof(cases "is_a_scheduler sysconf d")
    assume a0:"is_a_scheduler sysconf d"
    show ?thesis using a0 no_intf_sched_help p1 p5 sch_not_trans by auto
  next
    assume a1:"\<not> is_a_scheduler sysconf d"
    have a2:"comm s' = comm t' \<and> part_ports s' = part_ports t'"
      using  p1 p6  trans_que_msg_mlost_presrv_comm_part_ports[OF p2 _ p4 p7 p8]
      by (metis is_a_transmitter_def) 
    show ?thesis
    proof(cases "is_a_partition sysconf d")
      assume b0:"is_a_partition sysconf d"
      show ?thesis 
      proof -
        have d0:"vpeq_part s' d t'"
        proof -
          have e1:"partitions s' d = partitions t' d"
            using a1 b0  p1 p3 p4 p7 p8 
            part_imp_not_tras sched_current_lemma trans_que_msg_mlost_notchg_partstate
            by force                 
          from a2 have e2:"vpeq_part_comm s' d t'"
            unfolding vpeq_part_comm_def Let_def get_ports_of_partition_def is_a_queuingport_def 
            is_dest_port_def get_port_buf_size_def get_current_bufsize_port_def get_port_byid_def by simp            
          with e1 show ?thesis by auto 
        qed
        then show ?thesis  using a1 b0 
          using trans_imp_not_part by fastforce
      qed
    next
      assume b1:"\<not> is_a_partition sysconf d"
      show ?thesis
      proof(cases "is_a_transmitter sysconf d")
        assume c0:"is_a_transmitter sysconf d"
        show ?thesis
        proof -
        {
          have "vpeq_transmitter s' d t'" unfolding vpeq_transmitter_def
          proof-
            from p2 p3 p4 p7 p8
            show "comm s' = comm t' \<and> part_ports s' = part_ports t' "
              using c0 trans_que_msg_mlost_presrv_comm_part_ports by force 
          qed
        }
        then show ?thesis using a1 b1 by auto
        qed
      next
        assume c1:"\<not> is_a_transmitter sysconf d"
        show ?thesis using a1 b1 c1 by auto
      qed
    qed
  qed

  lemma trans_que_msg_mlost_presrv_wk_stp_cons_e: "weak_step_consistent_e (sys (Transfer_Queuing_Message c))"
    using trans_que_msg_mlost_presrv_wk_stp_cons weak_step_consistent_e_def exec_event_def mem_Collect_eq
      non_interference1_def non_interference_def singletonD sched_vpeq same_part_mode
        by (smt Event.case(2) System_Event.case(3) domain_of_event.simps(2) event_enabled.simps(2) 
            option.sel prod.simps(2) is_a_transmitter_def vpeq1_def vpeq_sched_def)

subsubsection{*proving the "weakly step consistent" property*}
  theorem weak_step_consistent:weak_step_consistent
    proof -
      {
        fix e
        have "weak_step_consistent_e e"
          apply(induct e)
          using crt_smpl_port_presrv_wk_stp_cons_e wrt_smpl_msg_presrv_wk_stp_cons_e 
                  read_smpl_msg_presrv_wk_stp_cons_e get_smpl_pid_presrv_wk_stp_cons_e 
                  get_smpl_psts_presrv_wk_stp_cons_e crt_que_port_presrv_wk_stp_cons_e 
                  snd_que_msg_lst_presrv_wk_stp_cons_e rec_que_msg_presrv_wk_stp_cons_e 
                  get_que_pid_presrv_wk_stp_cons_e get_que_psts_presrv_wk_stp_cons_e 
                  clr_que_port_presrv_wk_stp_cons_e set_part_mode_presrv_wk_stp_cons_e 
                  get_part_status_presrv_wk_stp_cons_e
          apply (rule Hypercall.induct)
          using schedule_presrv_wk_stp_cons_e trans_smpl_msg_presrv_wk_stp_cons_e
                trans_que_msg_mlost_presrv_wk_stp_cons_e 
          by (rule System_Event.induct)
      }
      then show ?thesis using weak_step_consistent_all_evt by blast
    qed

subsection{* Information flow security of top-level specification *}

  theorem noninfluence_sat: noninfluence
    using local_respect uc_eq_noninf weak_step_consistent weak_with_step_cons by blast

  theorem noninfluence_gen_sat: noninfluence_gen
    using noninf_eq_noninf_gen noninfluence_sat by blast 

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
