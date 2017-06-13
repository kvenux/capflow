theory CapFlow_v2
imports Dynamic_model_v1
begin

subsection {* Definitions *}

type_synonym max_buffer_size = nat
type_synonym buffer_size = nat
typedecl Message
type_synonym compartment_id = nat

type_synonym domain_id = nat
type_synonym domain_name = string
type_synonym port_name = string
type_synonym port_id = nat
datatype port_direction = SOURCE | DESTINATION

datatype
  right = TAINT
          |GRANT

record cap = 
  target :: compartment_id
  rights :: "right set"

datatype Port_Conf = Queuing port_id port_name max_buffer_size port_direction "Message set"

record Communication_Config = 
  ports_conf :: "Port_Conf set"

datatype Domain_Conf = DomainConf domain_id domain_name "cap set" "port_name set"
                           
type_synonym Domains = "domain_id \<rightharpoonup> Domain_Conf"

record Sys_Config = 
  domain_conf :: Domains
  commconf :: Communication_Config

subsubsection {* System state *}

type_synonym Ports = "port_id \<rightharpoonup> Port_Conf"

record Communication_State = 
          ports :: Ports

record State = 
  domains :: Domains
  comm :: Communication_State
  domain_ports :: "port_id \<rightharpoonup> domain_id"
  next_comp_id :: compartment_id

subsubsection {* Utility Functions used for Event Specification *} 

primrec get_domain_name_by_type :: "Domain_Conf \<Rightarrow> domain_name"
  where "get_domain_name_by_type (DomainConf _ dn _ _) = dn"

primrec get_domain_id_by_type :: "Domain_Conf \<Rightarrow> domain_id"
  where "get_domain_id_by_type (DomainConf did _ _ _) = did"

definition is_source_port :: "State \<Rightarrow> port_id \<Rightarrow> bool"
  where "is_source_port s pid \<equiv> 
          case ((ports (comm s)) pid) of 
              Some (Queuing _ _ _ SOURCE _) \<Rightarrow> True |
              _ \<Rightarrow> False"

definition is_dest_port :: "State \<Rightarrow> port_id \<Rightarrow> bool"
  where "is_dest_port s pid \<equiv> 
            case ((ports (comm s)) pid) of 
                Some (Queuing _ _ _ DESTINATION _) \<Rightarrow> True |
                _ \<Rightarrow> False"

definition is_a_port_of_domain :: "State \<Rightarrow> port_id \<Rightarrow> domain_id \<Rightarrow> bool"
  where "is_a_port_of_domain s port part \<equiv> (domain_ports s) port = Some part"

definition is_queuingport_name :: "Port_Conf \<Rightarrow> port_name \<Rightarrow> bool" 
  where
  "is_queuingport_name p n 
     \<equiv> case p of 
         (Queuing _ name _ _ _) \<Rightarrow> name = n
  "

definition is_port_name :: "Port_Conf \<Rightarrow> port_name \<Rightarrow> bool" 
  where
  "is_port_name p n 
     \<equiv> case p of 
         (Queuing _ name _ _ _) \<Rightarrow> name = n
  "

definition get_queuingport_conf :: "Sys_Config \<Rightarrow> port_name \<Rightarrow> Port_Conf option"
  where "get_queuingport_conf sc pname \<equiv> 
              (if (\<exists>p. p \<in> ports_conf (commconf sc)\<and> is_queuingport_name p pname)  
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
                    | None \<Rightarrow> None"

definition get_portname_by_type :: "Port_Conf \<Rightarrow> port_name"
  where "get_portname_by_type pt \<equiv> case pt of (Queuing _ name _ _ _) \<Rightarrow> name
                                           "

definition is_a_queuingport :: "State \<Rightarrow> port_id \<Rightarrow> bool" 
  where "is_a_queuingport s pid \<equiv> case ((ports (comm s)) pid) of 
                                        Some (Queuing _ _ _ _ _) \<Rightarrow> True | 
                                        _ \<Rightarrow> False"

definition get_portid_in_type :: "Port_Conf \<Rightarrow> port_id"
  where "get_portid_in_type pt \<equiv> case pt of (Queuing pid _ _ _ _) \<Rightarrow> pid
                                           "
                                                                      
primrec get_domain_cfg_ports :: "Domain_Conf \<Rightarrow> port_name set"
  where "get_domain_cfg_ports (DomainConf _ _ _ pset) = pset "

definition get_domain_cfg_ports_byid :: "Sys_Config \<Rightarrow> domain_id \<Rightarrow> port_name set"
  where "get_domain_cfg_ports_byid sc p \<equiv> 
              if (domain_conf sc) p = None 
                then {} 
              else get_domain_cfg_ports (the ((domain_conf sc) p) )"

primrec get_domain_cfg_cap_set :: "Domain_Conf \<Rightarrow> cap set"
  where "get_domain_cfg_cap_set (DomainConf _ _ cset _) = cset "

definition get_domain_cfg_cap_set_byid :: "State \<Rightarrow> domain_id \<Rightarrow> cap set"
  where "get_domain_cfg_cap_set_byid s p \<equiv> 
              if (domains s) p = None 
                then {} 
              else get_domain_cfg_cap_set (the ((domains s) p) )"


definition get_ports_of_domain :: "State \<Rightarrow> domain_id \<Rightarrow> port_id set"
  where "get_ports_of_domain s p = {x. (domain_ports s) x = Some p}"

primrec get_msgs_from_queuingport :: "Port_Conf \<Rightarrow> (Message set) option"
  where "get_msgs_from_queuingport (Queuing _ _ _ _ msgs) = Some msgs"

definition get_port_byid :: "State \<Rightarrow> port_id \<Rightarrow> Port_Conf option"
  where "get_port_byid s pid \<equiv>  ports (comm s) pid"

definition get_the_msgs_of_queuingport :: "State \<Rightarrow> port_id \<Rightarrow> (Message set) option"
  where "get_the_msgs_of_queuingport s pid \<equiv>
            let ps = get_port_byid s pid in
                 if ps = None then None else get_msgs_from_queuingport (the ps)"
   
definition get_port_conf_byid :: "Sys_Config \<Rightarrow> State \<Rightarrow> port_id \<Rightarrow> Port_Conf option"
  where "get_port_conf_byid sc s pid \<equiv> ports (comm s) pid"                                                      

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

definition clear_msg_queuingport :: "Port_Conf \<Rightarrow> Port_Conf"
  where "clear_msg_queuingport pt \<equiv> (case pt of (Queuing spid name maxs d _) \<Rightarrow> (Queuing spid name maxs d {}))"

definition is_a_domain :: "Sys_Config \<Rightarrow> domain_id \<Rightarrow> bool"
  where "is_a_domain sc nid \<equiv> (domain_conf sc) nid \<noteq> None"


primrec get_max_bufsize_of_port :: "Port_Conf \<Rightarrow> max_buffer_size"
  where "get_max_bufsize_of_port (Queuing _ _ n _ _) = n" 

primrec get_current_bufsize_port :: "Port_Conf \<Rightarrow> buffer_size"
  where "get_current_bufsize_port (Queuing _ _ _ _ ms) = card ms" 

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

definition has_msg_inportqueuing :: "State \<Rightarrow> port_id \<Rightarrow> bool"
  where "has_msg_inportqueuing s pid \<equiv> 
            case ((ports (comm s)) pid) of 
                Some (Queuing _ _ _ _ msgs)
                  \<Rightarrow> card msgs \<noteq> 0
                | _ \<Rightarrow> False"

definition get_partconf_byid :: "Sys_Config \<Rightarrow> domain_id \<Rightarrow> Domain_Conf option"
  where "get_partconf_byid sc pid \<equiv> (domain_conf sc) pid"

definition get_t_set :: "State \<Rightarrow> domain_id \<Rightarrow> cap set " where
  "get_t_set s d_id \<equiv>
          
                  let
                    cap_set = (get_domain_cfg_cap_set_byid s d_id)
                  in
                    ({cap. cap \<in> cap_set \<and> TAINT \<in> rights cap})"

definition domain_port_interf :: "State \<Rightarrow> domain_id \<Rightarrow> port_id \<Rightarrow> bool"
  where "domain_port_interf s did pid \<equiv>
        let
          did_dst = the ((domain_ports s) pid)
        in
          if(get_t_set s did \<subseteq> get_t_set s did_dst)
            then
              True
          else
            False"

subsubsection{* Event specification *}

definition create_new_tag :: "State \<Rightarrow> domain_id \<Rightarrow> (State \<times> cap option)" where
  "create_new_tag s did \<equiv> 
        case ((domains s) did) of
          Some (DomainConf did dname cset pn_set)
            \<Rightarrow> (
                let cap_set = get_domain_cfg_cap_set_byid s did ;
                    new_add_cap =  \<lparr> target = next_comp_id s,
                               rights = {TAINT,GRANT} \<rparr>;
                    new_cap_set = insert new_add_cap cap_set;
                    doms = domains s
                in
                  (s\<lparr>domains := doms(did := Some (DomainConf did dname (insert new_add_cap cset) pn_set)) 
                            \<rparr>, Some new_add_cap)
                )
          | _ \<Rightarrow> (s, None)"

definition grant_cap :: "State \<Rightarrow> domain_id \<Rightarrow> domain_id \<Rightarrow> cap \<Rightarrow> State" where
  "grant_cap s src_id dst_id cap \<equiv> 
        if (cap \<notin> get_domain_cfg_cap_set_byid s src_id)
          then
            s
        else                       
          case ((domains s) dst_id) of
            Some (DomainConf dst_id dname cset pn_set)
            \<Rightarrow> (
                let 
                  doms = domains s;
                  newly_granted_cap =  \<lparr> target = target cap,
                             rights = {TAINT} \<rparr>
                in
                  s\<lparr>domains := doms(dst_id := Some (DomainConf dst_id dname (insert newly_granted_cap cset) pn_set)) 
                       \<rparr>)
            | _ \<Rightarrow> s"        
                          
definition get_caps :: "State \<Rightarrow> domain_id \<Rightarrow> (State \<times> (cap set) option) " where
  "get_caps s did \<equiv> 
                if (domains s) did = None 
                  then (s, None) 
                else
                  (s, Some (get_domain_cfg_cap_set_byid s did))"

definition get_taint_cap_set :: "State \<Rightarrow> domain_id \<Rightarrow> (State \<times>  (cap set) option) " where
   "get_taint_cap_set s did \<equiv> 
                if (domains s) did = None 
                  then (s, None) 
                else
                  let
                    cap_set = (get_domain_cfg_cap_set_byid s did)
                  in
                    (s, Some ({cap. cap \<in> cap_set \<and> TAINT \<in> rights cap}))"

definition create_queuing_port :: "Sys_Config \<Rightarrow> State \<Rightarrow> domain_id \<Rightarrow> port_name \<Rightarrow> (State \<times> port_id option)" where
  "create_queuing_port sc s did p \<equiv>          
            if (get_queuingport_conf sc p = None
                 \<or> get_portid_by_name s p \<noteq> None
                \<or> p \<notin> get_domain_cfg_ports_byid sc (did))
            then (s, None)            
            else                         
              let cs = comm s; 
                  pts = ports cs; 
                  domainpts = domain_ports s;
                  newid = get_portid_in_type (the (get_queuingport_conf sc p)) 
              in
              (s\<lparr>comm :=
                cs\<lparr> ports := pts(newid := get_queuingport_conf sc p)\<rparr>,
                 domain_ports := domainpts (newid := Some did)
               \<rparr>, Some newid)"   

definition send_queuing_message_maylost :: "Sys_Config \<Rightarrow> State \<Rightarrow> domain_id \<Rightarrow> port_id \<Rightarrow> Message \<Rightarrow> (State \<times> bool)" where
  "send_queuing_message_maylost sc s did p m \<equiv> 
              (if(\<not> is_a_queuingport s p
                \<or> \<not> is_source_port s p
                \<or> \<not> domain_port_interf s did p)
              then (s, False)
              else if is_full_portqueuing sc s p then
                (replace_msg2queuing_port s p m, True)
              else
                (insert_msg2queuing_port s p m, True))"

definition receive_queuing_message :: "State \<Rightarrow> domain_id \<Rightarrow> port_id \<Rightarrow> (State \<times> Message option)" where
  "receive_queuing_message s did pid \<equiv> 
              (if (\<not> is_a_queuingport s pid 
                \<or> \<not> is_a_port_of_domain s pid (did)
                \<or> \<not> is_dest_port s pid 
                \<or> is_empty_portqueuing s pid)
              then (s, None)
              else remove_msg_from_queuingport s pid
              )"

definition get_queuing_port_id :: "Sys_Config \<Rightarrow> State \<Rightarrow> domain_id \<Rightarrow> port_name \<Rightarrow> (State \<times> port_id option)" where
  "get_queuing_port_id sc s did pname \<equiv> 
          (if (pname \<notin> get_domain_cfg_ports_byid sc (did))
          then (s, None) 
          else (s, get_portid_by_name s pname))"

definition clear_queuing_port :: "State \<Rightarrow> domain_id \<Rightarrow> port_id \<Rightarrow> State" where
  "clear_queuing_port s did pid \<equiv> 
          (if (\<not> is_a_queuingport s pid
                \<or> \<not> is_a_port_of_domain s pid (did)
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


definition system_init :: "Sys_Config \<Rightarrow> State"
  where "system_init sc \<equiv> \<lparr>
                            domains=(domain_conf sc),                                  
                            comm = \<lparr>ports=(\<lambda> x. None)\<rparr>,
                            domain_ports = (\<lambda> x. None),
                            next_comp_id = 0
                           \<rparr>"  


subsubsection{* Instantiation and Its Proofs of Security Model  *}

consts sysconf :: "Sys_Config" 
definition sys_config_witness :: Sys_Config 
where 
"sys_config_witness \<equiv> \<lparr>
                        domain_conf = Map.empty, 
                        commconf = \<lparr> ports_conf = {}\<rparr>                       
                        \<rparr>" 

specification (sysconf)
  trans_not_part : "domain_conf sysconf = x \<Longrightarrow> domain_conf sysconf = x"
  port_domain:"\<forall>p1 p2. get_domain_cfg_ports_byid sysconf p1 \<inter> get_domain_cfg_ports_byid sysconf p2 = {}"
    apply (intro exI[of _ "sys_config_witness"] allI impI, simp) 
    by (simp add: get_domain_cfg_ports_byid_def sys_config_witness_def)

(*
definition domain_id_is_valid :: "State \<Rightarrow> domain_id \<Rightarrow> bool" where
  "domain_id_is_valid s domain_id  \<equiv>
          (if (\<exists>d. d \<in> (domains s) \<and> id_of_domain d = domain_id )
          then True
          else False)
          "


definition get_domain :: "State \<Rightarrow> domain_id \<Rightarrow> domain option" where
  "get_domain s domain_id  \<equiv>
          (if (\<exists>d. d \<in> (domains s) \<and> id_of_domain d = domain_id )
          then Some (SOME d. d \<in> (domains s) \<and> id_of_domain d = domain_id)
          else None)
          "

definition get_domain2 :: "State \<Rightarrow> domain_id \<Rightarrow> (State \<times> domain option)" where
  "get_domain2 s domain_id  \<equiv>
          (if (\<exists>d. d \<in> (domains s) \<and> id_of_domain d = domain_id )
          then (s, get_domain s domain_id)
          else (s, None)               
          )"

definition create_tag_add_new_caps_to_domain :: "domain \<Rightarrow> cap set \<Rightarrow> domain" where
  "create_tag_add_new_caps_to_domain d cs \<equiv> 
          \<lparr> id_of_domain = id_of_domain d,
            cap_config = cs \<union> (cap_config d)\<rparr>"

definition create_tag_add_new_caps_to_domain_1 :: "State \<Rightarrow> domain_id \<Rightarrow> cap set \<Rightarrow> domain" where
  "create_tag_add_new_caps_to_domain_1 s d_id cs \<equiv> 
          let d = the (get_domain s d_id)
          in
          \<lparr> id_of_domain = id_of_domain d,
            cap_config = cs \<union> (cap_config d)\<rparr>"

definition create_tag_state_trans :: "State \<Rightarrow> domain_id \<Rightarrow> State" where
  "create_tag_state_trans s d_id \<equiv> 
          let rest_domains = {v. v\<in>domains s \<and> \<not> (id_of_domain v = d_id) };
              new_add_cap =  \<lparr> target = next_comp_id s,
                             rights = {TAINT} \<rparr>;
              new_domain = create_tag_add_new_caps_to_domain_1 s d_id {new_add_cap}
          in
           \<lparr> domains = insert new_domain rest_domains,
             next_comp_id = next_comp_id s + 1 \<rparr>"

definition create_tag :: "State \<Rightarrow> domain_id \<Rightarrow> (State \<times> cap option) " where
  "create_tag s d_id \<equiv>
          if( domain_id_is_valid s d_id )
          then
            let rest_domains = {v. v\<in>domains s \<and> \<not> (id_of_domain v = d_id) };
                new_add_cap =  \<lparr> target = next_comp_id s,
                               rights = {TAINT,GRANT} \<rparr>;
                new_domain = create_tag_add_new_caps_to_domain_1 s d_id {new_add_cap}
            in (\<lparr> domains = insert new_domain rest_domains,
                  next_comp_id = next_comp_id s + 1 \<rparr> , Some new_add_cap)
          else
            (s, None)
          "

definition get_caps0 :: "State \<Rightarrow> domain_id \<Rightarrow> (cap set) option " where
"get_caps0 s domain_id \<equiv>
          (if (\<exists>d. d \<in> (domains s) \<and> id_of_domain d = domain_id )
          then Some (SOME cap. \<exists>d. d \<in> (domains s) \<and> id_of_domain d = domain_id \<and> cap = cap_config d)
          else None
          )"

definition get_caps :: "State \<Rightarrow> domain_id \<Rightarrow> (State \<times> (cap set) option) " where
  "get_caps s domain_id \<equiv>
          (if (\<exists>d. d \<in> (domains s) \<and> id_of_domain d = domain_id )
          then (s, Some (SOME cap. \<exists>d. d \<in> (domains s) \<and> id_of_domain d = domain_id \<and> cap = cap_config d))
          else (s, None)                             
          )"

definition get_taint_cap_set0 :: "State \<Rightarrow> domain_id \<Rightarrow> (cap set) option " where
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

definition get_taint_cap_set :: "State \<Rightarrow> domain_id \<Rightarrow> (State \<times>  (cap set) option) " where
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

definition grant_cap_is_valid :: "State \<Rightarrow> domain_id \<Rightarrow> domain_id \<Rightarrow> cap \<Rightarrow> bool" where 
  "grant_cap_is_valid s d_id dst_id cap \<equiv> True"

definition grant_cap :: "State \<Rightarrow> domain_id \<Rightarrow> domain_id \<Rightarrow> cap \<Rightarrow> State" where
  "grant_cap s d_id dst_id cap \<equiv> 
          let rest_domains = {v. v\<in>domains s \<and> \<not> (id_of_domain v = d_id) };
              newly_granted_cap =  \<lparr> target = target cap,
                             rights = {TAINT} \<rparr>;
              new_domain = create_tag_add_new_caps_to_domain_1 s d_id {newly_granted_cap}
          in
           \<lparr> domains = insert new_domain rest_domains,
             next_comp_id = next_comp_id s \<rparr>
            "

definition send_message :: "State \<Rightarrow> domain_id \<Rightarrow> domain_id \<Rightarrow> Message \<Rightarrow> State"
  where
  "send_message s src_id dst_id m \<equiv>
        s
        "
*)

datatype Event = Create_Cap domain_id
                   | Grant_Cap domain_id domain_id cap
                   | Get_Taint_Cap_Set domain_id
                   | Get_Caps domain_id
                   | Create_Queuing_Port domain_id port_name
                   | Send_Queuing_Message domain_id port_id Message
                   | Receive_Queuing_Message domain_id port_id
                   | Get_Queuing_Portid domain_id port_name
                   | Clear_Queuing_Port domain_id port_id

definition exec_event :: "State \<Rightarrow> Event \<Rightarrow> State" where
  "exec_event s e  \<equiv>
    case e of  Create_Cap d_id \<Rightarrow> fst (create_new_tag s d_id)
             | Grant_Cap d_id dst_id cap \<Rightarrow> grant_cap  s d_id dst_id cap
             | Get_Taint_Cap_Set d_id \<Rightarrow> fst (get_taint_cap_set s d_id)
             | Get_Caps d_id \<Rightarrow> fst (get_caps s d_id)
             | Create_Queuing_Port domain_id port_name \<Rightarrow>fst (create_queuing_port sysconf s domain_id port_name)
             | Send_Queuing_Message domain_id port_id msg \<Rightarrow> fst (send_queuing_message_maylost sysconf s domain_id port_id msg)
             | Receive_Queuing_Message domain_id port_id \<Rightarrow> fst (receive_queuing_message s domain_id port_id)
             | Get_Queuing_Portid domain_id port_name \<Rightarrow> fst (get_queuing_port_id sysconf s domain_id port_name )
             | Clear_Queuing_Port domain_id port_id \<Rightarrow> clear_queuing_port s domain_id port_id
               "

definition domain_of_event :: "Event \<Rightarrow> domain_id option"
  where
    "domain_of_event e \<equiv> 
       case e of  Create_Cap d_id \<Rightarrow> Some d_id
                | Grant_Cap d_id dst_id cap \<Rightarrow> Some d_id
                | Get_Taint_Cap_Set d_id \<Rightarrow> Some d_id
                | Get_Caps d_id \<Rightarrow> Some d_id
                | Create_Queuing_Port d_id port_name \<Rightarrow> Some d_id
                | Send_Queuing_Message d_id port_name msg \<Rightarrow>  Some d_id
                | Receive_Queuing_Message d_id port_id \<Rightarrow>  Some d_id
                | Get_Queuing_Portid d_id port_name \<Rightarrow>  Some d_id
                | Clear_Queuing_Port d_id port_id \<Rightarrow>  Some d_id
                "

definition grant_dest_of_event :: "Event \<Rightarrow> domain_id option"
 where
    "grant_dest_of_event e \<equiv> 
       case e of  Create_Cap d_id \<Rightarrow> Some d_id
                | Grant_Cap d_id dst_id cap \<Rightarrow> Some dst_id
                | Get_Taint_Cap_Set d_id \<Rightarrow> None
                | Get_Caps d_id \<Rightarrow> None
                | Create_Queuing_Port d_id port_name \<Rightarrow> None
                | Send_Queuing_Message d_id port_name msg \<Rightarrow> None
                | Receive_Queuing_Message d_id port_id \<Rightarrow> None
                | Get_Queuing_Portid d_id port_name \<Rightarrow> None
                | Clear_Queuing_Port d_id port_id \<Rightarrow> None
                 "                                            
definition is_execute1 :: "Event \<Rightarrow> bool"
  where
    "is_execute1 e \<equiv> 
          case e of   Create_Cap d_id \<Rightarrow> False
                | Grant_Cap d_id dst_id cap \<Rightarrow> False
                | Get_Taint_Cap_Set d_id \<Rightarrow> True
                | Get_Caps d_id \<Rightarrow> True
                | Create_Queuing_Port d_id port_name \<Rightarrow> True
                | Send_Queuing_Message d_id port_name msg \<Rightarrow> True
                | Receive_Queuing_Message d_id port_id \<Rightarrow> True
                | Get_Queuing_Portid d_id port_name \<Rightarrow> True
                | Clear_Queuing_Port d_id port_id \<Rightarrow> True
                 "

definition is_grant1 :: "Event \<Rightarrow> bool"
  where
    "is_grant1 e \<equiv> \<not>is_execute1 e"

definition vpeq_domain_com :: "State \<Rightarrow> domain_id \<Rightarrow> State \<Rightarrow> bool"
  where "vpeq_domain_com s d t\<equiv> 
                (let ps1 = get_ports_of_domain s d;
                ps2 = get_ports_of_domain t d in
                  (ps1 = ps2) \<and> 
                  (\<forall>p. p\<in>ps1 \<longrightarrow> 
                   (is_a_queuingport s p = is_a_queuingport t p) \<and>
                   (is_dest_port s p = is_dest_port t p) \<and>
                   (if is_dest_port s p then
                      get_port_buf_size s p = get_port_buf_size t p
                    else True)
                  )
          )"

definition vpeq1 :: "State \<Rightarrow> domain_id \<Rightarrow> State \<Rightarrow> bool" ("(_ \<sim> _ \<sim> _)") 
  where
    "vpeq1 s d t \<equiv> 
        let
          d1 = (domains s) d;
          d2 = (domains t) d;
          ps1 = get_ports_of_domain s d;
          ps2 = get_ports_of_domain t d
        in
          if(d1 = d2 \<and> ps1 = ps2)
          then
            True
          else
            False
          "

declare vpeq_domain_com_def [cong] and vpeq1_def [cong]

consts s0t :: State
definition s0t_witness :: State
  where "s0t_witness \<equiv> system_init sysconf"
specification (s0t) 
  s0t_init: "s0t = system_init sysconf"
  by simp

lemma vpeq1_transitive_lemma : "\<forall> s t r d. (vpeq1 s d t) \<and> (vpeq1 t d r) \<longrightarrow> (vpeq1 s d r)"
  using vpeq1_def by auto

lemma vpeq1_symmetric_lemma : "\<forall> s t d. (vpeq1 s d t) \<longrightarrow> (vpeq1 t d s)"
  using vpeq1_def by auto

lemma vpeq1_reflexive_lemma : "\<forall> s d. (vpeq1 s d s)"
  using vpeq1_def by auto

lemma execute_exclusive1 :  "\<forall>a. is_execute1 a  \<longleftrightarrow> \<not>(is_grant1 a)"
  using is_grant1_def by auto

lemma grant_exclusive1: "\<forall>a. is_grant1 a   \<longleftrightarrow> \<not>(is_execute1 a)"
  using is_grant1_def by auto

lemma vpeq1_domain_eq_lemma : "\<forall>s t d. vpeq1 s d t \<longrightarrow> get_domain_cfg_cap_set_byid s d = get_domain_cfg_cap_set_byid t d"
  using vpeq1_def get_domain_cfg_cap_set_byid_def  by auto

lemma vpeq1_domain_eq_lemma1 : "\<forall>s t d. vpeq1 s d t \<longrightarrow> (domains s) d = (domains t) d"
  using vpeq1_def by auto

lemma taint_set_respect_lemma1: "\<forall>s t d. vpeq1 s d t \<longrightarrow> get_t_set s d = get_t_set t d"
  using get_t_set_def vpeq1_domain_eq_lemma by presburger

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
        case (Create_Queuing_Port x1a x2 ) show ?case
          apply (induct x1a)
          by (simp add: exec_event_def) +
        case (Send_Queuing_Message x1a x2 x3a ) show ?case
          apply (induct x1a)
          by (simp add: exec_event_def) +
        case (Receive_Queuing_Message x1a x2 ) show ?case
          apply (induct x1a)
          by (simp add: exec_event_def) +
        case (Get_Queuing_Portid x1a x2 ) show ?case
          apply (induct x1a)
          by (simp add: exec_event_def) +
        case (Clear_Queuing_Port x1a x2 ) show ?case
          apply (induct x1a)
          by (simp add: exec_event_def) +
      qed
    }
  then show ?thesis by auto
  qed

declare  Let_def [cong]

interpretation SM_enabled 
    s0t is_execute1 is_grant1 exec_event domain_of_event grant_dest_of_event get_t_set vpeq1
    using vpeq1_transitive_lemma vpeq1_symmetric_lemma vpeq1_reflexive_lemma
          grant_exclusive1 execute_exclusive1 taint_set_respect_lemma1 reachable_top
          SM.intro[of vpeq1 is_execute1 is_grant1 get_t_set]
          SM_enabled_axioms.intro[of s0t exec_event]
          SM_enabled.intro[of is_execute1 is_grant1 get_t_set vpeq1 s0t exec_event] by blast

subsection{* Concrete unwinding condition of "local respect" *}

  lemma get_caps_lcl_resp:
  assumes p0:"reachable0 s"
    and   p1: "a = Get_Caps d_id"
   (* and   p2:"is_execute1 a"*)
    and   p3:"\<not>(get_t_set s (the (domain_of_event a)) \<subseteq> get_t_set s d) "
    and   p4:"s' = fst (get_caps s d_id)"
  shows   "s \<sim> d \<sim> s'"
  proof -
  {
    have a0: "is_execute1 a"
      by (simp add: is_execute1_def p1)
    have a2: "s = s'"
      by (simp add: p4 get_caps_def p1)
    }
  then show ?thesis by auto
  qed

  lemma crt_que_port_notchg_partportsinotherdom:
  assumes p0:"reachable0 s"
    and   p3:"domain_id \<noteq> d"
    and   p4:"s' =  fst (create_queuing_port sysconf  s domain_id pname)"
  shows   "get_ports_of_domain s d = get_ports_of_domain s' d"
  proof -
  {
    have "\<forall>p. p\<in>get_ports_of_domain s d \<longrightarrow> p\<in>get_ports_of_domain s' d"
    proof-
    {
      fix p
      assume a0:"p\<in>get_ports_of_domain s d"
      have a1:"p\<in>get_ports_of_domain s' d"
      proof(cases "pname \<in> get_domain_cfg_ports_byid sysconf domain_id")
        assume b0:"pname \<in> get_domain_cfg_ports_byid sysconf domain_id"
        have b1:"p \<noteq> get_portid_in_type (the (get_queuingport_conf sysconf pname))" 
          using b0 port_domain by auto 
        then show ?thesis using b0 port_domain by auto 
      next
        assume c0:"\<not>(pname \<in> get_domain_cfg_ports_byid sysconf domain_id)"
        then have c1:"s' = s" by (simp add: create_queuing_port_def p4) 
        then show ?thesis by (simp add: a0) 
      qed
    }
    then show ?thesis by auto
    qed
    moreover
    have "\<forall>p. p\<in>get_ports_of_domain s' d \<longrightarrow> p\<in>get_ports_of_domain s d"
    proof-
    {
      fix p
      assume a0:"p\<in>get_ports_of_domain s' d"
      have "p\<in>get_ports_of_domain s d" 
      proof(cases "pname \<in> get_domain_cfg_ports_byid sysconf domain_id")
        assume b0:"pname \<in> get_domain_cfg_ports_byid sysconf domain_id"
        have b1:"p \<noteq> get_portid_in_type (the (get_queuingport_conf sysconf pname))" 
          using b0 port_domain by auto 
        then show ?thesis using b0 port_domain by auto 
      next
        assume c0:"\<not>(pname \<in> get_domain_cfg_ports_byid sysconf domain_id)"
        then have c1:"s' = s" by (simp add: create_queuing_port_def p4) 
        then show ?thesis using a0 by auto  
      qed
    }
    then show ?thesis by auto
    qed
    then show ?thesis using calculation by blast
  }
  qed

  lemma crt_que_port_notchg_partstate:
                "\<lbrakk>s' = fst (create_queuing_port sysconf  s domain_id pname)
                  \<and> domain_id \<noteq> d\<rbrakk>
                                         \<Longrightarrow> (domains s) d  = (domains s') d "
   by (clarsimp simp:create_queuing_port_def )

  lemma crt_qport_lcl_resp:
   assumes p0:"reachable0 s"
    and   p1: "a = Create_Queuing_Port domain_id port_name"
   (* and   p2:"is_execute1 a"*)
    and   p3:"\<not>(get_t_set s (the (domain_of_event a)) \<subseteq> get_t_set s d) "
    and   p4:"s' = fst (create_queuing_port sysconf s domain_id port_name)"
  shows   "s \<sim> d \<sim> s'"
  proof -
  {
    have a0: "is_execute1 a"
      by (simp add: is_execute1_def p1)
    have a1: "d \<noteq> (the (domain_of_event a))"
      using p3 by auto
    have a2: "(domains s) d = (domains s') d"
      using a1 p3 p4 p1 create_queuing_port_def by auto
    have a3: "get_ports_of_domain s d = get_ports_of_domain s' d"
      by (metis all_not_in_conv create_queuing_port_def inf.idem p4 port_domain prod.sel(1))
    have a4:  "s \<sim> d \<sim> s'"
      using a2 a3 by auto
    }
  then show ?thesis by auto
  qed

  lemma snd_que_msg_lst_notchg_partstate:
                  "\<lbrakk>
                  s' = fst (send_queuing_message_maylost sysconf s domain_id pid m)\<rbrakk>
                                           \<Longrightarrow> (domains s) d = (domains s') d"
        
    apply(clarsimp simp:insert_msg2queuing_port_def 
           replace_msg2queuing_port_def send_queuing_message_maylost_def)
    apply(case_tac "ports (comm s) pid")
    apply simp
    apply(case_tac "a")        
    by auto

  lemma insert_msg_notchg_portstate:
 assumes p0:"reachable0 s"
    and   p1: "dst = the ((domain_ports s) port_id)"
    and   p2: "dst \<noteq> d "
    and   p3: "s' = (insert_msg2queuing_port s port_id msg)"
  shows   "get_ports_of_domain s d = get_ports_of_domain s' d"
  proof(induct "(ports (comm s)) port_id")
    case None 
      show ?case 
      using None.hyps p3 insert_msg2queuing_port_def by auto  
  next
    case (Some x)
    have e0:"(ports (comm s)) port_id = Some x" 
      by (simp add: Some.hyps)
    show ?case
      proof(induct "the ((ports (comm s)) port_id)")
        case (Queuing x1 x2 x3 x4 x5)
        have a1: "get_ports_of_domain s dst = get_ports_of_domain s' dst"
          using p1 p3 insert_msg2queuing_port_def by auto
        show ?case
           
        

  lemma send_que_msg_notchg_portstate:
  assumes p0:"reachable0 s"
    and   p1: "a = Send_Queuing_Message domain_id port_id msg"
    and   p2: "dst = the ((domain_ports s) port_id)"
    and   p3: "dst \<noteq> d "
    and   p4: "s' = fst (send_queuing_message_maylost sysconf s domain_id port_id msg)"
  shows   "get_ports_of_domain s d = get_ports_of_domain s' d"
  proof -
  {
    have "get_ports_of_domain s d = get_ports_of_domain s' d"
      proof (cases "(\<not> is_a_queuingport s port_id
                \<or> \<not> is_source_port s port_id
                \<or> \<not> domain_port_interf s domain_id port_id)")
        assume b0: "(\<not> is_a_queuingport s port_id
                \<or> \<not> is_source_port s port_id
                \<or> \<not> domain_port_interf s domain_id port_id)"
        with p4 show ?thesis using send_queuing_message_maylost_def by auto 
      next
        assume b0: "\<not> (\<not> is_a_queuingport s port_id
                \<or> \<not> is_source_port s port_id
                \<or> \<not> domain_port_interf s domain_id port_id)"
        show ?thesis
        proof(cases "is_full_portqueuing sysconf s port_id")
          assume c0:"is_full_portqueuing sysconf s port_id"
          with b0 have c1:"s' = s" by (simp add: p4 replace_msg2queuing_port_def 
                                  send_queuing_message_maylost_def) 
          then show ?thesis by auto
        next
          assume c0:"\<not> is_full_portqueuing sysconf s port_id"
          have d1:"s' = insert_msg2queuing_port s port_id msg" 
            using b0 c0 p4 send_queuing_message_maylost_def by auto
          with b0 show ?thesis
            proof(induct "(ports (comm s)) port_id")
              case None show ?case using None.hyps d1 insert_msg2queuing_port_def by auto  
            next
              case (Some x) 
              have e0:"(ports (comm s)) port_id = Some x" by (simp add: Some.hyps)
              show ?case
              proof(induct "the ((ports (comm s)) port_id)")
                case (Queuing x1 x2 x3 x4 x5)
                show ?case
    }
  then show ?thesis by auto
  qed

  lemma send_que_msg_lcl_resp:
   assumes p0:"reachable0 s"
    and   p1: "a = Send_Queuing_Message domain_id port_id msg"
    and   p2: "dst = the ((domain_ports s) port_id)"
    and   p3: "\<not>(get_t_set s domain_id \<subseteq> get_t_set s d) "
    and   p4: "s' = fst (send_queuing_message_maylost sysconf s domain_id port_id msg)"
  shows   "s \<sim> d \<sim> s'"
  proof -
  {
    have a0: "is_execute1 a"
      by (simp add: is_execute1_def p1)
    have a1: "d \<noteq> domain_id"
      using p3 by auto
    have "s \<sim> d \<sim> s'"
      proof (cases "d = dst")
        assume b0: "d = dst"
        have b1: "\<not> domain_port_interf s domain_id port_id"
          using b0 p2 p3 domain_port_interf_def by auto
        have b2: "s' = s"
          by (simp add: b1 p4 send_queuing_message_maylost_def)
        show "s \<sim> d \<sim> s'"
          using b2 vpeq1_symmetric_lemma by auto
      next
        assume b0: "d \<noteq> dst"
        have b1: "(domains s) d = (domains s') d"
          using p4 snd_que_msg_lst_notchg_partstate by blast
        have b2: "get_ports_of_domain s d = get_ports_of_domain s' d"
          
        
   
    have a2: "\<not> domain_port_interf s domain_id port_id"
      using p2 p3 domain_port_interf_def by auto
    have a2: "(domains s) d = (domains s') d"
      using a1 p3 p4 p1 send_queuing_message_maylost_def by auto
    have a3: "get_ports_of_domain s d = get_ports_of_domain s' d"
    have a4:  "s \<sim> d \<sim> s'"
      using a2 a3 by auto
    }
  then show ?thesis by auto
  qed


(*
by1 (smt SM.intro SM_enabled.intro SM_enabled_axioms.intro grant_exclusive1 s0t_init taint_set_respect_lemma1 vpeq1_def vpeq1_symmetric_lemma)
*)
end