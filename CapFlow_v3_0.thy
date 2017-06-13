theory CapFlow_v3_0
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

record Port = 
  p_buf_size :: max_buffer_size
  p_id :: port_id
  p_name :: port_name
  p_msgs ::  "Message set"

record Communication_Config = 
  ports_conf :: "Port set"

record Domain = 
  d_id :: domain_id
  d_name :: domain_name
  d_caps :: "cap set"
  d_ports :: "port_id set"

record Domains_Config = 
  domain_conf :: "Domain set"

record Sys_Config = 
  domconf :: Domains_Config
  commconf :: Communication_Config

subsubsection {* System state *}

record Communication_State = 
          ports :: "Port set"

record State = 
  domains :: "Domain set"
  comm :: Communication_State
  domain_ports :: "port_id \<rightharpoonup> domain_id"
  next_comp_id :: compartment_id
  next_port_id :: port_id

subsubsection {* Utility Functions used for Event Specification *} 

definition get_domain_from_sc_by_id :: "Sys_Config \<Rightarrow> domain_id \<Rightarrow> Domain option"
  where "get_domain_from_sc_by_id sc did \<equiv>
         if (\<exists>p. p \<in> domain_conf (domconf sc) \<and> d_id p = did)
         then
           Some (SOME p. p \<in> domain_conf (domconf sc) \<and> d_id p = did)
         else
           None"

definition get_domain_from_sc_by_name :: "Sys_Config \<Rightarrow> domain_name \<Rightarrow> Domain option"
  where "get_domain_from_sc_by_name sc dname \<equiv>
         if (\<exists>p. p \<in> domain_conf (domconf sc) \<and> d_name p = dname)
         then
           Some (SOME p. p \<in> domain_conf (domconf sc) \<and> d_name p = dname)
         else
           None"

definition get_domain_from_st_by_id :: "State \<Rightarrow> domain_id \<Rightarrow> Domain option"
  where "get_domain_from_st_by_id s did \<equiv>
         if (\<exists>p. p \<in> domains s \<and> d_id p = did)
         then
           Some (SOME p. p \<in> domains s \<and> d_id p = did)
         else
           None"

definition get_domain_from_st_by_name :: "State \<Rightarrow> domain_name \<Rightarrow> Domain option"
  where "get_domain_from_st_by_name s dname \<equiv>
         if (\<exists>p. p \<in> domains s \<and> d_name p = dname)
         then
           Some (SOME p. p \<in> domains s \<and> d_name p = dname)
         else
           None"


definition get_port_from_sc_by_id :: "Sys_Config \<Rightarrow> port_id \<Rightarrow> Port option"
  where "get_port_from_sc_by_id sc pid \<equiv>
         if (\<exists>p. p \<in> ports_conf (commconf sc) \<and> p_id p = pid)
         then
           Some (SOME p. p \<in> ports_conf (commconf sc) \<and> p_id p = pid)
         else
           None"

definition get_port_from_sc_by_name :: "Sys_Config \<Rightarrow> port_name \<Rightarrow> Port option"
  where "get_port_from_sc_by_name sc pname \<equiv>
         if (\<exists>p. p \<in> ports_conf (commconf sc) \<and> p_name p = pname)
         then
           Some (SOME p. p \<in> ports_conf (commconf sc) \<and> p_name p = pname)
         else
           None"

definition get_port_from_st_by_id :: "State \<Rightarrow> port_id \<Rightarrow> Port option"
  where "get_port_from_st_by_id s pid \<equiv>
         if (\<exists>p. p \<in> ports (comm s) \<and> p_id p = pid)
         then
           Some (SOME p. p \<in> ports (comm s) \<and> p_id p = pid)
         else
           None"

definition get_port_from_st_by_name :: "State \<Rightarrow> port_name \<Rightarrow> Port option"
  where "get_port_from_st_by_name s pname \<equiv>
         if (\<exists>p. p \<in> ports (comm s) \<and> p_name p = pname)
         then
           Some (SOME p. p \<in> ports (comm s) \<and> p_name p = pname)
         else
           None"


definition get_domain_from_st_by_port_id :: "State \<Rightarrow> port_id \<Rightarrow> Domain option"
  where "get_domain_from_st_by_port_id s pid \<equiv>
         if (\<exists>d. d \<in> domains s \<and> (domain_ports s) pid = Some (d_id d))
         then
           Some (SOME d. d \<in> domains s \<and> (domain_ports s) pid = Some (d_id d))
         else
           None"

definition get_domain_from_st_by_port_name :: "State \<Rightarrow> port_name \<Rightarrow> Domain option"
  where "get_domain_from_st_by_port_name s pname \<equiv>
         if (get_port_from_st_by_name s pname \<noteq> None)
         then
           let 
             pt = the (get_port_from_st_by_name s pname);
             pid = p_id pt
           in
             get_domain_from_st_by_port_id s pid
         else
           None"

definition is_a_port_of_domain :: "State \<Rightarrow> port_id \<Rightarrow> domain_id \<Rightarrow> bool"
  where "is_a_port_of_domain s port part \<equiv> (domain_ports s) port = Some part"

definition is_port_name :: "State \<Rightarrow> port_name \<Rightarrow> bool" 
  where
  "is_port_name s pn \<equiv> 
      if (get_port_from_st_by_name s pn \<noteq> None)
      then
        True
      else
        False
  "


definition get_portid_by_name :: "State \<Rightarrow> port_name \<Rightarrow> port_id option"
  where "get_portid_by_name s pn \<equiv> 
                  (if (is_port_name s pn) 
                    then 
                      let
                        pt = the (get_port_from_st_by_name s pn)
                      in
                      Some (p_id pt)
                    else 
                      None)"

definition get_portids_by_names :: "State \<Rightarrow> port_name set \<Rightarrow> (port_id option) set"
  where "get_portids_by_names s ps \<equiv>  {x. (\<exists>y. y \<in> ps \<and> x = get_portid_by_name s y)}"

definition get_portname_by_id :: "State \<Rightarrow> port_id \<Rightarrow> port_name option"
  where "get_portname_by_id s pid \<equiv> 
                  (if (get_port_from_st_by_id s pid \<noteq> None) 
                    then 
                      let
                        pt = the (get_port_from_st_by_id s pid)
                      in
                      Some (p_name pt)
                    else 
                      None)"

definition is_a_port :: "State \<Rightarrow> port_id \<Rightarrow> bool" 
  where "is_a_port s pid \<equiv> 
        if (get_port_from_st_by_id s pid \<noteq> None)
        then
          True
        else
          False
        "
                                                                      
definition get_domain_cfg_ports :: "State \<Rightarrow> domain_id \<Rightarrow> port_id set"
  where "get_domain_cfg_ports s did \<equiv>
    if(get_domain_from_st_by_id s did \<noteq> None)
    then
      let
        d = the (get_domain_from_st_by_id s did)
      in
        d_ports d
    else
      {}"

definition get_domain_cfg_ports_set :: "State \<Rightarrow> domain_id \<Rightarrow> Port set"
  where "get_domain_cfg_ports_set s did \<equiv>
    if(get_domain_from_st_by_id s did \<noteq> None)
    then
      let
        d = the (get_domain_from_st_by_id s did);
        pid_set = d_ports d;
        pts = ports (comm s);
        dst_pts = {p. p\<in>pts \<and> p_id p \<in> pid_set }
      in
        dst_pts
    else
      {}"

definition get_domain_cfg_ports_from_sc_byid :: "Sys_Config \<Rightarrow> domain_id \<Rightarrow> port_id set"
  where "get_domain_cfg_ports_from_sc_byid sc did \<equiv> 
   if(get_domain_from_sc_by_id sc did \<noteq> None)
    then
      let
        d = the (get_domain_from_sc_by_id sc did)
      in
        d_ports d
    else
      {}"

definition get_domain_cfg_cap_set_by_id :: "State \<Rightarrow> domain_id \<Rightarrow> cap set"
  where "get_domain_cfg_cap_set_by_id s did \<equiv>
    if(get_domain_from_st_by_id s did \<noteq> None)
    then
      let
        d = the (get_domain_from_st_by_id s did)
      in
        d_caps d
    else
      {}"

definition get_domain_cfg_cap_set_from_sc_byid :: "Sys_Config \<Rightarrow> domain_id \<Rightarrow> cap set"
  where "get_domain_cfg_cap_set_from_sc_byid sc did \<equiv> 
   if(get_domain_from_sc_by_id sc did \<noteq> None)
    then
      let
        d = the (get_domain_from_sc_by_id sc did)
      in
        d_caps d
    else
      {}"

definition get_ports_of_domain :: "State \<Rightarrow> domain_id \<Rightarrow> port_id set"
  where "get_ports_of_domain s p = {x. (domain_ports s) x = Some p}"

definition get_msgs_from_port :: "Port \<Rightarrow> (Message set) option"
  where "get_msgs_from_port p = Some (p_msgs p)"

definition get_msgs_from_port_by_id :: "State \<Rightarrow> port_id \<Rightarrow> (Message set) option"
  where "get_msgs_from_port_by_id s pid \<equiv>
    if(get_port_from_st_by_id s pid \<noteq> None)
    then
      let
        p = the (get_port_from_st_by_id s pid )
      in
        Some (p_msgs p)
    else
      None"

definition get_the_msgs_of_queuingport :: "State \<Rightarrow> port_id \<Rightarrow> (Message set) option"
  where "get_the_msgs_of_queuingport s pid \<equiv>
    if(get_port_from_st_by_id s pid \<noteq> None)
    then
      let
        p = the (get_port_from_st_by_id s pid )
      in
        Some (p_msgs p)
    else
      None"

definition insert_msg2queuing_port_to_port :: "Port \<Rightarrow> Message \<Rightarrow> Port"
  where "insert_msg2queuing_port_to_port pt m \<equiv> 
        let
          msg_set = p_msgs pt
        in
          pt\<lparr>p_msgs := insert m msg_set\<rparr>"

definition insert_msg2queuing_port_to_port_set :: "Port set \<Rightarrow> port_id \<Rightarrow> Message \<Rightarrow> Port set"
  where "insert_msg2queuing_port_to_port_set pts pid m \<equiv> 
        if(\<exists>p. p\<in>pts \<and> p_id p = pid)
        then
          let
            pt = SOME p. p\<in>pts \<and> p_id p = pid;
            msg_set = p_msgs pt;
            pts_rest = {p. p\<in>pts \<and> p_id p \<noteq> pid};
            new_pt = pt \<lparr> p_msgs := insert m msg_set \<rparr>
          in
            insert new_pt pts_rest
        else
          pts"

definition insert_msg2queuing_port :: "State \<Rightarrow> port_id
        \<Rightarrow> Message \<Rightarrow> State"
  where "insert_msg2queuing_port s pid m \<equiv>
        if(get_port_from_st_by_id s pid \<noteq> None)
        then
          let
            cs = comm s;
            pts = ports cs;
            pt = SOME p. p\<in>pts \<and> p_id p = pid;
            msg_set = p_msgs pt;
            pts_rest = {p. p\<in>pts \<and> p_id p \<noteq> pid};
            new_pt = pt \<lparr> p_msgs := insert m msg_set \<rparr>
          in
            s\<lparr>comm := cs
               \<lparr> ports := insert new_pt pts_rest \<rparr>
             \<rparr>
        else
          s"

definition replace_msg2queuing_port :: "State \<Rightarrow> port_id \<Rightarrow> Message \<Rightarrow> State"
  where "replace_msg2queuing_port s pid m \<equiv> s"

definition remove_msg_from_queuingport :: "State \<Rightarrow> port_id \<Rightarrow> (State \<times> Message option)"
  where "remove_msg_from_queuingport s pid \<equiv>
        if(get_port_from_st_by_id s pid \<noteq> None)
        then
          let
            cs = comm s;
            pts = ports cs;
            pt = SOME p. p\<in>pts \<and> p_id p = pid;
            msg_set = p_msgs pt;
            pts_rest = {p. p\<in>pts \<and> p_id p \<noteq> pid};
            m = SOME x. x\<in>msg_set;
            new_pt = pt \<lparr> p_msgs := msg_set - {m} \<rparr>
          in
            (s\<lparr>comm := cs
               \<lparr> ports := insert new_pt pts_rest \<rparr>
             \<rparr>, Some m)
        else
          (s, None)"

definition clear_msg_queuingport :: "State \<Rightarrow> port_id \<Rightarrow> State"
  where "clear_msg_queuingport s pid  \<equiv> 
        if(get_port_from_st_by_id s pid \<noteq> None)
        then
          let
            cs = comm s;
            pts = ports cs;
            pt = SOME p. p\<in>pts \<and> p_id p = pid;
            msg_set = p_msgs pt;
            pts_rest = {p. p\<in>pts \<and> p_id p \<noteq> pid};
            new_pt = pt \<lparr> p_msgs := {} \<rparr>
          in
            s\<lparr>comm := cs
               \<lparr> ports := insert new_pt pts_rest \<rparr>
             \<rparr>
        else
          s"

definition is_a_domain :: "State \<Rightarrow> domain_id \<Rightarrow> bool"
  where "is_a_domain s did \<equiv> get_domain_from_st_by_id s did \<noteq> None"

definition get_max_bufsize_of_port :: "State \<Rightarrow> port_id \<Rightarrow> max_buffer_size option"
  where "get_max_bufsize_of_port s pid \<equiv>
      if(get_port_from_st_by_id s pid \<noteq> None)
        then
          let
            pt = the(get_port_from_st_by_id s pid)
          in
          Some (p_buf_size pt )
        else
          None" 

definition get_current_bufsize_port :: "State \<Rightarrow> port_id \<Rightarrow> buffer_size option"
   where "get_current_bufsize_port s pid \<equiv>
      if(get_port_from_st_by_id s pid \<noteq> None)
        then
          let
            pt = the(get_port_from_st_by_id s pid);
            msg_set = p_msgs pt
          in
          Some (card msg_set )
        else
          None" 

definition is_full_portqueuing :: "State \<Rightarrow> port_id \<Rightarrow> bool"
  where "is_full_portqueuing s pid \<equiv> 
                get_max_bufsize_of_port s pid = get_current_bufsize_port s pid"

definition is_empty_port :: "State \<Rightarrow> port_id \<Rightarrow> bool"
  where "is_empty_port s pid \<equiv> 
              the (get_current_bufsize_port s pid) = 0"

definition get_port_buf_size :: "State \<Rightarrow> port_id \<Rightarrow> buffer_size"
  where "get_port_buf_size s p \<equiv> 
              the (get_current_bufsize_port s p)"

definition is_empty_portqueuing :: "State \<Rightarrow> port_id \<Rightarrow> bool"
  where "is_empty_portqueuing s p \<equiv> 
            the (get_current_bufsize_port s p) = 0"

definition has_msg_inportqueuing :: "State \<Rightarrow> port_id \<Rightarrow> bool"
  where "has_msg_inportqueuing s pid \<equiv> 
            the (get_current_bufsize_port s pid) \<noteq> 0"

definition get_t_set :: "State \<Rightarrow> domain_id \<Rightarrow> cap set " where
  "get_t_set s did \<equiv>
        if(get_domain_from_st_by_id s did \<noteq> None)
        then
          let
            cap_set =  (get_domain_cfg_cap_set_by_id s did)
          in
          ({cap. cap \<in> cap_set \<and> TAINT \<in> rights cap})
        else
          {}"

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
    if(get_domain_from_st_by_id s did \<noteq> None)
    then
      let
        cap_set = get_domain_cfg_cap_set_by_id s did ;
        new_add_cap =  \<lparr> target = next_comp_id s,
                               rights = {TAINT,GRANT} \<rparr>;
        new_cap_set = insert new_add_cap cap_set;
        rest_doms = {d. d\<in> domains s \<and> d_id d \<noteq> did};
        new_domain = SOME d. d\<in>domains s \<and> d_id d = did;
        updated_domain = new_domain\<lparr>d_caps := new_cap_set\<rparr>;
        dst_doms = {d. \<forall>d1. d1\<in>domains s \<and> d = d1\<lparr>d_caps := insert new_add_cap cap_set\<rparr> \<and> d_id d1 = did}
      in
      (s\<lparr>
         (*domains := insert updated_domain rest_doms,*)
         domains := dst_doms \<union> rest_doms,
         next_comp_id := (next_comp_id s) + 1
         \<rparr>, Some new_add_cap)
    else
      (s, None)"

definition grant_cap :: "State \<Rightarrow> domain_id \<Rightarrow> domain_id \<Rightarrow> cap \<Rightarrow> State" where
  "grant_cap s src_id dst_id cap \<equiv> 
        if (cap \<notin> get_domain_cfg_cap_set_by_id s src_id
            \<or> get_domain_from_st_by_id s src_id \<noteq> None
            \<or> get_domain_from_st_by_id s dst_id \<noteq> None)
          then
            s
        else
          let
            doms = domains s;
            newly_granted_cap =  \<lparr> target = target cap,
                             rights = {TAINT} \<rparr>;
            rest_doms = {d. d\<in>domains s \<and> d_id d \<noteq> dst_id};
            dst_dom = SOME d. d\<in>domains s \<and> d_id d = dst_id;
            cap_set = d_caps dst_dom;
            updated_dom = dst_dom\<lparr>d_caps := insert newly_granted_cap cap_set\<rparr>;
            dst_doms = {d. \<forall>d1. d1\<in>domains s \<and> d = d1\<lparr>d_caps := insert newly_granted_cap cap_set\<rparr> \<and> d_id d1 = dst_id}
          in
          s\<lparr>
            (*domains := insert updated_dom rest_doms *)
            domains := dst_doms \<union> rest_doms 
            \<rparr>"
                          
definition get_caps :: "State \<Rightarrow> domain_id \<Rightarrow> (State \<times> (cap set) option) " where
  "get_caps s did \<equiv> 
                if get_domain_from_st_by_id s did = None 
                  then (s, None) 
                else
                  (s, Some (get_domain_cfg_cap_set_by_id s did))"

definition get_taint_cap_set :: "State \<Rightarrow> domain_id \<Rightarrow> (State \<times>  (cap set) option) " where
   "get_taint_cap_set s did \<equiv> 
                if get_domain_from_st_by_id s did = None  
                  then (s, None) 
                else
                  let
                    cap_set = (get_domain_cfg_cap_set_by_id s did)
                  in
                    (s, Some ({cap. cap \<in> cap_set \<and> TAINT \<in> rights cap}))"

definition create_queuing_port :: "State \<Rightarrow> domain_id \<Rightarrow> port_name \<Rightarrow> (State \<times> port_id option)" where
  "create_queuing_port s did pn \<equiv>          
            if (get_domain_from_st_by_id s did = None)
            then
              (s, None)
            else
              let
                cs = comm s;
                pts = ports cs;
                domainpts = domain_ports s;
                new_port =  \<lparr> 
                             p_buf_size = 16,
                             p_id = next_port_id s,
                             p_name = pn,
                             p_msgs = {}
                              \<rparr>;
                new_id = next_port_id s;
                rest_doms = {d. d\<in>domains s \<and> d_id d \<noteq> did};
                dst_dom = SOME d. d\<in>domains s \<and> d_id d = did;
                port_id_set = d_ports dst_dom;
                updated_dom = dst_dom\<lparr>d_ports := insert new_id port_id_set\<rparr>;
                (*dst_doms = {d. \<forall>d1. d1\<in>domains s \<and> d = d1\<lparr>d_ports := insert new_id port_id_set\<rparr> \<and> d_id d1 = did};*)
                dst_doms = {d\<lparr>d_ports := insert new_id port_id_set\<rparr> | d. d\<in>domains s \<and> d_id d = did};
                dst_doms1 = {d\<lparr>d_ports := insert new_id port_id_set\<rparr> | d. d = dst_dom};
                new_dst_doms = {d. \<exists>d1. d1\<in>domains s \<and> (d = d1 \<and> (d_id d1 \<noteq> did) )
                                  \<or> (d = d1\<lparr>d_ports := insert new_id port_id_set\<rparr> \<and> (d_id d1 = did))};
                new_ports = insert new_port pts
              in
              (s\<lparr>
                 (*domains := insert updated_dom rest_doms,*)
                 (*domains := dst_doms1 \<union> rest_doms,*)
                 domains := new_dst_doms,
                 comm := cs\<lparr> ports := new_ports\<rparr>,
                 domain_ports := domainpts (new_id := Some did),
                 next_port_id := (next_port_id s) + 1
                 \<rparr>, Some new_id)
              "

definition send_queuing_message_maylost :: "State \<Rightarrow> domain_id \<Rightarrow> port_id \<Rightarrow> Message \<Rightarrow> (State \<times> bool)" where
  "send_queuing_message_maylost s did pid m \<equiv> 
              (if(\<not> is_a_port s pid
                \<or> \<not> domain_port_interf s did pid)
              then (s, False)
              else if is_full_portqueuing s pid then
                (replace_msg2queuing_port s pid m, True)
              else
                (insert_msg2queuing_port s pid m, True))"

definition receive_queuing_message :: "State \<Rightarrow> domain_id \<Rightarrow> port_id \<Rightarrow> (State \<times> Message option)" where
  "receive_queuing_message s did pid \<equiv> 
              (if (\<not> is_a_port_of_domain s pid (did)
                \<or> is_empty_portqueuing s pid)
              then (s, None)
              else remove_msg_from_queuingport s pid
              )"

definition get_queuing_port_id :: "State \<Rightarrow> domain_id \<Rightarrow> port_name \<Rightarrow> (State \<times> port_id option)" where
  "get_queuing_port_id s did pname \<equiv> 
          (if (\<exists>p. p\<in>get_domain_cfg_ports_set s did \<and> p_name p = pname)
          then (s, None) 
          else (s, get_portid_by_name s pname))"

definition clear_queuing_port :: "State \<Rightarrow> domain_id \<Rightarrow> port_id \<Rightarrow> State" where
  "clear_queuing_port s did pid \<equiv> 
          (if (\<not> is_a_port_of_domain s pid (did)
                \<or> \<not> is_a_port_of_domain s pid (did)
                )
          then s
          else 
          let
            cs = comm s;
            pts = ports cs;
            pt = SOME p. p\<in>pts \<and> p_id p = pid;
            msg_set = p_msgs pt;
            pts_rest = {p. p\<in>pts \<and> p_id p \<noteq> pid};
            new_pt = pt \<lparr> p_msgs := {} \<rparr>
          in
            s\<lparr>comm := cs
               \<lparr> ports := insert new_pt pts_rest \<rparr>
             \<rparr>
          )"


definition system_init :: "Sys_Config \<Rightarrow> State"
  where "system_init sc \<equiv> \<lparr>
                            domains = domain_conf (domconf sc),                                  
                            comm = \<lparr>ports=ports_conf (commconf sc)\<rparr>,
                            domain_ports = (\<lambda> x. None),
                            next_comp_id = 0,
                            next_port_id = 0
                           \<rparr>"  


subsubsection{* Instantiation and Its Proofs of Security Model  *}

consts sysconf :: "Sys_Config" 
definition sys_config_witness :: Sys_Config 
where 
"sys_config_witness \<equiv> \<lparr>
                        domconf = \<lparr> domain_conf = {}\<rparr> , 
                        commconf = \<lparr> ports_conf = {}\<rparr>                       
                        \<rparr>" 
(*
specification (sysconf)
  trans_not_part : "domain_conf sysconf = x \<Longrightarrow> domain_conf sysconf = x"
  port_domain:"\<forall>p1 p2. get_domain_cfg_ports_byid sysconf p1 \<inter> get_domain_cfg_ports_byid sysconf p2 = {}"
    apply (intro exI[of _ "sys_config_witness"] allI impI, simp) 
    by (simp add: get_domain_cfg_ports_byid_def sys_config_witness_def)
*)

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
    case e of  Create_Cap did \<Rightarrow> fst (create_new_tag s did)
             | Grant_Cap did dst_id cap \<Rightarrow> grant_cap  s did dst_id cap
             | Get_Taint_Cap_Set did \<Rightarrow> fst (get_taint_cap_set s did)
             | Get_Caps did \<Rightarrow> fst (get_caps s did)
             | Create_Queuing_Port domain_id port_name \<Rightarrow>fst (create_queuing_port s domain_id port_name)
             | Send_Queuing_Message domain_id port_id msg \<Rightarrow> fst (send_queuing_message_maylost s domain_id port_id msg)
             | Receive_Queuing_Message domain_id port_id \<Rightarrow> fst (receive_queuing_message s domain_id port_id)
             | Get_Queuing_Portid domain_id port_name \<Rightarrow> fst (get_queuing_port_id s domain_id port_name )
             | Clear_Queuing_Port domain_id port_id \<Rightarrow> clear_queuing_port s domain_id port_id
               "

definition domain_of_event :: "Event \<Rightarrow> domain_id option"
  where
    "domain_of_event e \<equiv> 
       case e of  Create_Cap did \<Rightarrow> Some did
                | Grant_Cap did dst_id cap \<Rightarrow> Some did
                | Get_Taint_Cap_Set did \<Rightarrow> Some did
                | Get_Caps did \<Rightarrow> Some did
                | Create_Queuing_Port did port_name \<Rightarrow> Some did
                | Send_Queuing_Message did port_name msg \<Rightarrow>  Some did
                | Receive_Queuing_Message did port_id \<Rightarrow>  Some did
                | Get_Queuing_Portid did port_name \<Rightarrow>  Some did
                | Clear_Queuing_Port did port_id \<Rightarrow>  Some did
                "

definition grant_dest_of_event :: "Event \<Rightarrow> domain_id option"
 where
    "grant_dest_of_event e \<equiv> 
       case e of  Create_Cap did \<Rightarrow> Some did
                | Grant_Cap did dst_id cap \<Rightarrow> Some dst_id
                | Get_Taint_Cap_Set did \<Rightarrow> None
                | Get_Caps did \<Rightarrow> None
                | Create_Queuing_Port did port_name \<Rightarrow> None
                | Send_Queuing_Message did port_name msg \<Rightarrow> None
                | Receive_Queuing_Message did port_id \<Rightarrow> None
                | Get_Queuing_Portid did port_name \<Rightarrow> None
                | Clear_Queuing_Port did port_id \<Rightarrow> None
                 "                                            
definition is_execute1 :: "Event \<Rightarrow> bool"
  where
    "is_execute1 e \<equiv> 
          case e of   Create_Cap did \<Rightarrow> False
                | Grant_Cap did dst_id cap \<Rightarrow> False
                | Get_Taint_Cap_Set did \<Rightarrow> True
                | Get_Caps did \<Rightarrow> True
                | Create_Queuing_Port did port_name \<Rightarrow> True
                | Send_Queuing_Message did port_name msg \<Rightarrow> True
                | Receive_Queuing_Message did port_id \<Rightarrow> True
                | Get_Queuing_Portid did port_name \<Rightarrow> True
                | Clear_Queuing_Port did port_id \<Rightarrow> True
                 "

definition is_grant1 :: "Event \<Rightarrow> bool"
  where
    "is_grant1 e \<equiv> \<not>is_execute1 e"

definition vpeq1 :: "State \<Rightarrow> domain_id \<Rightarrow> State \<Rightarrow> bool" ("(_ \<sim> _ \<sim> _)") 
  where
    "vpeq1 s d t \<equiv> 
        let
          d1 = get_domain_from_st_by_id s d;
          d2 = get_domain_from_st_by_id t d;
          ps1 = get_domain_cfg_ports s d;
          ps2 = get_domain_cfg_ports t d
        in
          if(d1 = d2 \<and> ps1 = ps2)
          then
            True
          else
            False
          "

declare vpeq1_def [cong]

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

lemma vpeq1_domain_eq_lemma : "\<forall>s t d. vpeq1 s d t \<longrightarrow> get_domain_cfg_cap_set_by_id s d = get_domain_cfg_cap_set_by_id t d"
  using vpeq1_def get_domain_cfg_cap_set_by_id_def  by auto

lemma vpeq1_domain_eq_lemma1 : "\<forall>s t d. vpeq1 s d t \<longrightarrow> get_domain_from_st_by_id s d = get_domain_from_st_by_id t d"
  using vpeq1_def by auto

lemma taint_set_respect_lemma1: "\<forall>s t d. vpeq1 s d t \<longrightarrow> get_t_set s d = get_t_set t d"
  using get_t_set_def vpeq1_domain_eq_lemma vpeq1_domain_eq_lemma1 by presburger

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

subsubsection{*proving "get caps" satisfying the "local respect" property*}

  lemma get_caps_lcl_resp:
  assumes p0:"reachable0 s"
    and   p1: "a = Get_Caps did"
   (* and   p2:"is_execute1 a"*)
    and   p3:"\<not>(get_t_set s (the (domain_of_event a)) \<subseteq> get_t_set s d) "
    and   p4:"s' = fst (get_caps s did)"
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

subsubsection{*proving "get taint cap set" satisfying the "local respect" property*}

  lemma get_tt_cap_set_lcl_resp:
  assumes p0:"reachable0 s"
    and   p1: "a = Get_Taint_Cap_Set did"
   (* and   p2:"is_execute1 a"*)
    and   p3:"\<not>(get_t_set s (the (domain_of_event a)) \<subseteq> get_t_set s d) "
    and   p4:"s' = fst (get_taint_cap_set s did)"
  shows   "s \<sim> d \<sim> s'"
  proof -
  {
    have a0: "is_execute1 a"
      by (simp add: is_execute1_def p1)
    have a2: "s = s'"
      by (simp add: p4 get_taint_cap_set_def p1)
    }
  then show ?thesis by auto
  qed

subsubsection{*proving "create queuing port" satisfying the "local respect" property*}

 lemma crt_que_port_notchg_domain:
  assumes p0:"reachable0 s"
    and   p1:"domain_id \<noteq> d"
    and   p2:"s' =  fst (create_queuing_port s domain_id pname)"
  shows   "get_domain_from_st_by_id s d = get_domain_from_st_by_id s' d"
  proof -
  {
    show ?thesis
    proof (cases "get_domain_from_st_by_id s domain_id = None")
      assume a0: "get_domain_from_st_by_id s domain_id = None"
      have a1: "s' = s"
        using a0 create_queuing_port_def p2 by auto
      show ?thesis
        using a1 get_ports_of_domain_def by auto
    next
      assume a0: "\<not> get_domain_from_st_by_id s domain_id = None" 
      show ?thesis
        proof (cases "\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)")
        assume b0: "\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)"
        have b1: "get_domain_from_st_by_id s d = None"
          using b0 get_domain_from_st_by_id_def by auto
        have b2: "next_comp_id s = next_comp_id s'"
          using a0 p2 create_queuing_port_def by auto
        have b3: "\<forall>p. p\<in>{dom. dom\<in>domains s \<and> d_id dom \<noteq> domain_id} 
                    \<longrightarrow> p\<in>{dom. dom\<in>domains s' \<and> d_id dom \<noteq> domain_id}"
          using a0 p2 create_queuing_port_def by auto
        have b4: "\<forall>p. p\<in>{dom. dom\<in>domains s' \<and> d_id dom \<noteq> domain_id} 
                    \<longrightarrow> p\<in>{dom. dom\<in>domains s \<and> d_id dom \<noteq> domain_id}"
          using a0 p2 create_queuing_port_def by auto
        have b5:"{dom. dom\<in>domains s \<and> d_id dom \<noteq> domain_id} = {dom. dom\<in>domains s' \<and> d_id dom \<noteq> domain_id}"
          using a0 p2 create_queuing_port_def by auto
        have b6: "(\<forall>p. p \<in> domains s \<longrightarrow> d_id p \<noteq> d)"
          using b0 by auto
        have b7: "(\<forall>p. p \<in> domains s' \<longrightarrow> d_id p \<noteq> d)"
          using p1 b5 b6 by auto
        have b8: "\<not> (\<exists>p. p \<in> domains s' \<and> d_id p = d)"
          using b7 by auto
        have b9: "get_domain_from_st_by_id s' d = None"
          using b8 get_domain_from_st_by_id_def by auto
        show ?thesis
          using b9 b1 by auto
      next
        assume b0: "\<not> \<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)"
        have b1: "(\<exists>p. p \<in> domains s \<and> d_id p = d)"
          using b0 by auto
        have b2: "\<forall>p. p\<in>{dom. dom\<in>domains s \<and> d_id dom \<noteq> domain_id} 
                    \<longrightarrow> p\<in>{dom. dom\<in>domains s' \<and> d_id dom \<noteq> domain_id}"
          using a0 p2 create_queuing_port_def by auto
        have b3: "\<forall>p. p\<in>{dom. dom\<in>domains s' \<and> d_id dom \<noteq> domain_id} 
                    \<longrightarrow> p\<in>{dom. dom\<in>domains s \<and> d_id dom \<noteq> domain_id}"
          using a0 p2 create_queuing_port_def by auto
        have b4:"{dom. dom\<in>domains s \<and> d_id dom \<noteq> domain_id} = {dom. dom\<in>domains s' \<and> d_id dom \<noteq> domain_id}"
          using a0 p2 create_queuing_port_def by auto
        have b5: "\<exists>p. p \<in> domains s \<and> d_id p = d \<longrightarrow> p \<in> domains s'"
          using b4 p1 by auto
        have b6: "(SOME p. p \<in> domains s \<and> d_id p = d) = (SOME p. p \<in> domains s' \<and> d_id p = d)"
          proof -
            { fix dd :: Domain
              have "d_id dd \<noteq> d \<or> dd \<notin> domains s \<and> dd \<notin> domains s' \<or> dd \<in> domains s \<and> d_id dd = d \<and> dd \<in> domains s'"
                using b4 p1 by blast }
            then have "\<forall>da. d_id da \<noteq> d \<or> da \<notin> domains s \<and> da \<notin> domains s' \<or> da \<in> domains s \<and> d_id da = d \<and> da \<in> domains s'"
              by metis
            then show ?thesis
              by meson
          qed
        have b7: "get_domain_from_st_by_id s d = Some(SOME p. p \<in> domains s \<and> d_id p = d)"
          using b1 get_domain_from_st_by_id_def by auto
        have b8: "(\<exists>p. p \<in> domains s' \<and> d_id p = d)"
          using p1 b1 b2 b3 b4 b5 b6 by auto
        have b9: "get_domain_from_st_by_id s' d = Some(SOME p. p \<in> domains s' \<and> d_id p = d)"
          using b8 get_domain_from_st_by_id_def by auto
        have b10: "get_domain_from_st_by_id s d = get_domain_from_st_by_id s' d"
          using b7 b9 b6 by auto
        then show ?thesis by auto
        qed
      qed
  }
  qed

  lemma crt_que_port_notchg_domain_ports:
  assumes p0:"reachable0 s"
    and   p1:"domain_id \<noteq> d"
    and   p2:"s' =  fst (create_queuing_port s domain_id pname)"
  shows   "get_domain_cfg_ports s d = get_domain_cfg_ports s' d"
  proof -
  {
    show ?thesis
    proof (cases "get_domain_from_st_by_id s domain_id = None")
      assume a0: "get_domain_from_st_by_id s domain_id = None"
      have a1: "s' = s"
        using a0 create_queuing_port_def p2 by auto
      show ?thesis
        using a1 get_ports_of_domain_def by auto
    next
      assume a0: "\<not> get_domain_from_st_by_id s domain_id = None"
      have a2:"get_domain_from_st_by_id s d = get_domain_from_st_by_id s' d"
          using p0 p1 p2 crt_que_port_notchg_domain by auto
      show ?thesis
        proof (cases "get_domain_from_st_by_id s d = None")
          assume b0: "get_domain_from_st_by_id s d = None"
          have b1: "get_domain_cfg_ports s d = {}"
            using b0 get_domain_cfg_ports_def by auto
          have b2: "get_domain_from_st_by_id s' d = None"
            using a2 b0 by auto
          have b3: "get_domain_cfg_ports s' d = {}"
            using b2 get_domain_cfg_ports_def by auto
          show ?thesis
            using b3 b1 by auto
        next
          assume b0: "get_domain_from_st_by_id s d \<noteq> None"
          have b1: "d_ports (the (get_domain_from_st_by_id s d)) 
                    = d_ports (the (get_domain_from_st_by_id s' d))"
            using a2 by auto
          have b2: "get_domain_cfg_ports s d 
                    = d_ports (the (get_domain_from_st_by_id s d))"
            using b0 get_domain_cfg_ports_def by auto
          have b3: "get_domain_from_st_by_id s' d \<noteq> None"
            using a2 b0 by auto
          have b4: "get_domain_cfg_ports s' d 
                    = d_ports (the (get_domain_from_st_by_id s' d))"
            using b3 get_domain_cfg_ports_def by auto
          show ?thesis
            using b4 b2 b1 by auto
        qed
      qed
  }
  qed

(*
  lemma crt_que_port_notchg_partstate:
                "\<lbrakk>s' = fst (create_queuing_port sysconf  s domain_id pname)
                  \<and> domain_id \<noteq> d\<rbrakk>
                                         \<Longrightarrow> (domains s) d  = (domains s') d "
   by (clarsimp simp:create_queuing_port_def )
*)

  lemma crt_qport_lcl_resp:
   assumes p0:"reachable0 s"
    and   p1: "a = Create_Queuing_Port domain_id port_name"
   (* and   p2:"is_execute1 a"*)
    and   p3:"\<not>(get_t_set s domain_id \<subseteq> get_t_set s d) "
    and   p4:"s' = fst (create_queuing_port s domain_id port_name)"
  shows   "s \<sim> d \<sim> s'"
  proof -
  {
    have a0: "is_execute1 a"
      by (simp add: is_execute1_def p1)
    have a1: "d \<noteq> domain_id"
      using p3 by auto
    have a2: "get_domain_from_st_by_id s d = get_domain_from_st_by_id s' d"
      using p0 a1 p4 crt_que_port_notchg_domain by auto
    have a3: "get_domain_cfg_ports s d = get_domain_cfg_ports s' d"
      using p0 a1 p4 crt_que_port_notchg_domain_ports by auto
    have a4:  "s \<sim> d \<sim> s'"
      using a2 a3 by auto
    }
  then show ?thesis by auto
  qed

subsubsection{*proving "send queuing message maylost" satisfying the "local respect" property*}

lemma snd_que_msg_ml_notchg_domain:
  assumes p0:"reachable0 s"
    and   p1:"domain_id \<noteq> d"
    and   p2:"s' =  fst (send_queuing_message_maylost s domain_id pid m)"
  shows   "get_domain_from_st_by_id s d = get_domain_from_st_by_id s' d"    
  proof (cases "\<not> is_a_port s pid
                \<or> \<not> domain_port_interf s domain_id pid")
    assume a0: "\<not> is_a_port s pid
                \<or> \<not> domain_port_interf s domain_id pid"
    have a1: "s = s'"
      using a0 p2 send_queuing_message_maylost_def by auto
    show ?thesis
      using a1 by auto
  next
    assume a0: "\<not> (\<not> is_a_port s pid 
                \<or> \<not> domain_port_interf s domain_id pid)"
    show ?thesis
    proof (cases "is_full_portqueuing s pid")
      assume b0: "is_full_portqueuing s pid"
      have b1: "s' = replace_msg2queuing_port s pid m"
        using a0 b0 p2 send_queuing_message_maylost_def by auto
      have b2: "s =  replace_msg2queuing_port s pid m"
        using replace_msg2queuing_port_def by auto
      have b3: "s = s'"
        using b1 b2 by auto
      show ?thesis
        using b3 by auto
    next
      assume b0: "\<not> is_full_portqueuing s pid"
      have b1: "s' = insert_msg2queuing_port s pid m"
        using a0 b0 p2 send_queuing_message_maylost_def by auto
      have b2: "{dom. dom\<in>domains s} = {dom. dom\<in>domains s'}"
          using a0 b1 insert_msg2queuing_port_def by auto
      show ?thesis
        proof (cases "\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)")
        assume c0: "\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)"
        have c1: "get_domain_from_st_by_id s d = None"
          using c0 get_domain_from_st_by_id_def by auto
        have c2: "(\<forall>p. p \<in> domains s \<longrightarrow> d_id p \<noteq> d)"
          using c0 by auto
        have c3: "(\<forall>p. p \<in> domains s' \<longrightarrow> d_id p \<noteq> d)"
          using p1 b2 c2 by auto
        have c4: "\<not> (\<exists>p. p \<in> domains s' \<and> d_id p = d)"
          using c3 by auto
        have c5: "get_domain_from_st_by_id s' d = None"
          using c4 get_domain_from_st_by_id_def by auto
        show ?thesis
          using c5 c1 by auto
        next
        assume c0: "\<not>\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)"
        have c1: "(\<exists>p. p \<in> domains s \<and> d_id p = d)"
          using c0 by auto
        have c2: "\<exists>p. p \<in> domains s \<and> d_id p = d \<longrightarrow> p \<in> domains s'"
          using b2 p1 by auto
        have c3: "(SOME p. p \<in> domains s \<and> d_id p = d) = (SOME p. p \<in> domains s' \<and> d_id p = d)"
          proof -
            { fix dd :: Domain
              have "d_id dd \<noteq> d \<or> dd \<notin> domains s \<and> dd \<notin> domains s' \<or> dd \<in> domains s \<and> d_id dd = d \<and> dd \<in> domains s'"
                using b2 p1 by blast }
            then have "\<forall>da. d_id da \<noteq> d \<or> da \<notin> domains s \<and> da \<notin> domains s' \<or> da \<in> domains s \<and> d_id da = d \<and> da \<in> domains s'"
              by metis
            then show ?thesis
              by meson
          qed
        have c4: "get_domain_from_st_by_id s d = Some(SOME p. p \<in> domains s \<and> d_id p = d)"
          using c1 get_domain_from_st_by_id_def by auto
        have c5: "(\<exists>p. p \<in> domains s' \<and> d_id p = d)"
          using p1 b2 c1 c2 c3 c4 by auto
        have c6: "get_domain_from_st_by_id s' d = Some(SOME p. p \<in> domains s' \<and> d_id p = d)"
          using c5 get_domain_from_st_by_id_def by auto
        have b10: "get_domain_from_st_by_id s d = get_domain_from_st_by_id s' d"
          using c3 c4 c5 c6 by auto
        then show ?thesis by auto
        qed
     qed
  qed

  lemma snd_que_msg_ml_notchg_domain_ports:
  assumes p0:"reachable0 s"
    and   p1:"domain_id \<noteq> d"
    and   p2:"s' =  fst (send_queuing_message_maylost s domain_id pid m)"
  shows   "get_domain_cfg_ports s d = get_domain_cfg_ports s' d"
  proof (cases "\<not> is_a_port s pid
                \<or> \<not> domain_port_interf s domain_id pid")
    assume a0: "\<not> is_a_port s pid
                \<or> \<not> domain_port_interf s domain_id pid"
    have a1: "s = s'"
      using a0 p2 send_queuing_message_maylost_def by auto
    show ?thesis
      using a1 by auto
  next
    assume a0: "\<not> (\<not> is_a_port s pid 
                \<or> \<not> domain_port_interf s domain_id pid)"
    show ?thesis
    proof (cases "is_full_portqueuing s pid")
      assume b0: "is_full_portqueuing s pid"
      have b1: "s' = replace_msg2queuing_port s pid m"
        using a0 b0 p2 send_queuing_message_maylost_def by auto
      have b2: "s =  replace_msg2queuing_port s pid m"
        using replace_msg2queuing_port_def by auto
      have b3: "s = s'"
        using b1 b2 by auto
      show ?thesis
        using b3 by auto
    next
      assume b0: "\<not> is_full_portqueuing s pid"
      have b1: "s' = insert_msg2queuing_port s pid m"
        using a0 b0 p2 send_queuing_message_maylost_def by auto
      have b2: "{dom. dom\<in>domains s} = {dom. dom\<in>domains s'}"
          using a0 b1 insert_msg2queuing_port_def by auto
      show ?thesis
        proof (cases "\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)")
        assume c0: "\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)"
        have c1: "get_domain_from_st_by_id s d = None"
          using c0 get_domain_from_st_by_id_def by auto
        have c2: "(\<forall>p. p \<in> domains s \<longrightarrow> d_id p \<noteq> d)"
          using c0 by auto
        have c3: "(\<forall>p. p \<in> domains s' \<longrightarrow> d_id p \<noteq> d)"
          using p1 b2 c2 by auto
        have c4: "\<not> (\<exists>p. p \<in> domains s' \<and> d_id p = d)"
          using c3 by auto
        have c5: "get_domain_from_st_by_id s' d = None"
          using c4 get_domain_from_st_by_id_def by auto
        have c6: "get_domain_cfg_ports s d = {}"
          using c1 get_domain_cfg_ports_def by auto
        have c7: "get_domain_cfg_ports s' d = {}"
          using c5 get_domain_cfg_ports_def by auto
        show ?thesis
          using c6 c7 by auto
        next
        assume c0: "\<not>\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)"
        have c1: "(\<exists>p. p \<in> domains s \<and> d_id p = d)"
          using c0 by auto
        have c2: "\<exists>p. p \<in> domains s \<and> d_id p = d \<longrightarrow> p \<in> domains s'"
          using b2 p1 by auto
        have c3: "(SOME p. p \<in> domains s \<and> d_id p = d) = (SOME p. p \<in> domains s' \<and> d_id p = d)"
          proof -
            { fix dd :: Domain
              have "d_id dd \<noteq> d \<or> dd \<notin> domains s \<and> dd \<notin> domains s' \<or> dd \<in> domains s \<and> d_id dd = d \<and> dd \<in> domains s'"
                using b2 p1 by blast }
            then have "\<forall>da. d_id da \<noteq> d \<or> da \<notin> domains s \<and> da \<notin> domains s' \<or> da \<in> domains s \<and> d_id da = d \<and> da \<in> domains s'"
              by metis
            then show ?thesis
              by meson
          qed
        have c4: "get_domain_from_st_by_id s d = Some(SOME p. p \<in> domains s \<and> d_id p = d)"
          using c1 get_domain_from_st_by_id_def by auto
        have c5: "(\<exists>p. p \<in> domains s' \<and> d_id p = d)"
          using p1 b2 c1 c2 c3 c4 by auto
        have c6: "get_domain_from_st_by_id s' d = Some(SOME p. p \<in> domains s' \<and> d_id p = d)"
          using c5 get_domain_from_st_by_id_def by auto
        have c7: "get_domain_from_st_by_id s d = get_domain_from_st_by_id s' d"
          using c3 c4 c5 c6 by auto
        have c8: "get_domain_from_st_by_id s' d \<noteq> None"
          using c6 by auto
        have c9: "get_domain_from_st_by_id s d \<noteq> None"
          using c4 by auto
        have c10: "d_ports (the (get_domain_from_st_by_id s d)) 
                    = d_ports (the (get_domain_from_st_by_id s' d))"
          using c7 by auto
        have c11: "get_domain_cfg_ports s d 
                    = d_ports (the (get_domain_from_st_by_id s d))"
          using c9 get_domain_cfg_ports_def by auto
        have c12: "get_domain_cfg_ports s' d 
                    = d_ports (the (get_domain_from_st_by_id s' d))"
          using c8 get_domain_cfg_ports_def by auto
        show ?thesis
            using c10 c11 c12 by auto
      qed
    qed
  qed

  lemma snd_que_msg_ml_lcl_resp:
   assumes p0:"reachable0 s"
    and   p1: "a = Send_Queuing_Message did pid m"
   (* and   p2:"is_execute1 a"*)
    and   p3:"\<not>(get_t_set s did \<subseteq> get_t_set s d) "
    and   p4:"s' = fst (send_queuing_message_maylost s did pid m)"
  shows   "s \<sim> d \<sim> s'"
  proof -
  {
    have a0: "is_execute1 a"
      by (simp add: is_execute1_def p1)
    have a1: "d \<noteq> did"
      using p3 by auto
    have a2: "get_domain_from_st_by_id s d = get_domain_from_st_by_id s' d"
      using p0 a1 p4 snd_que_msg_ml_notchg_domain by auto
    have a3: "get_domain_cfg_ports s d = get_domain_cfg_ports s' d"
      using p0 a1 p4 snd_que_msg_ml_notchg_domain_ports by auto
    have a4:  "s \<sim> d \<sim> s'"
      using a2 a3 by auto
    }
  then show ?thesis by auto
  qed

subsubsection{*proving "receive queuing message" satisfying the "local respect" property*}

lemma rcv_que_msg_notchg_domain:
  assumes p0:"reachable0 s"
    and   p1:"domain_id \<noteq> d"
    and   p2:"s' =  fst (receive_queuing_message s domain_id pid)"
  shows   "get_domain_from_st_by_id s d = get_domain_from_st_by_id s' d"
  proof (cases "\<not> is_a_port_of_domain s pid (domain_id)
                \<or> is_empty_portqueuing s pid")
    assume a0: "\<not> is_a_port_of_domain s pid (domain_id)
                \<or> is_empty_portqueuing s pid"
    have a1: "s' = s"
      using a0 p2 receive_queuing_message_def by auto
    show ?thesis
      using a1 by auto
  next
    assume a0: "\<not> (\<not> is_a_port_of_domain s pid domain_id 
                \<or> is_empty_portqueuing s pid)"
    have a1: "s' = fst(remove_msg_from_queuingport s pid)"
      using a0 p2 receive_queuing_message_def by auto
    show ?thesis
    proof (cases "get_port_from_st_by_id s pid = None")
      assume b0: "get_port_from_st_by_id s pid = None"
      have b1: "s' = s"
        using b0 a1 remove_msg_from_queuingport_def by auto
      show ?thesis
        using b1 by auto
    next
      assume b0: "get_port_from_st_by_id s pid \<noteq> None"
      have b2: "{dom. dom\<in>domains s} = {dom. dom\<in>domains s'}"
          using b0 a1 remove_msg_from_queuingport_def by auto
      show ?thesis
      proof (cases "\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)")
        assume c0: "\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)"
        have c1: "get_domain_from_st_by_id s d = None"
          using c0 get_domain_from_st_by_id_def by auto
        have c2: "(\<forall>p. p \<in> domains s \<longrightarrow> d_id p \<noteq> d)"
          using c0 by auto
        have c3: "(\<forall>p. p \<in> domains s' \<longrightarrow> d_id p \<noteq> d)"
          using p1 b2 c2 by auto
        have c4: "\<not> (\<exists>p. p \<in> domains s' \<and> d_id p = d)"
          using c3 by auto
        have c5: "get_domain_from_st_by_id s' d = None"
          using c4 get_domain_from_st_by_id_def by auto
        show ?thesis
          using c5 c1 by auto
      next
        assume c0: "\<not>\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)"
        have c1: "(\<exists>p. p \<in> domains s \<and> d_id p = d)"
          using c0 by auto
        have c2: "\<exists>p. p \<in> domains s \<and> d_id p = d \<longrightarrow> p \<in> domains s'"
          using b2 p1 by auto
        have c3: "(SOME p. p \<in> domains s \<and> d_id p = d) = (SOME p. p \<in> domains s' \<and> d_id p = d)"
          proof -
            { fix dd :: Domain
              have "d_id dd \<noteq> d \<or> dd \<notin> domains s \<and> dd \<notin> domains s' \<or> dd \<in> domains s \<and> d_id dd = d \<and> dd \<in> domains s'"
                using b2 p1 by blast }
            then have "\<forall>da. d_id da \<noteq> d \<or> da \<notin> domains s \<and> da \<notin> domains s' \<or> da \<in> domains s \<and> d_id da = d \<and> da \<in> domains s'"
              by metis
            then show ?thesis
              by meson
          qed
        have c4: "get_domain_from_st_by_id s d = Some(SOME p. p \<in> domains s \<and> d_id p = d)"
          using c1 get_domain_from_st_by_id_def by auto
        have c5: "(\<exists>p. p \<in> domains s' \<and> d_id p = d)"
          using p1 b2 c1 c2 c3 c4 by auto
        have c6: "get_domain_from_st_by_id s' d = Some(SOME p. p \<in> domains s' \<and> d_id p = d)"
          using c5 get_domain_from_st_by_id_def by auto
        have b10: "get_domain_from_st_by_id s d = get_domain_from_st_by_id s' d"
          using c3 c4 c5 c6 by auto
        then show ?thesis by auto
      qed
    qed
  qed

lemma rcv_que_msg_notchg_domain_ports:
  assumes p0:"reachable0 s"
    and   p1:"domain_id \<noteq> d"
    and   p2:"s' =  fst (receive_queuing_message s domain_id pid)"
  shows   "get_domain_cfg_ports s d = get_domain_cfg_ports s' d"
  proof (cases "\<not> is_a_port_of_domain s pid (domain_id)
                \<or> is_empty_portqueuing s pid")
    assume a0: "\<not> is_a_port_of_domain s pid (domain_id)
                \<or> is_empty_portqueuing s pid"
    have a1: "s' = s"
      using a0 p2 receive_queuing_message_def by auto
    show ?thesis
      using a1 by auto
  next
    assume a0: "\<not> (\<not> is_a_port_of_domain s pid domain_id 
                \<or> is_empty_portqueuing s pid)"
    have a1: "s' = fst(remove_msg_from_queuingport s pid)"
      using a0 p2 receive_queuing_message_def by auto
    show ?thesis
    proof (cases "get_port_from_st_by_id s pid = None")
      assume b0: "get_port_from_st_by_id s pid = None"
      have b1: "s' = s"
        using b0 a1 remove_msg_from_queuingport_def by auto
      show ?thesis
        using b1 by auto
    next
      assume b0: "get_port_from_st_by_id s pid \<noteq> None"
      have b2: "{dom. dom\<in>domains s} = {dom. dom\<in>domains s'}"
          using b0 a1 remove_msg_from_queuingport_def by auto
      show ?thesis
      proof (cases "\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)")
        assume c0: "\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)"
        have c1: "get_domain_from_st_by_id s d = None"
          using c0 get_domain_from_st_by_id_def by auto
        have c2: "(\<forall>p. p \<in> domains s \<longrightarrow> d_id p \<noteq> d)"
          using c0 by auto
        have c3: "(\<forall>p. p \<in> domains s' \<longrightarrow> d_id p \<noteq> d)"
          using p1 b2 c2 by auto
        have c4: "\<not> (\<exists>p. p \<in> domains s' \<and> d_id p = d)"
          using c3 by auto
        have c5: "get_domain_from_st_by_id s' d = None"
          using c4 get_domain_from_st_by_id_def by auto
        have c6: "get_domain_cfg_ports s d = {}"
          using c1 get_domain_cfg_ports_def by auto
        have c7: "get_domain_cfg_ports s' d = {}"
          using c5 get_domain_cfg_ports_def by auto
        show ?thesis
          using c6 c7 by auto
      next
        assume c0: "\<not>\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)"
        have c1: "(\<exists>p. p \<in> domains s \<and> d_id p = d)"
          using c0 by auto
        have c2: "\<exists>p. p \<in> domains s \<and> d_id p = d \<longrightarrow> p \<in> domains s'"
          using b2 p1 by auto
        have c3: "(SOME p. p \<in> domains s \<and> d_id p = d) = (SOME p. p \<in> domains s' \<and> d_id p = d)"
          proof -
            { fix dd :: Domain
              have "d_id dd \<noteq> d \<or> dd \<notin> domains s \<and> dd \<notin> domains s' \<or> dd \<in> domains s \<and> d_id dd = d \<and> dd \<in> domains s'"
                using b2 p1 by blast }
            then have "\<forall>da. d_id da \<noteq> d \<or> da \<notin> domains s \<and> da \<notin> domains s' \<or> da \<in> domains s \<and> d_id da = d \<and> da \<in> domains s'"
              by metis
            then show ?thesis
              by meson
          qed
        have c4: "get_domain_from_st_by_id s d = Some(SOME p. p \<in> domains s \<and> d_id p = d)"
          using c1 get_domain_from_st_by_id_def by auto
        have c5: "(\<exists>p. p \<in> domains s' \<and> d_id p = d)"
          using p1 b2 c1 c2 c3 c4 by auto
        have c6: "get_domain_from_st_by_id s' d = Some(SOME p. p \<in> domains s' \<and> d_id p = d)"
          using c5 get_domain_from_st_by_id_def by auto
        have c7: "get_domain_from_st_by_id s d = get_domain_from_st_by_id s' d"
          using c3 c4 c5 c6 by auto
        have c8: "get_domain_from_st_by_id s' d \<noteq> None"
          using c6 by auto
        have c9: "get_domain_from_st_by_id s d \<noteq> None"
          using c4 by auto
        have c10: "d_ports (the (get_domain_from_st_by_id s d)) 
                    = d_ports (the (get_domain_from_st_by_id s' d))"
          using c7 by auto
        have c11: "get_domain_cfg_ports s d 
                    = d_ports (the (get_domain_from_st_by_id s d))"
          using c9 get_domain_cfg_ports_def by auto
        have c12: "get_domain_cfg_ports s' d 
                    = d_ports (the (get_domain_from_st_by_id s' d))"
          using c8 get_domain_cfg_ports_def by auto
        show ?thesis
            using c10 c11 c12 by auto
      qed
    qed
  qed

lemma rcv_que_msg_lcl_resp:
  assumes p0:"reachable0 s"
    and   p1: "a = Receive_Queuing_Message did pid"
   (* and   p2:"is_execute1 a"*)
    and   p3:"\<not>(get_t_set s did \<subseteq> get_t_set s d) "
    and   p4:"s' = fst (receive_queuing_message s did pid)"
  shows   "s \<sim> d \<sim> s'"
  proof -
  {
    have a0: "is_execute1 a"
      by (simp add: is_execute1_def p1)
    have a1: "d \<noteq> did"
      using p3 by auto
    have a2: "get_domain_from_st_by_id s d = get_domain_from_st_by_id s' d"
      using p0 a1 p4 rcv_que_msg_notchg_domain by auto
    have a3: "get_domain_cfg_ports s d = get_domain_cfg_ports s' d"
      using p0 a1 p4 rcv_que_msg_notchg_domain_ports by auto
    have a4:  "s \<sim> d \<sim> s'"
      using a2 a3 by auto
    }
  then show ?thesis by auto
  qed

subsubsection{*proving "get queuing port id" satisfying the "local respect" property*}

lemma gt_que_pt_id_resp:
  assumes p0:"reachable0 s"
    and   p1: "a = Get_Queuing_Portid did pname"
   (* and   p2:"is_execute1 a"*)
    and   p3:"\<not>(get_t_set s did \<subseteq> get_t_set s d) "
    and   p4:"s' = fst (get_queuing_port_id s did pname)"
  shows   "s \<sim> d \<sim> s'"
  proof -
  {
    have a0: "is_execute1 a"
      by (simp add: is_execute1_def p1)
    have a1: "d \<noteq> did"
      using p3 by auto
    have a2: "s' = s"
      using p4 get_queuing_port_id_def by auto
    have a3:  "s \<sim> d \<sim> s'"
      using a2 vpeq1_symmetric_lemma by auto
    }
  then show ?thesis by auto
  qed

subsubsection{*proving "clear queuing port" satisfying the "local respect" property*}

lemma clr_que_pt_notchg_domain:
  assumes p0:"reachable0 s"
    and   p1:"did \<noteq> d"
    and   p2:"s' = (clear_queuing_port s did pid)"
  shows   "get_domain_from_st_by_id s d = get_domain_from_st_by_id s' d"
  proof (cases "\<not> is_a_port_of_domain s pid (did)
                \<or> \<not> is_a_port_of_domain s pid (did)")
    assume a0: "\<not> is_a_port_of_domain s pid (did)
                \<or> \<not> is_a_port_of_domain s pid (did)"
    have a1: "s' = s"
      using a0 p2 clear_queuing_port_def by auto
    show ?thesis
      using a1 by auto
  next
    assume a0: "\<not> (\<not> is_a_port_of_domain s pid (did)
                \<or> \<not> is_a_port_of_domain s pid (did))"
      have b2: "{dom. dom\<in>domains s} = {dom. dom\<in>domains s'}"
        using a0 p2 clear_queuing_port_def by auto
      show ?thesis
      proof (cases "\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)")
        assume c0: "\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)"
        have c1: "get_domain_from_st_by_id s d = None"
          using c0 get_domain_from_st_by_id_def by auto
        have c2: "(\<forall>p. p \<in> domains s \<longrightarrow> d_id p \<noteq> d)"
          using c0 by auto
        have c3: "(\<forall>p. p \<in> domains s' \<longrightarrow> d_id p \<noteq> d)"
          using p1 b2 c2 by auto
        have c4: "\<not> (\<exists>p. p \<in> domains s' \<and> d_id p = d)"
          using c3 by auto
        have c5: "get_domain_from_st_by_id s' d = None"
          using c4 get_domain_from_st_by_id_def by auto
        show ?thesis
          using c5 c1 by auto
      next
        assume c0: "\<not>\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)"
        have c1: "(\<exists>p. p \<in> domains s \<and> d_id p = d)"
          using c0 by auto
        have c2: "\<exists>p. p \<in> domains s \<and> d_id p = d \<longrightarrow> p \<in> domains s'"
          using b2 p1 by auto
        have c3: "(SOME p. p \<in> domains s \<and> d_id p = d) = (SOME p. p \<in> domains s' \<and> d_id p = d)"
          proof -
            { fix dd :: Domain
              have "d_id dd \<noteq> d \<or> dd \<notin> domains s \<and> dd \<notin> domains s' \<or> dd \<in> domains s \<and> d_id dd = d \<and> dd \<in> domains s'"
                using b2 p1 by blast }
            then have "\<forall>da. d_id da \<noteq> d \<or> da \<notin> domains s \<and> da \<notin> domains s' \<or> da \<in> domains s \<and> d_id da = d \<and> da \<in> domains s'"
              by metis
            then show ?thesis
              by meson
          qed
        have c4: "get_domain_from_st_by_id s d = Some(SOME p. p \<in> domains s \<and> d_id p = d)"
          using c1 get_domain_from_st_by_id_def by auto
        have c5: "(\<exists>p. p \<in> domains s' \<and> d_id p = d)"
          using p1 b2 c1 c2 c3 c4 by auto
        have c6: "get_domain_from_st_by_id s' d = Some(SOME p. p \<in> domains s' \<and> d_id p = d)"
          using c5 get_domain_from_st_by_id_def by auto
        have b10: "get_domain_from_st_by_id s d = get_domain_from_st_by_id s' d"
          using c3 c4 c5 c6 by auto
        then show ?thesis by auto
    qed
  qed

lemma clr_que_pt_notchg_domain_ports:
  assumes p0:"reachable0 s"
    and   p1:"did \<noteq> d"
    and   p2:"s' = (clear_queuing_port s did pid)"
  shows   "get_domain_cfg_ports s d = get_domain_cfg_ports s' d"
  proof (cases "\<not> is_a_port_of_domain s pid (did)
                \<or> \<not> is_a_port_of_domain s pid (did)")
    assume a0: "\<not> is_a_port_of_domain s pid (did)
                \<or> \<not> is_a_port_of_domain s pid (did)"
    have a1: "s' = s"
      using a0 p2 clear_queuing_port_def by auto
    show ?thesis
      using a1 by auto
  next
    assume a0: "\<not> (\<not> is_a_port_of_domain s pid (did)
                \<or> \<not> is_a_port_of_domain s pid (did))"
      have b2: "{dom. dom\<in>domains s} = {dom. dom\<in>domains s'}"
        using a0 p2 clear_queuing_port_def by auto
      show ?thesis
      proof (cases "\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)")
        assume c0: "\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)"
        have c1: "get_domain_from_st_by_id s d = None"
          using c0 get_domain_from_st_by_id_def by auto
        have c2: "(\<forall>p. p \<in> domains s \<longrightarrow> d_id p \<noteq> d)"
          using c0 by auto
        have c3: "(\<forall>p. p \<in> domains s' \<longrightarrow> d_id p \<noteq> d)"
          using p1 b2 c2 by auto
        have c4: "\<not> (\<exists>p. p \<in> domains s' \<and> d_id p = d)"
          using c3 by auto
        have c5: "get_domain_from_st_by_id s' d = None"
          using c4 get_domain_from_st_by_id_def by auto
        have c6: "get_domain_cfg_ports s d = {}"
          using c1 get_domain_cfg_ports_def by auto
        have c7: "get_domain_cfg_ports s' d = {}"
          using c5 get_domain_cfg_ports_def by auto
        show ?thesis
          using c6 c7 by auto
      next
        assume c0: "\<not>\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)"
        have c1: "(\<exists>p. p \<in> domains s \<and> d_id p = d)"
          using c0 by auto
        have c2: "\<exists>p. p \<in> domains s \<and> d_id p = d \<longrightarrow> p \<in> domains s'"
          using b2 p1 by auto
        have c3: "(SOME p. p \<in> domains s \<and> d_id p = d) = (SOME p. p \<in> domains s' \<and> d_id p = d)"
          proof -
            { fix dd :: Domain
              have "d_id dd \<noteq> d \<or> dd \<notin> domains s \<and> dd \<notin> domains s' \<or> dd \<in> domains s \<and> d_id dd = d \<and> dd \<in> domains s'"
                using b2 p1 by blast }
            then have "\<forall>da. d_id da \<noteq> d \<or> da \<notin> domains s \<and> da \<notin> domains s' \<or> da \<in> domains s \<and> d_id da = d \<and> da \<in> domains s'"
              by metis
            then show ?thesis
              by meson
          qed
        have c4: "get_domain_from_st_by_id s d = Some(SOME p. p \<in> domains s \<and> d_id p = d)"
          using c1 get_domain_from_st_by_id_def by auto
        have c5: "(\<exists>p. p \<in> domains s' \<and> d_id p = d)"
          using p1 b2 c1 c2 c3 c4 by auto
        have c6: "get_domain_from_st_by_id s' d = Some(SOME p. p \<in> domains s' \<and> d_id p = d)"
          using c5 get_domain_from_st_by_id_def by auto
        have c7: "get_domain_from_st_by_id s d = get_domain_from_st_by_id s' d"
          using c3 c4 c5 c6 by auto
        have c8: "get_domain_from_st_by_id s' d \<noteq> None"
          using c6 by auto
        have c9: "get_domain_from_st_by_id s d \<noteq> None"
          using c4 by auto
        have c10: "d_ports (the (get_domain_from_st_by_id s d)) 
                    = d_ports (the (get_domain_from_st_by_id s' d))"
          using c7 by auto
        have c11: "get_domain_cfg_ports s d 
                    = d_ports (the (get_domain_from_st_by_id s d))"
          using c9 get_domain_cfg_ports_def by auto
        have c12: "get_domain_cfg_ports s' d 
                    = d_ports (the (get_domain_from_st_by_id s' d))"
          using c8 get_domain_cfg_ports_def by auto
        show ?thesis
            using c10 c11 c12 by auto
    qed
  qed

lemma clr_que_pt_lcl_resp:
  assumes p0:"reachable0 s"
    and   p1: "a = Clear_Queuing_Port did pid"
   (* and   p2:"is_execute1 a"*)
    and   p3:"\<not>(get_t_set s did \<subseteq> get_t_set s d) "
    and   p4:"s' = (clear_queuing_port s did pid)"
  shows   "s \<sim> d \<sim> s'"
  proof -
  {
    have a0: "is_execute1 a"
      by (simp add: is_execute1_def p1)
    have a1: "d \<noteq> did"
      using p3 by auto
    have a2: "get_domain_from_st_by_id s d = get_domain_from_st_by_id s' d"
      using p0 a1 p4 clr_que_pt_notchg_domain by auto
    have a3: "get_domain_cfg_ports s d = get_domain_cfg_ports s' d"
      using p0 a1 p4 clr_que_pt_notchg_domain_ports by auto
    have a4:  "s \<sim> d \<sim> s'"
      using a2 a3 by auto
    }
  then show ?thesis by auto
  qed

subsection{* Concrete unwinding condition of "grant local respect" *}

subsubsection{*proving "create new tag" satisfying the "grant local respect" property*}

lemma crt_new_tag_notchg_domain:
  assumes p0:"reachable0 s"
    and   p1: "a = Create_Cap did"
    and   p3:"\<not>(d = the(grant_dest_of_event a)) "
    and   p4:"s' = fst (create_new_tag s did)"
  shows   "get_domain_from_st_by_id s d = get_domain_from_st_by_id s' d"
  proof (cases "get_domain_from_st_by_id s did = None")
    assume a0: "get_domain_from_st_by_id s did = None"
    have a1: "s' = s"
      using a0 p4 create_new_tag_def by auto
    show ?thesis
      using a1 by auto
  next
    assume a0: "get_domain_from_st_by_id s did \<noteq> None"
    have a1: "did = the(grant_dest_of_event a)"
      using grant_dest_of_event_def p1 by auto
    have a2: "did \<noteq> d"
      using a1 p3 by auto
    have a3:"{dom. dom\<in>domains s \<and> d_id dom \<noteq> did} = {dom. dom\<in>domains s' \<and> d_id dom \<noteq> did}"
      using a0 p4 create_new_tag_def by auto
    show ?thesis
    proof (cases "\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)")
      assume c0: "\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)"
      have c1: "get_domain_from_st_by_id s d = None"
        using c0 get_domain_from_st_by_id_def by auto
      have c2: "(\<forall>p. p \<in> domains s \<longrightarrow> d_id p \<noteq> d)"
        using c0 by auto
      have c3: "(\<forall>p. p \<in> domains s' \<longrightarrow> d_id p \<noteq> d)"
        using p1 a3 a2 c2 by auto
      have c4: "\<not> (\<exists>p. p \<in> domains s' \<and> d_id p = d)"
        using c3 by auto
      have c5: "get_domain_from_st_by_id s' d = None"
        using c4 get_domain_from_st_by_id_def by auto
      show ?thesis
        using c5 c1 by auto  
    next
      assume c0: "\<not>\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)"
      have c1: "(\<exists>p. p \<in> domains s \<and> d_id p = d)"
        using c0 by auto
      have c2: "\<exists>p. p \<in> domains s \<and> d_id p = d \<longrightarrow> p \<in> domains s'"
        using a2 a3 p1 by auto
      have c3: "(SOME p. p \<in> domains s \<and> d_id p = d) = (SOME p. p \<in> domains s' \<and> d_id p = d)"
        proof -
          { fix dd :: Domain
            have "d_id dd \<noteq> d \<or> dd \<notin> domains s \<and> dd \<notin> domains s' \<or> dd \<in> domains s \<and> d_id dd = d \<and> dd \<in> domains s'"
              using a2 a3 p1 by blast }
          then have "\<forall>da. d_id da \<noteq> d \<or> da \<notin> domains s \<and> da \<notin> domains s' \<or> da \<in> domains s \<and> d_id da = d \<and> da \<in> domains s'"
            by metis
          then show ?thesis
            by meson
        qed
      have c4: "get_domain_from_st_by_id s d = Some(SOME p. p \<in> domains s \<and> d_id p = d)"
        using c1 get_domain_from_st_by_id_def by auto
      have c5: "(\<exists>p. p \<in> domains s' \<and> d_id p = d)"
        using p1 a2 a3 c1 c2 c3 c4 by auto
      have c6: "get_domain_from_st_by_id s' d = Some(SOME p. p \<in> domains s' \<and> d_id p = d)"
        using c5 get_domain_from_st_by_id_def by auto
      have b10: "get_domain_from_st_by_id s d = get_domain_from_st_by_id s' d"
        using c3 c4 c5 c6 by auto
      then show ?thesis by auto
    qed
  qed

lemma crt_new_tag_notchg_domain_ports:
  assumes p0:"reachable0 s"
    and   p1: "a = Create_Cap did"
    and   p3:"\<not>(d = the(grant_dest_of_event a)) "
    and   p4:"s' = fst (create_new_tag s did)"
  shows   "get_domain_cfg_ports s d = get_domain_cfg_ports s' d"
  proof (cases "get_domain_from_st_by_id s did = None")
    assume a0: "get_domain_from_st_by_id s did = None"
    have a1: "s' = s"
      using a0 p4 create_new_tag_def by auto
    show ?thesis
      using a1 by auto
  next
    assume a0: "get_domain_from_st_by_id s did \<noteq> None"
    have a1: "did = the(grant_dest_of_event a)"
      using grant_dest_of_event_def p1 by auto
    have a2: "did \<noteq> d"
      using a1 p3 by auto
    have a3:"{dom. dom\<in>domains s \<and> d_id dom \<noteq> did} = {dom. dom\<in>domains s' \<and> d_id dom \<noteq> did}"
      using a0 p4 create_new_tag_def by auto
    show ?thesis
    proof (cases "\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)")
      assume c0: "\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)"
      have c1: "get_domain_from_st_by_id s d = None"
        using c0 get_domain_from_st_by_id_def by auto
      have c2: "(\<forall>p. p \<in> domains s \<longrightarrow> d_id p \<noteq> d)"
        using c0 by auto
      have c3: "(\<forall>p. p \<in> domains s' \<longrightarrow> d_id p \<noteq> d)"
        using p1 a3 a2 c2 by auto
      have c4: "\<not> (\<exists>p. p \<in> domains s' \<and> d_id p = d)"
        using c3 by auto
      have c5: "get_domain_from_st_by_id s' d = None"
        using c4 get_domain_from_st_by_id_def by auto
      have c6: "get_domain_cfg_ports s d = {}"
        using c1 get_domain_cfg_ports_def by auto
      have c7: "get_domain_cfg_ports s' d = {}"
        using c5 get_domain_cfg_ports_def by auto
      show ?thesis
        using c6 c7 by auto
    next
      assume c0: "\<not>\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)"
      have c1: "(\<exists>p. p \<in> domains s \<and> d_id p = d)"
        using c0 by auto
      have c2: "\<exists>p. p \<in> domains s \<and> d_id p = d \<longrightarrow> p \<in> domains s'"
        using a2 a3 p1 by auto
      have c3: "(SOME p. p \<in> domains s \<and> d_id p = d) = (SOME p. p \<in> domains s' \<and> d_id p = d)"
        proof -
          { fix dd :: Domain
            have "d_id dd \<noteq> d \<or> dd \<notin> domains s \<and> dd \<notin> domains s' \<or> dd \<in> domains s \<and> d_id dd = d \<and> dd \<in> domains s'"
              using a2 a3 p1 by blast }
          then have "\<forall>da. d_id da \<noteq> d \<or> da \<notin> domains s \<and> da \<notin> domains s' \<or> da \<in> domains s \<and> d_id da = d \<and> da \<in> domains s'"
            by metis
          then show ?thesis
            by meson
        qed
      have c4: "get_domain_from_st_by_id s d = Some(SOME p. p \<in> domains s \<and> d_id p = d)"
        using c1 get_domain_from_st_by_id_def by auto
      have c5: "(\<exists>p. p \<in> domains s' \<and> d_id p = d)"
        using p1 a2 a3 c1 c2 c3 c4 by auto
      have c6: "get_domain_from_st_by_id s' d = Some(SOME p. p \<in> domains s' \<and> d_id p = d)"
        using c5 get_domain_from_st_by_id_def by auto
      have c7: "get_domain_from_st_by_id s d = get_domain_from_st_by_id s' d"
        using c3 c4 c5 c6 by auto
      have c8: "get_domain_from_st_by_id s' d \<noteq> None"
        using c6 by auto
      have c9: "get_domain_from_st_by_id s d \<noteq> None"
        using c4 by auto
      have c10: "d_ports (the (get_domain_from_st_by_id s d)) 
                  = d_ports (the (get_domain_from_st_by_id s' d))"
        using c7 by auto
      have c11: "get_domain_cfg_ports s d 
                  = d_ports (the (get_domain_from_st_by_id s d))"
        using c9 get_domain_cfg_ports_def by auto
      have c12: "get_domain_cfg_ports s' d 
                  = d_ports (the (get_domain_from_st_by_id s' d))"
        using c8 get_domain_cfg_ports_def by auto
      show ?thesis
        using c10 c11 c12 by auto
    qed
  qed

lemma crt_new_tag_grt_lcl_resp:
  assumes p0:"reachable0 s"
    and   p1: "a = Create_Cap did"
    and   p3:"\<not>(d = the(grant_dest_of_event a)) "
    and   p4:"s' = fst (create_new_tag s did)"
  shows   "s \<sim> d \<sim> s'"
  proof -
  {
    have a0: "is_grant1 a"
      using is_grant1_def is_execute1_def p1 by auto
    have a3: "get_domain_from_st_by_id s d = get_domain_from_st_by_id s' d"
      using p0 p1 p3 p4 crt_new_tag_notchg_domain by auto
    have a4: "get_domain_cfg_ports s d = get_domain_cfg_ports s' d"
      using p0 p1 p3 p4 crt_new_tag_notchg_domain_ports by auto
    have a4:  "s \<sim> d \<sim> s'"
      using a3 a4 by auto
    }
  then show ?thesis by auto
  qed

subsubsection{*proving "grant cap" satisfying the "grant local respect" property*}

lemma grt_cap_grt_notchg_domain:
  assumes p0:"reachable0 s"
    and   p1: "a = Grant_Cap did dst_id cap"
   (* and   p2:"is_execute1 a"*)
    and   p3:"\<not>(d = the(grant_dest_of_event a)) "
    and   p4:"s' = (grant_cap s did dst_id cap)"
  shows   "get_domain_from_st_by_id s d = get_domain_from_st_by_id s' d"
  proof (cases "cap \<notin> get_domain_cfg_cap_set_by_id s did
            \<or> get_domain_from_st_by_id s did \<noteq> None
            \<or> get_domain_from_st_by_id s dst_id \<noteq> None")
    assume a0: "cap \<notin> get_domain_cfg_cap_set_by_id s did
            \<or> get_domain_from_st_by_id s did \<noteq> None
            \<or> get_domain_from_st_by_id s dst_id \<noteq> None"
    have a1: "s' = s"
      using a0 p4 grant_cap_def by auto
    then show ?thesis by auto
  next
    assume a0: "\<not> (cap \<notin> get_domain_cfg_cap_set_by_id s did
            \<or> get_domain_from_st_by_id s did \<noteq> None
            \<or> get_domain_from_st_by_id s dst_id \<noteq> None)"
    have a1: "dst_id = the(grant_dest_of_event a)"
      using p1 grant_dest_of_event_def by auto
    have a2: "dst_id \<noteq> d"
      using a1 p3 by auto
    have a3:"{dom. dom\<in>domains s \<and> d_id dom \<noteq> dst_id} = {dom. dom\<in>domains s' \<and> d_id dom \<noteq> dst_id}"
      using a0 p4 grant_cap_def by auto
    show ?thesis
    proof (cases "\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)")
      assume c0: "\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)"
      have c1: "get_domain_from_st_by_id s d = None"
        using c0 get_domain_from_st_by_id_def by auto
      have c2: "(\<forall>p. p \<in> domains s \<longrightarrow> d_id p \<noteq> d)"
        using c0 by auto
      have c3: "(\<forall>p. p \<in> domains s' \<longrightarrow> d_id p \<noteq> d)"
        using p1 a3 a2 c2 by auto
      have c4: "\<not> (\<exists>p. p \<in> domains s' \<and> d_id p = d)"
        using c3 by auto
      have c5: "get_domain_from_st_by_id s' d = None"
        using c4 get_domain_from_st_by_id_def by auto
      show ?thesis
        using c5 c1 by auto  
    next
      assume c0: "\<not>\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)"
      have c1: "(\<exists>p. p \<in> domains s \<and> d_id p = d)"
        using c0 by auto
      have c2: "\<exists>p. p \<in> domains s \<and> d_id p = d \<longrightarrow> p \<in> domains s'"
        using a2 a3 p1 by auto
      have c3: "(SOME p. p \<in> domains s \<and> d_id p = d) = (SOME p. p \<in> domains s' \<and> d_id p = d)"
        proof -
          { fix dd :: Domain
            have "d_id dd \<noteq> d \<or> dd \<notin> domains s \<and> dd \<notin> domains s' \<or> dd \<in> domains s \<and> d_id dd = d \<and> dd \<in> domains s'"
              using a2 a3 p1 by blast }
          then have "\<forall>da. d_id da \<noteq> d \<or> da \<notin> domains s \<and> da \<notin> domains s' \<or> da \<in> domains s \<and> d_id da = d \<and> da \<in> domains s'"
            by metis
          then show ?thesis
            by meson
        qed
      have c4: "get_domain_from_st_by_id s d = Some(SOME p. p \<in> domains s \<and> d_id p = d)"
        using c1 get_domain_from_st_by_id_def by auto
      have c5: "(\<exists>p. p \<in> domains s' \<and> d_id p = d)"
        using p1 a2 a3 c1 c2 c3 c4 by auto
      have c6: "get_domain_from_st_by_id s' d = Some(SOME p. p \<in> domains s' \<and> d_id p = d)"
        using c5 get_domain_from_st_by_id_def by auto
      have b10: "get_domain_from_st_by_id s d = get_domain_from_st_by_id s' d"
        using c3 c4 c5 c6 by auto
      then show ?thesis by auto
    qed
  qed

lemma grt_cap_grt_notchg_domain_ports:
  assumes p0:"reachable0 s"
    and   p1: "a = Grant_Cap did dst_id cap"
    and   p3:"\<not>(d = the(grant_dest_of_event a)) "
    and   p4:"s' = (grant_cap s did dst_id cap)"
  shows   "get_domain_cfg_ports s d = get_domain_cfg_ports s' d"
  proof (cases "cap \<notin> get_domain_cfg_cap_set_by_id s did
            \<or> get_domain_from_st_by_id s did \<noteq> None
            \<or> get_domain_from_st_by_id s dst_id \<noteq> None")
    assume a0: "cap \<notin> get_domain_cfg_cap_set_by_id s did
            \<or> get_domain_from_st_by_id s did \<noteq> None
            \<or> get_domain_from_st_by_id s dst_id \<noteq> None"
    have a1: "s' = s"
      using a0 p4 grant_cap_def by auto
    then show ?thesis by auto
  next
    assume a0: "\<not> (cap \<notin> get_domain_cfg_cap_set_by_id s did
            \<or> get_domain_from_st_by_id s did \<noteq> None
            \<or> get_domain_from_st_by_id s dst_id \<noteq> None)"
    have a1: "dst_id = the(grant_dest_of_event a)"
      using p1 grant_dest_of_event_def by auto
    have a2: "dst_id \<noteq> d"
      using a1 p3 by auto
    have a3:"{dom. dom\<in>domains s \<and> d_id dom \<noteq> dst_id} = {dom. dom\<in>domains s' \<and> d_id dom \<noteq> dst_id}"
      using a0 p4 grant_cap_def by auto
    show ?thesis
    proof (cases "\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)")
      assume c0: "\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)"
      have c1: "get_domain_from_st_by_id s d = None"
        using c0 get_domain_from_st_by_id_def by auto
      have c2: "(\<forall>p. p \<in> domains s \<longrightarrow> d_id p \<noteq> d)"
        using c0 by auto
      have c3: "(\<forall>p. p \<in> domains s' \<longrightarrow> d_id p \<noteq> d)"
        using p1 a3 a2 c2 by auto
      have c4: "\<not> (\<exists>p. p \<in> domains s' \<and> d_id p = d)"
        using c3 by auto
      have c5: "get_domain_from_st_by_id s' d = None"
        using c4 get_domain_from_st_by_id_def by auto
      have c6: "get_domain_cfg_ports s d = {}"
        using c1 get_domain_cfg_ports_def by auto
      have c7: "get_domain_cfg_ports s' d = {}"
        using c5 get_domain_cfg_ports_def by auto
      show ?thesis
        using c6 c7 by auto
    next
      assume c0: "\<not>\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)"
      have c1: "(\<exists>p. p \<in> domains s \<and> d_id p = d)"
        using c0 by auto
      have c2: "\<exists>p. p \<in> domains s \<and> d_id p = d \<longrightarrow> p \<in> domains s'"
        using a2 a3 p1 by auto
      have c3: "(SOME p. p \<in> domains s \<and> d_id p = d) = (SOME p. p \<in> domains s' \<and> d_id p = d)"
        proof -
          { fix dd :: Domain
            have "d_id dd \<noteq> d \<or> dd \<notin> domains s \<and> dd \<notin> domains s' \<or> dd \<in> domains s \<and> d_id dd = d \<and> dd \<in> domains s'"
              using a2 a3 p1 by blast }
          then have "\<forall>da. d_id da \<noteq> d \<or> da \<notin> domains s \<and> da \<notin> domains s' \<or> da \<in> domains s \<and> d_id da = d \<and> da \<in> domains s'"
            by metis
          then show ?thesis
            by meson
        qed
      have c4: "get_domain_from_st_by_id s d = Some(SOME p. p \<in> domains s \<and> d_id p = d)"
        using c1 get_domain_from_st_by_id_def by auto
      have c5: "(\<exists>p. p \<in> domains s' \<and> d_id p = d)"
        using p1 a2 a3 c1 c2 c3 c4 by auto
      have c6: "get_domain_from_st_by_id s' d = Some(SOME p. p \<in> domains s' \<and> d_id p = d)"
        using c5 get_domain_from_st_by_id_def by auto
      have c7: "get_domain_from_st_by_id s d = get_domain_from_st_by_id s' d"
        using c3 c4 c5 c6 by auto
      have c8: "get_domain_from_st_by_id s' d \<noteq> None"
        using c6 by auto
      have c9: "get_domain_from_st_by_id s d \<noteq> None"
        using c4 by auto
      have c10: "d_ports (the (get_domain_from_st_by_id s d)) 
                  = d_ports (the (get_domain_from_st_by_id s' d))"
        using c7 by auto
      have c11: "get_domain_cfg_ports s d 
                  = d_ports (the (get_domain_from_st_by_id s d))"
        using c9 get_domain_cfg_ports_def by auto
      have c12: "get_domain_cfg_ports s' d 
                  = d_ports (the (get_domain_from_st_by_id s' d))"
        using c8 get_domain_cfg_ports_def by auto
      show ?thesis
        using c10 c11 c12 by auto
    qed
  qed  


lemma grt_cap_grt_lcl_resp:
  assumes p0:"reachable0 s"
    and   p1: "a = Grant_Cap did dst_id cap"
    and   p3:"\<not>(d = the(grant_dest_of_event a)) "
    and   p4:"s' = (grant_cap s did dst_id cap)"
  shows   "s \<sim> d \<sim> s'"
  proof -
  {
    have a0: "is_grant1 a"
      using is_grant1_def is_execute1_def p1 by auto
    have a1: "dst_id = the(grant_dest_of_event a)"
      using p1 grant_dest_of_event_def by auto
    have a2: "dst_id \<noteq> d"
      using a1 p3 by auto
    have a3: "get_domain_from_st_by_id s d = get_domain_from_st_by_id s' d"
      using p0 p1 p3 p4 grt_cap_grt_notchg_domain by auto
    have a4: "get_domain_cfg_ports s d = get_domain_cfg_ports s' d"
      using p0 p1 p3 p4 grt_cap_grt_notchg_domain_ports by auto
    have a4:  "s \<sim> d \<sim> s'"
      using a3 a4 by auto
    }
  then show ?thesis by auto
  qed

subsection{* Concrete unwinding condition of "weakly step consistent" *}

subsubsection{*proving "create queuing port" satisfying the "weakly step consistent" property*}

lemma domain_lcl_rsp_equal:
  assumes b1: "{dom. dom\<in>domains s \<and> d_id dom \<noteq> did} = {dom. dom\<in>domains s' \<and> d_id dom \<noteq> did}"
    and   b0: "did \<noteq> d"
  shows   "get_domain_from_st_by_id s d = get_domain_from_st_by_id s' d"
  proof (cases "\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)")
    assume c0: "\<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)"
    have c1: "get_domain_from_st_by_id s d = None"
      using c0 get_domain_from_st_by_id_def by auto
    have c6: "(\<forall>p. p \<in> domains s \<longrightarrow> d_id p \<noteq> d)"
      using c0 by auto
    have c7: "(\<forall>p. p \<in> domains s' \<longrightarrow> d_id p \<noteq> d)"
      using b0 c6 b1 by auto  
    have c8: "\<not> (\<exists>p. p \<in> domains s' \<and> d_id p = d)"
      using c7 by auto
    have c9: "get_domain_from_st_by_id s' d = None"
      using c8 get_domain_from_st_by_id_def by auto
    show ?thesis
      using c9 c1 by auto
  next
    assume c0: "\<not> \<not> (\<exists>p. p \<in> domains s \<and> d_id p = d)"
    have c1: "(\<exists>p. p \<in> domains s \<and> d_id p = d)"
      using c0 by auto
    have c5: "\<exists>p. p \<in> domains s \<and> d_id p = d \<longrightarrow> p \<in> domains s'"
      using b1 b0 by auto
    have c6: "(SOME p. p \<in> domains s \<and> d_id p = d) = (SOME p. p \<in> domains s' \<and> d_id p = d)"
      proof -
        { fix dd :: Domain
          have "d_id dd \<noteq> d \<or> dd \<notin> domains s \<and> dd \<notin> domains s' \<or> dd \<in> domains s \<and> d_id dd = d \<and> dd \<in> domains s'"
            using b1 b0 by blast }
        then have "\<forall>da. d_id da \<noteq> d \<or> da \<notin> domains s \<and> da \<notin> domains s' \<or> da \<in> domains s \<and> d_id da = d \<and> da \<in> domains s'"
          by metis
        then show ?thesis
          by meson
      qed
    have c7: "get_domain_from_st_by_id s d = Some(SOME p. p \<in> domains s \<and> d_id p = d)"
      using c1 get_domain_from_st_by_id_def by auto  
    have c8: "(\<exists>p. p \<in> domains s' \<and> d_id p = d)"
      using b0 b1 c1 c5 c6 by auto
    have c9: "get_domain_from_st_by_id s' d = Some(SOME p. p \<in> domains s' \<and> d_id p = d)"
      using c8 get_domain_from_st_by_id_def by auto
    have c10: "get_domain_from_st_by_id s d = get_domain_from_st_by_id s' d"
      using c7 c9 c6 by auto
    then show ?thesis by auto
  qed

  lemma crt_que_port_wsc_domain:
   assumes p0:"reachable0 s"
    and   p1: "a = Create_Queuing_Port did port_name"
    and   p2: "s \<sim> d \<sim> t"
    and   p3: "s \<sim> did \<sim> t "
    and   p4: "s' = fst (create_queuing_port s did pname)"
    and   p5: "t' = fst (create_queuing_port t did pname)"
  shows   "get_domain_from_st_by_id s' d = get_domain_from_st_by_id t' d"
  proof (cases "get_domain_from_st_by_id s did = None")
    assume a0: "get_domain_from_st_by_id s did = None"
    have a1: "get_domain_from_st_by_id s did = get_domain_from_st_by_id t did"
      by (meson p3 vpeq1_def)
    have a2: "get_domain_from_st_by_id t did = None"
      using a0 a1 by auto
    have a3: "s' = s"
      using p4 a0 create_queuing_port_def by auto
    have a4: "t' = t"
      using p5 a2 create_queuing_port_def by auto
    have a5: "get_domain_from_st_by_id s d = get_domain_from_st_by_id t d"
      by (meson p2 vpeq1_def)
    then show ?thesis
      using a3 a4 p2 by auto
  next
    assume a0: "get_domain_from_st_by_id s did \<noteq> None"
    have a1: "get_domain_from_st_by_id s did = get_domain_from_st_by_id t did"
      by (meson p3 vpeq1_def)
    have a2: "get_domain_from_st_by_id t did \<noteq> None"
      using a0 a1 by auto
    have a3: "get_domain_from_st_by_id s d = get_domain_from_st_by_id t d"
      by (meson p2 vpeq1_def)
    show ?thesis
    proof (cases "did \<noteq> d")
      assume b0: "did \<noteq> d"
      have b1: "{dom. dom\<in>domains s \<and> d_id dom \<noteq> did} = {dom. dom\<in>domains s' \<and> d_id dom \<noteq> did}"
        using a0 p4 create_queuing_port_def by auto
      have b2: "{dom. dom\<in>domains t \<and> d_id dom \<noteq> did} = {dom. dom\<in>domains t' \<and> d_id dom \<noteq> did}"
        using a0 p5 create_queuing_port_def by auto
      have b3: "get_domain_from_st_by_id s d = get_domain_from_st_by_id s' d"
        using b1 b0 domain_lcl_rsp_equal by blast
      have b4: "get_domain_from_st_by_id t d = get_domain_from_st_by_id t' d"
        using b2 b0 domain_lcl_rsp_equal by blast
      have b5: "get_domain_from_st_by_id s' d = get_domain_from_st_by_id t' d"
        using b3 b4 a3 by auto
      then show ?thesis by auto
    next
      assume b0: "\<not> did \<noteq> d"
      have b1: "did = d"
        using b0 by auto
      have b2: "get_domain_from_st_by_id s did 
              = Some (SOME p. p \<in> domains s \<and> d_id p = did)"
        proof -
          obtain dd :: "State \<Rightarrow> nat \<Rightarrow> Domain" where
            "\<And>s n d sa na. (d_id (dd s n) = n \<or> get_domain_from_st_by_id s n = None) \<and> (dd s n \<in> domains s \<or> get_domain_from_st_by_id s n = None) \<and> (d \<notin> domains sa \<or> d_id d \<noteq> na \<or> get_domain_from_st_by_id sa na = Some (SOME d. d \<in> domains sa \<and> d_id d = na))"
            using get_domain_from_st_by_id_def by moura
          then show ?thesis
            by (meson a0)
        qed
      have b3: "get_domain_from_st_by_id t did 
              = Some (SOME p. p \<in> domains t \<and> d_id p = did)"
        proof -
          obtain dd :: "State \<Rightarrow> nat \<Rightarrow> Domain" where
            "\<And>s n d sa na. (d_id (dd s n) = n \<or> get_domain_from_st_by_id s n = None) \<and> (dd s n \<in> domains s \<or> get_domain_from_st_by_id s n = None) \<and> (d \<notin> domains sa \<or> d_id d \<noteq> na \<or> get_domain_from_st_by_id sa na = Some (SOME d. d \<in> domains sa \<and> d_id d = na))"
            using get_domain_from_st_by_id_def by moura
          then show ?thesis
            by (meson a2)
        qed
      have b4: "Some (SOME p. p \<in> domains s \<and> d_id p = did) = Some (SOME p. p \<in> domains t \<and> d_id p = did)"
        using b2 b3 a1 by auto
      have c1: "domains s = domains s'"
        using a0 p4 create_queuing_port_def by auto
      have c2: "\<forall> d1 d2. d1\<in>domains s \<and> d_id d1 = did \<and> d_id d2 =did \<and> d2\<in>domains s'
            \<longrightarrow> d1 = d2"
        using c1 by auto
      have b5: "\<exists>d1 d2. (d1\<in>domains s \<and> d2 \<in> domains s'
            \<longrightarrow> d_ports d1 =  d_ports d2)"
        using a0 p4 create_queuing_port_def by auto
      have b6: "\<forall>d1. \<exists>d2. d1 \<in> {dom. dom\<in>domains s \<and> d_id dom = did }
                \<and> d2 \<in> {dom. dom\<in>domains t \<and> d_id dom = did }
                \<longrightarrow> d1 = d2"
        using b4 by auto
      have b7: "\<exists>d1 d2. d1 \<in> {dom. dom\<in>domains s \<and> d_id dom = did }
                \<and> d2 \<in> {dom. dom\<in>domains t \<and> d_id dom = did }
                \<longrightarrow> d_ports d1 = d_ports d2"
        by auto
      have b8: "\<exists>d1 d2. d1\<in>domains s \<and> d_id d1 = did \<and> d2 \<in> domains s' \<and> d_id d2 = did
            \<longrightarrow> d1 = d2"
        using a0 p4 create_queuing_port_def by auto
      have b9: "Some (SOME p. p \<in> domains s \<and> d_id p = did) = Some (SOME p. p \<in> domains s' \<and> d_id p = did)"
        using b5 by auto
      have b15: "\<exists>d1 d2. d1\<in>domains s \<and> d_id d1 = did \<and> d2 \<in> domains s' \<and> d_id d2 = did
            \<longrightarrow> d_ports d2 = d_ports d1 \<union> {next_port_id s}"
        using a0 p4 create_queuing_port_def by auto
      have b15: "\<forall>dom dom'. dom\<in>domains s \<and> d_id dom =  d_id dom' \<and> dom'\<in>domains s'
                \<longrightarrow> d_ports dom \<subseteq> d_ports dom'"
        using a0 p4 create_queuing_port_def by auto
      have b15: "d_ports ((SOME p. p \<in> domains s \<and> d_id p \<noteq> did)) 
              \<subseteq> d_ports ((SOME p. p \<in> domains s' \<and> d_id p \<noteq> did))"
        using a0 b0 p4 create_queuing_port_def by auto1
      show ?thesis

      have b5: "{d. d\<in>domains s \<and> d_id d = did} = {d. d\<in>domains t \<and> d_id d = did}"
        using b4  
      
      

(*
by1 (smt SM.intro SM_enabled.intro SM_enabled_axioms.intro grant_exclusive1 s0t_init taint_set_respect_lemma1 vpeq1_def vpeq1_symmetric_lemma)
*)
end