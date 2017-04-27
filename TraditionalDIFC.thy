theory TraditionalDIFC
imports DynamicSecurityModel
begin
subsection {* Definitions *}

typedecl Message
type_synonym tag_id = nat
datatype tag_type = SECRECY | INTEGRITY
record tag =           
  id :: tag_id
  type :: tag_type   

type_synonym domain_id = nat
type_synonym domain_name = string

datatype
  right = TAG_ADD
          |TAG_REMOVE

record cap = 
  target :: tag_id
  rights :: "right set"     
                            
record label = 
  tags :: "tag set"

record domain = 
  id_of_domain :: domain_id
  label_of_domain :: label
  cap_config :: "cap set"

datatype Domain_Conf = DomainConf domain_id domain_name
                           
type_synonym Domains = "domain_id \<rightharpoonup> Domain_Conf"

record State = 
  domains :: "domain set"
  next_tag_id :: tag_id

record Sys_Config = 
  domain_conf :: Domains

consts sysconf :: "Sys_Config" 

definition system_init :: "Sys_Config \<Rightarrow> State"
  where "system_init sc \<equiv> \<lparr>domains = {},
                           next_tag_id = 0\<rparr>"

subsection {* Events *}

datatype Event = Create_Tag domain_id tag_type
                   |Change_Label domain_id tag_type label
                   |Get_Label domain_id
                   |Get_Caps domain_id
                   |Send_Message domain_id domain_id Message

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

definition get_label_by_domain_id :: "State \<Rightarrow> domain_id \<Rightarrow> label option " where
  "get_label_by_domain_id s domain_id  \<equiv>
            (if ((get_domain s domain_id) \<noteq> None )
            then Some (SOME lb. \<exists>d. d \<in> (domains s) \<and> id_of_domain d = domain_id \<and> lb = label_of_domain d)
            else None   
            )"

definition get_secrecy_label_by_domain_id :: "State \<Rightarrow> domain_id \<Rightarrow> label option " where
  "get_secrecy_label_by_domain_id s d_id  \<equiv>
            (if ((get_domain s d_id) \<noteq> None )
            then 
              let
                dom = the (get_domain s d_id);
                lbl = label_of_domain dom;
                tag_set = tags lbl
              in
                Some (\<lparr>tags = {tg. tg \<in> tag_set \<and> type tg = SECRECY}\<rparr>)
            else None   
            )"

definition get_integrity_label_by_domain_id :: "State \<Rightarrow> domain_id \<Rightarrow> label option " where
  "get_integrity_label_by_domain_id s d_id  \<equiv>
            (if ((get_domain s d_id) \<noteq> None )
            then 
              let
                dom = the (get_domain s d_id);
                lbl = label_of_domain dom;
                tag_set = tags lbl
              in
                Some (\<lparr>tags = {tg. tg \<in> tag_set \<and> type tg = INTEGRITY}\<rparr>)
            else None   
            )"

definition get_label :: "State \<Rightarrow> domain_id \<Rightarrow> (State \<times> label option) " where
  "get_label s domain_id \<equiv>
          (if (\<exists>d. d \<in> (domains s) \<and> id_of_domain d = domain_id )
          then (s, get_label_by_domain_id s domain_id )
          else (s, None)                             
          )"

definition get_caps_by_domain_id :: "State \<Rightarrow> domain_id \<Rightarrow> cap set option " where
  "get_caps_by_domain_id s domain_id  \<equiv>
            (if ((get_domain s domain_id) \<noteq> None )
            then Some (SOME cap_s. \<exists>d. d \<in> (domains s) \<and> id_of_domain d = domain_id \<and> cap_s = cap_config d)
            else None                   
            )"

definition get_add_caps_from :: "cap set \<Rightarrow> cap set" where
  "get_add_caps_from cs \<equiv> {c. c \<in> cs \<and> TAG_ADD \<in> rights c}"

definition get_addable_tag_ids_from :: "cap set \<Rightarrow> tag_id set" where
  "get_addable_tag_ids_from cs \<equiv> {t. \<exists>c. c \<in> cs \<and> TAG_ADD \<in> rights c \<and> t = target c }"

definition get_removable_tag_ids_from :: "cap set \<Rightarrow> tag_id set" where
  "get_removable_tag_ids_from cs \<equiv> {t. \<exists>c. c \<in> cs \<and> TAG_REMOVE \<in> rights c \<and> t = target c }"

definition get_caps :: "State \<Rightarrow> domain_id \<Rightarrow> (State \<times> (cap set) option) " where
  "get_caps s domain_id \<equiv>
          (if (\<exists>d. d \<in> (domains s) \<and> id_of_domain d = domain_id )
          then (s, Some (SOME lb. \<exists>d. d \<in> (domains s) \<and> id_of_domain d = domain_id \<and> lb = cap_config d))
          else (s, None)                             
          )"

definition create_tag_add_new_caps_to_domain :: "domain \<Rightarrow> cap set \<Rightarrow> domain" where
  "create_tag_add_new_caps_to_domain d cs \<equiv> 
          \<lparr> id_of_domain = id_of_domain d,
            label_of_domain = label_of_domain d,
            cap_config = cs \<union> (cap_config d)\<rparr>"


definition create_tag_add_new_caps_to_domain_1 :: "State \<Rightarrow> domain_id \<Rightarrow> cap set \<Rightarrow> domain" where
  "create_tag_add_new_caps_to_domain_1 s d_id cs \<equiv> 
          let d = the (get_domain s d_id)
          in
          \<lparr> id_of_domain = id_of_domain d,
            label_of_domain = label_of_domain d,
            cap_config = cs \<union> (cap_config d)\<rparr>"

definition create_tag_state_trans :: "State \<Rightarrow> domain_id \<Rightarrow> tag \<Rightarrow> State" where
  "create_tag_state_trans s d_id tag_1 \<equiv> 
          let rest_domains = {v. v\<in>domains s \<and> \<not> (id_of_domain v = d_id) };
              new_add_cap =  \<lparr> target = id tag_1,
                             rights = {TAG_ADD, TAG_REMOVE} \<rparr>;
              new_domain = create_tag_add_new_caps_to_domain_1 s d_id {new_add_cap}
          in
           \<lparr> domains = insert new_domain rest_domains,
             next_tag_id = next_tag_id s + 1 \<rparr>"

definition create_tag :: "State \<Rightarrow> domain_id \<Rightarrow> tag_type \<Rightarrow> (State \<times> tag option) " where
  "create_tag s domain_id tt \<equiv>
          if((tt = SECRECY \<or> tt = INTEGRITY) \<and> domain_id_is_valid s domain_id )
          then
            let newTag = \<lparr> id = next_tag_id s,
                          type = SECRECY \<rparr>;
                target_domain = get_domain s domain_id
            in (create_tag_state_trans s domain_id newTag, Some newTag)
          else
            (s, None)
          "
(*Change_Label domain_id tag_type label*)

definition is_domain_label_changable :: "State \<Rightarrow> domain_id \<Rightarrow> tag_type \<Rightarrow> label \<Rightarrow> bool"
  where
  "is_domain_label_changable s d_id tt lbl \<equiv>
          let cur_lbl = (the (get_label_by_domain_id s d_id));
              cur_cap_set = (the (get_caps_by_domain_id s d_id));
              cur_addable_tag_ids = get_addable_tag_ids_from cur_cap_set;
              cur_removable_tag_ids = get_removable_tag_ids_from cur_cap_set
          in
          if (tt = SECRECY \<or> tt = INTEGRITY)
          then
            if((\<forall>t. t\<in>tags lbl
                   \<and> \<not> (t\<in>tags cur_lbl)
                   \<and> (id t)\<in> cur_addable_tag_ids)
                \<or>
                (\<forall>t. \<not>(t\<in>tags lbl)
                   \<and> t\<in>tags cur_lbl
                   \<and> (id t)\<in> cur_addable_tag_ids))
            then
              True
            else
              False
          else
            False
  "

definition change_label_of_domain :: "State \<Rightarrow> domain_id \<Rightarrow> label \<Rightarrow> domain" where
  "change_label_of_domain s d_id lbl \<equiv> 
          let d = the (get_domain s d_id)         
          in
          \<lparr> id_of_domain = id_of_domain d,
            label_of_domain = lbl,
            cap_config = cap_config d\<rparr>"


definition change_label_state_trans :: "State \<Rightarrow> domain_id \<Rightarrow> tag_type \<Rightarrow> label \<Rightarrow> State" where
  "change_label_state_trans s d_id tt lbl \<equiv>
          let rest_domains = {v. v\<in>domains s \<and> \<not> (id_of_domain v = d_id) };
              new_domain = change_label_of_domain s d_id lbl
          in
           \<lparr> domains = insert new_domain rest_domains,
             next_tag_id = next_tag_id s\<rparr>"                 

definition change_label :: "State \<Rightarrow> domain_id \<Rightarrow> tag_type \<Rightarrow> label \<Rightarrow> (State \<times> bool ) " where
  "change_label s domain_id tt lbl \<equiv>
          if((tt = SECRECY \<or> tt = INTEGRITY)
              \<and> domain_id_is_valid s domain_id
              \<and> is_domain_label_changable s domain_id tt lbl)
          then (change_label_state_trans s domain_id tt lbl, True)
          else
            (s, False)
          "
definition send_message :: "State \<Rightarrow> domain_id \<Rightarrow> domain_id \<Rightarrow> Message \<Rightarrow> State"
  where
  "send_message s src_id dst_id m \<equiv>
        s
        "
                                                
definition exec_event :: "State \<Rightarrow> Event \<Rightarrow> State" where
  "exec_event s e  \<equiv>
    case e of  Create_Tag d_id tt \<Rightarrow> fst (create_tag s d_id tt)
               |Change_Label d_id tt lbl \<Rightarrow> fst (change_label s d_id tt lbl )
               |Get_Label d_id \<Rightarrow> fst (get_label s d_id)
               |Get_Caps d_id \<Rightarrow> fst (get_caps s d_id)
               |Send_Message src_id dst_id msg \<Rightarrow> s
               "
(*
definition dominates :: "label \<Rightarrow> label \<Rightarrow> bool"
*)

definition domain_of_event :: "Event \<Rightarrow> domain_id option"
  where
    "domain_of_event e \<equiv> 
          case e of  Create_Tag d_id tt \<Rightarrow> Some d_id
               |Change_Label d_id tt lbl \<Rightarrow> Some d_id
               |Get_Label d_id \<Rightarrow> Some d_id
               |Get_Caps d_id \<Rightarrow> Some d_id
               |Send_Message src_id dst_id msg \<Rightarrow> Some src_id
               "

definition interference1 :: "domain_id \<Rightarrow> State \<Rightarrow> domain_id \<Rightarrow> bool" ("(_ \<leadsto> _)")
    where                                                                                                  
      "interference1 d1 s d2 \<equiv>
          let
            secrecy_lbl1 = the (get_secrecy_label_by_domain_id s d1);
            secrecy_lbl2 = the (get_secrecy_label_by_domain_id s d2);
            integrity_lbl1 = the (get_integrity_label_by_domain_id s d1);
            integrity_lbl2 = the (get_integrity_label_by_domain_id s d2)
          in
          if d1 = d2 then True
          else if d1 \<noteq> d2
            then
              tags secrecy_lbl1 \<subseteq> tags secrecy_lbl2 \<and> 
              tags integrity_lbl1 \<subseteq> tags integrity_lbl2
          else False"             

definition vpeq1 :: "State \<Rightarrow> domain_id \<Rightarrow> State \<Rightarrow> bool"
  where
    "vpeq1 s d t \<equiv> 
        let
          d1 = get_domain s d;
          d2 = get_domain t d
        in
          if(d1 = d2)
          then
            True
          else
            False
          "

consts s0t :: State
definition s0t_witness :: State
  where "s0t_witness \<equiv> system_init sysconf"
specification (s0t) 
  s0t_init: "s0t = system_init sysconf"
  by simp

end