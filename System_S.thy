theory System_S
imports Main
begin
subsection {* Capability Model *}

type_synonym compartment_id = nat
type_synonym entity_id = nat

datatype
  right = Taint
          |Endorse
          |Grant
          |Declassify
          |Export

record cap = 
  target :: compartment_id
  rights :: "right set"

datatype entity = Entity "cap set"

type_synonym state = "entity_id \<Rightarrow> entity option"

definition diminish :: "right set \<Rightarrow> cap \<Rightarrow> cap" where
  "diminish R cap \<equiv> cap \<lparr> rights := rights cap \<inter> R \<rparr>"

definition direct_caps :: "entity \<Rightarrow> cap set"
where
  "direct_caps e \<equiv> case e of (Entity c) \<Rightarrow> c"

definition direct_caps_of :: "state \<Rightarrow> entity_id \<Rightarrow> cap set"
where
  "direct_caps_of s p \<equiv>
  case s p of
    None \<Rightarrow> {}
  | Some (Entity e) \<Rightarrow> e"

definition cap_connected :: "state \<Rightarrow> (entity_id \<times> compartment_id) set" where
  "cap_connected s \<equiv>{(e,comp).  \<exists>cap. cap \<in> direct_caps_of s e \<and>
                                      target cap = comp}"

definition taint_cap :: "entity_id \<Rightarrow> cap" where
  "taint_cap e\<^sub>x \<equiv> \<lparr>target = e\<^sub>x, rights = {Taint}\<rparr>"

definition endorse_cap :: "entity_id \<Rightarrow> cap" where
  "endorse_cap e\<^sub>x \<equiv> \<lparr>target = e\<^sub>x, rights = {Endorse}\<rparr>"

definition grant_cap :: "entity_id \<Rightarrow> cap" where
  "grant_cap e\<^sub>x \<equiv> \<lparr>target = e\<^sub>x, rights = {Grant}\<rparr>"

definition declassify_cap :: "entity_id \<Rightarrow> cap" where
  "declassify_cap e\<^sub>x \<equiv> \<lparr>target = e\<^sub>x, rights = {Declassify}\<rparr>"

definition export_cap :: "entity_id \<Rightarrow> cap" where
  "export_cap e\<^sub>x \<equiv> \<lparr>target = e\<^sub>x, rights = {Export}\<rparr>"

subsection {* DIFC Model *}

definition taint_set :: "state \<Rightarrow> entity_id \<Rightarrow> compartment_id set" where
  "taint_set s e \<equiv> {comp. \<forall>cap. cap \<in> direct_caps_of s e \<and> Taint \<in> rights cap}"

definition taint_dominate :: "state \<Rightarrow> entity_id \<Rightarrow> entity_id \<Rightarrow> bool" where
  "taint_dominate s e\<^sub>x e\<^sub>y \<equiv>( taint_set s e\<^sub>x \<subseteq> taint_set s e\<^sub>y )"

definition can_send :: "state \<Rightarrow> entity_id \<Rightarrow> entity_id \<Rightarrow> bool" where
  "can_send s e\<^sub>x e\<^sub>y \<equiv> ( taint_set s e\<^sub>x \<subseteq> taint_set s e\<^sub>y )"

definition can_declassfy_send :: "state \<Rightarrow> entity_id \<Rightarrow> entity_id \<Rightarrow> cap \<Rightarrow> bool"
  where
        "can_declassfy_send s e_src e_dst declassfy_cap \<equiv>
            (declassfy_cap \<in> direct_caps_of s e_src 
              \<and> taint_set s e_src - {target declassfy_cap} \<subseteq> taint_set s e_dst )"
                                         
definition can_export_send :: "state \<Rightarrow> entity_id \<Rightarrow> entity_id \<Rightarrow> cap \<Rightarrow> bool"
  where
        "can_export_send s e_src e_dst export_cap_s \<equiv>
            (export_cap_s \<in> direct_caps_of s e_src 
              \<and> taint_set s e_src \<union> {target export_cap_s} \<subseteq> taint_set s e_dst )"

end
