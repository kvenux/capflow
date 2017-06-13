theory take_grant_cap
imports Dynamic_model_v3
begin

subsection {* Definitions *}

type_synonym domain_id = nat
type_synonym domain_name = string

datatype
  right = ENDPOINT
          |TAKE
          |GRANT

record cap = 
  target :: domain_id
  rights :: "right set"

record State = 
  cap_by_id :: "domain_id \<rightharpoonup> (cap set)"

definition get_caps_by_id :: "State \<Rightarrow> domain_id \<Rightarrow> (cap set)"
  where "get_caps_by_id s did \<equiv>
        if((cap_by_id s) did = None)
        then
          {}
        else
          the((cap_by_id s) did)"

definition grant_action :: "State \<Rightarrow> domain_id \<Rightarrow> domain_id \<Rightarrow> cap \<Rightarrow> State"
  where "grant_action s did did_dst dst_cap \<equiv> 
         
           if(
              (\<exists>c. c\<in>get_caps_by_id s did \<and> target c = did_dst \<and> GRANT\<in>rights c)
              \<and> dst_cap\<in>get_caps_by_id s did)
           then
             let
               cs0 = get_caps_by_id s did;
               cs_dst = get_caps_by_id s did_dst;
               cap_by_id0 = (cap_by_id s);
               granted_cap = \<lparr> target = target dst_cap,
                             rights = {ENDPOINT} \<rparr>
             in
             s\<lparr>
                cap_by_id := cap_by_id0(did_dst := Some (insert granted_cap cs_dst))
              \<rparr>
           else                                             
             s"

definition interferes :: "domain_id \<Rightarrow> State \<Rightarrow> domain_id \<Rightarrow> bool"
  where "interferes w s v \<equiv> 
        if( w = v
            \<or> (\<exists>c. c\<in>(get_caps_by_id s w) \<and> target c = v))
        then
          True
        else
          False
        "

definition vpeq1 :: "State \<Rightarrow> domain_id \<Rightarrow> State \<Rightarrow> bool" ("(_ \<sim> _ \<sim> _)") 
  where
    "vpeq1 s d t \<equiv> 
       let
         cs1 = get_caps_by_id s d;
         cs2 = get_caps_by_id t d
       in
       if(cs1 = cs2
          \<and> (\<forall>v. interferes v s d \<longleftrightarrow> interferes v t d))
       then
         True
       else
         False
       "

lemma get_caps_lcl_resp:                                                            
  assumes p1:"\<not>interferes did s d "
    and   p2:"s' = grant_action s did did_dst dst_cap"
  shows   "s \<sim> d \<sim> s'"
  proof (cases "\<not>((\<exists>c. c\<in>get_caps_by_id s did \<and> target c = did_dst \<and> GRANT\<in>rights c)
              \<and> dst_cap\<in>get_caps_by_id s did)")
    assume a0: "\<not>((\<exists>c. c\<in>get_caps_by_id s did \<and> target c = did_dst \<and> GRANT\<in>rights c)
              \<and> dst_cap\<in>get_caps_by_id s did)"
    have a1: "s' = s"
      using a0 p2 grant_action_def by auto
    then show ?thesis 
      using vpeq1_def by auto
  next
    assume a0: "\<not>\<not>((\<exists>c. c\<in>get_caps_by_id s did \<and> target c = did_dst \<and> GRANT\<in>rights c)
              \<and> dst_cap\<in>get_caps_by_id s did)"
    have a1: "((\<exists>c. c\<in>get_caps_by_id s did \<and> target c = did_dst \<and> GRANT\<in>rights c)
              \<and> dst_cap\<in>get_caps_by_id s did)"
      using a0 by auto
    have a2: "\<forall>v. v\<noteq>did_dst
              \<longrightarrow> (cap_by_id s') v = (cap_by_id s) v"
      using a1 p2 grant_action_def by auto
    have a3: "d \<noteq> did"
      using p1 interferes_def by auto
    have a4: "\<forall>c. c\<in>(get_caps_by_id s did)
              \<longrightarrow> target c \<noteq> d"
      using interferes_def p1 by presburger
    have a5: "d \<noteq> did_dst"
      using a1 a4 by auto
    have a6: "(cap_by_id s') d = (cap_by_id s) d"
      using a2 a5 by auto
    have a7: "get_caps_by_id s' d = get_caps_by_id s d"
      using a6 get_caps_by_id_def by auto
    have a8:"\<forall>v. v\<noteq>did_dst
              \<longrightarrow> get_caps_by_id s v = get_caps_by_id s' v"
      using a2 get_caps_by_id_def by auto    
    have a9:"\<forall>v. v\<noteq>did_dst
              \<longrightarrow> interferes v s d = interferes v s' d"
      using a8 interferes_def by auto
    let ?granted_cap = "\<lparr> target = target dst_cap,
                             rights = {ENDPOINT} \<rparr>"
    have a10: "get_caps_by_id s' did_dst = {?granted_cap} \<union> get_caps_by_id s did_dst"
      using a1 p2 grant_action_def get_caps_by_id_def by auto
    have a11: "dst_cap\<in>get_caps_by_id s did"
      using a1 by auto
    have a12: "target ?granted_cap \<noteq> d"
      using a11 a4 by auto
    have a13: "interferes did_dst s d = interferes did_dst s' d"
      using a10 a12 interferes_def by auto
    have a14: "\<forall>v. interferes v s d = interferes v s' d"
      using a9 a13 by auto
    then show ?thesis
      using a14 a7 vpeq1_def by auto
  qed

 lemma crt_que_port_wsc_domain:
   assumes  p1: "interferes did s d"
    and     p2: "s \<sim> d \<sim> t"
    and     p3: "s \<sim> did \<sim> t "
    and     p4: "s' = grant_action s did did_dst dst_cap"
    and     p5: "t' = grant_action t did did_dst dst_cap"
  shows   "s' \<sim> d \<sim> t'"
  proof (cases "\<not>((\<exists>c. c\<in>get_caps_by_id s did \<and> target c = did_dst \<and> GRANT\<in>rights c)
              \<and> dst_cap\<in>get_caps_by_id s did)")
    assume a0: "\<not>((\<exists>c. c\<in>get_caps_by_id s did \<and> target c = did_dst \<and> GRANT\<in>rights c)
              \<and> dst_cap\<in>get_caps_by_id s did)"
    have a1: "get_caps_by_id s did = get_caps_by_id t did"
      by (meson p3 vpeq1_def)
    have a2: "\<not>((\<exists>c. c\<in>get_caps_by_id t did \<and> target c = did_dst \<and> GRANT\<in>rights c)
              \<and> dst_cap\<in>get_caps_by_id t did)"
      using a0 a1 by auto
    have a3: "s' = s"
      using a0 p4 grant_action_def by auto
    have a4: "t' = t"
      using a2 p5 grant_action_def by auto
    show ?thesis
      using a3 a4 p2 by auto
  next
    assume a0: "\<not>\<not>((\<exists>c. c\<in>get_caps_by_id s did \<and> target c = did_dst \<and> GRANT\<in>rights c)
              \<and> dst_cap\<in>get_caps_by_id s did)"
    have a1: "get_caps_by_id s did = get_caps_by_id t did"
      by (meson p3 vpeq1_def)
    have a2: "((\<exists>c. c\<in>get_caps_by_id t did \<and> target c = did_dst \<and> GRANT\<in>rights c)
              \<and> dst_cap\<in>get_caps_by_id t did)"
      using a0 a1 by auto
    let ?granted_cap = "\<lparr> target = target dst_cap,
                             rights = {ENDPOINT} \<rparr>"
    have a3: "\<forall>v. v\<noteq>did_dst
              \<longrightarrow> (cap_by_id s') v = (cap_by_id s) v"
      using a1 p4 grant_action_def by auto
    have a4:"\<forall>v. v\<noteq>did_dst
              \<longrightarrow> get_caps_by_id s v = get_caps_by_id s' v"
      using a3 get_caps_by_id_def by auto  
    have a5: "get_caps_by_id s' did_dst = {?granted_cap} \<union> get_caps_by_id s did_dst"
      using a0 p4 grant_action_def get_caps_by_id_def by auto
    have a6: "\<forall>v. v\<noteq>did_dst
              \<longrightarrow> (cap_by_id t') v = (cap_by_id t) v"
      using a2 p5 grant_action_def by auto
    have a7:"\<forall>v. v\<noteq>did_dst
              \<longrightarrow> get_caps_by_id t v = get_caps_by_id t' v"
      using a6 get_caps_by_id_def by auto
    have a8: "get_caps_by_id t' did_dst = {?granted_cap} \<union> get_caps_by_id t did_dst"
      using a2 p5 grant_action_def get_caps_by_id_def by auto
    show ?thesis
    proof (cases "d = did_dst")
      assume b0: "d = did_dst"
      have b1: "get_caps_by_id s d = get_caps_by_id t d"
        by (meson p2 vpeq1_def)
      have b2: "get_caps_by_id s' d = get_caps_by_id t' d"
        using a5 a8 b0 b1 by auto
      have b3:"\<forall>v. v\<noteq>did_dst
              \<longrightarrow> interferes v s d = interferes v s' d"
        using a4 interferes_def by auto
      have b4:"\<forall>v. v\<noteq>did_dst
              \<longrightarrow> interferes v t d = interferes v t' d"
        using a7 interferes_def by auto
      have b5: "\<forall>v. interferes v s d = interferes v t d"
        by (meson p2 vpeq1_def)
      have b6: "\<forall>v. v\<noteq>did_dst
              \<longrightarrow> interferes v s' d = interferes v t' d"
        using b3 b4 b5 by auto
      have b7: "interferes did_dst s' d = interferes did_dst t' d"
        using b0 interferes_def by auto
      have b8: "\<forall>v. interferes v s' d = interferes v t' d"
        using b6 b7 by auto
      then show ?thesis
        using b2 vpeq1_def by auto
    next
      assume b0: "d \<noteq> did_dst"
      have b1: "get_caps_by_id s' d = get_caps_by_id s d"
        using a4 b0 by auto
      have b2: "get_caps_by_id t' d = get_caps_by_id t d"
        using a7 b0 by auto
      have b3: "get_caps_by_id s d = get_caps_by_id t d"
        by (meson p2 vpeq1_def)
      have b4: "get_caps_by_id s' d = get_caps_by_id t' d"
        using b1 b2 b3 by auto
      have b5: "\<forall>v. interferes v s d = interferes v t d"
        by (meson p2 vpeq1_def)
      have b6:"\<forall>v. v\<noteq>did_dst
              \<longrightarrow> interferes v s d = interferes v s' d"
        using a4 interferes_def by auto
      have b7:"\<forall>v. v\<noteq>did_dst
              \<longrightarrow> interferes v t d = interferes v t' d"
        using a7 interferes_def by auto
      have b8: "\<forall>v. v\<noteq>did_dst
              \<longrightarrow> interferes v s' d = interferes v t' d"
        using b5 b6 b7 by auto
      have b9: "interferes did_dst s d = interferes did_dst t d"
        using b5 by auto
      have b10: "interferes did_dst s' d = interferes did_dst t' d"
      proof (cases "interferes did_dst s d")
        assume c0: "interferes did_dst s d"
        have c1: "interferes did_dst t d"
          using c0 b9 by auto
        have c2: "( did_dst = d
            \<or> (\<exists>c. c\<in>(get_caps_by_id s did_dst) \<and> target c = d))"
          by (meson c0 interferes_def)
        have c3: "(\<exists>c. c\<in>(get_caps_by_id s did_dst) \<and> target c = d)"
          using c2 b0 by auto
        have c4: "(\<exists>c. c\<in>(get_caps_by_id s' did_dst) \<and> target c = d)"
          using a5 c3 by auto
        have c5: "interferes did_dst s' d"
          using c4 interferes_def by auto
        have c6: "( did_dst = d
            \<or> (\<exists>c. c\<in>(get_caps_by_id t did_dst) \<and> target c = d))"
          by (meson c1 interferes_def)
        have c7: "(\<exists>c. c\<in>(get_caps_by_id t did_dst) \<and> target c = d)"
          using c6 b0 by auto
        have c8: "(\<exists>c. c\<in>(get_caps_by_id t' did_dst) \<and> target c = d)"
          using a8 c7 by auto
        have c9: "interferes did_dst t' d"
          using c8 interferes_def by auto
        have c10: "interferes did_dst s' d = interferes did_dst t' d"
          using c5 c9 by auto
        then show ?thesis by auto
      next
        assume c0: "\<not>interferes did_dst s d"
        have c1: "\<not>interferes did_dst t d"
          using c0 b9 by auto
        have c2: "\<not>(did_dst = d
            \<or> (\<exists>c. c\<in>(get_caps_by_id s did_dst) \<and> target c = d))"
          using c0 interferes_def by force
        have c3: "\<forall>c. c\<in>(get_caps_by_id s did_dst)
            \<longrightarrow> target c \<noteq> d"
          using c2 by auto
        have c4: "\<not>(did_dst = d
            \<or> (\<exists>c. c\<in>(get_caps_by_id t did_dst) \<and> target c = d))"
          using c1 interferes_def by force
        have c5: "\<forall>c. c\<in>(get_caps_by_id t did_dst)
            \<longrightarrow> target c \<noteq> d"
          using c4 by auto
        show ?thesis
        proof (cases "d = target ?granted_cap")
          assume d0: "d = target ?granted_cap"
          have d1: "interferes did_dst s' d"
            using a5 d0 interferes_def by auto
          have d2: "interferes did_dst t' d"
            using a8 d0 interferes_def by auto
          show ?thesis
            using d1 d2 by auto
        next
          assume d0: "d \<noteq> target ?granted_cap"
          have d1: "\<not>interferes did_dst s' d"
            using a5 d0 c3 b0 interferes_def by auto
          have d2: "\<not>interferes did_dst t' d"
            using a8 d0 c5 b0 interferes_def by auto
          show ?thesis
            using d1 d2 by auto
        qed
      qed
      have b11: "\<forall>v. interferes v s' d = interferes v t' d"
        using b10 b8 by auto
      then show ?thesis
        using b4 vpeq1_def by auto
    qed
  qed

end
