section {*Security Model of Separation Kernels*}
theory SK_SecurityModel
imports Main
begin

subsection {* Security State Machine *}

locale SM =
  fixes s0 :: 's
  fixes step :: "'e \<Rightarrow> ('s \<times> 's) set"
  fixes domain :: "'s \<Rightarrow> 'e \<Rightarrow> ('d option)"
  fixes sched :: 'd            
  fixes vpeq :: "'s \<Rightarrow> 'd \<Rightarrow> 's \<Rightarrow> bool"  ("(_ \<sim> _ \<sim> _)")
  fixes interference :: "'d \<Rightarrow> 'd \<Rightarrow> bool" ("(_ \<leadsto> _)")
  assumes 
    vpeq_transitive_lemma : "\<forall> s t r d. (s \<sim> d \<sim> t) \<and> (t \<sim> d \<sim> r) \<longrightarrow> (s \<sim> d \<sim> r)" and
    vpeq_symmetric_lemma : "\<forall> s t d. (s \<sim> d \<sim> t) \<longrightarrow> (t \<sim> d \<sim> s)" and
    vpeq_reflexive_lemma : "\<forall> s d. (s \<sim> d \<sim> s)" and
    sched_vpeq : "\<forall>s t a. (s \<sim> sched \<sim> t) \<longrightarrow> (domain s a) = (domain t a)" and
    sched_intf_all : "\<forall>d. (sched \<leadsto> d)" and
    no_intf_sched : "\<forall>d. (d \<leadsto> sched) \<longrightarrow> d = sched" and
    interf_reflexive: "\<forall>d. (d \<leadsto> d)"
begin
 
    definition non_interference :: "'d \<Rightarrow> 'd \<Rightarrow> bool" ("(_ \<setminus>\<leadsto> _)")
      where "(u \<setminus>\<leadsto>  v) \<equiv> \<not> (u \<leadsto> v)"
   
    definition ivpeq :: "'s \<Rightarrow> 'd set \<Rightarrow> 's \<Rightarrow> bool" ("(_ \<approx> _ \<approx> _)")
    where "ivpeq s D t \<equiv> \<forall> d \<in> D. (s \<sim> d \<sim> t)"

    primrec run :: "'e list \<Rightarrow> ('s \<times> 's) set" 
      where run_Nil: "run [] = Id" |
            run_Cons: "run (a#as) = step a O run as"
                                                                                  
    definition next_states :: "'s \<Rightarrow> 'e \<Rightarrow> 's set"
      where "next_states s a \<equiv> {Q. (s,Q)\<in>step a}"

    definition execute  :: "'e list \<Rightarrow> 's \<Rightarrow> 's set" 
      where "execute as s = Image (run as) {s} " 

    definition reachable :: "'s \<Rightarrow> 's \<Rightarrow> bool" ("(_ \<hookrightarrow> _)" [70,71] 60) where
      "reachable s1 s2 \<equiv>  (\<exists>as. (s1,s2) \<in> run as)"

    definition reachable0 :: "'s \<Rightarrow> bool"  where
      "reachable0 s \<equiv> reachable s0 s"
    
   declare non_interference_def[cong] and ivpeq_def[cong] and next_states_def[cong]
            execute_def[cong] and reachable_def[cong] and reachable0_def[cong] and run.simps(1)[cong] and
            run.simps(2)[cong] 
  
    lemma reachable_s0 : "reachable0 s0"
      by (metis SM.reachable_def SM_axioms pair_in_Id_conv reachable0_def run.simps(1)) 
    
    lemma reachable_self : "reachable s s"
      using reachable_def run.simps(1) by fastforce

    lemma reachable_step : "(s,s')\<in>step a \<Longrightarrow> reachable s s'"
      proof-
        assume a0: "(s,s')\<in>step a"
        then have "(s,s')\<in>run [a]" by auto          
        then show ?thesis using reachable_def by blast 
      qed

    lemma run_trans : "\<forall>C T V as bs. (C,T)\<in>run as \<and> (T,V)\<in>run bs \<longrightarrow> (C,V)\<in>run (as@bs)"
      proof -
      {
        fix T V as bs
        have "\<forall>C. (C,T)\<in>run as \<and> (T,V)\<in>run bs \<longrightarrow> (C,V)\<in>run (as@bs)"
          proof(induct as)
            case Nil show ?case by simp
          next
            case (Cons c cs)
            assume a0: "\<forall>C. (C, T) \<in> run cs \<and> (T, V) \<in> run bs \<longrightarrow> (C, V) \<in> run (cs @ bs)"
            show ?case
              proof-
              {
                fix C
                have "(C, T) \<in> run (c # cs) \<and> (T, V) \<in> run bs \<longrightarrow> (C, V) \<in> run ((c # cs) @ bs) "
                  proof
                    assume b0: "(C, T) \<in> run (c # cs) \<and> (T, V) \<in> run bs"
                    from b0 obtain C' where b2: "(C,C')\<in>step c \<and> (C',T)\<in>run cs" by auto
                    with a0 b0 have "(C',V)\<in>run (cs@bs)" by blast
                    with b2 show "(C, V) \<in> run ((c # cs) @ bs)"
                      using append_Cons relcomp.relcompI run_Cons by auto 
                  qed
              }
              then show ?thesis by auto
              qed
          qed
      }
      then show ?thesis by auto
      qed

    lemma reachable_trans : "\<lbrakk>reachable C T; reachable T V\<rbrakk> \<Longrightarrow> reachable C V"
      proof-
        assume a0: "reachable C T"
        assume a1: "reachable T V"
        from a0 have "C = T \<or> (\<exists>as. (C,T)\<in>run as)" by simp
        then show ?thesis
          proof
            assume b0: "C = T"
            show ?thesis 
              proof -
                from a1 have "T = V \<or> (\<exists>as. (T,V)\<in>run as)" by simp
                then show ?thesis
                  proof
                    assume c0: "T=V"
                    with a0 show ?thesis by auto
                  next
                    assume c0: "(\<exists>as. (T,V)\<in>run as)"
                    then show ?thesis using a1 b0 by auto 
                  qed
              qed
          next
            assume b0: "\<exists>as. (C,T)\<in>run as"
            show ?thesis
              proof -
                from a1 have "T = V \<or> (\<exists>as. (T,V)\<in>run as)" by simp
                then show ?thesis
                  proof
                    assume c0: "T=V"
                    then show ?thesis using a0 by auto 
                  next
                    assume c0: "(\<exists>as. (T,V)\<in>run as)"
                    from b0 obtain as where d0: "(C,T)\<in>run as" by auto
                    from c0 obtain bs where d1: "(T,V)\<in>run bs" by auto
                    then show ?thesis using d0  run_trans by fastforce
                  qed
              qed
          qed
      qed

    lemma reachableStep : "\<lbrakk>reachable0 C; (C,C')\<in>step a\<rbrakk> \<Longrightarrow> reachable0 C'"
      proof -
        assume a0: "reachable0 C"
        assume a1: "(C,C')\<in>step a"
        from a0 have "(C = s0) \<or> (\<exists>as. (s0,C) \<in> run as)"  by auto
        then show "reachable0 C'"
          proof
            assume b0: "C = s0"
            show "reachable0 C'"
              using a1 b0  reachable_step by auto 
          next
            assume b0: "\<exists>as. (s0,C) \<in> run as"
            show "reachable0 C'"
              using a0 a1 reachable_step reachable0_def reachable_trans by blast
          qed
      qed
    
    lemma reachable0_reach : "\<lbrakk>reachable0 C; reachable C C'\<rbrakk> \<Longrightarrow> reachable0 C'"
      using  reachable_trans by fastforce

    declare reachable_def[cong del] and reachable0_def[cong del]

end

subsection{* Information flow security properties *}

locale SM_enabled = SM s0 step domain sched vpeq interference            
  for s0 :: 's and
       step :: "'e \<Rightarrow> ('s \<times> 's) set" and
       domain :: "'s \<Rightarrow> 'e \<Rightarrow> ('d option)" and
       sched :: 'd and
       vpeq :: "'s \<Rightarrow> 'd \<Rightarrow> 's \<Rightarrow> bool"  ("(_ \<sim> _ \<sim> _)") and
       interference :: "'d \<Rightarrow> 'd \<Rightarrow> bool" ("(_ \<leadsto> _)")
  +
  assumes enabled0: "\<forall>s a. reachable0 s \<longrightarrow> (\<exists> s'. (s,s') \<in> step a)"
begin
    lemma enabled : "reachable0 s \<Longrightarrow> (\<exists> s'. (s,s') \<in> step a)"
      using enabled0 by simp

    lemma enabled_ex: "\<forall>s es. reachable0 s \<longrightarrow> (\<exists> s'. s' \<in> execute es s)" 
      proof -
      {
        fix es
        have "\<forall>s. reachable0 s \<longrightarrow> (\<exists> s'. s' \<in> execute es s)"
          proof(induct es)
            case Nil show ?case by auto 
          next
            case (Cons a as)
            assume a0: "\<forall>s. reachable0 s \<longrightarrow> (\<exists>s'. s' \<in> execute as s)"
            show ?case 
              proof-
              {
                fix s
                assume b0: "reachable0 s"
                have b1: "\<exists>s1. (s,s1)\<in>step a" using enabled b0 by simp
                then obtain s1 where b2: "(s,s1)\<in>step a" by auto
                with a0 b0 have b3: "\<exists>s'. s' \<in> execute as s1"
                  using reachableStep by blast 
                then obtain s2 where b4: "s2\<in>execute as s1" by auto
                then have "s2 \<in> execute (a # as) s"
                  using Image_singleton_iff  SM_axioms b2 relcomp.simps run_Cons by fastforce 
                then have "\<exists>s'. s' \<in> execute (a # as) s" by auto
              }
              then show ?thesis by auto
              qed
          qed
      }
      then show ?thesis by auto
      qed
            
    lemma enabled_ex2: "reachable0 s \<Longrightarrow> (\<exists> s'. s' \<in> execute es s)" 
      using enabled_ex by auto

    primrec sources :: "'e list \<Rightarrow> 's \<Rightarrow> 'd \<Rightarrow> 'd set" where
      sources_Nil:"sources [] s d = {d}" |
      sources_Cons:"sources (a # as) s d = (\<Union>{sources as s' d| s'. (s,s') \<in> step a}) \<union> 
                              {w . w = the (domain s a) \<and> (\<exists>v s'. (w \<leadsto> v) \<and> (s,s')\<in>step a \<and> v\<in>sources as s' d)}"
    declare sources_Nil [simp del]     
    declare sources_Cons [simp del]
    
    primrec ipurge :: "'e list \<Rightarrow> 'd \<Rightarrow> 's set \<Rightarrow> 'e list" where
      ipurge_Nil:   "ipurge [] u ss = []" |
      ipurge_Cons:  "ipurge (a#as) u ss = (if \<exists>s\<in>ss. the (domain s a) \<in> (sources (a#as) s u) then
                                              a # ipurge as u (\<Union>s\<in>ss. {s'. (s,s') \<in> step a})
                                           else
                                              ipurge as u ss
                                          )"

    definition observ_equivalence :: "'s \<Rightarrow> 'e list \<Rightarrow> 's \<Rightarrow> 
          'e list \<Rightarrow> 'd \<Rightarrow> bool" ("(_ \<lhd> _ \<cong> _ \<lhd> _ @ _)")
      where "observ_equivalence s as t bs d \<equiv> 
                \<forall>s' t'. ((s,s')\<in> run as \<and> (t,t')\<in> run bs) \<longrightarrow>(s' \<sim> d \<sim> t')"
                
    declare observ_equivalence_def[cong]

    lemma observ_equiv_sym:
      "(s \<lhd> as \<cong> t \<lhd> bs @ d) \<Longrightarrow> (t \<lhd> bs \<cong> s \<lhd> as @ d)"
      using observ_equivalence_def vpeq_symmetric_lemma by blast
    
    lemma observ_equiv_trans:
      "\<lbrakk>reachable0 t; (s \<lhd> as \<cong> t \<lhd> bs @ d); (t \<lhd> bs \<cong> x \<lhd> cs @ d)\<rbrakk> \<Longrightarrow> (s \<lhd> as \<cong> x \<lhd> cs @ d)"
      apply clarsimp 
      apply(cut_tac s=t and es=bs in enabled_ex2)
      apply simp
      apply auto[1]
      by (metis (no_types, hide_lams) vpeq_transitive_lemma)
      

    lemma exec_equiv_leftI:
   "\<lbrakk>reachable0 C; \<forall> C'. (C,C')\<in>step a \<longrightarrow> (C' \<lhd> as \<cong> D \<lhd> bs @ d)\<rbrakk> \<Longrightarrow> (C \<lhd> (a # as) \<cong> D \<lhd> bs @ d)"
      proof -
        assume a0: "reachable0 C"
        assume a1: "\<forall> C'. (C,C')\<in>step a \<longrightarrow> (C' \<lhd> as \<cong> D \<lhd> bs @ d)"
        have "\<forall>S' T'. ((C,S')\<in> run (a#as) \<and> (D,T')\<in> run bs) \<longrightarrow>(S' \<sim> d \<sim> T')" 
          proof -
          {
            fix S' T'
            assume b0: "(C, S') \<in> run (a # as) \<and> (D, T') \<in> run bs"
            then obtain C' where b1: "(C,C')\<in>step a \<and> (C',S')\<in>run as"
              using relcompEpair run_Cons by auto 
            with a1 have b2: "(C' \<lhd> as \<cong> D \<lhd> bs @ d)" by auto
            with b0 b1 have "S' \<sim> d \<sim> T'" by auto
          }
          then show ?thesis by auto
          qed
        then show ?thesis  by fastforce 
      qed

    lemma exec_equiv_both:
   "\<lbrakk>reachable0 C1; reachable0 C2; \<forall> C1' C2'. (C1,C1')\<in>step a \<and>(C2,C2')\<in>step b\<longrightarrow> (C1' \<lhd> as \<cong> C2' \<lhd> bs @ u)\<rbrakk> 
      \<Longrightarrow> (C1 \<lhd> (a # as) \<cong> C2 \<lhd> (b # bs) @ u)"
      proof -
        assume a0: "reachable0 C1"
        assume a1: "reachable0 C2"
        assume a2: "\<forall> C1' C2'. (C1,C1')\<in>step a \<and>(C2,C2')\<in>step b\<longrightarrow> (C1' \<lhd> as \<cong> C2' \<lhd> bs @ u)"
        then have "\<forall>S' T'. ((C1,S')\<in> run (a # as) \<and> (C2,T')\<in> run (b # bs)) \<longrightarrow>(S' \<sim> u \<sim> T')"
          using relcompEpair run_Cons  by auto           
        then show ?thesis by auto                  
      qed

    lemma sources_refl:"reachable0 s \<Longrightarrow> u \<in> sources as s u"
      apply(induct as arbitrary: s)
       apply(simp add: sources_Nil)
      apply(simp add: sources_Cons) 
      using enabled reachableStep  
        by metis

    lemma scheduler_in_sources_Cons:
      "reachable0 s \<Longrightarrow> the (domain s a) = sched \<Longrightarrow> the (domain s a) \<in> sources (a#as) s u"
      apply(unfold sources_Cons)
      apply(erule ssubst)
      apply(rule UnI2)
      apply(clarsimp)
      apply(rule_tac x=u in exI)
      apply(safe)
      apply (simp add: sched_intf_all)
      using enabled reachableStep sources_refl 
      by blast


    definition noninterference_r :: "bool"
      where "noninterference_r \<equiv> \<forall>d as s. reachable0 s \<longrightarrow> (s \<lhd> as \<cong> s \<lhd> (ipurge as d {s}) @ d)"

    definition noninterference :: "bool"
      where "noninterference \<equiv> \<forall>d as. (s0 \<lhd> as \<cong> s0 \<lhd> (ipurge as d {s0}) @ d)"

    definition weak_noninterference :: "bool"
      where "weak_noninterference \<equiv> \<forall>d as bs. ipurge as d {s0} = ipurge bs d {s0}
                                                  \<longrightarrow> (s0 \<lhd> as \<cong> s0 \<lhd> bs @ d)"
   
    definition weak_noninterference_r :: "bool"
      where "weak_noninterference_r \<equiv> \<forall>d as bs s. reachable0 s \<and> ipurge as d {s} = ipurge bs d {s}
                                                  \<longrightarrow> (s \<lhd> as \<cong> s \<lhd> bs @ d)"

    definition noninfluence::"bool" 
      where "noninfluence \<equiv> \<forall> d as s t . reachable0 s \<and> reachable0 t \<and> (s \<approx> (sources as s d) \<approx> t) 
                                \<and> (s \<sim> sched \<sim> t) \<longrightarrow> (s \<lhd> as \<cong> t \<lhd> (ipurge as d {t}) @ d)"

    definition noninfluence_gen::"bool" 
      where "noninfluence_gen \<equiv> \<forall> d as s ts . reachable0 s \<and> (\<forall>t\<in>ts. reachable0 t) 
                                \<and> (\<forall>t\<in>ts. (s \<approx> (sources as s d) \<approx> t)) 
                                \<and> (\<forall>t\<in>ts. (s \<sim> sched \<sim> t)) 
                                \<longrightarrow> (\<forall>t\<in>ts. (s \<lhd> as \<cong> t \<lhd> (ipurge as d ts) @ d))"

    definition weak_noninfluence ::"bool" 
      where "weak_noninfluence \<equiv> \<forall> d as bs s t . reachable0 s \<and> reachable0 t \<and> (s \<approx> (sources as s d) \<approx> t) 
                                     \<and> (s \<sim> sched \<sim> t) \<and> ipurge as d {s} = ipurge bs d {s} 
                                     \<longrightarrow> (s \<lhd> as \<cong> t \<lhd> bs @ d)"

    definition weak_noninfluence2 ::"bool" 
      where "weak_noninfluence2 \<equiv> \<forall> d as bs s t . reachable0 s \<and> reachable0 t \<and> (s \<approx> (sources as s d) \<approx> t) 
                                     \<and> (s \<sim> sched \<sim> t) \<and> ipurge as d {s} = ipurge bs d {t} 
                                     \<longrightarrow> (s \<lhd> as \<cong> t \<lhd> bs @ d)"

    definition nonleakage :: "bool" 
      where "nonleakage \<equiv> \<forall>d as s t. reachable0 s \<and> reachable0 t \<and> (s \<sim> sched \<sim> t) 
                                      \<and> (s \<approx> (sources as s d) \<approx> t) \<longrightarrow> (s \<lhd> as \<cong> t \<lhd> as @ d)"
declare noninterference_r_def[cong] and noninterference_def[cong] and weak_noninterference_def[cong] and
        weak_noninterference_r_def[cong] and noninfluence_def[cong] and noninfluence_gen_def[cong] and
        weak_noninfluence_def[cong] and weak_noninfluence2_def[cong] and nonleakage_def[cong]


subsection{* Unwinding conditions*}

    definition step_consistent :: "bool" where
      "step_consistent \<equiv> \<forall>a d s t. reachable0 s \<and> reachable0 t \<and> (s \<sim> d \<sim> t) \<and> (s \<sim> sched \<sim> t) \<and> 
                              (((the (domain s a)) \<leadsto> d) \<longrightarrow> (s \<sim> (the (domain s a)) \<sim> t)) \<longrightarrow> 
                              (\<forall> s' t'. (s,s') \<in> step a \<and> (t,t') \<in> step a \<longrightarrow> (s' \<sim>d\<sim> t'))"

    definition weak_step_consistent :: "bool" where
      "weak_step_consistent \<equiv> \<forall>a d s t. reachable0 s \<and> reachable0 t \<and> (s \<sim> d \<sim> t) \<and> (s \<sim> sched \<sim> t) \<and> 
                              ((the (domain s a)) \<leadsto> d) \<and> (s \<sim> (the (domain s a)) \<sim> t) \<longrightarrow>
                              (\<forall> s' t'. (s,s') \<in> step a \<and> (t,t') \<in> step a \<longrightarrow> (s' \<sim>d\<sim> t'))"

    definition step_consistent_e :: "'e \<Rightarrow> bool" where
      "step_consistent_e a \<equiv> \<forall>d s t. reachable0 s \<and> reachable0 t \<and> (s \<sim> d \<sim> t) \<and> (s \<sim> sched \<sim> t) \<and> 
                              (((the (domain s a)) \<leadsto> d) \<longrightarrow> (s \<sim> (the (domain s a)) \<sim> t)) \<longrightarrow> 
                              (\<forall> s' t'. (s,s') \<in> step a \<and> (t,t') \<in> step a \<longrightarrow> (s' \<sim>d\<sim> t'))"

    definition weak_step_consistent_e :: "'e \<Rightarrow> bool" where
      "weak_step_consistent_e a \<equiv> \<forall>d s t. reachable0 s \<and> reachable0 t \<and> (s \<sim> d \<sim> t) \<and> (s \<sim> sched \<sim> t) \<and> 
                              ((the (domain s a)) \<leadsto> d) \<and> (s \<sim> (the (domain s a)) \<sim> t) \<longrightarrow>
                              (\<forall> s' t'. (s,s') \<in> step a \<and> (t,t') \<in> step a \<longrightarrow> (s' \<sim>d\<sim> t'))"

    
    definition local_respect :: "bool" where
      "local_respect \<equiv> \<forall> a d s s'. reachable0 s \<and> ((the (domain s a)) \<setminus>\<leadsto> d) \<and> (s,s')\<in>step a \<longrightarrow> (s \<sim> d \<sim> s')"

    definition local_respect_e :: "'e \<Rightarrow> bool" where
      "local_respect_e a \<equiv> \<forall>d s s'. reachable0 s \<and> ((the (domain s a)) \<setminus>\<leadsto> d) \<and> (s,s')\<in>step a \<longrightarrow> (s \<sim> d \<sim> s')"

    lemma local_respect_all_evt : "local_respect = (\<forall>a. local_respect_e a)"
      by (simp add: local_respect_def local_respect_e_def)

   declare step_consistent_def [cong] and weak_step_consistent_def[cong] and step_consistent_e_def[cong] and
        weak_step_consistent_e_def[cong] and local_respect_def[cong] and local_respect_e_def [cong]

    lemma step_consistent_all_evt : "step_consistent = (\<forall>a. step_consistent_e a)"   
     by simp

    lemma weak_step_consistent_all_evt : "weak_step_consistent = (\<forall>a. weak_step_consistent_e a)"
      by simp
      
    lemma step_cons_impl_weak : "step_consistent \<Longrightarrow> weak_step_consistent"
      using step_consistent_def weak_step_consistent_def by blast
       
      

    lemma weak_with_step_cons:
      assumes p1:weak_step_consistent
        and   p2:local_respect
      shows   step_consistent  
      proof -
      {
        fix d a s t s' t'
        have "reachable0 s \<and> reachable0 t \<longrightarrow> (s \<sim> d \<sim> t) \<and> (s \<sim> sched \<sim> t) \<and> 
              (((the (domain s a)) \<leadsto> d) \<longrightarrow> (s \<sim> (the (domain s a)) \<sim> t)) \<longrightarrow> (s,s')\<in>step a \<and> (t,t')\<in>step a
              \<longrightarrow> (s' \<sim> d \<sim> t')" 
           proof -
           {
             assume aa:"reachable0 s \<and> reachable0 t"
             assume a0:"s \<sim> d \<sim> t"
             assume a1:"s \<sim> sched \<sim> t"
             assume a2:"((the (domain s a)) \<leadsto> d) \<longrightarrow> (s \<sim> (the (domain s a)) \<sim> t)"
             assume a3: "(s,s')\<in>step a \<and> (t,t')\<in>step a"
             have "s' \<sim> d \<sim> t'"
              proof(cases "(the (domain s a)) \<leadsto> d")
                assume b0:"(the (domain s a)) \<leadsto> d"
                show ?thesis using aa a0 a1 a2 b0 p1 weak_step_consistent_def a3 by blast 
                next
                assume b1:"\<not>((the (domain s a)) \<leadsto> d)"
                have b2:"(domain s a) = (domain t a)" by (simp add: a1 sched_vpeq)
                with b1 have b3:"\<not>((the (domain t a)) \<leadsto> d)" by auto
                then have b4:"s\<sim>d\<sim>s'" using aa b1  p2 a3  by fastforce 
                then have b5:"t\<sim>d\<sim>t'" using aa b3 p2 a3 by fastforce
                then show ?thesis using a0 b4 vpeq_symmetric_lemma vpeq_transitive_lemma by blast
              qed
           }
           then show ?thesis by auto
           qed
      }
      then show ?thesis using step_consistent_def by blast
      qed

subsection{* Lemmas for the inference framework *}

    lemma sched_equiv_preserved:
      assumes 1:step_consistent
      and     2:"s \<sim>sched\<sim> t"
      and     3:"(s,s')\<in>step a"
      and     4:"(t,t')\<in>step a"
      and     5:"reachable0 s \<and> reachable0 t"
    shows "s' \<sim>sched\<sim> t'"
      apply(case_tac "the (domain s a) = sched")
      using "1" "2" "3" "4" "5" step_consistent_def apply blast
      using "1" "2" "3" "4" "5" no_intf_sched step_consistent_def by blast
      
    lemma sched_equiv_preserved_left:
      "\<lbrakk>local_respect; reachable0 s; (s \<sim>sched\<sim> t); the (domain s a) \<noteq> sched; (s,s')\<in> step a\<rbrakk> 
        \<Longrightarrow>  (s' \<sim>sched\<sim> t)"
        using local_respect_def no_intf_sched non_interference_def 
          vpeq_symmetric_lemma vpeq_transitive_lemma by blast 


    lemma un_eq:
      "\<lbrakk>S = S'; T = T'\<rbrakk> \<Longrightarrow> S \<union> T = S' \<union> T'"
    by auto

    lemma Un_eq:
      "\<lbrakk>\<And> x y. \<lbrakk>x \<in> xs; y \<in> ys\<rbrakk> \<Longrightarrow> P x = Q y; \<exists> x. x \<in> xs; \<exists> y. y \<in> ys\<rbrakk> \<Longrightarrow> (\<Union>x\<in>xs. P x) = (\<Union>y\<in>ys. Q y)"
    by auto

    declare step_consistent_def [cong del]                                                   

    lemma sources_eq0: "step_consistent \<and> (s \<sim> sched \<sim> t) \<and> reachable0 s \<and> reachable0 t
                      \<longrightarrow> sources as s d = sources as t d"
      proof (induct as arbitrary: s t)
        case Nil show ?case
          by (simp add: sources_Nil)
      next
        case (Cons a as) show ?case                    
          using sources_Cons apply(clarsimp simp: sources_Cons)
          apply(rule un_eq)
          apply(simp only: Union_eq, simp only: UNION_eq[symmetric])
           apply(rule Un_eq, clarsimp)
           apply (meson Cons.hyps reachable0_reach reachableStep reachable_s0 sched_equiv_preserved)             
             using enabled apply simp
            using enabled apply simp
          apply(clarsimp simp: sched_vpeq)
          apply(rule Collect_cong)
          apply(rule conj_cong, rule refl)
          apply(rule iff_exI)
          apply (metis (no_types, hide_lams) Cons.hyps enabled reachableStep sched_equiv_preserved)
          done                    
      qed

    lemma sources_eq:
      "\<lbrakk>step_consistent; s \<sim> sched \<sim> t; reachable0 s; reachable0 t\<rbrakk> \<Longrightarrow> sources as s d = sources as t d"
      using sources_eq0 by blast

    lemma same_sources_dom:
      "\<lbrakk>s \<approx>(sources (a#as) s d)\<approx> t; (the (domain s a)) \<leadsto> x; x \<in> sources as s' d; 
        (s,s')\<in>step a\<rbrakk> \<Longrightarrow> (s \<sim>(the (domain s a))\<sim> t)"
       apply simp
       apply(erule bspec)
       apply(subst sources_Cons)
       apply(rule UnI2)
       apply(blast)
       done

    lemma sources_step:
      "\<lbrakk>reachable0 s; (the (domain s a)) \<setminus>\<leadsto> d\<rbrakk> \<Longrightarrow> sources [a] s d = {d}" 
      by (auto simp: sources_Cons  sources_Nil enabled dest: enabled)

    
    lemma sources_step2:
      "\<lbrakk>reachable0 s; (the (domain s a)) \<leadsto> d\<rbrakk> \<Longrightarrow> sources [a] s d = {the (domain s a),d}"
      apply(auto simp: sources_Cons sources_Nil enabled dest: enabled)
      done

    lemma sources_unwinding_step:
      "\<lbrakk>s \<approx>(sources (a#as) s d)\<approx> t; (s\<sim>sched\<sim>t); step_consistent;
        (s,s')\<in>step a; (t,t')\<in>step a; reachable0 s; reachable0 t\<rbrakk>  \<Longrightarrow> (s' \<approx>(sources as s' d)\<approx> t')"
       apply(clarsimp simp: ivpeq_def sources_Cons)        
        using UnionI step_consistent_def by blast
       
    lemma sources_eq_step:
      "\<lbrakk>local_respect; step_consistent;(s,s')\<in>step a; 
        (the (domain s a)) \<noteq> sched; reachable0 s\<rbrakk> \<Longrightarrow>
        (sources as s' d) = (sources as s d)"
        using reachableStep sched_equiv_preserved_left sources_eq0 vpeq_reflexive_lemma by blast 
                                     
    lemma sources_equiv_preserved_left: "\<lbrakk>local_respect; step_consistent; s\<sim>sched\<sim>t; 
          the (domain s a) \<notin> sources (a#as) s d; s \<approx>sources (a#as) s d\<approx> t; (s,s')\<in>step a; 
          (the (domain s a)) \<noteq> sched; reachable0 s; reachable0 t\<rbrakk> \<Longrightarrow> (s' \<approx>sources as s' d\<approx> t)"
          apply(clarsimp simp: ivpeq_def cong del: local_respect_def)
          apply(rename_tac v)
          apply(case_tac "(the (domain s a)) \<leadsto> v")
             apply(fastforce simp: sources_Cons cong del: local_respect_def)
          proof -
            fix v :: 'd
            assume a1: local_respect
            assume a2: step_consistent
            assume a3: "s \<sim> sched \<sim> t"
            assume a4: "\<forall>d\<in>sources (a # as) s d. (s \<sim> d \<sim> t)"
            assume a5: "(s, s') \<in> step a"
            assume a6: "reachable0 s"
            assume a7: "reachable0 t"
            assume a8: "v \<in> sources as s' d"
            assume a9: "\<not> ((the (domain s a)) \<leadsto> v)"
            obtain ss :: "'s \<Rightarrow> 'e \<Rightarrow> 's" where
              f10: "\<forall>e. (t, ss t e) \<in> step e"
              using a7 by (meson enabled)
            have "\<forall>e. domain s e = domain t e"
              using a3 by (meson sched_vpeq)
            then have f11: "\<forall>d sa e. (t, sa) \<notin> step e \<or> (t \<sim> d \<sim> sa) \<or> ((the (domain s e)) \<leadsto> d)"
              using a7 a1 local_respect_def non_interference_def by force
            have "s' \<sim> v \<sim> (ss t a)"
              using f10 a8 a7 a6 a5 a4 a3 a2 by (metis (no_types) ivpeq_def sources_unwinding_step)
            then show "s' \<sim> v \<sim> t"
              using f11 f10 a9 by (meson vpeq_symmetric_lemma vpeq_transitive_lemma)
          qed

    lemma ipurge_eq'_helper:
      "\<lbrakk>s \<in> ss; the (domain s a) \<in> sources (a # as) s u; \<forall>s\<in>ts. the (domain s a) \<notin> sources (a # as) s u;
       (\<forall>s t. s \<in> ss \<and> t \<in> ts \<longrightarrow> (s \<sim>sched\<sim> t) \<and> reachable0 s \<and> reachable0 t);  t \<in> ts; step_consistent\<rbrakk> \<Longrightarrow>
      False"
      apply(cut_tac s=s and t=t and as=as and d=u in sources_eq, (simp cong del: step_consistent_def)+)
      apply(clarsimp  simp: sources_Cons | safe)+
      apply(rename_tac s')
       apply(drule_tac x=t in bspec, simp)
       apply (clarsimp cong del: step_consistent_def)
       apply(cut_tac s=t in enabled, simp)
       apply(erule exE, rename_tac t')
       apply(drule_tac x="sources as t' u" in spec)
       apply(cut_tac s=s' and t=t' and d=u in sources_eq, simp+)
          apply(fastforce elim: sched_equiv_preserved)
         apply(fastforce intro: reachableStep)
        apply(fastforce intro: reachableStep)
       apply(fastforce simp: sched_vpeq )
      apply(drule_tac x=t in bspec, simp)
      apply (clarsimp )
      apply(rename_tac v s')
      apply(drule_tac x=v in spec, erule impE, fastforce simp: sched_vpeq)
      apply(cut_tac s=t in enabled[where a=a], simp, clarsimp, rename_tac t')
      apply(cut_tac s=s' and t=t' and d=u in sources_eq, simp+)
         apply(fastforce elim: sched_equiv_preserved )
        apply(fastforce intro: reachableStep )
       apply(fastforce intro: reachableStep )
      apply(fastforce simp: sched_vpeq )
      done
 
    lemma ipurge_eq':
      "(\<forall> s t. s\<in>ss \<and> t\<in>ts \<longrightarrow> (s \<sim>sched\<sim> t) \<and> reachable0 s \<and> reachable0 t) \<and> 
        (\<exists> s. s \<in> ss) \<and> (\<exists> t. t \<in> ts) \<and> step_consistent \<longrightarrow> ipurge as u ss = ipurge as u ts"
      proof (induct as arbitrary: ss ts)
      case Nil show ?case
       apply simp
       done
      next
      case (Cons a as) show ?case
       apply(clarsimp simp: sched_vpeq )
       apply(intro conjI impI)
          apply(rule "Cons.hyps"[rule_format])
          apply (clarsimp)
          apply(metis sched_equiv_preserved reachableStep enabled)
         apply (clarsimp)
         apply(drule ipurge_eq'_helper, simp+)[1]
        apply (clarsimp)
        apply(drule ipurge_eq'_helper, (simp add: vpeq_symmetric_lemma)+)[1]
       apply(rule "Cons.hyps"[rule_format], auto)
       done  
      qed
 
    lemma ipurge_eq:"\<lbrakk>step_consistent; s \<sim> sched \<sim> t; reachable0 s \<and> reachable0 t\<rbrakk>
                      \<Longrightarrow> ipurge as d {s} = ipurge as d {t}" 
      by (simp add: ipurge_eq')
      
declare step_consistent_def [cong]
subsection{* Inference framework of information flow security properties *}

    theorem nonintf_impl_weak: "noninterference \<Longrightarrow> weak_noninterference"
      by (metis noninterference_def observ_equiv_sym observ_equiv_trans reachable_s0 weak_noninterference_def)       

    theorem wk_nonintf_r_impl_wk_nonintf: "weak_noninterference_r \<Longrightarrow> weak_noninterference"
      using reachable_s0 by auto
      
    theorem nonintf_r_impl_noninterf: "noninterference_r \<Longrightarrow> noninterference"
      using noninterference_def noninterference_r_def reachable_s0 by auto 

    theorem nonintf_r_impl_wk_nonintf_r: "noninterference_r \<Longrightarrow> weak_noninterference_r"
      by (metis noninterference_r_def observ_equiv_sym observ_equiv_trans weak_noninterference_r_def)
      
    lemma noninf_impl_nonintf_r: "noninfluence \<Longrightarrow> noninterference_r"
      using ivpeq_def noninfluence_def noninterference_r_def vpeq_reflexive_lemma by blast      

    lemma noninf_impl_nonlk: "noninfluence \<Longrightarrow> nonleakage"
      using noninterference_r_def nonleakage_def observ_equiv_sym 
        observ_equiv_trans noninfluence_def noninf_impl_nonintf_r by blast 

    lemma wk_noninfl_impl_nonlk: "weak_noninfluence \<Longrightarrow> nonleakage"
      using weak_noninfluence_def nonleakage_def by blast       
    
    lemma wk_noninfl_impl_wk_nonintf_r: "weak_noninfluence \<Longrightarrow> weak_noninterference_r"
      using ivpeq_def weak_noninfluence_def vpeq_reflexive_lemma weak_noninterference_r_def by blast 
   
    lemma noninf_gen_impl_noninfl: "noninfluence_gen \<Longrightarrow> noninfluence"
      using noninfluence_gen_def noninfluence_def
      by (metis empty_iff insert_iff) 
      
    lemma nonlk_imp_sc: "nonleakage \<Longrightarrow> step_consistent" 
      proof -
        assume p0: "nonleakage"
        then have p1[rule_format]: "\<forall>as d s t. reachable0 s \<and> reachable0 t \<longrightarrow> (s \<sim> sched \<sim> t) 
                         \<longrightarrow> (s \<approx> (sources as s d) \<approx> t) \<longrightarrow> (s \<lhd> as \<cong> t \<lhd> as @ d)"
          using nonleakage_def by blast
        
        have "\<forall>a d s t. reachable0 s \<and> reachable0 t \<longrightarrow> (s \<sim> d \<sim> t) \<and> (s \<sim> sched \<sim> t) \<and> 
                          (((the (domain s a)) \<leadsto> d) \<longrightarrow> (s \<sim> (the (domain s a)) \<sim> t)) \<longrightarrow> 
                          (\<forall> s' t'. (s,s') \<in> step a \<and> (t,t') \<in> step a \<longrightarrow> (s' \<sim>d\<sim> t'))"
          proof -
          {
            fix a d s t
            assume a0: "reachable0 s \<and> reachable0 t"
              and  a1: "(s \<sim> d \<sim> t) \<and> (s \<sim> sched \<sim> t)"
              and  a2: "((the (domain s a)) \<leadsto> d) \<longrightarrow> (s \<sim> (the (domain s a)) \<sim> t)"
            have "\<forall> s' t'. (s,s') \<in> step a \<and> (t,t') \<in> step a \<longrightarrow> (s' \<sim>d\<sim> t')"
              proof -
              {
                fix s' t'
                assume b0: "(s,s') \<in> step a \<and> (t,t') \<in> step a"
                have "s' \<sim>d\<sim> t'" 
                  proof(cases "(the (domain s a)) \<leadsto> d")
                    assume c0: "(the (domain s a)) \<leadsto> d"
                    with a2 have "s \<sim> (the (domain s a)) \<sim> t" by simp
                    with a0 a1 c0 have "s \<approx> (sources [a] s d) \<approx> t" 
                      using sources_step2[of s a d]
                        insert_iff singletonD by auto 
                    then have "s \<lhd> [a] \<cong> t \<lhd> [a] @ d" 
                      using p1[of s t "[a]" d] a0 a1 by blast
                    with b0 show ?thesis
                     by auto
                  next
                    assume c0: "\<not>((the (domain s a)) \<leadsto> d)"
                    with a0 a1 have "s \<approx> (sources [a] s d) \<approx> t" 
                      using sources_step[of s a d]  by auto 
                    then have "s \<lhd> [a] \<cong> t \<lhd> [a] @ d" 
                      using p1[of s t "[a]" d] a0 a1 by auto
                    with b0 show ?thesis
                      by auto
                  qed
              }
              then show ?thesis by auto
              qed
          }
          then show ?thesis by blast
          qed
        then show "step_consistent" using step_consistent_def by blast
      qed


    lemma sc_imp_nonlk: "step_consistent \<Longrightarrow> nonleakage" 
      proof -
        assume p0: "step_consistent"
        have "\<forall>d as s t. reachable0 s \<and> reachable0 t \<longrightarrow> (s \<sim> sched \<sim> t) 
                         \<longrightarrow> (s \<approx> (sources as s d) \<approx> t) \<longrightarrow> (s \<lhd> as \<cong> t \<lhd> as @ d)"
          proof -
          {
            fix as
            have "\<forall>d s t. reachable0 s \<and> reachable0 t \<longrightarrow> (s \<sim> sched \<sim> t) 
                         \<longrightarrow> (s \<approx> (sources as s d) \<approx> t) \<longrightarrow> (s \<lhd> as \<cong> t \<lhd> as @ d)"
              proof(induct as)
                case Nil show ?case using sources_refl by auto 
              next
                case (Cons b bs)
                assume a0: "\<forall>d s t. reachable0 s \<and> reachable0 t \<longrightarrow> (s \<sim> sched \<sim> t) 
                                    \<longrightarrow> (s \<approx> sources bs s d \<approx> t) \<longrightarrow> (s \<lhd> bs \<cong> t \<lhd> bs @ d)"
                show ?case
                  proof -
                  {
                    fix d s t
                    assume b0: "reachable0 s \<and> reachable0 t"
                      and  b1: "s \<sim> sched \<sim> t"
                      and  b2: "s \<approx> sources (b # bs) s d \<approx> t"
                    then have "s \<lhd> b # bs \<cong> t \<lhd> b # bs @ d"
                      using exec_equiv_both sources_unwinding_step p0 a0 
                        by (meson reachableStep SM_axioms sched_equiv_preserved) 
                  }
                  then show ?thesis by blast
                  qed
              qed
          }
          then show ?thesis by blast
        qed

        then show "nonleakage" using nonleakage_def by blast
      qed

    theorem sc_eq_nonlk: "step_consistent = nonleakage" 
      using nonlk_imp_sc sc_imp_nonlk by blast

    lemma noninf_imp_lr: "noninfluence \<Longrightarrow> local_respect" 
      proof -
        assume p0: "noninfluence"
        then have p1[rule_format]: "\<forall> d as s t . reachable0 s \<and> reachable0 t \<longrightarrow> (s \<approx> (sources as s d) \<approx> t) 
                                \<longrightarrow> (s \<sim> sched \<sim> t) \<longrightarrow> (s \<lhd> as \<cong> t \<lhd> (ipurge as d {t}) @ d)"
          using noninfluence_def by blast
        
        have "\<forall> a d s s'. reachable0 s \<longrightarrow> ((the (domain s a)) \<setminus>\<leadsto> d) \<and> (s,s')\<in>step a \<longrightarrow> (s \<sim> d \<sim> s')"
          proof -
          {
            fix a d s s'
            assume a0: "reachable0 s"
              and  a1: "((the (domain s a)) \<setminus>\<leadsto> d) \<and> (s,s')\<in>step a"
            then have a2: "the (domain s a) \<noteq> d" using  interf_reflexive by auto
            from a0 a1 p1[of s s "[a]" d] have a3: "s \<lhd> [a] \<cong> s \<lhd> (ipurge [a] d {s}) @ d"
              using  vpeq_reflexive_lemma by auto
            from a0 a1 a2 have "ipurge [a] d {s} = []" 
              using sources_step SM_enabled_axioms  by fastforce
            with a1 a3 have "s \<sim> d \<sim> s'"
              by (metis IdI R_O_Id observ_equiv_sym observ_equivalence_def run_Cons run_Nil) 
          }
          then show ?thesis by auto
          qed
        then show "local_respect" using local_respect_def by blast
      qed

    lemma noninf_imp_sc: "noninfluence \<Longrightarrow> step_consistent"
      using nonlk_imp_sc noninf_impl_nonlk by blast  

    theorem UnwindingTheorem : "\<lbrakk>step_consistent; local_respect\<rbrakk> \<Longrightarrow> noninfluence_gen"
    proof -
      assume p1:step_consistent
      assume p2:local_respect
      {
        fix as d
        have "\<forall>s ts. reachable0 s \<and> (\<forall>t\<in>ts. reachable0 t) 
                    \<longrightarrow> (\<forall>t\<in>ts. (s \<approx> (sources as s d) \<approx> t)) 
                    \<longrightarrow> (\<forall>t\<in>ts. (s \<sim> sched \<sim> t)) 
                    \<longrightarrow> (\<forall>t\<in>ts. (s \<lhd> as \<cong> t \<lhd> (ipurge as d ts) @ d))"
          proof(induct as)
            case Nil show ?case using sources_refl by auto
          next
            case (Cons b bs)
            assume a0: "\<forall>s ts. reachable0 s \<and> (\<forall>t\<in>ts. reachable0 t) 
                          \<longrightarrow> (\<forall>t\<in>ts. (s \<approx> (sources bs s d) \<approx> t)) 
                          \<longrightarrow> (\<forall>t\<in>ts. (s \<sim> sched \<sim> t)) 
                          \<longrightarrow> (\<forall>t\<in>ts. (s \<lhd> bs \<cong> t \<lhd> (ipurge bs d ts) @ d))"
            show ?case 
              proof -
              {
                fix s ts
                assume b0: "reachable0 s \<and> (\<forall>t\<in>ts. reachable0 t)"
                  and  b1: "\<forall>t\<in>ts. (s \<approx> (sources (b # bs) s d) \<approx> t)"
                  and  b2: "\<forall>t\<in>ts. (s \<sim> sched \<sim> t)"
                {
                  fix t
                  assume c0: "t\<in>ts"
                  have c1: "sources (b#bs) s d = sources (b#bs) t d"
                    using b0 b2 c0 p1 sources_eq0 by blast 
                  have c2: "domain s b = domain t b"              
                    by (simp add: b2 c0 sched_vpeq) 
                  have "s \<lhd> b # bs \<cong> t \<lhd> ipurge (b # bs) d ts @ d"
                    proof(cases "the (domain s b) \<in> sources (b#bs) s d")
                      assume d0:"the (domain s b) \<in> sources (b#bs) s d"
                      have d1: "ipurge (b # bs) d ts = b # ipurge bs d (\<Union>s\<in>ts. {s'. (s,s') \<in> step b})"
                        using c0 c1 c2 d0 by auto
                      let ?ts' = "\<Union>s\<in>ts. {s'. (s,s') \<in> step b}" 
                      let ?bs' = "ipurge bs d (\<Union>s\<in>ts. {s'. (s,s') \<in> step b})"
                      {
                        fix s' t'
                        assume e0: "(s,s')\<in> run (b#bs) \<and> (t,t')\<in> run (b # ?bs')"
                        then have e1: "\<exists>s'' t''. (s,s'')\<in>step b \<and> (s'',s')\<in>run bs \<and> (t,t'')\<in>step b \<and> (t'',t')\<in>run ?bs'"
                          using relcompEpair run_Cons by auto
                        then obtain s'' and t'' where e2: "(s,s'')\<in>step b \<and> (s'',s')\<in>run bs \<and> (t,t'')\<in>step b \<and> (t'',t')\<in>run ?bs'"
                          by auto
                        have "\<forall>t\<in>?ts'. reachable0 t" using b0 reachableStep by auto 
                        moreover
                        have "\<forall>t\<in>?ts'. (s'' \<approx> (sources bs s'' d) \<approx> t)"
                          using b0 b1 b2 e2 p1 sources_unwinding_step by blast 
                        moreover
                        have "\<forall>t\<in>?ts'. (s'' \<sim> sched \<sim> t)"
                          using SM_enabled.sched_equiv_preserved SM_enabled_axioms b0 b2 e2 p1 by fast
                        ultimately 
                        have e3: "\<forall>t\<in>?ts'. (s'' \<lhd> bs \<cong> t \<lhd> (ipurge bs d ?ts') @ d)" using a0
                          by (metis b0 e2 reachableStep) 
                        then have "s' \<sim> d \<sim> t'"
                          using UN_iff c0 e2 mem_Collect_eq  by auto 
                      }
                      then have "\<forall>s' t'. ((s,s')\<in> run (b#bs) \<and> (t,t')\<in> run (b # ?bs')) \<longrightarrow>(s' \<sim> d \<sim> t')"
                        by simp
                      with d1 show ?thesis by auto
                    next
                      assume d0:"\<not>(the (domain s b) \<in> sources (b#bs) s d)"
                      have d1: "ipurge (b # bs) d ts = ipurge bs d ts"
                        using b0 b2 d0 p1 sched_vpeq sources_eq by (auto cong del: step_consistent_def)
                      let ?bs' = "ipurge bs d ts"
                      {
                        fix s' t'
                        assume e0: "(s,s')\<in> run (b#bs) \<and> (t,t')\<in> run ?bs'"
                        then have e1: "\<exists>s'' t''. (s,s'')\<in>step b \<and> (s'',s')\<in>run bs"
                          using relcompEpair run_Cons by auto
                        then obtain s'' where e2: "(s,s'')\<in>step b \<and> (s'',s')\<in>run bs"
                          by auto
                        have "\<forall>t\<in>ts. (s'' \<approx> (sources bs s'' d) \<approx> t)"
                          using b0 b1 b2 d0 e2 p1 p2 scheduler_in_sources_Cons 
                          sources_equiv_preserved_left by blast 
                        moreover
                        have "\<forall>t\<in>ts. (s'' \<sim> sched \<sim> t)"
                          using b0 b2 d0 e2 p2 sched_equiv_preserved_left 
                            scheduler_in_sources_Cons by blast 
                        ultimately 
                        have e3: "\<forall>t\<in>ts. (s'' \<lhd> bs \<cong> t \<lhd> (ipurge bs d ts) @ d)" using a0
                          by (metis b0 e2 reachableStep) 
                        then have "s' \<sim> d \<sim> t'"
                          using c0 e0 e2 by auto 
                      }
                      then have "\<forall>s' t'. ((s,s')\<in> run (b#bs) \<and> (t,t')\<in> run ?bs') \<longrightarrow>(s' \<sim> d \<sim> t')"
                        by simp
                      with d1 show ?thesis by auto
                    qed
                      
                }
                
              }
              then show ?thesis by auto
              qed
          qed
      }
      then show ?thesis using noninfluence_gen_def by blast
    qed
    
    theorem UnwindingTheorem1 : "\<lbrakk>weak_step_consistent; local_respect\<rbrakk> \<Longrightarrow> noninfluence_gen"
      using UnwindingTheorem weak_with_step_cons by blast

    theorem noninf_eq_noninf_gen: "noninfluence = noninfluence_gen"
      using UnwindingTheorem noninf_imp_lr noninf_imp_sc noninf_gen_impl_noninfl by blast 

    theorem uc_eq_noninf : "(step_consistent \<and> local_respect) = noninfluence"
      using UnwindingTheorem1 step_cons_impl_weak noninf_eq_noninf_gen 
        noninf_imp_lr noninf_imp_sc by blast
      
    theorem noninf_impl_weak:"noninfluence \<Longrightarrow> weak_noninfluence"
      by (smt observ_equiv_sym observ_equiv_trans ipurge_eq weak_noninfluence_def 
          noninterference_r_def noninf_imp_sc noninfluence_def noninf_impl_nonintf_r)

    lemma wk_nonintf_r_and_nonlk_impl_noninfl: "\<lbrakk>weak_noninterference_r; nonleakage\<rbrakk> \<Longrightarrow> weak_noninfluence"
      proof -
        assume p0: "weak_noninterference_r"
          and  p1: "nonleakage"
        then have a0: "\<forall>d as bs s. reachable0 s \<and> ipurge as d {s} = ipurge bs d {s}
                                    \<longrightarrow> (s \<lhd> as \<cong> s \<lhd> bs @ d)" 
          using weak_noninterference_r_def by blast
        from p1 have a1: "\<forall>d as s t. reachable0 s \<and> reachable0 t \<and> (s \<sim> sched \<sim> t) 
                                      \<and> (s \<approx> (sources as s d) \<approx> t) \<longrightarrow> (s \<lhd> as \<cong> t \<lhd> as @ d)"
          using nonleakage_def by blast
        
        then have "\<forall> d as bs s t . reachable0 s \<and> reachable0 t \<and> (s \<approx> (sources as s d) \<approx> t) 
                                     \<and> (s \<sim> sched \<sim> t) \<and> ipurge as d {s} = ipurge bs d {s} 
                                     \<longrightarrow> (s \<lhd> as \<cong> t \<lhd> bs @ d)"
          proof -
          {
            fix d as bs s t
            assume b0: "reachable0 s \<and> reachable0 t \<and> (s \<approx> (sources as s d) \<approx> t) 
                        \<and> (s \<sim> sched \<sim> t) \<and> ipurge as d {s} = ipurge bs d {s}"
            with a1 have b1: "s \<lhd> as \<cong> t \<lhd> as @ d" by blast
            from b0 have b2: "ipurge as d {s} = ipurge as d {t}"
              using ipurge_eq nonlk_imp_sc p1 by blast 
            from b0 have b3: "ipurge bs d {s} = ipurge bs d {t}"
              using ipurge_eq nonlk_imp_sc p1 by blast 
            from a0 b0 b2 b3 have b4: "s \<lhd> as \<cong> s \<lhd> bs @ d" by blast
            from a0 b0 b2 b3 have b5: "t \<lhd> as \<cong> t \<lhd> bs @ d" by auto
            from b1 b4 b5 have "s \<lhd> as \<cong> t \<lhd> bs @ d"
              using b0 observ_equiv_trans by blast 
          }
          then show ?thesis by blast
          qed
        then show ?thesis using weak_noninfluence_def by blast
      qed

    lemma nonintf_r_and_nonlk_impl_noninfl: "\<lbrakk>noninterference_r; nonleakage\<rbrakk> \<Longrightarrow> noninfluence"
      proof -
        assume p0: "noninterference_r"
          and  p1: "nonleakage"
        then have a0: "\<forall>d as s. reachable0 s \<longrightarrow> (s \<lhd> as \<cong> s \<lhd> (ipurge as d {s}) @ d)" 
          using noninterference_r_def by blast
        from p1 have a1: "\<forall>d as s t. reachable0 s \<and> reachable0 t \<and> (s \<sim> sched \<sim> t) 
                                      \<and> (s \<approx> (sources as s d) \<approx> t) \<longrightarrow> (s \<lhd> as \<cong> t \<lhd> as @ d)"
          using nonleakage_def by blast
        
        then have "\<forall> d as s t . reachable0 s \<and> reachable0 t \<and> (s \<approx> (sources as s d) \<approx> t) 
                                \<and> (s \<sim> sched \<sim> t) \<longrightarrow> (s \<lhd> as \<cong> t \<lhd> (ipurge as d {t}) @ d)"
          proof -
          {
            fix d as bs s t
            assume b0: "reachable0 s \<and> reachable0 t \<and> (s \<approx> (sources as s d) \<approx> t) 
                        \<and> (s \<sim> sched \<sim> t)"
            with a1 have b1: "s \<lhd> as \<cong> t \<lhd> as @ d" by blast
            from b0 a0 have b2: "s \<lhd> as \<cong> s \<lhd> (ipurge as d {s}) @ d" by fast
            from b0 a0 have b3: "t \<lhd> as \<cong> t \<lhd> (ipurge as d {t}) @ d" by fast
            
            from b1 b2 b3 have "s \<lhd> as \<cong> t \<lhd> (ipurge as d {t}) @ d"
              using b0 observ_equiv_trans by blast 
          }
          then show ?thesis by blast
          qed
        then show ?thesis using noninfluence_def by blast
      qed

    lemma noninfl_impl_noninfl2: "weak_noninfluence \<Longrightarrow> weak_noninfluence2"
      using ipurge_eq wk_noninfl_impl_nonlk weak_noninfluence2_def 
        weak_noninfluence_def nonlk_imp_sc by metis 

    lemma noninf2_imp_lr: "weak_noninfluence2 \<Longrightarrow> local_respect" 
      proof -
        assume p0: "weak_noninfluence2"
        then have p1[rule_format]: "\<forall> d as bs s t . reachable0 s \<and> reachable0 t \<and> (s \<approx> (sources as s d) \<approx> t) 
                                     \<and> (s \<sim> sched \<sim> t) \<and> ipurge as d {s} = ipurge bs d {t} 
                                     \<longrightarrow> (s \<lhd> as \<cong> t \<lhd> bs @ d)"
          using weak_noninfluence2_def by blast
        
        have "\<forall> a d s s'. reachable0 s \<longrightarrow> ((the (domain s a)) \<setminus>\<leadsto> d) \<and> (s,s')\<in>step a \<longrightarrow> (s \<sim> d \<sim> s')"
          proof -
          {
            fix a d s s'
            assume a0: "reachable0 s"
              and  a1: "((the (domain s a)) \<setminus>\<leadsto> d) \<and> (s,s')\<in>step a"
            then have a2: "the (domain s a) \<noteq> d" using non_interference_def interf_reflexive by auto
            from a0 a1 a2 have "ipurge [a] d {s} = ipurge [] d {s}" 
              using sources_step SM_enabled_axioms  by fastforce
            with a0 have "s \<lhd> [a] \<cong> s \<lhd> [] @ d" 
              using p1[of s s "[a]" d "[]"] ivpeq_def vpeq_reflexive_lemma by blast 
            with a1 have "s \<sim> d \<sim> s'"
              by (metis IdI R_O_Id observ_equiv_sym observ_equivalence_def run_Cons run_Nil) 
          }
          then show ?thesis by auto
          qed
        then show "local_respect" using local_respect_def by blast
      qed
    
    lemma noninf2_imp_sc: "weak_noninfluence2 \<Longrightarrow> step_consistent" 
      proof -
        assume p0: "weak_noninfluence2"
        then have p1[rule_format]: "\<forall> d as bs s t . reachable0 s \<and> reachable0 t \<and> (s \<approx> (sources as s d) \<approx> t) 
                                     \<and> (s \<sim> sched \<sim> t) \<and> ipurge as d {s} = ipurge bs d {t} 
                                     \<longrightarrow> (s \<lhd> as \<cong> t \<lhd> bs @ d)"
          using weak_noninfluence2_def by blast
        
        have "\<forall>a d s t. reachable0 s \<and> reachable0 t \<and> (s \<sim> d \<sim> t) \<and> (s \<sim> sched \<sim> t) \<and> 
                              (((the (domain s a)) \<leadsto> d) \<longrightarrow> (s \<sim> (the (domain s a)) \<sim> t)) \<longrightarrow> 
                              (\<forall> s' t'. (s,s') \<in> step a \<and> (t,t') \<in> step a \<longrightarrow> (s' \<sim>d\<sim> t'))"
          proof -
          {
            fix a d s t
            assume a0: "reachable0 s \<and> reachable0 t"
              and  a1: "(s \<sim> d \<sim> t) \<and> (s \<sim> sched \<sim> t)"
              and  a2: "((the (domain s a)) \<leadsto> d) \<longrightarrow> (s \<sim> (the (domain s a)) \<sim> t)"
            then have a3: "domain s a = domain t a" by (simp add: sched_vpeq) 
                    
            have "\<forall> s' t'. (s,s') \<in> step a \<and> (t,t') \<in> step a \<longrightarrow> (s' \<sim>d\<sim> t')"
              proof -
              {
                fix s' t'
                assume b0: "(s,s') \<in> step a \<and> (t,t') \<in> step a"
                have "s' \<sim>d\<sim> t'" 
                  proof(cases "(the (domain s a)) \<leadsto> d")
                    assume c0: "(the (domain s a)) \<leadsto> d"
                    with a2 have c1: "s \<sim> (the (domain s a)) \<sim> t" by simp
                    with a0 a1 c0 have c2: "s \<approx> (sources [a] s d) \<approx> t" 
                      using sources_step2[of s a d] by auto 
                    from a0 c0 a3 have c4: "ipurge [a] d {s} = ipurge [a] d {t}" 
                      using sources_step2[of s a d] sources_step2[of t a d] 
                        ipurge_Cons[of a "[]" d "{s}"] ipurge_Cons[of a "[]" d "{t}"] 
                        ipurge_Nil by auto
                    then have "s \<lhd> [a] \<cong> t \<lhd> [a] @ d" 
                      using p1[of s t "[a]" d] a0 a1 c2 by blast 
                    with b0 show ?thesis
                      by auto
                  next
                    assume c0: "\<not>((the (domain s a)) \<leadsto> d)"
                    then have c1: "the (domain s a) \<noteq> d" using interf_reflexive by auto
                    from c0 a0 a1 have c2: "s \<approx> (sources [a] s d) \<approx> t" 
                      using sources_step[of s a d]  by auto 
                    from a0 c0 c1 a3 have c4: "ipurge [a] d {s} = ipurge [a] d {t}" 
                      using sources_step[of s a d] sources_step[of t a d] 
                        ipurge_Cons[of a "[]" d "{s}"] ipurge_Cons[of a "[]" d "{t}"] 
                        ipurge_Nil by auto
                    then have "s \<lhd> [a] \<cong> t \<lhd> [a] @ d" 
                      using p1[of s t "[a]" d] a0 a1 c2 by blast 
                    with b0 show ?thesis
                      by auto 
                  qed
              }
              then show ?thesis by auto
              qed
          }
          then show ?thesis by blast
          qed
        then show "step_consistent" using step_consistent_def by blast
      qed

    theorem noninfl_eq_noninfl2: "weak_noninfluence = weak_noninfluence2"
      using noninf2_imp_lr noninf2_imp_sc noninf_impl_weak noninfl_impl_noninfl2 uc_eq_noninf by blast
      
    theorem nonintf_r_and_nonlk_eq_strnoninfl: "(noninterference_r \<and> nonleakage) = noninfluence"
      using nonintf_r_and_nonlk_impl_noninfl noninf_impl_nonintf_r noninf_impl_nonlk by blast 

    theorem wk_nonintf_r_and_nonlk_eq_noninfl: "(weak_noninterference_r \<and> nonleakage) = weak_noninfluence"
      using wk_noninfl_impl_nonlk wk_noninfl_impl_wk_nonintf_r wk_nonintf_r_and_nonlk_impl_noninfl by blast
      
  end
end