theory Dynamic_model_v3
imports Main
begin
subsection {* Security State Machine *}
locale SM =
  fixes s0 :: "'s"
  fixes is_execute :: "'e \<Rightarrow> bool"
  fixes is_grant :: "'e \<Rightarrow> bool"
  fixes step :: "'s \<Rightarrow> 'e \<Rightarrow> 's"
  fixes domain :: "'e \<Rightarrow> ('d option)"
  fixes grant_dest :: "'e \<Rightarrow> ('d option)"
  fixes t_set :: "'s \<Rightarrow> 'd \<Rightarrow>  't set"      
  fixes vpeq :: "'s \<Rightarrow> 'd \<Rightarrow> 's \<Rightarrow> bool"  ("(_ \<sim> _ \<sim> _)")
  assumes 
    vpeq_transitive_lemma : "\<forall> s t r d. (s \<sim> d \<sim> t) \<and> (t \<sim> d \<sim> r) \<longrightarrow> (s \<sim> d \<sim> r)" and
    vpeq_symmetric_lemma : "\<forall> s t d. (s \<sim> d \<sim> t) \<longrightarrow> (t \<sim> d \<sim> s)" and
    vpeq_reflexive_lemma : "\<forall> s d. (s \<sim> d \<sim> s)" and
    execute_exclusive: "\<forall>a. is_execute a  \<longleftrightarrow> \<not>(is_grant a)" and
    grant_exclusive: "\<forall>a. is_grant a   \<longleftrightarrow> \<not>(is_execute a)" 
begin

    definition ivpeq :: "'s \<Rightarrow> 'd set \<Rightarrow> 's \<Rightarrow> bool" ("(_ \<approx> _ \<approx> _)")
      where "ivpeq s D t \<equiv> \<forall> d \<in> D. (s \<sim> d \<sim> t)"

    primrec run :: "'s \<Rightarrow> 'e list \<Rightarrow> 's"
      where run_Nil: "run s [] = s" |
            run_Cons: "run s (a#as) = run (step s a) as "

    definition reachable :: "'s \<Rightarrow> 's \<Rightarrow> bool" ("(_ \<hookrightarrow> _)" [70,71] 60) where
      "reachable s1 s2 \<equiv>  (\<exists>as. run s1 as = s2 )"
    
    definition reachable0 :: "'s \<Rightarrow> bool"  where
      "reachable0 s \<equiv> reachable s0 s"
      
    declare ivpeq_def[cong] and reachable_def[cong]
            and reachable0_def[cong] and run.simps(1)[cong] and run.simps(2)[cong]

    lemma reachable_s0 : "reachable0 s0"
      by (metis SM.reachable_def SM_axioms reachable0_def run.simps(1)) 

    
    lemma reachable_self : "reachable s s"
      using reachable_def run.simps(1) by fastforce

    lemma reachable_step : "s' = step s a \<Longrightarrow> reachable s s'"
      proof-
        assume a0: "s' = step s a"
        then have "s' = run s [a]" by auto          
        then show ?thesis using reachable_def by blast 
      qed

    lemma run_trans : "\<forall>C T V as bs. T = run C as \<and> V = run T bs \<longrightarrow> V = run C (as@bs)"
     proof -
      {
        fix T V as bs
        have "\<forall>C. T = run C as \<and> V = run T bs \<longrightarrow> V = run C (as@bs)"
          proof(induct as)
            case Nil show ?case by simp
          next
            case (Cons c cs)
            assume a0: "\<forall>C. T = run C cs \<and> V = run T bs \<longrightarrow> V = run C (cs @ bs)"
            show ?case
              proof-
              {
                fix C
                have "T = run C (c # cs) \<and> V = run T bs \<longrightarrow> V = run C ((c # cs) @ bs) "
                  proof
                    assume b0: "T = run C (c # cs) \<and> V = run T bs"
                    from b0 obtain C' where b2: "C' = step C c \<and> T = run C' cs" by auto
                    with a0 b0 have "V = run C' (cs@bs)" by blast
                    with b2 show "V = run C ((c # cs) @ bs)"
                      using append_Cons run_Cons by auto 
                  qed
              }
              then show ?thesis by blast
              qed
          qed
      }
      then show ?thesis by auto
      qed

    lemma reachable_trans : "\<lbrakk>reachable C T; reachable T V\<rbrakk> \<Longrightarrow> reachable C V"
      proof-
        assume a0: "reachable C T"
        assume a1: "reachable T V"
        from a0 have "C = T \<or> (\<exists>as. T = run C as)" by auto
        then show ?thesis
          proof
            assume b0: "C = T"
            show ?thesis 
              proof -
                from a1 have "T = V \<or> (\<exists>as. V = run T as)" by auto
                then show ?thesis
                  proof
                    assume c0: "T=V"
                    with a0 show ?thesis by auto
                  next
                    assume c0: "(\<exists>as. V = run T as)"
                    then show ?thesis using a1 b0 by auto 
                  qed
              qed
          next
            assume b0: "\<exists>as. T = run C as"
            show ?thesis
              proof -
                from a1 have "T = V \<or> (\<exists>as. V = run T as)" by auto
                then show ?thesis
                  proof
                    assume c0: "T=V"
                    then show ?thesis using a0 by auto 
                  next
                    assume c0: "(\<exists>as. V = run T as)"
                    from b0 obtain as where d0: "T = run C as" by auto
                    from c0 obtain bs where d1: "V = run T bs" by auto
                    then show ?thesis using d0  run_trans by fastforce
                  qed
              qed
          qed
      qed

    lemma reachableStep : "\<lbrakk>reachable0 C; C' = step C a\<rbrakk> \<Longrightarrow> reachable0 C'"
      apply (simp add: reachable0_def)
      using reachable_step reachable_trans by blast
    
    lemma reachable0_reach : "\<lbrakk>reachable0 C; reachable C C'\<rbrakk> \<Longrightarrow> reachable0 C'"
      using  reachable_trans by fastforce

    declare reachable_def[cong del] and reachable0_def[cong del]
end

subsection{* Information flow security properties *}

locale SM_enabled = SM s0 is_execute is_grant step domain grant_dest t_set vpeq
  for s0 :: 's and
       is_execute :: "'e \<Rightarrow> bool" and
       is_grant :: "'e \<Rightarrow> bool" and
       step :: "'s \<Rightarrow> 'e \<Rightarrow> 's" and
       domain :: "'e \<Rightarrow> ('d option)" and
       grant_dest :: "'e \<Rightarrow> ('d option)" and
       t_set :: "'s \<Rightarrow> 'd \<Rightarrow>  't set" and      
       vpeq :: "'s \<Rightarrow> 'd \<Rightarrow> 's \<Rightarrow> bool"  ("(_ \<sim> _ \<sim> _)")
  +
  assumes enabled0: "\<forall>s a. reachable0 s \<longrightarrow> (\<exists> s'. s' = step s a)"
begin

    lemma enabled : "reachable0 s \<Longrightarrow> (\<exists> s'. s' = step s a)"
        using enabled0 by simp

    primrec sources :: "'e list \<Rightarrow> 'd \<Rightarrow> 's \<Rightarrow> 'd set" where
      sources_Nil:"sources [] d s = {d}" |
      sources_Cons:"sources (a # as) d s = (\<Union>{sources as d (step s a)}) \<union> 
                              {w . (w = the (domain a) \<and> is_execute a \<and> (\<exists>v . t_set s w \<subseteq> t_set s v \<and> v\<in>sources as d (step s a)))
                              \<or> (w = the (grant_dest a) \<and> \<not> is_execute a \<and> (\<exists>v . t_set s w \<subseteq> t_set s v \<and> v\<in>sources as d (step s a)))}"
                                                                                            
    declare sources_Nil [simp del]                                         
    declare sources_Cons [simp del]

    
    
    primrec ipurge :: "'e list \<Rightarrow> 'd \<Rightarrow> 's  \<Rightarrow> 'e list" where
      ipurge_Nil:   "ipurge [] u s = []" |
      ipurge_Cons:  "ipurge (a#as) u s = (if (is_execute a \<and> the (domain a) \<notin> (sources (a#as) u s))
                                            then
                                              ipurge as u (step s a)
                                          else if(\<not>is_execute a \<and> the (grant_dest a) \<notin> (sources (a#as) u s))
                                            then
                                              ipurge as u (step s a)
                                           else
                                              a # ipurge as u (step s a)        
                                          )"
(*
    lemma execute_not_change0: "is_execute a \<and> t = step s a \<longrightarrow> t_set s d = t_set t d"
      using taint_set_consistance_lemma by auto*)
(*
    lemma execute_not_change_policy: "\<forall>a as u s. is_execute a \<longrightarrow> (sources as u s) = (sources as u (step s a))"
      proof - 
      {
        fix as
        have "\<forall>a u s. is_execute a \<longrightarrow> (sources as u s) = (sources as u (step s a))"
          proof (induct as)
            case Nil then show ?case by (simp add: sources_Nil)
          next
            case (Cons b bs)
            assume p0: "\<forall>a u s. is_execute a \<longrightarrow> (sources bs u s) = (sources bs u (step s a))"
            then show ?case
              proof -
              {
                fix a u s
                assume p1: "is_execute a"
                have "(sources (b # bs) u s) = (sources (b # bs) u (step s a))"
                  proof (cases "is_execute b")
                    assume a0: "is_execute b"
                    show "(sources (b # bs) u s) = (sources (b # bs) u (step s a))"
                      proof (cases "the (domain b) \<in> (sources (b # bs) u s)")
                        assume b0: "the (domain b) \<in> (sources (b # bs) u s)"
                        have b1: "\<exists>v. v\<in>sources bs u (step s b) \<and> t_set s (the (domain b)) \<subseteq> t_set s v"
                          using b0 sources_Cons by auto
                        have b2: "t_set s (the (domain b)) = t_set (step s a) (the (domain b))"
                          by (simp add: p1 taint_set_consistance_lemma)
                        have b3: "\<exists>v. v\<in>sources bs u (step s b) \<and> t_set (step s a) (the (domain b)) \<subseteq> t_set  (step s a) v"
                          using b1 p1 taint_set_consistance_lemma by blast
                        have b4: "(sources bs u (step s b)) = (sources bs u (step (step s b) a)) "
                          by (simp add: p0 p1) 
                        have b5: "\<exists>v. v\<in>(sources bs u (step (step s b) a)) \<and> t_set (step s a) (the (domain b)) \<subseteq> t_set  (step s a) v"
                          using b3 b4 by blast
                        have b7: "(sources (b # bs) u s) = (sources (b # bs) u (step s a))"
                        have b6: "the (domain b) \<in> (sources (b # bs) u (step s a))"
                }
                then show ?thesis by blast
              qed
        }
        then show ?thesis by blast
      qed
*)
(*
    lemma ipurge_completeness: "\<forall>s as u. reachable0 s
                                 \<longrightarrow> (sources as u s) = (sources (ipurge as u s) u s )"
      proof -
      {
        fix as
        have "\<forall>s u. reachable0 s
                                \<longrightarrow> (sources as u s) = (sources (ipurge as u s) u s )"
          proof (induct as)
            case Nil then show ?case by (simp add: sources_Nil)
          next
            case (Cons b bs)
            assume p0: "\<forall>s u. reachable0 s
                                \<longrightarrow> (sources bs u s) = (sources (ipurge bs u s) u s )"
            then show ?case
              proof -
              {
                fix s u
                assume p1: "reachable0 s"
                have "(sources (b # bs) u s) = (sources (ipurge (b # bs) u s) u s )"
                  proof (cases "is_execute b")
                    assume a0: "is_execute b"
                    show "(sources (b # bs) u s) = (sources (ipurge (b # bs) u s) u s )"
                      proof (cases "the (domain b) \<in> (sources (b # bs) u s)")
                        assume b0: "the (domain b) \<in> (sources (b # bs) u s)"
                        have b1: "(sources (b # bs) u s) = {the (domain b)} \<union> (sources bs u (step s b))"
                          using b0 sources_Cons by auto
                        have b2: "ipurge (b # bs) u s = b # ipurge bs u (step s b)"
                          by (simp add: a0 b0) 
                        have b3: "(sources bs u (step s b)) = (sources (ipurge bs u (step s b)) u (step s b))"
                          using p0 p1 reachableStep by blast
                        show ?thesis
                          using b2 b3 sources_Cons by auto
                      next
                        assume b0: "the (domain b) \<notin> (sources (b # bs) u s)"
                        have b1: "(sources (b # bs) u s) = (sources bs u (step s b))"
                          using b0 sources_Cons by auto
                        have b2: "ipurge (b # bs) u s = ipurge bs u (step s b)"
                          using a0 b0 execute_exclusive by auto
                        have b3: "(sources bs u (step s b)) = (sources (ipurge bs u (step s b)) u (step s b))"
                          using p0 p1 reachableStep by blast
                         
       
                 }
               qed

        }
       then show ?thesis by blast
       qed
*)

     definition observ_equivalence :: "'s \<Rightarrow> 'e list \<Rightarrow> 's \<Rightarrow> 
          'e list \<Rightarrow> 'd \<Rightarrow> bool" ("(_ \<lhd> _ \<cong> _ \<lhd> _ @ _)")
      where "observ_equivalence s as t bs d \<equiv> 
               ((run s as) \<sim> d \<sim> (run t bs))"
     declare observ_equivalence_def[cong]

     lemma observ_equiv_sym:
       "(s \<lhd> as \<cong> t \<lhd> bs @ d) \<Longrightarrow> (t \<lhd> bs \<cong> s \<lhd> as @ d)"
       using observ_equivalence_def vpeq_symmetric_lemma by blast

     lemma observ_equiv_trans:
      "\<lbrakk>reachable0 t; (s \<lhd> as \<cong> t \<lhd> bs @ d); (t \<lhd> bs \<cong> x \<lhd> cs @ d)\<rbrakk> \<Longrightarrow> (s \<lhd> as \<cong> x \<lhd> cs @ d)"
        using observ_equivalence_def vpeq_transitive_lemma by blast

     definition noninfluence::"bool" 
       where "noninfluence \<equiv> \<forall> d as s t. reachable0 s \<and> reachable0 t
                                \<and> (s \<approx> (sources as d s) \<approx> t)
                                \<longrightarrow> (s \<lhd> as \<cong> t \<lhd> (ipurge as d t) @ d)"

     definition noninterference :: "bool"
      where "noninterference \<equiv> \<forall>d as. (s0 \<lhd> as \<cong> s0 \<lhd> (ipurge as d s0) @ d)"

     definition noninterference_r :: "bool"
      where "noninterference_r \<equiv> \<forall>d as s. reachable0 s \<longrightarrow> (s \<lhd> as \<cong> s \<lhd> (ipurge as d s) @ d)"

     definition nonleakage :: "bool" 
      where "nonleakage \<equiv> \<forall>d as s t. reachable0 s \<and> reachable0 t
                                      \<and> (s \<approx> (sources as d s) \<approx> t) \<longrightarrow> (s \<lhd> as \<cong> t \<lhd> as @ d)"

subsection{* Unwinding conditions*}

     definition weakly_step_consistent :: "bool" where 
        "weakly_step_consistent \<equiv>  \<forall>a d s t. reachable0 s \<and> reachable0 t \<and> is_execute a \<and> (s \<sim> d \<sim> t) \<and>
                              (s \<sim> (the (domain a)) \<sim> t) \<longrightarrow> ((step s a) \<sim> d \<sim> (step t a))"

     definition dynamic_local_respect :: "bool" where
        "dynamic_local_respect \<equiv> \<forall>a d s. reachable0 s \<and> is_execute a \<and> \<not>(t_set s (the (domain a)) \<subseteq> t_set s d)
                                \<longrightarrow> (s \<sim> d \<sim> (step s a)) "
                                        
     definition non_interference_respect :: "bool" where
        "non_interference_respect \<equiv> \<forall>d v s t. reachable0 s \<and> reachable0 t \<and> (s \<sim> d \<sim> t) \<and>
                                    \<not> (t_set s v \<subseteq> t_set s d) \<longrightarrow> \<not> (t_set t v \<subseteq> t_set t d)"

     definition weakly_grant_step_consistent :: "bool" where
        "weakly_grant_step_consistent \<equiv>  \<forall>a d s t. reachable0 s \<and> reachable0 t \<and> is_grant a \<and> (s \<sim> d \<sim> t) \<and>
                              (s \<sim> (the (grant_dest a)) \<sim> t) \<longrightarrow> ((step s a) \<sim> d \<sim> (step t a))"

     (* 
     This action a is happened outside the sources.
     We may need to add a more specific condition:
       t_set s (the grant_dest a) \<subseteq> t_set s v
     If we add a tag to a domain whose t_set is already not subseteq to v,
     this action would not change the noninterf relationship.
      *)
     definition grant_local_respect :: "bool" where
        "grant_local_respect \<equiv>  \<forall>s v a. reachable0 s
                                \<and> is_grant a \<and> \<not> (t_set s (the (grant_dest a)) \<subseteq> t_set s v) \<longrightarrow> 
                                (s \<sim> v \<sim> (step s a))"
                                                       
     declare weakly_step_consistent_def [cong] and dynamic_local_respect_def [cong]
              and weakly_grant_step_consistent_def [cong] and grant_local_respect_def 

     definition lemma_local :: "bool" where
        "lemma_local \<equiv> \<forall>s a as u. the (domain a) \<notin> sources (a # as) u s \<longrightarrow> (s \<approx> (sources (a # as) u s)  \<approx> (step s a))"                                     
     
     lemma sources_refl:"reachable0 s \<Longrightarrow> u \<in> sources as u s"
      apply(induct as arbitrary: s)
       apply(simp add: sources_Nil)
      apply(simp add: sources_Cons) 
      using enabled reachableStep  
        by metis

     lemma sources_eq2: "(s \<sim> u \<sim> t) \<longrightarrow> ((sources as u s) = (sources as u t))"
       apply (induct as)
       apply (simp add: sources_Nil)
       apply (simp add: sources_Cons)

       oops
     
subsection{* Inference framework of information flow security properties *}

    lemma noninf_impl_nonintf_r: "noninfluence \<Longrightarrow> noninterference_r"
      using ivpeq_def noninfluence_def noninterference_r_def vpeq_reflexive_lemma by blast    

    lemma noninf_impl_nonlk: "noninfluence \<Longrightarrow> nonleakage"
      using noninterference_r_def nonleakage_def observ_equiv_sym 
        observ_equiv_trans noninfluence_def noninf_impl_nonintf_r by blast   

    theorem nonintf_r_impl_noninterf: "noninterference_r \<Longrightarrow> noninterference"
      using noninterference_def noninterference_r_def reachable_s0 by auto 

     lemma lemma_1_sub_1 : "\<lbrakk>reachable0 s ;
                       dynamic_local_respect;
                       policy_respect;
                       is_execute a;
                       the (domain a) \<notin> sources (a # as) u s;
                       (s \<approx> (sources (a # as) u s) \<approx> t)\<rbrakk>
                      \<Longrightarrow> (s \<approx> (sources as u (step s a)) \<approx> (step s a))"
        apply (simp add:dynamic_local_respect_def sources_Cons)
        by blast

     lemma lemma_1_sub_2 : "\<lbrakk>reachable0 s ;
                       reachable0 t ;
                       dynamic_local_respect;
                       is_execute a;
                       non_interference_respect;
                       the (domain a) \<notin> sources (a # as) u s; 
                       (s \<approx> (sources (a # as) u s) \<approx> t)\<rbrakk>       
                      \<Longrightarrow> (t \<approx> (sources as u (step s a)) \<approx> (step t a))"
        proof - 
          assume a1: "reachable0 s"
          assume a2: "reachable0 t"
          assume a3: dynamic_local_respect
          assume a4: non_interference_respect
          assume a5: "is_execute a"
          assume a6: "the (domain a) \<notin> sources (a # as) u s"
          assume a7: "(s \<approx> (sources (a # as) u s) \<approx> t)"
          have b1: "\<forall>v. v\<in>sources as u (step s a) \<longrightarrow> \<not> (t_set s (the(domain a)) \<subseteq> t_set s v)"
            using a5 a6 sources_Cons by auto
          have b2: "sources (a # as) u s = sources as u (step s a)"
            using a5 a6 sources_Cons by auto
          have b3: "\<forall>v. v\<in>sources as u (step s a) \<longrightarrow> (s \<sim> v \<sim> t)"
            using a7 b2 ivpeq_def by blast
          have b4: "\<forall>v. v\<in>sources as u (step s a) \<longrightarrow> \<not> (t_set t (the(domain a)) \<subseteq> t_set t v)"
            using a1 a2 a4 a5 b1 b3 non_interference_respect_def by blast          
          have b5: "\<forall>v. v\<in>sources as u (step s a) \<longrightarrow> (t \<sim> v \<sim> (step t a))"
            using a2 a3 a5 b4 dynamic_local_respect_def by blast
          then show ?thesis
            using ivpeq_def by auto
        qed

     (*lemma lemma_1_sub_2_1 : "\<lbrakk>reachable0 s ;
                       reachable0 t ;
                       dynamic_local_respect;
                       policy_respect;
                       is_execute a;
                       \<forall>v.\<not>interferes (the (domain s a)) s v \<and> v\<in>sources as u (step s a);
                       (s \<approx> (sources (a # as) u s) \<approx> t)\<rbrakk>       
                      \<Longrightarrow> (t \<approx> (sources as u (step s a)) \<approx> (step t a))"
        apply (simp)
        apply (erule allE)
        apply (simp add:sources_Cons)
        by blast*)
     
     lemma lemma_1_sub_3 : "\<lbrakk>is_execute a;
                       the (domain a) \<notin> sources (a # as) u s;
                       (s \<approx> (sources (a # as) u s) \<approx> t)\<rbrakk>     
                      \<Longrightarrow> (s \<approx> (sources as u (step s a)) \<approx> t)"
         apply (simp add:sources_Cons)
         apply (simp add:sources_Cons)
         done

     lemma lemma_1_sub_4 : "\<lbrakk>(s \<approx> (sources as u (step s a)) \<approx> t);
                             (s \<approx> (sources as u (step s a)) \<approx> (step s a));
                             (t \<approx> (sources as u (step s a)) \<approx> (step t a)) \<rbrakk>
                      \<Longrightarrow> ((step s a) \<approx>(sources as u (step s a)) \<approx> (step t a))"
       by (meson ivpeq_def vpeq_symmetric_lemma vpeq_transitive_lemma)
           
(*
     lemma lemma_1 : "\<lbrakk>reachable0 s;
                      reachable0 t;
                      weakly_step_consistent;
                      dynamic_local_respect;
                      (s \<approx> (sources (a # as) u s) \<approx> t);
                      is_execute a\<rbrakk>
                      \<Longrightarrow> ((step s a) \<approx> (sources as u (step s a)) \<approx> (step t a))"
       apply (case_tac "the (domain a)\<in>sources (a # as) u s")
       apply (simp add:weakly_step_consistent_def)
       apply (simp add:sources_Cons)                                                        
         proof -
           assume a1: dynamic_local_respect
           assume a3: "is_execute a"
           assume a4: "the (domain a) \<notin> sources (a # as) u s"
           assume a5: "(s \<approx> (sources (a # as) u s) \<approx> t)"
           assume b0: "reachable0 s"
           assume b1: "reachable0 t"

           have a6:"(s \<approx> (sources as u (step s a)) \<approx> t)"
            using a1 a3 a4 a5 lemma_1_sub_3 by auto
           then have a7: "(s \<approx> (sources as u (step s a)) \<approx> (step s a))"
            using b0 a1 a3 a4 a5 lemma_1_sub_1 by auto
           then have a8: "(t \<approx> (sources as u (step s a)) \<approx> (step t a))"
            using b1 b0 a1 a3 a4 a5 lemma_1_sub_2 by auto
           then show " ((step s a) \<approx>(sources as u (step s a)) \<approx> (step t a))"
            using a6 a7 lemma_1_sub_4 by blast
         qed
*)
     lemma lemma_1_0: "\<lbrakk>reachable0 s;
                      reachable0 t;
                      weakly_step_consistent;
                      the(domain a) \<in> sources(a#as) u s;
                      (s \<approx> (sources (a # as) u s) \<approx> t);
                      is_execute a\<rbrakk>
                      \<Longrightarrow> ((step s a) \<approx> (sources as u (step s a)) \<approx> (step t a))"
       proof -
          assume a0: "reachable0 s"
          assume a1: "reachable0 t"
          assume a2: weakly_step_consistent
          assume a3: "the(domain a) \<in> sources(a#as) u s"
          assume a4: "(s \<approx> (sources (a # as) u s) \<approx> t)"
          assume a5: "is_execute a"
          have b1: "s \<sim> (the(domain a)) \<sim> t"
            using a3 a4 by auto
          have b2: "sources (a#as) u s = sources as u (step s a) \<union> {the(domain a)}"
            using a3 a5 sources_Cons by auto
          have b3: "\<forall>v. v\<in>(sources as u (step s a)) \<longrightarrow> (s \<sim> v \<sim> t)"
            using a4 b2 by auto
          have b4: "\<forall>v. v\<in>(sources as u (step s a)) \<longrightarrow> ((step s a) \<sim> v \<sim> (step t a))"
            using a0 a1 a2 a5 b1 b3 weakly_step_consistent_def by blast
          then show ?thesis
            using ivpeq_def by auto
       qed


     lemma lemma_2 : "\<lbrakk>reachable0 s;
                      dynamic_local_respect;
                      the (domain a) \<notin> sources (a # as) u s;
                      is_execute a\<rbrakk>
                      \<Longrightarrow> (s \<approx> (sources as u (step s a)) \<approx> (step s a))"
       apply (simp add:dynamic_local_respect_def)
       apply (simp add:sources_Cons)
       by blast
(*
     lemma lemma_3_sub_1: "is_grant a \<Longrightarrow> (sources (a # as) u s) =  (sources as u (step s a))"
        apply (simp add:sources_Cons)
        using grant_exclusive
        by blast
*)
(*
     lemma lemma_3: "\<lbrakk>\<forall>a s t u as. reachable0 s;
                      reachable0 t;
                      weakly_grant_step_consistent;    
                      (s \<approx> (sources (a # as) u s) \<approx> t);
                      (grant_dest a) \<inter> (sources (a # as) u s) \<noteq> {};
                      is_grant a\<rbrakk>
                      \<Longrightarrow> ((step s a) \<approx> (sources as u (step s a)) \<approx> (step t a))"
       apply (simp add: weakly_grant_step_consistent_def)
       apply (simp add: sources_Cons)                  
       done
 *)    
     lemma lemma_4_sub3 : "the (grant_dest a) \<notin> (sources (a # as) u s) \<Longrightarrow>  v \<in> (sources (a # as) u s) \<longrightarrow> the (grant_dest a) \<noteq> v  "
        by blast

     lemma lemma_4_sub_1_0:"\<lbrakk>\<forall>a s v. is_grant a;
                      reachable0 s;
                      grant_local_respect;
                      \<not> (t_set s (the (grant_dest a)) \<subseteq> t_set s v)\<rbrakk>
                      \<Longrightarrow> (s \<sim> v \<sim> (step s a))"
       using grant_local_respect_def by force

     lemma lemma_4_sub_1: "\<lbrakk>\<forall>a s D. is_grant a;
                      reachable0 s;
                      grant_local_respect;
                      (\<forall>v. v \<in> D \<and>
                      \<not> (t_set s (the (grant_dest a)) \<subseteq> t_set s v))\<rbrakk>
                      \<Longrightarrow> (s \<approx> D \<approx> (step s a))"
       using grant_local_respect_def by force

     lemma lemma_4: "\<lbrakk>\<forall>a s u as. is_grant a;
                      reachable0 s; 
                      grant_local_respect;
                      (\<forall>v. v \<in> (sources (a # as) u s) \<and>
                      the (grant_dest a) \<noteq> v \<and>
                      \<not> (t_set s (the (grant_dest a)) \<subseteq> t_set s v))\<rbrakk>
                      \<Longrightarrow> (s \<approx> (sources (a # as) u s) \<approx> (step s a))"
       using grant_local_respect_def by force

     lemma sources_eq1: "\<forall>s t as u. reachable0 s \<and>
                    reachable0 t \<and>
                    weakly_step_consistent \<and>
                    dynamic_local_respect \<and>
                    non_interference_respect \<and>
                    weakly_grant_step_consistent \<and>
                    grant_local_respect \<and>
                    (s \<approx> (sources as u s) \<approx> t)
                    \<longrightarrow> (sources as u s) = (sources as u t)"
       proof -
       {
        fix as
        have "\<forall>s t u. reachable0 s \<and>
                    reachable0 t \<and>
                    weakly_step_consistent \<and>
                    dynamic_local_respect \<and>
                    non_interference_respect \<and>
                    weakly_grant_step_consistent \<and>
                    grant_local_respect \<and>
                    (s \<approx> (sources as u s) \<approx> t)
                    \<longrightarrow> (sources as u s) = (sources as u t)"
          proof(induct as)
            case Nil then show ?case by (simp add: sources_Nil)
          next
            case (Cons b bs)
            assume p0: "\<forall>s t u.((reachable0 s) 
                                \<and> (reachable0 t) 
                                \<and> weakly_step_consistent 
                                \<and> dynamic_local_respect 
                                \<and> non_interference_respect
                                \<and> weakly_grant_step_consistent 
                                \<and> grant_local_respect 
                                \<and> (s \<approx> (sources bs u s) \<approx> t)) \<longrightarrow>
                                  (sources bs u s) = (sources bs u t)"
            then show ?case
              proof -                   
              {
                 fix s t u
                 assume p1: "reachable0 s"
                 assume p2: "reachable0 t"
                 assume p3: weakly_step_consistent
                 assume p4: non_interference_respect
                 assume p5: "dynamic_local_respect"
                 assume p6: "weakly_grant_step_consistent"
                 assume p7: "grant_local_respect"
                 assume p9: "(s \<approx> (sources (b # bs) u s) \<approx> t)" 
                 have "sources (b # bs) u s = sources (b # bs) u t "
                   proof (cases "is_execute b")
                     assume a0: "is_execute b "
                     show "sources (b # bs) u s = sources (b # bs) u t"
                       proof (cases "the (domain b) \<in> (sources (b # bs) u s)")
                         assume b0: "the (domain b) \<in> (sources (b # bs) u s)"
                         have b1: "s \<sim> (the(domain b)) \<sim> t"
                           using b0 p9 by auto
                         have b2: "sources (b # bs) u s = {the (domain b)} \<union> sources bs u (step s b)"
                           using b0 a0 sources_Cons by auto
                         have b3: "((step s b) \<approx> (sources bs u (step s b)) \<approx> (step t b))"
                           using a0 lemma_1_0 p1 p2 p3 p5 p9 b0 by blast 
                         have b4: "(sources bs u (step s b)) = (sources bs u (step t b))"
                           using b3 p0 p1 p2 p3 p4 p5 p6 p7 reachableStep by blast

                         have b6: "\<forall>v. v\<in>sources bs u (step s b) \<longrightarrow> (s \<sim> v \<sim> t)"
                           using p9 b2 by auto

                         have b8: "\<exists>v. v\<in>sources bs u (step s b) \<and> (t_set s (the (domain b)) \<subseteq> t_set s v)"
                           using b0 sources_Cons by auto
                         have b9: "\<exists>v. v\<in>sources bs u (step t b) \<and> (t_set t (the (domain b)) \<subseteq> t_set t v)"
                           by (metis b4 b6 b8 non_interference_respect_def p1 p2 p4 vpeq_symmetric_lemma)
                         have b10: "sources (b # bs) u t = {the (domain b)} \<union> sources bs u (step t b)"
                           using b9 sources_Cons a0 by auto
                         show "sources (b # bs) u s = sources (b # bs) u t"
                           using b4 b10 b2 by auto
                       next                                      
                         assume b0: "the (domain b) \<notin> (sources (b # bs) u s)"
                         have b1: "sources (b # bs) u s = sources bs u (step s b)"
                           using b0 a0 sources_Cons by auto
                         have b2: "(s \<approx> (sources bs u (step s b)) \<approx> (step s b))"
                           using a0 b0 lemma_2 p1 p5 by blast
                         have b3: "\<forall>v. v\<in>sources bs u (step s b) \<longrightarrow> (s \<sim> v \<sim> t)"
                           using p9 b1 by auto
                         have b5: "(t \<approx> (sources bs u (step s b)) \<approx> (step t b))"
                           using a0 b0 lemma_1_sub_2 p1 p2 p4 p5 p9 by blast
                         have b6: "(s \<approx> (sources bs u (step s b)) \<approx> t)"
                           using b1 p9 by auto
                         have b7: "((step s b) \<approx> (sources bs u (step s b)) \<approx> (step t b))"
                           using b1 b2 b5 lemma_1_sub_4 p9 by auto         
                         have b8: "(sources bs u (step s b)) = (sources bs u (step t b))"
                           using b7 p0 p1 p2 p3 p4 p5 p6 p7 reachableStep by blast
                         have b9: "\<forall>v. v\<in>sources bs u (step s b) \<longrightarrow> \<not> t_set s (the(domain b)) \<subseteq> t_set s v"
                           using a0 b0 sources_Cons by auto
                         have b10: "\<forall>v. v\<in>sources bs u (step s b) \<longrightarrow> \<not> t_set t (the(domain b)) \<subseteq> t_set t v"
                           using p1 p2 p4 a0 b3 b9 non_interference_respect_def by blast
                         have b11: "the (domain b) \<notin> (sources (b # bs) u t)"
                           using b10 b8 sources_Cons by auto
                         have b12: "sources (b # bs) u t = sources bs u (step t b)"
                           using b11 a0 sources_Cons by auto
                         then show ?thesis
                           by (simp add: b1 b8)
                         qed
                     next
                       assume a0: "\<not> is_execute b "
                       have a1: "sources bs u (step s b) \<subseteq> sources (b # bs) u s"
                         by (simp add: a0 sources_Cons)
                       have a3: "is_grant b"
                         using a0 execute_exclusive by auto
                       have a4: "sources (b # bs) u s = sources (b # bs) u t"
                         proof (cases "the (grant_dest b) \<in> (sources (b # bs) u s)")
                           assume b0: "the (grant_dest b) \<in> (sources (b # bs) u s)"
                           have b1: "s \<sim> (the(grant_dest b)) \<sim> t"
                             using b0 p9 by auto
                           have b2: "sources (b # bs) u s = {the (grant_dest b)} \<union> sources bs u (step s b)"
                             using b0 a0 sources_Cons by auto
                           have b3: "((step s b) \<approx> (sources bs u (step s b)) \<approx> (step t b))"
                             using a1 a3 b0 p1 p2 p6 p9 by auto
                           have b4: "(sources bs u (step s b)) = (sources bs u (step t b))"
                             using b3 p0 p1 p2 p3 p4 p5 p6 p7 reachableStep by blast
                           have b6: "\<forall>v. v\<in>sources bs u (step s b) \<longrightarrow> (s \<sim> v \<sim> t)"
                             using p9 b2 by auto
                           have b8: "\<exists>v. v\<in>sources bs u (step s b) \<and> (t_set s (the (grant_dest b)) \<subseteq> t_set s v)"
                             using b0 sources_Cons by auto
                           have b9: "\<exists>v. v\<in>sources bs u (step t b) \<and> (t_set t (the (grant_dest b)) \<subseteq> t_set t v)"
                             by (metis b4 b6 b8 non_interference_respect_def p1 p2 p4 vpeq_symmetric_lemma)
                           have b10: "sources (b # bs) u t = {the (grant_dest b)} \<union> sources bs u (step t b)"
                             using b9 sources_Cons a0 by auto
                           show "sources (b # bs) u s = sources (b # bs) u t"
                             using b4 b10 b2 by auto  
                         next
                           assume b0: "the (grant_dest b) \<notin> (sources (b # bs) u s)"
                           have b1: "\<forall>v. v\<in>sources bs u (step s b) \<longrightarrow> \<not> t_set s (the(grant_dest b)) \<subseteq> t_set s v"
                             using a0 b0 sources_Cons by auto
                           have b2: "(s \<approx> (sources bs u (step s b)) \<approx> (step s b))"
                             using a3 b1 grant_local_respect_def p1 p7 by force
                           have b3: "\<forall>v. v\<in>sources bs u (step s b) \<longrightarrow> (s \<sim> v \<sim> t)"
                             using p9 a1 by auto
                           have b4: "\<forall>v. v\<in>sources bs u (step s b) \<longrightarrow> \<not> t_set t (the(grant_dest b)) \<subseteq> t_set t v"
                             using p1 p2 p4 b3 b2 b1 non_interference_respect_def by blast
                           have b5: "(t \<approx> (sources bs u (step s b)) \<approx> (step t b))"
                             using a3 b1 b4 grant_local_respect_def p2 p7 by force
                           have b6: "(s \<approx> (sources bs u (step s b)) \<approx> t)"
                             using a1 p9 by auto
                           have b7: "((step s b) \<approx> (sources bs u (step s b)) \<approx> (step t b))"
                             using b2 b5 b6 lemma_1_sub_4 by blast
                           have b8: "(sources bs u (step s b)) = (sources bs u (step t b))"
                             using b7 p0 p1 p2 p3 p4 p5 p6 p7 reachableStep by blast
                           have b9: "\<forall>v. v\<in>sources bs u (step s b) \<longrightarrow> \<not> t_set s (the(grant_dest b)) \<subseteq> t_set s v"
                             using a0 b0 sources_Cons by auto
                           have b10: "\<forall>v. v\<in>sources bs u (step s b) \<longrightarrow> \<not> t_set t (the(grant_dest b)) \<subseteq> t_set t v"
                             using p1 p2 p4 a0 b3 b9 non_interference_respect_def by blast
                           have b11: "the (grant_dest b) \<notin> (sources (b # bs) u t)"
                             using b10 b8 sources_Cons by auto
                           have b12: "sources (b # bs) u t = sources bs u (step t b)"
                             using b11 a0 sources_Cons by auto
                           have b13: "sources (b # bs) u s = sources bs u (step s b)"
                             using b0 a0 sources_Cons by auto
                           show ?thesis
                             using b13 b12 b8 by auto
                         qed
                       then show ?thesis
                         by auto
                   qed
              }
              then show ?thesis by blast
              qed
          qed

       }
       then show ?thesis by blast
       qed

    lemma ipurge_eq: "\<forall>s t as u. reachable0 s \<and>
                    reachable0 t \<and>
                    weakly_step_consistent \<and>
                    dynamic_local_respect \<and>
                    non_interference_respect \<and>
                    weakly_grant_step_consistent \<and>
                    grant_local_respect \<and>
                    (s \<approx> (sources as u s) \<approx> t)
                    \<longrightarrow> (ipurge as u s) = (ipurge as u t)"
       proof -                                               
       {
        fix as
        have "\<forall>s t u. reachable0 s \<and>
                    reachable0 t \<and>
                    weakly_step_consistent \<and>
                    dynamic_local_respect \<and>
                    non_interference_respect \<and>
                    weakly_grant_step_consistent \<and>
                    grant_local_respect \<and>
                    (s \<approx> (sources as u s) \<approx> t)
                    \<longrightarrow> (ipurge as u s) = (ipurge as u t)"
          proof(induct as)                                         
            case Nil then show ?case by (simp add: sources_Nil)
          next
            case (Cons b bs)
            assume p0: "\<forall>s t u.((reachable0 s) 
                                \<and> (reachable0 t) 
                                \<and> weakly_step_consistent 
                                \<and> dynamic_local_respect 
                                \<and> non_interference_respect 
                                \<and> weakly_grant_step_consistent 
                                \<and> grant_local_respect
                                \<and> (s \<approx> (sources bs u s) \<approx> t))
                                \<longrightarrow> (ipurge bs u s) = (ipurge bs u t)"
            then show ?case
              proof -
              {
                 fix s t u
                 assume p1: "reachable0 s"
                 assume p2: "reachable0 t"
                 assume p3: weakly_step_consistent
                 assume p4: non_interference_respect
                 assume p5: "dynamic_local_respect"
                 assume p6: "weakly_grant_step_consistent"
                 assume p7: "grant_local_respect"
                 assume p9: "(s \<approx> (sources (b # bs) u s) \<approx> t)"
                 have "ipurge (b # bs) u s = ipurge (b # bs) u t "
                   proof (cases "is_execute b")
                     assume a0: "is_execute b"
                     have a3: "sources (b # bs) u s = sources (b # bs) u t"
                       using p1 p2 p3 p4 p5 p6 p7 p9 sources_eq1 by blast
                     then show ?thesis
                       proof (cases "the (domain b) \<in> (sources (b # bs) u s)")
                         assume b0: "the (domain b) \<in> (sources (b # bs) u s)"
                         have b1: "s \<sim> (the(domain b)) \<sim> t"
                           using b0 p9 by auto
                         have b2: "the (domain b) \<in> (sources (b # bs) u t)"
                           using a3 b0 by auto
                         have b3: "((step s b) \<approx> (sources bs u (step s b)) \<approx> (step t b))"
                           using a0 lemma_1_0 p1 p2 p3 p5 p9 b0 by blast
                         have b4: "(ipurge bs u (step s b)) = (ipurge bs u (step t b))"
                           using b3 p0 p1 p2 p3 p4 p5 p6 p7 p9 reachableStep by blast
                         then show ?thesis
                           using a0 b0 b2 ipurge_Cons by auto
                       next
                         assume b0: "the (domain b) \<notin> (sources (b # bs) u s)"
                         have b1: "sources (b # bs) u s = sources bs u (step s b)"
                           using a0 b0 sources_Cons by auto
                         have b2: "(s \<approx> (sources bs u (step s b)) \<approx> (step s b))"
                           using a0 b0 lemma_2 p1 p5 by blast
                         have b3: "\<forall>v. v\<in>sources bs u (step s b) \<longrightarrow> (s \<sim> v \<sim> t)"
                           using p9 b1 by auto
                         have b5: "(t \<approx> (sources bs u (step s b)) \<approx> (step t b))"
                           using a0 b0 lemma_1_sub_2 p1 p2 p4 p5 p9 by blast
                         have b6: "(s \<approx> (sources bs u (step s b)) \<approx> t)"
                           using b1 p9 by auto
                         have b7: "((step s b) \<approx> (sources bs u (step s b)) \<approx> (step t b))"
                           using b1 b2 b5 lemma_1_sub_4 p9 by auto         
                         have b8: "(sources bs u (step s b)) = (sources bs u (step t b))"
                           by (meson b7 p1 p2 p3 p4 p5 p6 p7 reachableStep sources_eq1)
                         have b9: "\<forall>v. v\<in>sources bs u (step s b)\<longrightarrow> \<not> t_set s (the(domain b)) \<subseteq> t_set s v"
                           using a0 b0 sources_Cons by auto
                         have b10: "\<forall>v. v\<in>sources bs u (step s b) \<longrightarrow> \<not> t_set t (the(domain b)) \<subseteq> t_set t v"
                           by (metis b1 b9 ivpeq_def non_interference_respect_def p1 p2 p4 p9)
                         have b11: "the (domain b) \<notin> (sources (b # bs) u t)"
                           using b10 b8 sources_Cons by auto
                         have b12: "ipurge (b # bs) u s = ipurge bs u (step s b)"
                           using a0 b0 execute_exclusive by auto
                         have b13: "ipurge (b # bs) u t = ipurge bs u (step t b)"
                           using a0 b11 execute_exclusive by auto
                         then show ?thesis
                           by (metis p0 SM.reachableStep SM_enabled_axioms SM_enabled_def b12 b7 p1 p2 p3 p4 p5 p6 p7)
                       qed
                   next
                     assume a0: "\<not> is_execute b "
                     have a1: "is_grant b"
                       using a0 execute_exclusive by auto
                     then show ?thesis
                       proof (cases "the (grant_dest b) \<in> (sources (b # bs) u s)")
                         assume b0: "the (grant_dest b) \<in> (sources (b # bs) u s)"
                         have b1: "(sources (b # bs) u s) = {the (grant_dest b)} \<union> (sources bs u (step s b))"
                           using b0 a0 sources_Cons by auto
                         have b2: "((step s b) \<approx> (sources bs u (step s b)) \<approx> (step t b))"
                           using a1 b1 b0 p1 p2 p6 p9 by auto
                         have b3: "(ipurge bs u (step s b)) = (ipurge bs u (step t b))"
                           using b2 p0 p1 p2 p3 p4 p5 p6 p7 p9 reachableStep by blast
                         then show ?thesis
                           by (metis b0 ipurge_Cons p1 p2 p3 p4 p5 p6 p7 p9 sources_eq1)
                       next
                         assume b0: "the (grant_dest b) \<notin> (sources (b # bs) u s)"
                         have b1: "sources (b # bs) u s = sources bs u (step s b)"
                           using b0 a0 sources_Cons by auto
                         have c0: "\<forall>v. v\<in>sources bs u (step s b) \<longrightarrow> \<not> t_set s (the(grant_dest b)) \<subseteq> t_set s v"
                           using a0 b0 sources_Cons by auto 
                         have b2: "(s \<approx> (sources (b # bs) u s) \<approx> (step s b))"
                           using a1 b0 c0 b1 grant_local_respect_def p1 p7 by force
                         have b3: "ipurge (b # bs) u s = ipurge bs u (step s b)"
                           using a0 b0 by auto
                         have b4: "the (grant_dest b) \<notin> (sources (b # bs) u t)"
                           by (metis b0 p1 p2 p3 p4 p5 p6 p7 p9 sources_eq1)
                         have b5: "ipurge (b # bs) u t = ipurge bs u (step t b)"
                           using a0 b4 by auto
                         have c1: "\<forall>v. v\<in>sources bs u (step t b) \<longrightarrow> \<not> t_set t (the(grant_dest b)) \<subseteq> t_set t v"
                           using a0 b4 sources_Cons by auto 
                         have c2: "sources (b # bs) u t = sources bs u (step t b)"
                           using b4 a0 sources_Cons by auto
                         have b6: "(t \<approx> (sources (b # bs) u t) \<approx> (step t b))"
                           using a1 b4 c1 c2 grant_local_respect_def p2 p7 by force
                         have b7: "((step s b) \<approx> (sources (b # bs) u t) \<approx> (step t b))"
                           by (metis (full_types) b1 b2 b6 lemma_1_sub_4 p1 p2 p3 p4 p5 p6 p7 p9 sources_eq1)
                         have b8: "((step s b) \<approx> (sources bs u (step s b)) \<approx> (step t b))"
                           by (metis b1 b7 p1 p2 p3 p4 p5 p6 p7 p9 sources_eq1)
                         have b9: "(ipurge bs u (step s b)) = (ipurge bs u (step t b))"
                           using b8 p0 p1 p2 p3 p4 p5 p6 p7 p9 reachableStep by blast
                         then show ?thesis
                           using b3 b5 b9 by auto
                         qed
                     qed
              }
              then show ?thesis by blast
              qed
          qed
       }
       then show ?thesis by blast
       qed

    lemma non_influgence_lemma: "\<forall>s t as u. reachable0 s \<and>
                    reachable0 t \<and>
                    weakly_step_consistent \<and>
                    dynamic_local_respect \<and>
                    non_interference_respect \<and>
                    weakly_grant_step_consistent \<and>
                    grant_local_respect \<and>
                    (s \<approx> (sources as u s) \<approx> t)
                    \<longrightarrow> ((s \<lhd> as \<cong> t \<lhd> (ipurge as u t) @ u))"
      proof -
      { 
        fix as
        have  "\<forall>s t u. reachable0 s \<and>
                    reachable0 t \<and>
                    weakly_step_consistent \<and>
                    dynamic_local_respect \<and>
                    non_interference_respect \<and>
                    weakly_grant_step_consistent \<and>
                    grant_local_respect \<and>
                    (s \<approx> (sources as u s) \<approx> t)
                    \<longrightarrow> ((s \<lhd> as \<cong> t \<lhd> (ipurge as u t) @ u))"
          proof (induct as)
            case Nil show ?case using sources_Nil by auto
          next
            case (Cons b bs)
            assume p0: "\<forall>s t u.((reachable0 s) 
                                \<and> (reachable0 t) 
                                \<and> weakly_step_consistent 
                                \<and> dynamic_local_respect 
                                \<and> non_interference_respect 
                                \<and> weakly_grant_step_consistent 
                                \<and> grant_local_respect
                                \<and> (s \<approx> (sources bs u s) \<approx> t)) \<longrightarrow>
                                  ((s \<lhd> bs \<cong> t \<lhd> (ipurge bs u t) @ u))"
            then show ?case
              proof -
              { 
                fix s t u
                assume p1: "reachable0 s"
                assume p2: "reachable0 t"
                assume p3: weakly_step_consistent
                assume p4: dynamic_local_respect
                assume p5: non_interference_respect
                assume p6: weakly_grant_step_consistent
                assume p7: grant_local_respect
                assume p8: "(s \<approx> (sources (b # bs) u s) \<approx> t)"
                have "s \<lhd> b # bs \<cong> t \<lhd> ipurge (b # bs) u t @ u"
                  proof (cases "is_execute b")
                    assume a0: "is_execute b"
                    then show ?thesis
                      proof (cases "the (domain b) \<in> sources (b # bs) u s")
                        assume b0: "the (domain b) \<in> sources (b # bs) u s"
                        have b1: "((step s b) \<approx> (sources bs u (step s b)) \<approx> (step t b))"
                           using a0 lemma_1_0 p1 p2 p3 p5 p8 b0 by blast 
                        have b3: "ipurge (b # bs) u t = b # (ipurge bs u (step t b))"
                          by (metis a0 b0 ipurge_Cons p1 p2 p3 p4 p5 p6 p7 p8 sources_eq1)
                        have b4: "(((step s b) \<lhd> bs \<cong> (step t b) \<lhd> (ipurge bs u (step t b)) @ u))"
                          using b1 p0 p1 p2 p3 p4 p5 p6 p7 reachableStep by blast
                        then show ?thesis
                          using b3 b4 by auto
                      next
                        assume b0: "the (domain b) \<notin> sources (b # bs) u s"
                        have b1: "sources (b # bs) u s = sources bs u (step s b)"
                           using a0 b0 sources_Cons by auto
                        have b2: "(s \<approx> (sources bs u (step s b)) \<approx> (step s b))"
                           using a0 b0 lemma_2 p1 p4 by blast
                        have b3: "\<forall>v. v\<in>sources bs u (step s b) \<longrightarrow> (s \<sim> v \<sim> t)"
                           using p8 b1 by auto
                        have b5: "(t \<approx> (sources bs u (step s b)) \<approx> (step t b))"
                          using a0 b0 lemma_1_sub_2 p1 p2 p4 p5 p8 by blast
                        have b6: "(s \<approx> (sources bs u (step s b)) \<approx> t)"
                          using b1 p8 by auto
                        have b7: "((step s b) \<approx> (sources bs u (step s b)) \<approx> (step t b))"
                          using b1 b2 b5 lemma_1_sub_4 p8 by auto         
                        have b8: "(sources bs u (step s b)) = (sources bs u (step t b))"
                          by (meson b7 p1 p2 p3 p4 p5 p6 p7 reachableStep sources_eq1)
                        have b9: "\<forall>v. v\<in>sources bs u (step s b)\<longrightarrow> \<not> t_set s (the(domain b)) \<subseteq> t_set s v"
                          using a0 b0 sources_Cons by auto
                        have b10: "\<forall>v. v\<in>sources bs u (step s b) \<longrightarrow> \<not> t_set t (the(domain b)) \<subseteq> t_set t v"
                          by (metis b3 b9 non_interference_respect_def p1 p2 p5)
                        have b11: "the (domain b) \<notin> (sources (b # bs) u t)"
                           using b10 b8 sources_Cons by auto
                        have b12: "ipurge (b # bs) u t = ipurge bs u (step t b)"
                           using a0 b11 execute_exclusive by auto
                        have b13: "(s \<approx> (sources bs u (step s b)) \<approx> (step s b))"
                          using a0 b0 lemma_2 p1 p4 by blast
                        have b14:"(s \<approx> (sources bs u (step s b)) \<approx> t)"
                          using a0 b0 lemma_1_sub_3 p8 by blast
                        have b15: "((step s b) \<approx> (sources bs u (step s b)) \<approx> t)"
                          by (meson b3 b2 ivpeq_def vpeq_symmetric_lemma vpeq_transitive_lemma)
                        have b16: "(((step s b) \<lhd> bs \<cong> t \<lhd> (ipurge bs u t) @ u))"
                          using b15 p0 p1 p2 p3 p4 p5 p6 p7 reachableStep by blast
                        have b17: "(t \<approx> (sources bs u (step s b)) \<approx> (step t b))"
                          using p1 p2 a0 b0 lemma_1_sub_2 p4 p5 p8 by blast
                        have b18: "ipurge bs u t = ipurge bs u (step t b)"
                          by (metis SM.reachableStep SM_axioms b15 b7 ipurge_eq p1 p2 p3 p4 p5 p6 p7)
                        have b19: "(((step s b) \<lhd> bs \<cong> t \<lhd> (ipurge bs u (step t b)) @ u))"
                          using b16 b17 b18 by auto
                        then show ?thesis
                          using b12 observ_equivalence_def run_Cons by auto
                      qed
                   next
                     assume a0: "\<not> is_execute b "
                     have a1: "is_grant b"
                       using a0 execute_exclusive by auto
                     then show ?thesis
                       proof (cases "the (grant_dest b) \<in> (sources (b # bs) u s)")
                         assume b0: "the (grant_dest b) \<in> (sources (b # bs) u s)"
                         have c0: "(sources (b # bs) u s) = {the (grant_dest b)} \<union> (sources bs u (step s b))"
                           using b0 a0 sources_Cons by auto
                         have b1: "((step s b) \<approx> (sources bs u (step s b)) \<approx> (step t b))"
                           using a1 b0 c0 p1 p2 p6 p8 by auto
                         have b2: "(ipurge bs u (step s b)) = (ipurge bs u (step t b))"
                           using b1 ipurge_eq p1 p2 p3 p4 p5 p6 p7 reachableStep by blast
                         have b3: "ipurge (b # bs) u t = b # (ipurge bs u (step t b))"
                           by (metis a0 b0 b2 ipurge_Cons ipurge_eq p1 p2 p3 p4 p5 p6 p7 p8)                           
                         have b4: "(step s b) \<lhd> bs \<cong> (step t b) \<lhd> ipurge bs u (step t b) @ u "
                           using p0 b1 p1 p2 p3 p4 p5 p6 p7 reachableStep by blast
                         then show ?thesis
                           using b3 observ_equivalence_def run_Cons by auto
                       next
                         assume b0: "the (grant_dest b) \<notin> (sources (b # bs) u s)"
                         have b1: "the (grant_dest b) \<notin> (sources (b # bs) u t)"
                           by (metis b0 p1 p2 p3 p4 p5 p6 p7 p8 sources_eq1)
                         have c0: "\<forall>v. v\<in>sources bs u (step s b) \<longrightarrow> \<not> t_set s (the(grant_dest b)) \<subseteq> t_set s v"
                           using a0 b0 sources_Cons by auto 
                         have c1: "the (grant_dest b) \<notin> (sources (b # bs) u t)"
                           by (metis b0 p1 p2 p3 p4 p5 p6 p7 p8 sources_eq1)
                         have c2: "\<forall>v. v\<in>sources bs u (step t b) \<longrightarrow> \<not> t_set t (the(grant_dest b)) \<subseteq> t_set t v"
                           using a0 c1 sources_Cons by auto
                         have c3: "(sources (b # bs) u s) = (sources bs u (step s b))"
                           using a0 b0 sources_Cons by auto
                         have c4: "(sources (b # bs) u t) = (sources bs u (step t b))"
                           using a0 b1 sources_Cons by auto
                         have b2: "ipurge (b # bs) u t = (ipurge bs u (step t b))"
                           by (simp add: a0 b1)
                         have b3: "(s \<approx> (sources bs u (step s b)) \<approx> (step s b))"
                           by (metis a1 grant_local_respect_def ivpeq_def c0 p1 p7)
                         have b4: "(t \<approx> (sources bs u (step t b)) \<approx> (step t b))"
                           by (metis a1 grant_local_respect_def ivpeq_def c2 p2 p7)
                         have b6: "(s \<approx> (sources bs u (step s b)) \<approx> t)"
                           using a1 c3 p8 by auto
                         have b7: "((step s b) \<approx> (sources bs u (step s b)) \<approx> t)"
                           by (meson b3 b6 ivpeq_def vpeq_symmetric_lemma vpeq_transitive_lemma)
                         have b8: "(((step s b) \<lhd> bs \<cong> t \<lhd> (ipurge bs u t) @ u))"
                           using b7 p0 p1 p2 p3 p4 p5 p6 p7 reachableStep by blast
                         have b5: "(sources bs u (step s b)) = (sources bs u (step t b))"
                           by (metis c3 c4 p1 p2 p3 p4 p5 p6 p7 p8 sources_eq1)
                         have b9: "((step s b) \<approx> (sources bs u (step s b)) \<approx> (step t b))"
                           by (metis b3 b4 b5 b6 lemma_1_sub_4)
                         have b10: "ipurge bs u t = ipurge bs u (step t b)"
                           by (metis b9 b7 ipurge_eq p1 p2 p3 p4 p5 p6 p7 reachableStep)
                         have b11: "(((step s b) \<lhd> bs \<cong> t \<lhd> (ipurge bs u (step t b)) @ u))"
                           using b8 b10 by auto
                         then show ?thesis
                           using b2 observ_equivalence_def run_Cons by auto
                       qed
                   qed
              }
              then show ?thesis by blast
              qed
          qed
       }
       then show ?thesis by blast
       qed


    theorem UnwindingTheorem : "\<lbrakk>weakly_step_consistent;
                            dynamic_local_respect;
                            non_interference_respect;
                            weakly_grant_step_consistent;
                            grant_local_respect\<rbrakk> 
                            \<Longrightarrow> noninfluence"
      proof -
        assume p3: weakly_step_consistent
        assume p4: dynamic_local_respect
        assume p5: non_interference_respect
        assume p6: weakly_grant_step_consistent
        assume p7: grant_local_respect
        {
        fix as d
        have "\<forall>s t. reachable0 s \<and>
                  reachable0 t \<and>
                  (s \<approx> (sources as d s) \<approx> t)
                  \<longrightarrow> ((s \<lhd> as \<cong> t \<lhd> (ipurge as d  t) @ d))"
          proof(induct as)
            case Nil show ?case using sources_Nil by auto
          next
            case (Cons b bs)
            assume p0: "\<forall>s t. reachable0 s \<and>
                  reachable0 t \<and>
                  (s \<approx> (sources bs d s) \<approx> t)
                  \<longrightarrow> ((s \<lhd> bs \<cong> t \<lhd> (ipurge bs d  t) @ d))"
            then show ?case
              proof -
              { 
                fix s t
                assume p1: "reachable0 s"
                assume p2: "reachable0 t"
                assume p8: "(s \<approx> (sources (b # bs) d s) \<approx> t)"
                have "s \<lhd> b # bs \<cong> t \<lhd> ipurge (b # bs) d t @ d"
                  proof (cases "is_execute b")
                    assume a0: "is_execute b"
                    then show ?thesis
                      proof (cases "the (domain b) \<in> sources (b # bs) d s")
                        assume b0: "the (domain b) \<in> sources (b # bs) d s"
                        have b1: "((step s b) \<approx> (sources bs d (step s b)) \<approx> (step t b))"
                           using a0 lemma_1_0 p1 p2 p3 p5 p8 b0 by blast 
                        have b3: "ipurge (b # bs) d t = b # (ipurge bs d (step t b))"
                          by (metis a0 b0 ipurge_Cons p1 p2 p3 p4 p5 p6 p7 p8 sources_eq1)
                        have b4: "(((step s b) \<lhd> bs \<cong> (step t b) \<lhd> (ipurge bs d (step t b)) @ d))"
                          using b1 p0 p1 p2 p3 p4 p5 p6 p7 reachableStep by blast
                        then show ?thesis
                          using b3 b4 by auto
                      next
                        assume b0: "the (domain b) \<notin> sources (b # bs) d s"
                        have b1: "sources (b # bs) d s = sources bs d (step s b)"
                           using a0 b0 sources_Cons by auto
                        have b2: "(s \<approx> (sources bs d (step s b)) \<approx> (step s b))"
                           using a0 b0 lemma_2 p1 p4 by blast
                        have b3: "\<forall>v. v\<in>sources bs d (step s b) \<longrightarrow> (s \<sim> v \<sim> t)"
                           using p8 b1 by auto
                        have b5: "(t \<approx> (sources bs d (step s b)) \<approx> (step t b))"
                          using a0 b0 lemma_1_sub_2 p1 p2 p4 p5 p8 by blast
                        have b6: "(s \<approx> (sources bs d (step s b)) \<approx> t)"
                          using b1 p8 by auto
                        have b7: "((step s b) \<approx> (sources bs d (step s b)) \<approx> (step t b))"
                          using b1 b2 b5 lemma_1_sub_4 p8 by auto         
                        have b8: "(sources bs d (step s b)) = (sources bs d (step t b))"
                          by (meson b7 p1 p2 p3 p4 p5 p6 p7 reachableStep sources_eq1)
                        have b9: "\<forall>v. v\<in>sources bs d (step s b)\<longrightarrow> \<not> t_set s (the(domain b)) \<subseteq> t_set s v"
                          using a0 b0 sources_Cons by auto
                        have b10: "\<forall>v. v\<in>sources bs d (step s b) \<longrightarrow> \<not> t_set t (the(domain b)) \<subseteq> t_set t v"
                          by (metis b3 b9 non_interference_respect_def p1 p2 p5)
                        have b11: "the (domain b) \<notin> (sources (b # bs) d t)"
                           using b10 b8 sources_Cons by auto
                        have b12: "ipurge (b # bs) d t = ipurge bs d (step t b)"
                           using a0 b11 execute_exclusive by auto
                        have b13: "(s \<approx> (sources bs d (step s b)) \<approx> (step s b))"
                          using a0 b0 lemma_2 p1 p4 by blast
                        have b14:"(s \<approx> (sources bs d (step s b)) \<approx> t)"
                          using a0 b0 lemma_1_sub_3 p8 by blast
                        have b15: "((step s b) \<approx> (sources bs d (step s b)) \<approx> t)"
                          by (meson b3 b2 ivpeq_def vpeq_symmetric_lemma vpeq_transitive_lemma)
                        have b16: "(((step s b) \<lhd> bs \<cong> t \<lhd> (ipurge bs d t) @ d))"
                          using b15 p0 p1 p2 p3 p4 p5 p6 p7 reachableStep by blast
                        have b17: "(t \<approx> (sources bs d (step s b)) \<approx> (step t b))"
                          using p1 p2 a0 b0 lemma_1_sub_2 p4 p5 p8 by blast
                        have b18: "ipurge bs d t = ipurge bs d (step t b)"
                          by (metis SM.reachableStep SM_axioms b15 b7 ipurge_eq p1 p2 p3 p4 p5 p6 p7)
                        have b19: "(((step s b) \<lhd> bs \<cong> t \<lhd> (ipurge bs d (step t b)) @ d))"
                          using b16 b17 b18 by auto
                        then show ?thesis
                          using b12 observ_equivalence_def run_Cons by auto
                      qed
                   next
                     assume a0: "\<not> is_execute b "
                     have a1: "is_grant b"
                       using a0 execute_exclusive by auto
                     then show ?thesis
                       proof (cases "the (grant_dest b) \<in> (sources (b # bs) d s)")
                         assume b0: "the (grant_dest b) \<in> (sources (b # bs) d s)"
                         have c0: "(sources (b # bs) d s) = {the (grant_dest b)} \<union> (sources bs d (step s b))"
                           using b0 a0 sources_Cons by auto
                         have b1: "((step s b) \<approx> (sources bs d (step s b)) \<approx> (step t b))"
                           using a1 b0 c0 p1 p2 p6 p8 by auto
                         have b2: "(ipurge bs d (step s b)) = (ipurge bs d (step t b))"
                           using b1 ipurge_eq p1 p2 p3 p4 p5 p6 p7 reachableStep by blast
                         have b3: "ipurge (b # bs) d t = b # (ipurge bs d (step t b))"
                           by (metis a0 b0 b2 ipurge_Cons ipurge_eq p1 p2 p3 p4 p5 p6 p7 p8)
                         have b4: "(step s b) \<lhd> bs \<cong> (step t b) \<lhd> ipurge bs d (step t b) @ d "
                           using p0 b1 p1 p2 p3 p4 p5 p6 p7 reachableStep by blast
                         then show ?thesis
                           using b3 observ_equivalence_def run_Cons by auto
                       next
                         assume b0: "the (grant_dest b) \<notin> (sources (b # bs) d s)"
                         have b1: "the (grant_dest b) \<notin> (sources (b # bs) d t)"
                           by (metis b0 p1 p2 p3 p4 p5 p6 p7 p8 sources_eq1)
                         have c0: "\<forall>v. v\<in>sources bs d (step s b) \<longrightarrow> \<not> t_set s (the(grant_dest b)) \<subseteq> t_set s v"
                           using a0 b0 sources_Cons by auto 
                         have c1: "the (grant_dest b) \<notin> (sources (b # bs) d t)"
                           by (metis b0 p1 p2 p3 p4 p5 p6 p7 p8 sources_eq1)
                         have c2: "\<forall>v. v\<in>sources bs d (step t b) \<longrightarrow> \<not> t_set t (the(grant_dest b)) \<subseteq> t_set t v"
                           using a0 c1 sources_Cons by auto
                         have c3: "(sources (b # bs) d s) = (sources bs d (step s b))"
                           using a0 b0 sources_Cons by auto
                         have c4: "(sources (b # bs) d t) = (sources bs d (step t b))"
                           using a0 b1 sources_Cons by auto
                         have b2: "ipurge (b # bs) d t = (ipurge bs d (step t b))"
                           by (simp add: a0 b1)
                         have b3: "(s \<approx> (sources bs d (step s b)) \<approx> (step s b))"
                           by (metis a1 grant_local_respect_def ivpeq_def c0 p1 p7)
                         have b4: "(t \<approx> (sources bs d (step t b)) \<approx> (step t b))"
                           by (metis a1 grant_local_respect_def ivpeq_def c2 p2 p7)
                         have b6: "(s \<approx> (sources bs d (step s b)) \<approx> t)"
                           using a1 c3 p8 by auto
                         have b7: "((step s b) \<approx> (sources bs d (step s b)) \<approx> t)"
                           by (meson b3 b6 ivpeq_def vpeq_symmetric_lemma vpeq_transitive_lemma)
                         have b8: "(((step s b) \<lhd> bs \<cong> t \<lhd> (ipurge bs d t) @ d))"
                           using b7 p0 p1 p2 p3 p4 p5 p6 p7 reachableStep by blast
                         have b5: "(sources bs d (step s b)) = (sources bs d (step t b))"
                           by (metis c3 c4 p1 p2 p3 p4 p5 p6 p7 p8 sources_eq1)
                         have b9: "((step s b) \<approx> (sources bs d (step s b)) \<approx> (step t b))"
                           by (metis b3 b4 b5 b6 lemma_1_sub_4)
                         have b10: "ipurge bs d t = ipurge bs d (step t b)"
                           by (metis b9 b7 ipurge_eq p1 p2 p3 p4 p5 p6 p7 reachableStep)
                         have b11: "(((step s b) \<lhd> bs \<cong> t \<lhd> (ipurge bs d (step t b)) @ d))"
                           using b8 b10 by auto
                         then show ?thesis
                           using b2 observ_equivalence_def run_Cons by auto
                       qed
                   qed
              }
              then show ?thesis by blast
              qed
          qed
       }
       then show ?thesis using noninfluence_def by blast
    qed
  end
end